---------------------------- MODULE Scheduler --------------------------------
(*
 * TLA+ formal model of Chief Wiggum's task scheduler.
 *
 * Models the core scheduling algorithm: priority calculation with plan bonus,
 * aging bonus, dependency bonus, and sibling WIP penalty; capacity management
 * for main and priority (fix) workers; skip cooldown with exponential backoff;
 * and file conflict prevention.
 *
 * Simplifications for tractability:
 *   - Worker pipeline abstracted to spawned -> PASS/FAIL (no internal steps)
 *   - 3 tasks, MaxWorkers=2, PriorityLimit=1
 *   - Sibling grouping via explicit TaskGroup constant (not string prefix)
 *   - Linear sibling penalty (not sqrt - sufficient for property verification)
 *   - Skip cooldown uses linear decrement (not exponential backoff)
 *
 * NOTE: Bound variables in set comprehensions use distinct names (w, u, v)
 * to avoid shadowing operator parameters -- Apalache's SubstRule cannot
 * resolve substitutions through shadowed bindings.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Tasks,
    \* @type: Int;
    MaxWorkers,            \* max concurrent main workers
    \* @type: Int;
    PriorityLimit,         \* max concurrent fix workers
    \* @type: Int;
    MAX_SKIP,              \* maximum skip cooldown value
    \* @type: Str -> Int;
    BasePriority,          \* task -> base priority (0=CRITICAL, 10000=HIGH, etc.)
    \* @type: Str -> Set(Str);
    TaskDeps,              \* task -> set of prerequisite task IDs
    \* @type: Str -> Set(Str);
    TaskFiles,             \* task -> set of files touched
    \* @type: Str -> Bool;
    HasPlan,               \* task -> TRUE if .ralph/plans/<TASK-ID>.md exists
    \* @type: Str -> Str;
    TaskGroup              \* task -> group ID (sibling detection)

VARIABLES
    \* @type: Str -> Str;
    taskStatus,            \* task -> "pending", "spawned", "merged", "failed"
    \* @type: Str -> Int;
    skipCount,             \* task -> skip cooldown counter (0 = ready)
    \* @type: Str -> Int;
    readySince,            \* task -> aging counter (scheduling ticks waiting)
    \* @type: Str -> Str;
    workerType,            \* task -> "none", "main", "fix"
    \* @type: Int;
    mainCount,             \* current number of active main workers
    \* @type: Int;
    priorityCount,         \* current number of active fix workers
    \* @type: Int;
    tick                   \* global scheduling tick counter

\* @type: <<Str -> Str, Str -> Int, Str -> Int, Str -> Str, Int, Int, Int>>;
vars == <<taskStatus, skipCount, readySince, workerType, mainCount, priorityCount, tick>>

\* =========================================================================
\* Type definitions
\* =========================================================================

StatusValues == {"pending", "spawned", "merged", "failed"}
WorkerTypeValues == {"none", "main", "fix"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ taskStatus = [u \in Tasks |-> "pending"]
    /\ skipCount = [u \in Tasks |-> 0]
    /\ readySince = [u \in Tasks |-> 0]
    /\ workerType = [u \in Tasks |-> "none"]
    /\ mainCount = 0
    /\ priorityCount = 0
    /\ tick = 0

\* Apalache constant initialization
\* T1: HIGH(10000), files={f1}, deps={}, plan=TRUE, group="A"
\* T2: MEDIUM(20000), files={f2}, deps={}, plan=FALSE, group="A"
\* T3: HIGH(10000), files={f1,f3}, deps={T1}, plan=FALSE, group="B"
CInit ==
    /\ Tasks = {"T1", "T2", "T3"}
    /\ MaxWorkers = 2
    /\ PriorityLimit = 1
    /\ MAX_SKIP = 3
    /\ BasePriority = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> 10000
          [] u = "T2" -> 20000
          [] u = "T3" -> 10000]
    /\ TaskDeps = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> {}
          [] u = "T2" -> {}
          [] u = "T3" -> {"T1"}]
    /\ TaskFiles = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> {"f1"}
          [] u = "T2" -> {"f2"}
          [] u = "T3" -> {"f1", "f3"}]
    /\ HasPlan = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> TRUE
          [] u = "T2" -> FALSE
          [] u = "T3" -> FALSE]
    /\ TaskGroup = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> "A"
          [] u = "T2" -> "A"
          [] u = "T3" -> "B"]

\* =========================================================================
\* Helpers - Derived Sets
\* =========================================================================

\* Dependencies completed: all deps have merged
DepsCompleted(q) == \A d \in TaskDeps[q] : taskStatus[d] = "merged"

\* Active main workers: spawned with main worker type
ActiveMainWorkers == {w \in Tasks : workerType[w] = "main" /\ taskStatus[w] = "spawned"}

\* Active fix workers: spawned with fix worker type
ActiveFixWorkers == {w \in Tasks : workerType[w] = "fix" /\ taskStatus[w] = "spawned"}

\* =========================================================================
\* Helpers - Priority Calculation
\* =========================================================================

\* Sibling count: active main workers in the same group (excluding self)
\* @type: (Str) => Int;
SiblingActiveCount(q) ==
    Cardinality({w \in Tasks : workerType[w] = "main" /\ taskStatus[w] = "spawned"
                             /\ w /= q /\ TaskGroup[w] = TaskGroup[q]})

\* Direct dependents count: tasks that list q as a dependency
\* @type: (Str) => Int;
BlockedByCount(q) ==
    Cardinality({v \in Tasks : q \in TaskDeps[v]})

\* Effective priority: lower value = higher priority
\* Uses fixed-point arithmetic (10000 = 1.0)
\* Inlined computation avoids multi-binding LET (Apalache SubstRule issue)
\* @type: (Str) => Int;
EffectivePriority(q) ==
    LET raw == BasePriority[q]
               - (IF HasPlan[q] THEN 15000 ELSE 0)
               - (readySince[q] * 8000)
               - (BlockedByCount(q) * 7000)
               + (SiblingActiveCount(q) * 20000)
    IN IF raw < 0 THEN 0 ELSE raw

\* File conflict: task q shares files with an active main worker
HasFileConflict(q) ==
    \E w \in Tasks : workerType[w] = "main" /\ taskStatus[w] = "spawned"
                   /\ w /= q /\ TaskFiles[q] \cap TaskFiles[w] /= {}

\* Eligible tasks: pending, skip=0, deps met, no file conflict, capacity available
Eligible(q) ==
    /\ taskStatus[q] = "pending"
    /\ skipCount[q] = 0
    /\ DepsCompleted(q)
    /\ ~HasFileConflict(q)
    /\ mainCount < MaxWorkers

\* =========================================================================
\* Actions - Scheduler Tick (spawn highest priority eligible task)
\* =========================================================================

\* Spawn a task that is eligible and has the lowest effective priority value
\* (i.e., highest scheduling priority). Uses existential quantifier with
\* a minimality guard instead of CHOOSE for Apalache compatibility.
SchedulerTick ==
    \E t \in Tasks :
        /\ Eligible(t)
        /\ \A s \in Tasks : Eligible(s) => EffectivePriority(t) <= EffectivePriority(s)
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "spawned"]
        /\ workerType' = [workerType EXCEPT ![t] = "main"]
        /\ mainCount' = mainCount + 1
        /\ readySince' = readySince  \* freeze aging once spawned
        /\ UNCHANGED <<skipCount, priorityCount, tick>>

\* =========================================================================
\* Actions - Worker Completion
\* =========================================================================

\* Main worker passes: spawned -> merged
WorkerPass(t) ==
    /\ taskStatus[t] = "spawned"
    /\ workerType[t] = "main"
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "merged"]
    /\ workerType' = [workerType EXCEPT ![t] = "none"]
    /\ mainCount' = mainCount - 1
    /\ UNCHANGED <<skipCount, readySince, priorityCount, tick>>

\* Main worker fails: spawned -> failed, apply skip cooldown
WorkerFail(t) ==
    /\ taskStatus[t] = "spawned"
    /\ workerType[t] = "main"
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "failed"]
    /\ workerType' = [workerType EXCEPT ![t] = "none"]
    /\ mainCount' = mainCount - 1
    /\ skipCount' = [skipCount EXCEPT ![t] = IF skipCount[t] < MAX_SKIP THEN skipCount[t] + 1 ELSE MAX_SKIP]
    /\ UNCHANGED <<readySince, priorityCount, tick>>

\* =========================================================================
\* Actions - Fix Worker Cycle (priority workers)
\* =========================================================================

\* Spawn fix worker on a failed task (PR comments trigger)
SpawnFixWorker(t) ==
    /\ taskStatus[t] = "failed"
    /\ workerType[t] = "none"
    /\ priorityCount < PriorityLimit
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "spawned"]
    /\ workerType' = [workerType EXCEPT ![t] = "fix"]
    /\ priorityCount' = priorityCount + 1
    /\ UNCHANGED <<skipCount, readySince, mainCount, tick>>

\* Fix worker passes: spawned -> merged
FixPass(t) ==
    /\ taskStatus[t] = "spawned"
    /\ workerType[t] = "fix"
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "merged"]
    /\ workerType' = [workerType EXCEPT ![t] = "none"]
    /\ priorityCount' = priorityCount - 1
    /\ UNCHANGED <<skipCount, readySince, mainCount, tick>>

\* Fix worker fails: spawned -> failed
FixFail(t) ==
    /\ taskStatus[t] = "spawned"
    /\ workerType[t] = "fix"
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "failed"]
    /\ workerType' = [workerType EXCEPT ![t] = "none"]
    /\ priorityCount' = priorityCount - 1
    /\ UNCHANGED <<skipCount, readySince, mainCount, tick>>

\* =========================================================================
\* Actions - Aging and Skip Decay
\* =========================================================================

\* Tick: increment aging for pending tasks with met deps, decrement skip cooldown
TickAging ==
    /\ tick' = tick + 1
    /\ readySince' = [u \in Tasks |->
        IF taskStatus[u] = "pending" /\ DepsCompleted(u)
        THEN readySince[u] + 1
        ELSE readySince[u]]
    /\ skipCount' = [u \in Tasks |->
        IF skipCount[u] > 0
        THEN skipCount[u] - 1
        ELSE 0]
    /\ UNCHANGED <<taskStatus, workerType, mainCount, priorityCount>>

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \/ SchedulerTick
    \/ TickAging
    \/ \E t \in Tasks :
        \/ WorkerPass(t)
        \/ WorkerFail(t)
        \/ SpawnFixWorker(t)
        \/ FixPass(t)
        \/ FixFail(t)

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness ==
    /\ WF_vars(SchedulerTick)
    /\ WF_vars(TickAging)
    /\ \A t \in Tasks :
        /\ WF_vars(WorkerPass(t) \/ WorkerFail(t))
        /\ WF_vars(FixPass(t) \/ FixFail(t))

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ \A t \in Tasks : taskStatus[t] \in StatusValues
    /\ \A t \in Tasks : skipCount[t] \in 0..MAX_SKIP
    /\ \A t \in Tasks : readySince[t] \in 0..100
    /\ \A t \in Tasks : workerType[t] \in WorkerTypeValues
    /\ mainCount \in 0..MaxWorkers
    /\ priorityCount \in 0..PriorityLimit
    /\ tick \in 0..100

\* CapacityInvariant: worker counts within limits
CapacityInvariant ==
    /\ mainCount <= MaxWorkers
    /\ priorityCount <= PriorityLimit

\* DependencyInvariant: spawned tasks have all deps completed
DependencyInvariant ==
    \A t \in Tasks :
        taskStatus[t] = "spawned" /\ workerType[t] = "main" => DepsCompleted(t)

\* FileConflictInvariant: no two active main workers share files
FileConflictInvariant ==
    \A t1, t2 \in ActiveMainWorkers :
        t1 /= t2 => TaskFiles[t1] \cap TaskFiles[t2] = {}

\* SkipBoundInvariant: skip cooldown never exceeds MAX_SKIP
SkipBoundInvariant ==
    \A t \in Tasks : skipCount[t] <= MAX_SKIP

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* NOTE: Apalache --temporal does not enforce fairness ("Handling fairness
\* is not supported yet!"). These properties require TLC for verification.
\* Kept here for documentation and TLC compatibility.
\*
\* Properties are manually unrolled for CInit's concrete tasks because
\* Apalache's SubstRule cannot handle \A-quantified temporal formulas.

\* EventualSpawn: a pending task with satisfied deps eventually leaves pending
EventualSpawn ==
    /\ (taskStatus["T1"] = "pending" /\ DepsCompleted("T1")) ~> taskStatus["T1"] /= "pending"
    /\ (taskStatus["T2"] = "pending" /\ DepsCompleted("T2")) ~> taskStatus["T2"] /= "pending"
    /\ (taskStatus["T3"] = "pending" /\ DepsCompleted("T3")) ~> taskStatus["T3"] /= "pending"

\* SkipDecay: skip cooldown eventually reaches 0
SkipDecay ==
    /\ skipCount["T1"] > 0 ~> skipCount["T1"] = 0
    /\ skipCount["T2"] > 0 ~> skipCount["T2"] = 0
    /\ skipCount["T3"] > 0 ~> skipCount["T3"] = 0

=============================================================================
