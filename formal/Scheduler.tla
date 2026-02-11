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
 *   - 5 tasks, MaxWorkers=3, PriorityLimit=1
 *   - Sibling grouping via explicit TaskGroup constant (not string prefix)
 *   - Sqrt sibling penalty via precomputed lookup table (matches impl's sqrt(N)*20000)
 *
 * QUICK WIN #3: Exponential backoff skip cooldown
 * Skip cooldown now uses exponential backoff values {0,1,2,4,8,16,30} matching
 * the real implementation (1,2,4,8,16 capped at 30 cycles).
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
    TaskGroup,             \* task -> group ID (sibling detection)
    \* @type: Int;
    AgingFactor            \* divisor for aging bonus (default 7 in impl)

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

\* Exponential backoff skip cooldown values (Quick Win #3)
\* Matches implementation: 1,2,4,8,16 capped at 30
SkipCooldownValues == {0, 1, 2, 4, 8, 16, 30}

\* Helper: compute next exponential backoff value
\* @type: (Int) => Int;
NextSkipValue(current) ==
    CASE current = 0  -> 1
      [] current = 1  -> 2
      [] current = 2  -> 4
      [] current = 4  -> 8
      [] current = 8  -> 16
      [] current = 16 -> 30
      [] current = 30 -> 30
      [] OTHER        -> 1

\* Helper: compute previous (halved) cooldown value for decay
\* @type: (Int) => Int;
PrevSkipValue(current) ==
    CASE current = 0  -> 0
      [] current = 1  -> 0
      [] current = 2  -> 1
      [] current = 4  -> 2
      [] current = 8  -> 4
      [] current = 16 -> 8
      [] current = 30 -> 16
      [] OTHER        -> 0

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

\* Apalache constant initialization (Medium Term #2: Expanded task set)
\* 5 tasks with overlapping sibling groups and files to expose starvation/priority inversions
\*
\* T1: HIGH(10000), files={f1}, deps={}, plan=TRUE, group="A"  - high priority with plan
\* T2: MEDIUM(20000), files={f2}, deps={}, plan=FALSE, group="A" - sibling of T1
\* T3: HIGH(10000), files={f1,f3}, deps={T1}, plan=FALSE, group="B" - conflicts with T1
\* T4: CRITICAL(0), files={f2,f4}, deps={}, plan=FALSE, group="B" - sibling of T3, conflicts with T2
\* T5: LOW(30000), files={f5}, deps={T3,T4}, plan=TRUE, group="C" - depends on two tasks
CInit ==
    /\ Tasks = {"T1", "T2", "T3", "T4", "T5"}
    /\ MaxWorkers = 3
    /\ PriorityLimit = 1
    /\ MAX_SKIP = 3
    /\ AgingFactor = 7
    /\ BasePriority = [u \in {"T1", "T2", "T3", "T4", "T5"} |->
        CASE u = "T1" -> 10000   \* HIGH
          [] u = "T2" -> 20000   \* MEDIUM
          [] u = "T3" -> 10000   \* HIGH
          [] u = "T4" -> 0       \* CRITICAL
          [] u = "T5" -> 30000]  \* LOW
    /\ TaskDeps = [u \in {"T1", "T2", "T3", "T4", "T5"} |->
        CASE u = "T1" -> {}
          [] u = "T2" -> {}
          [] u = "T3" -> {"T1"}
          [] u = "T4" -> {}
          [] u = "T5" -> {"T3", "T4"}]
    /\ TaskFiles = [u \in {"T1", "T2", "T3", "T4", "T5"} |->
        CASE u = "T1" -> {"f1"}
          [] u = "T2" -> {"f2"}
          [] u = "T3" -> {"f1", "f3"}   \* conflicts with T1
          [] u = "T4" -> {"f2", "f4"}   \* conflicts with T2
          [] u = "T5" -> {"f5"}]
    /\ HasPlan = [u \in {"T1", "T2", "T3", "T4", "T5"} |->
        CASE u = "T1" -> TRUE
          [] u = "T2" -> FALSE
          [] u = "T3" -> FALSE
          [] u = "T4" -> FALSE
          [] u = "T5" -> TRUE]
    /\ TaskGroup = [u \in {"T1", "T2", "T3", "T4", "T5"} |->
        CASE u = "T1" -> "A"
          [] u = "T2" -> "A"  \* sibling of T1
          [] u = "T3" -> "B"
          [] u = "T4" -> "B"  \* sibling of T3
          [] u = "T5" -> "C"]

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

\* Precomputed sqrt sibling penalty lookup table (matches impl's sqrt(N) * 20000)
\* floor(sqrt(0)*20000)=0, floor(sqrt(1)*20000)=20000, floor(sqrt(2)*20000)=28284,
\* floor(sqrt(3)*20000)=34641, floor(sqrt(4)*20000)=40000
\* With CInit's 5 tasks (max 2 per group), SiblingActiveCount <= 1, but the
\* table covers up to 4 for reuse with larger CInit configurations.
\* @type: (Int) => Int;
SqrtSiblingPenalty(n) ==
    CASE n = 0 -> 0
      [] n = 1 -> 20000
      [] n = 2 -> 28284
      [] n = 3 -> 34641
      [] n = 4 -> 40000
      [] OTHER -> 40000  \* cap at sqrt(4) for n > 4

\* Effective priority: lower value = higher priority
\* Uses fixed-point arithmetic (10000 = 1.0)
\* Inlined computation avoids multi-binding LET (Apalache SubstRule issue)
\* @type: (Str) => Int;
EffectivePriority(q) ==
    LET raw == BasePriority[q]
               - (IF HasPlan[q] THEN 15000 ELSE 0)
               - ((readySince[q] * 8000) \div AgingFactor)
               - (BlockedByCount(q) * 7000)
               + SqrtSiblingPenalty(SiblingActiveCount(q))
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

\* Main worker fails: spawned -> failed, apply skip cooldown (exponential backoff)
WorkerFail(t) ==
    /\ taskStatus[t] = "spawned"
    /\ workerType[t] = "main"
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "failed"]
    /\ workerType' = [workerType EXCEPT ![t] = "none"]
    /\ mainCount' = mainCount - 1
    \* Quick Win #3: Exponential backoff instead of linear increment
    /\ skipCount' = [skipCount EXCEPT ![t] = NextSkipValue(skipCount[t])]
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
\* Actions - Retry After Cooldown
\* =========================================================================

\* Failed task becomes eligible again after skip cooldown expires.
\* In the implementation, failed tasks are re-checked by scheduler_can_spawn_task
\* on each tick and become eligible when skip count reaches 0.
RetryAfterCooldown(t) ==
    /\ taskStatus[t] = "failed"
    /\ workerType[t] = "none"
    /\ skipCount[t] = 0
    /\ taskStatus' = [taskStatus EXCEPT ![t] = "pending"]
    /\ UNCHANGED <<skipCount, readySince, workerType, mainCount, priorityCount, tick>>

\* =========================================================================
\* Actions - Aging and Skip Decay
\* =========================================================================

\* Tick: increment aging for pending tasks with met deps, decay skip cooldown
\* Halving matches implementation's exponential backoff decay
TickAging ==
    /\ tick' = tick + 1
    /\ readySince' = [u \in Tasks |->
        IF taskStatus[u] = "pending" /\ DepsCompleted(u)
        THEN readySince[u] + 1
        ELSE readySince[u]]
    /\ skipCount' = [u \in Tasks |-> PrevSkipValue(skipCount[u])]
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
        \/ RetryAfterCooldown(t)

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness ==
    /\ WF_vars(SchedulerTick)
    /\ WF_vars(TickAging)
    /\ \A t \in Tasks :
        /\ WF_vars(WorkerPass(t) \/ WorkerFail(t))
        /\ WF_vars(FixPass(t) \/ FixFail(t))
        /\ WF_vars(RetryAfterCooldown(t))

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ \A t \in Tasks : taskStatus[t] \in StatusValues
    \* Quick Win #3: skipCount uses exponential backoff values
    /\ \A t \in Tasks : skipCount[t] \in SkipCooldownValues
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

\* SkipBoundInvariant: skip cooldown only takes valid exponential values
SkipBoundInvariant ==
    \A t \in Tasks : skipCount[t] \in SkipCooldownValues

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
    /\ (taskStatus["T4"] = "pending" /\ DepsCompleted("T4")) ~> taskStatus["T4"] /= "pending"
    /\ (taskStatus["T5"] = "pending" /\ DepsCompleted("T5")) ~> taskStatus["T5"] /= "pending"

\* SkipDecay: skip cooldown eventually reaches 0
SkipDecay ==
    /\ skipCount["T1"] > 0 ~> skipCount["T1"] = 0
    /\ skipCount["T2"] > 0 ~> skipCount["T2"] = 0
    /\ skipCount["T3"] > 0 ~> skipCount["T3"] = 0
    /\ skipCount["T4"] > 0 ~> skipCount["T4"] = 0
    /\ skipCount["T5"] > 0 ~> skipCount["T5"] = 0

=============================================================================
