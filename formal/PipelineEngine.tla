--------------------------- MODULE PipelineEngine ----------------------------
(*
 * TLA+ formal model of Chief Wiggum's pipeline engine.
 *
 * Models a simplified 3-step pipeline capturing all structural features of
 * the jump-based state machine in lib/pipeline/pipeline-runner.sh:
 *   - Visit counters with per-step maximums
 *   - on_max jump targets (default: "next")
 *   - Nondeterministic agent results: {PASS, FAIL, FIX, SKIP}
 *   - Inline agent handlers for FIX results
 *   - Circuit breaker: consecutive same non-terminal results escalate to FAIL
 *   - Jump target resolution: self, prev, next, abort, <step-id>
 *   - UNKNOWN result with backup extraction (nondeterministic recovery)
 *   - Cost budget enforcement (pipeline aborts when accumulated cost exceeds budget)
 *
 * The 3-step pipeline exercises:
 *   Step 0: No inline handler (FIX -> jump prev, clamped to self at step 0)
 *   Step 1: Has inline handler (FIX -> run inline, then re-run self)
 *   Step 2: Has inline handler (FIX -> run inline, then re-run self)
 *
 * GAP CLOSURE #3: UNKNOWN result + backup extraction
 * When an agent produces no recognizable result, the pipeline attempts a backup
 * session resume to recover the result tag. Modeled as nondeterministic choice:
 * either backup recovers a valid result, or UNKNOWN persists and jumps to self.
 * Consecutive UNKNOWNs are tracked by the circuit breaker.
 * Matches _pipeline_backup_result_extraction() in lib/pipeline/pipeline-runner.sh.
 *
 * GAP CLOSURE #4: Cost budget enforcement
 * Each step consumes an abstract cost unit. If CostBudget > 0 and accumulated
 * cost exceeds the budget, the pipeline aborts. Matches _check_cost_budget() /
 * _update_step_cost() in lib/pipeline/pipeline-runner.sh.
 *
 * GAP CLOSURE #5: Named jump targets
 * ResolveJump supports step IDs in addition to self/prev/next/abort.
 * Modeled via step index lookup (step0/step1/step2 for CInit's 3 steps).
 * Matches pipeline_find_step_index() resolution in _resolve_jump_target().
 *
 * MEDIUM TERM #3: Supervisor Loop
 * Models supervisor-level interruption and restart:
 *   - SupervisorInterval: how often supervisor reviews progress
 *   - Supervisor can issue CONTINUE, STOP, or RESTART decisions
 *   - RESTART resets current step's visit counter (iteration reset)
 *   - Models "supervisor restarts reset counters" class of bugs
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, Sequences

CONSTANTS
    \* @type: Int;
    NumSteps,
    \* @type: Int -> Int;
    MaxVisits,         \* function: step index -> max visits (0 = unlimited)
    \* @type: Int -> Bool;
    HasInline,         \* function: step index -> TRUE if FIX has inline handler
    \* @type: Int -> Int;
    InlineMax,         \* function: step index -> max inline visits (0 = unlimited)
    \* @type: Int;
    CircuitBreakerThreshold,
    \* @type: Int;
    SupervisorInterval,  \* iterations between supervisor checks (0 = no supervisor)
    \* @type: Int;
    MaxSupervisorRestarts, \* max times supervisor can restart a step
    \* @type: Int;
    CostBudget             \* max accumulated cost (0 = unlimited). GAP CLOSURE #4.

VARIABLES
    \* @type: Int;
    pc,                \* current step index (-1 = aborted, NumSteps = completed)
    \* @type: Int -> Int;
    visits,            \* function: step index -> visit count
    \* @type: Int -> Int;
    inlineVisits,      \* function: step index -> inline handler visit count
    \* @type: Int -> Int;
    consecutiveSame,   \* function: step index -> consecutive same result count
    \* @type: Int -> Str;
    lastResult,        \* function: step index -> last non-terminal result string
    \* @type: Str;
    status,            \* "running", "completed", "aborted"
    \* === SUPERVISOR STATE (Medium Term #3) ===
    \* @type: Int;
    iterationsSinceCheck,  \* iterations since last supervisor check
    \* @type: Int -> Int;
    supervisorRestarts,    \* function: step index -> restart count by supervisor
    \* @type: Int;
    currentCost            \* accumulated pipeline cost (GAP CLOSURE #4)

\* @type: <<Int, Int -> Int, Int -> Int, Int -> Int, Int -> Str, Str, Int, Int -> Int, Int>>;
vars == <<pc, visits, inlineVisits, consecutiveSame, lastResult, status, iterationsSinceCheck, supervisorRestarts, currentCost>>

\* =========================================================================
\* Type definitions
\* =========================================================================

StepRange == 0..(NumSteps - 1)
\* GAP CLOSURE #3: UNKNOWN added — matches implementation's UNKNOWN result path
Results == {"PASS", "FAIL", "FIX", "SKIP", "UNKNOWN"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ pc = 0
    /\ visits = [i \in StepRange |-> 0]
    /\ inlineVisits = [i \in StepRange |-> 0]
    /\ consecutiveSame = [i \in StepRange |-> 0]
    /\ lastResult = [i \in StepRange |-> ""]
    /\ status = "running"
    /\ iterationsSinceCheck = 0
    /\ supervisorRestarts = [i \in StepRange |-> 0]
    /\ currentCost = 0

\* Apalache constant initialization
CInit ==
    /\ NumSteps = 3
    /\ MaxVisits = [i \in 0..2 |-> IF i = 0 THEN 2 ELSE 3]
    /\ HasInline = [i \in 0..2 |-> IF i = 0 THEN FALSE ELSE TRUE]
    /\ InlineMax = [i \in 0..2 |-> IF i = 0 THEN 0 ELSE 2]
    /\ CircuitBreakerThreshold = 3
    /\ SupervisorInterval = 2       \* supervisor checks every 2 iterations
    /\ MaxSupervisorRestarts = 1    \* supervisor can restart each step once
    /\ CostBudget = 5              \* pipeline aborts after 5 abstract cost units (GAP CLOSURE #4)

\* =========================================================================
\* Helpers
\* =========================================================================

\* Resolve jump target to step index
\* GAP CLOSURE #5: Named step targets (step0/step1/step2) in addition to
\* self/prev/next/abort. Matches pipeline_find_step_index() in pipeline-runner.sh.
\* @type: (Str, Int) => Int;
ResolveJump(target, current) ==
    CASE target = "self"  -> current
      [] target = "next"  -> current + 1
      [] target = "prev"  -> IF current > 0 THEN current - 1 ELSE 0
      [] target = "abort" -> -1
      \* Named step targets: resolve to step index (CInit has 3 steps: 0, 1, 2)
      [] target = "step0" -> 0
      [] target = "step1" -> 1
      [] target = "step2" -> 2
      [] OTHER            -> -1

\* Check if a result is terminal for the step (resets circuit breaker)
\* @type: (Str) => Bool;
IsTerminalResult(r) == r \in {"PASS", "FAIL", "SKIP"}

\* Helper: unchanged supervisor state
SupervisorUnchanged == UNCHANGED <<iterationsSinceCheck, supervisorRestarts>>

\* Helper: unchanged cost state
CostUnchanged == UNCHANGED currentCost

\* =========================================================================
\* Actions
\* =========================================================================

\* Execute a pipeline step: nondeterministically choose a result and dispatch
ExecuteStep ==
    /\ status = "running"
    /\ pc >= 0
    /\ pc < NumSteps
    \* GAP CLOSURE #4: Cost budget check before execution
    /\ CostBudget = 0 \/ currentCost < CostBudget
    /\ \E result \in Results :
        LET
            i == pc
            currentVisits == visits[i]
            maxV == MaxVisits[i]
        IN
        \* --- Check max visits first ---
        IF maxV > 0 /\ currentVisits >= maxV
        THEN
            \* on_max fires: default jump is "next"
            LET nextPc == ResolveJump("next", i) IN
            /\ pc' = nextPc
            /\ status' = IF nextPc < 0 THEN "aborted"
                          ELSE IF nextPc >= NumSteps THEN "completed"
                          ELSE "running"
            /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult>>
            /\ CostUnchanged
        ELSE
            LET
                \* Increment visit counter
                newVisits == [visits EXCEPT ![i] = currentVisits + 1]

                \* GAP CLOSURE #3: Backup extraction for UNKNOWN results.
                \* Nondeterministically recover to a valid result, or stay UNKNOWN.
                \* Matches _pipeline_backup_result_extraction() in pipeline-runner.sh.
                recoveredResult == result  \* identity; backup nondeterminism modeled below

                \* Circuit breaker check (tracks UNKNOWN same as FIX — non-terminal)
                prevCount == consecutiveSame[i]
                prevResult == lastResult[i]
                newCount == IF IsTerminalResult(recoveredResult) THEN 0
                            ELSE IF prevResult = recoveredResult THEN prevCount + 1
                            ELSE 1
                cbTripped == ~IsTerminalResult(recoveredResult) /\ newCount >= CircuitBreakerThreshold
                effectiveResult == IF cbTripped THEN "FAIL" ELSE recoveredResult

                \* Update circuit breaker tracking
                newConsec == [consecutiveSame EXCEPT ![i] = newCount]
                newLast == [lastResult EXCEPT ![i] = IF IsTerminalResult(recoveredResult) THEN "" ELSE recoveredResult]
            IN
            \* --- Dispatch on effective result ---
            CASE effectiveResult = "PASS" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1

              [] effectiveResult = "FAIL" ->
                /\ pc' = -1
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = "aborted"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1

              [] effectiveResult = "SKIP" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1

              [] effectiveResult = "FIX" ->
                IF HasInline[i]
                THEN
                    \* Inline handler: check inline max, then re-run self
                    LET
                        currentInline == inlineVisits[i]
                        inlineMax == InlineMax[i]
                    IN
                    IF inlineMax > 0 /\ currentInline >= inlineMax
                    THEN
                        \* Inline max exceeded: on_max default "next"
                        LET nextPc == ResolveJump("next", i) IN
                        /\ pc' = nextPc
                        /\ visits' = newVisits
                        /\ inlineVisits' = inlineVisits
                        /\ consecutiveSame' = newConsec
                        /\ lastResult' = newLast
                        /\ status' = IF nextPc < 0 THEN "aborted"
                                      ELSE IF nextPc >= NumSteps THEN "completed"
                                      ELSE "running"
                        /\ currentCost' = currentCost + 1
                    ELSE
                        \* Run inline (atomic), then jump to self (re-run parent)
                        \* Reset circuit breaker for parent since inline ran between
                        /\ pc' = i
                        /\ visits' = newVisits
                        /\ inlineVisits' = [inlineVisits EXCEPT ![i] = currentInline + 1]
                        /\ consecutiveSame' = [newConsec EXCEPT ![i] = 0]
                        /\ lastResult' = [newLast EXCEPT ![i] = ""]
                        /\ status' = "running"
                        /\ currentCost' = currentCost + 1
                ELSE
                    \* No inline handler: jump prev (or self if at step 0)
                    LET nextPc == ResolveJump("prev", i) IN
                    /\ pc' = nextPc
                    /\ visits' = newVisits
                    /\ inlineVisits' = inlineVisits
                    /\ consecutiveSame' = newConsec
                    /\ lastResult' = newLast
                    /\ status' = "running"
                    /\ currentCost' = currentCost + 1

              \* GAP CLOSURE #3: UNKNOWN result — backup extraction failed or not attempted.
              \* Jump to self (re-run step). Circuit breaker tracks consecutive UNKNOWNs.
              [] effectiveResult = "UNKNOWN" ->
                /\ pc' = i
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1

\* Execute step and increment iteration counter
\* Guard: when supervisor is enabled, execution blocks once the interval is reached
\* — the real implementation checks the supervisor deterministically at that point.
ExecuteStepWithCount ==
    /\ SupervisorInterval = 0 \/ iterationsSinceCheck < SupervisorInterval
    /\ ExecuteStep
    /\ iterationsSinceCheck' = iterationsSinceCheck + 1
    /\ UNCHANGED supervisorRestarts

\* GAP CLOSURE #4: Cost budget exceeded — pipeline aborts immediately.
\* Matches _check_cost_budget() in pipeline-runner.sh which returns 1 when
\* WIGGUM_WORKER_COST_LIMIT is exceeded, causing pipeline_run_all to return 1.
CostBudgetAbort ==
    /\ status = "running"
    /\ CostBudget > 0
    /\ currentCost >= CostBudget
    /\ status' = "aborted"
    /\ pc' = -1
    /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult, currentCost>>
    /\ SupervisorUnchanged

\* =========================================================================
\* Supervisor Actions (Medium Term #3)
\* =========================================================================

\* Supervisor checks and decides to CONTINUE (no-op, reset counter)
SupervisorContinue ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<pc, visits, inlineVisits, consecutiveSame, lastResult, status, supervisorRestarts, currentCost>>

\* Supervisor decides to STOP (abort pipeline)
SupervisorStop ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ status' = "aborted"
    /\ pc' = -1
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult, supervisorRestarts, currentCost>>

\* Supervisor decides to RESTART current step (reset visit counter)
\* This models "supervisor restarts reset counters" class of bugs
SupervisorRestart ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ pc >= 0
    /\ pc < NumSteps
    /\ supervisorRestarts[pc] < MaxSupervisorRestarts
    \* Reset current step's visit counter (the dangerous reset)
    /\ visits' = [visits EXCEPT ![pc] = 0]
    /\ inlineVisits' = [inlineVisits EXCEPT ![pc] = 0]
    /\ consecutiveSame' = [consecutiveSame EXCEPT ![pc] = 0]
    /\ lastResult' = [lastResult EXCEPT ![pc] = ""]
    /\ supervisorRestarts' = [supervisorRestarts EXCEPT ![pc] = supervisorRestarts[pc] + 1]
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<pc, status, currentCost>>

\* Terminal states are absorbing
Terminated ==
    /\ status \in {"completed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ ExecuteStepWithCount
    \/ CostBudgetAbort
    \/ SupervisorContinue
    \/ SupervisorStop
    \/ SupervisorRestart
    \/ Terminated

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness == WF_vars(ExecuteStep)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ pc \in -1..NumSteps
    /\ \A i \in StepRange : visits[i] \in 0..(MaxVisits[i] + 2)
    /\ \A i \in StepRange : inlineVisits[i] \in 0..(InlineMax[i] + 1)
    /\ \A i \in StepRange : consecutiveSame[i] \in 0..CircuitBreakerThreshold
    /\ \A i \in StepRange : lastResult[i] \in {"", "FIX", "UNKNOWN"}
    /\ status \in {"running", "completed", "aborted"}
    /\ iterationsSinceCheck \in 0..(SupervisorInterval + 1)
    /\ \A i \in StepRange : supervisorRestarts[i] \in 0..(MaxSupervisorRestarts + 1)
    /\ currentCost \in 0..(CostBudget + NumSteps)

\* VisitsBounded: visits never wildly exceed max
\* A step may enter at max count (visit happens, then on_max redirects),
\* so visits[i] can be at most MaxVisits[i] + 1
\* NOTE: With supervisor restarts, visits can exceed max if supervisor resets counter
\* This invariant may be violated with supervisor restarts enabled - that's the bug!
VisitsBounded ==
    \A i \in StepRange :
        MaxVisits[i] > 0 => visits[i] <= MaxVisits[i] + 1

\* InlineVisitsBounded: inline visits stay within bounds
InlineVisitsBounded ==
    \A i \in StepRange :
        InlineMax[i] > 0 => inlineVisits[i] <= InlineMax[i] + 1

\* SupervisorRestartsBounded: supervisor restarts don't exceed max
SupervisorRestartsBounded ==
    \A i \in StepRange : supervisorRestarts[i] <= MaxSupervisorRestarts

\* StatusConsistency: status matches pc
StatusConsistency ==
    /\ (pc = -1) => (status = "aborted")
    /\ (pc >= NumSteps) => (status = "completed")
    /\ (pc >= 0 /\ pc < NumSteps) => (status = "running")

\* CostBudgetInvariant: cost never exceeds budget + 1 (last step may push over)
\* GAP CLOSURE #4: safety property for cost budget enforcement
CostBudgetInvariant ==
    CostBudget > 0 => currentCost <= CostBudget + 1

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* PipelineTermination: the pipeline always eventually completes or aborts
\* Argument: every step has finite max visits. The circuit breaker escalates
\* repeated non-terminal results to FAIL (abort). Combined, this guarantees
\* the pipeline cannot loop forever.
\* NOTE: Requires TLC for verification -- Apalache --temporal does not
\* enforce fairness ("Handling fairness is not supported yet!").
PipelineTermination == <>(status \in {"completed", "aborted"})

=============================================================================
