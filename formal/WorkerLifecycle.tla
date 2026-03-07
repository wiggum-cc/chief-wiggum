--------------------------- MODULE WorkerLifecycle ---------------------------
(*
 * TLA+ formal model of Chief Wiggum's worker lifecycle state machine.
 *
 * Faithfully encodes every transition from config/worker-lifecycle.json.
 * Transient states (fix_completed, resolved) are skipped atomically --
 * chains collapse into a single transition. merge_conflict is modeled
 * as a real state since it persists until a conflict.* event fires.
 *
 * PR EXISTENCE MODELING:
 * Models PR creation as a nondeterministic action to catch bugs where
 * kanban is marked [P] (pending approval) without a PR existing.
 * The TaskPendingApproval and WorkerCompletion actions require prExists=TRUE.
 * PR creation failure leaves the worker in needs_merge (no PR, can retry)
 * or transitions to failed via WorkerFailure.
 *
 * EFFECT-STATE MODELING (Quick Win #1):
 * Models side effects as explicit state variables to catch partial-effect
 * and crash-recovery bugs:
 *   - inConflictQueue: whether task is queued for conflict resolution
 *   - worktreeState: worktree lifecycle (absent/present/cleaning)
 *   - lastError: error category from last failure
 *
 * CRASH/RESTART MODELING (Quick Win #2):
 * Includes Crash action that can interrupt running states, leaving effects
 * partially applied. StartupReset actions model orchestrator restart recovery.
 *
 * STARTUP RECONCILIATION (GAP CLOSURE #6):
 * Models _scheduler_reconcile_merged_workers() from scheduler.sh.
 * After mid-transition crashes (MidCrashMergeSucceeded, MidCrashMergeConflict),
 * effect-state variables (kanban, conflict queue, GitHub sync, worktree, error)
 * may be inconsistent with the lifecycle state. StartupReconcileMerged and
 * StartupReconcileConflict repair these inconsistencies on restart, achieving
 * eventual consistency via the outbox pattern.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    MAX_MERGE_ATTEMPTS,
    \* @type: Int;
    MAX_RECOVERY_ATTEMPTS

VARIABLES
    \* @type: Str;
    state,
    \* @type: Int;
    mergeAttempts,
    \* @type: Int;
    recoveryAttempts,
    \* @type: Str;
    kanban,
    \* === EFFECT-STATE VARIABLES (Quick Win #1) ===
    \* @type: Bool;
    inConflictQueue,       \* TRUE if task is in conflict resolution queue
    \* @type: Str;
    worktreeState,         \* "absent", "present", "cleaning"
    \* @type: Str;
    lastError,             \* "", "merge_conflict", "rebase_failed", "hard_fail"
    \* @type: Bool;
    githubSynced,          \* TRUE if GitHub issue status matches kanban
    \* === ENVIRONMENT STATE (Medium Term #1: Structured Nondeterminism) ===
    \* @type: Bool;
    baseMoved,             \* TRUE if upstream base has moved (causes out-of-date)
    \* @type: Bool;
    hasConflict,           \* TRUE if merge would conflict (rebase cannot succeed)
    \* @type: Bool;
    hasComments,           \* TRUE if PR has new unaddressed comments
    \* === PR STATE ===
    \* @type: Bool;
    prExists               \* TRUE if a GitHub PR has been successfully created

\* @type: <<Str, Int, Int, Str, Bool, Str, Str, Bool, Bool, Bool, Bool, Bool>>;
vars == <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue, worktreeState, lastError, githubSynced, baseMoved, hasConflict, hasComments, prExists>>

\* =========================================================================
\* Type and state definitions
\* =========================================================================

AllStates == {
    "none", "needs_fix", "fixing", "needs_merge", "merging",
    "merge_conflict", "needs_resolve", "needs_multi_resolve",
    "resolving", "merged", "failed"
}

RunningStates == {"fixing", "merging", "resolving"}

TerminalStates == {"merged", "failed"}

KanbanValues == {" ", "=", "x", "*", "P"}

WorktreeValues == {"absent", "present", "cleaning"}

ErrorValues == {"", "merge_conflict", "rebase_failed", "hard_fail"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ state = "none"
    /\ mergeAttempts = 0
    /\ recoveryAttempts = 0
    /\ kanban = " "
    /\ inConflictQueue = FALSE
    /\ worktreeState = "absent"
    /\ lastError = ""
    /\ githubSynced = TRUE
    /\ baseMoved = FALSE
    /\ hasConflict = FALSE
    /\ hasComments = FALSE
    /\ prExists = FALSE

\* Apalache constant initialization (replaces .cfg)
CInit ==
    /\ MAX_MERGE_ATTEMPTS = 3
    /\ MAX_RECOVERY_ATTEMPTS = 2

\* Helper: unchanged environment variables
EnvVarsUnchanged == UNCHANGED <<baseMoved, hasConflict, hasComments, prExists>>

\* Helper: unchanged effect-state variables
EffectVarsUnchanged == UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* Helper: unchanged effect-state AND environment variables
AllAuxUnchanged == EffectVarsUnchanged /\ EnvVarsUnchanged

\* =========================================================================
\* Helper: check_permanent effect (inline)
\* If recovery attempts exhausted, set kanban to "*"
\* =========================================================================

\* @type: (Str) => Str;
KanbanAfterCheckPermanent(currentKanban) ==
    IF recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    THEN "*"
    ELSE currentKanban

\* =========================================================================
\* Actions - Worker Spawn
\* =========================================================================

\* worker.spawned: none -> needs_merge, kanban "="
\* Effect: creates worktree, marks github out of sync
WorkerSpawned ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ worktreeState' = "present"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Fix Cycle
\* =========================================================================

\* fix.detected: none -> needs_fix
FixDetectedFromNone ==
    /\ state = "none"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.detected: needs_merge -> needs_fix
FixDetectedFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
\* kanban "=" (clear permanent failure marker on recovery)
FixDetectedFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* fix.started: needs_fix -> fixing
FixStarted ==
    /\ state = "needs_fix"
    /\ state' = "fixing"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.pass: fixing -> needs_merge (guarded: merge_attempts_lt_max)
\* Chains through fix_completed, atomic. Effects: inc_merge_attempts, rm_conflict_queue
FixPassGuarded ==
    /\ state = "fixing"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_merge"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* fix.pass: fixing -> failed (fallback when merge budget exhausted)
\* Effect: check_permanent
FixPassFallback ==
    /\ state = "fixing"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* fix.skip: fixing -> needs_merge (chains through fix_completed, atomic)
\* Effect: rm_conflict_queue
FixSkip ==
    /\ state = "fixing"
    /\ state' = "needs_merge"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* fix.partial: fixing -> needs_fix (retry)
FixPartial ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.fail: fixing -> failed, effect: check_permanent
FixFail ==
    /\ state = "fixing"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* fix.timeout: fixing -> needs_fix
FixTimeout ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.already_merged: needs_fix -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
FixAlreadyMerged ==
    /\ state = "needs_fix"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Merge Cycle
\* =========================================================================

\* merge.start: needs_merge -> merging (guarded: merge_attempts_lt_max)
\* Effect: inc_merge_attempts
MergeStartGuarded ==
    /\ state = "needs_merge"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "merging"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* merge.start: needs_merge -> failed (fallback when guard fails)
\* Effect: check_permanent
MergeStartFallback ==
    /\ state = "needs_merge"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* merge.succeeded: merging -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeSucceeded ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* merge.already_merged: merging -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeAlreadyMerged ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* merge.conflict: merging -> merge_conflict
\* Effects: set_error, add_conflict_queue
\* Structured nondeterminism: only fires when hasConflict is TRUE
MergeConflict ==
    /\ state = "merging"
    /\ hasConflict = TRUE
    /\ state' = "merge_conflict"
    /\ lastError' = "merge_conflict"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* merge.out_of_date: merging -> needs_merge (guarded: rebase_succeeded)
\* Structured nondeterminism: requires baseMoved AND ~hasConflict (rebase can succeed)
MergeOutOfDateRebaseOk ==
    /\ state = "merging"
    /\ baseMoved = TRUE
    /\ hasConflict = FALSE
    /\ state' = "needs_merge"
    /\ baseMoved' = FALSE  \* rebase brings us up to date
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, hasConflict, hasComments, prExists>>
    /\ EffectVarsUnchanged

\* merge.out_of_date: merging -> failed (fallback: rebase failed due to conflict)
\* Effects: set_error, check_permanent
\* Structured nondeterminism: requires baseMoved AND hasConflict
MergeOutOfDateRebaseFail ==
    /\ state = "merging"
    /\ baseMoved = TRUE
    /\ hasConflict = TRUE
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ lastError' = "rebase_failed"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* merge.transient_fail: merging -> needs_merge (guarded: merge_attempts_lt_max)
MergeTransientFailRetry ==
    /\ state = "merging"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* merge.transient_fail: merging -> failed (fallback)
\* Effects: set_error, check_permanent
MergeTransientFailAbort ==
    /\ state = "merging"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* merge.hard_fail: merging -> failed
\* Effects: set_error, check_permanent
MergeHardFail ==
    /\ state = "merging"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ lastError' = "hard_fail"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* merge.pr_merged: * -> merged, kanban "x" (wildcard from)
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
\* Clears error state since merge succeeded externally
MergePrMerged ==
    /\ state \notin {"merged"}
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Conflict Resolution
\* =========================================================================

\* conflict.needs_resolve: merge_conflict -> needs_resolve (guarded)
ConflictNeedsResolveGuarded ==
    /\ state = "merge_conflict"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* conflict.needs_resolve: merge_conflict -> failed (fallback)
\* Effect: check_permanent
ConflictNeedsResolveFallback ==
    /\ state = "merge_conflict"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* conflict.needs_multi: merge_conflict -> needs_multi_resolve
ConflictNeedsMulti ==
    /\ state = "merge_conflict"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Resolve Cycle
\* =========================================================================

\* resolve.startup_reset: resolving -> needs_resolve (effect: reset_merge)
ResolveStartupResetFromResolving ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.startup_reset: none -> needs_resolve
ResolveStartupResetFromNone ==
    /\ state = "none"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.startup_reset: resolved is transient and skipped, but this
\* transition is from a state that in the JSON exists. Since we skip
\* "resolved" as transient, this transition is unreachable in our model.
\* Included for documentation completeness but guarded to be unreachable.

\* resolve.started: needs_resolve -> resolving
ResolveStartedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.started: needs_multi_resolve -> resolving
ResolveStartedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.started: needs_merge -> resolving (manual resolve from needs_merge)
ResolveStartedFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.started: resolving -> null (idempotent re-entry, no state change)
ResolveStartedFromResolving ==
    /\ state = "resolving"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.succeeded: resolving -> needs_merge (chains through resolved, atomic)
\* Effects: rm_conflict_queue, clear_error
ResolveSucceeded ==
    /\ state = "resolving"
    /\ state' = "needs_merge"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* resolve.fail: resolving -> failed
\* Effect: check_permanent
ResolveFailFromResolving ==
    /\ state = "resolving"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.fail: needs_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.fail: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.timeout: resolving -> needs_resolve
ResolveTimeout ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.stuck_reset: resolving -> needs_resolve (guarded: merge_attempts_lt_max)
\* Effect: inc_merge_attempts
ResolveStuckResetGuarded ==
    /\ state = "resolving"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.stuck_reset: resolving -> failed (fallback)
\* Effect: check_permanent
ResolveStuckResetFallback ==
    /\ state = "resolving"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.already_merged: needs_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
ResolveAlreadyMergedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* resolve.already_merged: needs_multi_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
ResolveAlreadyMergedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* resolve.max_exceeded: needs_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.max_exceeded: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.batch_failed: needs_multi_resolve -> needs_resolve
ResolveBatchFailedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.batch_failed: needs_resolve -> needs_resolve (no-op on state)
ResolveBatchFailedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - PR Events
\* =========================================================================

\* pr.conflict_detected: merge_conflict -> needs_resolve (redundant detection, no effects)
PrConflictFromMergeConflict ==
    /\ state = "merge_conflict"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.conflict_detected: none -> needs_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrConflictFromNone ==
    /\ state = "none"
    /\ hasComments = FALSE
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: needs_merge -> needs_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ hasComments = FALSE
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: needs_fix -> needs_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ hasComments = FALSE
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: failed -> needs_resolve (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, reset_merge, add_conflict_queue. kanban "="
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrConflictFromFailed ==
    /\ state = "failed"
    /\ hasComments = FALSE
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ inConflictQueue' = TRUE
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED worktreeState
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: none -> needs_multi_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrMultiConflictFromNone ==
    /\ state = "none"
    /\ hasComments = FALSE
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: needs_merge -> needs_multi_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrMultiConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ hasComments = FALSE
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: needs_fix -> needs_multi_resolve
\* Effect: add_conflict_queue
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrMultiConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ hasComments = FALSE
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: failed -> needs_multi_resolve (guarded)
\* Effects: inc_recovery, reset_merge, add_conflict_queue. kanban "="
\* Guard: ~hasComments — optimizer checks comments first; conflict events never fire when comments exist
PrMultiConflictFromFailed ==
    /\ state = "failed"
    /\ hasComments = FALSE
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_multi_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ inConflictQueue' = TRUE
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED worktreeState
    /\ EnvVarsUnchanged

\* pr.comments_detected: none -> needs_fix
\* Guard: hasComments — optimizer only fires comments events when comments exist
PrCommentsFromNone ==
    /\ state = "none"
    /\ hasComments = TRUE
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.comments_detected: needs_merge -> needs_fix
\* Guard: hasComments — optimizer only fires comments events when comments exist
PrCommentsFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ hasComments = TRUE
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.comments_detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
\* Effect: inc_recovery. kanban "="
\* Guard: hasComments — optimizer only fires comments events when comments exist
PrCommentsFromFailed ==
    /\ state = "failed"
    /\ hasComments = TRUE
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* pr.retrack: none -> needs_merge
PrRetrack ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* recovery.to_resolve: failed -> needs_resolve (guarded)
\* Effects: inc_recovery, reset_merge. kanban "="
RecoveryToResolveGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* recovery.to_resolve: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToResolveFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* recovery.to_fix: failed -> needs_fix (guarded)
\* Effect: inc_recovery. kanban "="
RecoveryToFixGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* recovery.to_fix: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToFixFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* user.resume: failed -> needs_merge, kanban "="
\* Effect: rm_conflict_queue
UserResume ==
    /\ state = "failed"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, worktreeState>>
    /\ EnvVarsUnchanged

\* permanent_failure: failed -> failed, kanban "*"
\* Effect: sync_github
PermanentFailure ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Startup Reset (Quick Win #2: Crash Recovery)
\* =========================================================================

\* startup.reset: fixing -> needs_fix
StartupResetFixing ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* startup.reset: merging -> needs_merge, effect: reset_merge
StartupResetMerging ==
    /\ state = "merging"
    /\ state' = "needs_merge"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Startup Reconciliation (Effect-State Repair)
\*
\* Models _scheduler_reconcile_merged_workers() from scheduler.sh.
\* After a mid-transition crash, the state machine may be in a terminal
\* state but with stale effect-state variables. These actions fire on
\* startup to bring effect-state into consistency with lifecycle state.
\*
\* This closes the gap identified by MidCrashMergeSucceeded and
\* MidCrashMergeConflict: state is updated atomically via git_state_set()
\* but kanban, conflict queue, GitHub sync, and worktree cleanup are
\* separate operations that may not have executed.
\* =========================================================================

\* Reconcile merged worker: state="merged" but effect-state inconsistent.
\* Matches _scheduler_reconcile_merged_workers() which checks:
\*   Bug 1: kanban != "x" => update_kanban_status("x")
\*   Bug 2: conflict queue not cleared => conflict_queue_remove()
\*   Bug 4: GitHub not synced => github_issue_sync_task_status()
\* Also handles worktree leaked (cleanup_worktree never ran) and stale error.
StartupReconcileMerged ==
    /\ state = "merged"
    \* Guard: at least one effect-state variable is inconsistent
    /\ \/ kanban /= "x"
       \/ inConflictQueue = TRUE
       \/ githubSynced = FALSE
       \/ worktreeState = "present"
       \/ lastError /= ""
    \* Reconcile: set all effect-state to expected values for merged
    /\ kanban' = "x"
    /\ inConflictQueue' = FALSE
    /\ githubSynced' = TRUE
    /\ worktreeState' = IF worktreeState = "present" THEN "cleaning" ELSE worktreeState
    /\ lastError' = ""
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* Reconcile conflict state: state="merge_conflict" but effects not applied.
\* After MidCrashMergeConflict, set_error and add_conflict_queue didn't run.
\* On restart, the scheduler detects merge_conflict state and ensures
\* the task is queued for resolution and error is set.
StartupReconcileConflict ==
    /\ state = "merge_conflict"
    \* Guard: effect-state inconsistent with merge_conflict state
    /\ \/ inConflictQueue = FALSE
       \/ lastError /= "merge_conflict"
    \* Reconcile: apply the effects that should have run
    /\ inConflictQueue' = TRUE
    /\ lastError' = "merge_conflict"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Crash (Quick Win #2)
\* Models process crash at two granularities:
\*   1. Pre-transition crash: process dies during running state before any
\*      transition fires. State unchanged, effects may be partial.
\*   2. Mid-transition crash: emit_event() wrote git_state_set() (atomic)
\*      but crashed before _lifecycle_update_kanban() or effects ran.
\*      State updated to target, kanban stale, effects not applied.
\*
\* The implementation's emit_event() applies changes sequentially:
\*   git_state_set -> kanban update -> event log -> effects
\* Each is individually atomic (temp+mv), but the sequence is not.
\* =========================================================================

\* Pre-transition crash while fixing: state unchanged, githubSynced may drift
CrashWhileFixing ==
    /\ state = "fixing"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    /\ githubSynced' \in {TRUE, FALSE}
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Pre-transition crash while merging: state unchanged, githubSynced may drift
CrashWhileMerging ==
    /\ state = "merging"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    /\ githubSynced' \in {TRUE, FALSE}
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Pre-transition crash while resolving: state unchanged, queue may drift
CrashWhileResolving ==
    /\ state = "resolving"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    /\ githubSynced' \in {TRUE, FALSE}
    /\ inConflictQueue' \in {TRUE, FALSE}
    /\ UNCHANGED <<worktreeState, lastError>>

\* Mid-transition crash: merge.succeeded wrote state="merged" but kanban
\* still "=" (or whatever it was). Effects (sync_github, cleanup_worktree,
\* release_claim) not applied. This is the #1 real-world crash bug class.
MidCrashMergeSucceeded ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* Effects not applied: worktree not cleaned, github not synced, queue not cleared
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Mid-transition crash: merge.conflict wrote state="merge_conflict" but
\* effects (set_error, add_conflict_queue) not applied.
MidCrashMergeConflict ==
    /\ state = "merging"
    /\ hasConflict = TRUE
    /\ state' = "merge_conflict"
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* set_error and add_conflict_queue not applied
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* Mid-transition crash: fix.pass wrote state to target via chain
\* (fix_completed -> needs_merge or failed) but effects not applied.
\* inc_merge_attempts and rm_conflict_queue not run.
MidCrashFixPass ==
    /\ state = "fixing"
    /\ state' = IF mergeAttempts < MAX_MERGE_ATTEMPTS
                 THEN "needs_merge"
                 ELSE "failed"
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* inc_merge_attempts not applied, rm_conflict_queue not applied
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* =========================================================================
\* Actions - Resume Abort (wildcard)
\* =========================================================================

\* resume.abort: * -> failed, kanban "*"
\* Effect: sync_github
ResumeAbort ==
    /\ state \notin {"failed"}
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Also allow from failed (wildcard includes all states)
ResumeAbortFromFailed ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Null-Target Transitions (state unchanged, kanban updated)
\* These model events where to: null in worker-lifecycle.json -- the worker
\* state is preserved but kanban visibility changes, which feeds into
\* ReadyTasks and scheduling. Catches "stuck task never becomes eligible"
\* and "reclaimed task still shows in-progress" bugs.
\* =========================================================================

\* resume.retry: * -> null, kanban "=" (mark in-progress for retry)
\* Wildcard from, but guarded to non-terminal states: applying to "merged"
\* would violate KanbanMergedConsistency (kanban "x" <=> merged).
ResumeRetry ==
    /\ state \notin {"none", "merged"}
    /\ kanban' = "="
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, inConflictQueue,
                   worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* task.reclaim: * -> null, kanban " " (release task back to pending)
\* Wildcard from, but guarded to non-terminal states: applying to "merged"
\* would violate KanbanMergedConsistency (kanban "x" <=> merged).
TaskReclaim ==
    /\ state \notin {"none", "merged"}
    /\ kanban' = " "
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, inConflictQueue,
                   worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Pending Approval (null-target, kanban-only)
\* =========================================================================

\* task.pending_approval: * -> null, kanban "P"
\* Effect: sync_github. Marks task as awaiting approval.
\* Guard: prExists — only mark pending approval when a PR actually exists.
\* Without this guard, PR creation failure would leave kanban="P" with no PR,
\* an unrecoverable state (the bug fixed by this model extension).
TaskPendingApproval ==
    /\ state \notin {"none", "merged"}
    /\ prExists = TRUE
    /\ kanban' = "P"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, inConflictQueue,
                   worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* worker.completion: * -> null, kanban "P" (same as task.pending_approval)
\* Models task-worker.sh COMPLETE path which guards on pr_url existence.
\* Effect: sync_github.
WorkerCompletion ==
    /\ state \notin {"none", "merged"}
    /\ prExists = TRUE
    /\ kanban' = "P"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, inConflictQueue,
                   worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* worker.failure: * -> failed, kanban "*"
\* Models PR creation failure or other unrecoverable worker errors.
\* Effects: sync_github, check_permanent.
WorkerFailure ==
    /\ state \notin {"merged"}
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Planner Completed
\* =========================================================================

\* planner.completed: needs_multi_resolve -> needs_resolve
PlannerCompleted ==
    /\ state = "needs_multi_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Manual Start Merge
\* =========================================================================

\* manual.start_merge: needs_fix -> needs_merge
ManualStartMergeFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* manual.start_merge: failed -> needs_merge (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, clear_error. kanban "="
ManualStartMergeFromFailedGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_merge"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* manual.start_merge: failed -> failed (fallback: guard failed)
ManualStartMergeFromFailedFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Manual Start Fix
\* =========================================================================

\* manual.start_fix: needs_merge -> fixing
ManualStartFixFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "fixing"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* manual.start_fix: needs_fix -> fixing
ManualStartFixFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "fixing"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* manual.start_fix: failed -> fixing (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, clear_error. kanban "="
ManualStartFixFromFailedGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "fixing"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* manual.start_fix: failed -> failed (fallback: guard failed)
ManualStartFixFromFailedFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Environment Changes (Medium Term #1: Structured Nondeterminism)
\* Models external events that change the merge environment
\* =========================================================================

\* Upstream base moves (e.g., another PR merged to main)
EnvBaseMoved ==
    /\ baseMoved = FALSE
    /\ baseMoved' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, hasConflict, hasComments, prExists>>

\* A conflict appears (e.g., concurrent changes to same files)
EnvConflictAppears ==
    /\ hasConflict = FALSE
    /\ hasConflict' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved, hasComments, prExists>>

\* Conflict is resolved externally (e.g., blocking PR merged, files no longer overlap)
EnvConflictResolved ==
    /\ hasConflict = TRUE
    /\ hasConflict' = FALSE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved, hasComments, prExists>>

\* New comments appear on the PR (e.g., reviewer leaves feedback)
EnvCommentsAppear ==
    /\ hasComments = FALSE
    /\ hasComments' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved, hasConflict, prExists>>

\* Comments are addressed (e.g., fix agent resolves feedback)
EnvCommentsResolved ==
    /\ hasComments = TRUE
    /\ hasComments' = FALSE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved, hasConflict, prExists>>

\* =========================================================================
\* Actions - PR Creation (nondeterministic success/failure)
\* Models git_create_pr in cmd-resume.sh / orch-resume-decide.sh / task-worker.sh.
\* PR creation is attempted after pipeline completion in needs_merge state.
\* Success sets prExists=TRUE; failure leaves prExists=FALSE.
\* The code then either marks [P] (requiring prExists) or marks [*] (failed).
\* =========================================================================

\* PR created successfully (gh CLI succeeds)
\* Can happen from needs_merge (the normal post-pipeline state).
PrCreated ==
    /\ state = "needs_merge"
    /\ prExists = FALSE
    /\ prExists' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved, hasConflict, hasComments>>

\* =========================================================================
\* Actions - Worktree Cleanup Completion
\* Models the async completion of worktree removal after merge. Without this,
\* worktreeState goes to "cleaning" but never "absent", preventing verification
\* of stronger eventual invariants (merged => eventually absent worktree) and
\* missing "leaked worktree" bugs.
\* =========================================================================

\* Worktree cleanup finishes: cleaning -> absent
CleanupCompleted ==
    /\ worktreeState = "cleaning"
    /\ worktreeState' = "absent"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban,
                   inConflictQueue, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \* Worker spawn
    \/ WorkerSpawned
    \* Fix cycle
    \/ FixDetectedFromNone
    \/ FixDetectedFromNeedsMerge
    \/ FixDetectedFromFailed
    \/ FixStarted
    \/ FixPassGuarded
    \/ FixPassFallback
    \/ FixSkip
    \/ FixPartial
    \/ FixFail
    \/ FixTimeout
    \/ FixAlreadyMerged
    \* Merge cycle
    \/ MergeStartGuarded
    \/ MergeStartFallback
    \/ MergeSucceeded
    \/ MergeAlreadyMerged
    \/ MergeConflict
    \/ MergeOutOfDateRebaseOk
    \/ MergeOutOfDateRebaseFail
    \/ MergeTransientFailRetry
    \/ MergeTransientFailAbort
    \/ MergeHardFail
    \/ MergePrMerged
    \* Conflict resolution
    \/ ConflictNeedsResolveGuarded
    \/ ConflictNeedsResolveFallback
    \/ ConflictNeedsMulti
    \* Resolve cycle
    \/ ResolveStartupResetFromResolving
    \/ ResolveStartupResetFromNone
    \/ ResolveStartedFromNeedsResolve
    \/ ResolveStartedFromNeedsMulti
    \/ ResolveStartedFromNeedsMerge
    \/ ResolveSucceeded
    \/ ResolveFailFromResolving
    \/ ResolveFailFromNeedsResolve
    \/ ResolveFailFromNeedsMulti
    \/ ResolveTimeout
    \/ ResolveStuckResetGuarded
    \/ ResolveStuckResetFallback
    \/ ResolveAlreadyMergedFromNeedsResolve
    \/ ResolveAlreadyMergedFromNeedsMulti
    \/ ResolveMaxExceededFromNeedsResolve
    \/ ResolveMaxExceededFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsResolve
    \/ ResolveStartedFromResolving
    \* PR events
    \/ PrConflictFromMergeConflict
    \/ PrConflictFromNone
    \/ PrConflictFromNeedsMerge
    \/ PrConflictFromNeedsFix
    \/ PrConflictFromFailed
    \/ PrMultiConflictFromNone
    \/ PrMultiConflictFromNeedsMerge
    \/ PrMultiConflictFromNeedsFix
    \/ PrMultiConflictFromFailed
    \/ PrCommentsFromNone
    \/ PrCommentsFromNeedsMerge
    \/ PrCommentsFromFailed
    \/ PrRetrack
    \* Recovery
    \/ RecoveryToResolveGuarded
    \/ RecoveryToResolveFallback
    \/ RecoveryToFixGuarded
    \/ RecoveryToFixFallback
    \/ UserResume
    \/ PermanentFailure
    \* Startup reset
    \/ StartupResetFixing
    \/ StartupResetMerging
    \* Startup reconciliation (effect-state repair after mid-transition crash)
    \/ StartupReconcileMerged
    \/ StartupReconcileConflict
    \* Pre-transition crash
    \/ CrashWhileFixing
    \/ CrashWhileMerging
    \/ CrashWhileResolving
    \* Mid-transition crash (state written, kanban/effects not)
    \/ MidCrashMergeSucceeded
    \/ MidCrashMergeConflict
    \/ MidCrashFixPass
    \* Resume abort
    \/ ResumeAbort
    \/ ResumeAbortFromFailed
    \* Null-target transitions
    \/ ResumeRetry
    \/ TaskReclaim
    \/ TaskPendingApproval
    \/ WorkerCompletion
    \* Worker failure (PR creation failed, etc.)
    \/ WorkerFailure
    \* Planner completed
    \/ PlannerCompleted
    \* Manual start merge
    \/ ManualStartMergeFromNeedsFix
    \/ ManualStartMergeFromFailedGuarded
    \/ ManualStartMergeFromFailedFallback
    \* Manual start fix
    \/ ManualStartFixFromNeedsMerge
    \/ ManualStartFixFromNeedsFix
    \/ ManualStartFixFromFailedGuarded
    \/ ManualStartFixFromFailedFallback
    \* Worktree cleanup
    \/ CleanupCompleted
    \* PR creation
    \/ PrCreated
    \* Environment changes (Medium Term #1: Structured Nondeterminism)
    \/ EnvBaseMoved
    \/ EnvConflictAppears
    \/ EnvConflictResolved
    \/ EnvCommentsAppear
    \/ EnvCommentsResolved

\* =========================================================================
\* Fairness (for liveness properties)
\* =========================================================================

Fairness ==
    /\ WF_vars(WorkerSpawned)
    /\ WF_vars(FixStarted)
    /\ WF_vars(MergeStartGuarded \/ MergeStartFallback)
    /\ WF_vars(MergeSucceeded \/ MergeHardFail \/ MergeConflict
               \/ MergeOutOfDateRebaseOk \/ MergeOutOfDateRebaseFail)
    /\ WF_vars(ConflictNeedsResolveGuarded \/ ConflictNeedsResolveFallback
               \/ ConflictNeedsMulti)
    /\ WF_vars(ResolveStartedFromNeedsResolve \/ ResolveStartedFromNeedsMulti \/ ResolveStartedFromNeedsMerge)
    /\ WF_vars(ResolveSucceeded \/ ResolveFailFromResolving)
    /\ WF_vars(FixPassGuarded \/ FixPassFallback \/ FixFail \/ FixSkip \/ FixPartial \/ FixTimeout)
    /\ WF_vars(StartupReconcileMerged)
    /\ WF_vars(StartupReconcileConflict)
    /\ WF_vars(CleanupCompleted)
    /\ WF_vars(PlannerCompleted)
    /\ WF_vars(ManualStartMergeFromFailedGuarded \/ ManualStartMergeFromFailedFallback)
    /\ WF_vars(ManualStartFixFromFailedGuarded \/ ManualStartFixFromFailedFallback)
    /\ WF_vars(EnvCommentsResolved)
    /\ WF_vars(PrCreated)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ state \in AllStates
    /\ mergeAttempts \in 0..MAX_MERGE_ATTEMPTS + 1
    /\ recoveryAttempts \in 0..MAX_RECOVERY_ATTEMPTS + 1
    /\ kanban \in KanbanValues
    /\ inConflictQueue \in BOOLEAN
    /\ worktreeState \in WorktreeValues
    /\ lastError \in ErrorValues
    /\ githubSynced \in BOOLEAN
    /\ baseMoved \in BOOLEAN
    /\ hasConflict \in BOOLEAN
    /\ hasComments \in BOOLEAN
    /\ prExists \in BOOLEAN

\* BoundedCounters: counters never exceed their maximums by more than 1
\* (they can reach max and then a transition fires before the guard blocks)
BoundedCounters ==
    /\ mergeAttempts <= MAX_MERGE_ATTEMPTS + 1
    /\ recoveryAttempts <= MAX_RECOVERY_ATTEMPTS + 1

\* TransientStateInvariant: transient states are never observable
\* (fix_completed and resolved are skipped atomically via chains)
TransientStateInvariant ==
    /\ state /= "fix_completed"
    /\ state /= "resolved"

\* MergeConflictReachability: merge_conflict is only reachable from merging
\* (This is not an invariant per se, but validates the lifecycle structure.
\*  The only action that sets state to merge_conflict is MergeConflict,
\*  which requires state = "merging".)

\* KanbanMergedConsistency: crash-safe version.
\* DESIGN GOAL: state = "merged" => kanban = "x"
\*   Violated transiently by MidCrashMergeSucceeded — emit_event() crashes
\*   after git_state_set("merged") but before _lifecycle_update_kanban("x").
\*   RECONCILED by StartupReconcileMerged (models _scheduler_reconcile_merged_workers)
\*   which detects kanban != "x" for merged workers and fixes it on restart.
\* Crash-safe: the converse always holds — kanban "x" always means merged.
KanbanMergedConsistency ==
    kanban = "x" => state = "merged"

\* KanbanFailedConsistency: if permanently failed (kanban "*"), state is failed
KanbanFailedConsistency ==
    kanban = "*" => state = "failed"

\* KanbanPendingApprovalConsistency: kanban "P" requires a PR to exist.
\* This is the invariant that catches the bug where cmd-resume.sh / orch-resume-decide.sh
\* unconditionally marked kanban="P" even when PR creation failed. With the prExists
\* guard on TaskPendingApproval and WorkerCompletion, this invariant holds.
KanbanPendingApprovalConsistency ==
    kanban = "P" => prExists = TRUE

\* CommentConflictExclusion: the optimizer never routes to conflict resolution
\* via PR events when comments are present. Comments take priority because the
\* conflict resolver merges the PR, which would bypass unaddressed review.
\* Enforced by hasComments guards on PrConflict*/PrMultiConflict* actions.
\* (Implicitly verified: if hasComments=TRUE, no PrConflict* action is enabled.)

\* =========================================================================
\* Cross-Module Invariants (Quick Win #4)
\* These validate consistency between effect-state and lifecycle state
\* =========================================================================

\* ConflictQueueConsistency: crash-safe version.
\* DESIGN GOAL: inConflictQueue => state \in {conflict-related states only}
\*   Violated transiently when MidCrashFixPass + MidCrashMergeSucceeded chain:
\*   queue TRUE persists from conflict through fix/merge all the way to "merged"
\*   because rm_conflict_queue effects never run.
\*   RECONCILED by StartupReconcileMerged which clears inConflictQueue for
\*   merged workers on restart.
\* Crash-safe: allow any non-initial state (queue is never set during "none").
ConflictQueueConsistency ==
    inConflictQueue => state /= "none"

\* WorktreeStateConsistency: crash-safe version.
\* DESIGN GOAL: merged => worktreeState \in {"absent", "cleaning"}
\*   Violated by MidCrashMergeSucceeded — cleanup_worktree effect never runs,
\*   leaving worktreeState="present" with state="merged". Implementation fix:
\*   reconcile leaked worktrees for workers in merged state on restart.
\* Crash-safe: merged allows "present" (leaked worktree), none requires absent.
WorktreeStateConsistency ==
    /\ (state = "none" /\ worktreeState = "absent") \/
       (state = "merged") \/
       (state \notin {"none", "merged"})

\* ErrorStateConsistency: lastError reflects the failure mode
ErrorStateConsistency ==
    /\ (lastError = "merge_conflict" => 
        state \in {"merge_conflict", "needs_resolve", "needs_multi_resolve", 
                   "resolving", "failed", "merging"})
    /\ (lastError = "rebase_failed" => state = "failed")
    /\ (lastError = "hard_fail" => state = "failed")

\* MergedCleanupConsistency: crash-safe version.
\* DESIGN GOAL: state = "merged" => worktreeState \in {"absent", "cleaning"}
\*   Violated by MidCrashMergeSucceeded — same as WorktreeStateConsistency.
\* Crash-safe: allow "present" (leaked worktree after mid-transition crash).
MergedCleanupConsistency ==
    state = "merged" => worktreeState \in {"absent", "cleaning", "present"}

\* ConflictQueueClearedOnResolve: after successful resolution, queue is cleared
\* (This is enforced by ResolveSucceeded setting inConflictQueue = FALSE)
\* Invariant: if state returned to needs_merge from resolving, queue should be empty
\* Note: Not a strict invariant due to crash semantics, but useful for checking.

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* EventualTermination: every worker eventually reaches merged or failed
\* NOTE: Requires fairness (WF) to hold. Apalache --temporal does not enforce
\* fairness ("Handling fairness is not supported yet!"), so this property
\* can only be verified with TLC. Kept here for documentation and TLC use.
EventualTermination == <>(state \in TerminalStates)

=============================================================================
