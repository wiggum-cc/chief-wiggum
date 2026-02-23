# Intent DSL Reference (Distilled Subset)

This reference covers the Intent DSL constructs relevant to codebase pattern distillation. For the full language specification, see the Intent project documentation.

## Top-Level Constructs

The Intent language supports these top-level declarations. Distillation primarily uses `distilled pattern`, `distilled constraint`, and `rationale`:

| Construct | Purpose | Distillation Use |
|-----------|---------|------------------|
| `system Name { ... }` | Primary container for specs | Context only |
| `component Name { ... }` | Structural unit | Context only |
| `behavior Name { ... }` | State machine (transpiles to TLA+) | Embedded in distilled patterns |
| `pattern Name<T> { ... }` | Reusable parameterized behavior | Context only |
| `constraint Name { ... }` | Structural architectural rules | Embedded in distilled constraints |
| `rationale Name { ... }` | Design decision capture | Use for observed design decisions |
| `predicate Name(args) { ... }` | User-defined predicate macros | Use in distilled constraints |
| `distilled pattern Name { ... }` | Extracted behavioral pattern | **Primary output** |
| `distilled constraint Name { ... }` | Extracted structural rule | **Primary output** |
| `event Name` | Event type declaration | Context only |
| `message Channel.Name: TypeSpec` | Typed message for channels | Context only |
| `function Name(params) -> Type { ... }` | Behavior function | Context only |

---

## Distilled Pattern

Captures behavioral patterns observed in code.

```intent
distilled pattern <Name> {
    source: "<glob>"           // where the pattern was found (required)
    commit: "<hash>"           // git commit at extraction time (required)
    extracted: "<date>"        // ISO date of extraction
    confidence: <0.0-1.0>     // extraction certainty

    observation {
        "<human-readable description of what was observed>"
    }

    parameters {
        <name>: <Type> { default: <value> }
    }

    behavior {
        variables {
            <name>: <Type> = <initial_value>
        }

        states {
            <name> { initial: true }
            <name>
            <name> { terminal: true }
        }

        transitions {
            <from> -> <to> on <event>
            <from> -> <to> on <event> where { <condition> }
            <from> -> <to> on <event> effect { <action> }
            <from> -> <to> on <event> after { <duration> }
            * -> <to> on <event>                           // wildcard source
            [s1, s2] -> <to> on <event>                    // multi-source
            <from> -> fork { s1, s2 } on <event>           // parallel fork
            join { s1, s2 } -> <to> on <event>             // parallel join
        }

        composes [BehaviorA, BehaviorB]    // composition

        property <name> {
            <temporal_expression>
        }

        fairness {
            weak(<from> -> <to>)
            strong(<from> -> <to>)
        }
    }

    applies_to { <scope_glob> }  // suggested enforcement scope
}
```

### Required Fields

| Field | Description |
|-------|-------------|
| `source` | Glob pattern indicating where the pattern was found |
| `commit` | Git commit hash at extraction time |

### Optional Fields

| Field | Description |
|-------|-------------|
| `extracted` | ISO date string (e.g., `"2026-02-23"`) |
| `confidence` | Float between 0.0 and 1.0 |
| `observation` | Human-readable description block |
| `parameters` | Named parameters with types and defaults |
| `behavior` | State machine definition |
| `applies_to` | Scope glob for suggested enforcement |

### Parameter Types

- `Int` - Integer values
- `Nat` - Natural numbers (non-negative integers)
- `Float` - Floating point values
- `String` - String values
- `Bool` - Boolean values
- `Duration` - Time duration values (e.g., `100ms`, `30s`, `5m`)
- `Set(T)` - Set of elements of type T
- `Seq(T)` - Sequence of elements of type T

---

## Distilled Constraint

Captures structural rules observed in code.

```intent
distilled constraint <Name> {
    source: "<glob>"
    commit: "<hash>"
    confidence: <0.0-1.0>

    observation {
        "<human-readable description of what was observed>"
    }

    constraint {
        <predicate_expression>
    }
}
```

### Built-in Predicates

| Predicate | Meaning |
|-----------|---------|
| `A.depends(B)` | A has direct import/use of B (tracks explicit `use` statements) |
| `A.depends_transitively(B)` | A depends on B through a chain of dependencies |
| `A.references(B)` | A mentions type B anywhere in source (includes fully-qualified paths, does not require import) |
| `A.implements(T)` | A implements trait/interface T (detected via `impl Trait for Type`) |
| `A.contains(B)` | B is lexically nested within A (module contains submodule) |

### Operators

| Operator | Meaning |
|----------|---------|
| `!` | Negation |
| `&&` | Conjunction (and) |
| `\|\|` | Disjunction (or) |
| `=>` | Implication (if...then) |
| `<=>` | Biconditional (if and only if) |

### Quantifiers

```intent
forall x in <set>: <predicate(x)>
exists x in <set>: <predicate(x)>
```

### Scope Expressions

| Expression | Meaning |
|------------|---------|
| `services` | Named module/component |
| `[A, B, C]` | Explicit entity list |
| `all` | All components in scope |
| `{ x \| x matches *Client }` | Glob-based filter set |
| `{ x \| condition }` | Expression-based filter |
| `A \| B` | Set union |
| `A & B` | Set intersection |
| `A \ B` | Set difference |

### Comparison Constraints

Use the `check` keyword for value comparisons:

```intent
constraint performance_bounds {
    forall op in [Operation]: check op.latency < 100
}
```

### Constraint Suppression

Temporarily suppress a rule for specific entities:

```intent
constraint layering {
    !Storage.depends(API) allow {
        exception: [LegacyStorage]
        reason: "Migration in progress"
        expires: "2026-06-01"
        tracking: "JIRA-1234"
    }
}
```

---

## User-Defined Predicates

Compose built-in predicates into reusable macros:

```intent
predicate isolated(source, target) {
    !source.depends(target) && !source.references(target)
}

// Usage in a distilled constraint:
distilled constraint ModuleBoundaries {
    source: "src/**/*.rs"
    commit: "a1b2c3d"
    confidence: 0.88

    observation {
        "Services and storage modules are fully isolated."
    }

    constraint {
        isolated(services, storage_backends)
    }
}
```

Predicates are macro-expanded at parse time. They can only compose built-in predicates, not define new structural analysis logic.

---

## Behavior Block

Full state machine definition. Behaviors transpile to TLA+ for formal verification.

```intent
behavior <Name> {
    variables {
        balance: Nat = 0
        pending: Set(TxId) = {}
        retries: Nat = 0
    }

    parameters {
        max_retries: Int { default: 3 }
    }

    states {
        pending   { initial: true }
        active
        completed { terminal: true }
        failed    { terminal: true }
    }

    transitions {
        pending -> active      on start
        active -> completed    on finish     where { all_checks_pass }
        active -> failed       on error
        active -> active       on retry      where { retries < max_retries }
                                             effect { retries = retries + 1 }
        active -> waiting      on pause      after { 30s }
        * -> failed            on fatal_error           // wildcard: any state
        [active, waiting] -> cancelled on cancel        // multi-source
    }

    // Parallel composition
    composes [FlowA, FlowB]

    // Temporal properties
    property eventual_completion {
        always(pending => eventually(completed | failed))
    }

    fairness {
        weak(pending -> active | failed)
        strong(active -> completed | failed)
    }
}
```

### State Modifiers

| Modifier | Meaning |
|----------|---------|
| `initial: true` | Entry state (exactly one required per behavior) |
| `terminal: true` | Final state (no outgoing transitions allowed) |

### Transition Clauses

| Clause | Purpose |
|--------|---------|
| `on <event>` | Event that triggers the transition |
| `where { <condition> }` | Guard condition (transition only fires if true) |
| `effect { <statements> }` | Side effects (simultaneous execution semantics) |
| `after { <duration> }` | Timing constraint on the transition |

### Transition Sources

| Syntax | Meaning |
|--------|---------|
| `state -> target on event` | Single source state |
| `* -> target on event` | Wildcard: matches any current state |
| `[s1, s2] -> target on event` | Multi-source: any of the listed states |

### Fork/Join (Parallel Composition)

```intent
pending -> fork { processing, notification } on start
join { processing, notification } -> completed on both_done
```

### Effect Semantics

All statements in an effect block execute **simultaneously** (not sequentially). Reads use current state values; writes target the next state.

```intent
effect {
    counter = counter + 1              // reads current counter
    emit PaymentProcessed(amount)      // event emission
    send Channel.Message(n: counter)   // sends current counter (not incremented)
}
```

Available effect actions:
- `variable = expr` — assignment (next-state)
- `emit EventName(args)` — publish event
- `send Channel.Message(args)` — send typed message
- `receive Channel.Message` — receive message

### Variables

Explicit declaration with type and initial value:

```intent
variables {
    count: Nat = 0
    enabled: Bool = true
    items: Seq(String) = []
    seen: Set(Id) = {}
}
```

Type inference is available for prototyping but explicit declarations are preferred:
- `*count` / `*num` / `*size` → `Nat`
- `*enabled` / `*active` → `Bool`
- `*list` / `*queue` → `Seq(...)`
- `*set` → `Set(...)`

---

## Temporal Properties

Temporal operators for specifying liveness and safety properties:

| Operator | Semantics |
|----------|-----------|
| `always(P)` | P holds in every state (safety) |
| `eventually(P)` | P holds in some future state (liveness) |
| `next(P)` | P holds in the next state |
| `P until Q` | P holds until Q becomes true (Q must eventually hold) |
| `P releases Q` | Q holds until P becomes true (weak: Q can hold forever) |
| `P weak_until Q` | P holds until Q, but Q need not eventually occur |
| `P strong_releases Q` | Release but P must eventually occur |
| `P <=> Q` | Biconditional |

Cardinality in distributed contexts:
```intent
property single_leader {
    always(count(leader) <= 1)
}
```

---

## Non-Functional Constraints

Parsed and extracted to benchmark configuration (not formally verified):

```intent
constraint performance {
    p99(settle) < 100ms
    p95(validate) < 10ms
    throughput(system) > 10_000 / s
    memory < 4GB
    cpu < 2
}
```

| Metric | Unit | Meaning |
|--------|------|---------|
| `p50(op)`, `p95(op)`, `p99(op)` | Duration | Latency percentiles |
| `throughput(scope)` | N/s, N/m, N/h | Operations per time unit |
| `memory` | MB, GB | Peak memory usage |
| `cpu` | cores (float) | CPU utilization |

---

## Rationale (Design Decision Capture)

Use `rationale` to capture observed design decisions with traceability:

```intent
rationale <Name> {
    discovered: "<date>"
    source: "<origin>"

    observation {
        "<what was observed>"
    }

    recommendation {
        constraint <name> {
            <rules>
        }
    }

    decided because {
        "<reason 1>"
        "<reason 2>"
    }

    rejected {
        <alternative_name>: "<why rejected>"
    }

    revisit when {
        "<condition for revisiting>"
    }

    traces_to {
        file: "<path>"
        target: { kind: "<Struct|Function|Module>", name: "<name>" }
        path: "<member>"
        commit: "<hash>"
    }
}
```

All fields except the name are optional. For distillation, `rationale` is useful when you observe a clear design decision that isn't captured by a pattern or constraint alone.

---

## Complete Examples

### Example 1: Retry Pattern with Variables

```intent
distilled pattern RetryWithBackoff {
    source: "crates/client/src/*.rs"
    commit: "a1b2c3d"
    extracted: "2026-02-15"
    confidence: 0.85

    observation {
        "Exponential backoff pattern found in 5 client implementations.
         Each retries up to max_attempts times with a multiplied delay."
    }

    parameters {
        max_attempts: Int { default: 3 }
        backoff_factor: Float { default: 2.0 }
    }

    behavior {
        variables {
            attempt: Nat = 0
        }

        states {
            idle       { initial: true }
            attempting
            waiting
            succeeded  { terminal: true }
            failed     { terminal: true }
        }

        transitions {
            idle -> attempting       on request
            attempting -> succeeded  on success
            attempting -> waiting    on transient_error  where { attempt < max_attempts }
                                                        effect { attempt = attempt + 1 }
            attempting -> failed     on transient_error  where { attempt >= max_attempts }
            attempting -> failed     on permanent_error
            waiting -> attempting    on backoff_elapsed
        }

        property eventual_resolution {
            always(attempting => eventually(succeeded | failed))
        }
    }

    applies_to { *Client.call }
}
```

### Example 2: Layering Constraint with Suppression

```intent
distilled constraint ObservedLayering {
    source: "src/**/*.rs"
    commit: "b2c3d4e"
    confidence: 0.92

    observation {
        "All service modules avoid direct storage dependencies.
         Access goes through repository interfaces."
    }

    constraint {
        !services.depends(storage_backends) allow {
            exception: [LegacyService]
            reason: "Pre-refactor code, tracked for migration"
            tracking: "TASK-042"
        }
    }
}
```

### Example 3: Naming Convention Constraint

```intent
distilled constraint HandlerNaming {
    source: "src/handlers/**/*.ts"
    commit: "c3d4e5f"
    confidence: 0.78

    observation {
        "All HTTP handler files follow the pattern *Handler.ts
         and export a single default function."
    }

    constraint {
        forall h in handlers: h matches *Handler
    }
}
```

### Example 4: State Machine with Wildcard and Fork/Join

```intent
distilled pattern WorkerLifecycle {
    source: "lib/worker/**/*.sh"
    commit: "d4e5f6a"
    extracted: "2026-02-23"
    confidence: 0.90

    observation {
        "Workers follow a spawned -> fix/merge cycle with parallel
         notification. All states can transition to failed on fatal error."
    }

    behavior {
        variables {
            merge_attempts: Nat = 0
        }

        states {
            none         { initial: true }
            needs_merge
            merging
            needs_fix
            fixing
            merged       { terminal: true }
            failed       { terminal: true }
        }

        transitions {
            none -> needs_merge         on spawned
            needs_merge -> merging      on merge_start
            merging -> merged           on merge_succeeded
            merging -> needs_fix        on merge_conflict
                                        effect { merge_attempts = merge_attempts + 1 }
            needs_fix -> fixing         on fix_started
            fixing -> needs_merge       on fix_pass
            fixing -> needs_fix         on fix_fail
            * -> failed                 on fatal_error
        }

        property eventual_termination {
            always(needs_merge => eventually(merged | failed))
        }
    }

    applies_to { worker-* }
}
```

### Example 5: Design Decision Rationale

```intent
rationale EventDrivenLifecycle {
    discovered: "2026-02-23"
    source: "Code analysis"

    observation {
        "The worker lifecycle uses an event-driven state machine loaded from
         JSON config rather than hardcoded transitions in bash. This allows
         adding states and transitions without modifying engine code."
    }

    decided because {
        "Decouples state machine definition from engine implementation."
        "JSON spec is the single source of truth for valid transitions."
    }

    rejected {
        hardcoded_states: "Requires code changes for every new state."
        database_driven: "Overkill for a bash-based system."
    }

    traces_to {
        file: "config/worker-lifecycle.json"
        target: { kind: "Module", name: "lifecycle-engine" }
        commit: "d4e5f6a"
    }
}
```

### Example 6: User-Defined Predicate in Constraint

```intent
predicate isolated(source, target) {
    !source.depends(target) && !source.references(target)
}

distilled constraint SchedulerIsolation {
    source: "lib/scheduler/**/*.sh"
    commit: "e5f6a7b"
    confidence: 0.85

    observation {
        "Scheduler modules are fully isolated from git operations.
         All git interaction goes through lib/git/ interfaces."
    }

    constraint {
        isolated(scheduler, git)
    }
}
```

---

## Verification Levels

Distilled artifacts operate at the `advisory` level by default:

| Level | Description | Method |
|-------|-------------|--------|
| `sound` | Formally verified | TLA+/Apalache model checking |
| `checked` | Statically analyzed | Structural predicates via `syn` |
| `advisory` | Best-effort observation | Pattern matching, heuristics |
| `benchmark` | Empirical measurement | CI benchmark execution |

The `confidence` field indicates extraction certainty. Distilled patterns are observations, not prescriptions — they describe what IS, not what SHOULD BE.

---

## Linting Rules

`intent lint` validates distilled specs against 21+ rules covering:

- **Syntax**: Parse errors, malformed constructs
- **Semantics**: Undefined identifiers, invalid transitions, unreachable states
- **State machines**: Missing initial state, multiple initial states, transitions from terminal states
- **Style**: PascalCase for names, snake_case for states
- **Dead code**: Unused components
- **Cycles**: Circular dependency detection
- **Types**: Variable type consistency
