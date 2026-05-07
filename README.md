# Indexer

Indexer is the Elixir rewrite of Chief Wiggum. It is an agent harness
orchestrator: it prepares context, executes deterministic hooks, invokes external
agent harnesses, records JSONL state, and advances configurable pipelines.

The v1 implementation has been moved to `v1/`. The v2 contract lives in `spec/`.

Current implementation status:

- Mix/OTP application scaffold.
- Append-only JSONL event writer/reader.
- Effect outbox record helpers.
- Ordered-step pipeline schema validation.
- Effect executor with retry scheduling and git/work/control-branch effects.
- Agent definition validation, markdown rendering, completion checks, and
  supervised `ralph_loop` execution.
- Agent registry and runner that append `agent_runs.jsonl`, run deterministic
  hooks, and surface planned effects.
- Runtime facade plus generic executable adapter that append `agent_events.jsonl`
  and retry classified transient failures.
- Agent communication queries over `agent_runs.jsonl`.
- Service loader, scheduler, runner, daemon, restart policies, circuit breakers,
  and JSONL state projection.
- Work item, worker lifecycle, and change-set ledgers with merge planning.
- Control-branch import/export/publish under `.indexer/control`.
- Pipeline `commit_after` effect requests and conservative readonly restore.
- Disposable projection materializer under `.indexer/state/projections`.

Run the current checks:

```sh
mix test
```
