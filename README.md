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
- Agent definition validation.
- Runtime adapter behaviour and invocation/session structs.

Run the current checks:

```sh
mix test
```
