# JSON Schemas

These schema files define the structure of Chief Wiggum's configuration files.
They are **documentation-only** and are not used for runtime validation.

## Files

| Schema | Validates |
|--------|-----------|
| `agents.schema.json` | `config/agents.json` |
| `config.schema.json` | `config/config.json` and `.ralph/config.json` |
| `pipeline.schema.json` | `config/pipelines/*.json` |
| `service.schema.json` | `config/services.json` |

## CI Validation (Optional)

To wire these schemas into CI validation, install
[check-jsonschema](https://github.com/python-jsonschema/check-jsonschema) and add:

```bash
check-jsonschema --schemafile config/schemas/agents.schema.json config/agents.json
check-jsonschema --schemafile config/schemas/pipeline.schema.json config/pipelines/default.json
check-jsonschema --schemafile config/schemas/config.schema.json config/config.json
check-jsonschema --schemafile config/schemas/service.schema.json config/services.json
```
