defmodule Indexer.Pipeline.SchemaTest do
  use ExUnit.Case, async: true

  alias Indexer.Pipeline.Schema

  test "accepts ordered steps and inline handlers" do
    pipeline = %{
      name: "default",
      steps: [
        %{
          id: "audit",
          agent: "engineering.security-audit",
          max: 3,
          on_result: %{
            FIX: %{
              id: "audit-fix",
              agent: "engineering.security-fix",
              max: 2,
              on_result: %{PASS: %{jump: "audit"}}
            }
          }
        }
      ]
    }

    assert :ok = Schema.validate(pipeline)
  end

  test "rejects duplicate step ids and unknown jumps" do
    pipeline = %{
      name: "bad",
      steps: [
        %{id: "a", agent: "x.y", on_result: %{FAIL: %{jump: "missing"}}},
        %{id: "a", agent: "x.z"}
      ]
    }

    assert {:error, errors} = Schema.validate(pipeline)
    assert Enum.any?(errors, &(&1.message =~ "duplicate step id"))
    assert Enum.any?(errors, &(&1.message =~ "unknown jump target"))
  end
end
