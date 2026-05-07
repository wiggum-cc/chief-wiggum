defmodule Indexer.Agents.DefinitionTest do
  use ExUnit.Case, async: true

  alias Indexer.Agents.Definition

  test "validates required agent fields" do
    assert {:ok, definition} =
             Definition.from_map(%{
               type: "engineering.security-audit",
               description: "Audit security issues",
               required_paths: ["workspace"],
               valid_results: ["PASS", "FIX", "FAIL"],
               mode: "ralph_loop"
             })

    assert definition.type == "engineering.security-audit"
    assert definition.result_tag == "result"
  end

  test "resume mode requires session_from" do
    assert {:error, errors} =
             Definition.from_map(%{
               type: "general.task-summarizer",
               description: "Summarize",
               required_paths: ["workspace"],
               valid_results: ["PASS"],
               mode: "resume"
             })

    assert Enum.any?(errors, &(&1.path == "$.session_from"))
  end
end
