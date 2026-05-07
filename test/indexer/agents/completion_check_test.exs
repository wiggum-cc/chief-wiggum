defmodule Indexer.Agents.CompletionCheckTest do
  use ExUnit.Case, async: true

  alias Indexer.Agents.{CompletionCheck, Definition}

  test "file_exists check passes only for a non-empty file" do
    root = tmp_dir()
    output = Path.join(root, "result.json")
    definition = definition(%{"completion_check" => "file_exists:{{output_path}}"})
    context = %{"output_path" => output}

    assert %{"complete" => false} = CompletionCheck.evaluate(root, definition, context)

    File.write!(output, "")
    assert %{"complete" => false} = CompletionCheck.evaluate(root, definition, context)

    File.write!(output, "{}")

    assert %{"complete" => true, "gate_result" => "PASS", "path" => ^output} =
             CompletionCheck.evaluate(root, definition, context)
  end

  test "status_file check passes when no unchecked items remain" do
    root = tmp_dir()
    status_file = Path.join(root, "status.md")
    definition = definition(%{"completion_check" => "status_file:status.md"})

    File.write!(status_file, "- [x] Done\n")

    assert %{"complete" => true, "gate_result" => "PASS", "path" => ^status_file} =
             CompletionCheck.evaluate(root, definition, %{})
  end

  test "status_file check remains incomplete while unchecked items exist" do
    root = tmp_dir()
    status_file = Path.join(root, "status.md")
    definition = definition(%{"completion_check" => "status_file:status.md"})

    File.write!(status_file, "- [x] Done\n- [ ] Pending\n")

    assert %{"complete" => false, "path" => ^status_file} =
             CompletionCheck.evaluate(root, definition, %{})
  end

  test "status_file result tag can provide an explicit terminal result" do
    root = tmp_dir()
    status_file = Path.join(root, "status.md")
    definition = definition(%{"completion_check" => "status_file:status.md"})

    File.write!(status_file, "- [ ] Pending\n<result>FAIL</result>\n")

    assert %{"complete" => true, "gate_result" => "FAIL", "path" => ^status_file} =
             CompletionCheck.evaluate(root, definition, %{})
  end

  defp definition(attrs) do
    {:ok, definition} =
      Definition.from_map(
        Map.merge(
          %{
            "type" => "test.completion",
            "description" => "Completion check test",
            "required_paths" => ["workspace"],
            "valid_results" => ["PASS", "FAIL"],
            "mode" => "ralph_loop"
          },
          attrs
        )
      )

    definition
  end

  defp tmp_dir do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-completion-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
