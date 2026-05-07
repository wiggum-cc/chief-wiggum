defmodule Indexer.Agents.CompletionCheck do
  @moduledoc """
  Deterministic completion checks for iterative agents.

  These checks preserve the useful v1 contract while keeping the logic inside
  Indexer. A completion check can stop a `ralph_loop` without asking the model for
  another turn, and can also provide the gate result used by pipeline routing.
  """

  alias Indexer.Agents.Result

  @type evaluation :: %{required(String.t()) => term()}

  @doc """
  Evaluates an agent completion check against the current project/workspace state.
  """
  @spec evaluate(Path.t(), map() | struct(), map()) :: evaluation()
  def evaluate(project_root, definition, context)
      when is_binary(project_root) and is_map(context) do
    definition
    |> completion_check()
    |> do_evaluate(project_root, definition, context)
  end

  defp do_evaluate("result_tag", _project_root, _definition, _context) do
    base("result_tag", false, [
      %{"level" => "debug", "message" => "result_tag checks are evaluated from runtime text"}
    ])
  end

  defp do_evaluate("status_file:" <> path_template, project_root, definition, context) do
    path = resolve_path(project_root, context, path_template)

    cond do
      not File.exists?(path) ->
        base("status_file", false, [
          %{"level" => "debug", "message" => "status file does not exist", "path" => path}
        ])
        |> Map.put("path", path)

      File.dir?(path) ->
        base("status_file", false, [
          %{"level" => "warning", "message" => "status file path is a directory", "path" => path}
        ])
        |> Map.put("path", path)

      true ->
        text = File.read!(path)
        gate_result = Result.extract_gate_result(text, definition)
        has_terminal_result? = terminal_result?(gate_result, definition)
        has_pending? = Regex.match?(~r/^\s*[-*]\s+\[ \]/m, text)
        complete? = has_terminal_result? or not has_pending?

        base("status_file", complete?, [
          %{
            "level" => "info",
            "message" => "status file evaluated",
            "path" => path,
            "pending" => has_pending?
          }
        ])
        |> Map.put("path", path)
        |> maybe_put_gate_result(status_file_gate_result(gate_result, complete?, definition))
    end
  end

  defp do_evaluate("file_exists:" <> path_template, project_root, definition, context) do
    path = resolve_path(project_root, context, path_template)
    complete? = File.regular?(path) and File.stat!(path).size > 0

    base("file_exists", complete?, [
      %{
        "level" => "info",
        "message" => "file existence evaluated",
        "path" => path,
        "exists" => File.exists?(path)
      }
    ])
    |> Map.put("path", path)
    |> maybe_put_gate_result(if(complete?, do: default_success_result(definition)))
  end

  defp do_evaluate("hook:" <> hook_name, _project_root, _definition, _context) do
    base("hook", false, [
      %{
        "level" => "debug",
        "message" => "hook completion checks are evaluated by the agent runner",
        "hook" => String.trim(hook_name)
      }
    ])
    |> Map.put("hook", String.trim(hook_name))
  end

  defp do_evaluate("artifact_schema:" <> kind, _project_root, _definition, _context) do
    base("artifact_schema", false, [
      %{
        "level" => "warning",
        "message" => "artifact schema completion checks are not available yet",
        "kind" => String.trim(kind)
      }
    ])
    |> Map.put("kind", String.trim(kind))
  end

  defp do_evaluate(other, _project_root, _definition, _context) do
    base("unknown", false, [
      %{"level" => "warning", "message" => "unknown completion check", "check" => other}
    ])
  end

  defp base(type, complete?, diagnostics) do
    %{
      "type" => type,
      "complete" => complete?,
      "diagnostics" => diagnostics
    }
  end

  defp completion_check(%_{} = definition),
    do: Map.get(definition, :completion_check, "result_tag")

  defp completion_check(%{} = definition),
    do: Map.get(definition, "completion_check", "result_tag")

  defp completion_check(_definition), do: "result_tag"

  defp resolve_path(project_root, context, template) do
    rendered =
      template
      |> String.trim()
      |> Indexer.Agents.Markdown.render_template(context)

    if Path.type(rendered) == :absolute do
      rendered
    else
      context
      |> workspace_path(project_root)
      |> Path.join(rendered)
    end
  end

  defp workspace_path(context, project_root) do
    Map.get(context, "workspace") || Map.get(context, "project_root") || project_root
  end

  defp status_file_gate_result(gate_result, complete?, definition) do
    cond do
      terminal_result?(gate_result, definition) -> gate_result
      complete? -> default_success_result(definition)
      true -> nil
    end
  end

  defp terminal_result?(gate_result, definition) do
    gate_result != "UNKNOWN" and gate_result in valid_results(definition)
  end

  defp default_success_result(definition) do
    results = valid_results(definition)

    cond do
      "PASS" in results -> "PASS"
      results != [] -> hd(results)
      true -> "UNKNOWN"
    end
  end

  defp valid_results(%_{} = definition), do: Map.get(definition, :valid_results, [])
  defp valid_results(%{} = definition), do: Map.get(definition, "valid_results", [])
  defp valid_results(_definition), do: []

  defp maybe_put_gate_result(evaluation, nil), do: evaluation

  defp maybe_put_gate_result(evaluation, gate_result) do
    Map.put(evaluation, "gate_result", gate_result)
  end
end
