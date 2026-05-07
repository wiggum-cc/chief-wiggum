defmodule Indexer.ConfigDefaultsTest do
  use ExUnit.Case, async: true

  test "default pipeline config validates" do
    pipeline = Indexer.Config.read_json!("config/pipelines/default.json")
    assert :ok = Indexer.Pipeline.Schema.validate(pipeline)
  end

  test "default service config validates" do
    services = Indexer.Config.read_json!("config/services.json")
    assert :ok = Indexer.Services.Schema.validate(services)
  end
end
