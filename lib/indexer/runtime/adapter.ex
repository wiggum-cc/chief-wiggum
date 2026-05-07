defmodule Indexer.Runtime.Adapter do
  @moduledoc """
  Behaviour implemented by external agent harness adapters.
  """

  alias Indexer.Runtime.{Invocation, Session}

  @callback init(map()) :: {:ok, map()} | {:error, term()}
  @callback validate_config(map()) :: :ok | {:error, term()}
  @callback capabilities(map()) :: map()
  @callback invoke(Invocation.t()) :: {:ok, Session.t()} | {:error, term()}
  @callback build_exec_args(Invocation.t()) :: {:ok, [String.t()]} | {:error, term()}
  @callback build_resume_args(Session.t(), Invocation.t()) ::
              {:ok, [String.t()]} | {:error, term()}
  @callback classify_error(term(), map()) :: :retryable | :permanent | :operator_required
  @callback extract_text(map()) :: {:ok, String.t()} | {:error, term()}
  @callback extract_session_id(map()) :: {:ok, String.t() | nil} | {:error, term()}
  @callback normalize_event(term()) :: {:ok, map()} | :ignore | {:error, term()}

  @callback supports_sessions?(map()) :: boolean()
  @callback usage_update(map(), map()) :: :ok | {:error, term()}
  @callback rate_limit_check(map()) :: :ok | {:error, term()}
  @callback rate_limit_wait(map()) :: :ok | {:error, term()}
  @callback generate_session_id(map()) :: String.t()
  @callback backend_name() :: String.t()
  @callback cancel_turn(Session.t(), map()) :: :ok | {:error, term()}

  @optional_callbacks supports_sessions?: 1,
                      usage_update: 2,
                      rate_limit_check: 1,
                      rate_limit_wait: 1,
                      generate_session_id: 1,
                      backend_name: 0,
                      cancel_turn: 2
end
