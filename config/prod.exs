# Production configuration
import Config

config :valence,
  sandbox_root: System.get_env("VALENCE_SANDBOX") || raise("VALENCE_SANDBOX not set"),
  history_limit: String.to_integer(System.get_env("VALENCE_HISTORY_LIMIT") || "1000"),
  journal_retention_days: String.to_integer(System.get_env("VALENCE_JOURNAL_RETENTION") || "30")

config :logger,
  level: :info
