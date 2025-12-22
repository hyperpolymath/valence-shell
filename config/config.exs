# Valence Shell Configuration
#
# This file is loaded before any dependency and is restricted
# to this project only.

import Config

# General application configuration
config :valence,
  # Sandbox root for file operations (safety boundary)
  sandbox_root: System.get_env("VALENCE_SANDBOX") || "/tmp/valence",

  # History settings
  history_limit: 1000,
  journal_retention_days: 7,

  # Agent settings
  default_agent_tier: 1,
  agent_rate_limit: 60  # ops per minute

# Logger configuration
config :logger,
  level: :info,
  format: "$time $metadata[$level] $message\n",
  metadata: [:request_id, :idempotency_key]

config :logger, :console,
  format: "$time $metadata[$level] $message\n",
  metadata: [:request_id, :idempotency_key]

# Import environment-specific config
import_config "#{config_env()}.exs"
