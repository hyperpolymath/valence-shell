# Runtime configuration (loaded at runtime, not compile time)
import Config

if config_env() == :prod do
  # Production runtime configuration
  # These can be overridden by environment variables at runtime

  config :valence,
    sandbox_root: System.get_env("VALENCE_SANDBOX") || "/var/lib/valence"
end
