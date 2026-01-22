# SPDX-License-Identifier: PLMP-1.0-or-later

defmodule Mix.Tasks.Vsh.Daemon do
  @moduledoc """
  Mix task for managing the Valence Shell daemon.

  ## Usage

      # Start the daemon in foreground (useful for development)
      mix vsh.daemon start

      # Start with custom socket path
      VSH_SOCKET=/tmp/my-vsh.sock mix vsh.daemon start

      # Check daemon status
      mix vsh.daemon status

  ## Environment Variables

  - `VSH_SOCKET` - Unix socket path (default: /tmp/vsh-daemon.sock)
  - `VSH_SANDBOX` - Sandbox root directory (default: /tmp/vsh-sandbox)

  ## Integration with Zig CLI

  The daemon is required for operations that need:
  - Undo/redo functionality
  - Operation history
  - Transaction support
  - Secure deletion (obliterate)

  Simple operations (mkdir, rmdir, touch, rm, cat, ls, pwd)
  are handled directly by the Zig fast path.
  """

  use Mix.Task

  @shortdoc "Manage the Valence Shell daemon"

  @impl Mix.Task
  def run(args) do
    case args do
      ["start"] -> start_daemon()
      ["status"] -> check_status()
      ["stop"] -> stop_daemon()
      _ -> print_usage()
    end
  end

  defp start_daemon do
    Mix.shell().info("""
    Starting Valence Shell Daemon...

    Socket: #{socket_path()}
    Sandbox: #{sandbox_root()}

    Press Ctrl+C twice to stop.
    """)

    # Start the application
    Application.ensure_all_started(:vsh)

    # Keep the process running
    receive do
      :stop -> :ok
    end
  end

  defp check_status do
    path = socket_path()

    if File.exists?(path) do
      Mix.shell().info("Daemon socket exists at: #{path}")

      # Try to connect
      case :gen_tcp.connect({:local, path}, 0, [:binary, packet: :line, active: false], 1000) do
        {:ok, socket} ->
          :gen_tcp.close(socket)
          Mix.shell().info("Daemon is running and accepting connections.")

        {:error, reason} ->
          Mix.shell().error("Socket exists but connection failed: #{inspect(reason)}")
          Mix.shell().info("The daemon may have crashed. Try removing the socket and restarting.")
      end
    else
      Mix.shell().info("Daemon is not running (socket not found at #{path})")
    end
  end

  defp stop_daemon do
    path = socket_path()

    if File.exists?(path) do
      File.rm(path)
      Mix.shell().info("Daemon socket removed. If the daemon was running, it will exit.")
    else
      Mix.shell().info("Daemon is not running.")
    end
  end

  defp print_usage do
    Mix.shell().info("""
    Valence Shell Daemon

    Usage:
      mix vsh.daemon start    Start the daemon in foreground
      mix vsh.daemon status   Check if daemon is running
      mix vsh.daemon stop     Stop the daemon (remove socket)

    Environment:
      VSH_SOCKET    Socket path (default: /tmp/vsh-daemon.sock)
      VSH_SANDBOX   Sandbox root (default: /tmp/vsh-sandbox)
    """)
  end

  defp socket_path do
    System.get_env("VSH_SOCKET", "/tmp/vsh-daemon.sock")
  end

  defp sandbox_root do
    System.get_env("VSH_SANDBOX", "/tmp/vsh-sandbox")
  end
end
