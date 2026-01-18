# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH.Application do
  @moduledoc """
  Valence Shell OTP Application

  Supervises:
  - VSH.State - Operation history and state management
  - VSH.Daemon - Unix socket server for client connections
  """

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {VSH.State, root: sandbox_root()},
      {VSH.Daemon, socket_path: socket_path()}
    ]

    opts = [strategy: :one_for_one, name: VSH.Supervisor]
    Supervisor.start_link(children, opts)
  end

  defp sandbox_root do
    System.get_env("VSH_SANDBOX", "/tmp/vsh-sandbox")
  end

  defp socket_path do
    System.get_env("VSH_SOCKET", "/tmp/vsh-daemon.sock")
  end
end
