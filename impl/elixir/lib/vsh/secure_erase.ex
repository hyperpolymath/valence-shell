# SPDX-License-Identifier: PLMP-1.0-or-later
defmodule VSH.SecureErase do
  @moduledoc """
  Hardware-based secure erase for SSDs using NIST SP 800-88 Purge methods.

  This module provides:
  - ATA Secure Erase (SATA SSDs)
  - NVMe Format with crypto erase
  - NVMe Sanitize (block erase)

  All operations include comprehensive safety confirmations.
  """

  use Rustler, otp_app: :vsh, crate: "vsh_nif"

  @type drive_type :: :hdd | :sata_ssd | :nvme_ssd | :unknown
  @type result :: {:ok, any()} | {:error, String.t()}

  # NIF stubs - replaced at runtime by Rust implementations
  def detect_drive_type_nif(_device), do: :erlang.nif_error(:nif_not_loaded)
  def check_ata_support_nif(_device), do: :erlang.nif_error(:nif_not_loaded)
  def check_nvme_sanitize_support_nif(_device), do: :erlang.nif_error(:nif_not_loaded)
  def ata_secure_erase_nif(_device, _enhanced), do: :erlang.nif_error(:nif_not_loaded)
  def nvme_format_crypto_nif(_device), do: :erlang.nif_error(:nif_not_loaded)
  def nvme_sanitize_nif(_device, _block_erase), do: :erlang.nif_error(:nif_not_loaded)

  # Public API with confirmation

  @doc """
  Detect drive type (HDD, SATA SSD, NVMe SSD, Unknown).

  ## Examples

      iex> VSH.SecureErase.detect_drive_type("/dev/sda")
      {:ok, :sata_ssd}

      iex> VSH.SecureErase.detect_drive_type("/dev/nvme0n1")
      {:ok, :nvme_ssd}
  """
  @spec detect_drive_type(String.t()) :: {:ok, drive_type()} | {:error, String.t()}
  def detect_drive_type(device) do
    case detect_drive_type_nif(device) do
      {:ok, "hdd"} -> {:ok, :hdd}
      {:ok, "sata_ssd"} -> {:ok, :sata_ssd}
      {:ok, "nvme_ssd"} -> {:ok, :nvme_ssd}
      {:ok, "unknown"} -> {:ok, :unknown}
      {:error, msg} -> {:error, msg}
      other -> other
    end
  end

  @doc """
  Check if device supports ATA Secure Erase.

  ## Examples

      iex> VSH.SecureErase.check_ata_support("/dev/sda")
      {:ok, true}
  """
  @spec check_ata_support(String.t()) :: result()
  def check_ata_support(device) do
    check_ata_support_nif(device)
  end

  @doc """
  Check if device supports NVMe Sanitize.

  ## Examples

      iex> VSH.SecureErase.check_nvme_sanitize_support("/dev/nvme0n1")
      {:ok, true}
  """
  @spec check_nvme_sanitize_support(String.t()) :: result()
  def check_nvme_sanitize_support(device) do
    check_nvme_sanitize_support_nif(device)
  end

  @doc """
  Perform ATA Secure Erase on SATA SSD.

  **CRITICAL WARNING:** This erases the ENTIRE device!

  Includes safety checks:
  - System drive detection (aborts if true)
  - Mount point checking
  - User confirmation required

  ## Options

  - `enhanced` - Use enhanced erase (recommended)

  ## Examples

      iex> VSH.SecureErase.ata_secure_erase("/dev/sdb", enhanced: true)
      {:ok, "erase_complete"}
  """
  @spec ata_secure_erase(String.t(), keyword()) :: result()
  def ata_secure_erase(device, opts \\ []) do
    enhanced = Keyword.get(opts, :enhanced, true)

    with {:ok, _} <- confirm_device_erase(device, "ATA Secure Erase") do
      ata_secure_erase_nif(device, enhanced)
    end
  end

  @doc """
  Perform NVMe Format with cryptographic erase.

  **WARNING:** This erases the ENTIRE namespace!

  Fast method using encryption key destruction.

  ## Examples

      iex> VSH.SecureErase.nvme_format_crypto("/dev/nvme0n1")
      {:ok, "erase_complete"}
  """
  @spec nvme_format_crypto(String.t()) :: result()
  def nvme_format_crypto(device) do
    with {:ok, _} <- confirm_device_erase(device, "NVMe Format (Crypto)") do
      nvme_format_crypto_nif(device)
    end
  end

  @doc """
  Perform NVMe Sanitize with block erase.

  **WARNING:** This erases the ENTIRE device including over-provisioned space!

  Slow but thorough method for maximum security.

  ## Options

  - `block_erase` - Use block erase (default: true)

  ## Examples

      iex> VSH.SecureErase.nvme_sanitize("/dev/nvme0n1")
      {:ok, "erase_complete"}
  """
  @spec nvme_sanitize(String.t(), keyword()) :: result()
  def nvme_sanitize(device, opts \\ []) do
    block_erase = Keyword.get(opts, :block_erase, true)

    with {:ok, _} <- confirm_device_erase(device, "NVMe Sanitize") do
      nvme_sanitize_nif(device, block_erase)
    end
  end

  # Private confirmation logic

  defp confirm_device_erase(device, method) do
    # Get device info
    case get_device_info(device) do
      {:ok, info} -> display_warning_and_confirm(device, method, info)
      {:error, reason} -> {:error, reason}
    end
  end

  defp get_device_info(device) do
    # Check if system drive
    with {:ok, root_device} <- get_root_device(),
         is_system <- String.starts_with?(root_device, device),
         {:ok, mounts} <- get_mounted_partitions(device),
         {:ok, size} <- get_device_size(device),
         {:ok, drive_type} <- detect_drive_type(device) do
      {:ok,
       %{
         device: device,
         drive_type: drive_type,
         size: size,
         mounts: mounts,
         is_system_drive: is_system
       }}
    end
  end

  defp get_root_device do
    case System.cmd("df", ["/"], stderr_to_stdout: true) do
      {output, 0} ->
        [_header | lines] = String.split(output, "\n", trim: true)
        case lines do
          [line | _] ->
            [device | _] = String.split(line, " ", trim: true)
            {:ok, device}
          _ ->
            {:error, "Failed to get root device"}
        end
      _ ->
        {:error, "Failed to run df command"}
    end
  end

  defp get_mounted_partitions(device) do
    case System.cmd("lsblk", ["-no", "NAME,MOUNTPOINT", device], stderr_to_stdout: true) do
      {output, 0} ->
        mounts =
          output
          |> String.split("\n", trim: true)
          |> Enum.drop(1)  # Skip device itself
          |> Enum.map(&String.split(&1, " ", trim: true))
          |> Enum.filter(fn parts -> length(parts) >= 2 and Enum.at(parts, 1) != "" end)
          |> Enum.map(fn [name, mount | _] -> {"/dev/#{name}", mount} end)

        {:ok, mounts}
      _ ->
        {:ok, []}
    end
  end

  defp get_device_size(device) do
    case System.cmd("lsblk", ["-dno", "SIZE", device], stderr_to_stdout: true) do
      {size, 0} -> {:ok, String.trim(size)}
      _ -> {:ok, "unknown"}
    end
  end

  defp display_warning_and_confirm(device, method, info) do
    IO.puts("")
    IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <>
      "🚨 CRITICAL WARNING - DEVICE-LEVEL SECURE ERASE 🚨" <> IO.ANSI.reset())
    IO.puts("")
    IO.puts(IO.ANSI.red() <> String.duplicate("═", 60) <> IO.ANSI.reset())
    IO.puts("")
    IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <>
      "  THIS WILL ERASE THE ENTIRE DEVICE!" <> IO.ANSI.reset())
    IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <>
      "  ALL DATA ON THE DEVICE WILL BE PERMANENTLY DESTROYED!" <> IO.ANSI.reset())
    IO.puts("")
    IO.puts(IO.ANSI.red() <> String.duplicate("═", 60) <> IO.ANSI.reset())
    IO.puts("")
    IO.puts("  Device:   #{IO.ANSI.bright() <> IO.ANSI.white()}#{device}#{IO.ANSI.reset()}")
    IO.puts("  Type:     #{IO.ANSI.yellow()}#{info.drive_type}#{IO.ANSI.reset()}")
    IO.puts("  Size:     #{IO.ANSI.yellow()}#{info.size}#{IO.ANSI.reset()}")
    IO.puts("  Method:   #{IO.ANSI.cyan()}#{method} (NIST SP 800-88 Purge)#{IO.ANSI.reset()}")
    IO.puts("")

    # Display mounts
    if length(info.mounts) > 0 do
      IO.puts("  Mounted partitions:")
      Enum.each(info.mounts, fn {partition, mount_point} ->
        IO.puts("    #{IO.ANSI.red()}#{partition}#{IO.ANSI.reset()} → " <>
          "#{IO.ANSI.white()}#{mount_point}#{IO.ANSI.reset()}")
      end)
      IO.puts("")
    end

    # Safety checks
    IO.puts(IO.ANSI.bright() <> IO.ANSI.yellow() <> "  SAFETY CHECKS:" <> IO.ANSI.reset())

    system_check = if info.is_system_drive do
      IO.ANSI.bright() <> IO.ANSI.red() <> "❌ SYSTEM DRIVE DETECTED!" <> IO.ANSI.reset()
    else
      IO.ANSI.green() <> "✓ Not system drive" <> IO.ANSI.reset()
    end
    IO.puts("    #{system_check}")

    mount_check = if length(info.mounts) == 0 do
      IO.ANSI.green() <> "✓ Device unmounted" <> IO.ANSI.reset()
    else
      IO.ANSI.bright() <> IO.ANSI.red() <> "⚠️  Device has mounted partitions!" <> IO.ANSI.reset()
    end
    IO.puts("    #{mount_check}")
    IO.puts("")

    # Abort if system drive
    if info.is_system_drive do
      IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <>
        "❌ ABORTED: Cannot erase system drive!" <> IO.ANSI.reset())
      IO.puts("")
      {:error, "Cannot erase system drive"}
    else
      # Check for mounted partitions
      if length(info.mounts) > 0 do
        IO.puts(IO.ANSI.bright() <> IO.ANSI.yellow() <>
          "⚠️  WARNING: Device has mounted partitions!" <> IO.ANSI.reset())
        IO.puts("   You must unmount all partitions before secure erase.")
        IO.puts("")

        if prompt_yes_no("Attempt to unmount automatically?") do
          # Try to unmount
          case unmount_device(info.mounts) do
            :ok -> proceed_with_confirmation(device)
            {:error, reason} ->
              IO.puts(IO.ANSI.red() <> "Failed to unmount: #{reason}" <> IO.ANSI.reset())
              {:error, "Device has mounted partitions"}
          end
        else
          {:error, "Device has mounted partitions"}
        end
      else
        proceed_with_confirmation(device)
      end
    end
  end

  defp proceed_with_confirmation(device) do
    IO.puts(IO.ANSI.red() <> String.duplicate("═", 60) <> IO.ANSI.reset())
    IO.puts("")
    IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <> "  FINAL CONFIRMATION REQUIRED" <> IO.ANSI.reset())
    IO.puts("")
    IO.write("  Type the device name exactly to confirm: ")

    input = IO.gets("") |> String.trim()

    if input == device do
      IO.puts("")
      IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <> "⚠️  LAST CHANCE TO ABORT!" <> IO.ANSI.reset())

      if prompt_yes_no("PERMANENTLY ERASE ALL DATA?") do
        IO.puts("")
        {:ok, :confirmed}
      else
        IO.puts("")
        IO.puts(IO.ANSI.yellow() <> "❌ Operation cancelled by user" <> IO.ANSI.reset())
        {:error, "User cancelled operation"}
      end
    else
      IO.puts("")
      IO.puts(IO.ANSI.bright() <> IO.ANSI.red() <>
        "❌ Device name mismatch - operation CANCELLED" <> IO.ANSI.reset())
      IO.puts("")
      {:error, "Device name mismatch"}
    end
  end

  defp unmount_device(mounts) do
    results = Enum.map(mounts, fn {partition, _} ->
      System.cmd("umount", [partition], stderr_to_stdout: true)
    end)

    if Enum.all?(results, fn {_, code} -> code == 0 end) do
      :ok
    else
      {:error, "Failed to unmount all partitions"}
    end
  end

  defp prompt_yes_no(prompt) do
    IO.write("  #{prompt} [y/N]: ")

    case IO.gets("") |> String.trim() |> String.downcase() do
      "y" -> true
      "yes" -> true
      _ -> false
    end
  end
end
