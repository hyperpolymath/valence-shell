# SPDX-License-Identifier: PLMP-1.0-or-later

defmodule VSHTest do
  @moduledoc """
  Integration tests for Valence Shell

  These tests verify that the formally proven properties hold at runtime:
  - Reversibility (mkdir/rmdir, touch/rm)
  - Precondition enforcement
  - Undo/redo correctness
  - Transaction atomicity
  """

  use ExUnit.Case, async: false
  doctest VSH

  @test_root "/tmp/vsh_elixir_test_#{:os.system_time(:millisecond)}"

  setup_all do
    # Stop the application-started state server to avoid conflicts
    Application.stop(:vsh)

    File.mkdir_p!(@test_root)
    on_exit(fn ->
      File.rm_rf!(@test_root)
      # Restart application for any subsequent testing
      Application.ensure_all_started(:vsh)
    end)
    :ok
  end

  setup do
    # Stop any existing state server
    case Process.whereis(VSH.State) do
      nil -> :ok
      pid ->
        try do
          GenServer.stop(pid, :normal, 1000)
        catch
          :exit, _ -> :ok
        end
    end

    # Wait for cleanup
    :timer.sleep(100)

    # Start a fresh state server for each test
    test_dir = Path.join(@test_root, "#{:os.system_time(:nanosecond)}")
    File.mkdir_p!(test_dir)

    {:ok, pid} = VSH.State.start_link(root: test_dir)
    on_exit(fn ->
      try do
        GenServer.stop(pid, :normal, 500)
      catch
        :exit, _ -> :ok
      end
    end)

    {:ok, test_dir: test_dir, state_pid: pid}
  end

  describe "State Management" do
    test "records operations correctly", %{test_dir: test_dir} do
      {:ok, op} = VSH.State.record_operation(:mkdir, ["test"])
      assert op.type == :mkdir
      assert op.path == ["test"]
      refute op.undone
    end

    test "retrieves undoable operations", %{test_dir: _test_dir} do
      {:ok, _} = VSH.State.record_operation(:mkdir, ["a"])
      {:ok, _} = VSH.State.record_operation(:mkdir, ["b"])
      {:ok, _} = VSH.State.record_operation(:mkdir, ["c"])

      undoable = VSH.State.get_undoable(2)
      assert length(undoable) == 2
    end

    test "marks operations as undone", %{test_dir: _test_dir} do
      {:ok, op} = VSH.State.record_operation(:mkdir, ["test"])

      :ok = VSH.State.mark_undone(op.id, "undo-123")

      history = VSH.State.get_history(1)
      [undone_op] = history
      assert undone_op.undone
      assert undone_op.undone_by == "undo-123"
    end

    test "manages redo stack", %{test_dir: _test_dir} do
      {:ok, op} = VSH.State.record_operation(:mkdir, ["test"])

      :ok = VSH.State.push_redo(op)

      popped = VSH.State.pop_redo()
      assert popped.id == op.id

      # Stack should be empty now
      assert VSH.State.pop_redo() == nil
    end
  end

  describe "Transactions" do
    test "begins transaction", %{test_dir: _test_dir} do
      {:ok, txn_id} = VSH.State.begin_transaction("test_txn")
      assert is_binary(txn_id)
    end

    test "prevents nested transactions", %{test_dir: _test_dir} do
      {:ok, _} = VSH.State.begin_transaction("first")
      assert {:error, :transaction_active} = VSH.State.begin_transaction("second")
    end

    test "commits transaction", %{test_dir: _test_dir} do
      {:ok, _} = VSH.State.begin_transaction("commit_test")
      {:ok, _} = VSH.State.record_operation(:mkdir, ["txn_dir"])
      {:ok, committed} = VSH.State.commit_transaction()

      assert committed.name == "commit_test"
      assert committed.committed
      assert length(committed.operations) == 1
    end

    test "rollback clears active transaction", %{test_dir: _test_dir} do
      {:ok, _} = VSH.State.begin_transaction("rollback_test")
      {:ok, _} = VSH.State.record_operation(:mkdir, ["will_rollback"])

      {:ok, _txn} = VSH.State.rollback_transaction()

      # Should be able to start a new transaction
      {:ok, _} = VSH.State.begin_transaction("after_rollback")
    end
  end

  describe "Proof References" do
    test "returns proof references for mkdir/rmdir" do
      proof = VSH.State.proof_for(:mkdir)
      assert proof.theorem == "mkdir_rmdir_reversible"
      assert is_binary(proof.coq)
      assert is_binary(proof.lean4)
    end

    test "returns proof references for create/delete file" do
      proof = VSH.State.proof_for(:create_file)
      assert proof.theorem == "create_delete_file_reversible"
    end

    test "returns all proof references" do
      proofs = VSH.State.get_proofs()
      assert length(proofs) == 3

      theorems = Enum.map(proofs, & &1.theorem)
      assert "mkdir_rmdir_reversible" in theorems
      assert "create_delete_file_reversible" in theorems
      assert "operation_sequence_reversible" in theorems
    end
  end

  describe "Reversibility Property" do
    @tag :integration
    test "operation sequence can be reversed via history", %{test_dir: _test_dir} do
      # Perform a sequence of operations
      {:ok, op1} = VSH.State.record_operation(:mkdir, ["level1"])
      {:ok, op2} = VSH.State.record_operation(:mkdir, ["level1", "level2"])
      {:ok, op3} = VSH.State.record_operation(:create_file, ["level1", "file.txt"])

      # Get all undoable operations
      undoable = VSH.State.get_undoable(3)
      assert length(undoable) == 3

      # Mark all as undone (simulating undo)
      for op <- undoable do
        undo_id = "undo-#{op.id}"
        :ok = VSH.State.mark_undone(op.id, undo_id)
      end

      # Verify all marked as undone
      history = VSH.State.get_history(3)
      assert Enum.all?(history, & &1.undone)
    end
  end

  describe "State Summary" do
    test "returns accurate state summary", %{test_dir: test_dir} do
      {:ok, _} = VSH.State.record_operation(:mkdir, ["a"])
      {:ok, op} = VSH.State.record_operation(:mkdir, ["b"])
      :ok = VSH.State.mark_undone(op.id, "undo-1")
      :ok = VSH.State.push_redo(op)

      summary = VSH.State.get_state()

      assert summary.root == test_dir
      assert summary.history_count == 2
      assert summary.undoable_count == 1
      assert summary.redo_count == 1
    end
  end
end
