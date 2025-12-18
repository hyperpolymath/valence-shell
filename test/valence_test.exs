defmodule ValenceTest do
  use ExUnit.Case
  doctest Valence

  alias Valence.History.Zipper

  describe "Zipper" do
    test "push and back" do
      zipper =
        Zipper.new()
        |> Zipper.push(%{cmd: :a})
        |> Zipper.push(%{cmd: :b})
        |> Zipper.push(%{cmd: :c})

      assert Zipper.undo_count(zipper) == 3
      assert Zipper.redo_count(zipper) == 0

      {:ok, entry, zipper} = Zipper.back(zipper)
      assert entry.cmd == :c
      assert Zipper.undo_count(zipper) == 2
      assert Zipper.redo_count(zipper) == 1
    end

    test "forward after back" do
      zipper =
        Zipper.new()
        |> Zipper.push(%{cmd: :a})
        |> Zipper.push(%{cmd: :b})

      {:ok, _, zipper} = Zipper.back(zipper)
      {:ok, entry, zipper} = Zipper.forward(zipper)

      assert entry.cmd == :b
      assert Zipper.redo_count(zipper) == 0
    end

    test "push clears redo stack" do
      zipper =
        Zipper.new()
        |> Zipper.push(%{cmd: :a})
        |> Zipper.push(%{cmd: :b})

      {:ok, _, zipper} = Zipper.back(zipper)
      assert Zipper.redo_count(zipper) == 1

      # New push clears redo
      zipper = Zipper.push(zipper, %{cmd: :c})
      assert Zipper.redo_count(zipper) == 0
    end

    test "back on empty returns :empty" do
      assert Zipper.back(Zipper.new()) == :empty
    end

    test "forward on empty returns :empty" do
      assert Zipper.forward(Zipper.new()) == :empty
    end
  end
end
