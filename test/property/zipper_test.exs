defmodule Valence.Property.ZipperTest do
  use ExUnit.Case
  use ExUnitProperties

  alias Valence.History.Zipper

  describe "Zipper properties" do
    property "undo_count + redo_count equals total pushes after any navigation" do
      check all cmds <- list_of(term(), min_length: 1, max_length: 20),
                back_count <- integer(0..length(cmds)) do
        # Push all commands
        zipper =
          Enum.reduce(cmds, Zipper.new(), fn cmd, z ->
            Zipper.push(z, %{cmd: cmd})
          end)

        # Go back some number of times
        zipper =
          Enum.reduce(1..back_count, zipper, fn _, z ->
            case Zipper.back(z) do
              {:ok, _, new_z} -> new_z
              :empty -> z
            end
          end)

        # Total should always equal original push count
        assert Zipper.undo_count(zipper) + Zipper.redo_count(zipper) == length(cmds)
      end
    end

    property "back then forward is identity (when possible)" do
      check all cmds <- list_of(term(), min_length: 2, max_length: 20) do
        zipper =
          Enum.reduce(cmds, Zipper.new(), fn cmd, z ->
            Zipper.push(z, %{cmd: cmd})
          end)

        {:ok, entry, zipper_after_back} = Zipper.back(zipper)
        {:ok, ^entry, zipper_after_forward} = Zipper.forward(zipper_after_back)

        # State should be restored
        assert Zipper.undo_count(zipper_after_forward) == Zipper.undo_count(zipper)
        assert Zipper.redo_count(zipper_after_forward) == Zipper.redo_count(zipper)
      end
    end
  end
end
