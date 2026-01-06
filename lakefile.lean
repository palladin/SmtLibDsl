import Lake
open Lake DSL

package «CogitoCore» where
  -- All Lean modules are relative to the repository root.
  srcDir := "."

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "main"

lean_lib «CogitoCore» where
  -- We expose the aggregated `CogitoCore` module as the library entry point.
  roots := #[`CogitoCore]

lean_lib «Examples» where
  -- Examples library for shared modules
  roots := #[`Examples.SokobanLevels]

@[default_target]
lean_exe «cogito-core» where
  root := `Main

lean_exe «cogito-test» where
  root := `Tests.SMT

lean_exe «sudoku» where
  root := `Examples.Sudoku

lean_exe «eternity2» where
  root := `Examples.Eternity2

lean_exe «nqueens» where
  root := `Examples.NQueens

lean_exe «life» where
  root := `Examples.Life

lean_exe «minesweeper» where
  root := `Examples.Minesweeper

lean_exe «countdown» where
  root := `Examples.Countdown

lean_exe «magicsquare» where
  root := `Examples.MagicSquare

lean_exe «sokoban» where
  root := `Examples.Sokoban
