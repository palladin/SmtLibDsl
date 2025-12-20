import CogitoCore

def main (args : List String) : IO UInt32 := do
  IO.println s!"CogitoCore {CogitoCore.version}"
  IO.println ""

  if args.isEmpty then
    IO.println "A type-safe SMT-LIB DSL for Lean 4 with Z3 integration."
    IO.println ""
    IO.println "Available examples:"
    IO.println "  lake exe sudoku      - 9×9 Sudoku puzzle solver"
    IO.println "  lake exe nqueens     - N-Queens puzzle solver (8×8)"
    IO.println "  lake exe eternity2   - Eternity II edge-matching puzzle"
    IO.println ""
    IO.println "Build and run:"
    IO.println "  lake build && lake exe <example>"
    return 0

  let cmd := args.head!
  match cmd with
  | "sudoku" =>
    IO.println "Run: lake exe sudoku"
  | "nqueens" =>
    IO.println "Run: lake exe nqueens"
  | "eternity2" =>
    IO.println "Run: lake exe eternity2"
  | _ =>
    IO.eprintln s!"Unknown example: {cmd}"
    IO.eprintln "Run 'lake exe cogito-core' for available examples."
    return 1

  pure 0
