import CogitoCore

def main (args : List String) : IO UInt32 := do
  IO.println s!"CogitoCore {CogitoCore.version}"
  IO.println ""

  if args.isEmpty then
    IO.println "Usage: lake exe cogito-core <name>"
    IO.println ""
    IO.println "Available examples:"
    IO.println "  sudoku     - 9x9 Sudoku puzzle solver"
    IO.println "  eternity2  - Eternity II edge-matching puzzle solver"
    IO.println ""
    IO.println "Run an example:"
    IO.println "  lake exe sudoku"
    IO.println "  lake exe eternity2"
    return 0

  let cmd := args.head!
  match cmd with
  | "sudoku" =>
    IO.println "Run: lake exe sudoku"
  | "eternity2" =>
    IO.println "Run: lake exe eternity2"
  | _ =>
    IO.eprintln s!"Unknown example: {cmd}"
    IO.eprintln "Run 'lake exe cogito-core' for available examples."
    return 1

  pure 0
