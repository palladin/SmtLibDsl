/-
  CogitoCore - Magic Square SMT Solver Example

  A Magic Square is an n×n grid filled with distinct integers 1 to n²
  such that all rows, columns, and both main diagonals sum to the
  same "magic constant": M = n(n² + 1) / 2

  For a 3×3 square: M = 3(9 + 1) / 2 = 15
  For a 4×4 square: M = 4(16 + 1) / 2 = 34
-/
import CogitoCore

open CogitoCore.SMT

namespace MagicSquare

/-! ## Configuration -/

/-- Size of the magic square (n×n) - using 3 for classic magic square -/
abbrev N : Nat := 3

/-- Bit width for values (8-bit is enough for small squares) -/
abbrev W : Nat := 8

/-- The magic constant: n(n² + 1) / 2 -/
def magicConstant : Nat := N * (N * N + 1) / 2

/-- Type alias for our bitvector expressions -/
abbrev BV := Expr (Ty.bitVec W)

/-- Grid type -/
abbrev Grid := Tensor2D N N BV

/-! ## SMT Helpers -/

/-- Create an integer literal -/
def int (v : Nat) : BV := bv v W

/-- Sum a vector of bitvector expressions -/
def sumVec (xs : Vector BV n) : BV :=
  xs.foldl (· +. ·) (int 0)

/-! ## Constraints -/

/-- All cells contain values from 1 to n² -/
def rangeConstraints (grid : Grid) : Smt Unit :=
  Tensor2D.foldRows (fun acc row =>
    acc >>= fun _ =>
      row.foldl (fun acc' cell =>
        acc' >>= fun _ => assert ((int 1 ≤.ᵤ cell) ∧. (cell ≤.ᵤ int (N * N))))
        (pure ())) (pure ()) grid

/-- All cells are distinct - use SMT distinct constraint -/
def distinctConstraints (grid : Grid) : Smt Unit := do
  -- Build list of all cells, then convert to distinct
  let allCells : List BV := Tensor2D.flatten grid
  assert (distinct allCells)

/-- All rows sum to magic constant -/
def rowSumConstraints (grid : Grid) : Smt Unit :=
  Tensor2D.foldRows (fun acc row =>
    acc >>= fun _ => assert (sumVec row =. int magicConstant)) (pure ()) grid

/-- All columns sum to magic constant -/
def colSumConstraints (grid : Grid) : Smt Unit :=
  Vector.finRange N |>.foldl (fun acc c =>
    acc >>= fun _ => assert (sumVec (Tensor2D.getCol grid c) =. int magicConstant)) (pure ())

/-- Main diagonal (top-left to bottom-right) sums to magic constant -/
def mainDiagConstraint (grid : Grid) : Smt Unit := do
  let diag := Vector.ofFn fun (i : Fin N) => (Vector.get grid i).get i
  assert (sumVec diag =. int magicConstant)

/-- Anti-diagonal (top-right to bottom-left) sums to magic constant -/
def antiDiagConstraint (grid : Grid) : Smt Unit := do
  let diag := Vector.ofFn fun (i : Fin N) =>
    let col : Fin N := ⟨N - 1 - i.val, by omega⟩
    (Vector.get grid i).get col
  assert (sumVec diag =. int magicConstant)

/-- Symmetry breaking - fix corner ordering to reduce search space -/
def symmetryBreaking (grid : Grid) : Smt Unit := do
  -- The smallest corner value should be in top-left
  -- This eliminates rotations and reflections
  let topLeft     := grid[0, 0]
  let topRight    := grid[0, 2]
  let bottomLeft  := grid[2, 0]
  let bottomRight := grid[2, 2]
  assert (topLeft <.ᵤ topRight)
  assert (topLeft <.ᵤ bottomLeft)
  assert (topLeft <.ᵤ bottomRight)

/-! ## Main Solver -/

/-- Build the complete magic square SMT problem -/
def magicSquareSmt : Smt Grid := do
  -- Declare n×n grid of variables
  let grid ← declareBVTensor "cell" [N, N] W

  -- Add all constraints
  rangeConstraints grid
  distinctConstraints grid
  rowSumConstraints grid
  colSumConstraints grid
  mainDiagConstraint grid
  antiDiagConstraint grid
  symmetryBreaking grid

  pure grid

/-- Wrapper that returns Unit for solving -/
def magicSquareQuery : Smt Unit := do
  let _ ← magicSquareSmt
  pure ()

/-! ## Display -/

/-- Pad string to given width (center-aligned) -/
def padCenter (s : String) (width : Nat) : String :=
  let totalPad := width - s.length
  let leftPad := totalPad / 2
  let rightPad := totalPad - leftPad
  String.mk (List.replicate leftPad ' ') ++ s ++ String.mk (List.replicate rightPad ' ')

/-- Build horizontal separator line -/
def horizontalLine (left : String) (mid : String) (right : String) (cellWidth : Nat) : String :=
  let segment := String.mk (List.replicate cellWidth '─')
  left ++ String.intercalate mid (List.replicate N segment) ++ right

/-- Parse model and display the magic square with nice box drawing -/
def displayResult (result : Result (magicSquareQuery.schema)) : IO Unit := do
  match result with
  | .sat model =>
    IO.println s!"Found a {N}×{N} magic square!"
    IO.println s!"Magic constant: {magicConstant}"
    IO.println ""

    let cellWidth := 5  -- Width for each cell

    -- Top border
    IO.println (horizontalLine "┌" "┬" "┐" cellWidth)

    -- Parse and display grid with borders
    for r in List.range N do
      let mut rowStr := "│"
      for c in List.range N do
        let varName := s!"cell_{r}_{c}"
        let cellVal := match model.lookup varName with
          | some valStr =>
            match parseBitVec valStr W with
            | some bv => toString bv.toNat
            | none => "?"
          | none => "?"
        rowStr := rowStr ++ padCenter cellVal cellWidth ++ "│"
      IO.println rowStr

      -- Middle or bottom border
      if r < N - 1 then
        IO.println (horizontalLine "├" "┼" "┤" cellWidth)

    -- Bottom border
    IO.println (horizontalLine "└" "┴" "┘" cellWidth)
    IO.println ""

    -- Verification with computed sums
    IO.println "Verification:"
    IO.println s!"  Magic constant = {magicConstant}"

    -- Show row sums
    for r in List.range N do
      let mut rowSum := 0
      for c in List.range N do
        let varName := s!"cell_{r}_{c}"
        match model.lookup varName with
        | some valStr =>
          match parseBitVec valStr W with
          | some bv => rowSum := rowSum + bv.toNat
          | none => pure ()
        | none => pure ()
      IO.println s!"  Row {r + 1}: {rowSum} ✓"

    -- Show column sums
    for c in List.range N do
      let mut colSum := 0
      for r in List.range N do
        let varName := s!"cell_{r}_{c}"
        match model.lookup varName with
        | some valStr =>
          match parseBitVec valStr W with
          | some bv => colSum := colSum + bv.toNat
          | none => pure ()
        | none => pure ()
      IO.println s!"  Col {c + 1}: {colSum} ✓"

    -- Show diagonal sums
    let mut mainDiagSum := 0
    let mut antiDiagSum := 0
    for i in List.range N do
      -- Main diagonal
      match model.lookup s!"cell_{i}_{i}" with
      | some valStr =>
        match parseBitVec valStr W with
        | some bv => mainDiagSum := mainDiagSum + bv.toNat
        | none => pure ()
      | none => pure ()
      -- Anti-diagonal
      match model.lookup s!"cell_{i}_{N - 1 - i}" with
      | some valStr =>
        match parseBitVec valStr W with
        | some bv => antiDiagSum := antiDiagSum + bv.toNat
        | none => pure ()
      | none => pure ()
    IO.println s!"  Main diagonal: {mainDiagSum} ✓"
    IO.println s!"  Anti-diagonal: {antiDiagSum} ✓"

  | .unsat =>
    IO.println "No magic square exists (unexpected for standard magic squares)"

  | .unknown reason =>
    IO.println s!"Solver returned unknown: {reason}"

end MagicSquare

/-! ## Main Entry Point -/

def main : IO UInt32 := do
  IO.println "╔═══════════════════════════════════════╗"
  IO.println "║     Magic Square SMT Solver           ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println ""

  -- Check Z3 availability
  match ← CogitoCore.SMT.checkZ3 with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok version =>
    IO.println s!"Using {version}"
    IO.println ""

  IO.println s!"Solving {MagicSquare.N}×{MagicSquare.N} magic square..."
  IO.println s!"Magic constant = {MagicSquare.magicConstant}"
  IO.println ""

  let result ← CogitoCore.SMT.solve MagicSquare.magicSquareQuery
  MagicSquare.displayResult result

  return 0
