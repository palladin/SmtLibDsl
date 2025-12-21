/-
  CogitoCore - Eternity II Puzzle SMT Solver
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/Eternity2SMT.idr

  Eternity II is an edge-matching puzzle where:
  - Pieces are placed on a grid (rows × cols)
  - Each piece has 4 colored edges (up, right, down, left)
  - Adjacent edges must match colors
  - Border edges must be 'X' (gray)
  - Each piece can be rotated 0°, 90°, 180°, or 270°

  Supports various puzzle sizes:
  - 4×4 (16 pieces) - Demo/Test
-/
import CogitoCore

open CogitoCore.SMT

namespace Eternity2

/-! ## Configuration -/

/-- Bit size for piece indices -/
abbrev BitSize : Nat := 16

/-- Bit size for colors (A-Z = 0-25, needs 5 bits) -/
abbrev ColorBitSize : Nat := 5

/-! ## Piece Representation -/

/-- A puzzle piece with 4 colored edges -/
structure Piece where
  up : Char
  right : Char
  down : Char
  left : Char
deriving Repr, BEq

/-- SMT variables representing the 4 colors of a piece at a grid position -/
structure PieceColors where
  upVar : Expr (Ty.bitVec ColorBitSize)
  rightVar : Expr (Ty.bitVec ColorBitSize)
  downVar : Expr (Ty.bitVec ColorBitSize)
  leftVar : Expr (Ty.bitVec ColorBitSize)

/-! ## Puzzle Definition -/

/-- A puzzle instance with its dimensions and pieces -/
structure Puzzle where
  name : String
  rows : Nat
  cols : Nat
  pieces : List (List Char)  -- Each piece is [Up, Right, Down, Left]

/-- Convert a list of 4 chars to a Piece -/
def listToPiece (cs : List Char) : Piece :=
  match cs with
  | [u, r, d, l] => { up := u, right := r, down := d, left := l }
  | _ => { up := 'X', right := 'X', down := 'X', left := 'X' }

/-! ## Sample Puzzles -/

/-- Demo 4×4 puzzle (16 pieces) -/
def puzzle4x4 : Puzzle := {
  name := "Demo 4×4"
  rows := 4
  cols := 4
  pieces := [
    -- Row 0 (corners and edges)
    ['Y', 'X', 'X', 'B'], ['Y', 'B', 'X', 'X'],
    ['X', 'B', 'B', 'X'], ['X', 'Y', 'Y', 'X'],
    -- Row 1
    ['U', 'U', 'U', 'P'], ['P', 'U', 'P', 'P'],
    ['U', 'U', 'P', 'P'], ['U', 'U', 'P', 'P'],
    -- Row 2
    ['Y', 'X', 'Y', 'P'], ['B', 'X', 'B', 'P'],
    ['Y', 'X', 'B', 'P'], ['B', 'X', 'Y', 'P'],
    -- Row 3
    ['Y', 'X', 'Y', 'U'], ['B', 'X', 'B', 'U'],
    ['B', 'X', 'Y', 'U'], ['Y', 'X', 'B', 'U']
  ]
}

/-! ## Color Encoding -/

/-- Convert a color character to its integer value -/
def colorInt (c : Char) : Nat := c.toNat - 'A'.toNat

/-- Convert an integer back to a color character -/
def intColor (i : Nat) : Char := Char.ofNat ('A'.toNat + i)

/-- The border color 'X' as an integer -/
def borderColor : Nat := colorInt 'X'

/-! ## Piece Rotations -/

/-- Rotate a piece 90° clockwise: up→right, right→down, down→left, left→up -/
def rotatePiece (p : Piece) : Piece :=
  { up := p.left, right := p.up, down := p.right, left := p.down }

/-- Generate all 4 rotations of a piece -/
def rotations (p : Piece) : List Piece :=
  let p0 := p
  let p1 := rotatePiece p0
  let p2 := rotatePiece p1
  let p3 := rotatePiece p2
  [p0, p1, p2, p3]

/-! ## Dynamic Grid Types -/

/-- 2D array using lists (for dynamic sizing) -/
abbrev Grid2D (α : Type) := List (List α)

/-! ## SMT Constraints (Generalized) -/

/-- Border color as SMT bitvector -/
def borderBV : Expr (Ty.bitVec ColorBitSize) := bv borderColor ColorBitSize

/-- Check if a piece's colors match the expected colors -/
def equalColors (p : Piece) (pc : PieceColors) : Expr Ty.bool :=
  (bv (colorInt p.up) ColorBitSize =. pc.upVar) ∧.
  (bv (colorInt p.right) ColorBitSize =. pc.rightVar) ∧.
  (bv (colorInt p.down) ColorBitSize =. pc.downVar) ∧.
  (bv (colorInt p.left) ColorBitSize =. pc.leftVar)

/-- Valid piece index constraint: 0 ≤ index < numPieces -/
def validPieceConstraint (numPieces : Nat) (pieceVar : Expr (Ty.bitVec BitSize)) : Expr Ty.bool :=
  (bv 0 BitSize ≤ᵤ pieceVar) ∧. (pieceVar <ᵤ bv numPieces BitSize)

/-- Generate constraint for a single cell based on its position -/
def cellConstraint (rows cols : Nat) (pcs : Grid2D PieceColors) (r c : Nat) : Expr Ty.bool :=
  let getPc := fun (i j : Nat) =>
    match pcs[i]? with
    | some row => row[j]?
    | none => none

  match getPc r c with
  | none => Expr.btrue
  | some pc =>
    let isTop := r == 0
    let isBottom := r == rows - 1
    let isLeft := c == 0
    let isRight := c == cols - 1

    -- Border constraints
    let topBorder := if isTop then pc.upVar =. borderBV else Expr.btrue
    let bottomBorder := if isBottom then pc.downVar =. borderBV else Expr.btrue
    let leftBorder := if isLeft then pc.leftVar =. borderBV else Expr.btrue
    let rightBorder := if isRight then pc.rightVar =. borderBV else Expr.btrue

    -- Adjacency constraints
    let topMatch := if r > 0 then
      match getPc (r-1) c with
      | some up => pc.upVar =. up.downVar
      | none => Expr.btrue
      else Expr.btrue

    let bottomMatch := if r < rows - 1 then
      match getPc (r+1) c with
      | some down => pc.downVar =. down.upVar
      | none => Expr.btrue
      else Expr.btrue

    let leftMatch := if c > 0 then
      match getPc r (c-1) with
      | some left => pc.leftVar =. left.rightVar
      | none => Expr.btrue
      else Expr.btrue

    let rightMatch := if c < cols - 1 then
      match getPc r (c+1) with
      | some right => pc.rightVar =. right.leftVar
      | none => Expr.btrue
      else Expr.btrue

    topBorder ∧. bottomBorder ∧. leftBorder ∧. rightBorder ∧.
    topMatch ∧. bottomMatch ∧. leftMatch ∧. rightMatch

/-- Apply color constraints to all cells -/
def colorConstraints (rows cols : Nat) (pcs : Grid2D PieceColors) : Smt Unit := do
  for r in List.range rows do
    for c in List.range cols do
      assert (cellConstraint rows cols pcs r c)

/-- Constraint: piece index implies matching colors (with any rotation) -/
def pieceConstraint (pieces : List Piece) (pieceVar : Expr (Ty.bitVec BitSize)) (pc : PieceColors) : Expr Ty.bool :=
  let indexed := pieces.zip (List.range pieces.length)
  indexed.foldl (fun acc (p, idx) =>
    let rots := rotations p
    let rotMatch := rots.foldl (fun acc' rot => acc' ∨. equalColors rot pc) Expr.bfalse
    acc ∧. ((bv idx BitSize =. pieceVar) →. rotMatch)
  ) Expr.btrue

/-- Apply piece constraints to entire grid -/
def pieceConstraints (pieces : List Piece) (varPieces : Grid2D (Expr (Ty.bitVec BitSize)))
    (colorPieces : Grid2D PieceColors) : Smt Unit := do
  for (pieceRow, colorRow) in varPieces.zip colorPieces do
    for (vp, pc) in pieceRow.zip colorRow do
      assert (pieceConstraint pieces vp pc)

/-- Apply valid piece constraints to entire grid -/
def validPieces (numPieces : Nat) (vars : Grid2D (Expr (Ty.bitVec BitSize))) : Smt Unit := do
  for row in vars do
    for v in row do
      assert (validPieceConstraint numPieces v)

/-- Flatten a 2D grid to a list -/
def flatten2D (grid : Grid2D α) : List α :=
  grid.flatten

/-- Distinctness constraint: all pieces must be different -/
def distinctPieces (vars : Grid2D (Expr (Ty.bitVec BitSize))) : Smt Unit := do
  let flat := flatten2D vars
  assert (distinct flat)

/-! ## Main Solver -/

/-- Declare piece variables for a cell -/
def declarePieceVar (i j : Nat) : Smt (Expr (Ty.bitVec BitSize)) := do
  declareBV s!"x_{i}_{j}" BitSize

/-- Declare color variables for a cell -/
def declareColorCell (i j : Nat) : Smt PieceColors := do
  let up ← declareBV s!"cx_{i}_{j}_Up" ColorBitSize
  let right ← declareBV s!"cx_{i}_{j}_Right" ColorBitSize
  let down ← declareBV s!"cx_{i}_{j}_Down" ColorBitSize
  let left ← declareBV s!"cx_{i}_{j}_Left" ColorBitSize
  pure { upVar := up, rightVar := right, downVar := down, leftVar := left }

/-- Declare all piece index variables -/
def declarePieceVars (rows cols : Nat) : Smt (Grid2D (Expr (Ty.bitVec BitSize))) := do
  let mut grid := []
  for i in List.range rows do
    let mut row := []
    for j in List.range cols do
      let v ← declarePieceVar i j
      row := row ++ [v]
    grid := grid ++ [row]
  pure grid

/-- Declare all color variables -/
def declareColorPieces (rows cols : Nat) : Smt (Grid2D PieceColors) := do
  let mut grid := []
  for i in List.range rows do
    let mut row := []
    for j in List.range cols do
      let pc ← declareColorCell i j
      row := row ++ [pc]
    grid := grid ++ [row]
  pure grid

/-- Build the complete SMT problem for a puzzle -/
def buildSolver (puzzle : Puzzle) : Smt Unit := do
  let pieces := puzzle.pieces.map listToPiece
  let numPieces := pieces.length

  -- Declare piece index variables
  let varPieces ← declarePieceVars puzzle.rows puzzle.cols

  -- Declare color variables
  let colorPieces ← declareColorPieces puzzle.rows puzzle.cols

  -- Constraint 1: All piece indices are valid (0 ≤ x < numPieces)
  validPieces numPieces varPieces

  -- Constraint 2: All pieces are distinct (each piece used exactly once)
  distinctPieces varPieces

  -- Constraint 3: Adjacent edges must match, borders must be 'X'
  colorConstraints puzzle.rows puzzle.cols colorPieces

  -- Constraint 4: Piece index implies valid color combination
  pieceConstraints pieces varPieces colorPieces

/-! ## Display Helpers -/

/-- ANSI color codes -/
def resetColor : String := "\x1b[0m"
def bold : String := "\x1b[1m"

/-- Get ANSI color code for a puzzle color character -/
def colorCode (c : Char) : String :=
  match c with
  | 'X' => "\x1b[90m"   -- Gray (border)
  | 'Y' => "\x1b[93m"   -- Bright Yellow
  | 'B' => "\x1b[94m"   -- Bright Blue
  | 'U' => "\x1b[95m"   -- Bright Magenta
  | 'P' => "\x1b[92m"   -- Bright Green
  | 'R' => "\x1b[91m"   -- Bright Red
  | 'C' => "\x1b[96m"   -- Bright Cyan
  | 'O' => "\x1b[33m"   -- Orange (dark yellow)
  | 'W' => "\x1b[97m"   -- White
  | _ => "\x1b[0m"      -- Reset (unknown)

/-- Colorize a single character -/
def colorChar (c : Char) : String :=
  s!"{bold}{colorCode c}{c}{resetColor}"

/-- Left-pad a string to at least n characters -/
def leftPad (n : Nat) (c : Char) (s : String) : String :=
  let pad := String.mk (List.replicate (n - s.length) c)
  pad ++ s

/-- Parse a hex or binary string to Nat -/
def parseBitVec (s : String) : Option Nat :=
  if s.startsWith "#x" then
    let s' := s.drop 2
    s'.foldl (fun acc c =>
      acc.bind fun a =>
        if '0' ≤ c ∧ c ≤ '9' then some (a * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c ∧ c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c ∧ c ≤ 'F' then some (a * 16 + (c.toNat - 'A'.toNat + 10))
        else none
    ) (some 0)
  else if s.startsWith "#b" then
    let s' := s.drop 2
    s'.foldl (fun acc c =>
      acc.bind fun a =>
        if c == '0' then some (a * 2)
        else if c == '1' then some (a * 2 + 1)
        else none
    ) (some 0)
  else
    s.toNat?

/-- Display the piece index solution -/
def displayPieceSolution (puzzle : Puzzle) (model : Model schema) : IO Unit := do
  IO.println s!"Piece placement ({puzzle.rows}×{puzzle.cols}):"

  -- Build separator lines dynamically
  let cellWidth := if puzzle.pieces.length > 99 then 5 else 4
  let topLine := "┌" ++ String.intercalate "┬" (List.replicate puzzle.cols (String.mk (List.replicate cellWidth '─'))) ++ "┐"
  let midLine := "├" ++ String.intercalate "┼" (List.replicate puzzle.cols (String.mk (List.replicate cellWidth '─'))) ++ "┤"
  let botLine := "└" ++ String.intercalate "┴" (List.replicate puzzle.cols (String.mk (List.replicate cellWidth '─'))) ++ "┘"

  IO.println topLine
  for i in List.range puzzle.rows do
    let mut row := "│"
    for j in List.range puzzle.cols do
      let name := s!"x_{i}_{j}"
      match model.lookup name with
      | some v =>
        let displayVal := match parseBitVec v with
          | some n => s!"{n}"
          | none => v.take 3
        row := row ++ s!" {leftPad (cellWidth - 2) ' ' displayVal} │"
      | none => row := row ++ s!"{String.mk (List.replicate (cellWidth - 1) ' ')}?│"
    IO.println row
    if i < puzzle.rows - 1 then
      IO.println midLine
  IO.println botLine

/-- Display the color solution for each cell as a visual grid -/
def displayColorSolution (puzzle : Puzzle) (model : Model schema) : IO Unit := do
  IO.println ""
  IO.println s!"{bold}Solution grid (edges shown visually):{resetColor}"
  IO.println ""

  -- Helper to get color for a cell edge
  let getColorChar := fun (i j : Nat) (dir : String) =>
    match model.lookup s!"cx_{i}_{j}_{dir}" with
    | some v =>
      match parseBitVec v with
      | some n => intColor n
      | none => '?'
    | none => '?'

  -- Print each row of cells (each cell takes 3 lines)
  for i in List.range puzzle.rows do
    -- Line 1: Top edges (Up color in center of each cell)
    let mut topLine := "    "
    for j in List.range puzzle.cols do
      let up := getColorChar i j "Up"
      topLine := topLine ++ s!" {colorChar up}{colorChar up}{colorChar up} "
    IO.println topLine

    -- Line 2: Left, center, Right
    let mut midLine := "    "
    for j in List.range puzzle.cols do
      let left := getColorChar i j "Left"
      let right := getColorChar i j "Right"
      midLine := midLine ++ s!"{colorChar left}   {colorChar right}"
    IO.println midLine

    -- Line 3: Bottom edges (Down color in center of each cell)
    let mut botLine := "    "
    for j in List.range puzzle.cols do
      let down := getColorChar i j "Down"
      botLine := botLine ++ s!" {colorChar down}{colorChar down}{colorChar down} "
    IO.println botLine

    -- Separator line between rows (empty line)
    if i < puzzle.rows - 1 then
      IO.println ""

/-- Display puzzle pieces visually -/
def displayPuzzlePieces (puzzle : Puzzle) : IO Unit := do
  let pieces := puzzle.pieces
  let piecesPerRow := min puzzle.cols 8  -- Max 8 per row for readability

  for startIdx in List.range ((pieces.length + piecesPerRow - 1) / piecesPerRow) do
    let rowStart := startIdx * piecesPerRow
    let rowEnd := min (rowStart + piecesPerRow) pieces.length

    -- Line 1: Top edges
    let mut topLine := "    "
    for idx in List.range (rowEnd - rowStart) do
      let pieceIdx := rowStart + idx
      match pieces[pieceIdx]? with
      | some p =>
        let up := p.head?.getD 'X'
        topLine := topLine ++ s!" {colorChar up}{colorChar up}{colorChar up} "
      | none => pure ()
    IO.println topLine

    -- Line 2: Left, piece#, Right
    let mut midLine := "    "
    for idx in List.range (rowEnd - rowStart) do
      let pieceIdx := rowStart + idx
      match pieces[pieceIdx]? with
      | some p =>
        let left := (p[3]?).getD 'X'
        let right := (p[1]?).getD 'X'
        midLine := midLine ++ s!"{colorChar left}{leftPad 2 ' ' (toString pieceIdx)} {colorChar right}"
      | none => pure ()
    IO.println midLine

    -- Line 3: Bottom edges
    let mut botLine := "    "
    for idx in List.range (rowEnd - rowStart) do
      let pieceIdx := rowStart + idx
      match pieces[pieceIdx]? with
      | some p =>
        let down := (p[2]?).getD 'X'
        botLine := botLine ++ s!" {colorChar down}{colorChar down}{colorChar down} "
      | none => pure ()
    IO.println botLine

    IO.println ""

/-- Run the solver for a given puzzle -/
def solvePuzzle (puzzle : Puzzle) (dumpSmt : Bool := false) : IO UInt32 := do
  IO.println s!"{bold}=== Eternity II Puzzle: {puzzle.name} ==={resetColor}"
  IO.println s!"Grid size: {puzzle.rows}×{puzzle.cols} = {puzzle.rows * puzzle.cols} pieces"
  IO.println ""

  IO.println s!"{bold}Color legend:{resetColor}"
  IO.println s!"  {colorChar 'X'}=Border  {colorChar 'Y'}=Yellow  {colorChar 'B'}=Blue  {colorChar 'U'}=Magenta  {colorChar 'P'}=Green"
  IO.println s!"  {colorChar 'R'}=Red  {colorChar 'C'}=Cyan  {colorChar 'O'}=Orange  {colorChar 'W'}=White"
  IO.println ""

  IO.println s!"{bold}Puzzle pieces:{resetColor}"
  displayPuzzlePieces puzzle
  IO.println ""

  IO.println "Building SMT constraints..."
  let solver := buildSolver puzzle
  IO.println s!"Total pieces: {puzzle.pieces.length}"
  IO.println s!"Variables: {puzzle.rows * puzzle.cols} piece positions + {puzzle.rows * puzzle.cols * 4} colors"
  IO.println ""

  IO.println "Solving with Z3..."
  IO.println "(This may take a while for larger puzzles...)"
  IO.println ""

  let result ← solve solver dumpSmt
  match result with
  | .sat model =>
    IO.println s!"{bold}SAT - Solution found!{resetColor}"
    displayPieceSolution puzzle model
    displayColorSolution puzzle model
  | .unsat =>
    IO.println "UNSAT - No solution exists"
  | .unknown reason =>
    IO.println s!"Unknown: {reason}"

  return 0

end Eternity2

open Eternity2 in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"
  solvePuzzle puzzle4x4 dumpSmt
