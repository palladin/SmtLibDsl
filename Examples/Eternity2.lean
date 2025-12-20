/-
  CogitoCore - Eternity II Puzzle SMT Solver Example
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/Eternity2SMT.idr

  Eternity II is an edge-matching puzzle where:
  - Pieces are placed on a grid
  - Each piece has 4 colored edges (up, right, down, left)
  - Adjacent edges must match colors
  - Border edges must be 'X' (gray)
  - Each piece can be rotated 0°, 90°, 180°, or 270°

  This implementation uses a 4×4 simplified version.
  Uses 8-bit bitvectors for piece indices and 5-bit for colors.
-/
import CogitoCore

open CogitoCore.SMT

namespace Eternity2

/-! ## Configuration -/

/-- Bit size for piece indices (0-15 for 16 pieces) -/
abbrev BitSize : Nat := 8

/-- Bit size for colors (A-Z = 0-25, needs 5 bits) -/
abbrev ColorBitSize : Nat := 5

/-! ## Piece Representation -/

/-- A puzzle piece with 4 colored edges -/
structure Piece where
  up : Char
  right : Char
  down : Char
  left : Char
deriving Repr

/-- SMT variables representing the 4 colors of a piece at a grid position -/
structure PieceColors where
  upVar : Expr (Ty.bitVec ColorBitSize)
  rightVar : Expr (Ty.bitVec ColorBitSize)
  downVar : Expr (Ty.bitVec ColorBitSize)
  leftVar : Expr (Ty.bitVec ColorBitSize)

/-! ## Puzzle Definition -/

/-- The puzzle pieces: 16 pieces for a 4×4 grid.
    Each piece is represented as [Up, Right, Down, Left] colors.
    'X' represents the border color (gray). -/
def puzzle : Vector (Vector Char 4) 16 := ⟨#[
  -- Row 0 (corners and edges)
  ⟨#['Y', 'X', 'X', 'B'], rfl⟩, ⟨#['Y', 'B', 'X', 'X'], rfl⟩,
  ⟨#['X', 'B', 'B', 'X'], rfl⟩, ⟨#['X', 'Y', 'Y', 'X'], rfl⟩,
  -- Row 1
  ⟨#['U', 'U', 'U', 'P'], rfl⟩, ⟨#['P', 'U', 'P', 'P'], rfl⟩,
  ⟨#['U', 'U', 'P', 'P'], rfl⟩, ⟨#['U', 'U', 'P', 'P'], rfl⟩,
  -- Row 2
  ⟨#['Y', 'X', 'Y', 'P'], rfl⟩, ⟨#['B', 'X', 'B', 'P'], rfl⟩,
  ⟨#['Y', 'X', 'B', 'P'], rfl⟩, ⟨#['B', 'X', 'Y', 'P'], rfl⟩,
  -- Row 3
  ⟨#['Y', 'X', 'Y', 'U'], rfl⟩, ⟨#['B', 'X', 'B', 'U'], rfl⟩,
  ⟨#['B', 'X', 'Y', 'U'], rfl⟩, ⟨#['Y', 'X', 'B', 'U'], rfl⟩
], rfl⟩

/-! ## Color Encoding -/

/-- Convert a color character to its integer value -/
def colorInt (c : Char) : Nat := c.toNat - 'A'.toNat

/-- Convert an integer back to a color character -/
def intColor (i : Nat) : Char := Char.ofNat ('A'.toNat + i)

/-- The border color 'X' as an integer -/
def borderColor : Nat := colorInt 'X'

/-! ## Piece Rotations -/

/-- Rotate a vector left by 1 position: [a,b,c,d] -> [b,c,d,a] -/
def rotateLeft (v : Vector α 4) : Vector α 4 :=
  ⟨#[v.get ⟨1, by omega⟩, v.get ⟨2, by omega⟩, v.get ⟨3, by omega⟩, v.get ⟨0, by omega⟩], rfl⟩

/-- Convert a color vector [up, right, down, left] to a Piece -/
def toPiece (v : Vector Char 4) : Piece :=
  { up := v.get ⟨0, by omega⟩
  , right := v.get ⟨1, by omega⟩
  , down := v.get ⟨2, by omega⟩
  , left := v.get ⟨3, by omega⟩ }

/-- Generate all 4 rotations of a piece -/
def rotations (p : Vector Char 4) : Vector Piece 4 :=
  let p0 := p
  let p1 := rotateLeft p0
  let p2 := rotateLeft p1
  let p3 := rotateLeft p2
  ⟨#[toPiece p0, toPiece p1, toPiece p2, toPiece p3], rfl⟩

/-- All pieces with their index and all possible rotations -/
def pieces : Vector (Nat × Vector Piece 4) 16 :=
  Vector.ofFn fun i => (i.val, rotations (puzzle.get i))

/-! ## Grid Types -/

abbrev PieceGrid := Tensor2D 4 4 (Expr (Ty.bitVec BitSize))
abbrev ColorGrid := Tensor2D 4 4 PieceColors

/-! ## SMT Constraints -/

/-- Border color as SMT bitvector -/
def borderBV : Expr (Ty.bitVec ColorBitSize) := bv borderColor ColorBitSize

/-- Check if a piece's colors match the expected colors -/
def equalColors (p : Piece) (pc : PieceColors) : Expr Ty.bool :=
  (bv (colorInt p.up) ColorBitSize =. pc.upVar) ∧.
  (bv (colorInt p.right) ColorBitSize =. pc.rightVar) ∧.
  (bv (colorInt p.down) ColorBitSize =. pc.downVar) ∧.
  (bv (colorInt p.left) ColorBitSize =. pc.leftVar)

/-- Valid piece index constraint: 0 ≤ index < 16 -/
def validPieceConstraint (pieceVar : Expr (Ty.bitVec BitSize)) : Expr Ty.bool :=
  (bv 0 BitSize ≤ᵤ pieceVar) ∧. (pieceVar <ᵤ bv 16 BitSize)

/-- Apply valid piece constraints to entire grid -/
def validPieces (vars : PieceGrid) : Smt Unit :=
  Tensor2D.foldRows (fun acc row =>
    acc >>= fun _ => row.foldl (fun acc' v => acc' >>= fun _ => assert (validPieceConstraint v)) (pure ())
  ) (pure ()) vars

/-- Get piece colors at grid position -/
def getPc (pcs : ColorGrid) (r c : Nat) (hr : r < 4 := by omega) (hc : c < 4 := by omega) : PieceColors :=
  Tensor2D.get pcs ⟨r, hr⟩ ⟨c, hc⟩

/-- Color constraints for cell (0,0) - top-left corner -/
def colorConstraint_0_0 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 0 0
  let right := getPc pcs 0 1
  let down := getPc pcs 1 0
  (pc.upVar =. borderBV) ∧. (pc.leftVar =. borderBV) ∧.
  (pc.rightVar =. right.leftVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (0,1) - top edge -/
def colorConstraint_0_1 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 0 1
  let left := getPc pcs 0 0
  let right := getPc pcs 0 2
  let down := getPc pcs 1 1
  (pc.upVar =. borderBV) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (0,2) - top edge -/
def colorConstraint_0_2 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 0 2
  let left := getPc pcs 0 1
  let right := getPc pcs 0 3
  let down := getPc pcs 1 2
  (pc.upVar =. borderBV) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (0,3) - top-right corner -/
def colorConstraint_0_3 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 0 3
  let left := getPc pcs 0 2
  let down := getPc pcs 1 3
  (pc.upVar =. borderBV) ∧. (pc.rightVar =. borderBV) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (1,0) - left edge -/
def colorConstraint_1_0 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 1 0
  let up := getPc pcs 0 0
  let right := getPc pcs 1 1
  let down := getPc pcs 2 0
  (pc.leftVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.rightVar =. right.leftVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (1,1) - interior -/
def colorConstraint_1_1 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 1 1
  let up := getPc pcs 0 1
  let down := getPc pcs 2 1
  let left := getPc pcs 1 0
  let right := getPc pcs 1 2
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (1,2) - interior -/
def colorConstraint_1_2 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 1 2
  let up := getPc pcs 0 2
  let down := getPc pcs 2 2
  let left := getPc pcs 1 1
  let right := getPc pcs 1 3
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (1,3) - right edge -/
def colorConstraint_1_3 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 1 3
  let up := getPc pcs 0 3
  let down := getPc pcs 2 3
  let left := getPc pcs 1 2
  (pc.rightVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧. (pc.leftVar =. left.rightVar)

/-- Color constraints for cell (2,0) - left edge -/
def colorConstraint_2_0 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 2 0
  let up := getPc pcs 1 0
  let right := getPc pcs 2 1
  let down := getPc pcs 3 0
  (pc.leftVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.rightVar =. right.leftVar) ∧. (pc.downVar =. down.upVar)

/-- Color constraints for cell (2,1) - interior -/
def colorConstraint_2_1 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 2 1
  let up := getPc pcs 1 1
  let down := getPc pcs 3 1
  let left := getPc pcs 2 0
  let right := getPc pcs 2 2
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (2,2) - interior -/
def colorConstraint_2_2 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 2 2
  let up := getPc pcs 1 2
  let down := getPc pcs 3 2
  let left := getPc pcs 2 1
  let right := getPc pcs 2 3
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧.
  (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (2,3) - right edge -/
def colorConstraint_2_3 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 2 3
  let up := getPc pcs 1 3
  let down := getPc pcs 3 3
  let left := getPc pcs 2 2
  (pc.rightVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.downVar =. down.upVar) ∧. (pc.leftVar =. left.rightVar)

/-- Color constraints for cell (3,0) - bottom-left corner -/
def colorConstraint_3_0 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 3 0
  let up := getPc pcs 2 0
  let right := getPc pcs 3 1
  (pc.downVar =. borderBV) ∧. (pc.leftVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (3,1) - bottom edge -/
def colorConstraint_3_1 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 3 1
  let up := getPc pcs 2 1
  let left := getPc pcs 3 0
  let right := getPc pcs 3 2
  (pc.downVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (3,2) - bottom edge -/
def colorConstraint_3_2 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 3 2
  let up := getPc pcs 2 2
  let left := getPc pcs 3 1
  let right := getPc pcs 3 3
  (pc.downVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.leftVar =. left.rightVar) ∧. (pc.rightVar =. right.leftVar)

/-- Color constraints for cell (3,3) - bottom-right corner -/
def colorConstraint_3_3 (pcs : ColorGrid) : Expr Ty.bool :=
  let pc := getPc pcs 3 3
  let up := getPc pcs 2 3
  let left := getPc pcs 3 2
  (pc.downVar =. borderBV) ∧. (pc.rightVar =. borderBV) ∧.
  (pc.upVar =. up.downVar) ∧. (pc.leftVar =. left.rightVar)

/-- Apply all color constraints -/
def colorConstraints (pcs : ColorGrid) : Smt Unit := do
  assert (colorConstraint_0_0 pcs)
  assert (colorConstraint_0_1 pcs)
  assert (colorConstraint_0_2 pcs)
  assert (colorConstraint_0_3 pcs)
  assert (colorConstraint_1_0 pcs)
  assert (colorConstraint_1_1 pcs)
  assert (colorConstraint_1_2 pcs)
  assert (colorConstraint_1_3 pcs)
  assert (colorConstraint_2_0 pcs)
  assert (colorConstraint_2_1 pcs)
  assert (colorConstraint_2_2 pcs)
  assert (colorConstraint_2_3 pcs)
  assert (colorConstraint_3_0 pcs)
  assert (colorConstraint_3_1 pcs)
  assert (colorConstraint_3_2 pcs)
  assert (colorConstraint_3_3 pcs)

/-- Constraint: piece index implies matching colors (with any rotation) -/
def pieceConstraint (pieceVar : Expr (Ty.bitVec BitSize)) (pc : PieceColors) : Expr Ty.bool :=
  -- For each possible piece index, if pieceVar == index, then colors must match one rotation
  pieces.foldl (fun acc (idx, rots) =>
    let rotMatch := rots.foldl (fun acc' rot => acc' ∨. equalColors rot pc) Expr.bfalse
    acc ∧. ((bv idx BitSize =. pieceVar) →. rotMatch)
  ) Expr.btrue

/-- Apply piece constraints to entire grid -/
def pieceConstraints (varPieces : PieceGrid) (colorPieces : ColorGrid) : Smt Unit :=
  Vector.finRange 4 |>.foldl (fun acc i =>
    Vector.finRange 4 |>.foldl (fun acc' j =>
      acc' >>= fun _ =>
        let vp := Tensor2D.get varPieces i j
        let pc := Tensor2D.get colorPieces i j
        assert (pieceConstraint vp pc)
    ) acc
  ) (pure ())

/-- Left-pad a string to at least n characters -/
def leftPad (n : Nat) (c : Char) (s : String) : String :=
  let pad := String.mk (List.replicate (n - s.length) c)
  pad ++ s

/-- All pairs for distinctness (0 ≤ i < j < 16) -/
def allPairs16 : List (Fin 16 × Fin 16) :=
  List.flatten <| List.map (fun i =>
    List.filterMap (fun j =>
      if h : i < j ∧ j < 16 then
        some (⟨i, by omega⟩, ⟨j, h.2⟩)
      else none
    ) (List.range 16)
  ) (List.range 16)

/-- Distinctness constraint: all pieces must be different -/
def distinctPieces (vars : PieceGrid) : Smt Unit := do
  let flat := Vector.flatten vars
  for pair in allPairs16 do
    let (fi, fj) := pair
    let vi := flat.get fi
    let vj := flat.get fj
    assert (¬. (vi =. vj))

/-! ## Main Solver -/

/-- Convert color variables tensor to PieceColors grid -/
def mapColorPieces (cvars : Tensor2D 4 4 (Vector (Expr (Ty.bitVec ColorBitSize)) 4)) : ColorGrid :=
  Tensor2D.map (fun row =>
    { upVar := row.get ⟨0, by omega⟩
    , rightVar := row.get ⟨1, by omega⟩
    , downVar := row.get ⟨2, by omega⟩
    , leftVar := row.get ⟨3, by omega⟩ }
  ) cvars

/-- Declare color piece variables for one cell -/
def declareColorCell (i j : Nat) : Smt (Vector (Expr (Ty.bitVec ColorBitSize)) 4) := do
  let up ← declareBV s!"cx_{i}_{j}_Up" ColorBitSize
  let right ← declareBV s!"cx_{i}_{j}_Right" ColorBitSize
  let down ← declareBV s!"cx_{i}_{j}_Down" ColorBitSize
  let left ← declareBV s!"cx_{i}_{j}_Left" ColorBitSize
  pure ⟨#[up, right, down, left], rfl⟩

/-- Declare all color piece variables -/
def declareColorPieces : Smt (Tensor2D 4 4 (Vector (Expr (Ty.bitVec ColorBitSize)) 4)) := do
  Vector.tabulateM 4 fun i =>
    Vector.tabulateM 4 fun j =>
      declareColorCell i.val j.val

/-- Complete Eternity II SMT program -/
def eternity2 : Smt Unit := do
  -- Declare piece index variables (which piece is at each position)
  let varPieces ← declareBVTensor "x" [4, 4] BitSize
  -- Declare color variables for each piece position
  let varColorPieces ← declareColorPieces
  let colorPieces := mapColorPieces varColorPieces

  -- Constraint 1: All piece indices are valid (0 ≤ x < 16)
  validPieces varPieces

  -- Constraint 2: All pieces are distinct (each piece used exactly once)
  distinctPieces varPieces

  -- Constraint 3: Adjacent edges must match, borders must be 'X'
  colorConstraints colorPieces

  -- Constraint 4: Piece index implies valid color combination
  pieceConstraints varPieces colorPieces

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
  | _ => "\x1b[0m"      -- Reset (unknown)

/-- Get background ANSI color code for a puzzle color character -/
def bgColorCode (c : Char) : String :=
  match c with
  | 'X' => "\x1b[100m"  -- Gray background
  | 'Y' => "\x1b[103m"  -- Yellow background
  | 'B' => "\x1b[104m"  -- Blue background
  | 'U' => "\x1b[105m"  -- Magenta background
  | 'P' => "\x1b[102m"  -- Green background
  | _ => "\x1b[0m"

/-- Colorize a single character -/
def colorChar (c : Char) : String :=
  s!"{bold}{colorCode c}{c}{resetColor}"

/-- Colorize a piece string (4 chars) -/
def colorizePiece (s : String) : String :=
  String.join (s.toList.map colorChar)

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
def displayPieceSolution (model : Model schema) : IO Unit := do
  IO.println "Piece placement (piece index at each position):"
  IO.println "┌────┬────┬────┬────┐"
  for i in [0:4] do
    let mut row := "│"
    for j in [0:4] do
      let name := s!"x_{i}_{j}"
      match model.lookup name with
      | some v =>
        let displayVal := match parseBitVec v with
          | some n => s!"{n}"
          | none => v.take 3
        row := row ++ s!" {leftPad 2 ' ' displayVal} │"
      | none => row := row ++ "  ? │"
    IO.println row
    if i < 3 then
      IO.println "├────┼────┼────┼────┤"
  IO.println "└────┴────┴────┴────┘"

/-- Display the color solution for each cell as a visual grid -/
def displayColorSolution (model : Model schema) : IO Unit := do
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
  for i in [0:4] do
    -- Line 1: Top edges (Up color in center of each cell)
    let mut topLine := "    "
    for j in [0:4] do
      let up := getColorChar i j "Up"
      topLine := topLine ++ s!" {colorChar up}{colorChar up}{colorChar up} "
    IO.println topLine

    -- Line 2: Left, center, Right
    let mut midLine := "    "
    for j in [0:4] do
      let left := getColorChar i j "Left"
      let right := getColorChar i j "Right"
      midLine := midLine ++ s!"{colorChar left}   {colorChar right}"
    IO.println midLine

    -- Line 3: Bottom edges (Down color in center of each cell)
    let mut botLine := "    "
    for j in [0:4] do
      let down := getColorChar i j "Down"
      botLine := botLine ++ s!" {colorChar down}{colorChar down}{colorChar down} "
    IO.println botLine

    -- Separator line between rows (empty line)
    if i < 3 then
      IO.println ""

end Eternity2

open Eternity2 in
def main : IO UInt32 := do
  IO.println s!"{bold}=== Eternity II Puzzle SMT Solver ==={resetColor}"
  IO.println "(Ported from Idris idris-snippets/Eternity2SMT.idr)"
  IO.println "Grid size: 4×4 = 16 pieces"
  IO.println ""

  IO.println s!"{bold}Puzzle pieces:{resetColor}"
  IO.println s!"  {colorChar 'X'}=Border  {colorChar 'Y'}=Yellow  {colorChar 'B'}=Blue  {colorChar 'U'}=Magenta  {colorChar 'P'}=Green"
  IO.println ""

  -- Display puzzle pieces in visual format (4 pieces per row, 4 rows)
  for row in [0:4] do
    -- Line 1: Top edges of 4 pieces
    let mut topLine := "    "
    for col in [0:4] do
      let idx := row * 4 + col
      if hi : idx < 16 then
        let p := puzzle.get ⟨idx, hi⟩
        let up := p.get ⟨0, by omega⟩
        topLine := topLine ++ s!" {colorChar up}{colorChar up}{colorChar up} "
    IO.println topLine

    -- Line 2: Left, piece#, Right
    let mut midLine := "    "
    for col in [0:4] do
      let idx := row * 4 + col
      if hi : idx < 16 then
        let p := puzzle.get ⟨idx, hi⟩
        let left := p.get ⟨3, by omega⟩
        let right := p.get ⟨1, by omega⟩
        midLine := midLine ++ s!"{colorChar left}{leftPad 2 ' ' (toString idx)} {colorChar right}"
    IO.println midLine

    -- Line 3: Bottom edges
    let mut botLine := "    "
    for col in [0:4] do
      let idx := row * 4 + col
      if hi : idx < 16 then
        let p := puzzle.get ⟨idx, hi⟩
        let down := p.get ⟨2, by omega⟩
        botLine := botLine ++ s!" {colorChar down}{colorChar down}{colorChar down} "
    IO.println botLine

    IO.println ""
  IO.println ""

  IO.println "Solving with Z3..."
  IO.println "(This may take a moment...)"
  IO.println ""

  let result ← solve eternity2
  match result with
  | .sat model =>
    IO.println s!"{bold}SAT - Solution found!{resetColor}"
    displayPieceSolution model
    displayColorSolution model
  | .unsat =>
    IO.println "UNSAT - No solution exists"
  | .unknown reason =>
    IO.println s!"Unknown: {reason}"

  return 0
