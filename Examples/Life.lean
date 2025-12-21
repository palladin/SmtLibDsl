/-
  CogitoCore - Conway's Game of Life SMT Solver Example
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/LifeSMT.idr

  Given a target pattern, finds an initial pattern that evolves into it
  after one step of Conway's Game of Life.

  Uses integer variables (0 or 1) to represent cell states.
  The solver finds an initial board configuration that transitions to the target pattern.
-/
import CogitoCore

open CogitoCore.SMT

namespace Life

/-! ## Grid Configuration -/

/-- Grid dimensions for the Game of Life board (from Knuth's TAOCP Figure 35, with 1-cell padding) -/
def gridRows : Nat := 9
def gridCols : Nat := 17

/-- A board pattern (0 = dead, 1 = alive) -/
abbrev Pattern := Tensor2D gridRows gridCols Nat

/-! ## Patterns from Knuth's TAOCP Figure 35 (with 1-cell padding) -/

/--
  Initial pattern (Generation 0) from Knuth's TAOCP Figure 35.
  After 3 transitions, this evolves into the "LIFE" pattern.
  Padded with 1 cell of zeros on all sides.
-/
def initialPattern : Pattern := ⟨#[
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
  ⟨#[0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,0,1,0,0,1,0,1,0,1,0,0], rfl⟩,
  ⟨#[0,1,0,1,1,1,1,1,1,0,0,0,0,1,0,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0], rfl⟩,
  ⟨#[0,1,0,1,0,0,0,1,1,0,1,0,0,1,0,1,0], rfl⟩,
  ⟨#[0,0,0,1,1,1,1,1,0,0,1,0,0,1,1,0,0], rfl⟩,
  ⟨#[0,1,1,0,1,0,0,1,0,0,0,0,1,0,0,0,0], rfl⟩,
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩
], rfl⟩

/--
  Final "LIFE" pattern (Generation 3) from Knuth's TAOCP Figure 35.
  This is the target pattern we want to reach.
  Padded with 1 cell of zeros on all sides.
-/
def lifePattern : Pattern := ⟨#[
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,1,0,1,1,1,0,1,1,1,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,1,0,1,1,0,0,1,1,0,0,0], rfl⟩,
  ⟨#[0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0], rfl⟩,
  ⟨#[0,0,1,1,1,0,1,0,1,0,0,0,1,1,1,0,0], rfl⟩,
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩
], rfl⟩

/-! ## Grid Position Type -/

/-- Position in the grid: First, Middle, or Last -/
inductive Pos where
  | first
  | middle
  | last
deriving Repr, DecidableEq

/-- Convert a Fin index to a position type -/
def toPos (n : Nat) (i : Fin n) : Pos :=
  if i.val == 0 then Pos.first
  else if i.val == n - 1 then Pos.last
  else Pos.middle

/-! ## Grid Shifting Operations -/

/-- Shift a vector left by one position, filling with a default value -/
def shiftLeft (e : α) (v : Vector α n) : Vector α n :=
  Vector.ofFn fun i =>
    if h : i.val + 1 < n then v.get ⟨i.val + 1, h⟩ else e

/-- Shift a vector right by one position, filling with a default value -/
def shiftRight (e : α) (v : Vector α n) : Vector α n :=
  Vector.ofFn fun i =>
    if i.val == 0 then e else v.get ⟨i.val - 1, by omega⟩

/-- Shift a 2D grid up by one position -/
def shiftUp (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  shiftLeft (Vector.replicate n e) grid

/-- Shift a 2D grid down by one position -/
def shiftDown (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  shiftRight (Vector.replicate n e) grid

/-- Direction for grid shifting -/
inductive Dir where
  | left
  | right
  | up
  | down
deriving Repr, DecidableEq

/-- Apply a list of shift directions to a grid -/
def shift (dirs : List Dir) (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  dirs.foldl (fun g d =>
    match d with
    | Dir.left => Vector.map (shiftLeft e) g
    | Dir.right => Vector.map (shiftRight e) g
    | Dir.up => shiftUp e g
    | Dir.down => shiftDown e g
  ) grid

/-- Lookup a cell at position after applying shifts -/
def lookup (r : Fin m) (c : Fin n) (dirs : List Dir) (e : α) (grid : Tensor2D m n α) : α :=
  (shift dirs e grid).get r c

/-! ## SMT Grid Type -/

abbrev SMTGrid := Tensor2D gridRows gridCols (Expr (Ty.bitVec 4))

/-- Integer constant in SMT (using 4-bit bitvector) -/
def int (n : Nat) : Expr (Ty.bitVec 4) := bv n 4

/-- Add a list of SMT expressions -/
def add (exprs : List (Expr (Ty.bitVec 4))) : Expr (Ty.bitVec 4) :=
  exprs.foldl (· +. ·) (int 0)

/-! ## Neighbor Counting -/

/-- Lookup with default 0 for out-of-bounds -/
def lookupCell (r : Fin gridRows) (c : Fin gridCols) (dirs : List Dir) (grid : SMTGrid) : Expr (Ty.bitVec 4) :=
  lookup r c dirs (int 0) grid

/-- Count live neighbors for a cell, handling boundary conditions -/
def countNeighborhoods (r : Fin gridRows) (c : Fin gridCols) (grid : SMTGrid) : Expr (Ty.bitVec 4) :=
  let lookup' := fun dirs => lookupCell r c dirs grid
  match (toPos gridRows r, toPos gridCols c) with
  -- Corners: 3 neighbors
  | (Pos.first, Pos.first) =>
    add [lookup' [Dir.left], lookup' [Dir.up], lookup' [Dir.up, Dir.left]]
  | (Pos.last, Pos.last) =>
    add [lookup' [Dir.right], lookup' [Dir.down], lookup' [Dir.down, Dir.right]]
  | (Pos.first, Pos.last) =>
    add [lookup' [Dir.right], lookup' [Dir.up], lookup' [Dir.up, Dir.right]]
  | (Pos.last, Pos.first) =>
    add [lookup' [Dir.left], lookup' [Dir.down], lookup' [Dir.down, Dir.left]]
  -- Edges: 5 neighbors
  | (Pos.first, Pos.middle) =>
    add [lookup' [Dir.left], lookup' [Dir.right], lookup' [Dir.up],
         lookup' [Dir.up, Dir.right], lookup' [Dir.up, Dir.left]]
  | (Pos.last, Pos.middle) =>
    add [lookup' [Dir.left], lookup' [Dir.right], lookup' [Dir.down],
         lookup' [Dir.down, Dir.right], lookup' [Dir.down, Dir.left]]
  | (Pos.middle, Pos.first) =>
    add [lookup' [Dir.left], lookup' [Dir.down], lookup' [Dir.down, Dir.left],
         lookup' [Dir.up], lookup' [Dir.up, Dir.left]]
  | (Pos.middle, Pos.last) =>
    add [lookup' [Dir.right], lookup' [Dir.down], lookup' [Dir.down, Dir.right],
         lookup' [Dir.up], lookup' [Dir.up, Dir.right]]
  -- Interior: 8 neighbors
  | (Pos.middle, Pos.middle) =>
    add [lookup' [Dir.left], lookup' [Dir.right], lookup' [Dir.down],
         lookup' [Dir.up], lookup' [Dir.down, Dir.right], lookup' [Dir.down, Dir.left],
         lookup' [Dir.up, Dir.right], lookup' [Dir.up, Dir.left]]

/-! ## Game of Life Rules -/

/-- Conway's Game of Life rule for a single cell -/
def cellRule (r : Fin gridRows) (c : Fin gridCols) (counters fromBoard toBoard : SMTGrid) : Expr Ty.bool :=
  let cnt := counters.get r c
  let from_ := fromBoard.get r c
  let to_ := toBoard.get r c
  -- Constraint: cnt equals the actual neighbor count
  let eqCnt := (countNeighborhoods r c fromBoard) =. cnt
  -- Constraint: from is 0 or 1
  let eqFrom := (from_ =. int 0) ∨. (from_ =. int 1)
  -- Constraint: to is 0 or 1
  let eqTo := (to_ =. int 0) ∨. (to_ =. int 1)
  -- Game of Life rules:
  -- If cell is alive (from == 1):
  --   - Dies if cnt < 2 (underpopulation) or cnt > 3 (overpopulation)
  --   - Lives if cnt == 2 or cnt == 3
  -- If cell is dead (from == 0):
  --   - Becomes alive if cnt == 3 (reproduction)
  --   - Stays dead otherwise
  let rule :=
    Expr.ite (from_ =. int 1)
      -- Cell is alive
      (Expr.ite ((cnt =. int 0) ∨. (cnt =. int 1))
        (to_ =. int 0)  -- Dies from underpopulation
        (Expr.ite ((cnt =. int 4) ∨. (cnt =. int 5) ∨. (cnt =. int 6) ∨. (cnt =. int 7) ∨. (cnt =. int 8))
          (to_ =. int 0)  -- Dies from overpopulation
          (Expr.ite ((cnt =. int 2) ∨. (cnt =. int 3))
            (to_ =. int 1)  -- Survives
            Expr.bfalse)))
      -- Cell is dead
      (Expr.ite (cnt =. int 3)
        (to_ =. int 1)  -- Reproduction
        (to_ =. int 0))  -- Stays dead
  eqCnt ∧. eqFrom ∧. eqTo ∧. rule

/-- Apply rules to all cells -/
def rules (counters fromBoard toBoard : SMTGrid) : Smt Unit := do
  for r in List.finRange gridRows do
    for c in List.finRange gridCols do
      assert (cellRule r c counters fromBoard toBoard)

/-! ## Pattern Validation -/

/-- Assert that a board matches a given pattern -/
def validPattern (pattern : Pattern) (board : SMTGrid) : Smt Unit := do
  for r in List.finRange gridRows do
    for c in List.finRange gridCols do
      let patternVal := pattern.get r c
      let boardCell := board.get r c
      assert (boardCell =. int patternVal)

/-! ## Main Solver -/

/-- Find initial state that evolves to "LIFE" pattern -/
def life : Smt Unit := do
  -- Declare the initial board (unknowns to solve for)
  let initBoard ← declareBVTensor "x" [gridRows, gridCols] 4
  -- Declare the final board (will be constrained to match lifePattern)
  let finalBoard ← declareBVTensor "y" [gridRows, gridCols] 4
  -- Declare counter variables (for neighbor counts)
  let counters ← declareBVTensor "c" [gridRows, gridCols] 4
  -- Apply Game of Life rules
  rules counters initBoard finalBoard
  -- Constrain final board to match "LIFE" pattern
  validPattern lifePattern finalBoard

/-- Verify forward: Assert initial pattern, apply 3 steps, check final equals LIFE -/
def verifyForward : Smt Unit := do
  -- Declare boards for each generation
  let gen0 ← declareBVTensor "g0" [gridRows, gridCols] 4
  let gen1 ← declareBVTensor "g1" [gridRows, gridCols] 4
  let gen2 ← declareBVTensor "g2" [gridRows, gridCols] 4
  let gen3 ← declareBVTensor "g3" [gridRows, gridCols] 4
  -- Counters for each step
  let c1 ← declareBVTensor "c1" [gridRows, gridCols] 4
  let c2 ← declareBVTensor "c2" [gridRows, gridCols] 4
  let c3 ← declareBVTensor "c3" [gridRows, gridCols] 4
  -- Assert gen0 equals the known initial pattern
  validPattern initialPattern gen0
  -- Apply 3 steps of Game of Life rules
  rules c1 gen0 gen1
  rules c2 gen1 gen2
  rules c3 gen2 gen3
  -- Assert gen3 equals the expected LIFE pattern
  validPattern lifePattern gen3

/-! ## Display Helpers -/

/-- Display a pattern -/
def displayPattern (name : String) (pattern : Pattern) : IO Unit := do
  IO.println s!"{name}:"
  for r in List.finRange gridRows do
    let row := (List.finRange gridCols).map fun c =>
      if pattern.get r c == 1 then "█" else "·"
    IO.println ("  " ++ String.intercalate " " row)

/-- Extract board from model -/
def extractBoard (prefix_ : String) (model : Model schema) : Pattern :=
  Tensor2D.tabulate gridRows gridCols fun r c =>
    match model.lookup s!"{prefix_}_{r.val}_{c.val}" with
    | some v => (parseBitVec v 4 |>.getD 0).toNat
    | none => 0

/-- Display solution from model -/
def displaySolution (model : Model schema) : IO Unit := do
  IO.println "Found initial state that evolves to 'LIFE' pattern!"
  IO.println ""
  IO.println "Initial state (what we solved for):"
  let initBoard := extractBoard "x" model
  for r in List.finRange gridRows do
    let row := (List.finRange gridCols).map fun c =>
      if initBoard.get r c == 1 then "█" else "·"
    IO.println ("  " ++ String.intercalate " " row)
  IO.println ""
  IO.println "Target state ('LIFE' pattern):"
  for r in List.finRange gridRows do
    let row := (List.finRange gridCols).map fun c =>
      if lifePattern.get r c == 1 then "█" else "·"
    IO.println ("  " ++ String.intercalate " " row)

/-- Check if two patterns are equal -/
def patternsEqual (p1 p2 : Pattern) : Bool :=
  (List.finRange gridRows).all fun r =>
    (List.finRange gridCols).all fun c =>
      p1.get r c == p2.get r c

end Life

open Life in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"
  let profile := args.contains "--profile" || args.contains "-p"

  IO.println "=== Conway's Game of Life - SMT Verification ==="
  IO.println "(Verifying Knuth's TAOCP Figure 35)"
  IO.println ""

  displayPattern "Initial pattern (Generation 0)" initialPattern
  IO.println ""
  displayPattern "Expected final 'LIFE' pattern (Generation 3)" lifePattern
  IO.println ""

  IO.println "Using Z3 to verify: initialPattern →³ lifePattern"
  IO.println ""

  let result ← solve verifyForward { profile := profile, dumpSmt := dumpSmt }
  match result with
  | .sat _model =>
    IO.println "✓ SAT - Z3 confirms the initial pattern evolves to 'LIFE' after 3 steps!"
  | .unsat =>
    IO.println "✗ UNSAT - The initial pattern does NOT evolve to 'LIFE' after 3 steps."
    IO.println "         (The pattern transcription from the PDF may be incorrect)"
  | .unknown reason =>
    IO.println s!"Unknown: {reason}"

  return 0
