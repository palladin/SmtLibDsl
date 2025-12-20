/-
  CogitoCore - Minesweeper SMT Solver Example
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/MinesweeperSMT.idr

  Minesweeper is a puzzle where:
  - Hidden cells contain either a mine (1) or no mine (0)
  - Revealed cells show the count of adjacent mines (0-8)
  - Goal: Identify all mines and safe cells without triggering any mine

  This solver uses SMT to:
  1. Model each cell as a bitvector variable (0 = safe, 1 = mine)
  2. For revealed cells with a number N, constrain that exactly N neighbors are mines
  3. Query which unknown cells MUST be safe (0) or MUST be mines (1)
  4. Automatically reveal safe cells until the entire grid is known
-/
import CogitoCore

open CogitoCore.SMT

namespace Minesweeper

/-! ## Grid Configuration -/

/-- Grid dimensions -/
def gridRows : Nat := 9
def gridCols : Nat := 9

/-- Bit size for cell values (0 or 1, but we use 4 bits for neighbor sums up to 8) -/
def BitSize : Nat := 4

/-- Cell state: -1 = hidden/unknown, 0-8 = revealed (number of adjacent mines) -/
abbrev CellValue := Int

/-- A Minesweeper puzzle grid -/
abbrev Puzzle := Tensor2D gridRows gridCols CellValue

/-- SMT variable grid -/
abbrev SMTGrid := Tensor2D gridRows gridCols (Expr (Ty.bitVec BitSize))

/-! ## Sample Puzzle (from Idris version) -/

/--
  Sample puzzle where:
  - -1 represents an unknown/hidden cell
  - 0-8 represents a revealed cell with that many adjacent mines
-/
def puzzle : Puzzle := ⟨#[
  ⟨#[-1, -1, -1, -1,  1,  0,  0,  1, -1], rfl⟩,
  ⟨#[-1, -1,  2,  1,  1,  0,  0,  1,  1], rfl⟩,
  ⟨#[-1, -1,  1,  0,  0,  0,  0,  0,  0], rfl⟩,
  ⟨#[-1,  2,  1,  0,  0,  0,  0,  0,  0], rfl⟩,
  ⟨#[-1,  2,  0,  0,  0,  0,  0,  0,  0], rfl⟩,
  ⟨#[-1,  3,  1,  0,  0,  0,  1,  1,  1], rfl⟩,
  ⟨#[-1, -1,  1,  0,  0,  0,  1, -1, -1], rfl⟩,
  ⟨#[-1, -1,  2,  2,  1,  1,  1, -1, -1], rfl⟩,
  ⟨#[-1, -1, -1, -1, -1, -1, -1, -1, -1], rfl⟩
], rfl⟩

/-! ## Grid Position Type -/

/-- Position type for boundary handling -/
inductive Pos where
  | first
  | middle
  | last
deriving Repr, DecidableEq

/-- Convert index to position type -/
def toPos (n : Nat) (i : Fin n) : Pos :=
  if i.val == 0 then Pos.first
  else if i.val == n - 1 then Pos.last
  else Pos.middle

/-! ## Direction and Shifting (reused from Life.lean) -/

/-- Direction for grid shifting -/
inductive Dir where
  | left
  | right
  | up
  | down
deriving Repr, DecidableEq

/-- Shift a vector left -/
def shiftLeft (e : α) (v : Vector α n) : Vector α n :=
  Vector.ofFn fun i =>
    if h : i.val + 1 < n then v.get ⟨i.val + 1, h⟩ else e

/-- Shift a vector right -/
def shiftRight (e : α) (v : Vector α n) : Vector α n :=
  Vector.ofFn fun i =>
    if i.val == 0 then e else v.get ⟨i.val - 1, by omega⟩

/-- Shift a 2D grid up -/
def shiftUp (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  shiftLeft (Vector.replicate n e) grid

/-- Shift a 2D grid down -/
def shiftDown (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  shiftRight (Vector.replicate n e) grid

/-- Apply shift directions to a grid -/
def shift (dirs : List Dir) (e : α) (grid : Tensor2D m n α) : Tensor2D m n α :=
  dirs.foldl (fun g d =>
    match d with
    | Dir.left => Vector.map (shiftLeft e) g
    | Dir.right => Vector.map (shiftRight e) g
    | Dir.up => shiftUp e g
    | Dir.down => shiftDown e g
  ) grid

/-- Lookup a cell after applying shifts -/
def lookup (r : Fin m) (c : Fin n) (dirs : List Dir) (e : α) (grid : Tensor2D m n α) : α :=
  (shift dirs e grid).get r c

/-! ## SMT Helpers -/

/-- Integer constant as bitvector -/
def int (n : Nat) : Expr (Ty.bitVec BitSize) := bv n BitSize

/-- Sum a list of bitvector expressions -/
def add (exprs : List (Expr (Ty.bitVec BitSize))) : Expr (Ty.bitVec BitSize) :=
  exprs.foldl (· +. ·) (int 0)

/-- Lookup cell in SMT grid with 0 default for out-of-bounds -/
def lookupCell (r : Fin gridRows) (c : Fin gridCols) (dirs : List Dir) (grid : SMTGrid) : Expr (Ty.bitVec BitSize) :=
  lookup r c dirs (int 0) grid

/-! ## Neighbor Counting Constraints -/

/--
  For a revealed cell at (r, c) with value v, generate the constraint that
  the sum of neighboring mine indicators equals v.

  This handles boundary cases:
  - Corner cells have 3 neighbors
  - Edge cells have 5 neighbors
  - Interior cells have 8 neighbors
-/
def neighborSumConstraint (r : Fin gridRows) (c : Fin gridCols) (v : Nat) (vars : SMTGrid) : Expr Ty.bool :=
  let lookup' := fun dirs => lookupCell r c dirs vars
  let sumExpr := match (toPos gridRows r, toPos gridCols c) with
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
  sumExpr =. int v

/--
  Generate constraint for a single cell:
  - If hidden (-1): cell is either 0 (safe) or 1 (mine)
  - If revealed (0-8): cell must be 0 (not a mine) AND neighbor sum equals the revealed value
-/
def cellConstraint (r : Fin gridRows) (c : Fin gridCols) (puzzleVal : CellValue) (vars : SMTGrid) : Expr Ty.bool :=
  let cell := vars.get r c
  if puzzleVal < 0 then
    -- Hidden cell: must be 0 or 1
    (cell =. int 0) ∨. (cell =. int 1)
  else
    -- Revealed cell: must be 0 (safe) and neighbors sum to puzzleVal
    let v := puzzleVal.toNat
    (cell =. int 0) ∧. neighborSumConstraint r c v vars

/-! ## SMT Problem Construction -/

/-- Build all constraints for the puzzle -/
def buildConstraints (puz : Puzzle) (vars : SMTGrid) : Smt Unit := do
  for r in List.finRange gridRows do
    for c in List.finRange gridCols do
      let puzzleVal := puz.get r c
      assert (cellConstraint r c puzzleVal vars)

/-- Query if a specific cell must be safe (returns true if cell=0 is the only possibility) -/
def queryMustBeSafe (puz : Puzzle) (targetRow : Fin gridRows) (targetCol : Fin gridCols) : Smt Unit := do
  let vars ← declareBVTensor "x" [gridRows, gridCols] BitSize
  buildConstraints puz vars
  -- Assert the target cell is a mine (1) and check for UNSAT
  -- If UNSAT, the cell MUST be safe
  assert (Tensor2D.get vars targetRow targetCol =. int 1)

/-- Query if a specific cell must be a mine (returns true if cell=1 is the only possibility) -/
def queryMustBeMine (puz : Puzzle) (targetRow : Fin gridRows) (targetCol : Fin gridCols) : Smt Unit := do
  let vars ← declareBVTensor "x" [gridRows, gridCols] BitSize
  buildConstraints puz vars
  -- Assert the target cell is safe (0) and check for UNSAT
  -- If UNSAT, the cell MUST be a mine
  assert (Tensor2D.get vars targetRow targetCol =. int 0)

/-! ## Cell Status -/

/-- Status of a cell after SMT analysis -/
inductive CellStatus where
  | hidden       -- Unknown, could be either
  | safe         -- Definitely safe (no mine)
  | mine         -- Definitely a mine
  | revealed (n : Nat)  -- Already revealed with count n
deriving Repr, BEq

/-- Convert puzzle value to initial status -/
def initialStatus (v : CellValue) : CellStatus :=
  if v < 0 then CellStatus.hidden
  else CellStatus.revealed v.toNat

/-! ## Interactive Solver -/

/-- ANSI color codes -/
def resetColor : String := "\x1b[0m"
def bold : String := "\x1b[1m"
def red : String := "\x1b[91m"
def green : String := "\x1b[92m"
def yellow : String := "\x1b[93m"
def blue : String := "\x1b[94m"
def gray : String := "\x1b[90m"
def bgRed : String := "\x1b[41m"
def bgGreen : String := "\x1b[42m"
def bgYellow : String := "\x1b[43m"

/-- Display a cell based on its status -/
def displayCell (status : CellStatus) : String :=
  match status with
  | .hidden => s!"{gray}?{resetColor}"
  | .safe => s!"{green}·{resetColor}"
  | .mine => s!"{red}✱{resetColor}"
  | .revealed 0 => s!"{gray}0{resetColor}"
  | .revealed n => s!"{blue}{n}{resetColor}"

/-- Display the current grid state -/
def displayGrid (status : Tensor2D gridRows gridCols CellStatus) : IO Unit := do
  IO.println "┌───────────────────┐"
  for r in List.finRange gridRows do
    let mut row := "│ "
    for c in List.finRange gridCols do
      row := row ++ displayCell (status.get r c) ++ " "
    row := row ++ "│"
    IO.println row
  IO.println "└───────────────────┘"

/-- Count cells by status -/
def countStatus (status : Tensor2D gridRows gridCols CellStatus) (pred : CellStatus → Bool) : Nat :=
  Tensor2D.foldl (fun acc s => if pred s then acc + 1 else acc) 0 status

/-- Check if a cell is still hidden -/
def isHidden : CellStatus → Bool
  | .hidden => true
  | _ => false

/-- Get list of hidden cell positions -/
def getHiddenCells (status : Tensor2D gridRows gridCols CellStatus) : List (Fin gridRows × Fin gridCols) :=
  List.filterMap id <|
    (List.finRange gridRows).flatMap fun r =>
      (List.finRange gridCols).map fun c =>
        if isHidden (status.get r c) then some (r, c) else none

/-- The actual mine positions for verification (hidden from solver) -/
def actualMines : Tensor2D gridRows gridCols Bool := ⟨#[
  ⟨#[true,  false, false, true,  false, false, false, false, true ], rfl⟩,
  ⟨#[false, true,  false, false, false, false, false, false, false], rfl⟩,
  ⟨#[true,  false, false, false, false, false, false, false, false], rfl⟩,
  ⟨#[true,  false, false, false, false, false, false, false, false], rfl⟩,
  ⟨#[true,  false, false, false, false, false, false, false, false], rfl⟩,
  ⟨#[true,  false, false, false, false, false, false, false, false], rfl⟩,
  ⟨#[true,  true,  false, false, false, false, false, true,  true ], rfl⟩,
  ⟨#[false, true,  false, false, false, false, false, true,  true ], rfl⟩,
  ⟨#[true,  true,  true,  true,  true,  true,  true,  true,  true ], rfl⟩
], rfl⟩

/-- Get the number shown when revealing a cell (count of adjacent mines) -/
def getRevealedValue (r : Fin gridRows) (c : Fin gridCols) : Nat :=
  let offsets : List (Int × Int) := [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]
  offsets.foldl (fun acc (dr, dc) =>
    let nr : Int := r.val + dr
    let nc : Int := c.val + dc
    if h1 : 0 ≤ nr ∧ nr < gridRows then
      if h2 : 0 ≤ nc ∧ nc < gridCols then
        let nr' : Fin gridRows := ⟨nr.toNat, by omega⟩
        let nc' : Fin gridCols := ⟨nc.toNat, by omega⟩
        if actualMines.get nr' nc' then acc + 1 else acc
      else acc
    else acc
  ) 0

/-- Convert status grid back to puzzle for updated solving -/
def statusToPuzzle (status : Tensor2D gridRows gridCols CellStatus) : Puzzle :=
  Tensor2D.tabulate gridRows gridCols fun r c =>
    match status.get r c with
    | .hidden => -1
    | .safe => -1  -- Safe cells need to be revealed to get their number
    | .mine => -1  -- Mines stay hidden in puzzle representation
    | .revealed n => (n : Int)

/-- Update status with newly found safe cells and reveal their numbers -/
def revealSafeCells (status : Tensor2D gridRows gridCols CellStatus)
    (safeCells : List (Fin gridRows × Fin gridCols)) : Tensor2D gridRows gridCols CellStatus :=
  safeCells.foldl (fun s (r, c) =>
    if actualMines.get r c then
      -- This shouldn't happen if solver is correct!
      Tensor2D.tabulate gridRows gridCols fun r' c' =>
        if r == r' && c == c' then CellStatus.mine else s.get r' c'
    else
      let revealedVal := getRevealedValue r c
      Tensor2D.tabulate gridRows gridCols fun r' c' =>
        if r == r' && c == c' then CellStatus.revealed revealedVal else s.get r' c'
  ) status

/-- Update status with newly found mines -/
def markMines (status : Tensor2D gridRows gridCols CellStatus)
    (mineCells : List (Fin gridRows × Fin gridCols)) : Tensor2D gridRows gridCols CellStatus :=
  mineCells.foldl (fun s (r, c) =>
    Tensor2D.tabulate gridRows gridCols fun r' c' =>
      if r == r' && c == c' then CellStatus.mine else s.get r' c'
  ) status

/-- Check if cell must be safe by testing if "cell = mine" is UNSAT -/
def checkMustBeSafe (puz : Puzzle) (r : Fin gridRows) (c : Fin gridCols) : IO Bool := do
  let result ← solve (queryMustBeSafe puz r c)
  match result with
  | .unsat => pure true   -- Cannot be a mine, so must be safe
  | .sat _ => pure false  -- Could be a mine
  | .unknown _ => pure false

/-- Check if cell must be a mine by testing if "cell = safe" is UNSAT -/
def checkMustBeMine (puz : Puzzle) (r : Fin gridRows) (c : Fin gridCols) : IO Bool := do
  let result ← solve (queryMustBeMine puz r c)
  match result with
  | .unsat => pure true   -- Cannot be safe, so must be a mine
  | .sat _ => pure false  -- Could be safe
  | .unknown _ => pure false

/-- One iteration: find all determinable cells -/
def solveIteration (status : Tensor2D gridRows gridCols CellStatus) :
    IO (Tensor2D gridRows gridCols CellStatus × Nat × Nat) := do
  let hiddenCells := getHiddenCells status
  let puz := statusToPuzzle status

  let mut newSafeCells : List (Fin gridRows × Fin gridCols) := []
  let mut newMineCells : List (Fin gridRows × Fin gridCols) := []

  for (r, c) in hiddenCells do
    -- Check if must be safe
    let isSafe ← checkMustBeSafe puz r c
    if isSafe then
      newSafeCells := (r, c) :: newSafeCells
    else
      -- Check if must be a mine
      let isMine ← checkMustBeMine puz r c
      if isMine then
        newMineCells := (r, c) :: newMineCells

  -- Update status
  let status' := revealSafeCells status newSafeCells
  let status'' := markMines status' newMineCells

  pure (status'', newSafeCells.length, newMineCells.length)

/-- Main solving loop -/
partial def solveLoop (status : Tensor2D gridRows gridCols CellStatus) (iteration : Nat) : IO Unit := do
  IO.println s!"\n{bold}=== Iteration {iteration} ==={resetColor}"
  displayGrid status

  let hiddenCount := countStatus status isHidden
  if hiddenCount == 0 then
    IO.println s!"\n{green}{bold}✓ Puzzle completely solved!{resetColor}"
    let mineCount := countStatus status (· == CellStatus.mine)
    let safeCount := countStatus status (fun s => match s with | .revealed _ => true | .safe => true | _ => false)
    IO.println s!"  Mines found: {mineCount}"
    IO.println s!"  Safe cells revealed: {safeCount}"
    return

  IO.println s!"Hidden cells remaining: {hiddenCount}"
  IO.println "Analyzing with SMT solver..."

  let (newStatus, safeFound, minesFound) ← solveIteration status

  if safeFound == 0 && minesFound == 0 then
    IO.println s!"\n{yellow}⚠ No more cells can be determined with current information.{resetColor}"
    IO.println "The puzzle may require guessing or has multiple solutions."
    displayGrid newStatus
    return

  IO.println s!"  {green}Safe cells found: {safeFound}{resetColor}"
  IO.println s!"  {red}Mines identified: {minesFound}{resetColor}"

  solveLoop newStatus (iteration + 1)

end Minesweeper

open Minesweeper in
def main (_args : List String) : IO UInt32 := do
  IO.println s!"{bold}=== Minesweeper SMT Solver ==={resetColor}"
  IO.println "(Ported from Idris idris-snippets/MinesweeperSMT.idr)"
  IO.println ""
  IO.println "This solver uses Z3 to deduce which cells are definitely safe"
  IO.println "or definitely mines, based on the revealed number constraints."
  IO.println ""
  IO.println s!"{bold}Legend:{resetColor}"
  IO.println s!"  {gray}?{resetColor} = Hidden (unknown)"
  IO.println s!"  {green}·{resetColor} = Revealed safe (0 adjacent mines)"
  IO.println s!"  {blue}N{resetColor} = Revealed with N adjacent mines"
  IO.println s!"  {red}✱{resetColor} = Identified mine"
  IO.println ""

  -- Initialize status from puzzle
  let initialStatusGrid := Tensor2D.tabulate gridRows gridCols fun r c =>
    initialStatus (puzzle.get r c)

  solveLoop initialStatusGrid 1

  return 0
