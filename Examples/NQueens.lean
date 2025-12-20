/-
  CogitoCore - N-Queens SMT Solver Example
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/NQueensSMT.idr

  The N-Queens puzzle places N queens on an N×N chessboard such that:
  - No two queens share the same row
  - No two queens share the same column
  - No two queens share the same diagonal

  This implementation uses bitvector arithmetic (QF_BV) to model:
  - cols[i] = column position of queen in row i
  - All column values must be distinct
  - No two queens on same diagonal: |cols[i] - cols[j]| ≠ |i - j|
-/
import CogitoCore

open CogitoCore.SMT

namespace NQueens

/-! ## Configuration -/

/-- Board size (8×8 for standard chess) -/
def N : Nat := 8

/-- Bit size for column indices (need to represent 0 to N-1) -/
def BitSize : Nat := 8

/-! ## SMT Constraints -/

/-- Valid range constraint: 0 ≤ x < N -/
def validRange (x : Expr (Ty.bitVec BitSize)) : Expr Ty.bool :=
  (bv 0 BitSize ≤ᵤ x) ∧. (x <ᵤ bv N BitSize)

/-- Absolute difference using bitvector operations -/
def absDiff (x y : Expr (Ty.bitVec BitSize)) : Expr (Ty.bitVec BitSize) :=
  -- Use conditional: if x >= y then x - y else y - x
  Expr.ite (x ≥ᵤ y) (x -. y) (y -. x)

/-- Diagonal constraint: queens at rows i and j don't attack diagonally
    |col[i] - col[j]| ≠ |i - j| -/
def notOnDiagonal (colI colJ : Expr (Ty.bitVec BitSize)) (i j : Nat) : Expr Ty.bool :=
  let rowDiff := if i > j then bv (i - j) BitSize else bv (j - i) BitSize
  let colDiff := absDiff colI colJ
  ¬. (colDiff =. rowDiff)

/-- Generate all pairs (i, j) where i < j -/
def allPairs (n : Nat) : List (Nat × Nat) :=
  List.flatten <| List.map (fun i =>
    List.filterMap (fun j =>
      if i < j then some (i, j) else none
    ) (List.range n)
  ) (List.range n)

/-- Build the N-Queens SMT problem -/
def nqueens (n : Nat) : Smt Unit := do
  -- Declare column variables: cols[i] = column of queen in row i
  let mut cols : List (Expr (Ty.bitVec BitSize)) := []
  for i in List.range n do
    let col ← declareBV s!"col_{i}" BitSize
    cols := cols ++ [col]

  -- Constraint 1: All column values are in valid range [0, n)
  for col in cols do
    assert (validRange col)

  -- Constraint 2: All columns are distinct (no two queens in same column)
  for (i, j) in allPairs n do
    match cols[i]?, cols[j]? with
    | some ci, some cj => assert (¬. (ci =. cj))
    | _, _ => pure ()

  -- Constraint 3: No two queens on the same diagonal
  for (i, j) in allPairs n do
    match cols[i]?, cols[j]? with
    | some ci, some cj => assert (notOnDiagonal ci cj i j)
    | _, _ => pure ()

/-! ## Display Helpers -/

/-- ANSI color codes -/
def resetColor : String := "\x1b[0m"
def bold : String := "\x1b[1m"
def yellow : String := "\x1b[93m"
def blue : String := "\x1b[94m"
def white : String := "\x1b[97m"
def bgWhite : String := "\x1b[47m"   -- White background
def bgBlack : String := "\x1b[40m"   -- Black background
def fgBlack : String := "\x1b[30m"   -- Black foreground

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

/-- Display the chessboard with queens -/
def displayBoard (n : Nat) (queenCols : List Nat) : IO Unit := do
  -- Print column headers
  let mut header := "    "
  for j in List.range n do
    header := header ++ s!" {Char.ofNat ('a'.toNat + j)} "
  IO.println header

  -- Print top border
  let mut topBorder := "   ┌"
  for _ in List.range n do
    topBorder := topBorder ++ "───"
  topBorder := topBorder.dropRight 1 ++ "┐"
  IO.println topBorder

  -- Print each row
  for i in List.range n do
    let mut row := s!" {n - i} │"
    for j in List.range n do
      let isQueen := queenCols[i]? == some j
      let isLight := (i + j) % 2 == 0
      if isLight then
        -- Light square (white background)
        let cell := if isQueen then s!"{bgWhite}{fgBlack}{bold} ♛ {resetColor}" else s!"{bgWhite}   {resetColor}"
        row := row ++ cell
      else
        -- Dark square (black background)
        let cell := if isQueen then s!"{bgBlack}{yellow}{bold} ♛ {resetColor}" else s!"{bgBlack}   {resetColor}"
        row := row ++ cell
    row := row ++ s!"│ {n - i}"
    IO.println row

  -- Print bottom border
  let mut botBorder := "   └"
  for _ in List.range n do
    botBorder := botBorder ++ "───"
  botBorder := botBorder.dropRight 1 ++ "┘"
  IO.println botBorder

  -- Print column headers again
  IO.println header

/-- Extract queen positions from the model -/
def extractQueenPositions (n : Nat) (model : Model schema) : List Nat :=
  List.range n |>.map fun i =>
    match model.lookup s!"col_{i}" with
    | some v => parseBitVec v |>.getD 0
    | none => 0

end NQueens

open NQueens in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"

  IO.println s!"{bold}=== N-Queens Puzzle SMT Solver ==={resetColor}"
  IO.println s!"Board size: {N}×{N}"
  IO.println ""

  IO.println "Building SMT constraints..."
  IO.println s!"  - {N} column variables (one per row)"
  IO.println s!"  - {N} range constraints (0 ≤ col < {N})"
  IO.println s!"  - {N * (N - 1) / 2} distinctness constraints"
  IO.println s!"  - {N * (N - 1) / 2} diagonal constraints"
  IO.println ""

  let problem := nqueens N

  if dumpSmt then
    IO.println s!"{bold}SMT-LIB2 Script:{resetColor}"
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println (compile problem)
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println ""

  IO.println "Solving with Z3..."
  let result ← solve problem

  match result with
  | .sat model =>
    IO.println s!"{bold}SAT - Solution found!{resetColor}"
    IO.println ""

    let queenCols := extractQueenPositions N model
    IO.println s!"Queen positions (row → column): {queenCols}"
    IO.println ""

    displayBoard N queenCols
  | .unsat =>
    IO.println "UNSAT - No solution exists (should not happen for N ≥ 4)"
  | .unknown reason =>
    IO.println s!"Unknown: {reason}"

  return 0
