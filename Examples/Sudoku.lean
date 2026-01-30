/-
  SmtLibDsl - Sudoku SMT Solver Example
  Ported from: https://github.com/palladin/idris-snippets/blob/master/src/SudokuSMT.idr

  Uses 4-bit bitvectors to represent Sudoku digits (1-9).
  The puzzle is represented as a 9x9 grid (Tensor [9, 9]).

-/
import SmtLibDsl

open SmtLibDsl.SMT

namespace Sudoku

/-! ## Puzzle Definition -/

/-- Macro for building a 9x9 Sudoku grid with cleaner syntax -/
macro "sudoku!" "[" rows:term,* "]" : term => do
  let rowTerms := rows.getElems
  if rowTerms.size != 9 then
    Lean.Macro.throwError "Expected exactly 9 rows"
  let rec buildRow (elems : Array Lean.Term) : Lean.MacroM Lean.Term := do
    let arr ← `(#[$elems,*])
    `(⟨$arr, rfl⟩)
  let rec buildGrid (i : Nat) : Lean.MacroM (Array Lean.Term) := do
    if i >= 9 then return #[]
    else
      match rowTerms[i]! with
      | `([$elems,*]) =>
        let rowElems := elems.getElems
        if rowElems.size != 9 then
          Lean.Macro.throwError s!"Row {i} must have exactly 9 elements"
        let row ← buildRow rowElems
        let rest ← buildGrid (i + 1)
        return #[row] ++ rest
      | _ => Lean.Macro.throwError "Expected a list literal for each row"
  let rows ← buildGrid 0
  `(⟨#[$rows,*], rfl⟩)

/-- A Sudoku puzzle: 9x9 grid where 0 represents an empty cell -/
def puzzle : Tensor2D 9 9 Nat := sudoku![
  [5, 3, 0,  0, 7, 0,  0, 0, 0],
  [6, 0, 0,  1, 9, 5,  0, 0, 0],
  [0, 9, 8,  0, 0, 0,  0, 6, 0],

  [8, 0, 0,  0, 6, 0,  0, 0, 3],
  [4, 0, 0,  8, 0, 3,  0, 0, 1],
  [7, 0, 0,  0, 2, 0,  0, 0, 6],

  [0, 6, 0,  0, 0, 0,  2, 8, 0],
  [0, 0, 0,  4, 1, 9,  0, 0, 5],
  [0, 0, 0,  0, 8, 0,  0, 7, 9]
]

/-! ## Grid Access using Tensor2D -/

/-- Get a 3×3 box as a Vector 9 -/
def getBox (grid : Tensor2D 9 9 α) (boxRow boxCol : Fin 3) : Vector α 9 :=
  let r0 := boxRow.val * 3
  let c0 := boxCol.val * 3
  Vector.ofFn fun i =>
    grid[r0 + i.val / 3, c0 + i.val % 3]

/-! ## SMT Constraints using Vect -/

/-- Assert all constraints from a Vector -/
def assertAllV (constraints : Vector (Expr Ty.bool) n) : Smt Unit :=
  constraints.foldl (fun acc c => acc >>= fun _ => assert c) (pure ())

/-- Range constraints: all cells must be in 1-9 -/
def rangeConstraints (cells : Vector (Expr (Ty.bitVec 4)) 9) : Vector (Expr Ty.bool) 18 :=
  Vector.ofFn fun i =>
    let cellIdx : Fin 9 := ⟨i.val / 2, by omega⟩
    let cell := cells.get cellIdx
    if i.val % 2 == 0 then bv 1 4 ≤.ᵤ cell else cell ≤.ᵤ bv 9 4

abbrev Grid := Tensor2D 9 9 (Expr (Ty.bitVec 4))

/-- Cell range constraints for entire grid -/
def cellConstraints (vars : Grid) : Smt Unit :=
  Tensor2D.foldRows (fun acc row => acc >>= fun _ => assertAllV (rangeConstraints row)) (pure ()) vars

/-- Row uniqueness constraints -/
def rowConstraints (vars : Grid) : Smt Unit :=
  Tensor2D.foldRows (fun acc row => acc >>= fun _ => assert (distinctV row)) (pure ()) vars

/-- Column uniqueness constraints -/
def colConstraints (vars : Grid) : Smt Unit :=
  Vector.finRange 9 |>.foldl (fun acc c => acc >>= fun _ =>
    assert (distinctV (Tensor2D.getCol vars c))) (pure ())

/-- Box uniqueness constraints -/
def boxConstraints (vars : Grid) : Smt Unit :=
  Vector.finRange 3 |>.foldl (fun acc br =>
    Vector.finRange 3 |>.foldl (fun acc' bc =>
      acc' >>= fun _ => assert (distinctV (getBox vars br bc))) acc) (pure ())

/-- Fixed cell constraints from puzzle input -/
def instanceConstraints (puz : Tensor2D 9 9 Nat) (vars : Grid) : Smt Unit :=
  Tensor2D.foldlWithIndex (fun acc r c puzzleVal =>
    acc >>= fun _ =>
      if puzzleVal != 0 then assert (vars[r.val, c.val] =. bv puzzleVal 4)
      else pure ()) (pure ()) puz

/-! ## Main Sudoku Solver -/

/-- Complete Sudoku SMT program -/
def sudoku : Smt Unit := do
  let vars ← declareBVTensor "x" [9, 9] 4
  cellConstraints vars
  rowConstraints vars
  colConstraints vars
  boxConstraints vars
  instanceConstraints puzzle vars

/-! ## Display Helpers -/

/-- Build a display row string -/
def buildRowStr (row : Vector String 9) : String :=
  s!"│ {row.getN 0} {row.getN 1} {row.getN 2} │ {row.getN 3} {row.getN 4} {row.getN 5} │ {row.getN 6} {row.getN 7} {row.getN 8} │"

/-- Display a 9×9 grid with box separators -/
def displayGrid (grid : Tensor2D 9 9 String) : IO Unit := do
  IO.println "┌───────┬───────┬───────┐"
  IO.println (buildRowStr (Tensor2D.getRowN grid 0))
  IO.println (buildRowStr (Tensor2D.getRowN grid 1))
  IO.println (buildRowStr (Tensor2D.getRowN grid 2))
  IO.println "├───────┼───────┼───────┤"
  IO.println (buildRowStr (Tensor2D.getRowN grid 3))
  IO.println (buildRowStr (Tensor2D.getRowN grid 4))
  IO.println (buildRowStr (Tensor2D.getRowN grid 5))
  IO.println "├───────┼───────┼───────┤"
  IO.println (buildRowStr (Tensor2D.getRowN grid 6))
  IO.println (buildRowStr (Tensor2D.getRowN grid 7))
  IO.println (buildRowStr (Tensor2D.getRowN grid 8))
  IO.println "└───────┴───────┴───────┘"

/-- Display puzzle (0 shown as dot) -/
def displayPuzzle (puz : Tensor2D 9 9 Nat) : IO Unit := do
  IO.println "Puzzle:"
  displayGrid <| Tensor2D.map (fun v => if v == 0 then "." else toString v) puz

/-- Display solution from model -/
def displaySolution (model : Model schema) : IO Unit := do
  IO.println "Solution:"
  displayGrid <| Tensor2D.tabulate 9 9 fun r c =>
    match model.lookup s!"x_{r.val}_{c.val}" with
    | some v => toString (parseBitVec v 4 |>.getD 0).toNat
    | none => "?"

end Sudoku

open Sudoku in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"
  let profile := args.contains "--profile" || args.contains "-p"

  IO.println "=== Sudoku SMT Solver ==="
  IO.println "(Ported from Idris idris-snippets/SudokuSMT.idr)"
  IO.println ""

  displayPuzzle puzzle
  IO.println ""

  IO.println "Solving with Z3..."
  let result ← solve sudoku { dumpSmt := dumpSmt, profile := profile }
  match result with
  | .sat model =>
    IO.println "SAT - Solution found!"
    IO.println ""
    displaySolution model
  | .unsat =>
    IO.println "UNSAT - No solution exists"
  | .unknown reason =>
    IO.println s!"Unknown: {reason}"

  return 0
