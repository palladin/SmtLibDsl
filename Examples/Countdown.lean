/-
  SmtLibDsl - Countdown Numbers Game SMT Solver
  Ported from: https://github.com/palladin/fsharp-snippets/blob/master/src/FSharpSnippets/Countdown.fsx

  The Countdown Numbers Game:
  Given a list of numbers and a target, find an arithmetic expression
  using some or all of the numbers (each at most once) with +, -, *, /
  that evaluates to the target.

  Implementation uses:
  - RPN (Reverse Polish Notation) stack-based evaluation
  - BitVector arithmetic for the stack
  - SMT arrays to model the stack
  - op=0: Push a number, op=1: Apply an operator
  - opr: For push, the number; for apply, 0=Add, 1=Sub, 2=Mul, 3=Div
-/
import SmtLibDsl

open SmtLibDsl.SMT

namespace Countdown

/-! ## Configuration -/

/-- Bit width for values (16-bit signed) -/
def W : Nat := 16

/-- Type alias for our bitvector expressions -/
abbrev BV := Expr (Ty.bitVec W)

/-- Type alias for array expressions (stack) -/
abbrev Stack := Expr (Ty.array W (ElemTy.bitVec W))

/-! ## SMT Helpers -/

/-- Create an integer literal -/
def int (v : Int) : BV := bv v.toNat W

/-- Integer 0 -/
def zero : BV := int 0

/-- Integer 1 -/
def one : BV := int 1

/-- Integer 2 -/
def two : BV := int 2

/-- Integer 3 -/
def three : BV := int 3

/-! ## RPN Evaluation Constraints -/

/-- Build the recursive evaluation constraint (matches F# version closely)
    sp: current stack pointer, st: current stack, ops: remaining operations
    Returns (final_sp, final_st, constraint) -/
def evalRec (ops : List (BV × BV)) (target : BV) (sp : BV) (st : Stack) (idx : Nat) :
    Smt (Expr Ty.bool) := do
  match ops with
  | [] =>
    -- Terminal: stack has one element equal to target
    pure ((selectArr st sp =. target) ∧. (sp =. one))
  | (op, opr) :: rest =>
    -- Fresh stack pointer for next state
    let sp' ← declareBV s!"sp_{idx}" W

    -- Stack values at current positions
    let stTop := selectArr st sp           -- stack[sp]
    let stPrev := selectArr st (sp -. one) -- stack[sp-1]

    -- Valid op constraint: push increments sp, apply decrements
    let validOp := Expr.ite (op =. zero)
      (sp' =. (sp +. one))
      (Expr.ite (op =. one)
        (sp' =. (sp -. one))
        Expr.bfalse)

    -- Symmetry breaking for commutative ops
    let validAdd := Expr.ite ((op =. one) ∧. (opr =. zero))
      (stPrev ≤.ₛ stTop)
      Expr.btrue

    -- Subtraction: ensure positive result
    let validSub := Expr.ite ((op =. one) ∧. (opr =. one))
      (stPrev >.ₛ stTop)
      Expr.btrue

    -- Multiplication: neither operand is 1, symmetry breaking
    let validMul := Expr.ite ((op =. one) ∧. (opr =. two))
      ((¬. (stPrev =. one)) ∧. (¬. (stTop =. one)) ∧. (stPrev ≤.ₛ stTop))
      Expr.btrue

    -- Division: exact division, divisor not 0 or 1
    let validDiv := Expr.ite ((op =. one) ∧. (opr =. three))
      ((Expr.bvSMod stPrev stTop =. zero) ∧.
       (¬. (stTop =. one)) ∧.
       (¬. (stTop =. zero)))
      Expr.btrue

    -- Compute the new stack based on operation
    -- For push: st' = store st sp' opr
    -- For apply: st' = store st sp' (apply_op stPrev stTop opr)
    let applyResult := Expr.ite (opr =. zero)
      (stPrev +. stTop)
      (Expr.ite (opr =. one)
        (stPrev -. stTop)
        (Expr.ite (opr =. two)
          (stPrev *. stTop)
          (Expr.bvSDiv stPrev stTop)))

    let stExpr := Expr.ite (op =. zero)
      (storeArr st sp' opr)
      (storeArr st sp' applyResult)

    -- Declare a fresh array variable and assert it equals the computed stack
    -- This prevents exponential blowup by using the variable in recursion
    let st' ← declareArray s!"st_{idx}" W (ElemTy.bitVec W)
    assert (st' =.ₐ stExpr)

    -- Stack pointer must stay positive
    let validSp := sp' >.ₛ zero

    -- Recurse with updated state (using the variable, not the expression)
    let restConstraint ← evalRec rest target sp' st' (idx + 1)

    pure (validOp ∧. validAdd ∧. validSub ∧. validMul ∧. validDiv ∧. validSp ∧. restConstraint)
termination_by ops.length

/-- Constraint that pushed operands are all distinct -/
def distinctOperandsRec (ops : List (BV × BV)) (collected : List BV) (idx : Nat) :
    Smt (Expr Ty.bool) := do
  match ops with
  | [] =>
    -- Use SMT-LIB distinct constraint for all collected operands
    pure (distinct collected)
  | (op, opr) :: rest =>
    -- Fresh variable for tracking pushed operands
    let pushed ← declareBV s!"pushed_{idx}" W
    -- If push, track the operand; otherwise use a sentinel
    let constraint := Expr.ite (op =. zero)
      (pushed =. opr)
      Expr.btrue
    assert constraint
    -- Only add to collected if it's a push
    distinctOperandsRec rest (pushed :: collected) (idx + 1)

/-- Valid range constraints for operations and operands -/
def validRanges (nums : List Int) (ops : List (BV × BV)) : Expr Ty.bool :=
  ops.foldl (fun acc (op, opr) =>
    let opValid := (op =. zero) ∨. (op =. one)
    let pushValid := Expr.ite (op =. zero)
      (nums.foldl (fun acc' n => acc' ∨. (opr =. int n)) Expr.bfalse)
      Expr.btrue
    let applyValid := Expr.ite (op =. one)
      ((opr =. zero) ∨. (opr =. one) ∨. (opr =. two) ∨. (opr =. three))
      Expr.btrue
    acc ∧. opValid ∧. pushValid ∧. applyValid
  ) Expr.btrue

/-! ## RPN Evaluation (for verification) -/

/-- Evaluate an RPN expression given concrete operations -/
def rpnEval (ops : List (Int × Int)) (st : List Int) : Option (List Int) :=
  match ops with
  | [] => some st
  | (op, opr) :: rest =>
    match op with
    | 0 => rpnEval rest (opr :: st)  -- Push
    | 1 =>  -- Apply
      match st with
      | x :: y :: st' =>
        match opr with
        | 0 => rpnEval rest ((y + x) :: st')      -- Add
        | 1 => rpnEval rest ((y - x) :: st')      -- Sub
        | 2 => rpnEval rest ((y * x) :: st')      -- Mul
        | 3 => rpnEval rest ((y / x) :: st')      -- Div
        | _ => none
      | _ => none
    | _ => none

/-! ## Solver -/

/-- Build SMT constraints for the Countdown problem -/
def countdown (nums : List Int) (target : Int) (numInstrs : Nat) : Smt Unit := do
  -- Declare operation variables
  let mut ops : List (BV × BV) := []
  for i in List.range numInstrs do
    let op ← declareBV s!"op_{i}" W
    let opr ← declareBV s!"opr_{i}" W
    ops := ops ++ [(op, opr)]

  -- Assert valid ranges
  assert (validRanges nums ops)

  -- Assert distinct operands
  let distinctConstraint ← distinctOperandsRec ops [] 0
  assert distinctConstraint

  -- Initial state: sp = 0, empty stack
  let sp₀ ← declareBV "sp_init" W
  let st₀ ← declareArray "st_init" W (ElemTy.bitVec W)
  assert (sp₀ =. zero)

  -- Assert evaluation constraint
  let evalConstraint ← evalRec ops (int target) sp₀ st₀ 0
  assert evalConstraint

/-! ## Display Helpers -/

/-- Operator name lookup -/
def oprName : Int → String
  | 0 => "+"
  | 1 => "-"
  | 2 => "*"
  | 3 => "/"
  | _ => "?"

/-- Convert RPN ops to infix expression string -/
def toInfixExpr (ops : List (Int × Int)) : String :=
  let rec go (ops : List (Int × Int)) (stack : List String) : String :=
    match ops with
    | [] =>
      match stack with
      | [result] => result
      | _ => s!"Stack: {stack}"
    | (op, opr) :: rest =>
      match op with
      | 0 => go rest (toString opr :: stack)  -- Push
      | 1 =>  -- Apply
        match stack with
        | x :: y :: st' =>
          let expr := s!"({y} {oprName opr} {x})"
          go rest (expr :: st')
        | _ => s!"Error: stack underflow"
      | _ => s!"Error: invalid op {op}"
  go ops []

/-- Parse bitvector string from model -/
def parseBV (s : String) : Option Int :=
  if s.startsWith "#x" then
    let hex := s.drop 2
    hex.foldl (fun acc c =>
      acc.bind fun a =>
        if '0' ≤ c ∧ c ≤ '9' then some (a * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c ∧ c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c ∧ c ≤ 'F' then some (a * 16 + (c.toNat - 'A'.toNat + 10))
        else none
    ) (some 0)
    |>.map fun n => if n ≥ 32768 then n - 65536 else n  -- Handle signed
  else if s.startsWith "#b" then
    let bin := s.drop 2
    bin.foldl (fun acc c =>
      acc.bind fun a =>
        if c == '0' then some (a * 2)
        else if c == '1' then some (a * 2 + 1)
        else none
    ) (some 0)
    |>.map fun n => if n ≥ 32768 then n - 65536 else n
  else
    s.toInt?

/-- Extract solution from model -/
def extractSolution (model : Model schema) (numInstrs : Nat) : List (Int × Int) :=
  List.range numInstrs |>.filterMap fun i =>
    match model.lookup s!"op_{i}", model.lookup s!"opr_{i}" with
    | some opStr, some oprStr =>
      match parseBV opStr, parseBV oprStr with
      | some op, some opr => some (op, opr)
      | _, _ => none
    | _, _ => none

end Countdown

open Countdown in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"
  let profile := args.contains "--profile" || args.contains "-p"

  -- Default puzzle: classic Countdown example
  let nums := [1, 3, 7, 10, 25, 50]
  let target := 765
  let maxInstrs := 11  -- Maximum number of RPN instructions to try

  IO.println "=== Countdown Numbers Game SMT Solver ==="
  IO.println "(Ported from F# fsharp-snippets/Countdown.fsx)"
  IO.println ""
  IO.println s!"Numbers: {nums}"
  IO.println s!"Target: {target}"
  IO.println ""

  -- Try with increasing number of instructions
  for numInstrs in List.range maxInstrs do
    let n := numInstrs + 3  -- Start with at least 3 instructions (2 push + 1 apply)
    IO.println s!"Trying with {n} instructions..."

    let problem := countdown nums target n
    IO.println "Problem is set up."
    let result ← solve problem { dumpSmt := dumpSmt, profile := profile }
    match result with
    | .sat model =>
      IO.println s!"SAT - Solution found with {n} instructions!"
      IO.println ""

      let ops := extractSolution model n
      IO.println s!"RPN operations: {ops}"
      IO.println s!"Expression: {toInfixExpr ops}"

      -- Verify
      match rpnEval ops [] with
      | some [result] =>
        IO.println s!"Verification: {result}"
        if result == target then
          IO.println "✓ Correct!"
        else
          IO.println "✗ Verification failed!"
      | _ =>
        IO.println "✗ Could not verify (stack error)"

      return 0
    | .unsat =>
      IO.println s!"  No solution with {n} instructions"
    | .unknown reason =>
      IO.println s!"  Unknown: {reason}"

  IO.println ""
  IO.println "No solution found within instruction limit."
  return 1
