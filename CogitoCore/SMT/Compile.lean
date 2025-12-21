/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Compilation to SMT-LIB2 string format
-/
import CogitoCore.SMT.Cmd

namespace CogitoCore.SMT

/-- Compile an expression to SMT-LIB2 syntax -/
def compileExpr : Expr ty → String
  | .var name _ => name
  | .btrue => "true"
  | .bfalse => "false"
  | .bvLit val n => s!"(_ bv{val} {n})"
  -- Boolean operations
  | .and l r => s!"(and {compileExpr l} {compileExpr r})"
  | .or l r => s!"(or {compileExpr l} {compileExpr r})"
  | .not e => s!"(not {compileExpr e})"
  | .imp l r => s!"(=> {compileExpr l} {compileExpr r})"
  | .ite c t e => s!"(ite {compileExpr c} {compileExpr t} {compileExpr e})"
  -- BitVector arithmetic
  | .bvAdd l r => s!"(bvadd {compileExpr l} {compileExpr r})"
  | .bvSub l r => s!"(bvsub {compileExpr l} {compileExpr r})"
  | .bvMul l r => s!"(bvmul {compileExpr l} {compileExpr r})"
  | .bvUDiv l r => s!"(bvudiv {compileExpr l} {compileExpr r})"
  | .bvSDiv l r => s!"(bvsdiv {compileExpr l} {compileExpr r})"
  | .bvURem l r => s!"(bvurem {compileExpr l} {compileExpr r})"
  | .bvSMod l r => s!"(bvsmod {compileExpr l} {compileExpr r})"
  | .bvSRem l r => s!"(bvsrem {compileExpr l} {compileExpr r})"
  | .bvNeg e => s!"(bvneg {compileExpr e})"
  -- Bitwise operations
  | .bvAnd l r => s!"(bvand {compileExpr l} {compileExpr r})"
  | .bvOr l r => s!"(bvor {compileExpr l} {compileExpr r})"
  | .bvXor l r => s!"(bvxor {compileExpr l} {compileExpr r})"
  | .bvNot e => s!"(bvnot {compileExpr e})"
  | .bvNand l r => s!"(bvnand {compileExpr l} {compileExpr r})"
  | .bvNor l r => s!"(bvnor {compileExpr l} {compileExpr r})"
  | .bvXnor l r => s!"(bvxnor {compileExpr l} {compileExpr r})"
  -- Shifts
  | .bvShl l r => s!"(bvshl {compileExpr l} {compileExpr r})"
  | .bvLShr l r => s!"(bvlshr {compileExpr l} {compileExpr r})"
  | .bvAShr l r => s!"(bvashr {compileExpr l} {compileExpr r})"
  | .rotateLeft i e => s!"((_ rotate_left {i}) {compileExpr e})"
  | .rotateRight i e => s!"((_ rotate_right {i}) {compileExpr e})"
  -- Comparisons
  | .bvEq l r => s!"(= {compileExpr l} {compileExpr r})"
  | .bvULt l r => s!"(bvult {compileExpr l} {compileExpr r})"
  | .bvULe l r => s!"(bvule {compileExpr l} {compileExpr r})"
  | .bvUGt l r => s!"(bvugt {compileExpr l} {compileExpr r})"
  | .bvUGe l r => s!"(bvuge {compileExpr l} {compileExpr r})"
  | .bvSLt l r => s!"(bvslt {compileExpr l} {compileExpr r})"
  | .bvSLe l r => s!"(bvsle {compileExpr l} {compileExpr r})"
  | .bvSGt l r => s!"(bvsgt {compileExpr l} {compileExpr r})"
  | .bvSGe l r => s!"(bvsge {compileExpr l} {compileExpr r})"
  | .bvComp l r => s!"(bvcomp {compileExpr l} {compileExpr r})"
  -- Width-changing
  | .concat l r => s!"(concat {compileExpr l} {compileExpr r})"
  | .extract hi lo e => s!"((_ extract {hi} {lo}) {compileExpr e})"
  | .zeroExt i e => s!"((_ zero_extend {i}) {compileExpr e})"
  | .signExt i e => s!"((_ sign_extend {i}) {compileExpr e})"
  | .repeat i e => s!"((_ repeat {i}) {compileExpr e})"
  -- Overflow predicates
  | .bvNegO e => s!"(bvnego {compileExpr e})"
  | .bvUAddO l r => s!"(bvuaddo {compileExpr l} {compileExpr r})"
  | .bvSAddO l r => s!"(bvsaddo {compileExpr l} {compileExpr r})"
  | .bvUMulO l r => s!"(bvumulo {compileExpr l} {compileExpr r})"
  | .bvSMulO l r => s!"(bvsmulo {compileExpr l} {compileExpr r})"
  -- Array operations
  | .mkArray idxWidth elem v => s!"((as const (Array (_ BitVec {idxWidth}) {elem})) {compileExpr v})"
  | .select arr i => s!"(select {compileExpr arr} {compileExpr i})"
  | .store arr i v => s!"(store {compileExpr arr} {compileExpr i} {compileExpr v})"
  | .arrEq l r => s!"(= {compileExpr l} {compileExpr r})"
  -- Distinct constraint
  | .distinctBV _ names => s!"(distinct {names |> String.intercalate " "})"

/-- Compile a command, returning the result value and SMT-LIB2 string -/
def compileCmd : Cmd α → (α × String)
  | .declareConst name s => (.var name s, s!"(declare-const {name} {s})")
  | .assert e => ((), s!"(assert {compileExpr e})")

/-- Compile an Smt program to SMT-LIB2 string (with QF_ABV logic for arrays + bitvectors) -/
partial def compile (smt : Smt Unit) : String :=
  "(set-logic QF_ABV)\n" ++ compileBody smt ++ "\n(check-sat)\n(get-model)"
where
  compileBody : Smt Unit → String
    | .pure () => ""
    | .bind cmd f =>
      let (a, s) := compileCmd cmd
      let rest := compileBody (f a)
      if rest.isEmpty then s else s ++ "\n" ++ rest

end CogitoCore.SMT
