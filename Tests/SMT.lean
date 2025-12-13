/-
  CogitoCore - SMT DSL Tests
  Unit tests for the BitVector SMT-LIB DSL
-/
import LSpec
import CogitoCore.SMT

open CogitoCore.SMT
open LSpec

-- Test compileExpr for various expression types
def compileExprTests : TestSeq :=
  group "compileExpr" $
    -- Literals
    test "btrue" (compileExpr Expr.btrue = "true") $
    test "bfalse" (compileExpr Expr.bfalse = "false") $
    test "bvLit" (compileExpr (bv 42 8) = "(_ bv42 8)") $
    test "bvLit 16-bit" (compileExpr (bv 255 16) = "(_ bv255 16)") $
    -- Variables
    test "var bool" (compileExpr (Expr.var "x" Ty.bool) = "x") $
    test "var bv8" (compileExpr (Expr.var "y" (Ty.bitVec 8)) = "y") $
    -- Boolean operations
    test "and" (compileExpr (Expr.and Expr.btrue Expr.bfalse) = "(and true false)") $
    test "or" (compileExpr (Expr.or Expr.btrue Expr.bfalse) = "(or true false)") $
    test "not" (compileExpr (Expr.not Expr.btrue) = "(not true)") $
    test "imp" (compileExpr (Expr.imp Expr.btrue Expr.bfalse) = "(=> true false)") $
    -- BitVector arithmetic
    test "bvAdd" (compileExpr (Expr.bvAdd (bv 1 8) (bv 2 8)) = "(bvadd (_ bv1 8) (_ bv2 8))") $
    test "bvSub" (compileExpr (Expr.bvSub (bv 5 8) (bv 3 8)) = "(bvsub (_ bv5 8) (_ bv3 8))") $
    test "bvMul" (compileExpr (Expr.bvMul (bv 2 8) (bv 3 8)) = "(bvmul (_ bv2 8) (_ bv3 8))") $
    test "bvNeg" (compileExpr (Expr.bvNeg (bv 5 8)) = "(bvneg (_ bv5 8))") $
    test "bvUDiv" (compileExpr (Expr.bvUDiv (bv 10 8) (bv 2 8)) = "(bvudiv (_ bv10 8) (_ bv2 8))") $
    test "bvSDiv" (compileExpr (Expr.bvSDiv (bv 10 8) (bv 2 8)) = "(bvsdiv (_ bv10 8) (_ bv2 8))") $
    test "bvURem" (compileExpr (Expr.bvURem (bv 10 8) (bv 3 8)) = "(bvurem (_ bv10 8) (_ bv3 8))") $
    test "bvSMod" (compileExpr (Expr.bvSMod (bv 10 8) (bv 3 8)) = "(bvsmod (_ bv10 8) (_ bv3 8))") $
    test "bvSRem" (compileExpr (Expr.bvSRem (bv 10 8) (bv 3 8)) = "(bvsrem (_ bv10 8) (_ bv3 8))") $
    -- Bitwise operations
    test "bvAnd" (compileExpr (Expr.bvAnd (bv 0xFF 8) (bv 0x0F 8)) = "(bvand (_ bv255 8) (_ bv15 8))") $
    test "bvOr" (compileExpr (Expr.bvOr (bv 0xF0 8) (bv 0x0F 8)) = "(bvor (_ bv240 8) (_ bv15 8))") $
    test "bvXor" (compileExpr (Expr.bvXor (bv 0xFF 8) (bv 0x0F 8)) = "(bvxor (_ bv255 8) (_ bv15 8))") $
    test "bvNot" (compileExpr (Expr.bvNot (bv 0 8)) = "(bvnot (_ bv0 8))") $
    test "bvNand" (compileExpr (Expr.bvNand (bv 1 8) (bv 2 8)) = "(bvnand (_ bv1 8) (_ bv2 8))") $
    test "bvNor" (compileExpr (Expr.bvNor (bv 1 8) (bv 2 8)) = "(bvnor (_ bv1 8) (_ bv2 8))") $
    test "bvXnor" (compileExpr (Expr.bvXnor (bv 1 8) (bv 2 8)) = "(bvxnor (_ bv1 8) (_ bv2 8))") $
    -- Shifts
    test "bvShl" (compileExpr (Expr.bvShl (bv 1 8) (bv 2 8)) = "(bvshl (_ bv1 8) (_ bv2 8))") $
    test "bvLShr" (compileExpr (Expr.bvLShr (bv 8 8) (bv 2 8)) = "(bvlshr (_ bv8 8) (_ bv2 8))") $
    test "bvAShr" (compileExpr (Expr.bvAShr (bv 8 8) (bv 2 8)) = "(bvashr (_ bv8 8) (_ bv2 8))") $
    test "rotateLeft" (compileExpr (Expr.rotateLeft 2 (bv 1 8)) = "((_ rotate_left 2) (_ bv1 8))") $
    test "rotateRight" (compileExpr (Expr.rotateRight 2 (bv 1 8)) = "((_ rotate_right 2) (_ bv1 8))") $
    -- Comparisons
    test "bvEq" (compileExpr (Expr.bvEq (bv 5 8) (bv 5 8)) = "(= (_ bv5 8) (_ bv5 8))") $
    test "bvULt" (compileExpr (Expr.bvULt (bv 1 8) (bv 2 8)) = "(bvult (_ bv1 8) (_ bv2 8))") $
    test "bvULe" (compileExpr (Expr.bvULe (bv 1 8) (bv 2 8)) = "(bvule (_ bv1 8) (_ bv2 8))") $
    test "bvUGt" (compileExpr (Expr.bvUGt (bv 2 8) (bv 1 8)) = "(bvugt (_ bv2 8) (_ bv1 8))") $
    test "bvUGe" (compileExpr (Expr.bvUGe (bv 2 8) (bv 1 8)) = "(bvuge (_ bv2 8) (_ bv1 8))") $
    test "bvSLt" (compileExpr (Expr.bvSLt (bv 1 8) (bv 2 8)) = "(bvslt (_ bv1 8) (_ bv2 8))") $
    test "bvSLe" (compileExpr (Expr.bvSLe (bv 1 8) (bv 2 8)) = "(bvsle (_ bv1 8) (_ bv2 8))") $
    test "bvSGt" (compileExpr (Expr.bvSGt (bv 2 8) (bv 1 8)) = "(bvsgt (_ bv2 8) (_ bv1 8))") $
    test "bvSGe" (compileExpr (Expr.bvSGe (bv 2 8) (bv 1 8)) = "(bvsge (_ bv2 8) (_ bv1 8))") $
    test "bvComp" (compileExpr (Expr.bvComp (bv 5 8) (bv 5 8)) = "(bvcomp (_ bv5 8) (_ bv5 8))") $
    -- Width-changing
    test "concat" (compileExpr (Expr.concat (bv 1 4) (bv 2 4)) = "(concat (_ bv1 4) (_ bv2 4))") $
    test "extract" (compileExpr (Expr.extract 7 4 (bv 255 8)) = "((_ extract 7 4) (_ bv255 8))") $
    test "zeroExt" (compileExpr (Expr.zeroExt 8 (bv 255 8)) = "((_ zero_extend 8) (_ bv255 8))") $
    test "signExt" (compileExpr (Expr.signExt 8 (bv 255 8)) = "((_ sign_extend 8) (_ bv255 8))") $
    test "repeat" (compileExpr (Expr.repeat 4 (bv 1 8)) = "((_ repeat 4) (_ bv1 8))") $
    -- Overflow predicates
    test "bvNegO" (compileExpr (Expr.bvNegO (bv 128 8)) = "(bvnego (_ bv128 8))") $
    test "bvUAddO" (compileExpr (Expr.bvUAddO (bv 200 8) (bv 100 8)) = "(bvuaddo (_ bv200 8) (_ bv100 8))") $
    test "bvSAddO" (compileExpr (Expr.bvSAddO (bv 100 8) (bv 100 8)) = "(bvsaddo (_ bv100 8) (_ bv100 8))") $
    test "bvUMulO" (compileExpr (Expr.bvUMulO (bv 20 8) (bv 20 8)) = "(bvumulo (_ bv20 8) (_ bv20 8))") $
    test "bvSMulO" (compileExpr (Expr.bvSMulO (bv 20 8) (bv 20 8)) = "(bvsmulo (_ bv20 8) (_ bv20 8))")

-- Test Ty ToString
def tyTests : TestSeq :=
  group "Ty.toString" $
    test "bool" (toString Ty.bool = "Bool") $
    test "bitVec 8" (toString (Ty.bitVec 8) = "(_ BitVec 8)") $
    test "bitVec 32" (toString (Ty.bitVec 32) = "(_ BitVec 32)")

-- Test compileCmd
def compileCmdTests : TestSeq :=
  group "compileCmd" $
    test "declareConst" ((compileCmd (Cmd.declareConst "x" (Ty.bitVec 8))).2 = "(declare-const x (_ BitVec 8))") $
    test "checkSat" ((compileCmd Cmd.checkSat).2 = "(check-sat)") $
    test "getModel" ((compileCmd Cmd.getModel).2 = "(get-model)") $
    test "push" ((compileCmd Cmd.push).2 = "(push)") $
    test "pop" ((compileCmd Cmd.pop).2 = "(pop)")

-- Test full program compilation
def compileTests : TestSeq :=
  group "compile" $
    test "simple program" (
      let prog : Smt Unit := do
        let x ← declareBV "x" 8
        assert (x =. bv 5 8)
        checkSat
      compile prog = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x (_ bv5 8)))\n(check-sat)"
    )

-- All tests
def allTests : TestSeq :=
  tyTests ++ compileExprTests ++ compileCmdTests ++ compileTests

-- Main entry point for running tests
def main : IO UInt32 := do
  let (success, msg) := allTests.run
  if success then
    IO.println msg
    return 0
  else
    IO.eprintln msg
    return 1
