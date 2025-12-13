/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Commands and Smt monad (free monad pattern)
-/
import CogitoCore.SMT.BitVec

namespace CogitoCore.SMT

/-- SMT-LIB commands for QF_BV theory -/
inductive Cmd : Type → Type 1 where
  | declareConst : String → (s : Ty) → Cmd (Expr s)
  | assert       : Expr Ty.bool → Cmd Unit
  | checkSat     : Cmd Unit
  | getModel     : Cmd Unit
  | push         : Cmd Unit
  | pop          : Cmd Unit

/-- Free monad for sequencing SMT commands -/
inductive Smt : Type → Type 1 where
  | pure : α → Smt α
  | bind : Cmd α → (α → Smt β) → Smt β

/-- Bind operation for Smt monad -/
def Smt.flatMap (ma : Smt α) (f : α → Smt β) : Smt β :=
  match ma with
  | .pure a => f a
  | .bind cmd g => .bind cmd (fun x => flatMap (g x) f)

instance : Monad Smt where
  pure := Smt.pure
  bind := Smt.flatMap

-- Command API

/-- Declare a bitvector constant of width n -/
def declareBV (name : String) (n : Nat) : Smt (Expr (Ty.bitVec n)) :=
  Smt.bind (Cmd.declareConst name (Ty.bitVec n)) Smt.pure

/-- Declare a boolean constant -/
def declareBool (name : String) : Smt (Expr Ty.bool) :=
  Smt.bind (Cmd.declareConst name Ty.bool) Smt.pure

/-- Assert a boolean constraint -/
def assert (e : Expr Ty.bool) : Smt Unit := Smt.bind (Cmd.assert e) Smt.pure

/-- Check satisfiability -/
def checkSat : Smt Unit := Smt.bind Cmd.checkSat Smt.pure

/-- Get the model (if sat) -/
def getModel : Smt Unit := Smt.bind Cmd.getModel Smt.pure

/-- Push a context frame -/
def push : Smt Unit := Smt.bind Cmd.push Smt.pure

/-- Pop a context frame -/
def pop : Smt Unit := Smt.bind Cmd.pop Smt.pure

end CogitoCore.SMT
