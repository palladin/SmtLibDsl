/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Commands and Smt monad (free monad pattern)
-/
import CogitoCore.SMT.Expr
import CogitoCore.SMT.Tensor

namespace CogitoCore.SMT

/-- SMT-LIB commands for QF_BV theory -/
inductive Cmd : Type → Type _ where
  | declareConst : String → (ty : Ty) → Cmd (Expr ty)
  | assert       : Expr Ty.bool → Cmd Unit
  | checkSat     : Cmd Unit
  | getModel     : Cmd Unit
  | push         : Cmd Unit
  | pop          : Cmd Unit

/-- Free monad for sequencing SMT commands -/
inductive Smt : Type → Type _ where
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

-- Tensor declaration API

/-- Build variable name with indices appended -/
def indexedName (base : String) (indices : List Nat) : String :=
  base ++ String.join (indices.map (fun i => s!"_{i}"))

/-- Declare a single variable -/
def declareVar (name : String) (ty : Ty) : Smt (Expr ty) :=
  Smt.bind (Cmd.declareConst name ty) Smt.pure

/-- Declare a tensor of variables, building the nested Vect structure -/
def declareTensorAux (name : String) (ty : Ty) (prefix_ : List Nat) :
    (dims : List Nat) → Smt (Tensor dims (Expr ty))
  | [] => do
    let varName := indexedName name prefix_
    declareVar varName ty
  | d :: ds => do
    Vect.tabulateM d (fun ⟨i, _⟩ => declareTensorAux name ty (prefix_ ++ [i]) ds)

/-- Declare a tensor of variables with given shape, returning Tensor dims (Expr ty) -/
def declareTensor (name : String) (dims : List Nat) (ty : Ty) : Smt (Tensor dims (Expr ty)) :=
  declareTensorAux name ty [] dims

/-- Declare a bitvector tensor -/
def declareBVTensor (name : String) (dims : List Nat) (n : Nat) : Smt (Tensor dims (Expr (Ty.bitVec n))) :=
  declareTensor name dims (Ty.bitVec n)

/-- Declare a boolean tensor -/
def declareBoolTensor (name : String) (dims : List Nat) : Smt (Tensor dims (Expr Ty.bool)) :=
  declareTensor name dims Ty.bool

end CogitoCore.SMT
