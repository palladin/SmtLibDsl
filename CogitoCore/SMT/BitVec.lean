/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Core types and type-indexed expressions
-/
namespace CogitoCore.SMT

/-- SMT-LIB sorts for QF_BV theory -/
inductive Ty where
  | bool
  | bitVec (n : Nat)
deriving Repr, DecidableEq

instance : ToString Ty where
  toString
  | Ty.bool => "Bool"
  | Ty.bitVec n => s!"(_ BitVec {n})"

/-- Expressions indexed by sort, ensuring width-correctness at compile time -/
inductive Expr : Ty → Type where
  -- Variables
  | var     : String → (s : Ty) → Expr s

  -- Boolean literals
  | btrue   : Expr Ty.bool
  | bfalse  : Expr Ty.bool

  -- Boolean operations
  | and     : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | or      : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | not     : Expr Ty.bool → Expr Ty.bool
  | imp     : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | ite     : Expr Ty.bool → Expr s → Expr s → Expr s

  -- BitVector literals
  | bvLit   : (val : Nat) → (n : Nat) → Expr (Ty.bitVec n)

  -- BitVector arithmetic (width-preserving)
  | bvAdd   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvSub   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvMul   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvUDiv  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvSDiv  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvURem  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvSMod  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvSRem  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvNeg   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n)

  -- Bitwise operations
  | bvAnd   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvOr    : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvXor   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvNot   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvNand  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvNor   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvXnor  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)

  -- Shifts
  | bvShl   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvLShr  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | bvAShr  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | rotateLeft  : (i : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)
  | rotateRight : (i : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec n)

  -- Comparisons (return Bool)
  | bvEq    : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvULt   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvULe   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvUGt   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvUGe   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSLt   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSLe   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSGt   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSGe   : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvComp  : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr (Ty.bitVec 1)

  -- Width-changing operations
  | concat  : Expr (Ty.bitVec m) → Expr (Ty.bitVec n) → Expr (Ty.bitVec (m + n))
  | extract : (hi lo : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec (hi - lo + 1))
  | zeroExt : (i : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec (n + i))
  | signExt : (i : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec (n + i))
  | repeat  : (i : Nat) → Expr (Ty.bitVec n) → Expr (Ty.bitVec (i * n))

  -- Overflow predicates (return Bool)
  | bvNegO  : Expr (Ty.bitVec n) → Expr Ty.bool
  | bvUAddO : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSAddO : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvUMulO : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool
  | bvSMulO : Expr (Ty.bitVec n) → Expr (Ty.bitVec n) → Expr Ty.bool

-- Smart constructors

/-- Create a bitvector literal with value `val` and width `n` -/
def bv (val n : Nat) : Expr (Ty.bitVec n) := Expr.bvLit val n

/-- Boolean true -/
def btrue : Expr Ty.bool := Expr.btrue

/-- Boolean false -/
def bfalse : Expr Ty.bool := Expr.bfalse

-- Notation (scoped to SMT namespace)

-- BitVector arithmetic
scoped infixl:70 " +. " => Expr.bvAdd
scoped infixl:70 " -. " => Expr.bvSub
scoped infixl:75 " *. " => Expr.bvMul

-- Bitwise operations
scoped infixl:65 " &. " => Expr.bvAnd
scoped infixl:60 " |. " => Expr.bvOr
scoped infixl:60 " ^. " => Expr.bvXor
scoped prefix:80 "~. " => Expr.bvNot

-- Shifts
scoped infixl:55 " <<. " => Expr.bvShl
scoped infixl:55 " >>. " => Expr.bvLShr
scoped infixl:55 " >>>. " => Expr.bvAShr

-- Comparisons
scoped infixl:50 " =. " => Expr.bvEq
scoped infixl:50 " <ᵤ " => Expr.bvULt
scoped infixl:50 " ≤ᵤ " => Expr.bvULe
scoped infixl:50 " >ᵤ " => Expr.bvUGt
scoped infixl:50 " ≥ᵤ " => Expr.bvUGe
scoped infixl:50 " <ₛ " => Expr.bvSLt
scoped infixl:50 " ≤ₛ " => Expr.bvSLe
scoped infixl:50 " >ₛ " => Expr.bvSGt
scoped infixl:50 " ≥ₛ " => Expr.bvSGe

-- Boolean operations
scoped infixl:35 " ∧. " => Expr.and
scoped infixl:30 " ∨. " => Expr.or
scoped infixl:25 " →. " => Expr.imp
scoped prefix:40 "¬. " => Expr.not

end CogitoCore.SMT
