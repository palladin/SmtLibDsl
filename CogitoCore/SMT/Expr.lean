/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Core types and type-indexed expressions
-/
namespace CogitoCore.SMT

/-- Element types for arrays (base types only, no nested arrays) -/
inductive ElemTy where
  | bool
  | bitVec (n : Nat)
deriving Repr, DecidableEq

/-- Convert ElemTy to SMT-LIB2 syntax string -/
def ElemTy.toSmtLib : ElemTy → String
  | ElemTy.bool => "Bool"
  | ElemTy.bitVec n => s!"(_ BitVec {n})"

instance : ToString ElemTy where
  toString := ElemTy.toSmtLib

/-- SMT-LIB sorts for QF_ABV theory (arrays + bitvectors) -/
inductive Ty where
  | bool
  | bitVec (n : Nat)
  | array (idxWidth : Nat) (elem : ElemTy)  -- Array (BitVec idxWidth) elem
deriving Repr, DecidableEq

/-- Convert ElemTy to Ty -/
def ElemTy.toTy : ElemTy → Ty
  | ElemTy.bool => Ty.bool
  | ElemTy.bitVec n => Ty.bitVec n

/-- Convert Ty to SMT-LIB2 syntax string -/
def Ty.toSmtLib : Ty → String
  | Ty.bool => "Bool"
  | Ty.bitVec n => s!"(_ BitVec {n})"
  | Ty.array idxWidth elem => s!"(Array (_ BitVec {idxWidth}) {elem.toSmtLib})"

instance : ToString Ty where
  toString := Ty.toSmtLib

/-- Map SMT types to corresponding Lean types -/
def Ty.LeanType : Ty → Type
  | Ty.bool => Bool
  | Ty.bitVec n => BitVec n
  | Ty.array _ _ => Unit  -- Arrays don't have a simple Lean representation

/-- Map ElemTy to corresponding Lean types -/
def ElemTy.LeanType : ElemTy → Type
  | ElemTy.bool => Bool
  | ElemTy.bitVec n => BitVec n

/-- Parse an SMT-LIB boolean value to Lean Bool -/
def parseBool (s : String) : Option Bool :=
  if s == "true" then some true
  else if s == "false" then some false
  else none

/-- Parse a hexadecimal character to its value -/
private def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a hexadecimal string to Nat -/
private def hexToNat? (s : String) : Option Nat :=
  s.foldl (fun acc c => do
    let a ← acc
    let d ← hexDigitToNat? c
    some (a * 16 + d)
  ) (some 0)

/-- Parse a binary string to Nat -/
private def binToNat? (s : String) : Option Nat :=
  s.foldl (fun acc c => do
    let a ← acc
    if c == '0' then some (a * 2)
    else if c == '1' then some (a * 2 + 1)
    else none
  ) (some 0)

/-- Parse an SMT-LIB bitvector value to Lean BitVec -/
def parseBitVec (s : String) (n : Nat) : Option (BitVec n) :=
  if s.startsWith "#x" then
    -- Hexadecimal: #x09
    let hexStr := s.drop 2
    hexToNat? hexStr |>.map (BitVec.ofNat n)
  else if s.startsWith "#b" then
    -- Binary: #b101
    let binStr := s.drop 2
    binToNat? binStr |>.map (BitVec.ofNat n)
  else
    -- Try decimal
    s.toNat? |>.map (BitVec.ofNat n)

/-- Parse an SMT-LIB value string to the corresponding Lean type -/
def Ty.parse (ty : Ty) (s : String) : Option ty.LeanType :=
  match ty with
  | Ty.bool => parseBool s
  | Ty.bitVec n => parseBitVec s n
  | Ty.array _ _ => some ()  -- Arrays can't be easily parsed from SMT output

/-- Expressions indexed by sort, ensuring width-correctness at compile time -/
inductive Expr : Ty → Type where
  -- Variables
  | var     : String → (ty : Ty) → Expr ty

  -- Boolean literals
  | btrue   : Expr Ty.bool
  | bfalse  : Expr Ty.bool

  -- Boolean operations
  | and     : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | or      : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | not     : Expr Ty.bool → Expr Ty.bool
  | imp     : Expr Ty.bool → Expr Ty.bool → Expr Ty.bool
  | ite : Expr Ty.bool → Expr s → Expr s → Expr s

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

  -- Array operations
  | mkArray : (idxWidth : Nat) → (elem : ElemTy) → Expr elem.toTy → Expr (Ty.array idxWidth elem)
  | select  : Expr (Ty.array idxWidth elem) → Expr (Ty.bitVec idxWidth) → Expr elem.toTy
  | store   : Expr (Ty.array idxWidth elem) → Expr (Ty.bitVec idxWidth) → Expr elem.toTy → Expr (Ty.array idxWidth elem)

  -- Distinct constraint (names stored directly to avoid nested inductive issue)
  | distinctBV : (n : Nat) → (names : List String) → Expr Ty.bool

-- Smart constructors

/-- Create a bitvector literal with value `val` and width `n` -/
def bv (val n : Nat) : Expr (Ty.bitVec n) := Expr.bvLit val n

/-- Boolean true -/
def btrue : Expr Ty.bool := Expr.btrue

/-- Boolean false -/
def bfalse : Expr Ty.bool := Expr.bfalse

/-- Create a constant array where all indices map to the same value -/
def constArray (idxWidth : Nat) (elem : ElemTy) (v : Expr elem.toTy) : Expr (Ty.array idxWidth elem) :=
  Expr.mkArray idxWidth elem v

/-- Read from an array at index -/
def selectArr (arr : Expr (Ty.array idxWidth elem)) (i : Expr (Ty.bitVec idxWidth)) : Expr elem.toTy :=
  Expr.select arr i

/-- Write to an array at index, returning new array -/
def storeArr (arr : Expr (Ty.array idxWidth elem)) (i : Expr (Ty.bitVec idxWidth)) (v : Expr elem.toTy) : Expr (Ty.array idxWidth elem) :=
  Expr.store arr i v

/-- Extract variable name from a variable expression -/
def Expr.varName : Expr ty → Option String
  | .var name _ => some name
  | _ => none

/-- Assert all bitvector expressions are pairwise distinct (List version).
    Only works on variable expressions - extracts their names for the distinct constraint. -/
def distinct (es : List (Expr (Ty.bitVec n))) : Expr Ty.bool :=
  let names := es.filterMap Expr.varName
  Expr.distinctBV n names

/-- Assert all bitvector expressions are pairwise distinct (Vector version) -/
def distinctV (es : Vector (Expr (Ty.bitVec n)) m) : Expr Ty.bool :=
  distinct es.toList

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
