/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Tensor types for multi-dimensional variable declarations

  Uses Lean 4's standard library `Vector` type (structure wrapping Array with size proof).
-/
namespace CogitoCore.SMT

/-! ## Extended Vector operations

The standard library Vector already provides:
- get, map, mapM, foldl, foldr, foldlM
- zipWith, zip, append, head, tail
- any, all, find?, range, finRange
- replicate, ofFn, flatten, reverse, swap, set, push, pop
- toArray, toList

We only add what's missing for our use cases.
-/

namespace Vector

/-- Monadic tabulate (equivalent to standard ofFn but monadic) -/
def tabulateM [Monad m] (n : Nat) (f : Fin n → m α) : m (Vector α n) :=
  Vector.mapM f (Vector.finRange n)

/-- Build Vector from List with length proof -/
def ofList (xs : List α) : Vector α xs.length :=
  ⟨xs.toArray, by simp⟩

/-- Build Vector from List with explicit length -/
def ofList' (xs : List α) (h : xs.length = n) : Vector α n :=
  h ▸ ofList xs

/-- Map with index (using Fin) -/
def mapWithIndex (f : Fin n → α → β) (v : Vector α n) : Vector β n :=
  Vector.ofFn fun i => f i (v.get i)

/-- FlatMap to List (since result length unknown) -/
def flatMap (f : α → List β) (v : Vector α n) : List β :=
  v.toList.flatMap f

/-- Filter with mapping (returns List since length unknown) -/
def filterMap (f : α → Option β) (v : Vector α n) : List β :=
  v.toList.filterMap f

/-- Filter (returns List since length unknown) -/
def filter (p : α → Bool) (v : Vector α n) : List α :=
  v.toList.filter p

/-- Enumerate with indices (Nat-based) -/
def enum (v : Vector α n) : Vector (Nat × α) n :=
  v.mapIdx fun i x => (i, x)

/-- Find index of first element satisfying predicate -/
def findIdx? (p : α → Bool) (v : Vector α n) : Option Nat :=
  v.toList.findIdx? p

/-- Check membership -/
def elem [BEq α] (x : α) (v : Vector α n) : Bool :=
  v.any (x == ·)

/-- Check if vector contains element -/
def contains [BEq α] (x : α) (v : Vector α n) : Bool := elem x v

/-- Sum of elements -/
def sum [Add α] [OfNat α 0] (v : Vector α n) : α :=
  v.foldl (· + ·) 0

/-- Product of elements -/
def prod [Mul α] [OfNat α 1] (v : Vector α n) : α :=
  v.foldl (· * ·) 1

/-- Get element with Nat index (auto-proof using grind) -/
def getN (v : Vector α n) (i : Nat) (h : i < n := by grind) : α :=
  v.get ⟨i, h⟩

/-- Unzip a vector of pairs -/
def unzip (v : Vector (α × β) n) : Vector α n × Vector β n :=
  (v.map Prod.fst, v.map Prod.snd)

/-- Zip three vectors with function -/
def zipWith3 (f : α → β → γ → δ) (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n) : Vector δ n :=
  Vector.ofFn fun i => f (v1.get i) (v2.get i) (v3.get i)

end Vector

/-! ## Tensor Aliases -/

/-- Type-level tensor: Tensor [2,3,4] α ≡ Vector (Vector (Vector α 4) 3) 2 -/
def Tensor (dims : List Nat) (α : Type _) : Type _ :=
  dims.foldr (fun n acc => Vector acc n) α

/-- 1D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor1D (n : Nat) (α : Type _) := Vector α n

/-- 2D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor2D (m n : Nat) (α : Type _) := Vector (Vector α n) m

/-- 3D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor3D (l m n : Nat) (α : Type _) := Vector (Vector (Vector α n) m) l

namespace Tensor2D

/-- Get row from 2D tensor -/
def getRow (t : Tensor2D m n α) (r : Fin m) : Vector α n := Vector.get t r

/-- Get row with Nat index (auto-proof) -/
def getRowN (t : Tensor2D m n α) (r : Nat) (hr : r < m := by grind) : Vector α n := Vector.get t ⟨r, hr⟩

/-- Get column from 2D tensor -/
def getCol (t : Tensor2D m n α) (c : Fin n) : Vector α m := Vector.map (Vector.get · c) t

/-- Get element at (row, col) -/
def get (t : Tensor2D m n α) (r : Fin m) (c : Fin n) : α := Vector.get (Vector.get t r) c

/-- Get element with Nat indices (auto-proof) -/
def getN (t : Tensor2D m n α) (r : Nat) (c : Nat) (hr : r < m := by grind) (hc : c < n := by grind) : α :=
  Vector.get (Vector.get t ⟨r, hr⟩) ⟨c, hc⟩

/-- Map over all elements -/
def map (f : α → β) (t : Tensor2D m n α) : Tensor2D m n β :=
  Vector.map (Vector.map f) t

/-- Map with row and column indices -/
def mapWithIndex (f : Fin m → Fin n → α → β) (t : Tensor2D m n α) : Tensor2D m n β :=
  Vector.ofFn fun r => Vector.ofFn fun c => f r c (Vector.get (Vector.get t r) c)

/-- Fold over all elements (row-major order) -/
def foldl (f : β → α → β) (init : β) (t : Tensor2D m n α) : β :=
  Vector.foldl (fun acc row => Vector.foldl f acc row) init t

/-- Fold over rows -/
def foldRows (f : β → Vector α n → β) (init : β) (t : Tensor2D m n α) : β :=
  Vector.foldl f init t

/-- Fold over all elements (row-major order) with indices -/
def foldlWithIndex (f : β → Fin m → Fin n → α → β) (init : β) (t : Tensor2D m n α) : β :=
  Vector.foldl (fun acc r =>
    Vector.foldl (fun acc' c =>
      f acc' r c (Vector.get (Vector.get t r) c)) acc (Vector.finRange n))
    init (Vector.finRange m)

/-- Create 2D tensor from function -/
def tabulate (m n : Nat) (f : Fin m → Fin n → α) : Tensor2D m n α :=
  Vector.ofFn fun r => Vector.ofFn fun c => f r c

/-- Create 2D tensor with same value -/
def replicate (m n : Nat) (x : α) : Tensor2D m n α :=
  Vector.replicate m (Vector.replicate n x)

/-- Transpose a 2D tensor -/
def transpose (t : Tensor2D m n α) : Tensor2D n m α :=
  tabulate n m fun c r => Vector.get (Vector.get t r) c

/-- Flatten 2D tensor to 1D -/
def flatten (t : Tensor2D m n α) : List α :=
  Vector.foldl (fun acc row => acc ++ Vector.toList row) [] t

/-- Check if any element satisfies predicate -/
def any (p : α → Bool) (t : Tensor2D m n α) : Bool :=
  Vector.any t (fun row => Vector.any row p)

/-- Check if all elements satisfy predicate -/
def all (p : α → Bool) (t : Tensor2D m n α) : Bool :=
  Vector.all t (fun row => Vector.all row p)

end Tensor2D

namespace Tensor3D

/-- Get element at (i, j, k) -/
def get (t : Tensor3D l m n α) (i : Fin l) (j : Fin m) (k : Fin n) : α :=
  Vector.get (Vector.get (Vector.get t i) j) k

/-- Get element with Nat indices (auto-proof) -/
def getN (t : Tensor3D l m n α) (i : Nat) (j : Nat) (k : Nat)
    (hi : i < l := by grind) (hj : j < m := by grind) (hk : k < n := by grind) : α :=
  Vector.get (Vector.get (Vector.get t ⟨i, hi⟩) ⟨j, hj⟩) ⟨k, hk⟩

end Tensor3D

/-! ## Indexing Notation -/

/-- Notation for Vector indexing: v[i] -/
scoped macro:max v:term noWs "[" i:term "]" : term => `(Vector.getN $v $i)

/-- Notation for Tensor2D indexing: t[i, j] -/
scoped macro:max t:term noWs "[" i:term ", " j:term "]" : term => `(Tensor2D.getN $t $i $j)

/-- Notation for Tensor3D indexing: t[i, j, k] -/
scoped macro:max t:term noWs "[" i:term ", " j:term ", " k:term "]" : term => `(Tensor3D.getN $t $i $j $k)

/-! ## Legacy Vect alias for compatibility -/

/-- Alias for Vector (for code compatibility) -/
abbrev Vect := Vector

end CogitoCore.SMT
