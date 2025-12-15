/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Tensor and Vect types for multi-dimensional variable declarations
-/
namespace CogitoCore.SMT

/-- Length-indexed vector -/
inductive Vect (α : Type _) : Nat → Type _ where
  | nil  : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

namespace Vect

/-! ## Basic Operations -/

/-- Get element at index -/
def get : Vect α n → Fin n → α
  | cons x _, ⟨0, _⟩ => x
  | cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Get head element -/
def head : Vect α (n + 1) → α
  | cons x _ => x

/-- Get tail -/
def tail : Vect α (n + 1) → Vect α n
  | cons _ xs => xs

/-! ## Construction -/

/-- Create vector with n copies of x -/
def replicate : (n : Nat) → α → Vect α n
  | 0, _ => nil
  | n + 1, x => cons x (replicate n x)

/-- Create vector from function on indices -/
def tabulate : (n : Nat) → (Fin n → α) → Vect α n
  | 0, _ => nil
  | n + 1, f => cons (f ⟨0, Nat.zero_lt_succ n⟩)
                     (tabulate n (fun ⟨i, h⟩ => f ⟨i + 1, Nat.succ_lt_succ h⟩))

/-- Monadic tabulate -/
def tabulateM [Monad m] (n : Nat) (f : Fin n → m α) : m (Vect α n) :=
  match n with
  | 0 => pure nil
  | n + 1 => do
    let x ← f ⟨0, Nat.zero_lt_succ n⟩
    let xs ← tabulateM n (fun ⟨i, h⟩ => f ⟨i + 1, Nat.succ_lt_succ h⟩)
    pure (cons x xs)

/-- Build Vect from List with length proof -/
def ofList : (xs : List α) → Vect α xs.length
  | [] => nil
  | x :: xs => cons x (ofList xs)

/-- Build Vect from List with explicit length -/
def ofList' (xs : List α) (h : xs.length = n) : Vect α n :=
  h ▸ ofList xs

/-- Generate range [0, 1, ..., n-1] as Fin n -/
def finRange (n : Nat) : Vect (Fin n) n :=
  tabulate n id

/-! ## Conversion -/

/-- Convert to List -/
def toList : Vect α n → List α
  | nil => []
  | cons x xs => x :: toList xs

/-- Convert to Array -/
def toArray : Vect α n → Array α
  | nil => #[]
  | cons x xs => #[x] ++ toArray xs

/-! ## Transformations -/

/-- Map a function over elements -/
def map (f : α → β) : Vect α n → Vect β n
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

/-- Map with index -/
def mapWithIndex (f : Nat → α → β) : Vect α n → Vect β n :=
  go 0
where
  go {m : Nat} (i : Nat) : Vect α m → Vect β m
    | nil => nil
    | cons x xs => cons (f i x) (go (i + 1) xs)

/-! ## Folding -/

/-- Left fold -/
def foldl (f : β → α → β) (init : β) : Vect α n → β
  | nil => init
  | cons x xs => foldl f (f init x) xs

/-- Right fold -/
def foldr (f : α → β → β) (init : β) : Vect α n → β
  | nil => init
  | cons x xs => f x (foldr f init xs)

/-! ## Filtering & Selection (return List since length unknown) -/

/-- Filter elements -/
def filter (p : α → Bool) : Vect α n → List α
  | nil => []
  | cons x xs => if p x then x :: filter p xs else filter p xs

/-- Filter with mapping -/
def filterMap (f : α → Option β) : Vect α n → List β
  | nil => []
  | cons x xs => match f x with
    | some y => y :: filterMap f xs
    | none => filterMap f xs

/-- FlatMap to List -/
def flatMap (f : α → List β) : Vect α n → List β
  | nil => []
  | cons x xs => f x ++ flatMap f xs

/-! ## Combining -/

/-- Append two vectors -/
def append {α : Type _} {m n : Nat} (xs : Vect α m) (ys : Vect α n) : Vect α (m + n) :=
  match m, xs with
  | 0, nil => by simp; exact ys
  | m' + 1, cons x xs' => by
      have h : m' + 1 + n = (m' + n) + 1 := by omega
      exact h ▸ cons x (append xs' ys)

/-- Zip two vectors -/
def zip : Vect α n → Vect β n → Vect (α × β) n
  | nil, nil => nil
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)

/-- Zip with function -/
def zipWith (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | nil, nil => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)

/-- Zip three vectors -/
def zipWith3 (f : α → β → γ → δ) : Vect α n → Vect β n → Vect γ n → Vect δ n
  | nil, nil, nil => nil
  | cons x xs, cons y ys, cons z zs => cons (f x y z) (zipWith3 f xs ys zs)

/-- Unzip -/
def unzip : Vect (α × β) n → Vect α n × Vect β n
  | nil => (nil, nil)
  | cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (cons x xs, cons y ys)

/-- Enumerate with indices (Nat-based) -/
def enum : Vect α n → Vect (Nat × α) n :=
  mapWithIndex fun i x => (i, x)

/-- Zip with range for List-compatible enumeration -/
def zipWithIndex : Vect α n → List (α × Nat) :=
  go 0
where
  go {m : Nat} (i : Nat) : Vect α m → List (α × Nat)
    | nil => []
    | cons x xs => (x, i) :: go (i + 1) xs

/-! ## Predicates -/

/-- Check if any element satisfies predicate -/
def any (p : α → Bool) : Vect α n → Bool
  | nil => false
  | cons x xs => p x || any p xs

/-- Check if all elements satisfy predicate -/
def all (p : α → Bool) : Vect α n → Bool
  | nil => true
  | cons x xs => p x && all p xs

/-- Find first element satisfying predicate -/
def find? (p : α → Bool) : Vect α n → Option α
  | nil => none
  | cons x xs => if p x then some x else find? p xs

/-- Find index of first element satisfying predicate -/
def findIdx? (p : α → Bool) : Vect α n → Option Nat :=
  go 0
where
  go {m : Nat} (i : Nat) : Vect α m → Option Nat
    | nil => none
    | cons x xs => if p x then some i else go (i + 1) xs

/-- Check membership -/
def elem [BEq α] (x : α) : Vect α n → Bool
  | nil => false
  | cons y ys => x == y || elem x ys

/-- Check if vector contains element -/
def contains [BEq α] (x : α) (v : Vect α n) : Bool := elem x v

/-! ## Numeric Operations -/

/-- Sum of elements -/
def sum [Add α] [OfNat α 0] : Vect α n → α :=
  foldl (· + ·) 0

/-- Product of elements -/
def prod [Mul α] [OfNat α 1] : Vect α n → α :=
  foldl (· * ·) 1

end Vect

/-! ## Tensor -/

/-- Type-level tensor: Tensor [2,3,4] α ≡ Vect (Vect (Vect α 4) 3) 2 -/
def Tensor (dims : List Nat) (α : Type _) : Type _ :=
  dims.foldr (fun n acc => Vect acc n) α

/-- 1D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor1D (n : Nat) (α : Type _) := Vect α n

/-- 2D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor2D (m n : Nat) (α : Type _) := Vect (Vect α n) m

/-- 3D Tensor (reducible abbreviation for better type inference) -/
abbrev Tensor3D (l m n : Nat) (α : Type _) := Vect (Vect (Vect α n) m) l

namespace Tensor2D

/-- Get row from 2D tensor -/
def getRow (t : Tensor2D m n α) (r : Fin m) : Vect α n := Vect.get t r

/-- Get row with Nat index (auto-proof) -/
def getRowN (t : Tensor2D m n α) (r : Nat) (hr : r < m := by grind) : Vect α n := Vect.get t ⟨r, hr⟩

/-- Get column from 2D tensor -/
def getCol (t : Tensor2D m n α) (c : Fin n) : Vect α m := Vect.map (Vect.get · c) t

/-- Get element at (row, col) -/
def get (t : Tensor2D m n α) (r : Fin m) (c : Fin n) : α := Vect.get (Vect.get t r) c

/-- Get element with Nat indices (auto-proof) -/
def getN (t : Tensor2D m n α) (r : Nat) (c : Nat) (hr : r < m := by grind) (hc : c < n := by grind) : α :=
  Vect.get (Vect.get t ⟨r, hr⟩) ⟨c, hc⟩

/-- Map over all elements -/
def map (f : α → β) (t : Tensor2D m n α) : Tensor2D m n β :=
  Vect.map (Vect.map f) t

/-- Map with row and column indices -/
def mapWithIndex (f : Fin m → Fin n → α → β) (t : Tensor2D m n α) : Tensor2D m n β :=
  Vect.tabulate m fun r =>
    Vect.tabulate n fun c =>
      f r c (Vect.get (Vect.get t r) c)

/-- Fold over all elements (row-major order) -/
def foldl (f : β → α → β) (init : β) (t : Tensor2D m n α) : β :=
  Vect.foldl (fun acc row => Vect.foldl f acc row) init t

/-- Fold over rows -/
def foldRows (f : β → Vect α n → β) (init : β) (t : Tensor2D m n α) : β :=
  Vect.foldl f init t

/-- Fold over all elements (row-major order) with indices -/
def foldlWithIndex (f : β → Fin m → Fin n → α → β) (init : β) (t : Tensor2D m n α) : β :=
  Vect.foldl (fun acc r =>
    Vect.foldl (fun acc' c =>
      f acc' r c (Vect.get (Vect.get t r) c)) acc (Vect.finRange n))
    init (Vect.finRange m)

/-- Create 2D tensor from function -/
def tabulate (m n : Nat) (f : Fin m → Fin n → α) : Tensor2D m n α :=
  Vect.tabulate m fun r => Vect.tabulate n fun c => f r c

/-- Create 2D tensor with same value -/
def replicate (m n : Nat) (x : α) : Tensor2D m n α :=
  Vect.replicate m (Vect.replicate n x)

/-- Transpose a 2D tensor -/
def transpose (t : Tensor2D m n α) : Tensor2D n m α :=
  tabulate n m fun c r => Vect.get (Vect.get t r) c

/-- Flatten 2D tensor to 1D -/
def flatten (t : Tensor2D m n α) : List α :=
  Vect.foldl (fun acc row => acc ++ Vect.toList row) [] t

/-- Check if any element satisfies predicate -/
def any (p : α → Bool) (t : Tensor2D m n α) : Bool :=
  Vect.any (Vect.any p) t

/-- Check if all elements satisfy predicate -/
def all (p : α → Bool) (t : Tensor2D m n α) : Bool :=
  Vect.all (Vect.all p) t

end Tensor2D

namespace Tensor3D

/-- Get element at (i, j, k) -/
def get (t : Tensor3D l m n α) (i : Fin l) (j : Fin m) (k : Fin n) : α :=
  Vect.get (Vect.get (Vect.get t i) j) k

/-- Get element with Nat indices (auto-proof) -/
def getN (t : Tensor3D l m n α) (i : Nat) (j : Nat) (k : Nat)
    (hi : i < l := by grind) (hj : j < m := by grind) (hk : k < n := by grind) : α :=
  Vect.get (Vect.get (Vect.get t ⟨i, hi⟩) ⟨j, hj⟩) ⟨k, hk⟩

end Tensor3D

/-- Get element from Vect with auto-proof using grind -/
def Vect.getN (v : Vect α n) (i : Nat) (h : i < n := by grind) : α :=
  v.get ⟨i, h⟩

/-- Notation for Vect indexing: v[i] -/
scoped macro:max v:term noWs "[" i:term "]" : term => `(Vect.getN $v $i)

/-- Notation for Tensor2D indexing: t[i, j] -/
scoped macro:max t:term noWs "[" i:term ", " j:term "]" : term => `(Tensor2D.getN $t $i $j)

/-- Notation for Tensor3D indexing: t[i, j, k] -/
scoped macro:max t:term noWs "[" i:term ", " j:term ", " k:term "]" : term => `(Tensor3D.getN $t $i $j $k)

/-! ## Instances -/

instance [Repr α] : Repr (Vect α n) where
  reprPrec v _ := repr v.toList

instance [ToString α] : ToString (Vect α n) where
  toString v := toString v.toList

instance [BEq α] : BEq (Vect α n) where
  beq v1 v2 := v1.toList == v2.toList

instance : Functor (Vect · n) where
  map := Vect.map

end CogitoCore.SMT
