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

def get : Vect α n → Fin n → α
  | cons x _, ⟨0, _⟩ => x
  | cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

def map (f : α → β) : Vect α n → Vect β n
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

def toList : Vect α n → List α
  | nil => []
  | cons x xs => x :: toList xs

def replicate : (n : Nat) → α → Vect α n
  | 0, _ => nil
  | n + 1, x => cons x (replicate n x)

def tabulate : (n : Nat) → (Fin n → α) → Vect α n
  | 0, _ => nil
  | n + 1, f => cons (f ⟨0, Nat.zero_lt_succ n⟩)
                     (tabulate n (fun ⟨i, h⟩ => f ⟨i + 1, Nat.succ_lt_succ h⟩))

/-- Monadic tabulate for Vect -/
def tabulateM [Monad m] (n : Nat) (f : Fin n → m α) : m (Vect α n) :=
  match n with
  | 0 => pure Vect.nil
  | n + 1 => do
    let x ← f ⟨0, Nat.zero_lt_succ n⟩
    let xs ← Vect.tabulateM n (fun ⟨i, h⟩ => f ⟨i + 1, Nat.succ_lt_succ h⟩)
    pure (Vect.cons x xs)

end Vect

/-- Type-level tensor: Tensor [2,3,4] α ≡ Vect (Vect (Vect α 4) 3) 2 -/
abbrev Tensor (dims : List Nat) (α : Type _) : Type _ :=
  dims.foldr (fun n acc => Vect acc n) α

/-- Get element from Vect with auto-proof using grind -/
def Vect.getN (v : Vect α n) (i : Nat) (h : i < n := by grind) : α :=
  v.get ⟨i, h⟩

/-- Notation for Vect indexing: v[i] -/
scoped macro:max v:term noWs "[" i:term "]" : term => `(Vect.getN $v $i)

end CogitoCore.SMT
