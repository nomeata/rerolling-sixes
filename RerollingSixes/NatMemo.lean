-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std

set_option autoImplicit false

/-- Arrays of a given size, H'T Kyle Miller -/
def SArray (α : Type _) (n : Nat) := {a : Array α // a.size = n}

namespace SArray

protected def push {α n} (a : SArray α n) (x : α) : SArray α (n + 1) :=
  ⟨a.1.push x, by rw [Array.size_push, a.2]⟩

protected def get {α n} (a : SArray α n) (i : Fin n) : α :=
  a.1.get ⟨i, a.2.symm ▸ i.2⟩

protected theorem get_push {α n} (a : SArray α n) (x : α) (i : Nat) (hi : i < n + 1) :
    (a.push x).get (⟨i, hi⟩) = if h : i < n then a.get ⟨i, h⟩ else x := by
  simp only [SArray.get, SArray.push, Array.get_eq_getElem, Array.get_push, a.2]

protected def empty {α}: SArray α 0 := ⟨Array.empty, rfl⟩

end SArray

namespace NatMemo

protected def memoVec {α} (f : (n : Nat) → (∀ i, i < n → α) → α ) :
  (n : Nat) → SArray α n
  | 0 => .empty
  | n + 1 =>
    let v := NatMemo.memoVec f n
    v.push (f n (fun i ih => v.get ⟨i, ih⟩))

def memo {α} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  (NatMemo.memoVec f (n + 1)).get ⟨n, Nat.le_refl _⟩

def fix {α} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  f n (fun i _ => fix f i)

theorem memoVec_spec {α}
  (g : Nat → α)
  (f : (n : Nat) → (∀ i, i < n → α) → α)
  (h : ∀ n, f n (fun i _ => g i) = g n)
  n : ∀ i hi, (NatMemo.memoVec f n).get ⟨i, hi⟩ = g i := by
    induction n
    case zero => 
      intro i hi
      cases hi
    case succ n ih =>
      intro i hi
      rw [NatMemo.memoVec]
      apply Eq.trans (SArray.get_push _ _ _ _)
      split
      case inl hn =>
        apply ih
      case inr hn =>
        have i_eq_n : i = n := Nat.le_antisymm (Nat.lt_succ.1 hi) (Nat.not_lt.1 hn)
        rcases i_eq_n
        rw [<- h]
        congr with i hi'
        apply ih

theorem memo_spec {α}
  (g : Nat → α)
  (f : (n : Nat) → (∀ i, i < n → α) → α)
  (h : ∀ n, f n (fun i _ => g i) = g n) :
  g = memo f := funext (fun _ => (memoVec_spec g f h _ _ _).symm)

end NatMemo

namespace NatMemoDemo

/-
A small demo. Here a slow implemntation of a recursive function.
(The if inside is just to please the recursion checker, the condition is always true).
-/
def slow (n : Nat) : Nat :=
  1 + List.foldl (fun a i => a + (if _ : i<n then slow i else 0)) 0 (List.range n)

-- Kinda slow:
-- #eval (slow 20)

/-
Define the fast version using the fixed-point version
-/
def fast (n : Nat) : Nat :=
  NatMemo.memo (fun n r =>
    1 + List.foldl (fun a i => a + (if h : i<n then r i h else 0)) 0 (List.range n)
  ) n

/-
And prove them to be qual. The csimp attribute makes Lean use the fast version
when evaluating.
-/

@[csimp]
theorem slow_is_fast: slow = fast := by
  apply NatMemo.memo_spec
  intro n
  rw [slow]
  
-- Now faster:
-- #eval (slow 20)

end NatMemoDemo