import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

def fast_choose n k := Nat.descFactorial n k / Nat.factorial k
@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))

/-- Arrays of a given size, H'T Kyle Miller -/
def SArray (α : Type _) (n : Nat) := {a : Array α // a.size = n}

namespace SArray

protected def push {α n} (a : SArray α n) (x : α) : SArray α (n + 1) :=
  ⟨a.1.push x, by rw [Array.size_push, a.2]⟩

protected def get {α n} (a : SArray α n) (i : Fin n) : α := a.1.get ⟨i, a.2.symm ▸ i.2⟩

theorem get_push {α n} (a : SArray α n) (x : α) (i : Nat) (hi : i < n + 1) :
    (a.push x).get (⟨i, hi⟩) = (if h : i < n then a.get ⟨i, h⟩ else x) := by
  simp [SArray.get, SArray.push, Array.get_push, a.2]

protected def empty {α}: SArray α 0 := ⟨Array.empty, rfl⟩

end SArray

def memoVec {α} (f : (n : Nat) → SArray α n → α) : (n : Nat) → SArray α n
  | 0 => .empty
  | n + 1 =>
    let v := memoVec f n
    v.push (f n v)

def memo {α} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  let f' (n : Nat) (v : SArray α n) : α := f n (fun i ih => v.get ⟨i, ih⟩)
  (memoVec f' (n + 1)).get ⟨n, by simp⟩

def fix {α} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  f n (fun i _ => fix f i)

lemma memoVec_spec {α} (f : (n : Nat) → (∀ i, i < n → α) → α) n : 
  let f' (n : Nat) (v : SArray α n) : α := f n (fun i ih => v.get ⟨i, ih⟩)
  ∀ i hi, (memoVec f' n).get ⟨i, hi⟩ = fix f i := by
    intro f'
    induction n
    case zero => 
      intro i hi
      cases hi
    case succ n ih =>
      intro i hi
      rw [memoVec]
      -- TODO: How to unfold a local have := more conveniently
      change SArray.get (SArray.push _ _) _ = _
      rw [SArray.get_push]
      split
      case inl hn =>
        apply ih
      case inr hn =>
        have h : i = n := Nat.eq_of_lt_succ_of_not_lt hi hn
        rcases h
        rw [fix]
        change (f _ _ = f _ _) 
        congr with i hi'
        apply ih

lemma memo_spec {α} (f : (n : Nat) → (∀ i, i < n → α) → α) n : 
  memo f n = fix f n := by rw [memo, memoVec_spec]