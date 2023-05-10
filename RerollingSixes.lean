import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Real.Basic

def fast_choose n k := Nat.descFactorial n k / Nat.factorial k
@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))

set_option autoImplicit false
open BigOperators Nat

def v (n : ℕ) (p : ℚ) : ℚ :=
  if hn : n = 0 then 0 else  
  /- all tails -/
  (1-p)^n * v (n-1) p +
  ∑ j : Fin n, 
    /- j < n tails, so n-j heads -/
    Nat.choose n j * p^(n-j) * (1-p)^(j : ℕ) *
    /- Pick best next step -/
    Finset.sup' (Finset.range (n-j)) 
      (by simp)
      (fun i => (1+i) + v (n-(1+i)) p)
decreasing_by decreasing_with aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)

/-
#eval v 0 0.5
#eval v 1 0.5
#eval v 2 0.5
#eval v 3 0.5
#eval v 4 0.5
#eval v 5 0.5
#eval v 6 0.5 /- Now it is getting slow -/
-/

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

def memo {α} (f : (n : Nat) → (Fin n → α) → α) (n : Nat) : α :=
  let f' (n : Nat) (v : SArray α n) : α := f n v.get
  (memoVec f' (n + 1)).get n

def fix {α} (f : (n : Nat) → (Fin n → α) → α) (n : Nat) : α :=
  f n (fun ⟨i, _⟩ => fix f i)

lemma memoVec_spec {α} (f : (n : Nat) → (Fin n → α) → α) n : 
  let f' (n : Nat) (v : SArray α n) : α := f n v.get
  ∀ i : Fin n, (memoVec f' n).get i = fix f i := by
    intro f'
    induction n
    case zero => 
      intro ⟨i, hi⟩
      cases hi
    case succ n ih =>
      intro i
      rw [memoVec]
      -- TODO: How to unfold local have := more conveniently
      change SArray.get (SArray.push (memoVec f' n) (f' n (memoVec f' n))) i = fix f ↑i
      rw [SArray.get_push]
      split
      case inl hi =>
        apply ih
      case inr hi =>
        have h : i = Fin.last n := by
          sorry
        rcases h
        rw [fix]
        change (f _ _ = f _ _) 
        simp
        congr with i
        apply ih

        

#exit



def vf (p : ℚ) (n : ℕ) (r : Fin n -> ℚ) : ℚ :=
  if hn : n = 0 then 0 else  
  /- all tails -/
  (1-p)^n * r ⟨n-1, by aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)⟩ +
  ∑ j : Fin n, 
    /- j < n tails, so n-j heads -/
    n.choose j * p^(n-j) * (1-p)^(j : ℕ) *
    /- Pick best next step -/
    Finset.sup' (Finset.range (n-j)) 
      (by simp)
      (fun i => (1+i) + r ⟨n-(1+i), by aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)⟩)

def fast_v (n : ℕ) (p : ℚ) : ℚ :=
  memo (vf p) n