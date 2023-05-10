import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Real.Basic

import RerollingSixes.NatMemo

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


def vf (p : ℚ) (n : ℕ) (r : ∀ i, i < n -> ℚ) : ℚ :=
  if hn : n = 0 then 0 else  
  /- all tails -/
  (1-p)^n * r (n-1) (by aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)) +
  ∑ j : Fin n, 
    /- j < n tails, so n-j heads -/
    n.choose j * p^(n-j) * (1-p)^(j : ℕ) *
    /- Pick best next step -/
    Finset.sup' (Finset.range (n-j)) (by simp) (fun i =>
      (1+i) + r (n-(1+i)) (by aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)))

def fast_v (n : ℕ) (p : ℚ) : ℚ :=
  memo (vf p) n

lemma v_fix_vf n p : v n p = fix (vf p) n := by
  rw [v, fix, vf]
  congr; apply funext; intro hn
  congr
  . apply v_fix_vf
  . apply funext; intro x
    congr; apply funext; intro i
    congr
    have _ : n-(1+i) < n := by
      aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)
    apply v_fix_vf

@[csimp]
lemma v_fast_v : v = fast_v := by
  apply funext; intro n
  apply funext; intro p
  rw [fast_v, memo_spec, v_fix_vf]

#eval v 50 0.5