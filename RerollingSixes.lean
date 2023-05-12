import Mathlib.Data.Nat.Choose.Multinomial

import RerollingSixes.NatMemo
import RerollingSixes.NatMemoAttr
import RerollingSixes.FastChoose

set_option autoImplicit false

open BigOperators Nat

def v (p : ℚ) (n : ℕ) : ℚ :=
  if hn : n = 0 then 0 else  
  /- all tails -/
  (1-p)^n * v p (n-1) +
  ∑ j : Fin n, 
    /- j < n tails, so n-j heads -/
    Nat.choose n j * p^(n-j) * (1-p)^(j : ℕ) *
    /- Pick best next step -/
    Finset.sup' (Finset.range (n-j)) 
      (by simp)
      (fun i => (1+i) + v p (n-(1+i)))
decreasing_by decreasing_with aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)

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

-- Cannot use attr yet, due to extra parameters
def fast_v (p : ℚ) (n : ℕ)  : ℚ := NatMemo.memo (vf p) n

@[csimp]
lemma v_fast_v : v = fast_v := by
  funext p
  apply NatMemo.memo_spec
  intro n
  rw [v, vf]

#eval v 0.5 50