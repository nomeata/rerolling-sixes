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

-- #eval v 0.5 50

-- set_option trace.Tactic.positivity true

lemma v_nonneg {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n : 0 ≤ v p n := by
  have : 0 ≤ (1 - p) := by linarith
  induction' n using Nat.case_strong_induction_on
  case hz =>
    rewrite [v]
    simp
  case hi n IH =>
    have := IH n (by linarith)
    rewrite [v]
    simp
    apply add_nonneg
    . positivity
    . apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg; try positivity
      have hzero : 0 ∈ Finset.range (succ n - ↑i) := by simp
      apply Finset.le_sup'_of_le _ hzero
      positivity


lemma binom_part (p : ℚ) (n : ℕ) :
  1 = (1 - p) ^ (n + 1) +
      ∑ j : Fin (n + 1),
      (choose (n + 1) j) * p ^ (n + 1 - ↑j) * (1 - p) ^ (j : ℕ) := by
  calc
    1 = ((1-p) + p)^(n+1) := by simp
    _ = Finset.sum (Finset.range ((n + 1) + 1)) fun m =>
      (1-p) ^ m * p ^ ((n + 1) - m) * ↑(Nat.choose (n+1) m) := Commute.add_pow (by simp) _ 
    _ = (Finset.sum (Finset.range ((n + 1))) fun m =>
        (1-p) ^ m * p ^ ((n + 1) - m) * ↑(Nat.choose (n+1) m)
      ) + ((1-p) ^ (n+1) * p ^ ((n + 1) - (n+1)) * ↑(Nat.choose (n+1) (n+1)))
      := Finset.sum_range_succ _ _
    _ = (1-p) ^ (n+1) + Finset.sum (Finset.range ((n + 1))) fun m =>
      (1-p) ^ m * p ^ ((n + 1) - m) * ↑(Nat.choose (n+1) m) := by rw [add_comm]; simp
    _ = _ := by
      congr 1
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp at hi
      split
      case e_a.inl => linarith
      case e_a.inr h => contradiction

lemma v_mono_n {p} (hp : 0 ≤ p) (hp2 : p ≤ 1): Monotone (v p) := by
  have : 0 ≤ (1 - p) := by linarith
  apply monotone_nat_of_le_succ
  intro n
  conv => right ; rewrite [v] ; simp
  conv => left; rewrite [(by simp : v p n = 1 * v p n), binom_part p n]
  simp [ add_mul, Finset.sum_mul ]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul
  . simp
  . have hzero : 0 ∈ Finset.range (succ n - ↑i) := by simp
    apply Finset.le_sup'_of_le _ hzero
    simp
  . apply v_nonneg hp hp2
  . positivity
  

