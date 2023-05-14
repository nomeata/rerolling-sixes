import Mathlib.Data.Nat.Choose.Multinomial

import RerollingSixes.NatMemo
import RerollingSixes.NatMemoAttr
import RerollingSixes.FastChoose

set_option autoImplicit false

open BigOperators Nat

/- Binomial Expectation operator -/
def En (p : ℚ) (n : ℕ) (val : ∀ i, 0 < n -> i ≤ n -> ℚ) : ℚ :=
  if hnz : n = 0 then 0
  else ∑ j : Fin (n+1), 
    p^(j : ℕ) * (1-p)^(n - j) * n.choose j *
    val j (zero_lt_of_ne_zero hnz) (le_of_lt_succ j.2)

def v (p : ℚ) (n : ℕ) : ℚ :=
  En p n (fun i _ hi =>
    if hz : i = 0
    /- No heads -/
    then v p (n-1)
    /- i heads -/
    else 
      /- Fix 1 to i coins -/
      Finset.sup' (Finset.range i) (by simp [hz]) (fun j =>
        (j+1) + v p (n-(j+1))
      )
  )
decreasing_by decreasing_with aesop (add safe Nat.sub_lt, safe Nat.zero_lt_of_ne_zero)

def vf (p : ℚ) (n : ℕ) (r : ∀ i, i < n -> ℚ) : ℚ :=
  En p n (fun i hnz hi =>
    if hz : i = 0
    /- No heads -/
    then r (n-1) (Nat.sub_lt hnz zero_lt_one)
    /- i heads -/
    else 
      /- Fix 1 to i coins -/
      Finset.sup' (Finset.range i) 
      (by simp [hz])
      (fun j => (j+1) + r (n-(j+1)) (Nat.sub_lt hnz (Nat.zero_lt_succ _)))
  )  

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

lemma En_nonneg {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) (n)
  (val : ∀ i, 0 < n -> i ≤ n -> ℚ)
  (val_nonneg : ∀ i (hnz : 0 < n) (hin : i ≤ n), 0 ≤ val i hnz hin) :
  0 ≤ En p n val := by
  have : 0 ≤ (1 - p) := by linarith -- to help the positivity tactic
  rw [En] 
  split
  case inl hnz => exact (le_refl _)
  case inr hnz =>
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg; try positivity
    apply val_nonneg

lemma v_nonneg {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n : 0 ≤ v p n := by
  induction' n using Nat.case_strong_induction_on
  case hz =>
    rewrite [v]
    apply En_nonneg hp hp2
    intro i hnz
    cases hnz
  case hi n IH =>
    have IHn := IH n (by linarith)
    rewrite [v]
    apply En_nonneg hp hp2
    intro i _hnz _hin
    split
    case inl => exact IHn
    case inr hiz =>
      have hzero : 0 ∈ Finset.range i := by simp; apply zero_lt_of_ne_zero hiz
      apply Finset.le_sup'_of_le _ hzero
      positivity

/--
Show that En is normalized
-/
lemma En_const (p n) (hnz : 0 < n) (q : ℚ) :
  En p n (fun _ _ _ => q) = q := by
  rw [En]
  split
  case inl => aesop
  case inr =>
    rw [<- Finset.sum_mul]
    rw [ mul_left_eq_self₀ ]
    left
    symm
    calc
    1 = (p + (1-p))^n := by simp
    _ = Finset.sum (Finset.range (n + 1)) fun m =>
      p ^ m * (1-p) ^ (n - m) * ↑(Nat.choose n m) := Commute.add_pow (by simp) _ 
    _ = _ :=  by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp at hi
      split
      case inl => rfl
      case inr h => contradiction

lemma En_mono {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) (n)
  (val1 : ∀ i, 0 < n -> i ≤ n -> ℚ)
  (val2 : ∀ i, 0 < n -> i ≤ n -> ℚ)
  (val_nonneg : ∀ i (hnz : 0 < n) (hin : i ≤ n), val1 i hnz hin <= val2 i hnz hin) :
  En p n val1 ≤ En p n val2 := by
  have : 0 ≤ (1 - p) := by linarith
  unfold En
  split
  case inl => rfl
  case inr =>
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left
    apply val_nonneg
    positivity

lemma v_mono_n {p} (hp : 0 ≤ p) (hp2 : p ≤ 1): Monotone (v p) := by
  have : 0 ≤ (1 - p) := by linarith
  apply monotone_nat_of_le_succ
  intro n
  conv => right ; rewrite [v] ; simp
  conv => left; rw [<- En_const p (n+1) (by simp) (v p n)]
  apply En_mono hp hp2
  intro i _hnz _hin
  split
  case inl => simp
  case inr hiz =>
    have hzero : 0 ∈ Finset.range i := by simp; apply zero_lt_of_ne_zero hiz
    apply Finset.le_sup'_of_le _ hzero
    simp
