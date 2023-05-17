import Mathlib.Data.Nat.Choose.Multinomial

import RerollingSixes.NatMemo
import RerollingSixes.NatMemoAttr
import RerollingSixes.FastChoose

set_option autoImplicit false

open BigOperators Nat

/- Binomial Expectation operator -/
def bc (p : ℚ) (n : ℕ) (i : ℕ) : ℚ :=
  p^(i : ℕ) * (1-p)^(n - i) * n.choose i
    
def En (p : ℚ) (n : ℕ) (val : ∀ i, i ≤ n -> ℚ) : ℚ :=
  ∑ j : Fin (n+1), bc p n j * val j (le_of_lt_succ j.2)

def v (p : ℚ) (n : ℕ) : ℚ :=
  if hnz : n = 0 then 0
  else En p n (fun i hi =>
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
  if hnz : n = 0 then 0
  else En p n (fun i hi =>
    if hz : i = 0
    /- No heads -/
    then r (n-1) (Nat.sub_lt (Nat.zero_lt_of_ne_zero hnz) zero_lt_one)
    /- i heads -/
    else 
      /- Fix 1 to i coins -/
      Finset.sup' (Finset.range i) 
      (by simp [hz])
      (fun j => (j+1) + r (n-(j+1)) (Nat.sub_lt (Nat.zero_lt_of_ne_zero hnz) (Nat.zero_lt_succ _)))
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

/--
Show that En is normalized
-/
lemma En_const (p n) (q : ℚ) :
  En p n (fun _ _ => q) = q := by
  rw [En]
  rw [<- Finset.sum_mul]
  rw [ mul_left_eq_self₀ ]
  left
  symm
  calc
  1 = (p + (1-p))^n := by simp
  _ = Finset.sum (Finset.range (n + 1)) fun m => bc p n m := Commute.add_pow (by simp) _ 
  _ = _ :=  by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    split
    case inl => rfl
    case inr h => contradiction

lemma En_mono {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) (n)
  (val1 : ∀ i, i ≤ n -> ℚ)
  (val2 : ∀ i, i ≤ n -> ℚ)
  (val_nonneg : ∀ i (hin : i ≤ n), val1 i hin <= val2 i hin) :
  En p n val1 ≤ En p n val2 := by
  have : 0 ≤ (1 - p) := by linarith
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left
  apply val_nonneg
  unfold bc
  positivity

lemma En_le {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n val q 
  (hval : ∀ i (hin : i ≤ n), val i hin <= q) :
  En p n val ≤ q := by
  calc
    En p n val ≤ En p n (fun _ _ => q) := En_mono hp hp2 _ _ _ hval
    _ = q  := En_const _ _ _

lemma le_En {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n val q 
  (hval : ∀ i (hin : i ≤ n), q <= val i hin) :
  q ≤ En p n val := by
  calc
    q = En p n (fun _ _ => q) := (En_const _ _ _).symm
    _ ≤ En p n val := En_mono hp hp2 _ _ _ hval
    
lemma En_nonneg {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) (n)
  (val : ∀ i, i ≤ n -> ℚ)
  (val_nonneg : ∀ i (hin : i ≤ n), 0 ≤ val i hin) :
  0 ≤ En p n val := le_En hp hp2 n val 0 val_nonneg 

lemma v_nonneg {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n : 0 ≤ v p n := by
  induction' n using Nat.case_strong_induction_on
  case hz =>
    rewrite [v]
    simp
  case hi n IH =>
    have IHn := IH n (by linarith)
    rewrite [v]
    simp
    apply En_nonneg hp hp2
    intro i _hin
    split
    case inl => exact IHn
    case inr hiz =>
      have hzero : 0 ∈ Finset.range i := by simp; apply zero_lt_of_ne_zero hiz
      apply Finset.le_sup'_of_le _ hzero
      positivity

lemma v_mono_n {p} (hp : 0 ≤ p) (hp2 : p ≤ 1): Monotone (v p) := by
  have : 0 ≤ (1 - p) := by linarith
  apply monotone_nat_of_le_succ
  intro n
  conv => right ; rewrite [v] ; simp
  conv => left; rw [<- En_const p (n+1) (v p n)]
  apply En_mono hp hp2
  intro i _hin
  split
  case inl => simp
  case inr hiz =>
    have hzero : 0 ∈ Finset.range i := by simp; apply zero_lt_of_ne_zero hiz
    apply Finset.le_sup'_of_le _ hzero
    simp

lemma v_le_n {p} (hp : 0 ≤ p) (hp2 : p ≤ 1) n : v p n ≤ n := by
  induction' n using Nat.case_strong_induction_on
  case hz =>
    rewrite [v]
    simp
  case hi n IH =>
    have IHn := IH n (by linarith)
    rewrite [v]
    simp
    apply En_le hp hp2
    intro i _hin
    split
    case inl =>
      apply le_trans IHn
      simp
    case inr hiz =>
      rw [Finset.sup'_le_iff]
      intro j hj
      calc
        j + 1 + v p (n - j) ≤ j + 1 + (n - j : ℕ) := by
          rw [ add_le_add_iff_left ]
          apply IH
          simp
        _ = j + 1 + (n - j) := by
          congr
          apply Nat.cast_sub
          simp at hj
          linarith
        _ = n + 1 := by ring


def iter_le_plus_1
  (f : ℕ → ℚ) n₀ 
  (hf : ∀ n ≥ n₀, f n + 1 ≤ f (n + 1)) :
  ∀ n ≥ n₀, ∀ j, f n + j ≤ f (n + j) := by
  intros n hn j
  induction j
  case zero => simp
  case succ j IH => calc
    f n + (succ j) = (f n + j) + 1 := by simp [add_assoc]
    _ ≤ f (n + j) + 1 := add_le_add_right IH 1
    _ ≤ f (n + j + 1) := by apply hf; linarith

def iter_le_sub_1
  (f : ℕ → ℚ) n₀ 
  (hf : ∀ n ≥ n₀, f n + 1 ≤ f (n + 1)) :
  ∀ n ≥ n₀, ∀ j ≤ n - n₀, j + f (n - j) ≤ f n := by
  intros n hn j hj
  calc
    j + f (n - j) = f (n - j) + j := add_comm _ _
    _ ≤ f (n - j + j) := by
      apply iter_le_plus_1 f n₀ hf _ _ _
      rw [Nat.le_sub_iff_add_le hn] at hj
      apply Nat.le_sub_of_add_le
      linarith
    _ = f n := by
      rw [Nat.sub_add_cancel ]
      apply Nat.le_trans hj
      apply Nat.sub_le

-- (√5 - 1)/2 ≤ p
def phi_le (p : ℚ) := 5 ≤ (2*p + 1)^2

lemma theorem2_1 p (hp1 : 0.5 ≤ p) (hp2 : p < 1) :
  ∀ n ≥ 2, v p n + 1 ≤ v p (n + 1) :=
  sorry

lemma theorem2_2
  p (hp1 : phi_le p) (hp2 : p < 1) :
  ∀ n ≥ 1, v p n + 1 ≤ v p (n + 1) :=
  sorry

def v_simp p n :=
  if n ≤ 2 then v p n
  else 
  v p (n-1) + 1 +
  p^n * (n - 1 - v p (n-1)) +
  n * p^(n-1) * (1-p) * max 0 (n - 2 + p - v p (n-1) ) -
  (1 - p)^n

lemma En_upd p n f i (hi : i ≤ n) (q : ℚ)
  : En p n f = En p n (fun j hj => if j = i then q else f j hj)
              + bc p n i * (f i hi - q) := by
  rw [En, En]
  conv => right; rw [add_comm]
  let i' : Fin (n+1) := ⟨i, by linarith ⟩
  rw [@Finset.sum_eq_add_sum_diff_singleton _ _ _ _ _ i' (by simp)]
  conv => right; rw [@Finset.sum_eq_add_sum_diff_singleton _ _ _ _ _ i' (by simp)]
  conv => right; rw [<- add_assoc]
  congr 1
  . simp
    ring
  . apply Finset.sum_congr rfl
    intro j hj
    congr
    cases' j with j hj2
    simp at hj
    simp [hj]

-- This proof is full of very tediuos and silly
-- calculations about Nat, +, -, < and ≤.
-- I wish there was an easier way
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/tactic.20for.20trivial.20things.20related.20to.20Nat.2C.20.60.3C.60.20and.20.60.E2.89.A4.60/near/358795930
lemma En_eq_various_sums p n f a b c d
  (hn : 3 ≤ n)
  (ha : ∀ i (_ : 0 < i) (hi2 : i < n-1), f i (hi2.le.trans (n.sub_le 1)) = a)
  (hb : b = bc p n 0 * (f 0 (by simp) - a))
  (hc : c = bc p n n * (f n (by simp) - a))
  (hd : d = bc p n (n-1) * (f (n-1) (by simp) - a))
  : En p n f = a + b + c + d := by
  have hnn1 : n ≠ n -1 := by
    cases' n with n; cases hn
    simp
  have h0nn : 0 ≠ n := by
    cases' n with n; cases hn
    simp
  have h0n1 : 0 ≠ n -1 := by
    cases' n with n; cases hn
    have hn : 2 ≤ n := by linarith
    cases' n with n; cases hn
    simp
    linarith
  rw [En_upd p n _ (n-1) (by simp) a]; rw [hd]; congr 1
  rw [En_upd p n _ n (by simp) a]; simp [hnn1 ]; rw [hc]; congr 1
  rw [En_upd p n _ 0 (by simp) a]; simp [h0nn, h0n1 ]; rw [hb]; congr 1
  conv => right; apply (En_const p n _).symm
  congr
  funext j hj
  simp
  intros hj1 hj2 hj3
  apply ha
  . simp [*, zero_lt_of_ne_zero]
  . simp [*]
    apply Nat.lt_of_le_of_ne _ hj3
    apply Nat.le_sub_of_add_le
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne hj hj2

@[simp]
lemma choose_sub_1
  (n : ℕ) (hn : n ≠ 0) : n.choose (n - 1) = n := by
  cases n
  . simp at hn 
  . apply Nat.choose_succ_self_right

lemma v_eq_v_simp p (hp1 : 0.5 ≤ p) (hp2 : p < 1) :
  ∀ n, v p n = v_simp p n := by
  intro n
  rw [v_simp]
  split
  case inl hnle2 => rw [v]
  case inr h2len =>
    rw [v]
    have hnn0 : n ≠ 0 := by linarith
    have h1n : 1 ≤ n := by linarith
    simp only [dif_neg, hnn0]
    apply (@Eq.trans _ _
      ((v p (n-1) + 1)
        + (- ((1-p)^n))
        + p^n*(n - v p (n-1) - 1)
        + bc p n (n-1)*(max 0 (n - 2 + p - v p (n-1)))))
    . apply En_eq_various_sums
      case hn => linarith
      case ha => 
        intros i h0i hin2
        rw [dif_neg (Nat.not_eq_zero_of_lt h0i)]
        apply le_antisymm
        . apply Finset.sup'_le
          intro j hji
          simp only [Finset.mem_range] at hji
          have this1 : v p (n - (j + 1)) = v p ((n-1) - j) := by
            congr 1
            rw [Nat.sub_sub, Nat.add_comm]
          have this2 : (j + v p ((n-1) - j)) ≤ v p (n-1) := by 
            apply iter_le_sub_1
            . apply theorem2_1 _ hp1 hp2
            . sorry
            . sorry
          linarith
        . sorry
      case hb =>
        sorry
      case hc =>
        sorry
      case hd =>
        sorry
    . rw [bc]
      simp only [choose_sub_1 _ hnn0]
      simp only [ Nat.sub_sub_self h1n, pow_one]
      ring