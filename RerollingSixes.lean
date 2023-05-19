import Mathlib.Data.Nat.Choose.Multinomial

import RerollingSixes.NatMemo
import RerollingSixes.NatMemoAttr
import RerollingSixes.FastChoose
import RerollingSixes.NatSubElim

set_option autoImplicit false

open BigOperators Nat

/- Binomial Expectation operator -/
def bc (p : ℚ) (n : ℕ) (i : ℕ) : ℚ :=
  p^(i : ℕ) * (1-p)^(n - i) * n.choose i

@[simp]
lemma bc_0 p n : bc p n 0 = (1-p)^n := by simp [bc]

@[simp]
lemma bc_1 p n : bc p n 1 = p * (1-p)^(n-1) * n := by simp [bc]

@[simp]
lemma bc_n p n : bc p n n = p^n := by simp [bc]

  
    
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


@[simp]
lemma v_0 p : v p 0 = 0 := rfl

@[simp]
lemma v_1 p : v p 1 = p := by
  unfold v En
  simp
  rw [ Finset.sum_fin_eq_sum_range, Finset.range_succ ]
  simp [bc]

@[simp]
lemma v_2 p (hp2 : p ≤ 1) : v p 2 = 3*p - p^3 := by
  unfold v En
  simp [ Finset.sum_fin_eq_sum_range, Finset.range_succ,
      Finset.sum_insert, sup_eq_max ]
  rw [ max_eq_left (by linarith) ]
  ring

-- (√5 - 1)/2 ≤ p
def phi_le (p : ℚ) := 0 < p ∧ 5 ≤ (2*p + 1)^2

/- A predicate that it’s not useful to continue with n coins,
when one can continue with n+1 coins -/
def pointless (p : ℚ) n := v p n + 1 ≤ v p (n + 1)

def iter_fast_growth_add
  (f : ℕ → ℚ) n₀ n
  (hf : ∀ i ≥ n₀, i < n → f i + 1 ≤ f (i + 1)) :
  ∀ i j, n₀ ≤ i → i + j ≤ n → f i + j ≤ f (i + j) := by
  intros i j hi hj
  induction j
  case zero => simp
  case succ j IH => calc
    f i + (succ j) = (f i + j) + 1 := by simp [add_assoc]
    _ ≤ f (i + j) + 1 := by
      apply add_le_add_right
      apply IH
      linarith
    _ ≤ f (i + j + 1) := by
      apply hf
      . linarith
      . linarith

def iter_fast_growth_sub
  (f : ℕ → ℚ) n₀ n (hn0n : n₀ ≤ n)
  (hf : ∀ i ≥ n₀, i < n → f i + 1 ≤ f (i + 1)) :
  ∀ j ≤ n - n₀, j + f (n - j) ≤ f n := by
  intros j hj
  calc
    j + f (n - j) = f (n - j) + j := add_comm _ _
    _ ≤ f (n - j + j) := by
      apply iter_fast_growth_add f n₀ _ hf 
      . apply Nat.le_sub_of_add_le
        rw [add_comm]
        apply Nat.add_le_of_le_sub hn0n hj
      . rw [Nat.le_sub_iff_add_le hn0n] at hj
        rw [Nat.sub_add_cancel]
        linarith
    _ = f n := by
      rw [Nat.sub_add_cancel ]
      apply Nat.le_trans hj
      apply Nat.sub_le

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
    nat_intervals
    /-
    cases' n with n; cases hn
    simp
    -/
  have h0n1 : 0 ≠ n -1 := by
    -- nat_intervals
    cases' n with n; cases hn
    have hn : 2 ≤ n := by linarith
    cases' n with n; cases hn
    simp
    linarith
  rw [En_upd p n _ (n-1) (by simp) a]; rw [hd]; congr 1
  rw [En_upd p n _ n (by simp) a]; simp [hnn1 ]; rw [hc]; simp; congr 1
  rw [En_upd p n _ 0 (by simp) a]; simp [h0nn, h0n1 ]; rw [hb]; simp; congr 1
  conv => right; apply (En_const p n _).symm
  congr
  funext j hj
  simp
  intros hj1 hj2 hj3
  apply ha
  . nat_intervals
    -- simp [*, zero_lt_of_ne_zero]
  . nat_intervals
    /-
    apply Nat.lt_of_le_of_ne _ hj3
    apply Nat.le_sub_of_add_le
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne hj hj2
    -/

@[simp]
lemma choose_sub_1
  (n : ℕ) (hn : n ≠ 0) : n.choose (n - 1) = n := by
  cases n
  . simp at hn 
  . apply Nat.choose_succ_self_right


lemma sup'_eq_of_max
  {α β} [SemilatticeSup β]
  {s : Finset α}
  {hs f i} 
  (hi : i ∈ s)
  (x : β)
  (heq : f i = x)
  (hle : ∀ i ∈ s, f i ≤ x)
  : Finset.sup' s hs f = x := by
  apply le_antisymm
  . apply Finset.sup'_le _ _ hle
  . apply Finset.le_sup'_of_le _ hi
    rw [heq]


/- With n heads, it's best to fix all heads -/
lemma all_heads_is_great 
  p (hp1 : 1/2 ≤ p) (hp2 : p < 1) n hr :
  Finset.sup' (Finset.range n) hr (fun j => ↑j + 1 + v p (n - (j + 1))) = n := by
  have h1n : 1 ≤ n := by
    simp at hr
    nat_intervals
    -- exact Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero hr)
  have hmem : (n-1) ∈ Finset.range n := by
    simp
    nat_intervals
    /-
    apply Nat.sub_lt_left_of_lt_add h1n
    simp
    -/
  apply sup'_eq_of_max hmem
  case heq =>
    rw [ Nat.sub_add_cancel h1n]
    unfold v
    simp
    rw [ cast_sub h1n ]
    simp
  case hle =>
    intro i hin
    simp at hin
    apply @le_trans
    . apply add_le_add_left
      apply v_le_n (by linarith) (le_of_lt hp2)
    . rw [ cast_sub, cast_add ]
      simp
      nat_intervals
      -- apply succ_le_of_lt hin

/- With 0 < i < n-1 heads, it's best to fix one head -/
lemma best_is_to_fix_just_one 
  p n
  (hpointless : ∀ i, 2 ≤ i → i < n - 1 → pointless p i)
  i (h0i : 0 < i) (hin2 : i < n - 1) hr:
  Finset.sup' (Finset.range i) hr (fun j => ↑j + 1 + v p (n - (j + 1)))
    = v p (n - 1) + 1 := by
  have hmem : 0 ∈ Finset.range i := by simp [h0i]
  apply sup'_eq_of_max hmem 
  case heq => simp [add_comm]
  case hle =>
    intro j hji
    simp only [Finset.mem_range] at hji
    have this1 : v p (n - (j + 1)) = v p ((n-1) - j) := by
      congr 1
      rw [Nat.sub_sub, Nat.add_comm]
    have this2 : (j + v p ((n-1) - j)) ≤ v p (n-1) := by 
      apply iter_fast_growth_sub _ 2
      . linarith
      . intro j hj1 hj2
        apply hpointless _ hj1 hj2
      . rw [Nat.sub_sub, Nat.add_comm, <- Nat.sub_sub]
        
        nat_intervals
        /-
        apply le_sub_of_add_le
        apply succ_le_of_lt
        apply lt_of_lt_of_le hji
        apply le_sub_of_add_le
        apply succ_le_of_lt
        apply add_lt_of_lt_sub
        apply hin2
        -/
    linarith  

lemma almost_all_heads_is_great 
  p n hr 
  (hpointless : ∀ i, 2 ≤ i → i < n - 1 → pointless p i) :
  Finset.sup' (Finset.range (n-1)) hr (fun j => ↑j + 1 + v p (n - (j + 1))) =
    max (v p (n-1) + 1) (v p 1 + n -1) := by
  replace hr : 1 < n := by simp at hr; assumption
  cases' n with n; simp at hr
  cases' n with n; simp at hr
  cases' n with n; simp [add_sub_assoc, add_comm]
  simp_rw [Nat.succ_sub_one]
  simp_rw [Finset.range_succ]
  rw [Finset.sup'_insert (by simp)]
  simp_rw [<- Finset.range_succ]
  rw [sup_eq_max]
  rw [max_comm]
  congr 1
  . rw [best_is_to_fix_just_one p _ hpointless _ (by simp) (by simp) ]
    rfl
  . simp; ring

def v_simp p n :=
  if n ≤ 2 then v p n
  else 
  v p (n-1) + 1 +
  p^n * (n - 1 - v p (n-1)) +
  n * p^(n-1) * (1-p) * max 0 (n - 2 + p - v p (n-1) ) -
  (1 - p)^n

lemma v_eq_v_simp p (hp1 : 1/2 ≤ p) (hp2 : p < 1) n
  (hpointless : ∀ i, 2 ≤ i → i < n - 1 → pointless p i) :
  v p n = v_simp p n := by
  unfold v_simp
  split
  case inl hnle2 => rw [v]
  case inr h2len =>
    rw [v]
    have hnn0 : n ≠ 0 := by linarith
    have hnn10 : n - 1 ≠ 0 := by
      nat_intervals
      /-
      cases' n with n; simp at hnn0
      cases' n with n; simp at h2len
      simp
      -/
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
        apply best_is_to_fix_just_one _ _ hpointless _ h0i hin2 
      case hb => simp [bc]
      case hc =>
        rw [dif_neg hnn0]
        rw [all_heads_is_great _ hp1 hp2]
        simp [bc]
        left
        ring
      case hd =>
        rw [dif_neg hnn10]
        congr 1
        apply eq_sub_of_add_eq
        rw [almost_all_heads_is_great p n _ hpointless ]
        rw [<- max_add_add_right]
        congr 1
        . simp
        . simp; ring
    . rw [bc]
      have h1n : 1 ≤ n := by linarith
      simp only [choose_sub_1 _ hnn0]
      simp only [Nat.sub_sub_self h1n, pow_one]
      ring


lemma lemma1 
  p (hp1 : phi_le p) (hp2 : p < 1) :
  ∀ n, v p (n+1) + 1 ≤ v p (n+2)
       ∧ v p (n+2) < (n+2) - ((1-p)/p)^(n+3) := by
  intro n
  rw [phi_le] at hp1
  have hp3 : 1 < 2 * p := by nlinarith
  induction n using Nat.case_strong_induction_on
  case hz =>
    norm_num
    constructor
    . rw [ v_2 _ (le_of_lt hp2) ]
      nlinarith
    . apply lt_of_mul_lt_mul_right _ (by nlinarith : 0 ≤ p^3)
      rw [ v_2 _ (le_of_lt hp2), sub_mul, sub_mul, div_mul_cancel ]
      case h => nlinarith
      apply lt_of_sub_neg
      rw [(by nlinarith : 
        3 * p * p ^ 3 - p ^ 3 * p ^ 3 - (2 * p^3 - (1 - p) ^ 3)
        = - (p-1)^2 * (p^4 + 2*p^3 + p -1 )) ]
      apply mul_neg_of_neg_of_pos 
      . nlinarith
      . have : 1 < 2 * p := by nlinarith
        calc
          p ^ 4 + 2 * p ^ 3 + p - 1 ≥ 2 * p ^ 3 + p - 1 := by nlinarith
          _ > p ^ 2 + p - 1 := by nlinarith
          _ ≥ 0 := by nlinarith
  case hi n IH =>
    simp only [<- add_one, add_assoc, cast_add]
    norm_num
    rewrite [(?eq :
      v p (n + 3) = v p (n + 2) + 1 + p^(n+3) * (n+2 - v p (n+2)) - (1-p)^(n+3))]
    case eq =>
      trans
      . apply v_eq_v_simp p (by nlinarith) hp2
        . intro i hi1 hi2 
          unfold pointless
          have : i - 1 ≤ n := by nat_intervals
          replace IH : _ := (IH (i - 1) this).1
          rw [(by cases i; simp at hi1; simp : i - 1 + 1 = i)] at IH
          rw [(by cases i; simp at hi1; simp : i - 1 + 2 = i + 1)] at IH
          exact IH
      . unfold v_simp
        rw [if_neg]; case hnc => linarith
        rw [max_eq_left]
        . simp; left; linarith
        . simp_rw [cast_add]
          have : v p (1 + (n + 1)) ≥ v p 1 + (n + 1 : ℕ) := by
            apply iter_fast_growth_add _ 1 (n+2)
            . intro i hi1 hi2 
              have : i - 1 ≤ n := by nat_intervals
              replace IH : _ := (IH (i - 1) this).1
              rw [(by cases i; simp at hi1; simp : i - 1 + 1 = i)] at IH
              rw [(by cases i; simp at hi1; simp : i - 1 + 2 = i + 1)] at IH
              exact IH
            . exact (le_refl _)
            . linarith
          simp [cast_add] at this
          rw [cast_ofNat]
          rw [(by linarith : 1 + (n + 1) = n + 2)] at this
          rw [(by linarith : ↑n + 3 - 2 + p = p + (n + 1))]
          simp [this]

    constructor
    . sorry
    . sorry



lemma theorem2_1 p (hp1 : 0.5 ≤ p) (hp2 : p < 1) :
  ∀ n ≥ 2, pointless p n :=
  sorry

lemma theorem2_2
  p (hp1 : phi_le p) (hp2 : p < 1) :
  ∀ n ≥ 1, pointless p n :=
  sorry
