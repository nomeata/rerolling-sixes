import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum


private lemma summable_geometric_of_lt_1_norm {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  Summable (fun n => ‖r ^ n‖) := by
  convert (summable_geometric_of_lt_1 h₁ h₂) 
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg h₁]

private lemma Finset.sum_range_pow_diff {r : ℝ} :
  Finset.sum (Finset.range (n + 1)) (fun k => r ^ k * r ^ (n - k)) = (n+1) * r^n := by
  trans Finset.sum (Finset.range (n + 1)) (fun _ => r ^ n )
  . apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk 
    rw [mul_comm, ← pow_add]
    congr
    rw [ Nat.sub_add_cancel ]
    apply Nat.le_of_lt_succ
    apply hk
  . simp

lemma summable_n_mul_pow_n_plus_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  Summable (fun n : ℕ => (n + 1) * r ^ n) := by
  have h := summable_norm_sum_mul_range_of_summable_norm
      (summable_geometric_of_lt_1_norm h₁ h₂)
      (summable_geometric_of_lt_1_norm h₁ h₂)
  simp_rw [Finset.sum_range_pow_diff] at h
  apply summable_of_summable_norm h

lemma summable_n_mul_pow_n {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  Summable (fun n : ℕ => n * r ^ n) := by
  apply (summable_of_norm_bounded _ (summable_n_mul_pow_n_plus_1 h₁ h₂))
  intro n
  simp only [norm_mul, Real.norm_eq_abs, Nat.abs_cast, norm_pow, abs_of_nonneg h₁]
  apply mul_le_mul_of_nonneg_right
  . simp
  . positivity

lemma tsum_n_mul_pow_n {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  (∑' (n : ℕ), n * r ^ n) = r / (1 - r)^2 := calc
    _ = ∑' (n : ℕ), (n+1)*r^(n+1) := by
      rw [ tsum_eq_zero_add (summable_n_mul_pow_n h₁ h₂) ]
      simp
    _ = ∑' (n : ℕ), r * ((n+1)*r^n) := by congr with n; ring
    _ = r * (∑' (n : ℕ), (n+1)*r^n) := by
      apply Summable.tsum_mul_left
      exact (summable_n_mul_pow_n_plus_1 h₁ h₂)
    _ = r * (∑' (n : ℕ), Finset.sum (Finset.range (n + 1)) fun k => r^k * r^(n - k)) := by
      simp_rw [← Finset.sum_range_pow_diff]
    _ = r * ((∑' (n : ℕ), r ^ n) * (∑' (n : ℕ), r ^ n)) := by
      congr; symm; exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm 
        (summable_geometric_of_lt_1_norm h₁ h₂)
        (summable_geometric_of_lt_1_norm h₁ h₂)
    _ = r * ((∑' (n : ℕ), r ^ n))^2 := by rw [pow_two]
    _ = r * ((1-r)⁻¹)^2 := by congr; apply tsum_geometric_of_lt_1 h₁ h₂
    _ = r * (1/(1-r))^2 := by congr; exact inv_eq_one_div (1 - r)
    _ = _ := by rw [div_pow, @mul_div, one_pow, mul_one]

lemma hasSum_n_mul_pow_n {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  HasSum (fun (n : ℕ) => n * r ^ n) (r / (1 - r)^2) := by
  rw [(summable_n_mul_pow_n h₁ h₂).hasSum_iff] 
  apply tsum_n_mul_pow_n h₁ h₂

syntax (name := equals) "equals" term "by" tacticSeq: conv
macro_rules
  | `(conv|equals $rhs:term by $t:tacticSeq) => `(conv|tactic => show (_ = $rhs); . $t )

lemma lemma4 {n : ℕ} {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  HasSum (fun (k : ℕ) => (k + (n + 1)) * r ^ (k + (n+1))) 
         (r^(n+1) * (n / (1-r) + 1 / (1 - r)^2)) := by
  have h₃ : 1 - r > 0 := by exact Iff.mpr sub_pos h₂
  have expand : 1 / (1 - r) = (1 - r) / (1-r)^2 := by
    rw [pow_two, div_mul_eq_div_div, div_self]; positivity
  conv => left; ext k; equals r ^ (n+1) * ((↑n + 1) * r^k + k * r ^ k) by 
    ring
  conv => right; equals r ^ (n+1) * ((↑n+1) * (1/(1 - r)) + r / (1 - r) ^ 2) by
    rw [ mul_div, mul_one, add_div, expand ]; ring
  apply HasSum.mul_left
  apply HasSum.add
  . apply HasSum.mul_left
    rw [one_div]
    apply hasSum_geometric_of_lt_1 h₁ h₂
  . apply hasSum_n_mul_pow_n h₁ h₂