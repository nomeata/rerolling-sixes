import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

syntax (name := equals) "equals" term "by" tacticSeq: conv
macro_rules
  | `(conv|equals $rhs:term by $t:tacticSeq) => `(conv|tactic => show (_ = $rhs); ($t) )

syntax (name := cchange)
  "cchange" Lean.Parser.Tactic.Conv.convSeq (" with " (term (" by " tacticSeq)?)?)? : tactic
macro_rules
  | `(tactic|cchange $conv:convSeq with $rhs:term by $t:tacticSeq) =>
    `(tactic|conv => { ($conv); tactic => { show (_ = $rhs); ($t)}; done } )
  | `(tactic|cchange $conv:convSeq with $rhs:term ) =>
    `(tactic|conv => { ($conv); tactic => { show (_ = $rhs) }; done } )
  | `(tactic|cchange $conv:convSeq with) =>
    `(tactic|conv => $conv )
  | `(tactic|cchange $conv:convSeq) =>
    `(tactic|conv => $conv )

-- example : 1 = 2 + 3 := by
--   cchange { right; right } with 4 => { sorry }

lemma lemma4 {n : ℕ} {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  HasSum (fun (k : ℕ) => (k + (n + 1)) * r ^ (k + (n+1))) 
         (r^(n+1) * (n / (1-r) + 1 / (1 - r)^2)) := by
  have h₃' : 1 - r ≠ 0 := (Iff.mpr sub_pos h₂).ne'
  cchange left ; ext k with r ^ (n+1) * ((↑n + 1) * r^k + k * r ^ k) by ring
  conv => right; equals r ^ (n+1) * ((↑n+1) * (1/(1 - r)) + r / (1 - r) ^ 2) by
    field_simp; left; ring
  apply HasSum.mul_left
  apply HasSum.add
  . apply HasSum.mul_left
    rw [one_div]
    apply hasSum_geometric_of_lt_1 h₁ h₂
  . apply hasSum_coe_mul_geometric_of_norm_lt_1
    rw [Real.norm_eq_abs, abs_of_nonneg h₁]
    exact h₂
