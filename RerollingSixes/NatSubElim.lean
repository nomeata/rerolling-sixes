import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import RerollingSixes.NatSubElimRuleSet

variable (n : ℕ)
variable (i : ℕ)
variable (j : ℕ)
variable (k : ℕ)

structure SC (p q : Prop) : Prop :=
  imp : p → q

inductive MyFalse : Prop :=

@[aesop norm simp (rule_sets [NatElim])]
lemma sc (p q : Prop) : SC p q ↔ (¬ p ∨ (p /\ q)) := sorry

lemma le_intro : (i < n -> MyFalse) -> n ≤ i := sorry
lemma lt_intro : (i ≤ n -> MyFalse) -> n < i := sorry

attribute [aesop safe apply (rule_sets [NatElim])]
  le_intro lt_intro

lemma le_of_add_one_lt :
  n < m → n + 1 ≤ m := Nat.succ_le_of_lt

lemma le_sub (h1 : i ≤ n - j) : SC (j ≤ n) (i + j ≤ n) :=
  .mk (fun h2 => Nat.add_le_of_le_sub h2 h1)
lemma sub_le (h1 : n - j ≤ i) : SC (j ≤ n) (n ≤ i + j) :=
  .mk sorry
lemma sub_add_le (h1 : n - j + k ≤ i) : SC (j ≤ n) (n + k ≤ i + j) :=
  .mk sorry
lemma ne_sub (h1 : i ≠ n - j) : SC (j ≤ n) (i + j ≠ n) :=
  .mk sorry
lemma le_improve1 : n ≤ m -> ¬ (n = m) → n + 1 ≤ m := sorry
lemma le_improve2 : n ≤ m -> ¬ (m = n) → n + 1 ≤ m := sorry

attribute [aesop safe destruct (rule_sets [NatElim])]
  le_sub sub_le sub_add_le ne_sub le_improve1 le_improve2
  le_of_add_one_lt


def linarithTactic := do
  Lean.Elab.Tactic.evalTactic (← `(tactic| linarith))

attribute [aesop safe tactic (rule_sets [NatElim])] linarithTactic

syntax "nat_intervals" : tactic
macro_rules
  | `(tactic| nat_intervals) => `(tactic|
    aesop (rule_sets [$(Lean.mkIdent `NatElim):ident])
  )

example : n ≠ 0 → n - 1 < n := by
  intros
  nat_intervals

example : ¬i = 0 → 0 < i := by
  intros
  nat_intervals

example : i ≤ n → j ≤ n - i → i ≤ n - j := by
  intros
  nat_intervals

example : 3 ≤ n → n ≠ n - 1 := by
  intros
  -- loops: nat_intervals
  sorry

example : 3 ≤ n → j ≤ n → ¬j = 0 → ¬j = n → ¬j = n - 1 → j < n - 1 := by
  intros
  nat_intervals

example : 0 < i → i < n - 1 → j < i → j ≤ n - 2 - 1 := by
  intros
  nat_intervals
  

set_option trace.aesop true