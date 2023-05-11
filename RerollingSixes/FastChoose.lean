import Mathlib.Data.Nat.Choose.Basic

def fast_choose n k := Nat.descFactorial n k / Nat.factorial k
@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))
