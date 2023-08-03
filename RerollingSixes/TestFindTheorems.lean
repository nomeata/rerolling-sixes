import RerollingSixes.FindTheorems

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
-- import Mathlib

set_option autoImplicit false


set_option profiler true
set_option profiler.threshold 100

def foo : Bool := true

theorem foo_eq_foo_eq_foo_eq_foo : (foo = foo) = (foo = foo) := refl _

#find_theorems "all" (Nat → Bool)
-- #find Nat → Bool
#find_theorems |- (Nat → Bool) "all"

#find_theorems (Lean.Name → String)
#find_theorems |- (Lean.Name → String)
-- #find_theorems (Real.sqrt ?a * Real.sqrt ?a)

set_option pp.rawOnError true
-- #find_theorems  HMul.hMul HAdd.hAdd "Nat.left_distr"
-- #find_theorems (_ * (_ + _)) "distr"
#find_theorems tsum (_ * _ ^ _)
#find_theorems ⊢ (tsum _ = _) (_ * _ ^ _)

-- #find_theorems Eq

-- #find_theorems (Lean.Syntax → Lean.Name)
-- #find (Lean.Syntax → Lean.Name)

-- #find_theorems (∑' _, _ = _) HMul.hMul HPow.hPow

-- #find_theorems id (_ = _)