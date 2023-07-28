import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed

import RerollingSixes.FindTheorems

import Mathlib

set_option profiler true
set_option profiler.threshold 100

-- #find (tsum _ * tsum _ = _)

-- #find_theorems Eq

#find_theorems (Lean.Syntax → Lean.Name)
#find (Lean.Syntax → Lean.Name)

#find_theorems (∑' _, _ = _) HMul.hMul HPow.hPow