/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic
import Mathlib.Probability.Distributions.Gamma

/-!
# The law of `√(2V) Z`, `V` Gamma distributed and `Z` standard normal

`gammaGaussLaw d γ`: the law on `ℝ^d` of `√(2V) Z` with `V` Gamma distributed of shape `γ` and
scale `1` and `Z` standard normal, independent. For `γ > 0` its transform is `(1 + |ξ|²)^{-γ}`
(`AffineHemigroup.MaternLaw`): it is the Matérn law of index `γ`. The definition stood in
`AffineHemigroup.Defs.Orbits`, which imports this file; it is here unchanged (Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- **The law of `√(2V) Z`** (`prop:affine-orbits`(4)): `V` Gamma distributed of shape `γ` and
scale `1`, `Z` standard normal on `ℝ^d`, independent. -/
noncomputable def gammaGaussLaw (d : ℕ) (γ : ℝ) : Measure (Rd d) :=
  ((ProbabilityTheory.gammaMeasure γ 1).prod (ProbabilityTheory.stdGaussian (Rd d))).map
    fun p => Real.sqrt (2 * p.1) • p.2

end

end AffineHemigroup
