/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic

/-!
# The exponent of a Lévy measure, extended-valued

`levyExpL L ω = ∫ (1 - cos⟨ω, x⟩) L(dx)`, with values in `ℝ≥0∞`. It stood in
`AffineHemigroup.Defs.Cones`, which imports this file; it is here unchanged, so that
`AffineHemigroup.LevyKhintchineNegDef` can read it without the cone fields (Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Set Matrix
open scoped ENNReal MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- **The exponent of a Lévy measure** `ψ_L(ω) := ∫ (1 - cos⟨ω, x⟩) L(dx)`
(`prop:similarity-general-bounded-shape`(1)), `ℝ≥0∞`-valued. -/
noncomputable def levyExpL (L : Measure (Rd d)) (ω : Rd d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂L

end

end AffineHemigroup
