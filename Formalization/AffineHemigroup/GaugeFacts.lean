/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.IsotropicFamily

/-!
# Two facts on gauges

A gauge is positive on `(0,∞)` (`IsGauge.pos`), and the square of a gauge is a gauge
(`IsGauge.sq`). They stood in `AffineHemigroup.IsotropicCorner`, which imports this file; they
are here unchanged (Q-0452).
-/

namespace AffineHemigroup

section

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)
open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder RealInnerProductSpace

variable {d : ℕ}

theorem IsGauge.pos {χ : ℝ → ℝ} (hχ : IsGauge χ) {t : ℝ} (ht : 0 < t) : 0 < χ t := by
  have := hχ.2.1 (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (mem_Ici.2 ht.le) ht
  rwa [hχ.1] at this

/-- The square of a gauge is a gauge. -/
theorem IsGauge.sq {χ : ℝ → ℝ} (hχ : IsGauge χ) : IsGauge fun t => χ t ^ 2 := by
  refine ⟨by simp [hχ.1], fun a ha b hb hab => ?_, fun y hy => ?_⟩
  · exact pow_lt_pow_left₀ (hχ.2.1 ha hb hab) (hχ.nonneg ha) two_ne_zero
  · obtain ⟨t, ht, htχ⟩ := hχ.2.2 (mem_Ici.2 (Real.sqrt_nonneg y))
    exact ⟨t, ht, by simp only; rw [htχ, Real.sq_sqrt hy]⟩

end

end AffineHemigroup
