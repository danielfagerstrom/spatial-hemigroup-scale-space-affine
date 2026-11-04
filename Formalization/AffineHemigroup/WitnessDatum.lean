/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Origin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `def:filtration-thresholds`: the witness is a delay datum

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `def:filtration-thresholds`, the presupposition
of "let `D^{(w)}` be the delay datum [B, Def. 4.11] with drift `0` and profile
`u^{-1/2} + w 1_{[1,2]}(u)`" ([B, Lem. 4.12]). Wave 2, group A (Q-0281).

The two integrability conditions are `∫₀¹ u^{-1/2} du < ∞` (the bump vanishes on `(0,1)`) and
`∫₁^∞ (u^{-3/2} + w 1_{[1,2]}(u)/u) du < ∞`.
-/

namespace AffineHemigroup

open MeasureTheory Set

theorem witnessProfile_of_pos {w u : ℝ} (hu : 0 < u) :
    witnessProfile w u = u ^ (-(1 : ℝ) / 2) + (if u ∈ Icc (1 : ℝ) 2 then w else 0) := by
  simp [witnessProfile, hu]

theorem measurable_witnessProfile (w : ℝ) : Measurable (witnessProfile w) := by
  unfold witnessProfile
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (measurable_id.pow_const _).add (Measurable.ite measurableSet_Icc measurable_const
    measurable_const)

/-- **`def:filtration-thresholds`**, the presupposition of "let `D^{(w)}` be the delay datum
[B, Def. 4.11] with drift `0` and profile `u^{-1/2} + w 1_{[1,2]}(u)`" (`w > 0`): those data satisfy
[B, Def. 4.11]'s conditions ([B, Lem. 4.12]), and the datum's exponent is `witnessExponent w`. -/
theorem witness_isDelayDatum {w : ℝ} (hw : 0 < w) :
    ∃ D : DelayDatum, D.b₀ = 0 ∧ (∀ u ∈ Ioi (0 : ℝ), D.k u = witnessProfile w u) ∧
      ∀ σ : ℝ, D.exponent σ = witnessExponent w σ := by
  have hnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ witnessProfile w u := by
    intro u hu
    rw [witnessProfile_of_pos hu]
    have h1 : 0 ≤ u ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hu) _
    split_ifs <;> linarith
  have h0 : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (witnessProfile w u) ≠ ⊤ := by
    have hint : IntegrableOn (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by norm_num)
    have heq : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (witnessProfile w u)
        = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ (-(1 : ℝ) / 2)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [witnessProfile_of_pos hu.1, if_neg (fun h => absurd h.1 (not_le.mpr hu.2)), add_zero]
    rw [heq]
    exact (hint.lintegral_lt_top).ne
  have h1 : ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (witnessProfile w u / u) ≠ ⊤ := by
    have hint : IntegrableOn (fun u : ℝ => u ^ (-(3 : ℝ) / 2) + (Icc (1 : ℝ) 2).indicator
        (fun _ => w) u) (Ioi (1 : ℝ)) := by
      refine Integrable.add (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one) ?_
      refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
      exact (integrableOn_const (by simp [Real.volume_Icc]) ).restrict
    refine ne_top_of_le_ne_top (hint.lintegral_lt_top).ne
      (setLIntegral_mono' measurableSet_Ioi fun u (hu : 1 < u) => ?_)
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [witnessProfile_of_pos hu0, add_div]
    have hpow : u ^ (-(1 : ℝ) / 2) / u = u ^ (-(3 : ℝ) / 2) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu0]
      norm_num
    rw [hpow]
    by_cases hI : u ∈ Icc (1 : ℝ) 2
    · rw [if_pos hI, indicator_of_mem hI]
      have : w / u ≤ w := div_le_self hw.le hu.le
      linarith
    · rw [if_neg hI, indicator_of_notMem hI, zero_div]
  refine ⟨⟨0, witnessProfile w, le_rfl, hnn, (measurable_witnessProfile w).aemeasurable,
    by simp [witnessProfile], h0, h1⟩, rfl, fun u _ => rfl, fun σ => rfl⟩

end AffineHemigroup
