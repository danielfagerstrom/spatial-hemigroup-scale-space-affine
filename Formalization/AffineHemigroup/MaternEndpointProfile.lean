/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Subordination
import AffineHemigroup.Defs.RadialProfile
import AffineHemigroup.OriginBoundedness

/-!
# The radial profile of the Matérn law

`maternEndpointProfile hd γ hγ`: the radial profile `k₀ = γ F₀`, `F₀` the subordinated heat
profile of index `0` (`AffineHemigroup.Subordination`), which is the profile of the Matérn law of
index `γ` (`prop:tempered-step-cone`(4), `blueprint/src/parts/05-orbits.tex`), and the exponent
of a subordinated profile (`exponentL_of_subProfile`). Lean core only.

The three declarations stood in `AffineHemigroup.TemperedStepCone`, which imports this file; they
are here unchanged, for the formal example at the Matérn law (`AffineHemigroup.Witnesses`)
(Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- A tempering factor is positive near `0`. -/
theorem IsTemperingProfile.eventually_pos {j : ℝ → ℝ} {L : ℝ} (hL0 : 0 < L)
    (hL : Tendsto j (𝓝[>] 0) (𝓝 L)) : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ 0 < j r :=
  eventually_mem_nhdsWithin.and (hL.eventually (lt_mem_nhds hL0))

/-- **The exponent of a subordinated profile**: if `k(r) = r^{-2a} c F_a(r)` on `(0,∞)`, then
`ψ_I(ω) = c ∫₀^∞ s^{-1-a} e^{-s}(1 - e^{-s|ω|²}) ds`. -/
theorem exponentL_of_subProfile (hd : 1 ≤ d) (K : RadialProfile d) {a c : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hK : ∀ r : ℝ, 0 < r → K.k r = r ^ (-(2 * a)) * (c * subProfile d a r))
    (ω : Rd d) :
    K.exponentL ω = ENNReal.ofReal c * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 - a) *
      Real.exp (-s)) * ENNReal.ofReal (1 - Real.exp (-(s * ‖ω‖ ^ 2))) := by
  rw [← lintegral_one_sub_cos_subProfile hd ha ω, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold RadialProfile.exponentL
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hpow : ‖x‖ ^ (-(d : ℝ) - 2 * a) = ‖x‖ ^ (-(2 * a)) / ‖x‖ ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hρ]; ring_nf
    rw [RadialProfile.m, hK _ hρ, hpow]
    ring

/-- **`prop:tempered-step-cone`(4)**, the profile: for `γ > 0`, `k₀ = γ F₀` is a radial profile;
`F₀(r) ≤ C e^{-r/2}` gives the integrability. -/
noncomputable def maternEndpointProfile (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) : RadialProfile d where
  k := fun r => γ * subProfile d 0 r
  k_nonneg := fun r _ => mul_nonneg hγ.le (subProfile_nonneg _ _)
  k_antitone := fun r hr s hs hrs => mul_le_mul_of_nonneg_left
    (subProfile_antitone hd le_rfl (mem_Ici.2 (le_of_lt hr)) (mem_Ici.2 (le_of_lt hs)) hrs) hγ.le
  k_ne_zero := by
    have hF0 := subProfile_zero_pos hd le_rfl (d := d)
    have hlim : Tendsto (fun r => γ * subProfile d 0 r) (𝓝[>] 0) (𝓝 (γ * subProfile d 0 0)) :=
      ((continuous_const.mul (continuous_subProfile hd le_rfl (d := d))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    obtain ⟨r, hr, hk⟩ := (IsTemperingProfile.eventually_pos (mul_pos hγ hF0) hlim).exists
    exact ⟨r, hr, hk.ne'⟩
  integrable := by
    set C := ∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - (0 : ℝ)) *
        Real.exp (-(1 / 2) / (4 * t)) with hC
    have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have : (0 : ℝ) < t := ht
      positivity
    have hbound : ∀ r : ℝ, 0 ≤ r → γ * subProfile d 0 r ≤ γ * C * Real.exp (-(1 / 2) * r) := by
      intro r hr
      have := subProfile_le_exp hd le_rfl (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr (d := d)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) hγ.le
      rw [hC]; congr 2; ring
    set g : ℝ → ℝ≥0∞ := fun r =>
      ENNReal.ofReal (min (r ^ 2) 1 * (γ * C * Real.exp (-(1 / 2) * r) / r ^ d)) with hg
    have hgm : Measurable g := by fun_prop
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => ?_ : _ ≤ ∫⁻ x : Rd d, g ‖x‖)
    · rw [lintegral_radial hd g hgm]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      have hint : IntegrableOn (fun r : ℝ => γ * C * Real.exp (-(1 / 2) * r)) (Ioi 0) :=
        (exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul _
      refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne
        (setLIntegral_mono' measurableSet_Ioi fun r hr => ?_)
      have hr0 : (0 : ℝ) < r := hr
      rw [hg, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hpow : r ^ d = r ^ (d - 1) * r := by rw [← pow_succ]; congr 1; omega
      have hmin : min (r ^ 2) 1 ≤ r := by
        rcases le_or_gt r 1 with h | h
        · exact (min_le_left _ _).trans (by nlinarith)
        · exact (min_le_right _ _).trans h.le
      have hB : 0 ≤ γ * C * Real.exp (-(1 / 2) * r) := by positivity
      calc min (r ^ 2) 1 * (γ * C * Real.exp (-(1 / 2) * r) / r ^ d) * r ^ (d - 1)
          = min (r ^ 2) 1 / r * (γ * C * Real.exp (-(1 / 2) * r)) := by
            rw [hpow]; field_simp
        _ ≤ 1 * (γ * C * Real.exp (-(1 / 2) * r)) := by
            refine mul_le_mul_of_nonneg_right ?_ hB
            rw [div_le_one hr0]; exact hmin
        _ = γ * C * Real.exp (-(1 / 2) * r) := one_mul _
    · rcases eq_or_ne x 0 with rfl | hx
      · simp [hg]
      have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact div_le_div_of_nonneg_right (hbound _ hρ.le) (by positivity)

end

end AffineHemigroup
