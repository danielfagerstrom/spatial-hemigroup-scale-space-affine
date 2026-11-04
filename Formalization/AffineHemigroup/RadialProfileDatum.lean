/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.RadialProfile
import AffineHemigroup.Polar

/-!
# The origin datum of a radial profile

A radial profile `k` in dimension `d` gives the isotropic origin datum `(0, |S^{d-1}| k)`
(`RadialProfile.toOriginDatum`), with the same exponent and with profile at the origin
`|S^{d-1}| k(0+)`. Lean core only.

`RadialProfile.measurable_m_norm` stood in `AffineHemigroup.OrbitStepCone` and the other four
declarations in `AffineHemigroup.OrbitRays`; both import this file. They are here unchanged,
each with the `open` lines of its file, for the formal example at the Matérn law
(`AffineHemigroup.Witnesses`) (Q-0452).
-/

namespace AffineHemigroup

/-! ## From `AffineHemigroup.OrbitStepCone` -/

section

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

namespace RadialProfile

/-- `x ↦ m(|x|)` is measurable. -/
theorem measurable_m_norm (hd : 1 ≤ d) (K : RadialProfile d) :
    Measurable fun x : Rd d => K.m ‖x‖ := by
  have hk := measurable_indicator_Ioi_of_antitoneOn K.k_antitone
  have heq : (fun x : Rd d => K.m ‖x‖) =
      fun x => (Ioi (0 : ℝ)).indicator K.k ‖x‖ / ‖x‖ ^ d := by
    funext x
    by_cases hx : ‖x‖ = 0
    · simp [m, hx, zero_pow (by omega : d ≠ 0)]
    · have hpos : (0 : ℝ) < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      simp only [Set.indicator_apply, Set.mem_Ioi, if_pos hpos]
      rfl
  rw [heq]
  exact (hk.comp continuous_norm.measurable).div (continuous_norm.measurable.pow_const _)

end RadialProfile

end

/-! ## From `AffineHemigroup.OrbitRays` -/

section

open MeasureTheory Set Matrix Real Filter Complex
open scoped MatrixOrder RealInnerProductSpace ENNReal Topology

variable {d : ℕ}

namespace RadialProfile

/-- **The radial form of the integrability**: `∫ (|x|² ∧ 1) m(|x|) dx = |S^{d-1}| ∫₀^∞ (r² ∧ 1) k(r) dr/r`. -/
theorem lintegral_radial (hd : 1 ≤ d) (K : RadialProfile d) :
    ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) =
      ENNReal.ofReal (sphereArea d) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1 * K.k r / r) := by
  have hm : Measurable fun x : Rd d => ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) :=
    ((by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).mul
      (K.measurable_m_norm hd)).ennreal_ofReal
  rw [lintegral_polar hd _ hm, (sphereArea_eq_toSphere hd).1]
  have hinner : ∀ η : Metric.sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (min (‖r • (η : Rd d)‖ ^ 2) 1 * (K.k ‖r • (η : Rd d)‖ /
        ‖r • (η : Rd d)‖ ^ d)) * ENNReal.ofReal (r ^ (d - 1))) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1 * K.k r / r) := by
    intro η
    have hη : ‖(η : Rd d)‖ = 1 := by simp
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr0.le, ← ENNReal.ofReal_mul (by
      have := K.k_nonneg r hr0
      have : 0 ≤ min (r ^ 2) 1 := by positivity
      positivity)]
    congr 1
    have hpow : r ^ d = r ^ (d - 1) * r := by rw [← pow_succ]; congr 1; omega
    rw [hpow]
    field_simp
  simp_rw [hinner]
  rw [lintegral_const, mul_comm]

/-- **The origin datum of a radial profile**: `(0, |S^{d-1}| k)`. -/
noncomputable def toOriginDatum (hd : 1 ≤ d) (K : RadialProfile d) : OriginDatum d where
  a := 0
  k := fun r => sphereArea d * K.k r
  a_nonneg := le_rfl
  k_nonneg := fun r hr => mul_nonneg (sphereArea_eq_toSphere hd).2.le (K.k_nonneg r hr)
  k_antitone := fun a ha b hb hab =>
    mul_le_mul_of_nonneg_left (K.k_antitone ha hb hab) (sphereArea_eq_toSphere hd).2.le
  integrable_near_zero := by
    have hA := (sphereArea_eq_toSphere hd).2
    have hfin : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1 * K.k r / r) ≠ ⊤ := by
      intro htop
      apply K.integrable
      rw [K.lintegral_radial hd, htop, ENNReal.mul_top (by simp [hA])]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := sphereArea d))
      hfin) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (lintegral_mono_set (Ioo_subset_Ioi_self)).trans' (setLIntegral_mono'
      measurableSet_Ioo fun r hr => ?_)
    rw [← ENNReal.ofReal_mul hA.le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [min_eq_left (by nlinarith [hr.1, hr.2])]
    field_simp
  integrable_at_top := by
    have hA := (sphereArea_eq_toSphere hd).2
    have hfin : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1 * K.k r / r) ≠ ⊤ := by
      intro htop
      apply K.integrable
      rw [K.lintegral_radial hd, htop, ENNReal.mul_top (by simp [hA])]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := sphereArea d))
      hfin) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (lintegral_mono_set (Ioi_subset_Ioi zero_le_one)).trans' (setLIntegral_mono'
      measurableSet_Ioi fun r hr => ?_)
    rw [← ENNReal.ofReal_mul hA.le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hr1 : (1 : ℝ) < r := hr
    rw [min_eq_right (by nlinarith)]
    ring

theorem toOriginDatum_exponent (hd : 1 ≤ d) (K : RadialProfile d) (ξ : Rd d) :
    (K.toOriginDatum hd).exponent ξ = K.exponent ξ := by
  have hA := (sphereArea_eq_toSphere hd).2
  unfold OriginDatum.exponent RadialProfile.exponent
  congr 1
  unfold OriginDatum.exponentL RadialProfile.exponentL OriginDatum.levyMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ ((K.toOriginDatum hd).measurable_levyDensity)
    (by fun_prop)]
  simp only [toOriginDatum, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), ← ENNReal.ofReal_mul (by
      have : 0 ≤ (K.toOriginDatum hd).k ‖x‖ := (K.toOriginDatum hd).k_nonneg _
        (norm_pos_iff.2 hx)
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      positivity), mul_comm]
    congr 1
    simp only [RadialProfile.m]
    field_simp

theorem toOriginDatum_profileAtOrigin (hd : 1 ≤ d) (K : RadialProfile d) {L : ℝ}
    (hL : Tendsto K.k (𝓝[>] 0) (𝓝 L)) :
    (K.toOriginDatum hd).profileAtOrigin = ENNReal.ofReal (sphereArea d * L) := by
  have h1 := OriginDatum.tendsto_profileAtOrigin (K.toOriginDatum hd)
  have h2 : Tendsto (fun r => ENNReal.ofReal ((K.toOriginDatum hd).k r)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sphereArea d * L))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hL.const_mul _)
  exact tendsto_nhds_unique h1 h2

end RadialProfile

end

end AffineHemigroup
