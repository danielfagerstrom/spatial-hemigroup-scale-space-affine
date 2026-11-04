/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginDecay
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# `prop:isotropic-exponent-profile`(2): the mean of `log|⟨e,η⟩|` over the sphere

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-exponent-profile`, clause (2),
the step of the proof headed *the mean of the logarithm over the sphere* (Q-0427).

`sphereLogMean d` is `λ_d = |S^{d-1}|⁻¹ ∫_{S^{d-1}} log|⟨e,η⟩| σ_{d-1}(dη)`, defined at the first
basis vector for `d ≥ 1` (and `0` at `d = 0`, where nothing is claimed). The surface measure is
Mathlib's `volume.toSphere`, of total mass `sphereArea d` (`sphereArea_eq_toSphere`); at `d = 1`
it is the measure on `{±1}` of total mass `2`.

* `sphere_log_mean`: for every unit vector `e`, `η ↦ log|⟨e,η⟩|` is integrable for the surface
  measure, its normalized integral is `sphereLogMean d` (so the mean does not depend on `e`), and
  `sphereLogMean d ≤ 0`;
* `sphereLogMean_one`: `λ_1 = 0`.

The route is the proof of record's. Polar coordinates on the closed unit ball
(`lintegral_ballLog`) turn the surface integral of `-log|⟨e,η⟩|` into `d` times the Lebesgue
integral of `-log(|⟨e,x⟩|/|x|)` over the ball; a reflection carrying `e` to another unit vector
preserves Lebesgue measure (`lintegral_ballLog_eq`); and at the first basis vector the integrand
is at most `-log|x_1|` on the ball, which lies in the cube `[-1,1]^d`, where it is dominated by
the product `∏_j (1 - log|x_j|)` of integrable functions of one variable
(`integrable_ball_neg_log`).

Lean core: Mathlib types only.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## One variable: `1 - log|t|` on `[-1,1]` -/

/-- `1 - log|t|` on `[-1,1]`, and `0` elsewhere. -/
noncomputable def cubeLog (t : ℝ) : ℝ := (Icc (-1 : ℝ) 1).indicator (fun t => 1 - Real.log |t|) t

theorem cubeLog_of_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : cubeLog t = 1 - Real.log |t| := by
  rw [cubeLog, indicator_of_mem ht]

theorem one_le_cubeLog {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 1 ≤ cubeLog t := by
  rw [cubeLog_of_mem ht]
  have := Real.log_nonpos (abs_nonneg t) (abs_le.2 ht)
  linarith

theorem cubeLog_nonneg (t : ℝ) : 0 ≤ cubeLog t := by
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · linarith [one_le_cubeLog ht]
  · rw [cubeLog, indicator_of_notMem ht]

theorem integrable_cubeLog : Integrable cubeLog := by
  have heq : cubeLog = (Icc (-1 : ℝ) 1).indicator fun t => 1 - Real.log |t| := by
    funext t; rfl
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  have hlog : IntegrableOn Real.log (Icc (-1 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      intervalIntegral.intervalIntegrable_log'
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-1 : ℝ) 1) :=
    integrableOn_const (by simp [Real.volume_Icc])
  refine (h1.sub hlog).congr (Filter.Eventually.of_forall fun t => ?_)
  simp [Real.log_abs]

/-! ## The ball -/

/-- `x ↦ -log|x_i|` is integrable on the closed unit ball of `ℝ^d`. -/
theorem integrable_ball_neg_log (i : Fin d) :
    Integrable (fun x : Rd d =>
      (closedBall (0 : Rd d) 1).indicator (fun x => -Real.log |x i|) x) := by
  have hP : Integrable (fun y : Fin d → ℝ => ∏ j, cubeLog (y j)) :=
    Integrable.fintype_prod (f := fun _ : Fin d => cubeLog) (μ := fun _ => volume)
      (fun _ => integrable_cubeLog)
  have hP' : Integrable (fun x : Rd d => ∏ j, cubeLog (x j)) :=
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)).2 hP
  have hcoord : Measurable fun x : Rd d => x i :=
    (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable
  have hmeas : Measurable fun x : Rd d =>
      (closedBall (0 : Rd d) 1).indicator (fun x => -Real.log |x i|) x :=
    (Real.measurable_log.comp hcoord.abs).neg.indicator measurableSet_closedBall
  refine hP'.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hprod_nn : 0 ≤ ∏ j, cubeLog (x j) := Finset.prod_nonneg fun j _ => cubeLog_nonneg _
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · rw [indicator_of_mem hx]
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hmem : ∀ j, x j ∈ Icc (-1 : ℝ) 1 := fun j =>
      abs_le.1 (le_trans (by simpa using PiLp.norm_apply_le x j) hx1)
    have hlog : Real.log |x i| ≤ 0 := Real.log_nonpos (abs_nonneg _) (abs_le.2 (hmem i))
    rw [Real.norm_of_nonneg (by linarith)]
    have h1 : ∏ j ∈ (Finset.univ.erase i), (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, cubeLog (x j) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun j _ => one_le_cubeLog (hmem j)
    rw [Finset.prod_const_one] at h1
    have h2 := Finset.mul_prod_erase Finset.univ (fun j => cubeLog (x j)) (Finset.mem_univ i)
    have h3 : cubeLog (x i) = 1 - Real.log |x i| := cubeLog_of_mem (hmem i)
    have h4 : 0 ≤ cubeLog (x i) := cubeLog_nonneg _
    nlinarith
  · rw [indicator_of_notMem hx, norm_zero]
    exact hprod_nn

/-- The function on the closed unit ball whose polar integral is the surface integral of
`-log|⟨e,η⟩|`: `x ↦ -log(|⟨e,x⟩|/|x|)` on the ball, `0` outside. -/
noncomputable def ballLog (e : Rd d) (x : Rd d) : ℝ≥0∞ :=
  (closedBall (0 : Rd d) 1).indicator
    (fun x => ENNReal.ofReal (-Real.log (|⟪e, x⟫| / ‖x‖))) x

theorem measurable_ballLog (e : Rd d) : Measurable (ballLog e) := by
  have h1 : Measurable fun x : Rd d => |⟪e, x⟫| / ‖x‖ :=
    (continuous_const.inner continuous_id).measurable.abs.div measurable_norm
  exact ((Real.measurable_log.comp h1).neg.ennreal_ofReal).indicator measurableSet_closedBall

/-- **Polar coordinates on the unit ball**:
`∫_B -log(|⟨e,x⟩|/|x|) dx = (1/d) ∫_{S^{d-1}} -log|⟨e,η⟩| σ_{d-1}(dη)`. -/
theorem lintegral_ballLog (hd : 1 ≤ d) (e : Rd d) :
    ∫⁻ x, ballLog e x = ENNReal.ofReal (1 / (d : ℝ)) *
      ∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪e, (η : Rd d)⟫|)
        ∂((volume : Measure (Rd d)).toSphere) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow : ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ (d - 1))
      = ENNReal.ofReal (1 / (d : ℝ)) := by
    have hint : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 1 :=
      (continuous_pow (d - 1)).intervalIntegrable 0 1
    rw [← ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
          pow_nonneg hr.1.le _)),
      ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) + 1 = d := by
      rw [Nat.cast_sub hd]; simp
    rw [this]
    simp
  rw [lintegral_polar hd (ballLog e) (measurable_ballLog e), ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine lintegral_congr fun η => ?_
  have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
  have hinner : ∀ r ∈ Ioi (0 : ℝ), ballLog e (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))
      = (Ioc (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal (-Real.log |⟪e, (η : Rd d)⟫|) *
          ENNReal.ofReal (r ^ (d - 1))) r := by
    intro r (hr : 0 < r)
    have hnorm : ‖r • (η : Rd d)‖ = r := by rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr.le]
    by_cases hr1 : r ≤ 1
    · have hmem : r • (η : Rd d) ∈ closedBall (0 : Rd d) 1 := by
        rw [mem_closedBall_zero_iff, hnorm]; exact hr1
      have hq : r * |⟪e, (η : Rd d)⟫| / r = |⟪e, (η : Rd d)⟫| := by field_simp
      rw [ballLog, indicator_of_mem hmem, indicator_of_mem (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩),
        hnorm, inner_smul_right, abs_mul, abs_of_pos hr, hq]
    · have hmem : r • (η : Rd d) ∉ closedBall (0 : Rd d) 1 := by
        rw [mem_closedBall_zero_iff, hnorm]; exact hr1
      rw [ballLog, indicator_of_notMem hmem, zero_mul,
        indicator_of_notMem (show r ∉ Ioc (0 : ℝ) 1 from fun h => hr1 h.2)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 from inter_eq_left.2 Ioc_subset_Ioi_self,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hpow, mul_comm]

/-- **Rotation invariance**: the integral of `ballLog e` is the same for two vectors of the same
norm, through the reflection that carries one to the other. -/
theorem lintegral_ballLog_eq {e e' : Rd d} (h : ‖e‖ = ‖e'‖) :
    ∫⁻ x, ballLog e x = ∫⁻ x, ballLog e' x := by
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (e - e'))ᗮ with hQ
  have hQe : Q e = e' := Submodule.reflection_sub h
  have hpt : ∀ x : Rd d, ballLog e x = ballLog e' (Q x) := by
    intro x
    have hinner : ⟪e', Q x⟫ = ⟪e, x⟫ := by rw [← hQe]; exact Q.inner_map_map e x
    have hnorm : ‖Q x‖ = ‖x‖ := Q.norm_map x
    by_cases hx : x ∈ closedBall (0 : Rd d) 1
    · have hx' : Q x ∈ closedBall (0 : Rd d) 1 := by
        rw [mem_closedBall_zero_iff, hnorm]; exact mem_closedBall_zero_iff.1 hx
      rw [ballLog, ballLog, indicator_of_mem hx, indicator_of_mem hx', hinner, hnorm]
    · have hx' : Q x ∉ closedBall (0 : Rd d) 1 := by
        rw [mem_closedBall_zero_iff, hnorm]; exact fun h => hx (mem_closedBall_zero_iff.2 h)
      rw [ballLog, ballLog, indicator_of_notMem hx, indicator_of_notMem hx']
  rw [lintegral_congr hpt]
  exact (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding (ballLog e')

/-- At a basis vector the integral of `ballLog` is finite. -/
theorem lintegral_ballLog_ebasis_lt_top (i : Fin d) : ∫⁻ x, ballLog (ebasis i) x < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (integrable_ball_neg_log i).lintegral_lt_top
  have hinner : ⟪ebasis i, x⟫ = x i := by simp [ebasis, EuclideanSpace.inner_single_left]
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · rw [ballLog, indicator_of_mem hx, indicator_of_mem hx, hinner]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    by_cases h0 : x i = 0
    · simp [h0]
    · have hxn : 0 < ‖x‖ := by
        rw [norm_pos_iff]
        intro hx0
        exact h0 (by simp [hx0])
      rw [Real.log_div (abs_ne_zero.2 h0) hxn.ne']
      have := Real.log_nonpos hxn.le hx1
      linarith
  · rw [ballLog, indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]

/-! ## The sphere -/

/-- `|⟨e,η⟩| ≤ 1` on the unit sphere, for a unit vector `e`. -/
theorem abs_inner_sphere_le_one {e : Rd d} (he : ‖e‖ = 1) (η : sphere (0 : Rd d) 1) :
    |⟪e, (η : Rd d)⟫| ≤ 1 := by
  have h := abs_real_inner_le_norm e (η : Rd d)
  rwa [he, norm_eq_of_mem_sphere η, mul_one] at h

/-- The surface integral of `-log|⟨e,η⟩|` is finite, and the same for every unit vector `e`. -/
theorem lintegral_sphere_neg_log (hd : 1 ≤ d) {e e' : Rd d} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) :
    (∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪e, (η : Rd d)⟫|)
        ∂((volume : Measure (Rd d)).toSphere)) < ⊤ ∧
      ∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪e, (η : Rd d)⟫|)
        ∂((volume : Measure (Rd d)).toSphere)
      = ∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪e', (η : Rd d)⟫|)
        ∂((volume : Measure (Rd d)).toSphere) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul : ENNReal.ofReal (d : ℝ) * ENNReal.ofReal (1 / (d : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul hd0.le, mul_one_div_cancel hd0.ne', ENNReal.ofReal_one]
  have hval : ∀ v : Rd d, ∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪v, (η : Rd d)⟫|)
      ∂((volume : Measure (Rd d)).toSphere) = ENNReal.ofReal (d : ℝ) * ∫⁻ x, ballLog v x := by
    intro v
    rw [lintegral_ballLog hd v, ← mul_assoc, hmul, one_mul]
  haveI : NeZero d := ⟨by omega⟩
  have he₁ : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  refine ⟨?_, ?_⟩
  · rw [hval e, lintegral_ballLog_eq (he.trans he₁.symm)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ballLog_ebasis_lt_top 0)
  · rw [hval e, hval e', lintegral_ballLog_eq (he.trans he'.symm)]

/-- **`λ_d`**, the mean of `log|⟨e,η⟩|` over the unit sphere of `ℝ^d`
(`prop:isotropic-exponent-profile`(2)), written at the first basis vector; `0` at `d = 0`. That it
is the mean for every unit vector is `sphere_log_mean`. -/
noncomputable def sphereLogMean (d : ℕ) : ℝ :=
  if h : 0 < d then (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
    Real.log |⟪(ebasis (⟨0, h⟩ : Fin d) : Rd d), (η : Rd d)⟫| ∂((volume : Measure (Rd d)).toSphere)
  else 0

/-- The surface integral of `log|⟨e,η⟩|` is minus the lower integral of `-log|⟨e,η⟩|`. -/
theorem integral_sphere_log (hd : 1 ≤ d) {e : Rd d} (he : ‖e‖ = 1) :
    Integrable (fun η : sphere (0 : Rd d) 1 => Real.log |⟪e, (η : Rd d)⟫|)
        ((volume : Measure (Rd d)).toSphere) ∧
      ∫ η : sphere (0 : Rd d) 1, Real.log |⟪e, (η : Rd d)⟫| ∂((volume : Measure (Rd d)).toSphere)
        = -(∫⁻ η : sphere (0 : Rd d) 1, ENNReal.ofReal (-Real.log |⟪e, (η : Rd d)⟫|)
          ∂((volume : Measure (Rd d)).toSphere)).toReal := by
  have hmeas : Measurable fun η : sphere (0 : Rd d) 1 => Real.log |⟪e, (η : Rd d)⟫| :=
    Real.measurable_log.comp
      ((continuous_const.inner continuous_subtype_val).measurable.abs)
  have hnp : ∀ η : sphere (0 : Rd d) 1, Real.log |⟪e, (η : Rd d)⟫| ≤ 0 := fun η =>
    Real.log_nonpos (abs_nonneg _) (abs_inner_sphere_le_one he η)
  have hfin := (lintegral_sphere_neg_log hd he he).1
  have hint : Integrable (fun η : sphere (0 : Rd d) 1 => Real.log |⟪e, (η : Rd d)⟫|)
      ((volume : Measure (Rd d)).toSphere) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun η => ?_)) hfin
    rw [← enorm_neg, Real.enorm_eq_ofReal (by linarith [hnp η])]
  refine ⟨hint, ?_⟩
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := (volume : Measure (Rd d)).toSphere)
    (f := fun η : sphere (0 : Rd d) 1 => -Real.log |⟪e, (η : Rd d)⟫|)
    (Filter.Eventually.of_forall fun η => by simpa using hnp η) hmeas.neg.aestronglyMeasurable
  rw [integral_neg] at h
  linarith

/-- **`prop:isotropic-exponent-profile`(2), the mean of the logarithm over the sphere**: for
`d ≥ 1` and every unit vector `e`, `η ↦ log|⟨e,η⟩|` is integrable on `S^{d-1}` for the surface
measure, `λ_d = |S^{d-1}|⁻¹ ∫ log|⟨e,η⟩| σ_{d-1}(dη)` whatever the unit vector `e`, and
`λ_d ≤ 0`. -/
theorem sphere_log_mean (hd : 1 ≤ d) {e : Rd d} (he : ‖e‖ = 1) :
    Integrable (fun η : sphere (0 : Rd d) 1 => Real.log |⟪e, (η : Rd d)⟫|)
        ((volume : Measure (Rd d)).toSphere) ∧
      sphereLogMean d = (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
        Real.log |⟪e, (η : Rd d)⟫| ∂((volume : Measure (Rd d)).toSphere) ∧
      sphereLogMean d ≤ 0 := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hpos : 0 < d := hd
  have he₁ : ‖(ebasis (⟨0, hpos⟩ : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have heq : sphereLogMean d = (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
      Real.log |⟪e, (η : Rd d)⟫| ∂((volume : Measure (Rd d)).toSphere) := by
    rw [sphereLogMean, dif_pos hpos, (integral_sphere_log hd he₁).2, (integral_sphere_log hd he).2,
      (lintegral_sphere_neg_log hd he₁ he).2]
  refine ⟨(integral_sphere_log hd he).1, heq, ?_⟩
  rw [heq]
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hA.le) (integral_nonpos fun η => ?_)
  exact Real.log_nonpos (abs_nonneg _) (abs_inner_sphere_le_one he η)

/-- **`prop:isotropic-exponent-profile`(2)**: `λ_1 = 0`, the sphere of the line being `{±1}`. -/
theorem sphereLogMean_one : sphereLogMean 1 = 0 := by
  have hpos : 0 < 1 := one_pos
  rw [sphereLogMean, dif_pos hpos]
  have hz : ∀ η : sphere (0 : Rd 1) 1,
      Real.log |⟪(ebasis (⟨0, hpos⟩ : Fin 1) : Rd 1), (η : Rd 1)⟫| = 0 := by
    intro η
    have hη : ‖(η : Rd 1)‖ = 1 := norm_eq_of_mem_sphere η
    have hinner : ⟪(ebasis (⟨0, hpos⟩ : Fin 1) : Rd 1), (η : Rd 1)⟫ = (η : Rd 1) 0 := by
      simp [ebasis, EuclideanSpace.inner_single_left]
    have hnorm : ‖(η : Rd 1)‖ = |(η : Rd 1) 0| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq (abs_nonneg _)]
    rw [hinner, ← hnorm, hη, Real.log_one]
  simp only [hz, integral_zero, mul_zero]

end AffineHemigroup
