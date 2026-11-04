/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginDecay
import AffineHemigroup.PositiveTransform
import AffineHemigroup.Interfaces
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# `thm:origin-boundedness-d`(2), (4), (5): above, at and below the threshold

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `thm:origin-boundedness-d`, clauses (2), (4) and
(5). Wave 2, group A (Q-0281); clause (2) after ledger A1 was restated at its page's letter, its
density nonnegative (the author's decision of 2026-10-05).

Clause (2) is ledger A1 at `n = N`, whose hypothesis `∫ |μ̂(ξ)| |ξ|^N dξ < ∞` is
`lintegral_charFun_pow_ne_top` (clause (1)'s decay at a finite `β ∈ (d + N, c)`). Its "in
particular": at `N = 0` the density is continuous and tends to `0` at infinity, so bounded; at
`c = ∞` the densities A1 gives for each `N` are continuous, nonnegative and equal almost everywhere,
hence equal, so one of them is of class `C^N` for every `N`.

Clause (4) follows the blueprint: the transform `e^{-F_d}` of a law of the datum is real and
positive, so `lem:positive-transform-origin` applies; the lower bound of
`lem:isotropic-exponent-log`(1) and polar coordinates (`lintegral_radial`) make `∫ μ̂ = ∞` when
`c ≤ d`, which excludes every bound `μ(B) ≤ M|B|` near the origin and with it every representative
of a density bounded there. The rate reads the heat-kernel identity of
`lem:positive-transform-origin`(1): from below on the shell `t^{-1/2} ≤ |ξ| ≤ 2t^{-1/2}` (`c < d`)
or on `1 ≤ |ξ| ≤ t^{-1/2}` (`c = d`), from above through `lem:origin-decay-exponent` and the Gamma
integral `∫₀^∞ r^q e^{-br²} dr` (Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`). Clause (5) joins
ledger A1 at `n = 0` (`density_of_integrable_charFun`), applied through clause (1)'s decay, with
clause (4).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The law's transform, and radial integrals -/

theorem IsLawOf.charFun_re {D : OriginDatum d} {μ : Measure (Rd d)} (hμ : IsLawOf D μ)
    (ξ : Rd d) : (charFun μ ξ).re = Real.exp (-D.exponent ξ) := by
  rw [hμ.2 ξ, Complex.ofReal_re]

theorem IsLawOf.charFun_im {D : OriginDatum d} {μ : Measure (Rd d)} (hμ : IsLawOf D μ)
    (ξ : Rd d) : (charFun μ ξ).im = 0 := by
  rw [hμ.2 ξ, Complex.ofReal_im]

theorem IsLawOf.charFun_re_nonneg {D : OriginDatum d} {μ : Measure (Rd d)} (hμ : IsLawOf D μ)
    (ξ : Rd d) : 0 ≤ (charFun μ ξ).re := by
  rw [hμ.charFun_re]; exact (Real.exp_pos _).le

/-- **Polar coordinates for a radial function**: `∫ f(|x|) dx = |S^{d-1}| ∫_0^∞ f(r) r^{d-1} dr`
for measurable `f ≥ 0` on `[0,∞)`. Mathlib types only, in this paper's `sphereArea`. -/
theorem lintegral_radial (hd : 1 ≤ d) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x : Rd d, f ‖x‖ = ENNReal.ofReal (sphereArea d) *
      ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) := by
  rw [lintegral_polar hd (fun x => f ‖x‖) (hf.comp continuous_norm.measurable)]
  have : ∀ η : sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
      f ‖r • (η : Rd d)‖ * ENNReal.ofReal (r ^ (d - 1)))
      = ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) := by
    intro η
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr.le]
  simp_rw [this]
  rw [lintegral_const, (sphereArea_eq_toSphere hd).1, mul_comm]

/-- `r^{d-1}` as a real power, for `r > 0` and `d ≥ 1`. -/
theorem pow_pred_eq_rpow (hd : 1 ≤ d) {r : ℝ} (_hr : 0 < r) :
    r ^ (d - 1) = r ^ ((d : ℝ) - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one]

/-- `∫₁^∞ r^a dr = ∞` for `a ≥ -1`. Mathlib types only. -/
theorem lintegral_Ioi_one_rpow_eq_top {a : ℝ} (ha : -1 ≤ a) :
    ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ a) = ⊤ := by
  by_contra hne
  have hint : IntegrableOn (fun r : ℝ => r ^ a) (Ioi 1) := by
    refine ⟨(measurable_id.pow_const a).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr hne)
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith) a)]
  rw [integrableOn_Ioi_rpow_iff zero_lt_one] at hint
  linarith

/-! ## `thm:origin-boundedness-d`(4) -/

/-- For `c ≤ d` (finite), `∫ e^{-F_d} = ∞`: the lower bound of `lem:isotropic-exponent-log`(1) in
polar coordinates. -/
theorem lintegral_charFun_eq_top (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (μ : Measure (Rd d)) (hμ : IsLawOf D μ) (hcd : D.profileAtOrigin ≤ d) :
    ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re = ⊤ := by
  have hctop : D.profileAtOrigin ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcd
  set c := D.profileAtOrigin.toReal with hcdef
  have hc_le : c ≤ d := by
    rw [hcdef]
    have := ENNReal.toReal_mono (by simp) hcd
    simpa using this
  set C₀ := Real.exp (-(13 / 4 * c) - 2 * D.tailConst) with hC₀
  have hC₀ : 0 < C₀ := Real.exp_pos _
  set f : ℝ → ℝ≥0∞ := (Ici (1 : ℝ)).indicator fun r => ENNReal.ofReal (C₀ * r ^ (-c)) with hf
  have hfm : Measurable f :=
    ((measurable_const.mul (measurable_id.pow_const _)).ennreal_ofReal).indicator measurableSet_Ici
  have hle : ∀ ξ : Rd d, f ‖ξ‖ ≤ ENNReal.ofReal (charFun μ ξ).re := by
    intro ξ
    by_cases hξ : ‖ξ‖ ∈ Ici (1 : ℝ)
    · rw [hf, indicator_of_mem hξ, hμ.charFun_re]
      exact ENNReal.ofReal_le_ofReal
        ((isotropic_exponent_log_bound hd D ha hctop ξ hξ).2)
    · rw [hf, indicator_of_notMem hξ]; exact zero_le
  have hA := (sphereArea_eq_toSphere hd).2
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (sphereArea d) * (ENNReal.ofReal C₀ *
        ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ ((d : ℝ) - 1 - c))) := by
        rw [lintegral_Ioi_one_rpow_eq_top (by linarith), ENNReal.mul_top (by simp [hC₀]),
          ENNReal.mul_top (by simp [hA])]
    _ ≤ ENNReal.ofReal (sphereArea d) *
        ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) := by
        gcongr
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine le_trans ?_ (lintegral_mono_set (Ioi_subset_Ioi zero_le_one))
        refine setLIntegral_mono' measurableSet_Ioi fun r (hr : 1 < r) => ?_
        have hr0 : 0 < r := lt_trans zero_lt_one hr
        rw [hf, indicator_of_mem (show r ∈ Ici (1 : ℝ) from hr.le), ← ENNReal.ofReal_mul hC₀.le,
          ← ENNReal.ofReal_mul (by positivity), pow_pred_eq_rpow hd hr0]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [mul_assoc, ← Real.rpow_add hr0]
        ring_nf
    _ = ∫⁻ ξ : Rd d, f ‖ξ‖ := (lintegral_radial hd f hfm).symm
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re := lintegral_mono hle

/-- **`thm:origin-boundedness-d`(4)**: if `c ≤ d` then `∫ μ̂ = ∞`, no bound `μ(B) ≤ M|B|` holds on
the Borel subsets of a ball about the origin, and no representative of a density of `μ` is bounded
near the origin. -/
theorem origin_unbounded (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (_hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re = ⊤ ∧
      (¬ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ≥0, ∀ B : Set (Rd d), MeasurableSet B →
        B ⊆ Metric.ball 0 δ → μ B ≤ M * volume B) ∧
      ∀ q : Rd d → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
        ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ x : Rd d, 0 < ‖x‖ ∧ ‖x‖ < δ ∧ M < q x := by
  haveI := hμ.1
  have htop := lintegral_charFun_eq_top hd D ha μ hμ hcd
  have hno : ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ≥0, ∀ B : Set (Rd d), MeasurableSet B →
      B ⊆ Metric.ball 0 δ → μ B ≤ M * volume B := by
    rintro ⟨δ, hδ, M, hM⟩
    have h := positive_transform_bound hd μ hμ.charFun_im hμ.charFun_re_nonneg hδ M hM
    rw [htop, top_le_iff] at h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top h
  refine ⟨htop, hno, fun q hq δ hδ M => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hno ⟨δ, hδ, Real.toNNReal M, density_bound_ball hd μ hδ _ q hq fun x hx0 hxδ => ?_⟩
  exact (hcon x hx0 hxδ).trans (Real.le_coe_toNNReal M)

/-! ## `thm:origin-boundedness-d`(5) -/

/-- Above the threshold, `∫ |μ̂(ξ)| |ξ|^N dξ < ∞` when `c > d + N`: the decay of
`lem:origin-decay-exponent` at a finite `β ∈ (d + N, c)` against `(1 + |ξ|)^{N-β}`, integrable since
`β - N > d`. The hypothesis of ledger A1 at `n = N`. -/
theorem lintegral_charFun_pow_ne_top (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) (N : ℕ)
    (hN : ((d + N : ℕ) : ℝ≥0∞) < D.profileAtOrigin) :
    ∫⁻ z, ENNReal.ofReal (‖charFun μ z‖ * ‖z‖ ^ N) ≠ ⊤ := by
  obtain ⟨β, -, hβ1, hβ2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hN
  have hβ : ((d + N : ℕ) : ℝ) < β := by
    have h := hβ1
    rw [← ENNReal.ofReal_natCast] at h
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp h).1
  obtain ⟨C, hC⟩ := origin_decay_exponent hd D ha hc μ hμ β hβ2
  have hint : Integrable (fun z : Rd d => (1 + ‖z‖) ^ (-(β - N))) :=
    integrable_one_add_norm (by rw [finrank_Rd]; push_cast at hβ; linarith)
  have hint2 := (hint.const_mul (max C 0))
  refine ne_top_of_le_ne_top (hint2.lintegral_lt_top).ne ?_
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  have h1 : 0 < 1 + ‖z‖ := by positivity
  have hz : ‖z‖ ^ N ≤ (1 + ‖z‖) ^ (N : ℝ) := by
    rw [Real.rpow_natCast]; exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) N
  calc ‖charFun μ z‖ * ‖z‖ ^ N ≤ (max C 0 * (1 + ‖z‖) ^ (-β)) * (1 + ‖z‖) ^ (N : ℝ) := by
        refine mul_le_mul ((hC z).trans ?_) hz (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max C 0 * (1 + ‖z‖) ^ (-(β - N)) := by
        rw [mul_assoc, ← Real.rpow_add h1]; ring_nf

/-- **`thm:origin-boundedness-d`(5)**, the dichotomy: `μ` has a density bounded near the origin
exactly when `c > d`. Spends ledger A1 at `n = 0`. -/
theorem origin_dichotomy (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    (∃ q : Rd d → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ x : Rd d, ‖x‖ < δ → q x ≤ M) ↔
      (d : ℝ≥0∞) < D.profileAtOrigin := by
  haveI := hμ.1
  constructor
  · rintro ⟨q, hq, δ, hδ, M, hM⟩
    by_contra hcd
    push Not at hcd
    obtain ⟨x, -, hxδ, hMx⟩ := (origin_unbounded hd D ha hc μ hμ hcd).2.2 q hq δ hδ M
    exact absurd (hM x hxδ) (not_le.mpr hMx)
  · intro hcd
    have hfin := lintegral_charFun_pow_ne_top hd D ha hc μ hμ 0 (by simpa using hcd)
    obtain ⟨g, -, hg, hμg, -⟩ := density_of_integrable_charFun μ 0 hfin
    have hgc : Continuous g := hg.continuous
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Rd d) 1).bddAbove_image hgc.continuousOn
    refine ⟨g, hμg, 1, one_pos, M, fun x hx => hM ⟨x, ?_, rfl⟩⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hx.le

/-! ## `thm:origin-boundedness-d`(4), the rate -/

/-- The heat-kernel identity of `lem:positive-transform-origin`(1) for a law of the datum, in
`ℝ≥0∞`: `∫ g_t dμ = (2π)^{-d} ∫ e^{-F_d(ξ)} e^{-t|ξ|²/2} dξ`. -/
theorem IsLawOf.ofReal_integral_heatKernel (hd : 1 ≤ d) {D : OriginDatum d} {μ : Measure (Rd d)}
    (hμ : IsLawOf D μ) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (∫ x, heatKernel d t x ∂μ) = ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
      ∫⁻ ξ, ENNReal.ofReal ((charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) := by
  haveI := hμ.1
  have hpi : 0 < 2 * Real.pi := by positivity
  have hint : Integrable (fun ξ : Rd d => (charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) := by
    refine Integrable.mono' (integrable_rexp_neg_mul_sq_norm_Rd d (half_pos ht))
      (((Complex.continuous_re.comp continuous_charFun).mul (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hμ.charFun_re_nonneg ξ) (Real.exp_pos _).le),
      show -(t * ‖ξ‖ ^ 2) / 2 = -(t / 2) * ‖ξ‖ ^ 2 by ring]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      ((Complex.re_le_norm _).trans (norm_charFun_le_one ξ))
  rw [(positive_transform_heat hd μ hμ.charFun_im hμ.charFun_re_nonneg).1 t ht,
    ENNReal.ofReal_mul (Real.rpow_pos_of_pos hpi _).le,
    ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ξ => mul_nonneg (hμ.charFun_re_nonneg ξ) (Real.exp_pos _).le)]

theorem integral_heatKernel_nonneg {μ : Measure (Rd d)} {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ x, heatKernel d t x ∂μ :=
  integral_nonneg (heatKernel_nonneg ht)

/-- `c` is finite and positive when `0 < c ≤ d`. -/
theorem OriginDatum.profileAtOrigin_toReal_pos (D : OriginDatum d)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin ≤ d) :
    D.profileAtOrigin ≠ ⊤ ∧ 0 < D.profileAtOrigin.toReal ∧ D.profileAtOrigin.toReal ≤ d := by
  have hctop : D.profileAtOrigin ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcd
  refine ⟨hctop, ENNReal.toReal_pos hc.ne' hctop, ?_⟩
  have := ENNReal.toReal_mono (by simp) hcd
  simpa using this

/-- From below, `c < d`: on the shell `u ≤ |ξ| ≤ 2u`, `u = t^{-1/2}`, the bound
`e^{-F_d} ≥ C₀|ξ|^{-c}` and `e^{-t|ξ|²/2} ≥ e^{-2}` give `∫ g_t dμ ≥ C t^{-(d-c)/2}`. -/
theorem heat_lower_lt (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
      C * t ^ (-((d : ℝ) - D.profileAtOrigin.toReal) / 2) ≤ ∫ x, heatKernel d t x ∂μ := by
  obtain ⟨hctop, hc0, hcle⟩ := D.profileAtOrigin_toReal_pos hc hcd
  set c := D.profileAtOrigin.toReal with hcdef
  set a := (d : ℝ) - 1 - c with hadef
  set m := min 1 ((2 : ℝ) ^ a) with hm
  have hm0 : 0 < m := lt_min one_pos (Real.rpow_pos_of_pos two_pos a)
  set C₀ := Real.exp (-(13 / 4 * c) - 2 * D.tailConst) with hC₀def
  have hC₀ : 0 < C₀ := Real.exp_pos _
  have hA := (sphereArea_eq_toSphere hd).2
  have hpi : 0 < 2 * Real.pi := by positivity
  set K := sphereArea d * C₀ * m * Real.exp (-2) with hK
  refine ⟨(2 * Real.pi) ^ (-(d : ℝ)) * K, by positivity, fun t ht => ?_⟩
  obtain ⟨ht0, ht1⟩ := ht
  set u := t ^ (-(1 : ℝ) / 2) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 _
  have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
  have htu : t * u ^ 2 = 1 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      show (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ ht0.ne']
  have hpow : u ^ (a + 1) = t ^ (-((d : ℝ) - c) / 2) := by
    rw [hu, ← Real.rpow_mul ht0.le, hadef]; ring_nf
  -- the radial lower function
  set f : ℝ → ℝ≥0∞ := (Icc u (2 * u)).indicator
    (fun r => ENNReal.ofReal (C₀ * r ^ (-c) * Real.exp (-(t * r ^ 2) / 2))) with hf
  have hfm : Measurable f := by
    refine Measurable.indicator ?_ measurableSet_Icc
    exact ((measurable_const.mul (measurable_id.pow_const _)).mul (by fun_prop)).ennreal_ofReal
  have hle : ∀ ξ : Rd d, f ‖ξ‖ ≤ ENNReal.ofReal ((charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) := by
    intro ξ
    by_cases hξ : ‖ξ‖ ∈ Icc u (2 * u)
    · rw [hf, indicator_of_mem hξ]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      rw [hμ.charFun_re]
      exact (isotropic_exponent_log_bound hd D ha hctop ξ (le_trans hu1 hξ.1)).2
    · rw [hf, indicator_of_notMem hξ]; exact zero_le
  have hshell : ENNReal.ofReal (K * u ^ (a + 1)) ≤
      ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) := by
    have hbound : ∀ r ∈ Icc u (2 * u), ENNReal.ofReal (C₀ * m * Real.exp (-2) * u ^ a) ≤
        f r * ENNReal.ofReal (r ^ (d - 1)) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hu0 hr.1
      rw [hf, indicator_of_mem hr, ← ENNReal.ofReal_mul (by positivity),
        pow_pred_eq_rpow hd hr0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hra : r ^ (-c) * r ^ ((d : ℝ) - 1) = r ^ a := by
        rw [← Real.rpow_add hr0, hadef]; ring_nf
      have hexp : Real.exp (-2) ≤ Real.exp (-(t * r ^ 2) / 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h2 : t * r ^ 2 ≤ t * (2 * u) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr.2 2) ht0.le
        have h3 : t * (2 * u) ^ 2 = 4 := by rw [mul_pow, ← mul_assoc, mul_comm t, mul_assoc, htu]; norm_num
        linarith
      have hrm : m * u ^ a ≤ r ^ a := by
        have hq : r = u * (r / u) := by field_simp
        have hq1 : 1 ≤ r / u := by rw [le_div_iff₀ hu0]; linarith [hr.1]
        have hq2 : r / u ≤ 2 := by rw [div_le_iff₀ hu0]; linarith [hr.2]
        rw [hq, Real.mul_rpow hu0.le (by positivity), mul_comm (u ^ a)]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu0.le _)
        rcases le_or_gt 0 a with ha0 | ha0
        · exact (min_le_left _ _).trans (Real.one_le_rpow hq1 ha0)
        · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (by positivity) hq2 ha0.le)
      calc C₀ * m * Real.exp (-2) * u ^ a = C₀ * (m * u ^ a) * Real.exp (-2) := by ring
        _ ≤ C₀ * r ^ a * Real.exp (-(t * r ^ 2) / 2) := by gcongr
        _ = C₀ * r ^ (-c) * Real.exp (-(t * r ^ 2) / 2) * r ^ ((d : ℝ) - 1) := by
            rw [← hra]; ring
    calc ENNReal.ofReal (K * u ^ (a + 1))
        = ENNReal.ofReal (sphereArea d) * (ENNReal.ofReal (C₀ * m * Real.exp (-2) * u ^ a) *
            volume (Icc u (2 * u))) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hA.le, Real.rpow_add hu0, Real.rpow_one, hK]
          congr 1; ring
      _ = ENNReal.ofReal (sphereArea d) *
          ∫⁻ _r in Icc u (2 * u), ENNReal.ofReal (C₀ * m * Real.exp (-2) * u ^ a) := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (sphereArea d) *
          ∫⁻ r in Icc u (2 * u), f r * ENNReal.ofReal (r ^ (d - 1)) := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Icc hbound) _
      _ ≤ ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) :=
          mul_le_mul_right (lintegral_mono_set
            (fun r (hr : r ∈ Icc u (2 * u)) => (lt_of_lt_of_le hu0 hr.1 : r ∈ Ioi 0))) _
  have hfinal : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ)) * K * t ^ (-((d : ℝ) - c) / 2)) ≤
      ENNReal.ofReal (∫ x, heatKernel d t x ∂μ) := by
    rw [hμ.ofReal_integral_heatKernel hd ht0, mul_assoc,
      ENNReal.ofReal_mul (Real.rpow_pos_of_pos hpi _).le, ← hpow]
    gcongr
    calc ENNReal.ofReal (K * u ^ (a + 1))
        ≤ ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) :=
          hshell
      _ = ∫⁻ ξ : Rd d, f ‖ξ‖ := (lintegral_radial hd f hfm).symm
      _ ≤ _ := lintegral_mono hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_heatKernel_nonneg ht0)).mp hfinal

/-- From below, `c = d`: on `1 ≤ |ξ| ≤ t^{-1/2}`, `e^{-F_d} ≥ C₀|ξ|^{-d}` and
`e^{-t|ξ|²/2} ≥ e^{-1/2}` give `∫ g_t dμ ≥ C log(1/t)`. -/
theorem heat_lower_eq (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin = d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, C * Real.log (1 / t) ≤ ∫ x, heatKernel d t x ∂μ := by
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  have hcd' : D.profileAtOrigin.toReal = d := by rw [hcd]; simp
  set C₀ := Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) with hC₀def
  have hC₀ : 0 < C₀ := Real.exp_pos _
  have hA := (sphereArea_eq_toSphere hd).2
  have hpi : 0 < 2 * Real.pi := by positivity
  set K := sphereArea d * C₀ * Real.exp (-(1 / 2)) / 2 with hK
  refine ⟨(2 * Real.pi) ^ (-(d : ℝ)) * K, by positivity, fun t ht => ?_⟩
  obtain ⟨ht0, ht1⟩ := ht
  set u := t ^ (-(1 : ℝ) / 2) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 _
  have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
  have htu : t * u ^ 2 = 1 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      show (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ ht0.ne']
  have hlogu : Real.log u = Real.log (1 / t) / 2 := by
    rw [hu, Real.log_rpow ht0, one_div, Real.log_inv]; ring
  set f : ℝ → ℝ≥0∞ := (Icc 1 u).indicator
    (fun r => ENNReal.ofReal (C₀ * r ^ (-(d : ℝ)) * Real.exp (-(t * r ^ 2) / 2))) with hf
  have hfm : Measurable f := by
    refine Measurable.indicator ?_ measurableSet_Icc
    exact ((measurable_const.mul (measurable_id.pow_const _)).mul (by fun_prop)).ennreal_ofReal
  have hle : ∀ ξ : Rd d, f ‖ξ‖ ≤ ENNReal.ofReal ((charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) := by
    intro ξ
    by_cases hξ : ‖ξ‖ ∈ Icc 1 u
    · rw [hf, indicator_of_mem hξ]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      rw [hμ.charFun_re]
      have h := (isotropic_exponent_log_bound hd D ha hctop ξ hξ.1).2
      rwa [hcd'] at h
    · rw [hf, indicator_of_notMem hξ]; exact zero_le
  have hint1 : ∫⁻ r in Icc 1 u, ENNReal.ofReal (r⁻¹) = ENNReal.ofReal (Real.log u) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu1,
        integral_inv_of_pos one_pos hu0, div_one]
    · refine (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun r hr => ?_))
      exact ne_of_gt (lt_of_lt_of_le one_pos hr.1)
    · exact (ae_restrict_iff' measurableSet_Icc).mpr
        (.of_forall fun r hr => inv_nonneg.mpr (le_trans zero_le_one hr.1))
  have hshell : ENNReal.ofReal (K * Real.log (1 / t)) ≤
      ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) := by
    have hbound : ∀ r ∈ Icc (1 : ℝ) u, ENNReal.ofReal (C₀ * Real.exp (-(1 / 2))) *
        ENNReal.ofReal (r⁻¹) ≤ f r * ENNReal.ofReal (r ^ (d - 1)) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le one_pos hr.1
      rw [hf, indicator_of_mem hr, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), pow_pred_eq_rpow hd hr0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hra : r ^ (-(d : ℝ)) * r ^ ((d : ℝ) - 1) = r⁻¹ := by
        rw [← Real.rpow_add hr0, ← Real.rpow_neg_one]; ring_nf
      have hexp : Real.exp (-(1 / 2)) ≤ Real.exp (-(t * r ^ 2) / 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h2 : t * r ^ 2 ≤ t * u ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr.2 2) ht0.le
        rw [htu] at h2
        linarith
      calc C₀ * Real.exp (-(1 / 2)) * r⁻¹ = C₀ * r⁻¹ * Real.exp (-(1 / 2)) := by ring
        _ ≤ C₀ * r⁻¹ * Real.exp (-(t * r ^ 2) / 2) := by gcongr
        _ = C₀ * r ^ (-(d : ℝ)) * Real.exp (-(t * r ^ 2) / 2) * r ^ ((d : ℝ) - 1) := by
            rw [← hra]; ring
    calc ENNReal.ofReal (K * Real.log (1 / t))
        = ENNReal.ofReal (sphereArea d) * (ENNReal.ofReal (C₀ * Real.exp (-(1 / 2))) *
            ∫⁻ r in Icc 1 u, ENNReal.ofReal (r⁻¹)) := by
          rw [hint1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA.le, hlogu, hK]
          congr 1; ring
      _ ≤ ENNReal.ofReal (sphereArea d) * ∫⁻ r in Icc 1 u, f r * ENNReal.ofReal (r ^ (d - 1)) := by
          refine mul_le_mul_right ?_ _
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact setLIntegral_mono' measurableSet_Icc hbound
      _ ≤ ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) :=
          mul_le_mul_right (lintegral_mono_set
            (fun r (hr : r ∈ Icc 1 u) => (lt_of_lt_of_le one_pos hr.1 : r ∈ Ioi 0))) _
  have hfinal : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ)) * K * Real.log (1 / t)) ≤
      ENNReal.ofReal (∫ x, heatKernel d t x ∂μ) := by
    rw [hμ.ofReal_integral_heatKernel hd ht0, mul_assoc,
      ENNReal.ofReal_mul (Real.rpow_pos_of_pos hpi _).le]
    gcongr
    calc ENNReal.ofReal (K * Real.log (1 / t))
        ≤ ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) :=
          hshell
      _ = ∫⁻ ξ : Rd d, f ‖ξ‖ := (lintegral_radial hd f hfm).symm
      _ ≤ _ := lintegral_mono hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_heatKernel_nonneg ht0)).mp hfinal

/-- From above: for `0 < β < c`, the decay of `lem:origin-decay-exponent`, `(1+|ξ|)^{-β} ≤ |ξ|^{-β}`
and the Gamma integral `∫₀^∞ r^{d-1-β} e^{-tr²/2} dr = (t/2)^{-(d-β)/2} Γ((d-β)/2)/2` give
`∫ g_t dμ ≤ C' t^{-(d-β)/2}` for every `t > 0`. -/
theorem heat_upper (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) {β : ℝ} (hβ0 : 0 < β)
    (hβc : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 0 < t →
      ∫ x, heatKernel d t x ∂μ ≤ C' * t ^ (-((d : ℝ) - β) / 2) := by
  obtain ⟨hctop, hc0, hcle⟩ := D.profileAtOrigin_toReal_pos hc hcd
  have hβc' : β < D.profileAtOrigin.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hβ0.le hctop).mp hβc
  have hβd : β < d := lt_of_lt_of_le hβc' hcle
  obtain ⟨C, hC⟩ := origin_decay_exponent hd D ha hc μ hμ β hβc
  set C1 := max C 1 with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set q := (d : ℝ) - 1 - β with hq
  have hq1 : -1 < q := by rw [hq]; linarith
  have hA := (sphereArea_eq_toSphere hd).2
  have hpi : 0 < 2 * Real.pi := by positivity
  set Γq := Real.Gamma ((q + 1) / 2) with hΓq
  have hΓpos : 0 < Γq := Real.Gamma_pos_of_pos (by linarith)
  set C' := (2 * Real.pi) ^ (-(d : ℝ)) * sphereArea d * C1 *
    ((1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Γq) with hC'
  refine ⟨C', by positivity, fun t ht => ?_⟩
  -- the radial upper function
  set f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (C1 * r ^ (-β) * Real.exp (-(t * r ^ 2) / 2)) with hf
  have hfm : Measurable f :=
    ((measurable_const.mul (measurable_id.pow_const _)).mul (by fun_prop)).ennreal_ofReal
  have hle : ∀ᵐ ξ ∂(volume : Measure (Rd d)),
      ENNReal.ofReal ((charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) ≤ f ‖ξ‖ := by
    haveI : Nontrivial (Rd d) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      infer_instance
    have h0 : ∀ᵐ ξ ∂(volume : Measure (Rd d)), ξ ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [h0] with ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    calc (charFun μ ξ).re ≤ ‖charFun μ ξ‖ := Complex.re_le_norm _
      _ ≤ C * (1 + ‖ξ‖) ^ (-β) := hC ξ
      _ ≤ C1 * (1 + ‖ξ‖) ^ (-β) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C1 * ‖ξ‖ ^ (-β) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn (by linarith) (by linarith))
            hC1pos.le
  have hint : IntegrableOn (fun r : ℝ => r ^ q * Real.exp (-(t / 2) * r ^ (2 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hq1 one_le_two (half_pos ht)
  have hval := integral_rpow_mul_exp_neg_mul_rpow two_pos hq1 (half_pos ht)
  have hradial : ∫⁻ ξ : Rd d, f ‖ξ‖ = ENNReal.ofReal (sphereArea d) *
      ENNReal.ofReal (C1 * ∫ r in Ioi (0 : ℝ), r ^ q * Real.exp (-(t / 2) * r ^ (2 : ℝ))) := by
    rw [lintegral_radial hd f hfm, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal (hint.const_mul C1)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r (hr : 0 < r) => by positivity))]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, ← ENNReal.ofReal_mul (by positivity), pow_pred_eq_rpow hd hr]
    congr 1
    have h1 : r ^ (-β) * r ^ ((d : ℝ) - 1) = r ^ q := by
      rw [← Real.rpow_add hr, hq]; ring_nf
    have h2 : Real.exp (-(t * r ^ 2) / 2) = Real.exp (-(t / 2) * r ^ (2 : ℝ)) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring_nf
    rw [← h1, h2]; ring
  have hfinal : ENNReal.ofReal (∫ x, heatKernel d t x ∂μ) ≤
      ENNReal.ofReal (C' * t ^ (-((d : ℝ) - β) / 2)) := by
    rw [hμ.ofReal_integral_heatKernel hd ht]
    calc ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
          ∫⁻ ξ, ENNReal.ofReal ((charFun μ ξ).re * Real.exp (-(t * ‖ξ‖ ^ 2) / 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ : Rd d, f ‖ξ‖ :=
          mul_le_mul_right (lintegral_mono_ae hle) _
      _ = ENNReal.ofReal (C' * t ^ (-((d : ℝ) - β) / 2)) := by
          rw [hradial, hval, ← ENNReal.ofReal_mul hA.le,
            ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hpi _).le]
          congr 1
          have ht2 : (t / 2) ^ (-(q + 1) / 2) = t ^ (-((d : ℝ) - β) / 2) * (1 / 2 : ℝ) ^ (-(q + 1) / 2) := by
            rw [div_eq_mul_one_div t 2, Real.mul_rpow ht.le (by norm_num), hq]
            ring_nf
          rw [hC', ht2]
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfinal

/-- `∫ g_t dμ > 0` for a probability measure and `t > 0`. -/
theorem integral_heatKernel_pos (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {t : ℝ}
    (ht : 0 < t) : 0 < ∫ x, heatKernel d t x ∂μ := by
  have hint : Integrable (heatKernel d t) μ :=
    Integrable.of_bound (continuous_heatKernel).aestronglyMeasurable _
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht x)]
        exact heatKernel_le ht x)
  rw [integral_pos_iff_support_of_nonneg (heatKernel_nonneg ht) hint]
  have hsupp : Function.support (heatKernel d t) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    unfold heatKernel
    have : 0 < 2 * Real.pi * t := by positivity
    positivity
  rw [hsupp, measure_univ]
  exact one_pos

/-- **`thm:origin-boundedness-d`(4)**, quantitatively: `∫ g_t dμ ≥ C t^{-(d-c)/2}` (`c < d`) or
`≥ C log(1/t)` (`c = d`) on `0 < t ≤ 1`; `∫ g_t dμ ≤ C'_β t^{-(d-β)/2}` for `0 < β < c`; and
`log ∫ g_t dμ / log(1/t) → (d - c)/2` as `t ↓ 0`. -/
theorem origin_unbounded_rate (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    (D.profileAtOrigin < d → ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
        C * t ^ (-((d : ℝ) - D.profileAtOrigin.toReal) / 2) ≤ ∫ x, heatKernel d t x ∂μ) ∧
      (D.profileAtOrigin = d → ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
        C * Real.log (1 / t) ≤ ∫ x, heatKernel d t x ∂μ) ∧
      (∀ β : ℝ, 0 < β → ENNReal.ofReal β < D.profileAtOrigin → ∃ C' : ℝ, ∀ t : ℝ, 0 < t →
        ∫ x, heatKernel d t x ∂μ ≤ C' * t ^ (-((d : ℝ) - β) / 2)) ∧
      Tendsto (fun t => Real.log (∫ x, heatKernel d t x ∂μ) / Real.log (1 / t)) (𝓝[>] 0)
        (𝓝 (((d : ℝ) - D.profileAtOrigin.toReal) / 2)) := by
  haveI := hμ.1
  obtain ⟨hctop, hc0, hcle⟩ := D.profileAtOrigin_toReal_pos hc hcd
  refine ⟨fun _ => heat_lower_lt hd D ha hc μ hμ hcd, fun h => heat_lower_eq hd D ha hc μ hμ h,
    fun β hβ0 hβc => (heat_upper hd D ha hc μ hμ hcd hβ0 hβc).imp fun _ h => h.2, ?_⟩
  set c := D.profileAtOrigin.toReal with hcdef
  set L := ((d : ℝ) - c) / 2 with hL
  have hlog : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    simp_rw [one_div]; exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  have hlogpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < Real.log (1 / t) := fun t ht =>
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ht)
  have hratio : ∀ (K : ℝ), Tendsto (fun t : ℝ => K / Real.log (1 / t)) (𝓝[>] 0) (𝓝 0) :=
    fun K => tendsto_const_nhds.div_atTop hlog
  rw [tendsto_order]
  constructor
  · intro a' ha'
    rcases lt_or_eq_of_le hcd with hlt | heq
    · obtain ⟨C, hC0, hC⟩ := heat_lower_lt hd D ha hc μ hμ hcd
      have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), a' - L < Real.log C / Real.log (1 / t) :=
        (hratio (Real.log C)).eventually (lt_mem_nhds (by linarith))
      filter_upwards [h2, hsmall] with t h2t ht
      have hl := hlogpos t ht
      have hP := hC t ⟨ht.1, ht.2.le⟩
      have hlogP : Real.log C + L * Real.log (1 / t) ≤ Real.log (∫ x, heatKernel d t x ∂μ) := by
        have hpos : 0 < C * t ^ (-((d : ℝ) - c) / 2) := mul_pos hC0 (Real.rpow_pos_of_pos ht.1 _)
        calc Real.log C + L * Real.log (1 / t) = Real.log (C * t ^ (-((d : ℝ) - c) / 2)) := by
              rw [Real.log_mul hC0.ne' (Real.rpow_pos_of_pos ht.1 _).ne', Real.log_rpow ht.1,
                one_div, Real.log_inv, hL]; ring
          _ ≤ Real.log (∫ x, heatKernel d t x ∂μ) := Real.log_le_log hpos hP
      rw [lt_div_iff₀ hl]
      rw [lt_div_iff₀ hl] at h2t
      nlinarith
    · obtain ⟨C, hC0, hC⟩ := heat_lower_eq hd D ha hc μ hμ heq
      have hcd' : c = d := by rw [hcdef, heq]; simp
      have hL0 : L = 0 := by rw [hL, hcd']; ring
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ C * Real.log (1 / t) :=
        (hlog.const_mul_atTop hC0).eventually_ge_atTop 1
      filter_upwards [hev, hsmall] with t hev ht
      have hl := hlogpos t ht
      have hP := hC t ⟨ht.1, ht.2.le⟩
      have h0 : 0 ≤ Real.log (∫ x, heatKernel d t x ∂μ) :=
        Real.log_nonneg (le_trans hev hP)
      have : 0 ≤ Real.log (∫ x, heatKernel d t x ∂μ) / Real.log (1 / t) := div_nonneg h0 hl.le
      rw [hL0] at ha'
      linarith
  · intro b hb
    set β := max (c - (b - L)) (c / 2) with hβ
    have hβ0 : 0 < β := lt_of_lt_of_le (half_pos hc0) (le_max_right _ _)
    have hβc : β < c := max_lt (by linarith) (half_lt_self hc0)
    have hβL : ((d : ℝ) - β) / 2 < b := by
      have : c - (b - L) ≤ β := le_max_left _ _
      rw [hL] at hb this
      linarith
    have hβc' : ENNReal.ofReal β < D.profileAtOrigin :=
      (ENNReal.ofReal_lt_iff_lt_toReal hβ0.le hctop).mpr hβc
    obtain ⟨C', hC'0, hC'⟩ := heat_upper hd D ha hc μ hμ hcd hβ0 hβc'
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.log C' / Real.log (1 / t) < b - ((d : ℝ) - β) / 2 :=
      (hratio (Real.log C')).eventually (gt_mem_nhds (by linarith))
    filter_upwards [h2, hsmall] with t h2t ht
    have hl := hlogpos t ht
    have hPpos := integral_heatKernel_pos μ ht.1
    have hP := hC' t ht.1
    have hlogP : Real.log (∫ x, heatKernel d t x ∂μ) ≤
        Real.log C' + ((d : ℝ) - β) / 2 * Real.log (1 / t) := by
      calc Real.log (∫ x, heatKernel d t x ∂μ) ≤ Real.log (C' * t ^ (-((d : ℝ) - β) / 2)) :=
            Real.log_le_log hPpos hP
        _ = Real.log C' + ((d : ℝ) - β) / 2 * Real.log (1 / t) := by
            rw [Real.log_mul hC'0.ne' (Real.rpow_pos_of_pos ht.1 _).ne', Real.log_rpow ht.1,
              one_div, Real.log_inv]; ring
    rw [div_lt_iff₀ hl]
    rw [div_lt_iff₀ hl] at h2t
    nlinarith

/-! ## `thm:origin-boundedness-d`(2)

Ledger A1 at `n = N`, through clause (1)'s decay (`lintegral_charFun_pow_ne_top`); A1's density is
nonnegative at its page's letter (the author's decision of 2026-10-05). -/

/-- Two continuous nonnegative densities of the same measure are equal: their `ofReal`s agree
almost everywhere, and continuous functions equal a.e. for Lebesgue measure are equal. Mathlib types
only. -/
theorem eq_of_withDensity_ofReal_eq {g g' : Rd d → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (h0 : ∀ x, 0 ≤ g x) (h0' : ∀ x, 0 ≤ g' x)
    (h : volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g' x))) : g = g' := by
  have hae : (fun x => ENNReal.ofReal (g x)) =ᵐ[volume] fun x => ENNReal.ofReal (g' x) :=
    (withDensity_eq_iff_of_sigmaFinite hg.measurable.ennreal_ofReal.aemeasurable
      hg'.measurable.ennreal_ofReal.aemeasurable).mp h
  have hae' : g =ᵐ[volume] g' := hae.mono fun x hx => by
    have := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (h0 x), ENNReal.toReal_ofReal (h0' x)] using this
  exact (hg.ae_eq_iff_eq volume hg').mp hae'

/-- The zeroth derivative tending to `0` is the function tending to `0`. Mathlib types only. -/
theorem tendsto_of_iteratedFDeriv_zero {g : Rd d → ℝ}
    (h : Tendsto (fun x => iteratedFDeriv ℝ 0 g x) (cocompact (Rd d)) (𝓝 0)) :
    Tendsto g (cocompact (Rd d)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  simpa only [norm_iteratedFDeriv_zero] using h

/-- A continuous function tending to `0` at infinity is bounded (it is a `C₀` function). Mathlib
types only. -/
theorem bddAbove_range_of_tendsto_cocompact {g : Rd d → ℝ} (hg : Continuous g)
    (h : Tendsto g (cocompact (Rd d)) (𝓝 0)) : BddAbove (range g) := by
  let f : ZeroAtInftyContinuousMap (Rd d) ℝ := ⟨⟨g, hg⟩, h⟩
  exact f.isBounded_range.bddAbove

/-- **`thm:origin-boundedness-d`(2)**: if `c > d + N` then `μ` has a nonnegative density of class
`C^N` on `ℝ^d` whose derivatives of orders `0, …, N` tend to `0` at infinity. Ledger A1 at `n = N`,
whose hypothesis is `lintegral_charFun_pow_ne_top`. -/
theorem origin_density_smooth (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) (N : ℕ)
    (hN : ((d + N : ℕ) : ℝ≥0∞) < D.profileAtOrigin) :
    ∃ g : Rd d → ℝ, (∀ x, 0 ≤ g x) ∧ ContDiff ℝ N g ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∀ k : ℕ, k ≤ N → Tendsto (fun x => iteratedFDeriv ℝ k g x) (cocompact (Rd d)) (𝓝 0) := by
  haveI := hμ.1
  exact density_of_integrable_charFun μ N (lintegral_charFun_pow_ne_top hd D ha hc μ hμ N hN)

/-- **`thm:origin-boundedness-d`(2)**, in particular: `c > d` makes the density continuous and
bounded (clause (2) at `N = 0`), and `c = ∞` makes it `C^∞` (the densities of every order agree, being
continuous, nonnegative and equal a.e.). -/
theorem origin_density_bounded_smooth (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    ((d : ℝ≥0∞) < D.profileAtOrigin → ∃ g : Rd d → ℝ, (∀ x, 0 ≤ g x) ∧ Continuous g ∧
        BddAbove (range g) ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (g x))) ∧
      (D.profileAtOrigin = ⊤ → ∃ g : Rd d → ℝ, (∀ x, 0 ≤ g x) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
        μ = volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
  constructor
  · intro hcd
    obtain ⟨g, h0, hg, hμg, hlim⟩ := origin_density_smooth hd D ha hc μ hμ 0 (by simpa using hcd)
    have hgc : Continuous g := hg.continuous
    exact ⟨g, h0, hgc, bddAbove_range_of_tendsto_cocompact hgc
      (tendsto_of_iteratedFDeriv_zero (hlim 0 le_rfl)), hμg⟩
  · intro htop
    have hN : ∀ N : ℕ, ((d + N : ℕ) : ℝ≥0∞) < D.profileAtOrigin := fun N => by
      rw [htop]; exact ENNReal.natCast_lt_top _
    obtain ⟨g, h0, hg, hμg, -⟩ := origin_density_smooth hd D ha hc μ hμ 0 (hN 0)
    refine ⟨g, h0, contDiff_infty.mpr fun N => ?_, hμg⟩
    obtain ⟨g', h0', hg', hμg', -⟩ := origin_density_smooth hd D ha hc μ hμ N (hN N)
    have heq : g = g' := eq_of_withDensity_ofReal_eq hg.continuous hg'.continuous h0 h0'
      (hμg.symm.trans hμg')
    rw [heq]; exact hg'

end AffineHemigroup
