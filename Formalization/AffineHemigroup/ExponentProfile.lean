/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ProfileLayerCake
import AffineHemigroup.SphereLogMean

/-!
# `prop:isotropic-exponent-profile`: the exponent at infinity through the polar profile

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-exponent-profile` (Q-0427).

For an isotropic origin datum `(0, k_d)` in dimension `d ≥ 1` with a finite profile at the origin
`c = k_d(0+)`, exponent `F_d`, `C_k = ∫_1^∞ k_d dr/r` (`OriginDatum.tailConst`), the factor
`K(x) = exp ∫_x^1 (c - k_d(u)) du/u` (`OriginDatum.slowFactor`, a total function) and a unit vector
`e`:

* clause (1) is `AffineHemigroup.SlowFactor`: `slowFactor_basic`, `slowFactor_ratio`,
  `slowFactor_tendsto_of_integrable`, `slowFactor_tendsto_atTop`;
* clause (2): `cin_sub_log_limit` (`Cin(X) - log X → g_∞` with `-3 ≤ g_∞ ≤ 13/4`, `g_∞` the shared
  library's `ScaleSpace.cinConst`), and `sphere_log_mean`, `sphereLogMean_one` of
  `AffineHemigroup.SphereLogMean` (`λ_d`); `exponentConst d` is `ϰ_d = g_∞ + λ_d`;
* clause (3): `exponent_profile_asymptotic` (the limit `c ϰ_d` of
  `F_d(ρe) - (c log ρ - log K(1/ρ) + C_k)`, and the quotient form), `exponent_profile_bounds` (the
  two-sided bound for every `ρ > 0` with the tail integral of the profile, the identity of that
  integral with `c log ρ - log K(1/ρ) + C_k` for `ρ ≥ 1`, and the bound in that form);
* clause (4): `transform_power_comparison`, `transform_power_bounded_iff`,
  `transform_power_limit`.

**Choices.** The hypothesis `0 < c` of the printed statement is not assumed: no clause needs it.
The condition `∫_0^1 (c - k_d(u)) du/u < ∞` is the integrability of the integrand on `(0,1]`; the
integrand is nonnegative and measurable, so this is the finiteness of the integral. The limit of
clause (4) is along the cocompact filter of `ℝ^d`, that is as `|ξ| → ∞`.

**The route** is the proof of record's, with one piece of bookkeeping changed: the two terms of
`eq:profile-sphere` are kept in one integrand (`AffineHemigroup.ProfileLayerCake`), bounded by
`c(|log|⟨e,η⟩|| + 13/4)` and converging off the null great subsphere, so one dominated convergence
on `(0,c]` and one on the sphere give the limit, and the same two bounds give the interval.

Lean core: no ledger entry is read, and no law is named.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ScaleSpace
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- **`ϰ_d := g_∞ + λ_d`** (`prop:isotropic-exponent-profile`(2)), the constant of the exponent at
infinity: `g_∞ = lim (Cin X - log X)` and `λ_d` the mean of `log|⟨e,η⟩|` over the sphere. -/
noncomputable def exponentConst (d : ℕ) : ℝ := cinConst + sphereLogMean d

/-- **`prop:isotropic-exponent-profile`(2), the limit `g_∞`**: `Cin(X) - log X` has a limit as
`X → ∞`, the shared library's `ScaleSpace.cinConst`, and `-3 ≤ g_∞ ≤ 13/4`. -/
theorem cin_sub_log_limit :
    Tendsto (fun X : ℝ => cin X - Real.log X) atTop (𝓝 cinConst) ∧ -3 ≤ cinConst ∧
      cinConst ≤ 13 / 4 := by
  refine ⟨tendsto_cin_sub_log, ?_, ?_⟩
  · refine ge_of_tendsto tendsto_cin_sub_log ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    linarith [log_sub_le_cin (lt_of_lt_of_le one_pos hX)]
  · refine le_of_tendsto tendsto_cin_sub_log ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    linarith [cin_le_log_add hX]

/-! ## The sphere average -/

/-- **`eq:profile-sphere`, bounds and limit**: for a unit vector `e`, the difference
`Δ(ρ) = F_d(ρe) - ∫_{1/ρ}^∞ k_d(r) dr/r` lies in `[c(λ_d - 3), (13/4)c]` for every `ρ > 0`, and
tends to `c ϰ_d` as `ρ → ∞`. -/
theorem OriginDatum.exponent_sub_tail (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {e : Rd d} (he : ‖e‖ = 1) :
    (∀ ρ : ℝ, 0 < ρ →
      D.profileAtOrigin.toReal * (sphereLogMean d - 3)
          ≤ D.exponent (ρ • e) - ∫ r in Ioi ρ⁻¹, D.k r / r ∧
        D.exponent (ρ • e) - ∫ r in Ioi ρ⁻¹, D.k r / r ≤ 13 / 4 * D.profileAtOrigin.toReal) ∧
      Tendsto (fun ρ : ℝ => D.exponent (ρ • e) - ∫ r in Ioi ρ⁻¹, D.k r / r) atTop
        (𝓝 (D.profileAtOrigin.toReal * exponentConst d)) := by
  set σ := (volume : Measure (Rd d)).toSphere with hσ
  set c := D.profileAtOrigin.toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hA := (sphereArea_eq_toSphere hd).2
  have he0 : e ≠ 0 := by rw [← norm_ne_zero_iff, he]; exact one_ne_zero
  obtain ⟨hlogint, hmean, -⟩ := sphere_log_mean hd he
  set φR : ℝ → ℝ := fun s => (cosProfileL D.k s).toReal with hφR
  have hφm : Measurable φR := D.measurable_cosProfileL.ennreal_toReal
  set T : ℝ → ℝ := fun ρ => ∫ r in Ioi ρ⁻¹, D.k r / r with hT
  have htm : Measurable fun η : sphere (0 : Rd d) 1 => ⟪e, (η : Rd d)⟫ :=
    (continuous_const.inner continuous_subtype_val).measurable
  have ht1 : ∀ η : sphere (0 : Rd d) 1, |⟪e, (η : Rd d)⟫| ≤ 1 := fun η =>
    abs_inner_sphere_le_one he η
  have hlog_np : ∀ η : sphere (0 : Rd d) 1, Real.log |⟪e, (η : Rd d)⟫| ≤ 0 := fun η =>
    Real.log_nonpos (abs_nonneg _) (ht1 η)
  -- the great subsphere is null
  have hae : ∀ᵐ η : sphere (0 : Rd d) 1 ∂σ, ⟪e, (η : Rd d)⟫ ≠ 0 := by
    rw [ae_iff]
    exact measure_mono_null (fun η hη => not_not.mp hη) (toSphere_inner_eq_zero he0)
  have hmass : σ.real univ = sphereArea d := by
    rw [measureReal_def, hσ, ← (sphereArea_eq_toSphere hd).1, ENNReal.toReal_ofReal hA.le]
  have hL : ∫ η : sphere (0 : Rd d) 1, Real.log |⟪e, (η : Rd d)⟫| ∂σ
      = sphereArea d * sphereLogMean d := by
    rw [hmean, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  -- `η ↦ φ(ρ⟨e,η⟩)` is bounded, hence integrable
  have hφint : ∀ ρ : ℝ, Integrable (fun η : sphere (0 : Rd d) 1 => φR (ρ * ⟪e, (η : Rd d)⟫)) σ := by
    intro ρ
    set I0 := ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (D.k r * r) with hI0
    set I1 := ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r) with hI1
    have hfin : ENNReal.ofReal (|ρ| ^ 2 / 2) * I0 + 2 * I1 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top D.integrable_near_zero,
        ENNReal.mul_ne_top (by norm_num) D.integrable_at_top⟩
    refine Integrable.mono'
      (integrable_const ((ENNReal.ofReal (|ρ| ^ 2 / 2) * I0 + 2 * I1).toReal))
      ((hφm.comp (htm.const_mul ρ)).aestronglyMeasurable) (ae_of_all _ fun η => ?_)
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_mono hfin ((cosProfileL_le_sq D.k D.k_nonneg _).trans ?_)
    have hsq : (ρ * ⟪e, (η : Rd d)⟫) ^ 2 ≤ |ρ| ^ 2 := by
      rw [← sq_abs (ρ * ⟪e, (η : Rd d)⟫), abs_mul]
      have h1 := ht1 η
      have h0 := abs_nonneg ⟪e, (η : Rd d)⟫
      have h2 := abs_nonneg ρ
      nlinarith [mul_le_of_le_one_right h2 h1, mul_nonneg h2 h0]
    exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl) le_rfl
  -- the difference as one sphere integral
  have hdiff : ∀ ρ : ℝ, D.exponent (ρ • e) - T ρ = (sphereArea d)⁻¹ *
      ∫ η : sphere (0 : Rd d) 1, (φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) ∂σ := by
    intro ρ
    rw [integral_sub (hφint ρ) (integrable_const _), integral_const, smul_eq_mul, hmass, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul, D.exponent_eq_integral_sphere hd ha]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    simp only [hφR, inner_smul_left, RCLike.conj_to_real]
  -- the layer-cake form of the integrand
  have hform : ∀ ρ : ℝ, 0 < ρ → ∀ η : sphere (0 : Rd d) 1,
      φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ = ∫ y in Ioc (0 : ℝ) c,
        (cin (ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y)) :=
    fun ρ hρ η => (D.cosProfile_sub_tail hc hρ (ρ * ⟪e, (η : Rd d)⟫)).2
  have hHint : ∀ ρ : ℝ, 0 < ρ → ∀ η : sphere (0 : Rd d) 1, IntegrableOn (fun y =>
      cin (ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y))
      (Ioc 0 c) :=
    fun ρ hρ η => (D.cosProfile_sub_tail hc hρ (ρ * ⟪e, (η : Rd d)⟫)).1
  have hHb : ∀ ρ : ℝ, 0 < ρ → ∀ η : sphere (0 : Rd d) 1, ⟪e, (η : Rd d)⟫ ≠ 0 → ∀ y : ℝ,
      Real.log |⟪e, (η : Rd d)⟫| - 3
          ≤ cin (ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y) ∧
        cin (ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y)
          ≤ 13 / 4 := by
    intro ρ hρ η hη y
    have h := cin_sub_posLog_bounds (P := ρ * D.levelRadius y)
      (mul_nonneg hρ.le (D.levelRadius_nonneg y)) hη (ht1 η)
    rwa [show ⟪e, (η : Rd d)⟫ * (ρ * D.levelRadius y) = ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y by
      ring] at h
  have hvol : volume.real (Ioc (0 : ℝ) c) = c := by
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hc0]
  have hfinvol : volume (Ioc (0 : ℝ) c) ≠ ⊤ := by simp [Real.volume_Ioc]
  have hFb : ∀ ρ : ℝ, 0 < ρ → ∀ η : sphere (0 : Rd d) 1, ⟪e, (η : Rd d)⟫ ≠ 0 →
      c * (Real.log |⟪e, (η : Rd d)⟫| - 3) ≤ φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ ∧
        φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ ≤ 13 / 4 * c := by
    intro ρ hρ η hη
    rw [hform ρ hρ η]
    constructor
    · have h := setIntegral_mono_on
        (integrableOn_const (C := Real.log |⟪e, (η : Rd d)⟫| - 3) hfinvol) (hHint ρ hρ η)
        measurableSet_Ioc (fun y _ => (hHb ρ hρ η hη y).1)
      rwa [setIntegral_const, smul_eq_mul, hvol] at h
    · have h := setIntegral_mono_on (hHint ρ hρ η)
        (integrableOn_const (C := (13 / 4 : ℝ)) hfinvol) measurableSet_Ioc
        (fun y _ => (hHb ρ hρ η hη y).2)
      rw [setIntegral_const, smul_eq_mul, hvol] at h
      linarith
  -- the limit of the integrand, off the great subsphere: dominated convergence on `(0,c]`
  have hFlim : ∀ η : sphere (0 : Rd d) 1, ⟪e, (η : Rd d)⟫ ≠ 0 →
      Tendsto (fun ρ : ℝ => φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) atTop
        (𝓝 (c * (cinConst + Real.log |⟪e, (η : Rd d)⟫|))) := by
    intro η hη
    have hdct : Tendsto (fun ρ : ℝ => ∫ y in Ioc (0 : ℝ) c,
        (cin (ρ * ⟪e, (η : Rd d)⟫ * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y))) atTop
        (𝓝 (∫ _y in Ioc (0 : ℝ) c, (cinConst + Real.log |⟪e, (η : Rd d)⟫|))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun _ => abs (Real.log |⟪e, (η : Rd d)⟫|) + 13 / 4) ?_ ?_ (integrableOn_const hfinvol) ?_
      · filter_upwards [eventually_gt_atTop 0] with ρ hρ
        exact (hHint ρ hρ η).aestronglyMeasurable
      · filter_upwards [eventually_gt_atTop 0] with ρ hρ
        refine ae_of_all _ fun y => ?_
        obtain ⟨h1, h2⟩ := hHb ρ hρ η hη y
        have h3 := hlog_np η
        rw [Real.norm_eq_abs, abs_le, abs_of_nonpos h3]
        constructor <;> linarith
      · have hne : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) c)), y ≠ c :=
          ae_restrict_of_ae (show ∀ᵐ y ∂(volume : Measure ℝ), y ≠ c from
            compl_mem_ae_iff.2 (measure_singleton c))
        filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with y hyc hy
        exact tendsto_cin_sub_posLog hη (D.levelRadius_pos hc hy.1 (lt_of_le_of_ne hy.2 hyc))
    rw [setIntegral_const, smul_eq_mul, hvol] at hdct
    refine hdct.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    exact (hform ρ hρ η).symm
  -- dominated convergence on the sphere
  have hmeasF : ∀ ρ : ℝ, AEStronglyMeasurable
      (fun η : sphere (0 : Rd d) 1 => φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) σ := fun ρ =>
    ((hφm.comp (htm.const_mul ρ)).sub measurable_const).aestronglyMeasurable
  have hbint : Integrable (fun η : sphere (0 : Rd d) 1 =>
      c * (abs (Real.log |⟪e, (η : Rd d)⟫|) + 13 / 4)) σ :=
    (hlogint.abs.add (integrable_const _)).const_mul c
  have hFabs : ∀ ρ : ℝ, 0 < ρ → ∀ η : sphere (0 : Rd d) 1, ⟪e, (η : Rd d)⟫ ≠ 0 →
      |φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ| ≤ c * (abs (Real.log |⟪e, (η : Rd d)⟫|) + 13 / 4) := by
    intro ρ hρ η hη
    obtain ⟨h1, h2⟩ := hFb ρ hρ η hη
    have h3 := mul_nonneg hc0 (neg_nonneg.2 (hlog_np η))
    rw [abs_of_nonpos (hlog_np η), abs_le]
    constructor <;> nlinarith
  have hlimint : Tendsto (fun ρ : ℝ => ∫ η : sphere (0 : Rd d) 1,
      (φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) ∂σ) atTop
      (𝓝 (∫ η : sphere (0 : Rd d) 1, c * (cinConst + Real.log |⟪e, (η : Rd d)⟫|) ∂σ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun η : sphere (0 : Rd d) 1 => c * (abs (Real.log |⟪e, (η : Rd d)⟫|) + 13 / 4))
      (Filter.Eventually.of_forall hmeasF) ?_ hbint ?_
    · filter_upwards [eventually_gt_atTop 0] with ρ hρ
      filter_upwards [hae] with η hη
      rw [Real.norm_eq_abs]
      exact hFabs ρ hρ η hη
    · filter_upwards [hae] with η hη
      exact hFlim η hη
  have hval : (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
      c * (cinConst + Real.log |⟪e, (η : Rd d)⟫|) ∂σ = c * exponentConst d := by
    have hinv : (sphereArea d)⁻¹ * sphereArea d = 1 := inv_mul_cancel₀ hA.ne'
    rw [integral_const_mul, integral_add (integrable_const _) hlogint, integral_const, smul_eq_mul,
      hmass, hL, exponentConst]
    linear_combination (c * (cinConst + sphereLogMean d)) * hinv
  refine ⟨fun ρ hρ => ?_, ?_⟩
  · rw [hdiff ρ]
    have hFint : Integrable (fun η : sphere (0 : Rd d) 1 => φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) σ :=
      (hφint ρ).sub (integrable_const _)
    have hinv : (sphereArea d)⁻¹ * sphereArea d = 1 := inv_mul_cancel₀ hA.ne'
    constructor
    · have h1 : ∫ η : sphere (0 : Rd d) 1, c * (Real.log |⟪e, (η : Rd d)⟫| - 3) ∂σ
          ≤ ∫ η : sphere (0 : Rd d) 1, (φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) ∂σ :=
        integral_mono_ae ((hlogint.sub (integrable_const _)).const_mul c) hFint
          (by filter_upwards [hae] with η hη; exact (hFb ρ hρ η hη).1)
      rw [integral_const_mul, integral_sub hlogint (integrable_const _), integral_const,
        smul_eq_mul, hmass, hL] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hA.le)
      refine le_trans (le_of_eq ?_) h3
      linear_combination (-(c * (sphereLogMean d - 3))) * hinv
    · have h1 : ∫ η : sphere (0 : Rd d) 1, (φR (ρ * ⟪e, (η : Rd d)⟫) - T ρ) ∂σ
          ≤ ∫ _η : sphere (0 : Rd d) 1, (13 / 4 * c) ∂σ :=
        integral_mono_ae hFint (integrable_const _)
          (by filter_upwards [hae] with η hη; exact (hFb ρ hρ η hη).2)
      rw [integral_const, smul_eq_mul, hmass] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hA.le)
      refine le_trans h3 (le_of_eq ?_)
      linear_combination (13 / 4 * c) * hinv
  · rw [← hval]
    exact (hlimint.const_mul _).congr fun ρ => (hdiff ρ).symm

/-! ## Clause (3) -/

/-- **`prop:isotropic-exponent-profile`(3), the two-sided bounds**: for a datum with Gaussian
coefficient `0` and a finite profile at the origin `c`, and a unit vector `e`: for every `ρ > 0`,
`c(λ_d - 3) ≤ F_d(ρe) - ∫_{1/ρ}^∞ k_d(r) dr/r ≤ (13/4)c`; for `ρ ≥ 1` the integral equals
`c log ρ - log K(1/ρ) + C_k`; hence for `ρ ≥ 1`,
`c(λ_d - 3) ≤ F_d(ρe) - (c log ρ - log K(1/ρ) + C_k) ≤ (13/4)c`. -/
theorem exponent_profile_bounds (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {e : Rd d} (he : ‖e‖ = 1) :
    (∀ ρ : ℝ, 0 < ρ →
      D.profileAtOrigin.toReal * (sphereLogMean d - 3)
          ≤ D.exponent (ρ • e) - ∫ r in Ioi ρ⁻¹, D.k r / r ∧
        D.exponent (ρ • e) - ∫ r in Ioi ρ⁻¹, D.k r / r ≤ 13 / 4 * D.profileAtOrigin.toReal) ∧
      (∀ ρ : ℝ, 1 ≤ ρ → ∫ r in Ioi ρ⁻¹, D.k r / r =
        D.profileAtOrigin.toReal * Real.log ρ - Real.log (D.slowFactor ρ⁻¹) + D.tailConst) ∧
      ∀ ρ : ℝ, 1 ≤ ρ →
        D.profileAtOrigin.toReal * (sphereLogMean d - 3)
            ≤ D.exponent (ρ • e) - (D.profileAtOrigin.toReal * Real.log ρ -
              Real.log (D.slowFactor ρ⁻¹) + D.tailConst) ∧
          D.exponent (ρ • e) - (D.profileAtOrigin.toReal * Real.log ρ -
              Real.log (D.slowFactor ρ⁻¹) + D.tailConst) ≤ 13 / 4 * D.profileAtOrigin.toReal := by
  have h := (D.exponent_sub_tail hd ha hc he).1
  refine ⟨h, fun ρ hρ => integral_k_div_Ioi_eq D hρ, fun ρ hρ => ?_⟩
  rw [← integral_k_div_Ioi_eq D hρ]
  exact h ρ (lt_of_lt_of_le one_pos hρ)

/-- **`prop:isotropic-exponent-profile`(3), the asymptotic**: for a datum with Gaussian
coefficient `0` and a finite profile at the origin `c`, and a unit vector `e`, as `ρ → ∞`,
`F_d(ρe) - (c log ρ - log K(1/ρ) + C_k) → c ϰ_d`, that is
`e^{-F_d(ρe)} / (e^{-C_k - cϰ_d} ρ^{-c} K(1/ρ)) → 1`. -/
theorem exponent_profile_asymptotic (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {e : Rd d} (he : ‖e‖ = 1) :
    Tendsto (fun ρ : ℝ => D.exponent (ρ • e) - (D.profileAtOrigin.toReal * Real.log ρ -
        Real.log (D.slowFactor ρ⁻¹) + D.tailConst)) atTop
        (𝓝 (D.profileAtOrigin.toReal * exponentConst d)) ∧
      Tendsto (fun ρ : ℝ => Real.exp (-D.exponent (ρ • e)) /
        (Real.exp (-D.tailConst - D.profileAtOrigin.toReal * exponentConst d) *
          ρ ^ (-D.profileAtOrigin.toReal) * D.slowFactor ρ⁻¹)) atTop (𝓝 1) := by
  set c := D.profileAtOrigin.toReal with hcdef
  have h := (D.exponent_sub_tail hd ha hc he).2
  have h1 : Tendsto (fun ρ : ℝ => D.exponent (ρ • e) - (c * Real.log ρ -
      Real.log (D.slowFactor ρ⁻¹) + D.tailConst)) atTop (𝓝 (c * exponentConst d)) := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with ρ hρ
    rw [integral_k_div_Ioi_eq D hρ]
  refine ⟨h1, ?_⟩
  have h2 := (Real.continuous_exp.tendsto _).comp ((h1.sub_const (c * exponentConst d)).neg)
  rw [sub_self, neg_zero, Real.exp_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  simp only [Function.comp_apply]
  have hK : D.slowFactor ρ⁻¹ = Real.exp (Real.log (D.slowFactor ρ⁻¹)) := by
    rw [Real.exp_log]; exact Real.exp_pos _
  rw [Real.rpow_def_of_pos hρ, hK, Real.log_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-! ## Clause (4) -/

/-- For `ρ ≥ 1`: `ρ^c e^{-F_d(ρe)} = e^{-C_k - Δ(ρ)} K(1/ρ)`, with
`Δ(ρ) = F_d(ρe) - (c log ρ - log K(1/ρ) + C_k)`. -/
theorem OriginDatum.rpow_mul_exp_neg_exponent (D : OriginDatum d) (e : Rd d) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ρ ^ D.profileAtOrigin.toReal * Real.exp (-D.exponent (ρ • e)) =
      Real.exp (-D.tailConst - (D.exponent (ρ • e) - (D.profileAtOrigin.toReal * Real.log ρ -
        Real.log (D.slowFactor ρ⁻¹) + D.tailConst))) * D.slowFactor ρ⁻¹ := by
  have hK : D.slowFactor ρ⁻¹ = Real.exp (Real.log (D.slowFactor ρ⁻¹)) := by
    rw [Real.exp_log]; exact Real.exp_pos _
  rw [Real.rpow_def_of_pos hρ]
  conv_rhs => rw [hK]
  rw [Real.log_exp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **`prop:isotropic-exponent-profile`(4), the comparison**: for every `ξ` with `|ξ| ≥ 1`,
`e^{-13c/4 - C_k} K(1/|ξ|) ≤ |ξ|^c e^{-F_d(ξ)} ≤ e^{c(3-λ_d) - C_k} K(1/|ξ|)`. -/
theorem transform_power_comparison (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) (ξ : Rd d) (hξ : 1 ≤ ‖ξ‖) :
    Real.exp (-(13 / 4) * D.profileAtOrigin.toReal - D.tailConst) * D.slowFactor ‖ξ‖⁻¹
        ≤ ‖ξ‖ ^ D.profileAtOrigin.toReal * Real.exp (-D.exponent ξ) ∧
      ‖ξ‖ ^ D.profileAtOrigin.toReal * Real.exp (-D.exponent ξ)
        ≤ Real.exp (D.profileAtOrigin.toReal * (3 - sphereLogMean d) - D.tailConst) *
          D.slowFactor ‖ξ‖⁻¹ := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  have hρ0 : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hξ
  have hrad : D.exponent ξ = D.exponent (‖ξ‖ • e) :=
    D.exponent_eq_of_norm_eq (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg _)])
  obtain ⟨hlow, hupp⟩ := (exponent_profile_bounds hd D ha hc he).2.2 ‖ξ‖ hξ
  have hKpos : 0 < D.slowFactor ‖ξ‖⁻¹ := Real.exp_pos _
  rw [hrad, D.rpow_mul_exp_neg_exponent e hρ0]
  constructor
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hKpos.le
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hKpos.le

/-- **`prop:isotropic-exponent-profile`(4), the criterion**: `|ξ|^c e^{-F_d(ξ)}` is bounded on
`{|ξ| ≥ 1}` if and only if `(c - k_d(u))/u` is integrable on `(0,1]`. -/
theorem transform_power_bounded_iff (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) :
    (∃ M : ℝ, ∀ ξ : Rd d, 1 ≤ ‖ξ‖ →
        ‖ξ‖ ^ D.profileAtOrigin.toReal * Real.exp (-D.exponent ξ) ≤ M) ↔
      IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  set c := D.profileAtOrigin.toReal with hcdef
  constructor
  · rintro ⟨M, hM⟩
    by_contra hI
    have htop := slowFactor_tendsto_atTop D hc hI
    set M' := M / Real.exp (-(13 / 4) * c - D.tailConst) with hM'
    -- `K ≤ M'` on `(0,1]`
    have hK : ∀ x ∈ Ioc (0 : ℝ) 1, D.slowFactor x ≤ M' := by
      intro x hx
      have hρ : 1 ≤ x⁻¹ := (one_le_inv₀ hx.1).2 hx.2
      have hnorm : ‖x⁻¹ • e‖ = x⁻¹ := by
        rw [norm_smul, he, mul_one, Real.norm_of_nonneg (inv_nonneg.2 hx.1.le)]
      have h1 := (transform_power_comparison hd D ha hc (x⁻¹ • e) (by rw [hnorm]; exact hρ)).1
      have h2 := hM (x⁻¹ • e) (by rw [hnorm]; exact hρ)
      rw [hnorm, inv_inv] at h1
      rw [hnorm] at h2
      rw [hM', le_div_iff₀ (Real.exp_pos _), mul_comm]
      exact le_trans h1 h2
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), M' + 1 ≤ D.slowFactor x := tendsto_atTop.1 htop (M' + 1)
    have hmem : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
    obtain ⟨x, hx1, hx2⟩ := (hev.and hmem).exists
    linarith [hK x hx2]
  · intro hI
    obtain ⟨-, -, hle⟩ := slowFactor_tendsto_of_integrable D hc hI
    refine ⟨Real.exp (c * (3 - sphereLogMean d) - D.tailConst) * D.slowFactorZero, fun ξ hξ => ?_⟩
    have hρ0 : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hξ
    refine le_trans (transform_power_comparison hd D ha hc ξ hξ).2
      (mul_le_mul_of_nonneg_left (hle _ ⟨inv_pos.2 hρ0, inv_le_one_of_one_le₀ hξ⟩)
        (Real.exp_pos _).le)

/-- **`prop:isotropic-exponent-profile`(4), the limit**: if `(c - k_d(u))/u` is integrable on
`(0,1]`, then `|ξ|^c e^{-F_d(ξ)} → e^{-C_k - cϰ_d} K(0+)` as `|ξ| → ∞`. -/
theorem transform_power_limit (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤)
    (hI : IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto (fun ξ : Rd d => ‖ξ‖ ^ D.profileAtOrigin.toReal * Real.exp (-D.exponent ξ))
      (cocompact (Rd d))
      (𝓝 (Real.exp (-D.tailConst - D.profileAtOrigin.toReal * exponentConst d) *
        D.slowFactorZero)) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  set c := D.profileAtOrigin.toReal with hcdef
  have hΔ := (exponent_profile_asymptotic hd D ha hc he).1
  have hKlim : Tendsto (fun ρ : ℝ => D.slowFactor ρ⁻¹) atTop (𝓝 D.slowFactorZero) :=
    (slowFactor_tendsto_of_integrable D hc hI).1.comp tendsto_inv_atTop_nhdsGT_zero
  have hexp := (Real.continuous_exp.tendsto _).comp
    ((tendsto_const_nhds (x := -D.tailConst)).sub hΔ)
  have hray : Tendsto (fun ρ : ℝ => ρ ^ c * Real.exp (-D.exponent (ρ • e))) atTop
      (𝓝 (Real.exp (-D.tailConst - c * exponentConst d) * D.slowFactorZero)) := by
    refine (hexp.mul hKlim).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    simp only [Function.comp_apply]
    exact (D.rpow_mul_exp_neg_exponent e hρ).symm
  refine (hray.comp (tendsto_norm_cocompact_atTop (E := Rd d))).congr fun ξ => ?_
  simp only [Function.comp_apply]
  rw [D.exponent_eq_of_norm_eq (ξ := ξ) (ξ' := ‖ξ‖ • e)
    (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg _)])]

end AffineHemigroup
