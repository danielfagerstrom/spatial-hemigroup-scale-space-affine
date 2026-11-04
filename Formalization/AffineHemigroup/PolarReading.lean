/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.RotationInvariant
import AffineHemigroup.Interfaces
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.OriginBoundedness

/-!
# `prop:isotropic-polar-reading`(1): the polar form of a radial self-decomposable exponent

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-polar-reading`(1). Wave 2,
group A (Q-0281). Spends ledger A2 (`sato_polar_criterion`, both directions), A3
(`levy_khintchine_exists`, `_unique`, `_converse`) and A4 (`selfDecomposable_infinitelyDivisible`),
as the node's annotation assigns.

**Route.** The blueprint's, with two replacements. (i) The rotation invariance of the Lévy measure
is read from the uniqueness of the triplet (A3(ii)) applied to `μ` and the triplet pushed by a linear
isometry (`LevyTriplet.pushIso`), as in the blueprint; the Gaussian part is a multiple of `|ξ|²`
because the rest of the exponent is radial. (ii) **The average over `O(d)` is replaced** by the
determination of a rotation-invariant measure by its radial image (`eq_of_rotationInvariant`, through
the invariance of `σ_{d-1}` and the Fourier transform): the polar form of A2 gives the radial image
`k̄(r) dr/r` with `k̄ = ∫ k_η(r) λ(dη)` nonincreasing, and the datum's Lévy measure has the same image.
Measurability of `(η, r) ↦ k_η(r)`, which A2 does not state, is obtained by replacing `k_η` with its
right limits `sup_{q ∈ ℚ, q > r} k_η(q)`, equal to `k_η` off the countably many jumps.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix

variable {d : ℕ}

/-! ## The Lévy–Khintchine integrand -/

/-- `|e^{iθ} - 1 - iθ| ≤ 3θ²` for real `θ`. Mathlib types only. -/
theorem norm_exp_I_sub_one_sub_le (θ : ℝ) :
    ‖cexp ((θ : ℂ) * I) - 1 - I * (θ : ℂ)‖ ≤ 3 * θ ^ 2 := by
  rcases le_or_gt |θ| 1 with hθ | hθ
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := (θ : ℂ) * I) (by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hθ)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    rw [mul_comm I]
    nlinarith [sq_nonneg θ]
  · calc ‖cexp ((θ : ℂ) * I) - 1 - I * (θ : ℂ)‖
        ≤ ‖cexp ((θ : ℂ) * I)‖ + ‖(1 : ℂ)‖ + ‖I * (θ : ℂ)‖ := by
          have h1 := norm_sub_le (cexp ((θ : ℂ) * I)) 1
          have h2 := norm_sub_le (cexp ((θ : ℂ) * I) - 1) (I * (θ : ℂ))
          linarith
      _ = 2 + |θ| := by
          rw [Complex.norm_exp_ofReal_mul_I, norm_one, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]; ring
      _ ≤ 3 * θ ^ 2 := by nlinarith [sq_abs θ, abs_nonneg θ]

/-- The Lévy–Khintchine integrand `e^{i⟨z,x⟩} - 1 - i⟨z,x⟩ 1_D(x)`. -/
noncomputable def lkIntegrand (z x : Rd d) : ℂ :=
  cexp (((⟪z, x⟫ : ℝ) : ℂ) * I) - 1 - I * ((⟪z, x⟫ : ℝ) : ℂ) * (closedBall (0 : Rd d) 1).indicator 1 x

theorem norm_lkIntegrand_le (z x : Rd d) :
    ‖lkIntegrand z x‖ ≤ (3 * ‖z‖ ^ 2 + 2) * min (‖x‖ ^ 2) 1 := by
  rw [lkIntegrand]
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    rw [indicator_of_mem hx, Pi.one_apply, mul_one,
      min_eq_left (by nlinarith [norm_nonneg x])]
    refine (norm_exp_I_sub_one_sub_le _).trans ?_
    have h1 : ⟪z, x⟫ ^ 2 ≤ ‖z‖ ^ 2 * ‖x‖ ^ 2 := by
      have := abs_real_inner_le_norm z x
      rw [← mul_pow]; exact sq_le_sq' (by linarith [neg_abs_le ⟪z, x⟫]) (le_trans (le_abs_self _) this)
    nlinarith [sq_nonneg ‖x‖]
  · have hx1 : 1 < ‖x‖ := by simpa using hx
    rw [indicator_of_notMem hx, mul_zero, sub_zero,
      min_eq_right (by nlinarith)]
    calc ‖cexp (((⟪z, x⟫ : ℝ) : ℂ) * I) - 1‖ ≤ ‖cexp (((⟪z, x⟫ : ℝ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
      _ ≤ (3 * ‖z‖ ^ 2 + 2) * 1 := by nlinarith [sq_nonneg ‖z‖]

theorem measurable_lkIntegrand (z : Rd d) : Measurable (lkIntegrand z) := by
  unfold lkIntegrand
  refine ((by fun_prop : Measurable fun x : Rd d => cexp (((⟪z, x⟫ : ℝ) : ℂ) * I) - 1)).sub ?_
  exact (by fun_prop : Measurable fun x : Rd d => I * ((⟪z, x⟫ : ℝ) : ℂ)).mul
    (measurable_one.indicator measurableSet_closedBall)

/-- The integrand is integrable against a Lévy measure. -/
theorem LevyTriplet.integrable_lkIntegrand (T : LevyTriplet d) (z : Rd d) :
    Integrable (lkIntegrand z) T.ν := by
  have hmin : Integrable (fun x : Rd d => min (‖x‖ ^ 2) 1) T.ν := by
    refine ⟨(by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_))
      (lt_top_iff_ne_top.mpr T.ν_integrable)
    rw [Real.enorm_eq_ofReal (by positivity)]
  refine Integrable.mono' (hmin.const_mul (3 * ‖z‖ ^ 2 + 2))
    (measurable_lkIntegrand z).aestronglyMeasurable (ae_of_all _ fun x => norm_lkIntegrand_le z x)

theorem LevyTriplet.lkExponent_eq (T : LevyTriplet d) (z : Rd d) :
    T.lkExponent z = -((quad T.A z / 2 : ℝ) : ℂ) + I * ((⟪T.γ, z⟫ : ℝ) : ℂ)
      + ∫ x, lkIntegrand z x ∂T.ν := rfl

/-- `Re (e^{iθ} - 1 - iθ 1_D) = cos θ - 1`. -/
theorem re_lkIntegrand (z x : Rd d) : (lkIntegrand z x).re = Real.cos ⟪z, x⟫ - 1 := by
  rw [lkIntegrand]
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
    simp [Complex.exp_ofReal_mul_I_re]
  · rw [indicator_of_notMem hx, mul_zero, sub_zero]
    simp [Complex.exp_ofReal_mul_I_re]

/-- **The real part of the exponent**: `Re ψ(z) = -½⟨z,Az⟩ - ∫ (1 - cos⟨z,x⟩) ν(dx)`. -/
theorem LevyTriplet.re_lkExponent (T : LevyTriplet d) (z : Rd d) :
    (T.lkExponent z).re = -(quad T.A z / 2) - ∫ x, (1 - Real.cos ⟪z, x⟫) ∂T.ν := by
  rw [T.lkExponent_eq, Complex.add_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    one_mul, sub_zero, add_zero, ← RCLike.re_to_complex, ← integral_re (T.integrable_lkIntegrand z)]
  simp_rw [RCLike.re_to_complex, re_lkIntegrand]
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪z, x⟫) T.ν := by
    refine Integrable.mono' ((T.integrable_lkIntegrand z).norm) (by fun_prop)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one ⟪z, x⟫])]
    have := Complex.abs_re_le_norm (lkIntegrand z x)
    rw [re_lkIntegrand] at this
    rw [abs_of_nonpos (by linarith [Real.cos_le_one ⟪z, x⟫])] at this
    linarith
  rw [show (fun x : Rd d => Real.cos ⟪z, x⟫ - 1) = fun x => -(1 - Real.cos ⟪z, x⟫) by
    funext x; ring, integral_neg]
  ring

/-! ## The triplet pushed by a linear isometry -/

/-- The matrix of a linear isometry. -/
noncomputable def isoMat (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : Mat d :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (Q : Rd d →L[ℝ] Rd d)

theorem lin_isoMat (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : lin (isoMat Q) = (Q : Rd d →L[ℝ] Rd d) := by
  simp only [lin, isoMat, StarAlgEquiv.apply_symm_apply]

theorem lin_isoMat_transpose (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    lin (isoMat Q)ᵀ = (Q.symm : Rd d →L[ℝ] Rd d) := by
  rw [lin_transpose, lin_isoMat, LinearIsometryEquiv.adjoint_eq_symm]

/-- **The triplet of `Q_*μ`**: `(QAQᵀ, Q_*ν, Qγ)`. -/
noncomputable def LevyTriplet.pushIso (T : LevyTriplet d) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    LevyTriplet d where
  A := act (isoMat Q) T.A
  ν := T.ν.map Q
  γ := Q T.γ
  A_posSemidef := by
    have h := T.A_posSemidef.mul_mul_conjTranspose_same (isoMat Q)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  ν_zero := by
    rw [Measure.map_apply Q.continuous.measurable (measurableSet_singleton 0)]
    have : (Q : Rd d → Rd d) ⁻¹' {0} = {0} := by
      ext x; simp
    rw [this]; exact T.ν_zero
  ν_integrable := by
    rw [lintegral_map (by fun_prop) Q.continuous.measurable]
    simp_rw [LinearIsometryEquiv.norm_map]
    exact T.ν_integrable

/-- `ψ_{Q·T}(z) = ψ_T(Q⁻¹z)`. -/
theorem LevyTriplet.lkExponent_pushIso (T : LevyTriplet d) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (z : Rd d) :
    (T.pushIso Q).lkExponent z = T.lkExponent (Q.symm z) := by
  rw [LevyTriplet.lkExponent_eq, LevyTriplet.lkExponent_eq]
  have hquad : quad (T.pushIso Q).A z = quad T.A (Q.symm z) := by
    show quad (act (isoMat Q) T.A) z = _
    rw [quad_act, lin_isoMat_transpose]; rfl
  have hγ : ⟪(T.pushIso Q).γ, z⟫ = ⟪T.γ, Q.symm z⟫ := by
    show ⟪Q T.γ, z⟫ = _
    exact inner_isometry_symm Q T.γ z
  have hint : ∫ x, lkIntegrand z x ∂(T.pushIso Q).ν = ∫ x, lkIntegrand (Q.symm z) x ∂T.ν := by
    show ∫ x, lkIntegrand z x ∂(T.ν.map Q) = _
    rw [integral_map Q.continuous.measurable.aemeasurable
      (measurable_lkIntegrand z).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [lkIntegrand]
    rw [real_inner_comm, inner_isometry_symm, real_inner_comm]
    have hball : (Q x ∈ closedBall (0 : Rd d) 1) ↔ (x ∈ closedBall (0 : Rd d) 1) := by
      simp
    by_cases hx : x ∈ closedBall (0 : Rd d) 1
    · rw [indicator_of_mem hx, indicator_of_mem (hball.mpr hx)]
      simp only [Pi.one_apply]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hball.mp h))]
  rw [hquad, hγ, hint]

/-! ## A radial self-decomposable exponent: the forward direction -/

/-- **The Lévy measure of a law with radial transform is rotation invariant**: `μ` also has the
triplet pushed by any isometry, and the triplet is unique (A3(ii)). -/
theorem levyMeasure_rotationInvariant (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet d) (hT : HasTriplet μ T)
    (hrad : ∀ ξ ξ' : Rd d, ‖ξ‖ = ‖ξ'‖ → charFun μ ξ = charFun μ ξ') (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    T.ν.map Q = T.ν := by
  have hT' : HasTriplet μ (T.pushIso Q) := by
    intro z
    rw [hrad z (Q.symm z) (by rw [LinearIsometryEquiv.norm_map]), hT, T.lkExponent_pushIso]
  exact (levy_khintchine_unique μ hμ T (T.pushIso Q) hT hT').2.1.symm

/-- The cosine integral against a rotation-invariant measure is radial. -/
theorem integral_one_sub_cos_radial {ν : Measure (Rd d)}
    (hν : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν) {ξ ξ' : Rd d} (h : ‖ξ‖ = ‖ξ'‖) :
    ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂ν = ∫ x, (1 - Real.cos ⟪ξ', x⟫) ∂ν := by
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (ξ - ξ'))ᗮ with hQ
  have hQξ : Q ξ = ξ' := Submodule.reflection_sub h
  conv_rhs => rw [← hν Q]
  rw [integral_map Q.continuous.measurable.aemeasurable (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [← hQξ, LinearIsometryEquiv.inner_map_map]

/-! ## The right-limit modification of a family of nonincreasing profiles -/

/-- `g(η, r) = sup_{q ∈ ℚ, q > max(r, 0)} k_η(q)`, the right limit of `k_η` at `r > 0`, as a
jointly measurable function. -/
noncomputable def rightLim {X : Type*} (k : X → ℝ → ℝ) (η : X) (r : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if 0 < (q : ℝ) ∧ r < q then ENNReal.ofReal (k η q) else 0

theorem measurable_rightLim {X : Type*} [MeasurableSpace X] (k : X → ℝ → ℝ)
    (hk : ∀ r : ℝ, 0 < r → Measurable fun η => k η r) :
    Measurable (Function.uncurry (rightLim k)) := by
  unfold rightLim Function.uncurry
  refine Measurable.iSup fun q => ?_
  by_cases hq : (0 : ℝ) < q
  · have hset : MeasurableSet {p : X × ℝ | 0 < (q : ℝ) ∧ p.2 < q} := by
      simp only [hq, true_and]
      exact measurableSet_lt measurable_snd measurable_const
    exact Measurable.ite hset ((hk q hq).comp measurable_fst).ennreal_ofReal measurable_const
  · simp only [hq, false_and, if_false]
    exact measurable_const

theorem rightLim_antitone {X : Type*} (k : X → ℝ → ℝ) (η : X) : Antitone (rightLim k η) := by
  intro r r' hrr'
  refine iSup_mono fun q => ?_
  by_cases h : 0 < (q : ℝ) ∧ r' < q
  · rw [if_pos h, if_pos ⟨h.1, lt_of_le_of_lt hrr' h.2⟩]
  · rw [if_neg h]; exact zero_le

/-- For `r > 0` at which `k_η` is continuous on `(0,∞)`, `g(η, r) = k_η(r)`. -/
theorem rightLim_eq {X : Type*} {k : X → ℝ → ℝ} {η : X} (hanti : AntitoneOn (k η) (Ioi 0))
    {r : ℝ} (hr : 0 < r) (hcont : ContinuousWithinAt (k η) (Ioi 0) r) :
    rightLim k η r = ENNReal.ofReal (k η r) := by
  refine le_antisymm (iSup_le fun q => ?_) ?_
  · split_ifs with h
    · exact ENNReal.ofReal_le_ofReal (hanti hr h.1 h.2.le)
    · exact zero_le
  · -- approach `r` from the right through rationals
    have hlim : Tendsto (k η) (𝓝[>] r) (𝓝 (k η r)) :=
      (hcont.mono (Ioi_subset_Ioi hr.le)).tendsto
    have hlim' := (ENNReal.continuous_ofReal.tendsto _).comp hlim
    refine le_of_forall_lt fun c hc => ?_
    have hev : ∀ᶠ s in 𝓝[>] r, c < ENNReal.ofReal (k η s) := hlim'.eventually (lt_mem_nhds hc)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r < u from hu)
    have hq0 : (0 : ℝ) < q := lt_trans hr hq1
    refine lt_of_lt_of_le (hsub ⟨hq1, hq2⟩) (le_iSup_of_le q ?_)
    rw [if_pos ⟨hq0, hq1⟩]

/-! ## The radial image of a Lévy measure in polar form (A2's form) -/

/-- **The radial image** of a measure written as in ledger A2,
`ν(B) = ∫ λ(dξ) ∫_0^∞ 1_B(rξ) k_ξ(r) dr/r`, is `k̄(r) dr/r` on `(0,∞)` with
`k̄(r) = ∫ k_ξ(r+) λ(dξ)` (the right limits change no value of the inner integrals). -/
theorem map_norm_eq_of_polar (ν : Measure (Rd d)) (lam : Measure (sphere (0 : Rd d) 1))
    [IsFiniteMeasure lam] (k : sphere (0 : Rd d) 1 → ℝ → ℝ)
    (hk0 : ∀ ξ, ∀ r : ℝ, 0 < r → 0 ≤ k ξ r) (hkm : ∀ r : ℝ, 0 < r → Measurable fun ξ => k ξ r)
    (hka : ∀ ξ, AntitoneOn (k ξ) (Ioi 0))
    (hν : ∀ B : Set (Rd d), MeasurableSet B →
      ν B = ∫⁻ ξ, (∫⁻ r in Ioi (0 : ℝ), B.indicator 1 (r • (ξ : Rd d)) *
        ENNReal.ofReal (k ξ r / r)) ∂lam) :
    ν.map (fun x => ‖x‖) = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun r => (∫⁻ ξ, rightLim k ξ r ∂lam) * ENNReal.ofReal r⁻¹) := by
  have hg := measurable_rightLim k hkm
  have hgη : ∀ r : ℝ, Measurable fun ξ => rightLim k ξ r := fun r =>
    hg.comp (measurable_id.prodMk measurable_const)
  refine Measure.ext fun E hE => ?_
  rw [Measure.map_apply continuous_norm.measurable hE, hν _ (continuous_norm.measurable hE),
    withDensity_apply _ hE, Measure.restrict_restrict hE]
  -- each inner integral, with the right limits
  have hinner : ∀ ξ : sphere (0 : Rd d) 1,
      ∫⁻ r in Ioi (0 : ℝ), ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator 1 (r • (ξ : Rd d)) *
        ENNReal.ofReal (k ξ r / r)
      = ∫⁻ r in Ioi (0 : ℝ), E.indicator 1 r * (rightLim k ξ r * ENNReal.ofReal r⁻¹) := by
    intro ξ
    have hcount := (hka ξ).countable_not_continuousWithinAt
    have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
        r ∉ {x ∈ Ioi (0 : ℝ) | ¬ContinuousWithinAt (k ξ) (Ioi 0) x} :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero volume))
    have hae2 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    refine lintegral_congr_ae ?_
    filter_upwards [hae, hae2] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hcont : ContinuousWithinAt (k ξ) (Ioi 0) r := by
      by_contra h; exact hr ⟨hr0, h⟩
    have hind : ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator (1 : Rd d → ℝ≥0∞) (r • (ξ : Rd d))
        = E.indicator 1 r := by
      have hn : ‖r • (ξ : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere ξ, mul_one, Real.norm_of_nonneg hr0'.le]
      by_cases hrE : r ∈ E
      · rw [indicator_of_mem (show r • (ξ : Rd d) ∈ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE), indicator_of_mem hrE]
        rfl
      · rw [indicator_of_notMem (show r • (ξ : Rd d) ∉ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE), indicator_of_notMem hrE]
    rw [hind, rightLim_eq (hka ξ) hr0' hcont, div_eq_mul_inv,
      ENNReal.ofReal_mul (hk0 ξ r hr0')]
  simp_rw [hinner]
  have hjoint : Measurable (Function.uncurry fun (ξ : sphere (0 : Rd d) 1) (r : ℝ) =>
      E.indicator (1 : ℝ → ℝ≥0∞) r * (rightLim k ξ r * ENNReal.ofReal r⁻¹)) := by
    refine Measurable.mul ?_ (hg.mul ?_)
    · exact (measurable_one.indicator hE).comp measurable_snd
    · exact (measurable_snd.inv).ennreal_ofReal
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hstep : ∀ r : ℝ, ∫⁻ ξ, E.indicator (1 : ℝ → ℝ≥0∞) r * (rightLim k ξ r * ENNReal.ofReal r⁻¹) ∂lam
      = E.indicator (fun r => (∫⁻ ξ, rightLim k ξ r ∂lam) * ENNReal.ofReal r⁻¹) r := by
    intro r
    by_cases hrE : r ∈ E
    · simp only [indicator_of_mem hrE, Pi.one_apply, one_mul]
      rw [lintegral_mul_const _ (hgη r)]
    · simp only [indicator_of_notMem hrE, zero_mul, lintegral_zero]
  simp_rw [hstep]
  rw [lintegral_indicator hE, Measure.restrict_restrict hE]

/-! ## The Lévy measure of an origin datum -/

theorem LevyTriplet.integrable_one_sub_cos (T : LevyTriplet d) (z : Rd d) :
    Integrable (fun x : Rd d => 1 - Real.cos ⟪z, x⟫) T.ν := by
  refine Integrable.mono' ((T.integrable_lkIntegrand z).norm) (by fun_prop)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one ⟪z, x⟫])]
  have := Complex.abs_re_le_norm (lkIntegrand z x)
  rw [re_lkIntegrand, abs_of_nonpos (by linarith [Real.cos_le_one ⟪z, x⟫])] at this
  linarith

/-- `eq:polar-decomposition` for every nonnegative Borel `g` (the value at the origin is irrelevant,
`ν_d{0} = 0`). -/
theorem OriginDatum.polar_decomposition_any (hd : 1 ≤ d) (D : OriginDatum d) (g : Rd d → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂D.levyMeasure = (ENNReal.ofReal (sphereArea d))⁻¹ *
      ∫⁻ η : Metric.sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
        g (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)) ∂((volume : Measure (Rd d)).toSphere) := by
  have h0 : D.levyMeasure {0} = 0 := by
    rw [OriginDatum.levyMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    refine setLIntegral_eq_zero (measurableSet_singleton 0) fun x hx => ?_
    rw [mem_singleton_iff] at hx; subst hx; simp
  have hg' : Measurable (({0}ᶜ : Set (Rd d)).indicator g) :=
    hg.indicator (measurableSet_singleton 0).compl
  have hae : (fun x => g x) =ᵐ[D.levyMeasure] ({0}ᶜ : Set (Rd d)).indicator g := by
    have : ∀ᵐ x ∂D.levyMeasure, x ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [this] with x hx
    rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx)]
  rw [lintegral_congr_ae hae, D.polar_decomposition hd _ hg' (by simp)]
  congr 1
  refine lintegral_congr fun η => setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have hne : r • (η : Rd d) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr.le]
    exact hr.ne'
  rw [indicator_of_mem (show r • (η : Rd d) ∈ ({0}ᶜ : Set (Rd d)) from hne)]

/-- `ν_d` is invariant under linear isometries. -/
theorem OriginDatum.levyMeasure_map_isometry (D : OriginDatum d) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    D.levyMeasure.map Q = D.levyMeasure := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply Q.continuous.measurable hB, OriginDatum.levyMeasure,
    withDensity_apply _ (Q.continuous.measurable hB), withDensity_apply _ hB,
    ← lintegral_indicator (Q.continuous.measurable hB), ← lintegral_indicator hB]
  have h := (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding
    (B.indicator fun x => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x)
  rw [← h]
  refine lintegral_congr fun x => ?_
  by_cases hx : Q x ∈ B
  · rw [indicator_of_mem (show x ∈ Q ⁻¹' B from hx), indicator_of_mem hx]
    exact (D.levyDensity_isometry Q x).symm
  · rw [indicator_of_notMem (show x ∉ Q ⁻¹' B from hx), indicator_of_notMem hx]

theorem OriginDatum.levyMeasure_zero (D : OriginDatum d) : D.levyMeasure {0} = 0 := by
  rw [OriginDatum.levyMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  refine setLIntegral_eq_zero (measurableSet_singleton 0) fun x hx => ?_
  rw [mem_singleton_iff] at hx; subst hx; simp

/-- **The radial image of `ν_d`** is `k_d(r) dr/r` on `(0,∞)`, by `eq:polar-decomposition`. -/
theorem OriginDatum.map_norm_levyMeasure (hd : 1 ≤ d) (D : OriginDatum d) :
    D.levyMeasure.map (fun x => ‖x‖) = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun r => ENNReal.ofReal (D.k r / r)) := by
  have hA := (sphereArea_eq_toSphere hd).2
  refine Measure.ext fun E hE => ?_
  have hpre : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' E) := continuous_norm.measurable hE
  have hL : D.levyMeasure ((fun x : Rd d => ‖x‖) ⁻¹' E)
      = ∫⁻ x, ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator 1 x ∂D.levyMeasure :=
    (lintegral_indicator_one hpre).symm
  rw [Measure.map_apply continuous_norm.measurable hE, withDensity_apply _ hE,
    Measure.restrict_restrict hE, hL, D.polar_decomposition_any hd _
      (measurable_one.indicator hpre)]
  have hinner : ∀ η : sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)
      = ∫⁻ r in E ∩ Ioi 0, ENNReal.ofReal (D.k r / r) := by
    intro η
    rw [← lintegral_indicator (hE.inter measurableSet_Ioi), ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · have hn : ‖r • (η : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg (le_of_lt hr)]
      rw [indicator_of_mem hr]
      by_cases hrE : r ∈ E
      · rw [indicator_of_mem (show r • (η : Rd d) ∈ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE),
          indicator_of_mem (show r ∈ E ∩ Ioi 0 from ⟨hrE, hr⟩), Pi.one_apply, one_mul]
      · rw [indicator_of_notMem (show r • (η : Rd d) ∉ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE), indicator_of_notMem (fun h => hrE h.1),
          zero_mul]
    · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr h.2)]
  simp_rw [hinner]
  rw [lintegral_const, ← (sphereArea_eq_toSphere hd).1, mul_comm _ (ENNReal.ofReal (sphereArea d)),
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp [hA]) ENNReal.ofReal_ne_top, one_mul]

/-! ## `prop:isotropic-polar-reading`(1), forward -/

/-- A Lévy measure is finite off every ball about the origin. -/
theorem LevyTriplet.measure_norm_gt_ne_top (T : LevyTriplet d) {ε : ℝ} (hε : 0 < ε) :
    T.ν {x | ε < ‖x‖} ≠ ⊤ := by
  have hm : MeasurableSet {x : Rd d | ε < ‖x‖} := measurableSet_lt measurable_const
    continuous_norm.measurable
  have hc : 0 < min (ε ^ 2) 1 := lt_min (by positivity) one_pos
  have hle : ENNReal.ofReal (min (ε ^ 2) 1) * T.ν {x | ε < ‖x‖}
      ≤ ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂T.ν := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono' hm fun x (hx : ε < ‖x‖) => ENNReal.ofReal_le_ofReal ?_).trans
      (setLIntegral_le_lintegral _ _)
    exact min_le_min (pow_le_pow_left₀ hε.le hx.le 2) le_rfl
  intro htop
  rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc)] at hle
  exact T.ν_integrable (top_le_iff.mp hle)

/-- **`prop:isotropic-polar-reading`(1), forward**: a self-decomposable law with transform
`e^{-F(|ξ|)}` is the law of an isotropic origin datum. Spends A4, A3(i)–(ii), A2. -/
theorem polar_reading_forward (hd : 1 ≤ d) (F : ℝ → ℝ) (_hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hsd : IsSelfDecomposable μ)
    (hchar : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) :
    ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ := by
  haveI : NeZero d := ⟨by omega⟩
  set e₁ : Rd d := ebasis (0 : Fin d) with he₁
  have he₁1 : ‖e₁‖ = 1 := by simp [he₁, ebasis]
  have hsato := (isSelfDecomposable_iff_sato μ).mp hsd
  have hID := selfDecomposable_infinitelyDivisible μ hsato
  obtain ⟨T, hT⟩ := levy_khintchine_exists μ hID
  have hrad : ∀ ξ ξ' : Rd d, ‖ξ‖ = ‖ξ'‖ → charFun μ ξ = charFun μ ξ' := fun ξ ξ' h => by
    rw [hchar, hchar, h]
  have hrot := levyMeasure_rotationInvariant μ hID T hT hrad
  -- the exponent through the triplet
  have hFeq : ∀ ξ : Rd d, F ‖ξ‖ = quad T.A ξ / 2 + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂T.ν := by
    intro ξ
    have h1 : ‖charFun μ ξ‖ = Real.exp (-F ‖ξ‖) := by
      rw [hchar, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hT ξ, Complex.norm_exp, T.re_lkExponent] at h1
    have := Real.exp_injective h1
    linarith
  set a := quad T.A e₁ with ha
  have ha0 : 0 ≤ a := quad_nonneg T.A_posSemidef e₁
  have hquad : ∀ ξ : Rd d, quad T.A ξ = a * ‖ξ‖ ^ 2 := by
    intro ξ
    have hn : ‖ξ‖ = ‖‖ξ‖ • e₁‖ := by rw [norm_smul, he₁1, mul_one, norm_norm]
    have h1 := hFeq ξ
    have h2 := hFeq (‖ξ‖ • e₁)
    rw [← hn, integral_one_sub_cos_radial hrot hn.symm] at h2
    have h3 : quad T.A ξ = quad T.A (‖ξ‖ • e₁) := by linarith
    rw [h3, quad_smul_vec, ha]; ring
  -- the polar form (A2)
  obtain ⟨lam, k, hlamfin, hk0, hkm, hka, hν⟩ := (sato_polar_criterion μ hID T hT).mp hsato
  haveI := hlamfin
  have hmap := map_norm_eq_of_polar T.ν lam k hk0 hkm hka hν
  set K : ℝ → ℝ≥0∞ := fun r => ∫⁻ ξ, rightLim k ξ r ∂lam with hK
  have hKanti : Antitone K := fun r s hrs => lintegral_mono fun ξ => rightLim_antitone k ξ hrs
  -- the integrability of `min(r², 1)` against the radial image
  have hrint : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1) * (K r * ENNReal.ofReal r⁻¹)
      ≠ ⊤ := by
    have h := T.ν_integrable
    have heq : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂T.ν
        = ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1) ∂(T.ν.map fun x => ‖x‖) := by
      rw [lintegral_map (by fun_prop) continuous_norm.measurable]
    rw [heq, hmap, lintegral_withDensity_eq_lintegral_mul₀ ?_ (by fun_prop)] at h
    · refine ne_top_of_le_ne_top h (le_of_eq (lintegral_congr fun r => ?_))
      simp only [Pi.mul_apply]; ring
    · exact ((measurable_rightLim k hkm).lintegral_prod_left'.mul
        (measurable_inv.ennreal_ofReal)).aemeasurable
  have hKfin : ∀ r : ℝ, 0 < r → K r ≠ ⊤ := by
    intro r₀ hr₀ htop
    have hpos : 0 < volume (Ioo (r₀ / 2) r₀) := by
      rw [Real.volume_Ioo]; simp; linarith
    refine hrint (eq_top_iff.mpr ?_)
    calc (⊤ : ℝ≥0∞) = ∫⁻ _r in Ioo (r₀ / 2) r₀, ⊤ := by
          rw [setLIntegral_const, ENNReal.top_mul hpos.ne']
      _ ≤ ∫⁻ r in Ioo (r₀ / 2) r₀, ENNReal.ofReal (min (r ^ 2) 1) * (K r * ENNReal.ofReal r⁻¹) := by
          refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
          have hr0 : 0 < r := lt_trans (by linarith) hr.1
          have hKr : K r = ⊤ := top_le_iff.mp (htop ▸ hKanti hr.2.le)
          rw [hKr, ENNReal.top_mul (by simp [hr0]), ENNReal.mul_top (by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            exact lt_min (by positivity) one_pos)]
      _ ≤ _ := lintegral_mono_set (fun r hr => lt_trans (by linarith) hr.1)
  -- the datum
  have hkint : ∀ s : Set ℝ, s ⊆ Ioi 0 → MeasurableSet s →
      ∫⁻ r in s, ENNReal.ofReal (min (r ^ 2) 1) * (K r * ENNReal.ofReal r⁻¹) ≠ ⊤ :=
    fun s hs hsm => ne_top_of_le_ne_top hrint (lintegral_mono_set hs)
  have hval : ∀ r : ℝ, 0 < r → ENNReal.ofReal ((K r).toReal / r) = K r * ENNReal.ofReal r⁻¹ := by
    intro r hr
    rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hKfin r hr)]
  let D : OriginDatum d := {
    a := a
    k := fun r => (K r).toReal
    a_nonneg := ha0
    k_nonneg := fun r _ => ENNReal.toReal_nonneg
    k_antitone := fun r hr s hs hrs => ENNReal.toReal_mono (hKfin r hr) (hKanti hrs)
    integrable_near_zero := by
      refine ne_top_of_le_ne_top (hkint (Ioo 0 1) Ioo_subset_Ioi_self measurableSet_Ioo)
        (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_))
      have hr0 : 0 < r := hr.1
      rw [min_eq_left (by nlinarith [hr.1, hr.2]), ← hval r hr0, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    integrable_at_top := by
      refine ne_top_of_le_ne_top (hkint (Ioi 1) (Ioi_subset_Ioi zero_le_one) measurableSet_Ioi)
        (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_))
      rw [min_eq_right (by nlinarith), ENNReal.ofReal_one, one_mul, hval r (by linarith)] }
  -- its Lévy measure is `T.ν`
  have hmapD : D.levyMeasure.map (fun x => ‖x‖) = T.ν.map (fun x => ‖x‖) := by
    rw [D.map_norm_levyMeasure hd, hmap]
    refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun r (hr : 0 < r) => hval r hr))
  have hνD : D.levyMeasure = T.ν := by
    refine eq_of_rotationInvariant hd D.levyMeasure_map_isometry hrot D.levyMeasure_zero T.ν_zero
      (fun ε hε => ?_) (fun ε hε => T.measure_norm_gt_ne_top hε) hmapD
    have h1 : D.levyMeasure {x | ε < ‖x‖} = T.ν {x | ε < ‖x‖} := by
      have h := congrArg (fun m : Measure ℝ => m (Ioi ε)) hmapD
      rwa [Measure.map_apply continuous_norm.measurable measurableSet_Ioi,
        Measure.map_apply continuous_norm.measurable measurableSet_Ioi] at h
    rw [h1]; exact T.measure_norm_gt_ne_top hε
  refine ⟨D, fun ξ => ?_⟩
  have hint := T.integrable_one_sub_cos ξ
  have hnn : 0 ≤ ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂T.ν :=
    integral_nonneg fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪ξ, x⟫ by linarith [Real.cos_le_one ⟪ξ, x⟫]
  rw [OriginDatum.exponent, OriginDatum.exponentL, hνD,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪ξ, x⟫ by linarith [Real.cos_le_one ⟪ξ, x⟫]),
    ← ENNReal.ofReal_add (by positivity) hnn, ENNReal.toReal_ofReal (by positivity), hFeq ξ,
    hquad ξ]

/-! ## `prop:isotropic-polar-reading`(1), converse and uniqueness -/

/-- `∫ (|x|² ∧ 1) ν_d(dx) = ∫_0^∞ (r² ∧ 1) k_d(r) dr/r < ∞`. -/
theorem OriginDatum.lintegral_min_levyMeasure_ne_top (hd : 1 ≤ d) (D : OriginDatum d) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂D.levyMeasure ≠ ⊤ := by
  have heq : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂D.levyMeasure
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D.k r / r) * ENNReal.ofReal (min (r ^ 2) 1) := by
    have h1 : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂D.levyMeasure
        = ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1) ∂(D.levyMeasure.map fun x => ‖x‖) := by
      rw [lintegral_map (by fun_prop) continuous_norm.measurable]
    rw [h1, D.map_norm_levyMeasure hd, lintegral_withDensity_eq_lintegral_mul₀ ?_ (by fun_prop)]
    · rfl
    · exact (((measurable_indicator_Ioi_of_antitoneOn D.k_antitone).div measurable_id).ennreal_ofReal
        |>.aemeasurable).congr ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr => by
          simp only [indicator_of_mem hr, id]))
  rw [heq, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
  refine ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top D.integrable_near_zero
    (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_)),
    ne_top_of_le_ne_top D.integrable_at_top (le_of_eq ?_)⟩
  · have hr0 : 0 < r := hr.1
    rw [min_eq_left (by nlinarith [hr.1, hr.2]), ← ENNReal.ofReal_mul
      (div_nonneg (D.k_nonneg r hr0) hr0.le)]
    congr 1; field_simp
  · rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
    rw [min_eq_right (by nlinarith), ENNReal.ofReal_one, mul_one]

/-- **The triplet of an origin datum**: `(aI, ν_d, 0)`. -/
noncomputable def OriginDatum.triplet (hd : 1 ≤ d) (D : OriginDatum d) : LevyTriplet d where
  A := D.a • (1 : Mat d)
  ν := D.levyMeasure
  γ := 0
  A_posSemidef := Matrix.PosSemidef.one.smul D.a_nonneg
  ν_zero := D.levyMeasure_zero
  ν_integrable := D.lintegral_min_levyMeasure_ne_top hd

/-- The imaginary part of the Lévy–Khintchine integrand, `sin⟨z,x⟩ - ⟨z,x⟩ 1_D(x)`. -/
theorem im_lkIntegrand (z x : Rd d) : (lkIntegrand z x).im
    = Real.sin ⟪z, x⟫ - ⟪z, x⟫ * (closedBall (0 : Rd d) 1).indicator (1 : Rd d → ℝ) x := by
  rw [lkIntegrand]
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, Pi.one_apply, mul_one, mul_one]
    simp [Complex.exp_ofReal_mul_I_im]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero, sub_zero, sub_zero]
    simp [Complex.exp_ofReal_mul_I_im]

/-- The imaginary part of the Lévy–Khintchine integrand is odd in `x`. -/
theorem im_lkIntegrand_neg (z x : Rd d) : (lkIntegrand z (-x)).im = -(lkIntegrand z x).im := by
  rw [im_lkIntegrand, im_lkIntegrand, inner_neg_right, Real.sin_neg]
  have hball : (-x ∈ closedBall (0 : Rd d) 1) ↔ (x ∈ closedBall (0 : Rd d) 1) := by simp
  by_cases hx : x ∈ closedBall (0 : Rd d) 1
  · rw [indicator_of_mem hx, indicator_of_mem (hball.mpr hx)]; simp only [Pi.one_apply]; ring
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hball.mp h))]; ring

/-- **The exponent of the datum's triplet** is `-F_d`. -/
theorem OriginDatum.lkExponent_triplet (hd : 1 ≤ d) (D : OriginDatum d) (z : Rd d) :
    (D.triplet hd).lkExponent z = -((D.exponent z : ℝ) : ℂ) := by
  set T := D.triplet hd with hT
  have hsym : ∫ x, (lkIntegrand z x).im ∂T.ν = 0 := by
    have hneg := D.levyMeasure_map_isometry (LinearIsometryEquiv.neg ℝ)
    have h1 : ∫ x, (lkIntegrand z x).im ∂T.ν = ∫ x, (lkIntegrand z (-x)).im ∂T.ν := by
      show ∫ x, (lkIntegrand z x).im ∂D.levyMeasure = ∫ x, (lkIntegrand z (-x)).im ∂D.levyMeasure
      conv_lhs => rw [← hneg]
      exact integral_map (f := fun x => (lkIntegrand z x).im)
        (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
        ((Complex.measurable_im.comp (measurable_lkIntegrand z)).aestronglyMeasurable)
    simp_rw [im_lkIntegrand_neg, integral_neg] at h1
    linarith
  have hint := T.integrable_lkIntegrand z
  have hre := T.re_lkExponent z
  have hint1 : Integrable (fun x => 1 - Real.cos ⟪z, x⟫) D.levyMeasure :=
    (D.triplet hd).integrable_one_sub_cos z
  apply Complex.ext
  · rw [hre, Complex.neg_re, Complex.ofReal_re]
    show -(quad (D.a • (1 : Mat d)) z / 2) - ∫ x, (1 - Real.cos ⟪z, x⟫) ∂D.levyMeasure
      = -D.exponent z
    rw [quad_smul, quad_one, OriginDatum.exponent, OriginDatum.exponentL,
      ← ofReal_integral_eq_lintegral_ofReal hint1
        (ae_of_all _ fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪z, x⟫ by
          linarith [Real.cos_le_one ⟪z, x⟫]),
      ← ENNReal.ofReal_add (by have := D.a_nonneg; positivity)
        (integral_nonneg fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪z, x⟫ by
          linarith [Real.cos_le_one ⟪z, x⟫]),
      ENNReal.toReal_ofReal (add_nonneg (by have := D.a_nonneg; positivity)
        (integral_nonneg fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪z, x⟫ by
          linarith [Real.cos_le_one ⟪z, x⟫]))]
    ring
  · rw [T.lkExponent_eq, Complex.add_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.ofReal_im, ← RCLike.im_to_complex, ← integral_im hint]
    simp_rw [RCLike.im_to_complex, hsym]
    simp [hT, OriginDatum.triplet]

/-- **`prop:isotropic-polar-reading`(1), converse**: the law of an origin datum exists (A3(iii)) and
is self-decomposable (A2). -/
theorem polar_reading_converse (hd : 1 ≤ d) (D : OriginDatum d) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
      HasTriplet μ (D.triplet hd) ∧ ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-D.exponent ξ) : ℝ) : ℂ) := by
  obtain ⟨μ, hprob, hID, hT⟩ := levy_khintchine_converse (D.triplet hd)
  haveI := hprob
  have hA := (sphereArea_eq_toSphere hd).2
  refine ⟨μ, hprob, ?_, hT, fun ξ => ?_⟩
  · rw [isSelfDecomposable_iff_sato]
    refine (sato_polar_criterion μ hID (D.triplet hd) hT).mpr ⟨(volume : Measure (Rd d)).toSphere,
      fun _ r => D.k r / sphereArea d, inferInstance, fun _ r hr => div_nonneg (D.k_nonneg r hr) hA.le,
      fun _ _ => measurable_const, fun _ => fun r hr s hs hrs =>
        div_le_div_of_nonneg_right (D.k_antitone hr hs hrs) hA.le, fun B hB => ?_⟩
    show D.levyMeasure B = _
    rw [← lintegral_indicator_one hB, D.polar_decomposition_any hd _ (measurable_one.indicator hB),
      ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by simp [hA]))]
    refine lintegral_congr fun η => ?_
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by simp [hA]))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [mul_left_comm, ← ENNReal.ofReal_inv_of_pos hA, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  · rw [hT ξ, D.lkExponent_triplet hd, ← Complex.ofReal_neg, ← Complex.ofReal_exp]

/-- **`prop:isotropic-polar-reading`(1)**: for `F : [0,∞) → [0,∞)`, `ξ ↦ F(|ξ|)` is the exponent of
a self-decomposable law on `ℝ^d` if and only if it is the exponent `F_d` of an isotropic origin
datum in dimension `d`. -/
theorem polar_reading (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r) :
    (∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
        ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) ↔
      ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ := by
  constructor
  · rintro ⟨μ, hprob, hsd, hchar⟩
    haveI := hprob
    exact polar_reading_forward hd F hF μ hsd hchar
  · rintro ⟨D, hD⟩
    obtain ⟨μ, hprob, hsd, -, hchar⟩ := polar_reading_converse hd D
    exact ⟨μ, hprob, hsd, fun ξ => by rw [hchar, ← hD]⟩

/-- **`prop:isotropic-polar-reading`(1)**, uniqueness: the datum is unique, `k_d` up to modification
on a Lebesgue-null set. -/
theorem polar_reading_unique (hd : 1 ≤ d) (F : ℝ → ℝ) (_hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r)
    (D D' : OriginDatum d) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ)
    (hD' : ∀ ξ : Rd d, F ‖ξ‖ = D'.exponent ξ) :
    D.a = D'.a ∧ D.k =ᵐ[volume.restrict (Ioi (0 : ℝ))] D'.k := by
  obtain ⟨μ, hprob, -, hT, hchar⟩ := polar_reading_converse hd D
  obtain ⟨μ', hprob', -, hT', hchar'⟩ := polar_reading_converse hd D'
  haveI := hprob; haveI := hprob'
  have hμ : μ = μ' := by
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [hchar, hchar', ← hD, ← hD']
  have hID : IsInfinitelyDivisible μ := by
    obtain ⟨μ₀, h₀, hID₀, hT₀⟩ := levy_khintchine_converse (D.triplet hd)
    -- the law with triplet `T_D` is `μ` itself
    haveI := h₀
    have : μ₀ = μ := Measure.ext_of_charFun (funext fun ξ => by rw [hT₀ ξ, hT ξ])
    rwa [this] at hID₀
  have hT'μ : HasTriplet μ (D'.triplet hd) := by rw [hμ]; exact hT'
  obtain ⟨hA, hν, -⟩ := levy_khintchine_unique μ hID _ _ hT hT'μ
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun hA ⟨0, hd⟩) ⟨0, hd⟩
    simpa [OriginDatum.triplet] using h
  · have hν' : D.levyMeasure = D'.levyMeasure := hν
    have hmap := congrArg (fun m : Measure (Rd d) => m.map fun x => ‖x‖) hν'
    simp only [D.map_norm_levyMeasure hd, D'.map_norm_levyMeasure hd] at hmap
    have hmeas : ∀ D₀ : OriginDatum d, AEMeasurable (fun r => ENNReal.ofReal (D₀.k r / r))
        (volume.restrict (Ioi (0 : ℝ))) := fun D₀ =>
      (((measurable_indicator_Ioi_of_antitoneOn D₀.k_antitone).div measurable_id).ennreal_ofReal
        |>.aemeasurable).congr ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr => by
          simp only [indicator_of_mem hr, id]))
    have hae := (withDensity_eq_iff_of_sigmaFinite (hmeas D) (hmeas D')).mp hmap
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have h1 := (ENNReal.ofReal_eq_ofReal_iff (div_nonneg (D.k_nonneg r hr0) hr0'.le)
      (div_nonneg (D'.k_nonneg r hr0) hr0'.le)).mp hr
    field_simp at h1
    exact h1

end AffineHemigroup
