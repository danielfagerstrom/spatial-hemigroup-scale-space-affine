/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.IsotropicClassification
import AffineHemigroup.GaussMixture
import AffineHemigroup.RadialTransform
import ScaleSpaceCore.BridgeExponents
import ScaleSpaceCore.StudentTransform

/-!
# `prop:isotropic-bridge` and `prop:isotropic-bridge-student`: the bridge in dimension `d`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-bridge` (clauses (1)–(3)) and
`prop:isotropic-bridge-student` (clause (4)). Wave 2, group A (Q-0281).

The blueprint's route. The transform of the mixture `μ_{s,t} = ∫ g^{(d)}_u μ^I_{s²,t²}(du)` is the
Laplace transform of `μ^I_{s²,t²}` at `|ξ|²/2` (`charFun_bind_gaussVar`), which the causal kernels'
hypothesis evaluates. Clause (1): `F ∈ 𝒜_{d'}` for every `d'` by `ScaleSpace.bridge_exponents`
([B, Lem. 4.2]) and the law `μ_{0,1}` with residuals `μ_{c,1}`; the family axioms by
`isotropic_classification_sufficiency` with `χ = id`, the action `S_λ t = λt` checked on the
transform. Clauses (2)–(3) are exponent identities. Clause (4): `ScaleSpace.student_transform` and
`ScaleSpace.bridge_families_bessel` give the transform on the line, read at `ω = t|ξ|`; under the
hypothesis the kernels `μ_{0,t}` and the mixtures have the same transform (the Laplace transform of
`μ^I_{0,1}` at `t²|ξ|²/2`), so they are equal, without a separate Laplace uniqueness.

All of these are read from the shared library `ScaleSpaceCore` (v0.4.0: `bridge_exponents` since
v0.3.0, the Student-t and inverse-gamma material moved from Paper V's package by Q-0363), Lean
core; until this module's switch to v0.4.0 they were read from Paper V's package, the exponent
clause through a shim, because Paper V's `SpatialLine.BridgeExponents` declares the shared
library's `ScaleSpace.CausalAdmissible.bridgeProfile` and its siblings and could not be imported
beside `ScaleSpaceCore.BridgeExponents`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The transform of the bridge family -/

theorem IsCausalKernels.isProbability_sq {FI : ScaleSpace.CausalAdmissible} {μI : ℝ → ℝ → Measure ℝ}
    (hμI : IsCausalKernels FI μI) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsProbabilityMeasure (μI (s ^ 2) (t ^ 2)) :=
  hμI.isProbability _ _ (sq_nonneg s) (pow_le_pow_left₀ hs hst 2)

theorem isProbabilityMeasure_bridgeFamily {FI : ScaleSpace.CausalAdmissible}
    {μI : ℝ → ℝ → Measure ℝ} (hμI : IsCausalKernels FI μI) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsProbabilityMeasure (bridgeFamily d μI s t) := by
  haveI := hμI.isProbability_sq hs hst
  exact isProbabilityMeasure_bind_gaussVar _

/-- **The transform of the bridge family**: `μ̂_{s,t}(ξ) = exp[-(F_I(t²|ξ|²/2) - F_I(s²|ξ|²/2))]`. -/
theorem charFun_bridgeFamily {FI : ScaleSpace.CausalAdmissible} {μI : ℝ → ℝ → Measure ℝ}
    (hμI : IsCausalKernels FI μI) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ξ : Rd d) :
    charFun (bridgeFamily d μI s t) ξ =
      ((Real.exp (-(FI.exponent ((t * ‖ξ‖) ^ 2 / 2) - FI.exponent ((s * ‖ξ‖) ^ 2 / 2))) : ℝ) : ℂ) := by
  haveI := hμI.isProbability_sq hs hst
  rw [bridgeFamily, charFun_bind_gaussVar _ (hμI.support _ _ (sq_nonneg s)
    (pow_le_pow_left₀ hs hst 2)) ξ]
  have h := hμI.laplace _ _ (sq_nonneg s) (pow_le_pow_left₀ hs hst 2) (‖ξ‖ ^ 2 / 2) (by positivity)
  have heq : (fun u => Real.exp (-(u * ‖ξ‖ ^ 2) / 2)) = fun u => Real.exp (-(‖ξ‖ ^ 2 / 2 * u)) := by
    ext u; congr 1; ring
  rw [heq, h]
  congr 4 <;> ring_nf

/-! ## `prop:isotropic-bridge`(1) -/

/-- **`prop:isotropic-bridge`(1)**: the mixtures `μ_{s,t} := ∫ g^{(d)}_u μ^I_{s²,t²}(du)` form an
isotropic cascade family with `S_λ t = λt` and `μ̂_{s,t}(ξ) = exp[-(F(t|ξ|) - F(s|ξ|))]`,
`F(r) := F_I(r²/2)`; and `F ∈ 𝒜_d` for every `d ≥ 1`. -/
theorem isotropic_bridge_family (hd : 1 ≤ d) (FI : ScaleSpace.CausalAdmissible)
    (hFI : ∃ σ : ℝ, 0 ≤ σ ∧ FI.exponent σ ≠ 0) (μI : ℝ → ℝ → Measure ℝ)
    (hμI : IsCausalKernels FI μI) :
    IsIsotropicCascadeFamily (bridgeFamily d μI) (fun lam t => lam * t) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (bridgeFamily d μI s t) ξ =
        ((Real.exp (-(FI.exponent ((t * ‖ξ‖) ^ 2 / 2) - FI.exponent ((s * ‖ξ‖) ^ 2 / 2))) : ℝ) : ℂ)) ∧
      ∀ d' : ℕ, 1 ≤ d' → classA d' (fun r => FI.exponent (r ^ 2 / 2)) := by
  set F : ℝ → ℝ := fun r => FI.exponent (r ^ 2 / 2) with hF
  have hdisp := fun s t (hs : (0 : ℝ) ≤ s) (hst : s ≤ t) (ξ : Rd d) =>
    charFun_bridgeFamily (d := d) hμI hs hst ξ
  -- `F ∈ 𝒜_{d'}` for every `d'`: [B, Lem. 4.2] (the shared library's `bridge_exponents`) and the
  -- law `μ_{0,1}` with residuals `μ_{c,1}`
  have hclass : ∀ d' : ℕ, 1 ≤ d' → classA d' F := by
    intro d' _
    obtain ⟨Q, -, -, hQ⟩ := ScaleSpace.bridge_exponents FI
    refine ⟨⟨Q, fun r _ => (hQ r).symm⟩, bridgeFamily d' μI 0 1,
      isProbabilityMeasure_bridgeFamily hμI le_rfl zero_le_one, ?_, fun ξ => ?_⟩
    · haveI := isProbabilityMeasure_bridgeFamily (d := d') hμI le_rfl zero_le_one
      rw [ScaleSpace.isSelfDecomposable_iff_charFun]
      intro c hc0 hc1
      refine ⟨bridgeFamily d' μI c 1, isProbabilityMeasure_bridgeFamily hμI hc0.le hc1.le,
        fun ξ => ?_⟩
      rw [charFun_bridgeFamily hμI le_rfl zero_le_one, charFun_bridgeFamily hμI le_rfl zero_le_one,
        charFun_bridgeFamily hμI hc0.le hc1.le, ← Complex.ofReal_mul, ← Real.exp_add, norm_smul,
        Real.norm_of_nonneg hc0.le]
      congr 3
      simp only [zero_mul, one_mul]
      rw [show (0 : ℝ) ^ 2 / 2 = 0 by norm_num, FI.exponent_zero]
      ring_nf
    · rw [charFun_bridgeFamily hμI le_rfl zero_le_one]
      simp only [zero_mul, one_mul]
      rw [show (0 : ℝ) ^ 2 / 2 = 0 by norm_num, FI.exponent_zero, sub_zero]
  have hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0 := by
    obtain ⟨σ, hσ, hne⟩ := hFI
    refine ⟨Real.sqrt (2 * σ), Real.sqrt_nonneg _, ?_⟩
    show FI.exponent (Real.sqrt (2 * σ) ^ 2 / 2) ≠ 0
    rw [Real.sq_sqrt (by linarith)]
    convert hne using 2
    ring
  have hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (bridgeFamily d μI s t) :=
    fun s t hs hst => isProbabilityMeasure_bridgeFamily hμI hs hst
  have hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (bridgeFamily d μI s t) ξ =
      ((Real.exp (-(F (id t * ‖ξ‖) - F (id s * ‖ξ‖))) : ℝ) : ℂ) := hdisp
  have hid : IsGauge id := ⟨rfl, strictMonoOn_id, fun y hy => ⟨y, hy, rfl⟩⟩
  obtain ⟨S, hS⟩ := isotropic_classification_sufficiency hd (bridgeFamily d μI) hprob id F hid
    (hclass d hd) hFne hrep
  refine ⟨{ hS with
    scale_bij := fun lam hlam =>
      ⟨fun t (ht : 0 ≤ t) => (show 0 ≤ lam * t by positivity),
        fun x _ y _ hxy => mul_lt_mul_of_pos_left hxy hlam,
        fun y (hy : 0 ≤ y) => ⟨y / lam, (show 0 ≤ y / lam by positivity), by field_simp⟩⟩
    scale := fun lam hlam s t hs hst => by
      haveI := hprob s t hs hst
      haveI := hprob (lam * s) (lam * t) (by positivity) (mul_le_mul_of_nonneg_left hst hlam.le)
      refine eq_of_charFun_eq fun ξ => ?_
      rw [charFun_push_smul_one, hdisp s t hs hst, hdisp _ _ (by positivity)
        (mul_le_mul_of_nonneg_left hst hlam.le), norm_smul, Real.norm_of_nonneg hlam.le]
      congr 5 <;> ring_nf }, hdisp, hclass⟩

/-! ## `prop:isotropic-bridge`(2)–(3), the corners -/

/-- **`prop:isotropic-bridge`(2)**, the Matérn corner: if `F_I(σ) = γ log(1 + σ)`, `γ > 0`, then
`F(r) = γ log(1 + r²/2)` and `μ̂_{0,t}(ξ) = (1 + t²|ξ|²/2)^{-γ}`. -/
theorem isotropic_bridge_matern (_hd : 1 ≤ d) (FI : ScaleSpace.CausalAdmissible)
    (_hFI : ∃ σ : ℝ, 0 ≤ σ ∧ FI.exponent σ ≠ 0) (μI : ℝ → ℝ → Measure ℝ)
    (hμI : IsCausalKernels FI μI) {γ : ℝ} (_hγ : 0 < γ)
    (hFγ : ∀ σ : ℝ, 0 ≤ σ → FI.exponent σ = γ * Real.log (1 + σ)) :
    (∀ r : ℝ, 0 ≤ r → FI.exponent (r ^ 2 / 2) = γ * Real.log (1 + r ^ 2 / 2)) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ξ : Rd d, charFun (bridgeFamily d μI 0 t) ξ =
        (((1 + t ^ 2 * ‖ξ‖ ^ 2 / 2) ^ (-γ) : ℝ) : ℂ) := by
  refine ⟨fun r _ => hFγ _ (by positivity), fun t ht ξ => ?_⟩
  rw [charFun_bridgeFamily hμI le_rfl ht, zero_mul, show (0 : ℝ) ^ 2 / 2 = 0 by norm_num,
    FI.exponent_zero, sub_zero, hFγ _ (by positivity)]
  congr 1
  have hpos : 0 < 1 + t ^ 2 * ‖ξ‖ ^ 2 / 2 := by positivity
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  rw [mul_pow]
  ring

/-- **`prop:isotropic-bridge`(3)**, the stable corner: if `F_I(σ) = σ^α`, `0 < α ≤ 1`, then
`F(r) = 2^{-α} r^{2α}` and `μ̂_{0,t}(ξ) = exp(-2^{-α} t^{2α} |ξ|^{2α})`; at `α = 1`,
`μ_{s,t} = g^{(d)}_{t²-s²}`. -/
theorem isotropic_bridge_stable (_hd : 1 ≤ d) (FI : ScaleSpace.CausalAdmissible)
    (_hFI : ∃ σ : ℝ, 0 ≤ σ ∧ FI.exponent σ ≠ 0) (μI : ℝ → ℝ → Measure ℝ)
    (hμI : IsCausalKernels FI μI) {α : ℝ} (_hα0 : 0 < α) (_hα1 : α ≤ 1)
    (hFα : ∀ σ : ℝ, 0 ≤ σ → FI.exponent σ = σ ^ α) :
    (∀ r : ℝ, 0 ≤ r → FI.exponent (r ^ 2 / 2) = 2 ^ (-α) * r ^ (2 * α)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ ξ : Rd d, charFun (bridgeFamily d μI 0 t) ξ =
        ((Real.exp (-(2 ^ (-α) * t ^ (2 * α) * ‖ξ‖ ^ (2 * α))) : ℝ) : ℂ)) ∧
      (α = 1 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → bridgeFamily d μI s t = gaussVar d (t ^ 2 - s ^ 2)) := by
  have hF : ∀ r : ℝ, 0 ≤ r → FI.exponent (r ^ 2 / 2) = 2 ^ (-α) * r ^ (2 * α) := by
    intro r hr
    rw [hFα _ (by positivity), Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg
      (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hr]
    push_cast
    ring
  refine ⟨hF, fun t ht ξ => ?_, fun hα s t hs hst => ?_⟩
  · rw [charFun_bridgeFamily hμI le_rfl ht, zero_mul, show (0 : ℝ) ^ 2 / 2 = 0 by norm_num,
      FI.exponent_zero, sub_zero, hF _ (by positivity), Real.mul_rpow ht (norm_nonneg ξ)]
    congr 3
    ring
  · haveI := isProbabilityMeasure_bridgeFamily (d := d) hμI hs hst
    refine eq_of_charFun_eq fun ξ => ?_
    have hts : 0 ≤ t ^ 2 - s ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ hs hst 2)
    rw [charFun_bridgeFamily hμI hs hst, charFun_gaussVar hts, hFα _ (by positivity),
      hFα _ (by positivity), hα, Real.rpow_one, Real.rpow_one]
    congr 2
    ring

/-! ## `prop:isotropic-bridge-student` -/

/-- **`prop:isotropic-bridge-student`** (`prop:isotropic-bridge`(4)), the transform sentence: for
`ϑ > 0` and `t > 0` the Gaussian variance mixture `∫ g^{(d)}_u P(t²T₁ ∈ du)`, `T₁` the scaled
inverse-gamma law of shape `ϑ`, is a probability measure with transform
`2^{1-ϑ}Γ(ϑ)⁻¹ (t|ξ|)^ϑ K_ϑ(t|ξ|)` at `ξ ≠ 0`. -/
theorem isotropic_bridge_student_transform (_hd : 1 ≤ d) {ϑ t : ℝ} (hϑ : 0 < ϑ) (ht : 0 < t) :
    IsProbabilityMeasure
        (((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)).bind (gaussVar d)) ∧
      ∀ ξ : Rd d, ξ ≠ 0 →
        charFun (((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)).bind (gaussVar d)) ξ =
          ((2 ^ (1 - ϑ) / Real.Gamma ϑ * (t * ‖ξ‖) ^ ϑ * ScaleSpace.besselK ϑ (t * ‖ξ‖) : ℝ) : ℂ) := by
  haveI := ScaleSpace.isProbabilityMeasure_inverseGammaLaw hϑ
  have hmeas : Measurable fun u : ℝ => t ^ 2 * u := measurable_const.mul measurable_id
  haveI : IsProbabilityMeasure ((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ⟨isProbabilityMeasure_bind_gaussVar _, fun ξ hξ => ?_⟩
  have hsupp : ((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)) (Iio 0) = 0 := by
    rw [Measure.map_apply hmeas measurableSet_Iio]
    refine measure_mono_null (fun u (hu : t ^ 2 * u < 0) => ?_)
      (ScaleSpace.inverseGammaLaw_Iio_zero ϑ)
    show u < 0
    by_contra h
    push Not at h
    have : 0 ≤ t ^ 2 * u := by positivity
    linarith
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hω : t * ‖ξ‖ ≠ 0 := (mul_pos ht hξ0).ne'
  rw [charFun_bind_gaussVar _ hsupp ξ, integral_map hmeas.aemeasurable (by fun_prop)]
  have h1 := ScaleSpace.fourierCos_bind_brownianLaw (ScaleSpace.inverseGammaLaw_Iio_zero ϑ)
    (t * ‖ξ‖)
  rw [ScaleSpace.bridge_families_bessel ϑ hϑ, ScaleSpace.student_transform hϑ _ hω,
    abs_of_pos (mul_pos ht hξ0)] at h1
  congr 1
  rw [h1]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  congr 1
  ring

/-- **`prop:isotropic-bridge-student`** (`prop:isotropic-bridge`(4)), the conditional sentence: if
`μ^I_{0,1}` is the law of `T₁`, the mixtures are the kernels `μ_{0,t}` of (1), and their exponent is
in `𝒜_d`. -/
theorem isotropic_bridge_student_family (hd : 1 ≤ d) (FI : ScaleSpace.CausalAdmissible)
    (hFI : ∃ σ : ℝ, 0 ≤ σ ∧ FI.exponent σ ≠ 0) (μI : ℝ → ℝ → Measure ℝ)
    (hμI : IsCausalKernels FI μI) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hT : μI 0 1 = ScaleSpace.inverseGammaLaw ϑ) :
    (∀ t : ℝ, 0 < t → bridgeFamily d μI 0 t =
        ((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)).bind (gaussVar d)) ∧
      classA d (fun r => FI.exponent (r ^ 2 / 2)) := by
  refine ⟨fun t ht => ?_, (isotropic_bridge_family hd FI hFI μI hμI).2.2 d hd⟩
  haveI := ScaleSpace.isProbabilityMeasure_inverseGammaLaw hϑ
  have hmeas : Measurable fun u : ℝ => t ^ 2 * u := measurable_const.mul measurable_id
  haveI : IsProbabilityMeasure ((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  haveI := isProbabilityMeasure_bridgeFamily (d := d) hμI le_rfl ht.le
  haveI := (isotropic_bridge_student_transform (d := d) hd hϑ ht).1
  have hsupp : ((ScaleSpace.inverseGammaLaw ϑ).map (fun u => t ^ 2 * u)) (Iio 0) = 0 := by
    rw [Measure.map_apply hmeas measurableSet_Iio]
    refine measure_mono_null (fun u (hu : t ^ 2 * u < 0) => ?_)
      (ScaleSpace.inverseGammaLaw_Iio_zero ϑ)
    show u < 0
    by_contra h
    push Not at h
    have : 0 ≤ t ^ 2 * u := by positivity
    linarith
  refine eq_of_charFun_eq fun ξ => ?_
  rw [charFun_bind_gaussVar _ hsupp ξ, integral_map hmeas.aemeasurable (by fun_prop),
    charFun_bridgeFamily hμI le_rfl ht.le]
  -- the Laplace transform of `μ^I_{0,1}` at `t²|ξ|²/2`
  have h := hμI.laplace 0 1 le_rfl zero_le_one (t ^ 2 * (‖ξ‖ ^ 2 / 2)) (by positivity)
  rw [hT] at h
  rw [zero_mul, show (0 : ℝ) ^ 2 / 2 = 0 by norm_num, FI.exponent_zero, sub_zero]
  congr 1
  have h2 : ∫ u, Real.exp (-(t ^ 2 * u * ‖ξ‖ ^ 2) / 2) ∂(ScaleSpace.inverseGammaLaw ϑ)
      = ∫ u, Real.exp (-(t ^ 2 * (‖ξ‖ ^ 2 / 2) * u)) ∂(ScaleSpace.inverseGammaLaw ϑ) := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    congr 1
    ring
  rw [h2, h, zero_mul, FI.exponent_zero, sub_zero]
  congr 2
  ring_nf

end AffineHemigroup
