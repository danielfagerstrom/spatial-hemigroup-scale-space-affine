/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.GaussVar
import AffineHemigroup.PositiveTransform
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Gaussian variance mixtures on `ℝ^d`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, the mixtures `∫ g^{(d)}_u ρ(du)` of
`prop:origin-boundedness-subordinated`, `lem:delay-polar-profile` and `prop:isotropic-bridge`, which
Lean writes as `ρ.bind (gaussVar d)`. Wave 2, group A (Q-0281).

* `gaussVar_eq_withDensity`: for `u > 0`, `g^{(d)}_u` has the density `g_u` (the heat kernel),
  by the uniqueness of the Fourier transform and the Gaussian Fourier integral;
* `integral_bind_gaussVar`: integrals against the mixture are iterated integrals, through Mathlib's
  kernel composition (`Kernel.integral_comp`);
* `charFun_bind_gaussVar`: the transform of the mixture at `ξ` is the Laplace transform of the mixing
  law at `|ξ|²/2`, for a mixing law carried by `[0,∞)`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Complex ProbabilityTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-- **`g^{(d)}_u` has the density `g_u`** for `u > 0`: both are finite measures with transform
`e^{-u|ξ|²/2}`. -/
theorem gaussVar_eq_withDensity {u : ℝ} (hu : 0 < u) :
    gaussVar d u = volume.withDensity (fun x => ENNReal.ofReal (heatKernel d u x)) := by
  haveI : IsFiniteMeasure (volume.withDensity fun x : Rd d => ENNReal.ofReal (heatKernel d u x)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_heatKernel_volume hu]
    exact ENNReal.one_lt_top
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_gaussVar hu.le, charFun_apply]
  have hdens : (fun x : Rd d => ENNReal.ofReal (heatKernel d u x))
      = fun x => ((Real.toNNReal (heatKernel d u x) : ℝ≥0) : ℝ≥0∞) := by
    funext x; rfl
  rw [hdens, integral_withDensity_eq_integral_smul
    ((continuous_heatKernel.measurable).real_toNNReal)]
  have hpt : ∀ x : Rd d, (Real.toNNReal (heatKernel d u x)) • cexp (↑⟪x, ξ⟫ * I)
      = (((2 * Real.pi * u) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        cexp (-((1 / (2 * u) : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + I * (⟪ξ, x⟫ : ℂ)) := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (heatKernel_nonneg hu x), heatKernel_eq_gauss,
      real_inner_comm, Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using (by positivity : (0 : ℝ) < 1 / (2 * u))) I ξ, finrank_Rd]
  have h1 : ((Real.pi : ℂ) / ((1 / (2 * u) : ℝ) : ℂ)) ^ ((d : ℂ) / 2)
      = (((2 * Real.pi * u) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / ((1 / (2 * u) : ℝ) : ℂ)) = ((2 * Real.pi * u : ℝ) : ℂ) by
        push_cast; field_simp,
      Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have h2 : I ^ 2 * ((‖ξ‖ : ℂ)) ^ 2 / (4 * ((1 / (2 * u) : ℝ) : ℂ))
      = ((-(u * ‖ξ‖ ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast
    rw [I_sq]
    field_simp
    ring
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity),
    show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one, one_mul,
    Complex.ofReal_exp]

/-- The mixture kernel `u ↦ g^{(d)}_u` as a Markov kernel. -/
noncomputable def gaussVarKernel (d : ℕ) : Kernel ℝ (Rd d) := ⟨gaussVar d, measurable_gaussVar d⟩

instance (d : ℕ) : IsMarkovKernel (gaussVarKernel d) :=
  ⟨fun u => isProbabilityMeasure_gaussVar d u⟩

theorem bind_gaussVar_eq (ρ : Measure ℝ) :
    ρ.bind (gaussVar d) = (gaussVarKernel d ∘ₖ Kernel.const Unit ρ) () := by
  rw [← Measure.comp_eq_comp_const_apply]
  rfl

/-- The mixture of probability measures is a probability measure. -/
theorem isProbabilityMeasure_bind_gaussVar (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (ρ.bind (gaussVar d)) :=
  isProbabilityMeasure_bind (measurable_gaussVar d).aemeasurable
    (.of_forall fun u => isProbabilityMeasure_gaussVar d u)

/-- **Integrals against the mixture are iterated integrals.** -/
theorem integral_bind_gaussVar (ρ : Measure ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Rd d → E} (hf : Integrable f (ρ.bind (gaussVar d))) :
    ∫ x, f x ∂(ρ.bind (gaussVar d)) = ∫ u, ∫ x, f x ∂(gaussVar d u) ∂ρ := by
  rw [bind_gaussVar_eq] at hf ⊢
  rw [Kernel.integral_comp hf]
  simp only [Kernel.const_apply]
  rfl

/-- **The transform of a Gaussian variance mixture** with mixing law carried by `[0,∞)`:
`\widehat{∫ g^{(d)}_u ρ(du)}(ξ) = ∫ e^{-u|ξ|²/2} ρ(du)`. -/
theorem charFun_bind_gaussVar (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ0 : ρ (Iio 0) = 0)
    (ξ : Rd d) :
    charFun (ρ.bind (gaussVar d)) ξ = ((∫ u, Real.exp (-(u * ‖ξ‖ ^ 2) / 2) ∂ρ : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_bind_gaussVar (d := d) ρ
  have hae : ∀ᵐ u ∂ρ, 0 ≤ u := by
    rw [ae_iff]
    convert hρ0 using 2
    ext u; simp
  have hint : Integrable (fun x : Rd d => cexp (↑⟪x, ξ⟫ * I)) (ρ.bind (gaussVar d)) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply, integral_bind_gaussVar ρ hint, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hae] with u hu
  rw [← charFun_apply, charFun_gaussVar hu]

end AffineHemigroup
