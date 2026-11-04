/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Operators
import AffineHemigroup.OperatorForm
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.RepresentationSpace
import ScaleSpaceCore.FourierPairingSpace

/-!
# `lem:operators-to-kernels`, clauses (1)–(3)

Blueprint: `blueprint/src/parts/04-classical.tex`. Q-0281, wave M, phase 2.

* **(1), representation**: `operators_to_kernels_repr`, from the `d`-dimensional port of [V,
  Lem. 4.1] (`AffineHemigroup.RepresentationSpace`); **uniqueness** `operators_to_kernels_unique`,
  from the pairing `(μ * f)^ = μ̂ f̂` (`ScaleSpace.charCLME_mconvL1E`), the transform of the
  standard Gaussian density, which has no zero (`charCLME_gaussL1_ne_zero`), and Mathlib's
  `Measure.ext_of_charFun`; **the converse** `operators_to_kernels_converse`, from the shared
  library's `mconvL1E` lemmas.
* **(2), transport**: the shared library's `ScaleSpace.dilL1E_comp_mconvL1E` and
  `ScaleSpace.dilL1E_conj_mconvL1E`, the converse by uniqueness.
* **(3), continuity**: the pairing at `φ`, divided by `φ̂(ω) ≠ 0`.

Clauses (4) and (5), the split child `lem:operators-to-kernels-families`, are
`AffineHemigroup.OperatorFamilies`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory Complex
open scoped Topology MatrixOrder RealInnerProductSpace
open ScaleSpace (transL1E dilL1E matEquiv mconvL1E charCLME)

variable {d : ℕ}

/-! ## The transform of the standard Gaussian density -/

/-- **`φ̂(ω) ≠ 0`**: the transform of the standard Gaussian density is
`(2π)^{-d/2} (2π)^{d/2} e^{-|ω|²/2}`, a product of nonzero factors. -/
theorem charCLME_gaussL1_ne_zero (ω : Rd d) : charCLME ω (gaussL1 d) ≠ 0 := by
  rw [ScaleSpace.charCLME_apply]
  have hcongr : ∫ x : Rd d, cexp (⟪x, ω⟫ * I) * (((gaussL1 d : L1 d) : Rd d → ℝ) x : ℂ)
      = (((2 * Real.pi) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          ∫ x : Rd d, cexp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + I * (⟪ω, x⟫ : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_gaussDensity d)] with x hx
    rw [show ((gaussL1 d : L1 d) : Rd d → ℝ) x = gaussDensity d x from hx, gaussDensity,
      ofReal_mul, ofReal_exp, mul_left_comm, ← Complex.exp_add, real_inner_comm]
    congr 2
    push_cast
    ring
  rw [hcongr, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num) I ω]
  refine mul_ne_zero (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne')
    (mul_ne_zero ?_ (Complex.exp_ne_zero _))
  intro h
  have h0 := ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero hpi (by norm_num) h0

/-! ## `lem:operators-to-kernels`(1): uniqueness, the converse, the representation -/

/-- `μ ∗ φ = ν ∗ φ` forces `μ = ν`, without the dimension hypothesis. -/
theorem eq_of_mconvL1E_gaussL1_eq {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : mconvL1E μ (gaussL1 d) = mconvL1E ν (gaussL1 d)) : μ = ν := by
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have hω := congrArg (charCLME ω) h
  rw [ScaleSpace.charCLME_mconvL1E, ScaleSpace.charCLME_mconvL1E] at hω
  exact mul_right_cancel₀ (charCLME_gaussL1_ne_zero ω) hω

/-- Two probability measures giving the same operator are equal. -/
theorem eq_of_mconvL1E_eq {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : mconvL1E μ = mconvL1E ν) : μ = ν :=
  eq_of_mconvL1E_gaussL1_eq (congrArg (fun T => T (gaussL1 d)) h)

/-- **`lem:operators-to-kernels`(1)**, uniqueness in the strong form: `μ ∗ φ = ν ∗ φ` in
`L¹(ℝ^d)` forces `μ = ν`, `φ` the standard Gaussian density. -/
theorem operators_to_kernels_unique (_hd : 1 ≤ d) (μ ν : Measure (Rd d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : mconvL1E μ (gaussL1 d) = mconvL1E ν (gaussL1 d)) : μ = ν :=
  eq_of_mconvL1E_gaussL1_eq h

/-- **`lem:operators-to-kernels`(1)**, the converse: for every probability measure `μ`, the
operator `f ↦ μ ∗ f` on `L¹(ℝ^d)` satisfies (A1), (A2), (A4), (A5). -/
theorem operators_to_kernels_converse (_hd : 1 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] :
    IsSingleOperator (mconvL1E μ) where
  translation a := ContinuousLinearMap.ext fun f => ScaleSpace.mconvL1E_transL1E μ a f
  positive _ hf := ScaleSpace.isNonnegE_mconvL1E μ hf
  mass f _ := ScaleSpace.integral_mconvL1E μ f

/-- **`lem:operators-to-kernels`(1)**, representation: a linear `Φ` on `L¹(ℝ^d)` with (A1),
(A2), (A4), (A5) is convolution by a unique probability measure, `Φ = μ ∗ ·`. -/
theorem operators_to_kernels_repr (_hd : 1 ≤ d) (Φ : L1 d →L[ℝ] L1 d)
    (hΦ : IsSingleOperator Φ) :
    ∃! μ : Measure (Rd d), ∃ _ : IsProbabilityMeasure μ, Φ = mconvL1E μ := by
  obtain ⟨μ, hμ, hΦμ⟩ := exists_isProbabilityMeasure_eq_mconvL1E (L := Φ)
    (fun a f => congrArg (fun T => T f) (hΦ.translation a)) (fun f hf => hΦ.positive f hf)
    (fun f hf => hΦ.mass f hf)
  refine ⟨μ, ⟨hμ, hΦμ⟩, fun ν ⟨hν, hΦν⟩ => ?_⟩
  exact eq_of_mconvL1E_eq (hΦν.symm.trans hΦμ)

/-! ## `lem:operators-to-kernels`(2): transport -/

/-- **`lem:operators-to-kernels`(2)**, transport: `D_A(μ ∗ f) = (A_*μ) ∗ D_A f`. -/
theorem operators_to_kernels_transport (_hd : 1 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (A : Mat d) (hA : A ∈ glSet d) (f : L1 d) :
    dilL1E (matEquiv A hA) (mconvL1E μ f) = mconvL1E (push A μ) (dilL1E (matEquiv A hA) f) := by
  haveI : IsFiniteMeasure (μ.map (matEquiv A hA)) :=
    (inferInstance : IsFiniteMeasure (push A μ))
  exact congrArg (fun T => T f) (ScaleSpace.dilL1E_comp_mconvL1E (matEquiv A hA) μ)

/-- The conjugation `D_A (μ ∗ ·) D_A⁻¹` is convolution by `A_* μ`. -/
theorem dil_conj_mconvL1E (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (A : Mat d)
    (hA : IsUnit A.det) :
    ((dilL1E (matEquiv A hA)).comp (mconvL1E μ)).comp (dilL1E (matEquiv A hA).symm) =
      mconvL1E (push A μ) :=
  ScaleSpace.dilL1E_conj_mconvL1E (matEquiv A hA) μ (push A μ) rfl

/-- **`lem:operators-to-kernels`(2)**, consequently: `D_A (μ ∗ ·) D_A⁻¹ = ν ∗ ·` if and only if
`A_*μ = ν`. -/
theorem operators_to_kernels_transport_iff (_hd : 1 ≤ d) (μ ν : Measure (Rd d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Mat d) (hA : A ∈ glSet d) :
    ((dilL1E (matEquiv A hA)).comp (mconvL1E μ)).comp (dilL1E (matEquiv A hA).symm) =
        mconvL1E ν ↔
      push A μ = ν := by
  rw [dil_conj_mconvL1E μ A hA]
  exact ⟨eq_of_mconvL1E_eq, fun h => ScaleSpace.mconvL1E_congr h⟩

/-! ## `lem:operators-to-kernels`(3): continuity -/

/-- The transform of `μ` at `ω` read off `μ ∗ φ`: `μ̂(ω) = (μ ∗ φ)^(ω) / φ̂(ω)`. -/
theorem charFun_eq_charCLME_div (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (ω : Rd d) :
    charFun μ ω = charCLME ω (mconvL1E μ (gaussL1 d)) * (charCLME ω (gaussL1 d))⁻¹ := by
  rw [ScaleSpace.charCLME_mconvL1E, mul_inv_cancel_right₀ (charCLME_gaussL1_ne_zero ω)]

/-- **`lem:operators-to-kernels`(3)**, continuity: `μ_n ∗ φ → μ ∗ φ` in `L¹(ℝ^d)` gives
`μ̂_n(ω) → μ̂(ω)` for every `ω`. -/
theorem operators_to_kernels_continuity (_hd : 1 ≤ d) (μn : ℕ → Measure (Rd d))
    [∀ n, IsProbabilityMeasure (μn n)] (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (h : Tendsto (fun n => mconvL1E (μn n) (gaussL1 d)) atTop (𝓝 (mconvL1E μ (gaussL1 d))))
    (ω : Rd d) :
    Tendsto (fun n => charFun (μn n) ω) atTop (𝓝 (charFun μ ω)) := by
  simp only [charFun_eq_charCLME_div]
  exact (((charCLME ω).continuous.tendsto _).comp h).mul_const _

end AffineHemigroup
