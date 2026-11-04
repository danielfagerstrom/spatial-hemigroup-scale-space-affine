/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.Defs.Divisibility
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The transform of a self-decomposable law and of a rotation-invariant law

Three facts on transforms that the isotropic theory reads. A self-decomposable probability
measure on `ℝ^d` has a transform without zeros, and its images under matrices are
self-decomposable (`selfDecomposable_charFun_ne_zero`, which is `prop:gw-ray-families`(1); the
argument is the shared library's). A rotation-invariant law has a radial transform
(`charFun_eq_of_norm_eq`, `charFun_eq_norm_smul_ebasis`), by the reflection in `(ω - ω')^⊥`.
And a rotation-invariant law whose transform has no zero has `μ̂(ω) = e^{-g(|ω|²)}` with `g`
continuous and nonnegative on `[0,∞)`, `g(0) = 0` (`exists_exp_of_rotationInvariant`). Lean core
only.

The first three stood in `AffineHemigroup.RayFamilies` and the fourth in
`AffineHemigroup.ShapeAdapted`; both import this file. They are here unchanged, each with the
`open` lines of its file (Q-0452).
-/

namespace AffineHemigroup

/-! ## From `AffineHemigroup.RayFamilies` -/

section

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)
open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-- **`prop:gw-ray-families`(1)**: a self-decomposable probability measure on `ℝ^d` has a transform
without zeros, and every image `T_*μ` under a real `d × d` matrix is self-decomposable. -/
theorem selfDecomposable_charFun_ne_zero (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposable μ) :
    (∀ ξ : Rd d, charFun μ ξ ≠ 0) ∧ ∀ T : Mat d, IsSelfDecomposable (push T μ) := by
  refine ⟨hμ.charFun_ne_zero, fun T => ?_⟩
  exact hμ.map (lin T)

/-- **A rotation-invariant law has a radial transform**: `μ̂(ω) = μ̂(ω')` when `|ω| = |ω'|`, by
invariance under the reflection in `(ω - ω')^⊥`. -/
theorem charFun_eq_of_norm_eq {μ : Measure (Rd d)} (hμ : IsRotationInvariant μ) {ω ω' : Rd d}
    (h : ‖ω‖ = ‖ω'‖) : charFun μ ω = charFun μ ω' := by
  set e : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (ω - ω'))ᗮ with he
  set A : Mat d :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (e.symm : Rd d →L[ℝ] Rd d) with hAdef
  have hlinA : lin A = (e.symm : Rd d →L[ℝ] Rd d) := by
    simp only [lin, hAdef, StarAlgEquiv.apply_symm_apply]
  have hlinAT : lin Aᵀ = (e : Rd d →L[ℝ] Rd d) := by
    rw [lin_transpose, hlinA, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  have hAAT : A * Aᵀ = 1 := by
    apply lin_injective
    rw [lin_mul, hlinA, hlinAT, lin_one]
    ext x
    simp
  have hA : A ∈ orthSet d := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hAAT
  have h2 : charFun (push A μ) ω = charFun μ (e ω) := by
    rw [push, charFun_map_lin, hlinAT]
    rfl
  rw [hμ A hA] at h2
  rw [h2, he, Submodule.reflection_sub h]

/-- The radial form: `μ̂(ω) = μ̂(|ω| e₁)` for a rotation-invariant `μ`. -/
theorem charFun_eq_norm_smul_ebasis [NeZero d] {μ : Measure (Rd d)} (hμ : IsRotationInvariant μ)
    (ω : Rd d) : charFun μ ω = charFun μ (‖ω‖ • ebasis 0) := by
  apply charFun_eq_of_norm_eq hμ
  simp [ebasis, norm_smul]

end

/-! ## From `AffineHemigroup.ShapeAdapted` -/

section

open MeasureTheory Set Matrix ProbabilityTheory Module
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- A rotation-invariant law whose transform has no zero has `μ̂(ω) = e^{-g(|ω|²)}` with `g`
continuous on `[0,∞)`, nonnegative, `g(0) = 0`: the hypotheses of `prop:affine-orbits`. -/
theorem exists_exp_of_rotationInvariant [NeZero d] (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hrot : IsRotationInvariant μ) (hz : ∀ ξ : Rd d, charFun μ ξ ≠ 0) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      ∀ ω : Rd d, charFun μ ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  set φ : ℝ → ℂ := fun u => charFun μ (Real.sqrt u • ebasis 0) with hφdef
  have hφ : ∀ ω : Rd d, charFun μ ω = φ (‖ω‖ ^ 2) := by
    intro ω
    rw [charFun_eq_norm_smul_ebasis hrot ω, hφdef]
    simp only [Real.sqrt_sq (norm_nonneg ω)]
  have hφcont : Continuous φ :=
    continuous_charFun.comp (Real.continuous_sqrt.smul continuous_const)
  have hreal : ∀ ω : Rd d, (charFun μ ω).im = 0 := by
    intro ω
    have h1 : charFun μ (-ω) = charFun μ ω := charFun_eq_of_norm_eq hrot (norm_neg ω)
    rw [charFun_neg] at h1
    exact Complex.conj_eq_iff_im.1 h1
  set φr : ℝ → ℝ := fun u => (φ u).re with hφrdef
  have hφr : ∀ u : ℝ, φ u = (φr u : ℂ) := by
    intro u
    apply Complex.ext
    · simp [hφrdef]
    · simp only [Complex.ofReal_im]
      exact hreal _
  have hφr0 : φr 0 = 1 := by simp [hφrdef, hφdef, charFun_zero]
  have hφrcont : Continuous φr := Complex.continuous_re.comp hφcont
  have hφrle : ∀ u : ℝ, φr u ≤ 1 := fun u =>
    (Complex.re_le_norm _).trans (norm_charFun_le_one _)
  have hφrpos : ∀ u : ℝ, 0 ≤ u → 0 < φr u := by
    intro u hu
    by_contra hneg
    push Not at hneg
    obtain ⟨v, -, hv0⟩ := intermediate_value_Icc' hu hφrcont.continuousOn
      ⟨hneg, by rw [hφr0]; norm_num⟩
    apply hz (Real.sqrt v • ebasis 0)
    change φ v = 0
    rw [hφr, hv0, Complex.ofReal_zero]
  refine ⟨fun u => -Real.log (φr u), ?_, ?_, ?_, ?_⟩
  · exact (hφrcont.continuousOn.log fun u hu => (hφrpos u hu).ne').neg
  · intro u hu
    simp only [neg_nonneg]
    exact Real.log_nonpos (hφrpos u hu).le (hφrle u)
  · simp [hφr0]
  · intro ω
    rw [hφ, hφr, neg_neg, Real.exp_log (hφrpos _ (sq_nonneg _))]

end

end AffineHemigroup
