/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.RadialTransform
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.Defs.IsotropicFamily
import ScaleSpaceCore.TransformBridge

/-!
# `lem:radial-marginal` — a rotation-invariant law is determined by its marginal

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:radial-marginal`. Lean core only: the
uniqueness of the transform is Mathlib's `Measure.ext_of_charFun`, on `ℝ` and on `ℝ^d`, and the
radial form of a rotation-invariant transform is `charFun_eq_of_norm_eq`
(`AffineHemigroup.RayFamilies`, the reflection in `(ω - ω')^⊥`).

## The route

The blueprint's. The one computation is `charFun_marginal`, `\widehat{π_*μ}(ω) = μ̂(ωe)`, the
image of a measure under `π = ⟨e, ·⟩` read through `integral_map`; with it, (1) is
`charFun_eq_of_norm_eq` at `ξ` and `|ξ| e`, symmetry of `π_*μ` is invariance under `-I ∈ O(d)`
read on the image, and independence of `e` is uniqueness of the transform on `ℝ`. Instead of an
orthogonal `Q` with `Qe = ξ/|ξ|` the reflection of `charFun_eq_of_norm_eq` is used, which covers
`ξ = 0` without a separate case. (3) is Mathlib's `Measure.map_conv_continuousLinearMap` for the
continuous linear map `innerSL ℝ e`, and `Measure.map_map`.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- The projection `π = ⟨e, ·⟩` is continuous. -/
theorem continuous_inner_left (e : Rd d) : Continuous fun x : Rd d => ⟪e, x⟫ :=
  continuous_const.inner continuous_id

/-- The marginal of a probability measure is a probability measure. -/
instance isProbabilityMeasure_marginal (e : Rd d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (marginal e μ) :=
  Measure.isProbabilityMeasure_map (continuous_inner_left e).aemeasurable

/-- **The transform of a marginal**: `\widehat{π_*μ}(ω) = μ̂(ωe)`. -/
theorem charFun_marginal (e : Rd d) (μ : Measure (Rd d)) (ω : ℝ) :
    charFun (marginal e μ) ω = charFun μ (ω • e) := by
  rw [marginal, charFun_apply, charFun_apply, integral_map (continuous_inner_left e).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  ext x
  congr 3
  rw [RCLike.inner_apply, conj_trivial, real_inner_smul_right, real_inner_comm]

/-- `-I` is orthogonal. -/
theorem neg_one_mem_orthSet : (-1 : Mat d) ∈ orthSet d :=
  (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 (by simp)

/-- `lin (-I) x = -x`. -/
theorem lin_neg_one_apply (x : Rd d) : lin (-1 : Mat d) x = -x := by
  have h : (-1 : Mat d) = (-1 : ℝ) • (1 : Mat d) := by simp
  rw [h, lin_smul, lin_one]
  simp

/-- **`lem:radial-marginal`(1)**: for a rotation-invariant probability measure `μ`, the marginal
`κ := π_*μ` along a unit vector `e` is a symmetric probability measure with `μ̂(ξ) = κ̂(|ξ|)`; in
particular `μ̂` is real and radial, and `κ` does not depend on `e`. -/
theorem radial_marginal (_hd : 1 ≤ d) (e : Rd d) (he : ‖e‖ = 1) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hrot : IsRotationInvariant μ) :
    IsProbabilityMeasure (marginal e μ) ∧ ScaleSpace.IsSymmetric (marginal e μ) ∧
      (∀ ξ : Rd d, charFun μ ξ = charFun (marginal e μ) ‖ξ‖) ∧
      (∀ ξ : Rd d, (charFun μ ξ).im = 0) ∧
      (∀ ξ ξ' : Rd d, ‖ξ‖ = ‖ξ'‖ → charFun μ ξ = charFun μ ξ') ∧
      ∀ e' : Rd d, ‖e'‖ = 1 → marginal e' μ = marginal e μ := by
  -- Symmetry: invariance under `-I`, read on the image.
  have hsym : ScaleSpace.IsSymmetric (marginal e μ) := by
    unfold ScaleSpace.IsSymmetric marginal
    rw [Measure.map_map measurable_neg (continuous_inner_left e).measurable]
    conv_rhs => rw [← hrot (-1) neg_one_mem_orthSet, push,
      Measure.map_map (continuous_inner_left e).measurable (lin (-1 : Mat d)).measurable]
    congr 1
    ext x
    simp [Function.comp, lin_neg_one_apply, inner_neg_right]
  -- The radial form.
  have hrad : ∀ ξ : Rd d, charFun μ ξ = charFun (marginal e μ) ‖ξ‖ := by
    intro ξ
    rw [charFun_marginal]
    exact charFun_eq_of_norm_eq hrot (by rw [norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ξ)])
  refine ⟨inferInstance, hsym, hrad, fun ξ => ?_, fun ξ ξ' h => charFun_eq_of_norm_eq hrot h,
    fun e' he' => ?_⟩
  · rw [hrad ξ, ScaleSpace.charFun_eq_fourierCos_of_symmetric hsym]
    exact Complex.ofReal_im _
  · refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_marginal, charFun_marginal]
    exact charFun_eq_of_norm_eq hrot (by rw [norm_smul, norm_smul, he, he'])

/-- **`lem:radial-marginal`(2)**: under the hypothesis of (1), `π_*μ = δ₀` if and only if
`μ = δ₀`. -/
theorem radial_marginal_eq_dirac (hd : 1 ≤ d) (e : Rd d) (he : ‖e‖ = 1) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hrot : IsRotationInvariant μ) :
    marginal e μ = Measure.dirac 0 ↔ μ = Measure.dirac 0 := by
  constructor
  · intro h
    obtain ⟨-, -, hrad, -⟩ := radial_marginal hd e he μ hrot
    refine eq_of_charFun_eq fun ξ => ?_
    rw [hrad ξ, h, charFun_dirac, charFun_dirac]
    simp
  · intro h
    rw [h, marginal, Measure.map_dirac' (continuous_inner_left e).measurable]
    simp

/-- **`lem:radial-marginal`(3)**: for probability measures `μ, μ'` on `ℝ^d` and `λ > 0`,
`π_*(μ ∗ μ') = π_*μ ∗ π_*μ'`, `π_*((λI)_*μ) = (λI)_*(π_*μ)` and `π_*δ₀ = δ₀`. -/
theorem radial_marginal_ops (_hd : 1 ≤ d) (e : Rd d) (_he : ‖e‖ = 1) (μ μ' : Measure (Rd d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (lam : ℝ) (_hlam : 0 < lam) :
    marginal e (μ ∗ μ') = marginal e μ ∗ marginal e μ' ∧
      marginal e (push (lam • (1 : Mat d)) μ) = (marginal e μ).map (fun y => lam * y) ∧
      marginal e (Measure.dirac (0 : Rd d)) = Measure.dirac 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Measure.map_conv_continuousLinearMap (innerSL ℝ e)
  · rw [marginal, marginal, push, Measure.map_map (continuous_inner_left e).measurable
      (lin _).measurable, Measure.map_map (continuous_const_mul lam).measurable
      (continuous_inner_left e).measurable]
    congr 1
    ext x
    simp [Function.comp, lin_smul, lin_one, real_inner_smul_right]
  · rw [marginal, Measure.map_dirac' (continuous_inner_left e).measurable]
    simp

end AffineHemigroup
