/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.Defs.Origin
import ScaleSpaceCore.GaussianKernel

/-!
# The Gaussian kernel `u ↦ g^{(d)}_u`: its form, its transform, its measurability

Blueprint: `blueprint/src/parts/03-isotropic.tex`; the presupposition of every mixture
`∫ g^{(d)}_u ρ(du)` the chapter writes as `ρ.bind (gaussVar d)`
(`prop:origin-boundedness-subordinated`, `prop:isotropic-bridge`, `prop:isotropic-bridge-student`;
blind review R2-2). Wave 2, group A (Q-0281).

`gaussVar d u` is Mathlib's `multivariateGaussian 0 (uI)`. For `u ≥ 0`, `(uI)^{1/2} = √u I`
(`msqrt_sq_smul_one`); for `u < 0` the matrix `uI` is not positive semidefinite (when `d ≥ 1`), its
square root is the junk `0`, and `√u = 0` too. So `gaussVar d u` is the image of the standard
Gaussian under `x ↦ √u x` for **every** real `u` (`gaussVar_eq_map`), from which the transform and
the measurability of `u ↦ g^{(d)}_u` follow; the measurability is the shared library's
(`ScaleSpaceCore.GaussianKernel`, SSL-9) since Q-0365.
-/

namespace AffineHemigroup

open MeasureTheory Set ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder

variable {d : ℕ}

/-- `(uI)^{1/2} = √u I` for every real `u` (for `u < 0` both sides are `0`). -/
theorem msqrt_smul_one (d : ℕ) (u : ℝ) : msqrt (u • (1 : Mat d)) = Real.sqrt u • (1 : Mat d) := by
  rcases le_or_gt 0 u with hu | hu
  · have h := msqrt_sq_smul_one (d := d) (Real.sqrt_nonneg u)
    rwa [Real.sq_sqrt hu] at h
  · rw [Real.sqrt_eq_zero_of_nonpos hu.le, zero_smul]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exact Subsingleton.elim _ _
    · refine CFC.sqrt_of_not_nonneg fun h => ?_
      have hpsd : (u • (1 : Mat d)).PosSemidef := by
        rwa [Matrix.nonneg_iff_posSemidef] at h
      have := hpsd.diag_nonneg (i := ⟨0, hd⟩)
      simp at this
      linarith

/-- **`g^{(d)}_u` is the image of the standard Gaussian under `x ↦ √u x`**, for every real `u`. -/
theorem gaussVar_eq_map (d : ℕ) (u : ℝ) :
    gaussVar d u = (stdGaussian (Rd d)).map fun x => Real.sqrt u • x := by
  rw [gaussVar, multivariateGaussian, ← msqrt, msqrt_smul_one]
  congr 1
  funext x
  simp

instance isProbabilityMeasure_gaussVar (d : ℕ) (u : ℝ) : IsProbabilityMeasure (gaussVar d u) := by
  rw [gaussVar_eq_map]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- **The transform of `g^{(d)}_u`**: `ĝ^{(d)}_u(ξ) = e^{-u|ξ|²/2}` for `u ≥ 0`. -/
theorem charFun_gaussVar {u : ℝ} (hu : 0 ≤ u) (ξ : Rd d) :
    charFun (gaussVar d u) ξ = ((Real.exp (-(u * ‖ξ‖ ^ 2) / 2) : ℝ) : ℂ) := by
  have key : ((‖Real.sqrt u • ξ‖ : ℝ) : ℂ) ^ 2 = ((u * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg u),
      Real.sq_sqrt hu]
  rw [gaussVar_eq_map, charFun_map_smul, charFun_stdGaussian, key, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- **The kernel `u ↦ g^{(d)}_u = N(0, uI)` is measurable** (presupposed by
`prop:origin-boundedness-subordinated`, `prop:isotropic-bridge`, `prop:isotropic-bridge-student`,
where the mixtures are `Measure.bind`s; blind review R2-2). The shared library's
`ScaleSpace.measurable_multivariateGaussian_zero_smul_one` (SSL-9), `gaussVar d u` being
`multivariateGaussian 0 (u • 1)` by definition (Q-0365). -/
theorem measurable_gaussVar (d : ℕ) : Measurable (gaussVar d) :=
  ScaleSpace.measurable_multivariateGaussian_zero_smul_one d

end AffineHemigroup
