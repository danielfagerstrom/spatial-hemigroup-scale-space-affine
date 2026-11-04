/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.GWFamily
import AffineHemigroup.Defs.IsotropicFamily
import ScaleSpaceCore.L1OperatorsEuclidean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The operator form: `def:gw-cascade-family`(1) and the isotropic operator family

Blueprint: `def:gw-cascade-family`(1) and `lem:operators-to-kernels`
(`blueprint/src/parts/04-classical.tex`); PRICING.md item D9.

## The axioms are equations of operators, written with the shared library's operators

The operator axioms are stated literally, as equations of bounded operators on `L¹(ℝ^d)` (the
author's decision of 2026-10-07, closing open call 1 of `records/formalization/SKELETON.md`), with
the operators of `ScaleSpaceCore` v0.3.0 (`ScaleSpaceCore.L1OperatorsSpace`,
`ScaleSpaceCore.L1OperatorsEuclidean`; SSL-5, Q-0332):

* `T_a f = f(· - a)` is `ScaleSpace.transL1E a`;
* `D_A f = |det A|⁻¹ f(A⁻¹ ·)`, for a matrix `A` with `hA : IsUnit A.det`, is
  `ScaleSpace.dilL1E (ScaleSpace.matEquiv A hA)`. This is the blueprint's normalisation
  (`def:gw-cascade-family`: "on `L¹(ℝ^d)` by `D_A f := |det A|⁻¹ f(A⁻¹ ·)`"): the trunk's
  `dilateE A f x = |det A|⁻¹ f(A.symm x)`, the determinant of `matEquiv A hA` is the matrix
  determinant (`ScaleSpace.det_matEquiv`), and `(matEquiv A hA).symm x = toEuclideanCLM A⁻¹ x`,
  which is `lin A⁻¹ x` by the definition of `lin` (`ScaleSpace.coeFn_dilL1E_matEquiv`).
  The inverse operator `D_A⁻¹` is `ScaleSpace.dilL1E (ScaleSpace.matEquiv A hA).symm`, that is
  `D_{A⁻¹}` (`ScaleSpace.dilL1E_comp_symm`, `ScaleSpace.dilL1E_symm_comp`);
* the rotation `R_Q f = f(Q⁻¹ ·)`, `Q ∈ O(d)`, is `D_Q`, since `|det Q| = 1`
  (`ScaleSpace.coeFn_dilL1E_matEquiv_orthogonal`);
* the isotropic dilation `D_λ f = λ^{-d} f(·/λ)`, `λ > 0`, is `D_{λI}`, since `|det λI| = λ^d`
  (`ScaleSpace.matEquiv_smul_one` identifies `matEquiv (λ • 1)` with the trunk's homothety, and
  `ScaleSpace.coeFn_dilL1E_homothety` gives its representative);
* the convolution `f ↦ μ ∗ f`, `(μ ∗ f)(x) = ∫ f(x - y) μ(dy)`, by a finite measure `μ` is
  `ScaleSpace.mconvL1E μ`.

`L1 d` is the trunk's `Rd d →₁[volume] ℝ` on the nose (`L1_eq`), so the trunk's operators act on it
without conversion.

**Which form each axiom takes.** Each is written the way the blueprint writes it: (A2) as
`Φ T_a = T_a Φ`; the covariance of `def:gw-cascade-family`(1) as the conjugation
`D_A Φ_{Σ,Σ'} D_A⁻¹ = Φ_{A·Σ, A·Σ'}`; the rotation axiom of `lem:operators-to-kernels`(5) as
`Φ_{s,t} R_Q = R_Q Φ_{s,t}`; and (A8) as `D_λ Φ_{s,t} = Φ_{S_λ s, S_λ t} D_λ`.

**The relational reading is retired.** Before the trunk built `T_a` and `D_A`, the skeleton stated
these axioms relationally ("for all `f, g` with `g = T f` a.e., `Ψ g = T (Φ f)` a.e.", through a
definition `Intertwines`). That reading survives as theorems, not definitions:
`AffineHemigroup.OperatorForm` proves each axiom equivalent to its relational form.

The function-level convolution `convd μ f` is kept: proved declarations of the library read it
pointwise, and it is the trunk's `ScaleSpace.mconvE μ f` by definition (`convd_eq_mconvE`).
-/

namespace AffineHemigroup

open MeasureTheory Set
open scoped MatrixOrder
open ScaleSpace (transL1E dilL1E matEquiv mconvL1E)

variable {d : ℕ}

/-- **`L¹(ℝ^d)`**, the real space (D9). Named `L1` rather than `X` (Paper V's and the trunk's
`X` is `L¹(ℝ)`; SECOND-DEMAND.md § 7). -/
noncomputable abbrev L1 (d : ℕ) := Lp ℝ 1 (volume : Measure (Rd d))

/-- `L1 d` is the trunk's `L¹(E)` at `E = ℝ^d`, by definition. -/
theorem L1_eq (d : ℕ) : L1 d = (Rd d →₁[volume] ℝ) := rfl

/-- **`(μ ∗ f)(x) := ∫ f(x - y) μ(dy)`** on representatives (`lem:operators-to-kernels`). The
operator on `L¹(ℝ^d)` is the trunk's `ScaleSpace.mconvL1E μ`. -/
noncomputable def convd (μ : Measure (Rd d)) (f : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∫ y, f (x - y) ∂μ

/-- `convd` is the trunk's function-level convolution `ScaleSpace.mconvE`, by definition. -/
theorem convd_eq_mconvE (μ : Measure (Rd d)) : convd μ = ScaleSpace.mconvE μ := rfl

/-- **The standard Gaussian density** `γ(x) = (2π)^{-d/2} e^{-|x|²/2}`
(`lem:operators-to-kernels`). -/
noncomputable def gaussDensity (d : ℕ) (x : Rd d) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2)

/-- The standard Gaussian density is integrable on `ℝ^d`. -/
theorem integrable_gaussDensity (d : ℕ) : Integrable (gaussDensity d) := by
  have h : Integrable (fun v : Rd d => Real.exp (-(‖v‖ ^ 2) / 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Rd d) (b := (1 / 2 : ℂ))
      (by norm_num) 0 0).norm
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Complex.norm_exp, zero_mul, add_zero]
    congr 1
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
    norm_num
    ring
  exact h.const_mul _

/-- **`γ` as an element of `L¹(ℝ^d)`** (`lem:operators-to-kernels`(1), (3): "`μ ∗ γ`"). -/
noncomputable def gaussL1 (d : ℕ) : L1 d := (integrable_gaussDensity d).toL1 _

/-- An orthogonal matrix is invertible: `|det Q| = 1`. -/
theorem isUnit_det_of_mem_orthSet {Q : Mat d} (hQ : Q ∈ orthSet d) : IsUnit Q.det :=
  ScaleSpace.isUnit_det_of_transpose_mul_self ((Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hQ)

/-- `λ I` is invertible for `λ > 0`: `det (λ I) = λ^d`. -/
theorem isUnit_det_smul_one {lam : ℝ} (hlam : 0 < lam) : IsUnit (lam • (1 : Mat d)).det := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (pow_pos hlam _).ne'.isUnit

/-- **The single-operator axioms of [V, Def. 3.1] other than the reflection axiom (A3), read in
`ℝ^d`** (`def:gw-cascade-family`(1), `lem:operators-to-kernels`(1)): (A1), (A2), (A4), (A5).
**(A1)**, boundedness, is the type `L1 d →L[ℝ] L1 d`. -/
structure IsSingleOperator (Φ : L1 d →L[ℝ] L1 d) : Prop where
  /-- **(A2)** `Φ T_a = T_a Φ` for every `a ∈ ℝ^d`, `T_a f = f(· - a)` (`ScaleSpace.transL1E`). -/
  translation : ∀ a : Rd d, Φ.comp (transL1E a) = (transL1E a).comp Φ
  /-- **(A4)** `Φ f ≥ 0` whenever `f ≥ 0`. -/
  positive : ∀ f : L1 d, (∀ᵐ x ∂volume, 0 ≤ (f : Rd d → ℝ) x) →
    ∀ᵐ x ∂volume, 0 ≤ (Φ f : Rd d → ℝ) x
  /-- **(A5)** `∫ Φ f = ∫ f` whenever `f ≥ 0`. -/
  mass : ∀ f : L1 d, (∀ᵐ x ∂volume, 0 ≤ (f : Rd d → ℝ) x) →
    ∫ x, (Φ f : Rd d → ℝ) x = ∫ x, (f : Rd d → ℝ) x

/-- **A `(G, W)`-cascade family of operators** (D9; `def:gw-cascade-family`(1)): linear
operators `Φ Σ Σ'` on `L¹(ℝ^d)`, `(Σ, Σ') ∈ P_W`, each satisfying (A1), (A2), (A4), (A5), with
the cascade, continuity into `L¹(ℝ^d)`, (ND) and covariance. Totalised as the kernel form is: every
field reads `Φ` on `P_W` only. -/
structure IsGWOperatorFamily (G : Set (Mat d)) (le : Mat d → Mat d → Prop)
    (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)) : Prop where
  /-- (A1), (A2), (A4), (A5) for each operator. -/
  single : ∀ p ∈ wedgePairs le, IsSingleOperator (Φ p.1 p.2)
  /-- (cascade) `Φ Σ Σ = Id`. -/
  diag : ∀ S : Mat d, S.PosSemidef → Φ S S = ContinuousLinearMap.id ℝ (L1 d)
  /-- (cascade) `Φ Σ' Σ'' ∘ Φ Σ Σ' = Φ Σ Σ''` whenever `Σ ≤_W Σ' ≤_W Σ''`. -/
  cascade : ∀ S S' S'' : Mat d, S.PosSemidef → S'.PosSemidef → S''.PosSemidef →
    le S S' → le S' S'' → (Φ S' S'').comp (Φ S S') = Φ S S''
  /-- (continuity) `(Σ, Σ') ↦ Φ Σ Σ' f` is continuous from `P_W` into `L¹(ℝ^d)`. -/
  continuous : ∀ f : L1 d, ContinuousOn (fun p : Mat d × Mat d => Φ p.1 p.2 f) (wedgePairs le)
  /-- (ND) `Φ 0 I ≠ Id`. -/
  nondegenerate : Φ 0 1 ≠ ContinuousLinearMap.id ℝ (L1 d)
  /-- (covariance) `D_A Φ_{Σ,Σ'} D_A⁻¹ = Φ_{A·Σ, A·Σ'}` for `A ∈ G`, `(Σ, Σ') ∈ P_W`, written as
  the blueprint writes it, a conjugation: `D_A = dilL1E (matEquiv A hA)`,
  `D_A⁻¹ = dilL1E (matEquiv A hA).symm`. The invertibility `hA` is a binder because `D_A` needs it;
  for a wedge datum every `A ∈ G` is invertible (`IsClosedSubgroupGL.subset_gl`), so there the
  binder asks nothing. -/
  covariant : ∀ A ∈ G, ∀ hA : IsUnit A.det, ∀ p ∈ wedgePairs le,
    ((dilL1E (matEquiv A hA)).comp (Φ p.1 p.2)).comp (dilL1E (matEquiv A hA).symm) =
      Φ (act A p.1) (act A p.2)

/-- **The isotropic operator family** (`lem:operators-to-kernels`(5)): linear
operators `Φ s t` on `L¹(ℝ^d)`, `0 ≤ s ≤ t`, with (A1), (A2), (A4), (A5), the cascade (A6),
continuity (A7), rotation invariance `Φ R_Q = R_Q Φ`, the dilation covariance (A8)
`D_λ Φ_{s,t} = Φ_{S_λ s, S_λ t} D_λ` with `D_λ f = λ^{-d} f(·/λ)`, and (ND) at every `s < t`.
`R_Q = D_Q` and `D_λ = D_{λI}` (the module docstring). -/
structure IsIsotropicOperatorFamily (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (S : ℝ → ℝ → ℝ) :
    Prop where
  single : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSingleOperator (Φ s t)
  /-- (A6) `Φ t t = Id`. -/
  diag : ∀ t : ℝ, 0 ≤ t → Φ t t = ContinuousLinearMap.id ℝ (L1 d)
  /-- (A6) `Φ s t ∘ Φ r s = Φ r t`. -/
  cascade : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → (Φ s t).comp (Φ r s) = Φ r t
  /-- (A7) continuity into `L¹(ℝ^d)`. -/
  continuous : ∀ f : L1 d,
    ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 f) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  /-- `Φ_{s,t} R_Q = R_Q Φ_{s,t}` for `Q ∈ O(d)`, `R_Q f = f(Q⁻¹ ·)`, which is `D_Q`. -/
  rotation : ∀ Q : Mat d, ∀ hQ : Q ∈ orthSet d, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (Φ s t).comp (dilL1E (matEquiv Q (isUnit_det_of_mem_orthSet hQ))) =
      (dilL1E (matEquiv Q (isUnit_det_of_mem_orthSet hQ))).comp (Φ s t)
  /-- (A8) each `S λ` is an increasing bijection of `[0,∞)`. -/
  scale_bij : ∀ lam : ℝ, 0 < lam → IsIncreasingBijection (S lam)
  /-- (A8) `D_λ Φ_{s,t} = Φ_{S_λ s, S_λ t} D_λ`, `D_λ f = λ^{-d} f(·/λ)`, which is `D_{λI}`. -/
  scale : ∀ lam : ℝ, ∀ hlam : 0 < lam, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (dilL1E (matEquiv (lam • (1 : Mat d)) (isUnit_det_smul_one hlam))).comp (Φ s t) =
      (Φ (S lam s) (S lam t)).comp
        (dilL1E (matEquiv (lam • (1 : Mat d)) (isUnit_det_smul_one hlam)))
  /-- (ND) `Φ s t ≠ Id` whenever `s < t`. -/
  nondegenerate : ∀ s t : ℝ, 0 ≤ s → s < t → Φ s t ≠ ContinuousLinearMap.id ℝ (L1 d)

/-- **The measures `μ` represent the operators `Φ` on `P_W`** (`lem:operators-to-kernels`(4),
`lem:kernels-to-operators`(2)): for every `(Σ, Σ') ∈ P_W`, `μ_{Σ,Σ'}` is a probability measure and
`Φ_{Σ,Σ'} = μ_{Σ,Σ'} ∗ ·` on `L¹(ℝ^d)`. Both families are totalised and read on `P_W` only. -/
def IsConvOnPairs (le : Mat d → Mat d → Prop) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d))
    (μ : Mat d → Mat d → Measure (Rd d)) : Prop :=
  ∀ p ∈ wedgePairs le, ∃ _ : IsProbabilityMeasure (μ p.1 p.2), Φ p.1 p.2 = mconvL1E (μ p.1 p.2)

end AffineHemigroup
