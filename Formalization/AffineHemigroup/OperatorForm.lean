/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Operators

/-!
# The operator form, and the relational reading it replaced

Q-0281, wave M, phase 1 (the author's decision of 2026-10-07, closing open call 1 of
`records/formalization/SKELETON.md`). `AffineHemigroup.Defs.Operators` states the operator axioms
of `def:gw-cascade-family`(1) and `lem:operators-to-kernels`(5) as equations of operators on
`L¹(ℝ^d)`, with the shared library's `T_a = ScaleSpace.transL1E a` and
`D_A = ScaleSpace.dilL1E (ScaleSpace.matEquiv A hA)`. Before those operators existed the skeleton
stated each axiom relationally, through a definition `Intertwines c A Φ Ψ`:

  for all `f, g ∈ L¹` with `g = c · f(A⁻¹ ·)` a.e., `Ψ g = c · (Φ f)(A⁻¹ ·)` a.e.;

and (A2) likewise with `f(· - a)`. This file proves each axiom equivalent to that reading, so
that the old reading is a theorem rather than a definition and nothing stated against it is lost:
(A2) (`translation_iff_relational`), the covariance of `def:gw-cascade-family`(1) at
`c = |det A|⁻¹` (`covariant_iff_relational`), the rotation axiom at `c = 1`, `A = Q`
(`rotation_iff_relational`) and (A8) at `c = λ^{-d}`, `A = λI` (`scale_iff_relational`). Each is
the trunk's `ScaleSpace.translation_iff_transL1E` or `ScaleSpace.intertwines_iff_dilL1E_matEquiv`
read in this module's names, with the conjugation `D_A Φ D_A⁻¹ = Ψ` turned into the commutation
`D_A Φ = Ψ D_A` (`dil_conj_eq_iff`).
-/

namespace AffineHemigroup

open MeasureTheory
open ScaleSpace (transL1E dilL1E matEquiv mconvL1E)

variable {d : ℕ}

/-- `lin A` is `Matrix.toEuclideanCLM A`, by definition: the trunk's `matEquiv A hA` acts by
`lin A`, and its inverse by `lin A⁻¹`. -/
theorem lin_eq_toEuclideanCLM (A : Mat d) : lin A = Matrix.toEuclideanCLM (𝕜 := ℝ) A := rfl

theorem matEquiv_apply_eq_lin (A : Mat d) (hA : IsUnit A.det) (x : Rd d) :
    matEquiv A hA x = lin A x := rfl

theorem matEquiv_symm_apply_eq_lin (A : Mat d) (hA : IsUnit A.det) (x : Rd d) :
    (matEquiv A hA).symm x = lin A⁻¹ x := rfl

/-- `A_* μ` is the trunk's image measure under `matEquiv A hA`. -/
theorem push_eq_map_matEquiv (A : Mat d) (hA : IsUnit A.det) (μ : Measure (Rd d)) :
    push A μ = μ.map (matEquiv A hA) := rfl

/-- **(A2) and its relational reading.** `Φ T_a = T_a Φ` for every `a` if and only if, for all
`f, g` with `g = f(· - a)` a.e., `Φ g = (Φ f)(· - a)` a.e. -/
theorem translation_iff_relational (Φ : L1 d →L[ℝ] L1 d) :
    (∀ a : Rd d, Φ.comp (transL1E a) = (transL1E a).comp Φ) ↔
      ∀ (a : Rd d) (f g : L1 d), ((g : Rd d → ℝ) =ᵐ[volume] fun x => f (x - a)) →
        ((Φ g : Rd d → ℝ) =ᵐ[volume] fun x => (Φ f : Rd d → ℝ) (x - a)) :=
  (ScaleSpace.translation_iff_transL1E Φ).symm

/-- **The conjugation is the commutation**: `D_A Φ D_A⁻¹ = Ψ` if and only if `D_A Φ = Ψ D_A`. -/
theorem dil_conj_eq_iff (A : Mat d) (hA : IsUnit A.det) (Φ Ψ : L1 d →L[ℝ] L1 d) :
    ((dilL1E (matEquiv A hA)).comp Φ).comp (dilL1E (matEquiv A hA).symm) = Ψ ↔
      (dilL1E (matEquiv A hA)).comp Φ = Ψ.comp (dilL1E (matEquiv A hA)) := by
  constructor
  · rintro rfl
    rw [ContinuousLinearMap.comp_assoc, ScaleSpace.dilL1E_symm_comp, ContinuousLinearMap.comp_id]
  · intro h
    rw [h, ContinuousLinearMap.comp_assoc, ScaleSpace.dilL1E_comp_symm,
      ContinuousLinearMap.comp_id]

/-- **The commutation and the relational reading**, for any normalisation `c ≠ 0`:
`Ψ D_A = D_A Φ` if and only if, for all `f, g` with `g = c · f(A⁻¹ ·)` a.e.,
`Ψ g = c · (Φ f)(A⁻¹ ·)` a.e. This is the retired `Intertwines c A Φ Ψ`. -/
theorem dil_comp_eq_iff_relational (c : ℝ) (hc : c ≠ 0) (A : Mat d) (hA : IsUnit A.det)
    (Φ Ψ : L1 d →L[ℝ] L1 d) :
    Ψ.comp (dilL1E (matEquiv A hA)) = (dilL1E (matEquiv A hA)).comp Φ ↔
      ∀ f g : L1 d, ((g : Rd d → ℝ) =ᵐ[volume] fun x => c * f (lin A⁻¹ x)) →
        ((Ψ g : Rd d → ℝ) =ᵐ[volume] fun x => c * (Φ f : Rd d → ℝ) (lin A⁻¹ x)) :=
  (ScaleSpace.intertwines_iff_dilL1E_matEquiv c hc A hA Φ Ψ).symm

/-- **The covariance of `def:gw-cascade-family`(1) and its relational reading**:
`D_A Φ D_A⁻¹ = Ψ` if and only if the retired `Intertwines (|det A|⁻¹) A Φ Ψ` holds. -/
theorem covariant_iff_relational (A : Mat d) (hA : IsUnit A.det) (Φ Ψ : L1 d →L[ℝ] L1 d) :
    ((dilL1E (matEquiv A hA)).comp Φ).comp (dilL1E (matEquiv A hA).symm) = Ψ ↔
      ∀ f g : L1 d, ((g : Rd d → ℝ) =ᵐ[volume] fun x => |A.det|⁻¹ * f (lin A⁻¹ x)) →
        ((Ψ g : Rd d → ℝ) =ᵐ[volume] fun x => |A.det|⁻¹ * (Φ f : Rd d → ℝ) (lin A⁻¹ x)) :=
  (dil_conj_eq_iff A hA Φ Ψ).trans (eq_comm.trans
    (dil_comp_eq_iff_relational _ (inv_ne_zero (abs_ne_zero.mpr hA.ne_zero)) A hA Φ Ψ))

/-- **The rotation axiom of `lem:operators-to-kernels`(5) and its relational reading**:
`Φ R_Q = R_Q Φ` if and only if the retired `Intertwines 1 Q Φ Φ` holds. -/
theorem rotation_iff_relational {Q : Mat d} (hQ : Q ∈ orthSet d) (Φ : L1 d →L[ℝ] L1 d) :
    Φ.comp (dilL1E (matEquiv Q (isUnit_det_of_mem_orthSet hQ))) =
        (dilL1E (matEquiv Q (isUnit_det_of_mem_orthSet hQ))).comp Φ ↔
      ∀ f g : L1 d, ((g : Rd d → ℝ) =ᵐ[volume] fun x => 1 * f (lin Q⁻¹ x)) →
        ((Φ g : Rd d → ℝ) =ᵐ[volume] fun x => 1 * (Φ f : Rd d → ℝ) (lin Q⁻¹ x)) :=
  dil_comp_eq_iff_relational 1 one_ne_zero Q _ Φ Φ

/-- **(A8) and its relational reading**: `D_λ Φ = Ψ D_λ` if and only if the retired
`Intertwines (λ^{-d}) (λI) Φ Ψ` holds. -/
theorem scale_iff_relational {lam : ℝ} (hlam : 0 < lam) (Φ Ψ : L1 d →L[ℝ] L1 d) :
    (dilL1E (matEquiv (lam • (1 : Mat d)) (isUnit_det_smul_one hlam))).comp Φ =
        Ψ.comp (dilL1E (matEquiv (lam • (1 : Mat d)) (isUnit_det_smul_one hlam))) ↔
      ∀ f g : L1 d,
        ((g : Rd d → ℝ) =ᵐ[volume] fun x => lam ^ (-(d : ℝ)) * f (lin (lam • (1 : Mat d))⁻¹ x)) →
        ((Ψ g : Rd d → ℝ) =ᵐ[volume]
          fun x => lam ^ (-(d : ℝ)) * (Φ f : Rd d → ℝ) (lin (lam • (1 : Mat d))⁻¹ x)) :=
  eq_comm.trans (dil_comp_eq_iff_relational _ (Real.rpow_pos_of_pos hlam _).ne' _ _ Φ Ψ)

end AffineHemigroup
