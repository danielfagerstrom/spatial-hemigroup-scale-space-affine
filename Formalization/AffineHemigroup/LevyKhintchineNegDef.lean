/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.LevyExponent
import Mathlib.Analysis.Complex.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ScaleSpaceCore.PosSemidefSum

/-!
# `lem:lk-negative-definite`: a Lévy–Khintchine form is negative definite

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:lk-negative-definite` (Q-0281, wave N), a
child of `lem:filtration-top` split under ADR-0025. Cites nothing.

For `α ∈ ℝ` and a measure `L` on `ℝ^d`, `lkForm α L η = α|η|² + ∫ (1 - cos⟨η,x⟩) L(dx)`. If the
integral is finite for every `η`, `α' ≤ α` and `L' ≤ L`, then `lkForm α L - lkForm α' L'` is
negative definite on `ℝ^d` in the sense of Schoenberg (Schilling–Song–Vondraček Def. 4.3, (4.8)):
`∑ (φ(η_j) + φ(η_k) - φ(η_j - η_k)) c_j conj c_k ≥ 0` in `ℂ`.

The route: for real coefficients `a`,
`1 - cos A - cos B + cos (A - B) = (1 - cos A)(1 - cos B) + sin A sin B` and the polarization
`|η_j|² + |η_k|² - |η_j - η_k|² = 2⟨η_j, η_k⟩` give

  `∑ a_j a_k (ψ(η_j) + ψ(η_k) - ψ(η_j - η_k)) = 2α |∑ a_j η_j|² + ∫ P_a dL`,
  `P_a(x) = (∑ a_j (1 - cos⟨η_j,x⟩))² + (∑ a_j sin⟨η_j,x⟩)² ≥ 0`

(`lkForm_kernel`), and `∫ P_a dL' ≤ ∫ P_a dL`. A real symmetric kernel that is nonnegative on real
vectors is nonnegative on complex ones (`complex_kernel_nonneg`, the shared library's
`sum_mul_conj_nonneg_of_posSemidef`): the real part splits over the real and imaginary parts of
`c`, and the imaginary part cancels by symmetry.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-- **A Lévy–Khintchine form** `ψ(η) = α|η|² + ∫ (1 - cos⟨η,x⟩) L(dx)`, real-valued (the integral
read through `levyExpL`; finite where it is used). -/
noncomputable def lkForm (α : ℝ) (L : Measure (Rd d)) (η : Rd d) : ℝ :=
  α * ‖η‖ ^ 2 + (levyExpL L η).toReal

theorem one_sub_cos_nonneg_real (θ : ℝ) : 0 ≤ 1 - Real.cos θ := by
  linarith [Real.cos_le_one θ]

/-- `x ↦ 1 - cos⟨η,x⟩` is integrable when its integral is finite. -/
theorem integrable_one_sub_cos_of_levyExpL {L : Measure (Rd d)} {η : Rd d}
    (h : levyExpL L η ≠ ⊤) : Integrable (fun x => 1 - Real.cos ⟪η, x⟫) L := by
  refine ⟨(by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪η, x⟫).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => one_sub_cos_nonneg_real _)]
  exact lt_top_iff_ne_top.mpr h

theorem levyExpL_toReal_eq (L : Measure (Rd d)) (η : Rd d) :
    (levyExpL L η).toReal = ∫ x, (1 - Real.cos ⟪η, x⟫) ∂L := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => one_sub_cos_nonneg_real _)
    (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪η, x⟫).aestronglyMeasurable]
  rfl

theorem levyExpL_neg (L : Measure (Rd d)) (η : Rd d) : levyExpL L (-η) = levyExpL L η := by
  unfold levyExpL
  simp only [inner_neg_left, Real.cos_neg]

theorem lkForm_neg (α : ℝ) (L : Measure (Rd d)) (η : Rd d) : lkForm α L (-η) = lkForm α L η := by
  simp only [lkForm, norm_neg, levyExpL_neg]

theorem lkForm_zero_measure (η : Rd d) : lkForm 0 (0 : Measure (Rd d)) η = 0 := by
  simp [lkForm, levyExpL]

/-- `|∑ a_j η_j|² = ∑_{j,k} a_j a_k ⟨η_j, η_k⟩`. -/
theorem norm_sum_smul_sq {n : ℕ} (a : Fin n → ℝ) (η : Fin n → Rd d) :
    ‖∑ j, a j • η j‖ ^ 2 = ∑ j, ∑ k, a j * a k * ⟪η j, η k⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The pointwise kernel: `∑ a_j a_k (u_j + u_k - u_{jk}) = (∑ a_j u_j)² + (∑ a_j s_j)²`, with
`u_j = 1 - cos θ_j`, `s_j = sin θ_j` and `u_{jk} = 1 - cos (θ_j - θ_k)`. -/
theorem cos_kernel_sum {n : ℕ} (a θ : Fin n → ℝ) :
    ∑ j, ∑ k, a j * a k * ((1 - Real.cos (θ j)) + (1 - Real.cos (θ k)) -
      (1 - Real.cos (θ j - θ k))) =
      (∑ j, a j * (1 - Real.cos (θ j))) ^ 2 + (∑ j, a j * Real.sin (θ j)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.cos_sub]
  ring

/-- **The real kernel of a Lévy–Khintchine form**:
`∑ a_j a_k (ψ(η_j) + ψ(η_k) - ψ(η_j - η_k)) = 2α|∑ a_j η_j|² + ∫ P_a dL`. -/
theorem lkForm_kernel {L : Measure (Rd d)} (hfin : ∀ η, levyExpL L η ≠ ⊤) (α : ℝ) {n : ℕ}
    (η : Fin n → Rd d) (a : Fin n → ℝ) :
    ∑ j, ∑ k, a j * a k * (lkForm α L (η j) + lkForm α L (η k) - lkForm α L (η j - η k)) =
      2 * α * ‖∑ j, a j • η j‖ ^ 2 + ∫ x, ((∑ j, a j * (1 - Real.cos ⟪η j, x⟫)) ^ 2 +
        (∑ j, a j * Real.sin ⟪η j, x⟫) ^ 2) ∂L := by
  have hI := fun η => integrable_one_sub_cos_of_levyExpL (hfin η)
  have hG : ∀ j k, Integrable (fun x => a j * a k * ((1 - Real.cos ⟪η j, x⟫) +
      (1 - Real.cos ⟪η k, x⟫) - (1 - Real.cos ⟪η j - η k, x⟫))) L :=
    fun j k => (((hI _).add (hI _)).sub (hI _)).const_mul _
  have hpt : ∀ j k, a j * a k * (lkForm α L (η j) + lkForm α L (η k) - lkForm α L (η j - η k)) =
      2 * α * (a j * a k * ⟪η j, η k⟫) +
        ∫ x, a j * a k * ((1 - Real.cos ⟪η j, x⟫) + (1 - Real.cos ⟪η k, x⟫) -
          (1 - Real.cos ⟪η j - η k, x⟫)) ∂L := by
    intro j k
    have e : ∫ x, ((1 - Real.cos ⟪η j, x⟫) + (1 - Real.cos ⟪η k, x⟫) -
        (1 - Real.cos ⟪η j - η k, x⟫)) ∂L = ∫ x, (1 - Real.cos ⟪η j, x⟫) ∂L +
          ∫ x, (1 - Real.cos ⟪η k, x⟫) ∂L - ∫ x, (1 - Real.cos ⟪η j - η k, x⟫) ∂L := by
      rw [integral_sub, integral_add]
      exacts [hI _, hI _, (hI _).add (hI _), hI _]
    simp only [lkForm, levyExpL_toReal_eq]
    rw [integral_const_mul, e, norm_sub_sq_real]
    ring
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← norm_sum_smul_sq]
  congr 1
  have hx : ∀ x : Rd d, (∑ j, a j * (1 - Real.cos ⟪η j, x⟫)) ^ 2 +
      (∑ j, a j * Real.sin ⟪η j, x⟫) ^ 2 = ∑ j, ∑ k, a j * a k * ((1 - Real.cos ⟪η j, x⟫) +
        (1 - Real.cos ⟪η k, x⟫) - (1 - Real.cos ⟪η j - η k, x⟫)) := by
    intro x
    rw [← cos_kernel_sum a (fun j => ⟪η j, x⟫)]
    simp only [inner_sub_left]
  simp_rw [hx]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hG j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hG j k]

/-- `P_a` is integrable when every `1 - cos⟨η,·⟩` is. -/
theorem integrable_cos_kernel {L : Measure (Rd d)} (hfin : ∀ η, levyExpL L η ≠ ⊤) {n : ℕ}
    (η : Fin n → Rd d) (a : Fin n → ℝ) :
    Integrable (fun x => (∑ j, a j * (1 - Real.cos ⟪η j, x⟫)) ^ 2 +
      (∑ j, a j * Real.sin ⟪η j, x⟫) ^ 2) L := by
  have hI := fun η => integrable_one_sub_cos_of_levyExpL (hfin η)
  have hsum : Integrable (fun x => ∑ j, ∑ k, a j * a k * ((1 - Real.cos ⟪η j, x⟫) +
      (1 - Real.cos ⟪η k, x⟫) - (1 - Real.cos ⟪η j - η k, x⟫))) L :=
    integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun k _ =>
      (((hI (η j)).add (hI (η k))).sub (hI (η j - η k))).const_mul (a j * a k)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [← cos_kernel_sum a (fun j => ⟪η j, x⟫)]
  simp only [inner_sub_left]

/-- **A real symmetric kernel, nonnegative on real vectors, is nonnegative on complex ones**:
`∑ K_{jk} c_j conj c_k ≥ 0` in `ℂ` (real, and nonnegative). The shared library's
`ScaleSpace.sum_mul_conj_nonneg_of_posSemidef` at the matrix `K`, positive semidefinite by
`ScaleSpace.posSemidef_iff_sum` (`ScaleSpaceCore.PosSemidefSum`, moved there by Q-0364). -/
theorem complex_kernel_nonneg {n : ℕ} (K : Fin n → Fin n → ℝ) (hK : ∀ j k, K j k = K k j)
    (hpos : ∀ a : Fin n → ℝ, 0 ≤ ∑ j, ∑ k, a j * a k * K j k) (c : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, ((K j k : ℝ) : ℂ) * c j * starRingEnd ℂ (c k) := by
  have h := ScaleSpace.sum_mul_conj_nonneg_of_posSemidef
    ((ScaleSpace.posSemidef_iff_sum (Matrix.of K)).2 ⟨fun j k => hK k j, hpos⟩) c
  refine h.trans_eq (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_)
  rw [Matrix.of_apply]
  ring

/-- **`lem:lk-negative-definite`**: if `α' ≤ α`, `L' ≤ L` and `∫ (1 - cos⟨η,x⟩) L(dx) < ∞` for
every `η`, then `lkForm α L - lkForm α' L'` is negative definite on `ℝ^d`. -/
theorem lkForm_sub_negDef {L L' : Measure (Rd d)} (hL : L' ≤ L) {α α' : ℝ} (hα : α' ≤ α)
    (hfin : ∀ η, levyExpL L η ≠ ⊤) {n : ℕ} (η : Fin n → Rd d) (c : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, (((lkForm α L (η j) - lkForm α' L' (η j)) + (lkForm α L (η k) -
      lkForm α' L' (η k)) - (lkForm α L (η j - η k) - lkForm α' L' (η j - η k)) : ℝ) : ℂ) *
        c j * starRingEnd ℂ (c k) := by
  have hfin' : ∀ η, levyExpL L' η ≠ ⊤ := fun η =>
    ne_top_of_le_ne_top (hfin η) (lintegral_mono' hL le_rfl)
  refine complex_kernel_nonneg _ (fun j k => ?_) (fun a => ?_) c
  · rw [show η k - η j = -(η j - η k) by abel, lkForm_neg, lkForm_neg]
    ring
  · have e : ∀ j k, a j * a k * ((lkForm α L (η j) - lkForm α' L' (η j)) + (lkForm α L (η k) -
        lkForm α' L' (η k)) - (lkForm α L (η j - η k) - lkForm α' L' (η j - η k))) =
        a j * a k * (lkForm α L (η j) + lkForm α L (η k) - lkForm α L (η j - η k)) -
          a j * a k * (lkForm α' L' (η j) + lkForm α' L' (η k) - lkForm α' L' (η j - η k)) :=
      fun j k => by ring
    simp_rw [e, Finset.sum_sub_distrib]
    rw [lkForm_kernel hfin, lkForm_kernel hfin']
    have hP := integral_mono_measure hL (Eventually.of_forall fun x => by positivity)
      (integrable_cos_kernel hfin η a)
    have hq : 0 ≤ ‖∑ j, a j • η j‖ ^ 2 := sq_nonneg _
    nlinarith

/-- **`lem:lk-negative-definite`**, the case `α' = 0`, `L' = 0`: for `α ≥ 0`, `lkForm α L` is
negative definite on `ℝ^d`. -/
theorem lkForm_negDef {L : Measure (Rd d)} {α : ℝ} (hα : 0 ≤ α) (hfin : ∀ η, levyExpL L η ≠ ⊤)
    {n : ℕ} (η : Fin n → Rd d) (c : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, ((lkForm α L (η j) + lkForm α L (η k) - lkForm α L (η j - η k) : ℝ) : ℂ) *
        c j * starRingEnd ℂ (c k) := by
  have h := lkForm_sub_negDef (Measure.zero_le L) hα hfin η c
  simp only [lkForm_zero_measure, sub_zero] at h
  exact h

end AffineHemigroup
