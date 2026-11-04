/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Orbits
import AffineHemigroup.Scheme
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# `lem:elliptical-stable-density`: the constant and the action of `GL(d)`

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:elliptical-stable-density` (wave 1, group D,
Q-0281):

* `stableConst_pos_finite`: `c_{d,α} = ∫ (1 - cos y₁)|y|^{-d-α} dy` is finite and positive, for
  `0 < α < 2`: the integrand is at most `|y|^{2-d-α}/2` on the unit ball and `2|y|^{-d-α}` off it,
  a radial bound integrable by Mathlib's `integrable_fun_norm_addHaar` (polar coordinates), and it
  is positive on the open set `{0 < y₁ < π}`;
* `stableDensity_act`: clause (3), `n_{AHAᵀ}(x) = |det A|⁻¹ n_H(A⁻¹x)`.

Lean core only: no ledger entry is read.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ### The constant `c_{d,α}` -/

/-- The radial bound of the integrand of `c_{d,α}`: `r^{2-d-α}/2` on `(0,1]`, `2r^{-d-α}` on
`(1,∞)`, and `0` elsewhere. -/
noncomputable def stableConstBound (d : ℕ) (α r : ℝ) : ℝ :=
  (Ioc 0 1).indicator (fun r => r ^ (2 - (d : ℝ) - α) / 2) r +
    (Ioi 1).indicator (fun r => 2 * r ^ (-(d : ℝ) - α)) r

/-- The radial bound is integrable on `ℝ^d` (polar coordinates), for `0 < α < 2`. -/
theorem integrable_stableConstBound [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Integrable (fun y : Rd d => stableConstBound d α ‖y‖) := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  rw [integrable_fun_norm_addHaar volume (f := stableConstBound d α), finrank_euclideanSpace_fin]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)), Nat.cast_one]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have h : IntegrableOn (fun y : ℝ => y ^ (1 - α) / 2) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 1 - α)
        (by linarith)).1
      exact this.div_const 2
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioc
    have hy0 : 0 < y := hy.1
    simp only [stableConstBound, indicator_of_mem hy, smul_eq_mul,
      indicator_of_notMem (show y ∉ Ioi 1 from not_lt.2 hy.2), add_zero]
    rw [← rpow_natCast, hcast, mul_div_assoc', ← rpow_add hy0]
    ring_nf
  · have h : IntegrableOn (fun y : ℝ => 2 * y ^ (-1 - α)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul 2
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := lt_trans one_pos hy
    simp only [stableConstBound, indicator_of_mem hy, smul_eq_mul,
      indicator_of_notMem (show y ∉ Ioc 0 1 from fun h => not_le.2 (mem_Ioi.1 hy) h.2), zero_add]
    rw [← rpow_natCast, hcast, mul_left_comm, ← rpow_add hy0]
    ring_nf

/-- The integrand of `c_{d,α}` is nonnegative. -/
theorem stableConst_integrand_nonneg [NeZero d] (α : ℝ) (y : Rd d) :
    0 ≤ (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α) :=
  mul_nonneg (by linarith [Real.cos_le_one (y 0)]) (rpow_nonneg (norm_nonneg _) _)

/-- The integrand of `c_{d,α}` is dominated by the radial bound. -/
theorem stableConst_integrand_le [NeZero d] (α : ℝ) (y : Rd d) :
    (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α) ≤ stableConstBound d α ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [stableConstBound]
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hp : 0 < ‖y‖ ^ (-(d : ℝ) - α) := rpow_pos_of_pos hn _
  rcases le_or_gt ‖y‖ 1 with h1 | h1
  · simp only [stableConstBound, indicator_of_mem (show ‖y‖ ∈ Ioc 0 1 from ⟨hn, h1⟩),
      indicator_of_notMem (show ‖y‖ ∉ Ioi 1 from not_lt.2 h1), add_zero]
    have hc : 1 - Real.cos (y 0) ≤ ‖y‖ ^ 2 / 2 := by
      have h1 := one_sub_sq_div_two_le_cos (x := y 0)
      have h2 : |y 0| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 0
      have h3 : y 0 ^ 2 ≤ ‖y‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    calc (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α)
        ≤ ‖y‖ ^ 2 / 2 * ‖y‖ ^ (-(d : ℝ) - α) := mul_le_mul_of_nonneg_right hc hp.le
      _ = ‖y‖ ^ (2 - (d : ℝ) - α) / 2 := by
          rw [show (2 - (d : ℝ) - α) = (2 : ℕ) + (-(d : ℝ) - α) by push_cast; ring,
            rpow_add hn, rpow_natCast]
          ring
  · simp only [stableConstBound, indicator_of_mem (show ‖y‖ ∈ Ioi 1 from h1),
      indicator_of_notMem (show ‖y‖ ∉ Ioc 0 1 from fun h => not_le.2 h1 h.2), zero_add]
    have hc : 1 - Real.cos (y 0) ≤ 2 := by linarith [neg_one_le_cos (y 0)]
    exact mul_le_mul_of_nonneg_right hc hp.le

/-- **`lem:elliptical-stable-density`**, the constant: `0 < c_{d,α} < ∞`. -/
theorem stableConst_pos_finite [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Integrable (fun y : Rd d => (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α)) ∧
      0 < stableConst (d := d) α := by
  have hmeas : AEStronglyMeasurable
      (fun y : Rd d => (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α)) volume := by
    fun_prop
  have hint : Integrable (fun y : Rd d => (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α)) :=
    (integrable_stableConstBound hα0 hα2).mono' hmeas (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (stableConst_integrand_nonneg α y)]
      exact stableConst_integrand_le α y)
  refine ⟨hint, ?_⟩
  unfold stableConst
  rw [integral_pos_iff_support_of_nonneg (fun y => stableConst_integrand_nonneg α y) hint]
  -- the support contains the nonempty open set `{0 < y₁ < π}`
  set U : Set (Rd d) := (fun y : Rd d => y 0) ⁻¹' Ioo 0 π with hU
  have hUo : IsOpen U := isOpen_Ioo.preimage (by fun_prop)
  have hUne : U.Nonempty := ⟨EuclideanSpace.single 0 1, by
    simp only [hU, mem_preimage, PiLp.single_apply, if_true, mem_Ioo]
    exact ⟨one_pos, by linarith [Real.two_le_pi]⟩⟩
  refine lt_of_lt_of_le (hUo.measure_pos volume hUne) (measure_mono fun y hy => ?_)
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [hU] at hy
  rw [Function.mem_support]
  refine (mul_pos ?_ (rpow_pos_of_pos (norm_pos_iff.2 hy0) _)).ne'
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hy.2.le hy.1
  rw [Real.cos_zero] at this
  linarith

/-! ### Clause (3): the action of `GL(d)` -/

/-- **`lem:elliptical-stable-density`(3)**: `n_{AHAᵀ}(x) = |det A|⁻¹ n_H(A⁻¹x)` for `A ∈ GL(d)`,
`H ∈ PD(d)`, `x ≠ 0`. -/
theorem stableDensity_act [NeZero d] {α : ℝ} (_hα0 : 0 < α) (_hα2 : α < 2) (A : Mat d)
    (hA : A ∈ glSet d) {H : Mat d} (hH : H.PosDef) (x : Rd d) (_hx : x ≠ 0) :
    stableDensity α (act A H) x = |A.det|⁻¹ * stableDensity α H (lin A⁻¹ x) := by
  have hUA : IsUnit A.det := hA
  have hdet : (act A H).det = A.det ^ 2 * H.det := by
    rw [act, det_mul, det_mul, det_transpose]; ring
  have hinv : (act A H)⁻¹ = act (A⁻¹)ᵀ H⁻¹ := by
    rw [act, Matrix.mul_inv_rev, Matrix.mul_inv_rev, act, transpose_transpose,
      transpose_nonsing_inv, mul_assoc]
  have hquad : quad (act A H)⁻¹ x = quad H⁻¹ (lin A⁻¹ x) := by
    rw [hinv, quad_act, transpose_transpose]
  have hpow : (A.det ^ 2 * H.det) ^ (-(1 : ℝ) / 2) = |A.det|⁻¹ * H.det ^ (-(1 : ℝ) / 2) := by
    rw [mul_rpow (sq_nonneg _) hH.det_pos.le, ← sq_abs, ← rpow_natCast,
      ← rpow_mul (abs_nonneg _)]
    norm_num [rpow_neg_one]
  unfold stableDensity
  rw [hdet, hquad, hpow]
  ring

end AffineHemigroup
