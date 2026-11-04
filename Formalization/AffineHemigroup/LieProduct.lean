/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableExponentCone

/-!
# The Lie product formula `(e^{A/n}e^{B/n})^n → e^{A+B}`

Toolbox of `lem:cone-orders-closed` (wave 2, group F, Q-0281), which reads it for the closedness
under sums of the tangent wedge of a closed semigroup; Mathlib does not have it. The proof is the
blueprint's, with the first-order estimate read off a derivative: `φ(s) = e^{sA}e^{sB} - e^{s(A+B)}`
has `φ(0) = 0` and `φ'(0) = 0`, so `n‖φ(1/n)‖ → 0`; with `P = e^{A/n}e^{B/n}`, `Q = e^{(A+B)/n}` and
`‖P‖, ‖Q‖ ≤ e^{(‖A‖+‖B‖)/n}`, the telescoping `Pⁿ - Qⁿ = P(Pⁿ⁻¹ - Qⁿ⁻¹) + (P - Q)Qⁿ⁻¹` gives
`‖Pⁿ - Qⁿ‖ ≤ e^{‖A‖+‖B‖} n‖P - Q‖ → 0`, and `Qⁿ = e^{A+B}`. Norms are the `L^∞` operator norm
(`Matrix.Norms.Operator`), whose topology is the matrices'. Statements in Mathlib types only.
-/

namespace AffineHemigroup

open Matrix Filter
open scoped Topology Norms.Operator

variable {d : ℕ}

/-- `‖e^X‖ ≤ e^{‖X‖}`. -/
theorem norm_mexp_le [NeZero d] (X : Mat d) : ‖mexp X‖ ≤ Real.exp ‖X‖ := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le X n) (by positivity)

/-- **Telescoping**: `‖Pⁿ - Qⁿ‖ ≤ n cⁿ ‖P - Q‖` when `‖P‖, ‖Q‖ ≤ c` and `c ≥ 1`. -/
theorem norm_pow_sub_pow_le [NeZero d] {P Q : Mat d} {c : ℝ} (hc : 1 ≤ c) (hP : ‖P‖ ≤ c)
    (hQ : ‖Q‖ ≤ c) (n : ℕ) : ‖P ^ n - Q ^ n‖ ≤ n * c ^ n * ‖P - Q‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : P ^ (n + 1) - Q ^ (n + 1) = P * (P ^ n - Q ^ n) + (P - Q) * Q ^ n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hQn : ‖Q ^ n‖ ≤ c ^ n :=
      (norm_pow_le Q n).trans (pow_le_pow_left₀ (norm_nonneg _) hQ n)
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hcn : c ^ n ≤ c ^ (n + 1) := pow_le_pow_right₀ hc (Nat.le_succ n)
    rw [he]
    calc ‖P * (P ^ n - Q ^ n) + (P - Q) * Q ^ n‖
        ≤ ‖P‖ * ‖P ^ n - Q ^ n‖ + ‖P - Q‖ * ‖Q ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ c * (n * c ^ n * ‖P - Q‖) + ‖P - Q‖ * c ^ n := by
          gcongr
      _ ≤ c * (n * c ^ n * ‖P - Q‖) + ‖P - Q‖ * c ^ (n + 1) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * c ^ (n + 1) * ‖P - Q‖ := by
          push_cast
          ring

/-- **The Lie product formula**: `(e^{A/n}e^{B/n})ⁿ → e^{A+B}`. -/
theorem tendsto_lie_product [NeZero d] (A B : Mat d) :
    Tendsto (fun n : ℕ => (mexp ((1 / (n : ℝ)) • A) * mexp ((1 / (n : ℝ)) • B)) ^ n) atTop
      (𝓝 (mexp (A + B))) := by
  set φ : ℝ → Mat d := fun s => mexp (s • A) * mexp (s • B) - mexp (s • (A + B))
  have hφ : HasDerivAt φ 0 0 := by
    have h := ((hasDerivAt_mexp_smul A 0).mul (hasDerivAt_mexp_smul B 0)).sub
      (hasDerivAt_mexp_smul (A + B) 0)
    simp only [zero_smul, mexp_zero, Matrix.one_mul, Matrix.mul_one] at h
    exact h.congr_deriv (by abel)
  have hφ0 : φ 0 = 0 := by simp [φ, mexp_zero]
  have hslope := hφ.tendsto_slope_zero
  simp only [zero_add, hφ0, sub_zero] at hslope
  have hinv : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero, Nat.cast_eq_zero]
    omega
  have hT : Tendsto (fun n : ℕ => (n : ℝ) * ‖φ (1 / (n : ℝ))‖) atTop (𝓝 0) := by
    have := (hslope.comp hinv).norm
    rw [norm_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, one_div, inv_inv, norm_smul, Real.norm_natCast]
  set a := ‖A‖ + ‖B‖
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ‖(mexp ((1 / (n : ℝ)) • A) * mexp ((1 / (n : ℝ)) • B)) ^ n - mexp (A + B)‖ ≤
        Real.exp a * ((n : ℝ) * ‖φ (1 / (n : ℝ))‖) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set s : ℝ := 1 / (n : ℝ)
    have hs : 0 ≤ s := by positivity
    set c := Real.exp (s * a)
    have hc : 1 ≤ c := Real.one_le_exp (mul_nonneg hs (by positivity))
    have hP : ‖mexp (s • A) * mexp (s • B)‖ ≤ c := by
      calc ‖mexp (s • A) * mexp (s • B)‖ ≤ ‖mexp (s • A)‖ * ‖mexp (s • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖s • A‖ * Real.exp ‖s • B‖ :=
            mul_le_mul (norm_mexp_le _) (norm_mexp_le _) (norm_nonneg _) (Real.exp_pos _).le
        _ = c := by
            rw [← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hs]
            simp only [c, a]
            ring_nf
    have hQ : ‖mexp (s • (A + B))‖ ≤ c := by
      refine (norm_mexp_le _).trans (Real.exp_le_exp.2 ?_)
      rw [norm_smul, Real.norm_of_nonneg hs]
      exact mul_le_mul_of_nonneg_left (norm_add_le A B) hs
    have hns : (n : ℝ) * s = 1 := by simp only [s]; field_simp
    have hpow : ∀ m : ℕ, mexp (s • (A + B)) ^ m = mexp (((m : ℝ) * s) • (A + B)) := by
      intro m
      induction m with
      | zero => simp [mexp_zero]
      | succ m ih =>
        rw [pow_succ, ih, ← mexp_add_smul]
        push_cast
        ring_nf
    have hQn : mexp (s • (A + B)) ^ n = mexp (A + B) := by
      rw [hpow, hns, one_smul]
    have hcn : c ^ n = Real.exp a := by
      rw [← Real.exp_nat_mul, ← mul_assoc, hns, one_mul]
    have := norm_pow_sub_pow_le hc hP hQ n
    rw [hQn, hcn] at this
    calc _ ≤ (n : ℝ) * Real.exp a * ‖mexp (s • A) * mexp (s • B) - mexp (s • (A + B))‖ := this
      _ = Real.exp a * ((n : ℝ) * ‖φ s‖) := by simp only [φ]; ring
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlim : Tendsto (fun n : ℕ => Real.exp a * ((n : ℝ) * ‖φ (1 / (n : ℝ))‖)) atTop (𝓝 0) := by
    simpa using hT.const_mul (Real.exp a)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hbound n hn

end AffineHemigroup
