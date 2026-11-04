/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.LaplaceUniqueness

/-!
# `lem:bernstein-triplet-unique`: the triplet of a Bernstein representation is unique

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:bernstein-triplet-unique` (Q-0281,
wave N), a child of `lem:filtration-top` split under ADR-0025. It is the last sentence of
Schilling–Song–Vondraček Thm. 3.2 ("the triplet `(a, b, μ)` determines `f` uniquely"), which ledger
entry A10 deliberately does not carry.

If `a + bσ + ∫ (1 - e^{-σt}) m(dt) = a' + b'σ + ∫ (1 - e^{-σt}) m'(dt)` for every `σ > 0`, both
sides finite, with `a, b, a', b' ≥ 0` and `m, m'` carried by `(0,∞)`, then `a = a'`, `b = b'` and
`m = m'`.

The route takes no derivative and no limit. The second difference in steps of `1` kills the affine
part: pointwise,
`(1 - e^{-σt}) + (1 - e^{-(σ+2)t}) + e^{-σt}(1 - e^{-t})² = 2(1 - e^{-(σ+1)t})`
(`bernstein_second_difference`), so the measures `(1 - e^{-t})² m(dt)` and `(1 - e^{-t})² m'(dt)`
have the same finite Laplace transform at every `σ > 0`, hence are equal by the shared library's
`ScaleSpace.laplace_uniqueness_locally_finite` (Lean core; moved from Paper V's package by Q-0360,
read from `ScaleSpaceCore` v0.4.0 since this module's switch); the density `(1 - e^{-t})²` is
positive on `(0,∞)`, so `m = m'`; and then `a + bσ = a' + b'σ` for every `σ > 0`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped ENNReal

/-- A measure with `m((-∞, 0]) = 0` is carried by `(0,∞)`. -/
theorem ae_pos_of_Iic_eq_zero {m : Measure ℝ} (hm : m (Iic 0) = 0) : ∀ᵐ t ∂m, 0 < t := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) hm
  simp only [not_lt, mem_setOf_eq] at ht
  exact ht

theorem one_sub_exp_neg_mul_nonneg {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(σ * t)) :=
  sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))

/-- **The second difference** of `a + bσ + ∫ (1 - e^{-σt}) m(dt)` in steps of `1`:
`G(σ) + G(σ+2) + ∫ e^{-σt}(1 - e^{-t})² m(dt) = 2 G(σ+1)`. -/
theorem bernstein_second_difference (a : ℝ) {b : ℝ} (hb : 0 ≤ b) {m : Measure ℝ}
    (hm : m (Iic 0) = 0) {σ : ℝ} (hσ : 0 < σ) :
    (ENNReal.ofReal a + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m) +
      (ENNReal.ofReal a + ENNReal.ofReal (b * (σ + 2)) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 2) * t))) ∂m) +
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(σ * t)) * (1 - Real.exp (-t)) ^ 2) ∂m =
    2 * (ENNReal.ofReal a + ENNReal.ofReal (b * (σ + 1)) +
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 1) * t))) ∂m) := by
  have hlin : ENNReal.ofReal (b * σ) + ENNReal.ofReal (b * (σ + 2)) =
      2 * ENNReal.ofReal (b * (σ + 1)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hint : ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m +
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 2) * t))) ∂m +
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(σ * t)) * (1 - Real.exp (-t)) ^ 2) ∂m =
      2 * ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 1) * t))) ∂m := by
    rw [← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop),
      ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_of_Iic_eq_zero hm] with t ht
    rw [← ENNReal.ofReal_add (one_sub_exp_neg_mul_nonneg hσ.le ht.le)
        (one_sub_exp_neg_mul_nonneg (by linarith) ht.le),
      ← ENNReal.ofReal_add (add_nonneg (one_sub_exp_neg_mul_nonneg hσ.le ht.le)
        (one_sub_exp_neg_mul_nonneg (by linarith) ht.le)) (by positivity),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have e2 : Real.exp (-((σ + 2) * t)) = Real.exp (-(σ * t)) * Real.exp (-t) ^ 2 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have e1 : Real.exp (-((σ + 1) * t)) = Real.exp (-(σ * t)) * Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    ring
  calc _ = (ENNReal.ofReal a + ENNReal.ofReal a) +
        (ENNReal.ofReal (b * σ) + ENNReal.ofReal (b * (σ + 2))) +
        (∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m +
          ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 2) * t))) ∂m +
          ∫⁻ t, ENNReal.ofReal (Real.exp (-(σ * t)) * (1 - Real.exp (-t)) ^ 2) ∂m) := by ring
    _ = _ := by rw [hlin, hint, ← two_mul]; ring

/-- **`lem:bernstein-triplet-unique`**: two Bernstein representations
`a + bσ + ∫ (1 - e^{-σt}) m(dt)` that agree, finite, at every `σ > 0` have the same triplet. -/
theorem bernstein_triplet_unique {a b a' b' : ℝ} {m m' : Measure ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hm : m (Iic 0) = 0) (hm' : m' (Iic 0) = 0)
    (heq : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal a + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m =
      ENNReal.ofReal a' + ENNReal.ofReal (b' * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m')
    (hfin : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal a + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m ≠ ⊤) :
    a = a' ∧ b = b' ∧ m = m' := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 - Real.exp (-t)) ^ 2) with hw
  have hwm : Measurable w := by fun_prop
  have hlap : ∀ μ : Measure ℝ, ∀ σ : ℝ, ScaleSpace.laplaceL (μ.withDensity w) σ =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(σ * t)) * (1 - Real.exp (-t)) ^ 2) ∂μ := by
    intro μ σ
    rw [ScaleSpace.laplaceL, lintegral_withDensity_eq_lintegral_mul _ hwm (by fun_prop)]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, hw]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have hfin2 : ∀ σ : ℝ, 0 < σ → (ENNReal.ofReal a + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m) +
      (ENNReal.ofReal a + ENNReal.ofReal (b * (σ + 2)) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((σ + 2) * t))) ∂m) ≠ ⊤ := fun σ hσ =>
    ENNReal.add_ne_top.mpr ⟨hfin σ hσ, hfin (σ + 2) (by linarith)⟩
  -- the weighted measures have the same Laplace transform on `(0,∞)`
  have hL : ∀ σ : ℝ, 0 < σ → ScaleSpace.laplaceL (m.withDensity w) σ =
      ScaleSpace.laplaceL (m'.withDensity w) σ := by
    intro σ hσ
    have h1 := bernstein_second_difference a hb hm hσ
    have h2 := bernstein_second_difference a' hb' hm' hσ
    rw [← heq σ hσ, ← heq (σ + 2) (by linarith), ← heq (σ + 1) (by linarith), ← h1] at h2
    rw [hlap, hlap]
    exact ((ENNReal.add_right_inj (hfin2 σ hσ)).mp h2).symm
  have hLfin : ∀ σ : ℝ, 0 < σ → ScaleSpace.laplaceL (m.withDensity w) σ ≠ ⊤ := by
    intro σ hσ
    rw [hlap]
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hfin (σ + 1) (by linarith))) ?_
    rw [← bernstein_second_difference a hb hm hσ]
    exact le_add_self
  have hfold : ∀ μ : Measure ℝ, μ (Iic 0) = 0 → ScaleSpace.IsFolded (μ.withDensity w) :=
    fun μ hμ => withDensity_absolutelyContinuous μ w hμ
  have hn := ScaleSpace.laplace_uniqueness_locally_finite (hfold m hm) (hfold m' hm') (τ₀ := 0)
    hL hLfin
  -- divide the density back out
  have hne0 : ∀ μ : Measure ℝ, μ (Iic 0) = 0 → ∀ᵐ t ∂μ, w t ≠ 0 := by
    intro μ hμ
    filter_upwards [ae_pos_of_Iic_eq_zero hμ] with t ht
    simp only [hw, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  have hmm : m = m' := by
    rw [← withDensity_inv_same hwm (hne0 m hm)
        (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top), hn,
      withDensity_inv_same hwm (hne0 m' hm') (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)]
  subst hmm
  -- the affine parts
  have hab : ∀ σ : ℝ, 0 < σ → a + b * σ = a' + b' * σ := by
    intro σ hσ
    have h := heq σ hσ
    have hΦ := (ENNReal.add_ne_top.mp (hfin σ hσ)).2
    rw [ENNReal.add_left_inj hΦ, ← ENNReal.ofReal_add ha (by positivity),
      ← ENNReal.ofReal_add ha' (by positivity),
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h
    exact h
  have h1 := hab 1 one_pos
  have h2 := hab 2 two_pos
  exact ⟨by linarith, by linarith, rfl⟩

end AffineHemigroup
