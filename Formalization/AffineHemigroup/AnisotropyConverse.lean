/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OneParameter

/-!
# `prop:anisotropy-budget-converse`: the anisotropy budget is attained

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:anisotropy-budget-converse`
(`prop:anisotropy-budget`(2)). Wave 2, group E, Q-0281. `λ := λ_min(sym B) > 0` from
`tr B ≥ dλ`; `|e^{-tB}x| ≤ e^{-λt}|x|` by the derivative of `|e^{-tB}x|²`; `S_α(I)` is
`B`-self-decomposable by `prop:stable-exponent-cone` (A3(iii)), rotation invariant by its radial
transform, and not Gaussian because its one-dimensional marginal has the transform `e^{-|t|^α}`,
which no Gaussian transform has for `α < 2`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- `tr B ≥ d λ_min(sym B)` (`d ≥ 1`). -/
theorem trace_ge_card_mul_lamMin [NeZero d] (B : Mat d) :
    (d : ℝ) * lamMin (symPart B) ≤ B.trace := by
  rw [← trace_symPart, ← sum_eigUp (symPart_isHermitian B),
    lamMin_eq_eigUp_zero (symPart_isHermitian B)]
  calc (d : ℝ) * eigUp (symPart B) 0 = ∑ _k : Fin d, eigUp (symPart B) 0 := by simp
    _ ≤ ∑ k, eigUp (symPart B) k := Finset.sum_le_sum fun k _ =>
        eigUp_monotone (symPart_isHermitian B) (Fin.zero_le k)

/-- **`|e^{-tB}x|² ≤ e^{-2λt}|x|²`** for `t ≥ 0`, `λ = λ_min(sym B)`. -/
theorem norm_sq_mexp_neg_le [NeZero d] (B : Mat d) (x : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    ‖lin (mexp (t • (-B))) x‖ ^ 2 ≤ Real.exp (-(2 * lamMin (symPart B) * t)) * ‖x‖ ^ 2 := by
  set l := lamMin (symPart B) with hl
  set f : ℝ → ℝ := fun u => ‖lin (mexp (u • (-B))) x‖ ^ 2 with hf
  set g : ℝ → ℝ := fun u => Real.exp (2 * l * u) * f u with hg
  have hexp : ∀ u, HasDerivAt (fun u => Real.exp (2 * l * u)) (Real.exp (2 * l * u) * (2 * l)) u :=
    fun u => by
      have := ((hasDerivAt_id u).const_mul (2 * l)).exp
      simpa using this
  have hgd : ∀ u, HasDerivAt g (Real.exp (2 * l * u) * (2 * l) * f u +
      Real.exp (2 * l * u) * (2 * quad (-B) (lin (mexp (u • (-B))) x))) u := fun u =>
    (hexp u).mul (hasDerivAt_norm_sq_mexp (-B) x u)
  have hnp : ∀ u, Real.exp (2 * l * u) * (2 * l) * f u +
      Real.exp (2 * l * u) * (2 * quad (-B) (lin (mexp (u • (-B))) x)) ≤ 0 := by
    intro u
    have hq : l * f u ≤ quad B (lin (mexp (u • (-B))) x) := by
      rw [← quad_symPart]
      exact lamMin_mul_norm_sq_le (symPart_isHermitian B) _
    have hneg : quad (-B) (lin (mexp (u • (-B))) x) = -quad B (lin (mexp (u • (-B))) x) := by
      rw [show (-B : Mat d) = (-1 : ℝ) • B by simp, quad_smul]
      ring
    rw [hneg]
    have he := Real.exp_pos (2 * l * u)
    nlinarith
  have hanti : Antitone g := by
    have hd' : ∀ u, HasDerivAt (fun u => -g u)
        (-(Real.exp (2 * l * u) * (2 * l) * f u +
          Real.exp (2 * l * u) * (2 * quad (-B) (lin (mexp (u • (-B))) x)))) u :=
      fun u => (hgd u).neg
    have := monotone_of_hasDerivAt_nonneg hd' (fun u => by show (0 : ℝ) ≤ _; linarith [hnp u])
    exact fun a b hab => by have := this hab; simp only at this; linarith
  have h0 : g 0 = ‖x‖ ^ 2 := by
    simp [hg, hf, mexp_zero, lin_one]
  have h1 := hanti ht
  rw [h0] at h1
  have hpos := Real.exp_pos (-(2 * l * t))
  calc f t = Real.exp (-(2 * l * t)) * g t := by
        rw [hg]; simp only
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-(2 * l * t)) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hpos.le

/-- A one-dimensional marginal: `\widehat{(⟨e₀, ·⟩)_*μ}(t) = μ̂(t e₀)`. -/
theorem charFun_map_proj [NeZero d] (μ : Measure (Rd d)) (t : ℝ) :
    charFun (μ.map (EuclideanSpace.proj (0 : Fin d) : Rd d →L[ℝ] ℝ)) t =
      charFun μ (t • ebasis 0) := by
  have h := charFun_map_coord μ (0 : Fin d) t
  have hp : (EuclideanSpace.proj (0 : Fin d) : Rd d → ℝ) = fun x => x 0 := by
    funext x
    rfl
  rw [hp]
  exact h

/-- **`prop:anisotropy-budget-converse`** (`prop:anisotropy-budget`(2)): if `tr B < (d+2)λ`, then
`λ > 0`, `e^{-tB} → 0`, and `S_α(I)` is rotation invariant, not Gaussian, and
`B`-self-decomposable for every `α ∈ (0,2)` with `α ≥ tr B/λ - d`. -/
theorem anisotropy_budget_converse (hd : 1 ≤ d) (B : Mat d)
    (hB : B.trace < ((d : ℝ) + 2) * lamMin (symPart B)) :
    0 < lamMin (symPart B) ∧ IsExpContracting B ∧
      ∀ α : ℝ, 0 < α → α < 2 → B.trace / lamMin (symPart B) - d ≤ α →
        ∀ μ : Measure (Rd d), IsEllipticalStable α 1 μ →
          IsRotationInvariant μ ∧ ¬ IsGaussian μ ∧ IsBSelfDecomposable B μ := by
  haveI : NeZero d := ⟨by omega⟩
  set l := lamMin (symPart B) with hl
  have htr := trace_ge_card_mul_lamMin B
  have hl0 : 0 < l := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨hl0, ?_, fun α hα0 hα2 hα μ hμ => ⟨?_, ?_, ?_⟩⟩
  · -- `|e^{-tB}x| ≤ e^{-λt}|x|`, read on the basis vectors
    show Tendsto (fun t : ℝ => mexp (-t • B)) atTop (𝓝 0)
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hbound : ∀ t : ℝ, 0 ≤ t → |mexp (-t • B) i j| ≤ Real.exp (-(l * t)) := by
      intro t ht
      have h1 := norm_sq_mexp_neg_le B (ebasis j) ht
      rw [show t • (-B) = -t • B by rw [smul_neg, neg_smul]] at h1
      have hn : ‖ebasis j‖ = (1 : ℝ) := by simp [ebasis]
      rw [hn, one_pow, mul_one] at h1
      have hentry : |mexp (-t • B) i j| ≤ ‖lin (mexp (-t • B)) (ebasis j)‖ := by
        have : mexp (-t • B) i j = (lin (mexp (-t • B)) (ebasis j)) i := by
          change _ = (mexp (-t • B) *ᵥ (ebasis j).ofLp) i
          simp [ebasis, mulVec, dotProduct]
        rw [this]
        have := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ)
          (lin (mexp (-t • B)) (ebasis j)) i
        rwa [Real.norm_eq_abs] at this
      have hsq : ‖lin (mexp (-t • B)) (ebasis j)‖ ≤ Real.exp (-(l * t)) := by
        have he : Real.exp (-(2 * l * t)) = Real.exp (-(l * t)) ^ 2 := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [he] at h1
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h1
      exact hentry.trans hsq
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(l * t))) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl0)
      simpa [Function.comp_def] using this
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
    exact squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _)
      (eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩) hexp
  · -- rotation invariance: the transform is radial
    haveI := hμ.1
    intro Q hQ
    have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, ellipticalStable_one_charFun hμ, ellipticalStable_one_charFun hμ]
    have hn : ‖lin Qᵀ ω‖ = ‖ω‖ := by
      have h1 := quad_act Q 1 ω
      rw [act, Matrix.mul_one, hQQ, quad_one, quad_one] at h1
      have := congrArg Real.sqrt h1
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
      exact this.symm
    rw [hn]
  · -- not Gaussian: the marginal's transform `e^{-|t|^α}` is not `e^{imt - vt²/2}`
    haveI := hμ.1
    intro hG
    have hmap := hG.map_eq_gaussianReal (EuclideanSpace.proj (0 : Fin d))
    set m := μ[(EuclideanSpace.proj (0 : Fin d) : Rd d →L[ℝ] ℝ)]
    set v := (Var[(EuclideanSpace.proj (0 : Fin d) : Rd d →L[ℝ] ℝ); μ]).toNNReal
    have hcf : ∀ t : ℝ, Real.exp (-(|t| ^ α)) = Real.exp (-((v : ℝ) * t ^ 2 / 2)) := by
      intro t
      have h1 := charFun_map_proj μ t
      rw [hmap, charFun_gaussianReal, ellipticalStable_one_charFun hμ] at h1
      have h2 := congrArg (fun z : ℂ => ‖z‖) h1
      rw [Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
      have hre : ((t : ℂ) * (m : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2).re =
          -((v : ℝ) * t ^ 2 / 2) := by
        simp [Complex.mul_re, Complex.sub_re, pow_two]
      rw [hre] at h2
      have hn : ‖t • ebasis (0 : Fin d)‖ = |t| := by simp [ebasis, norm_smul]
      rw [hn] at h2
      exact h2.symm
    have h1 := Real.exp_injective (hcf 1)
    have h2 := Real.exp_injective (hcf 2)
    simp only [abs_one, Real.one_rpow] at h1
    have hv : (v : ℝ) = 2 := by linarith
    rw [hv, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    have h4 : (2 : ℝ) ^ α = 2 ^ (2 : ℝ) := by norm_num at h2 ⊢; linarith
    have hα : α = 2 := by
      have hlog := congrArg Real.log h4
      rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
      exact mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' hlog
    linarith
  · -- `B`-self-decomposable through `prop:stable-exponent-cone`
    refine (stable_exponent_cone hα0 hα2 B μ hμ).2 ?_
    show B.trace ≤ ((d : ℝ) + α) * l
    have := (div_le_iff₀ hl0).1 (by linarith : B.trace / l ≤ (d : ℝ) + α)
    linarith

end AffineHemigroup
