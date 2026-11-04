/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OrbitRays

/-!
# `prop:matern-cross-shape`: the Matérn orbit of index `1` across shapes

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:matern-cross-shape`. Wave 2, group E,
Q-0281, by the short route the author chose on 2026-10-05: the statement is `prop:matern-steps`
(`matern_steps`) at `γ = 1`, whose ray increment `(Σ^{1/2})_*ν_λ` is identified with
`λ^{-2}δ₀ + (1 - λ^{-2})μ_{Σ'}` by transforms. The Hessian-sign mechanism of the blueprint's
earlier proof is now a remark beside the node, not a step of its proof.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Complex
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- The transform of a two-term mixture `a • μ + b • ν` of probability measures. -/
theorem charFun_mix_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (μ ν : Measure (Rd d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ω : Rd d) :
    charFun (ENNReal.ofReal a • μ + ENNReal.ofReal b • ν) ω =
      (a : ℂ) * charFun μ ω + (b : ℂ) * charFun ν ω := by
  have hint : ∀ (c : ℝ) (m : Measure (Rd d)) [IsProbabilityMeasure m],
      Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * I)) (ENNReal.ofReal c • m) := by
    intro c m _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply, integral_add_measure (hint a μ) (hint b ν), integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, ← charFun_apply,
    ← charFun_apply, Complex.real_smul, Complex.real_smul]

/-- The Matérn orbit of index `1`: `μ̂_T(ω) = (1 + ⟨ω, Tω⟩)^{-1}`. -/
theorem charFun_maternOrbit_one {μI : Measure (Rd d)} (hμI : IsMaternLaw 1 μI) {T : Mat d}
    (hT : T.PosDef) (ω : Rd d) :
    charFun (affineOrbit μI T) ω = (((1 + quad T ω)⁻¹ : ℝ) : ℂ) := by
  haveI := hμI.1
  rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hT), msqrt_transpose, hμI.2,
    norm_sq_lin_msqrt hT.posSemidef, Real.rpow_neg_one]

/-- **`prop:matern-cross-shape`**: for `d ≥ 2`, the Matérn orbit of index `1`, and `Σ ≤ Σ'` in
`PD(d)` with `Σ' ≠ Σ`, a positive finite `ρ` with `μ_{Σ'} = μ_Σ * ρ` exists if and only if
`Σ' = λ²Σ` for some `λ > 1`; and then `ρ` is the probability measure
`λ^{-2}δ₀ + (1 - λ^{-2})μ_{Σ'}`. -/
theorem matern_cross_shape (hd : 2 ≤ d) (μI : Measure (Rd d)) (hμI : IsMaternLaw 1 μI)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (_hle : loewnerLE S S') (hne : S' ≠ S) :
    ((∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ affineOrbit μI S' = affineOrbit μI S ∗ ρ) ↔
        ∃ lam : ℝ, 1 < lam ∧ S' = lam ^ 2 • S) ∧
      ∀ lam : ℝ, 1 < lam → S' = lam ^ 2 • S →
        IsProbabilityMeasure (ENNReal.ofReal ((lam ^ 2)⁻¹) • Measure.dirac (0 : Rd d) +
          ENNReal.ofReal (1 - (lam ^ 2)⁻¹) • affineOrbit μI S') ∧
        ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
          (affineOrbit μI S' = affineOrbit μI S ∗ ρ ↔
            ρ = ENNReal.ofReal ((lam ^ 2)⁻¹) • Measure.dirac (0 : Rd d) +
              ENNReal.ofReal (1 - (lam ^ 2)⁻¹) • affineOrbit μI S') := by
  haveI := hμI.1
  have hmain := matern_steps (by omega) 1 one_pos μI hμI hS hS' hne
  refine ⟨hmain.1, fun lam hlam hSS => ?_⟩
  obtain ⟨hprob, hiff⟩ := hmain.2 lam hlam hSS
  set M : Measure (Rd d) := ENNReal.ofReal ((lam ^ 2)⁻¹) • Measure.dirac (0 : Rd d) +
    ENNReal.ofReal (1 - (lam ^ 2)⁻¹) • affineOrbit μI S' with hM
  haveI : IsProbabilityMeasure (affineOrbit μI S') := by unfold affineOrbit; infer_instance
  haveI : IsProbabilityMeasure (affineOrbit μI S) := by unfold affineOrbit; infer_instance
  haveI : IsFiniteMeasure M := ⟨by
    rw [hM, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩⟩
  have hl2 : 0 < lam ^ 2 := by positivity
  have hinv : (lam ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  -- `μ_{Σ'} = μ_Σ * M`, by transforms
  have hconv : affineOrbit μI S' = affineOrbit μI S ∗ M := by
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_conv, hM, charFun_mix_two (inv_nonneg.2 hl2.le) (by linarith), charFun_dirac,
      charFun_maternOrbit_one hμI hS', charFun_maternOrbit_one hμI hS, hSS, quad_smul]
    have hu : 0 ≤ quad S ω := quad_nonneg hS.posSemidef ω
    have key : (1 + lam ^ 2 * quad S ω)⁻¹ = (1 + quad S ω)⁻¹ *
        ((lam ^ 2)⁻¹ * 1 + (1 - (lam ^ 2)⁻¹) * (1 + lam ^ 2 * quad S ω)⁻¹) := by
      have h1 : 0 < 1 + quad S ω := by linarith
      have h2 : 0 < 1 + lam ^ 2 * quad S ω := by positivity
      field_simp
      ring
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact_mod_cast key
  have hMeq : M = push (msqrt S) (maternRayLaw d 1 lam) := (hiff M inferInstance).1 hconv
  refine ⟨by rw [hMeq]; exact hprob, fun ρ hρ => ?_⟩
  rw [hiff ρ hρ, ← hMeq]
