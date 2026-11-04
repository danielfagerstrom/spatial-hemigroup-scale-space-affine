/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Rigidity
import AffineHemigroup.RayFamilies
import AffineHemigroup.ScaleShape
import AffineHemigroup.MatrixCalculus

/-!
# `prop:affine-orbits`(1)–(3) and `prop:ray-families` — the base `(GL(d), rays)`

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:affine-orbits` (clauses (1)–(3); clause (4) is
the split child `prop:affine-orbits-matern`) and `prop:ray-families`. Lean core only: the
uniqueness of the transform is Mathlib's `Measure.ext_of_charFun`, and clause (3) reads
`thm:rank-deficient-step` and `thm:affine-rigidity`, both proved.

## The route

The blueprint's, step for step. `prop:affine-orbits` is read through the transforms
`μ̂_Σ(ω) = μ̂_I(Σ^{1/2}ω)` and `|Σ^{1/2}ω|² = ⟨ω, Σω⟩`; for the last sentence of (3) the proof takes
the blueprint's second route, through `thm:affine-rigidity`. `prop:ray-families` is pushforward and
convolution (Mathlib's `Measure.map_conv_continuousLinearMap`), with the transform only where
self-decomposability is defined by it; in the converse the orthogonal matrix is
`Q := Σ'^{-1/2}AΣ^{1/2}`, whose `QQᵀ = Σ'^{-1/2}Σ'Σ'^{-1/2} = I` is the relative step of `Σ'` to
itself (`AffineHemigroup.ScaleShape`).
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## The calculus of images and affine orbits -/

/-- The image of an image: `A_*(B_*μ) = (AB)_*μ`. -/
theorem push_push (A B : Mat d) (μ : Measure (Rd d)) : push A (push B μ) = push (A * B) μ := by
  rw [push, push, push, Measure.map_map (lin A).measurable (lin B).measurable, lin_mul]
  rfl

/-- The image of a convolution is the convolution of the images. -/
theorem push_conv (A : Mat d) (μ ν : Measure (Rd d)) [SFinite μ] [SFinite ν] :
    push A (μ ∗ ν) = push A μ ∗ push A ν :=
  Measure.map_conv_continuousLinearMap (lin A)

/-- `A · (cΣ) = c (A · Σ)`. -/
theorem act_smul (A : Mat d) (c : ℝ) (S : Mat d) : act A (c • S) = c • act A S := by
  simp only [act, Matrix.mul_smul, Matrix.smul_mul]

/-- The orbit at `I` is the law itself. -/
theorem affineOrbit_one (μI : Measure (Rd d)) : affineOrbit μI 1 = μI := by
  rw [affineOrbit, msqrt, CFC.sqrt_one, push_one]

/-- The transform of an affine orbit, for every law: `μ̂_Σ(ω) = μ̂_I(Σ^{1/2}ω)`. -/
theorem charFun_affineOrbit_lin (μI : Measure (Rd d)) (S : Mat d) (ω : Rd d) :
    charFun (affineOrbit μI S) ω = charFun μI (lin (msqrt S) ω) := by
  rw [affineOrbit, push, charFun_map_lin, msqrt_transpose]

/-- `|Σ^{1/2}ω|² = ⟨ω, Σω⟩` for `Σ ∈ PSD(d)`. -/
theorem norm_sq_lin_msqrt {S : Mat d} (hS : S.PosSemidef) (ω : Rd d) :
    ‖lin (msqrt S) ω‖ ^ 2 = quad S ω := by
  rw [← real_inner_self_eq_norm_sq, inner_lin_left, msqrt_transpose]
  conv_rhs => rw [quad, ← msqrt_mul_self hS, lin_mul]
  rfl

/-- The transform of the orbit of `μ_I` with `μ̂_I(ω) = e^{-g(|ω|²)}`:
`μ̂_Σ(ω) = e^{-g(⟨ω,Σω⟩)}` for every `Σ ∈ PSD(d)`. -/
theorem charFun_affineOrbit_exp {g : ℝ → ℝ} {μI : Measure (Rd d)}
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) {S : Mat d}
    (hS : S.PosSemidef) (ω : Rd d) :
    charFun (affineOrbit μI S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) := by
  rw [charFun_affineOrbit_lin, hμI, norm_sq_lin_msqrt hS]

/-- Every `u ≥ 0` is `|ω|²` for some `ω ∈ ℝ^d`, `d ≥ 1`. -/
theorem exists_norm_sq_eq (hd : 1 ≤ d) {u : ℝ} (hu : 0 ≤ u) : ∃ ω : Rd d, ‖ω‖ ^ 2 = u := by
  refine ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (Real.sqrt u), ?_⟩
  simp [sq_abs, Real.sq_sqrt hu]

/-- The exponent is read off the transform: if `e^{-g(|ω|²)} = e^{-b|ω|²}` for every `ω`, then
`g(u) = bu` for every `u ≥ 0`. -/
theorem eq_mul_of_exp_eq (hd : 1 ≤ d) {g : ℝ → ℝ} {b : ℝ}
    (h : ∀ ω : Rd d, ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(b * ‖ω‖ ^ 2)) : ℝ) : ℂ)) :
    ∀ u : ℝ, 0 ≤ u → g u = b * u := by
  intro u hu
  obtain ⟨ω, hω⟩ := exists_norm_sq_eq hd hu
  have h1 := Real.exp_injective (Complex.ofReal_injective (h ω))
  rw [hω] at h1
  linarith

/-- The transform of the centred Gaussian law with covariance `2bI`: `e^{-b|ω|²}`. -/
theorem charFun_gaussian_smul_one {b : ℝ} (hb : 0 ≤ b) (ω : Rd d) :
    charFun (multivariateGaussian 0 ((2 * b) • (1 : Mat d))) ω =
      ((Real.exp (-(b * ‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  rw [charFun_multivariateGaussian_zero (PosSemidef.one.smul (by positivity)), quad_smul, quad_one]
  congr 3
  ring

/-! ## `prop:affine-orbits`, clauses (1)–(3) -/

/-- **`prop:affine-orbits`(1)**, covariance: `μ̂_Σ(ω) = e^{-g(⟨ω,Σω⟩)}`, and
`A_*μ_Σ = μ_{AΣAᵀ}` for every `A ∈ GL(d)` and `Σ ∈ PD(d)`. -/
theorem affine_orbit_covariance (_hd : 1 ≤ d) (g : ℝ → ℝ) (_hg_cont : ContinuousOn g (Ici 0))
    (_hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (_hg0 : g 0 = 0) (μI : Measure (Rd d))
    [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) :
    (∀ S : Mat d, S.PosDef → ∀ ω : Rd d,
        charFun (affineOrbit μI S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ)) ∧
      ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef →
        push A (affineOrbit μI S) = affineOrbit μI (act A S) := by
  refine ⟨fun S hS ω => charFun_affineOrbit_exp hμI hS.posSemidef ω, fun A _ S hS => ?_⟩
  apply eq_of_charFun_eq
  intro ω
  rw [push, charFun_map_lin, charFun_affineOrbit_exp hμI hS.posSemidef,
    charFun_affineOrbit_exp hμI (posSemidef_act A hS.posSemidef), quad_act]

/-- **`prop:affine-orbits`(2)**, cascade along rays: if for some `λ > 1` a probability measure
`ν_λ` has `e^{-g(λ²|ω|²)} = e^{-g(|ω|²)} ν̂_λ(ω)`, then `μ_{λ²Σ} = μ_Σ * (Σ^{1/2})_*ν_λ` for every
`Σ ∈ PD(d)`. -/
theorem affine_orbit_ray_cascade (_hd : 1 ≤ d) (g : ℝ → ℝ) (_hg_cont : ContinuousOn g (Ici 0))
    (_hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (_hg0 : g 0 = 0) (μI : Measure (Rd d))
    [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    (lam : ℝ) (_hlam : 1 < lam) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (hν : ∀ ω : Rd d, ((Real.exp (-g (lam ^ 2 * ‖ω‖ ^ 2)) : ℝ) : ℂ) =
      ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) * charFun ν ω) :
    ∀ S : Mat d, S.PosDef →
      affineOrbit μI (lam ^ 2 • S) = affineOrbit μI S ∗ push (msqrt S) ν := by
  intro S hS
  apply eq_of_charFun_eq
  intro ω
  rw [charFun_conv, charFun_affineOrbit_exp hμI (hS.posSemidef.smul (sq_nonneg lam)),
    charFun_affineOrbit_exp hμI hS.posSemidef, push, charFun_map_lin, msqrt_transpose, quad_smul,
    ← norm_sq_lin_msqrt hS.posSemidef, hν]

/-- **`prop:affine-orbits`(3)**, no cascade across shapes: for `d ≥ 2` and `g` not linear, no
`Σ ∈ PD(d)` and `P ∈ PSD(d)` with `0 < rank P < d` have `μ_{Σ+P} = μ_Σ * ρ` with `ρ` a probability
measure; in particular the orbit is not the family of kernels from the origin of any affine cascade
family. -/
theorem affine_orbit_no_cross_shape (hd : 2 ≤ d) (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Ici 0))
    (hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (hg0 : g 0 = 0) (μI : Measure (Rd d))
    [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    (hlin : ¬ ∃ b : ℝ, ∀ u : ℝ, 0 ≤ u → g u = b * u) :
    (∀ S P : Mat d, S.PosDef → P.PosSemidef → 0 < P.rank → P.rank < d →
        ¬ ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
          affineOrbit μI (S + P) = affineOrbit μI S ∗ ρ) ∧
      ¬ ∃ μ : Mat d → Mat d → Measure (Rd d), IsAffineCascadeFamily μ ∧
          ∀ S : Mat d, S.PosDef → μ 0 S = affineOrbit μI S := by
  refine ⟨?_, ?_⟩
  · rintro S P hS hP hpos hlt ⟨ρ, hρ, heq⟩
    have hstep : ∀ ω : Rd d, ((Real.exp (-g (quad (S + P) ω)) : ℝ) : ℂ) =
        ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * charFun ρ ω := by
      intro ω
      have h := congrArg (fun m => charFun m ω) heq
      rwa [charFun_conv, charFun_affineOrbit_exp hμI (hS.posSemidef.add hP),
        charFun_affineOrbit_exp hμI hS.posSemidef] at h
    obtain ⟨hg, -, -⟩ := rank_deficient_step hd g hg_nonneg (hg_cont 0 self_mem_Ici) hg0 S P hS hP
      hpos hlt ρ hstep
    exact hlin ⟨g 1, hg⟩
  · rintro ⟨μ, hμ, hμS⟩
    obtain ⟨b, hb, hμ1⟩ := affine_rigidity_kernel hd μ hμ
    rw [hμS 1 PosDef.one, affineOrbit_one] at hμ1
    apply hlin
    refine ⟨b, eq_mul_of_exp_eq (by omega : 1 ≤ d) fun ω => ?_⟩
    rw [← hμI, hμ1, charFun_gaussian_smul_one hb.le]

/-! ## `prop:ray-families` -/

/-- **`prop:ray-families`**: probability measures `(μ_Σ)` on `PD(d)` with (R1) affine covariance and
(R2) a cascade along the ray of `I` have `μ_I` rotation invariant and self-decomposable,
`μ_Σ = (Σ^{1/2})_*μ_I`, and cascade along every ray: `μ_{λ²Σ} = μ_Σ * (Σ^{1/2})_*ρ_λ`. -/
theorem ray_families (_hd : 1 ≤ d) (μ : Mat d → Measure (Rd d))
    (hprob : ∀ S : Mat d, S.PosDef → IsProbabilityMeasure (μ S))
    (hR1 : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (μ S) = μ (act A S))
    (hR2 : ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      μ (lam ^ 2 • (1 : Mat d)) = μ 1 ∗ ρ) :
    IsRotationInvariant (μ 1) ∧ IsSelfDecomposable (μ 1) ∧
      (∀ S : Mat d, S.PosDef → μ S = affineOrbit (μ 1) S) ∧
      ∀ S : Mat d, S.PosDef → ∀ lam : ℝ, 1 < lam → ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
        μ (lam ^ 2 • (1 : Mat d)) = μ 1 ∗ ρ → μ (lam ^ 2 • S) = μ S ∗ push (msqrt S) ρ := by
  haveI : IsProbabilityMeasure (μ 1) := hprob 1 PosDef.one
  /- Covariance determines the orbit. -/
  have horbit : ∀ S : Mat d, S.PosDef → μ S = affineOrbit (μ 1) S := by
    intro S hS
    have h := hR1 (msqrt S) (msqrt_mem_glSet hS) 1 PosDef.one
    rw [act_msqrt_one hS.posSemidef] at h
    rw [← h, affineOrbit]
  have hrot : IsRotationInvariant (μ 1) := by
    intro Q hQ
    rw [hR1 Q (orthSet_subset_glSet hQ) 1 PosDef.one, act_orth_one hQ]
  /- Self-decomposability. -/
  have hsd : IsSelfDecomposable (μ 1) := by
    rw [isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    have hlam : 1 < c⁻¹ := (one_lt_inv₀ hc0).2 hc1
    obtain ⟨ρ, hρ, hρeq⟩ := hR2 c⁻¹ hlam
    refine ⟨push (c • (1 : Mat d)) ρ, inferInstance, fun ξ => ?_⟩
    have h := hR1 (c⁻¹ • (1 : Mat d)) (glSet_isClosedSubgroupGL.2 _ (inv_pos.2 hc0)) 1 PosDef.one
    rw [act_smul_one, hρeq] at h
    have h2 := congrArg (fun m => charFun m (c • ξ)) h
    rw [charFun_push_smul_one, charFun_conv, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] at h2
    rw [h2, charFun_push_smul_one]
  /- Every ray. -/
  refine ⟨hrot, hsd, horbit, fun S hS lam hlam ρ hρ hρeq => ?_⟩
  have hlam2 : (lam ^ 2 • (1 : Mat d)).PosDef := PosDef.one.smul (by positivity)
  have h := hR1 (msqrt S) (msqrt_mem_glSet hS) _ hlam2
  rw [act_smul, act_msqrt_one hS.posSemidef, hρeq, push_conv] at h
  rw [← h, horbit S hS, affineOrbit]

/-- **`prop:ray-families`**, the converse: for every rotation-invariant self-decomposable law `μ_I`
the family `μ_Σ := (Σ^{1/2})_*μ_I` satisfies (R1) and (R2). -/
theorem ray_families_converse (_hd : 1 ≤ d) (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI) :
    (∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef →
        push A (affineOrbit μI S) = affineOrbit μI (act A S)) ∧
      ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
        affineOrbit μI (lam ^ 2 • (1 : Mat d)) = affineOrbit μI 1 ∗ ρ := by
  refine ⟨fun A hA S hS => ?_, fun lam hlam => ?_⟩
  /- (R1): `Q := Σ'^{-1/2} A Σ^{1/2}` is orthogonal and `AΣ^{1/2} = Σ'^{1/2} Q`. -/
  · set S' := act A S with hS'def
    have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hA
    have hS' : S'.PosDef := by
      have h := Matrix.IsUnit.posDef_star_right_conjugate_iff hAu (x := S)
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact h.2 hS
    set Q := (msqrt S')⁻¹ * (A * msqrt S) with hQdef
    have hQQ : Q * Qᵀ = 1 := by
      have hB : (A * msqrt S) * (A * msqrt S)ᵀ = S' := by
        rw [transpose_mul, msqrt_transpose, mul_assoc, ← mul_assoc (msqrt S),
          msqrt_mul_self hS.posSemidef, ← mul_assoc]
        rfl
      rw [hQdef, transpose_mul, msqrt_inv_transpose, mul_assoc, ← mul_assoc (A * msqrt S), hB,
        ← mul_assoc]
      exact relStep_self hS'
    have hQ : Q ∈ orthSet d := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hQQ
    have hAQ : A * msqrt S = msqrt S' * Q := by
      rw [hQdef, ← mul_assoc, msqrt_mul_inv hS', one_mul]
    rw [affineOrbit, push_push, hAQ, ← push_push, hrot Q hQ, ← affineOrbit]
  /- (R2): the residual of self-decomposability at `c = λ⁻¹`, pushed by `λI`. -/
  · have hlam0 : 0 < lam := zero_lt_one.trans hlam
    obtain ⟨ρ, hρ, hρeq⟩ := (isSelfDecomposable_iff_charFun μI).1 hsd lam⁻¹ (inv_pos.2 hlam0)
      (inv_lt_one_of_one_lt₀ hlam)
    refine ⟨push (lam • (1 : Mat d)) ρ, inferInstance, ?_⟩
    rw [affineOrbit_one, affineOrbit, msqrt_sq_smul_one hlam0.le]
    apply eq_of_charFun_eq
    intro ω
    rw [charFun_conv, charFun_push_smul_one, charFun_push_smul_one, hρeq, smul_smul,
      inv_mul_cancel₀ hlam0.ne', one_smul]

end AffineHemigroup
