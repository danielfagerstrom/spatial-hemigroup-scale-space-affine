/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Rigidity
import AffineHemigroup.RadialTransform
import AffineHemigroup.Gauge

/-!
# `prop:affine-rigidity-boundary` — continuity is needed only at the boundary of `PSD(d)`

Blueprint: `blueprint/src/parts/04-classical.tex`, `prop:affine-rigidity-boundary`. Lean core only.

The hypothesis of the node is a family with (K1), (K3) and (K4) but not necessarily (K2), which
`IsGWCascadeFamily` cannot say: `IsAffineCascadeFamilyNoK2` is that structure without `continuous`,
at `glSet d` and `loewnerLE`, and `IsAffineCascadeFamily.toNoK2` is the forgetful map.

## The route

The blueprint's, with two choices of the Lean proof:

* **Clause (1).** The first step of `lem:affine-reduction` and the positivity and logarithm of its
  last step are `exists_exp_of_rotationInvariant`, at a law that is rotation invariant by (K3) at
  `O(d)` and whose transform has no zero. The self-decomposability is written out here at the
  predicate, since `gw_kernels_selfDecomposable` asks for a whole `(G, W)`-cascade family: (K1) at
  `0 ≤ c²I ≤ I` and (K3) at `cI`. Then `rank_deficient_step` at `I ≤ I + e₁e₁ᵀ`.
* **Clause (2).** Transforms throughout: `charFun_boundaryFamily`, then the uniqueness of the
  transform. "Not an affine Gaussian scale space" is proved for every real constant `b'`, not only a
  positive one; a negative `b'` makes `affineGaussian b' 0 1` a Dirac mass, since Mathlib's
  `multivariateGaussian` of a matrix that is not positive semidefinite is one, and it is excluded by
  the transform at `(0, I)` like the others.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set Filter
open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-- **The hypothesis of `prop:affine-rigidity-boundary`**: probability measures `μ Σ Σ'`, indexed by
the Loewner pairs of `PSD(d)`, with (K1), (K3) and (K4) of `def:affine-cascade-family`, not
necessarily (K2). The fields are those of `IsGWCascadeFamily` at `glSet d` and `loewnerLE`, without
`continuous`. -/
structure IsAffineCascadeFamilyNoK2 (μ : Mat d → Mat d → Measure (Rd d)) : Prop where
  /-- Each `μ Σ Σ'`, for a Loewner pair of `PSD(d)`, is a probability measure. -/
  isProbability : ∀ p ∈ wedgePairs (d := d) loewnerLE, IsProbabilityMeasure (μ p.1 p.2)
  /-- **(K1)**, the diagonal. -/
  diag : ∀ S : Mat d, S.PosSemidef → μ S S = Measure.dirac 0
  /-- **(K1)**, the cascade. -/
  cascade : ∀ S S' S'' : Mat d, S.PosSemidef → S'.PosSemidef → S''.PosSemidef →
    loewnerLE S S' → loewnerLE S' S'' → μ S S'' = μ S' S'' ∗ μ S S'
  /-- **(K3)**, at `GL(d)`. -/
  covariant : ∀ A ∈ glSet d, ∀ p ∈ wedgePairs (d := d) loewnerLE,
    push A (μ p.1 p.2) = μ (act A p.1) (act A p.2)
  /-- **(K4)**. -/
  nondegenerate : μ 0 1 ≠ Measure.dirac 0

/-- An affine cascade family satisfies (K1), (K3) and (K4). -/
theorem IsAffineCascadeFamily.toNoK2 {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : IsAffineCascadeFamily μ) : IsAffineCascadeFamilyNoK2 μ :=
  ⟨hμ.isProbability, hμ.diag, hμ.cascade, hμ.covariant, hμ.nondegenerate⟩

private theorem loewnerLE_zero_of_posSemidef {S : Mat d} (hS : S.PosSemidef) : loewnerLE 0 S := by
  rw [loewnerLE, sub_zero]
  exact hS

private theorem mem_pairs_zero {S : Mat d} (hS : S.PosSemidef) :
    ((0 : Mat d), S) ∈ wedgePairs loewnerLE :=
  ⟨PosSemidef.zero, hS, loewnerLE_zero_of_posSemidef hS⟩

/-- **The rank-one step `e₁e₁ᵀ`**, with what both clauses read of it: positive semidefinite, of rank
`1`, and a vector on which its quadratic form is positive. -/
private theorem exists_rank_one_step (hd : 2 ≤ d) :
    ∃ P : Mat d, P.PosSemidef ∧ P.rank = 1 ∧ ∃ ω : Rd d, 0 < quad P ω := by
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  refine ⟨diagonal (Pi.single i₀ 1), ?_, ?_, EuclideanSpace.single i₀ (1 : ℝ), ?_⟩
  · apply PosSemidef.diagonal
    intro i
    by_cases h : i = i₀
    · subst h
      simp
    · simp [h]
  · classical
    rw [rank_diagonal, Fintype.card_eq_one_iff]
    refine ⟨⟨i₀, by simp⟩, ?_⟩
    rintro ⟨j, hj⟩
    apply Subtype.ext
    by_contra hne
    exact hj (by simp [hne])
  · rw [quad_eq_dotProduct]
    simp [dotProduct, mulVec_diagonal, Pi.single_apply]

/-- A matrix of rank below the dimension is not positive definite. -/
private theorem not_posDef_of_rank_lt {P : Mat d} (h : P.rank < d) : ¬ P.PosDef := fun hP => by
  have := Matrix.rank_of_isUnit P hP.isUnit
  rw [Fintype.card_fin] at this
  omega

/-! ## Clause (1) -/

/-- (K3) at `O(d)` makes `μ_I` rotation invariant. -/
theorem IsAffineCascadeFamilyNoK2.rotationInvariant {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : IsAffineCascadeFamilyNoK2 μ) : IsRotationInvariant (μ 0 1) := by
  intro Q hQ
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  have h := hμ.covariant Q (orthSet_subset_glSet hQ) _ (mem_pairs_zero PosSemidef.one)
  have h1 : act Q (1 : Mat d) = 1 := by rw [act, mul_one, hQQ]
  simpa only [act_zero, h1] using h

/-- **`μ_I` is self-decomposable**, from (K1) at `0 ≤ c²I ≤ I` and (K3) at `cI`: the argument of
`gw_kernels_selfDecomposable`, at a family without (K2). -/
theorem IsAffineCascadeFamilyNoK2.selfDecomposable {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : IsAffineCascadeFamilyNoK2 μ) : IsSelfDecomposable (μ 0 1) := by
  haveI h1 : IsProbabilityMeasure (μ 0 1) := hμ.isProbability _ (mem_pairs_zero PosSemidef.one)
  rw [isSelfDecomposable_iff_charFun]
  intro c hc0 hc1
  have hs : (c ^ 2 • (1 : Mat d)).PosSemidef := PosSemidef.one.smul (by positivity)
  have hs1 : loewnerLE (c ^ 2 • (1 : Mat d)) 1 := by
    have : (1 : Mat d) - c ^ 2 • (1 : Mat d) = (1 - c ^ 2) • (1 : Mat d) := by
      rw [sub_smul, one_smul]
    rw [loewnerLE, this]
    exact PosSemidef.one.smul (by nlinarith)
  haveI hρ : IsProbabilityMeasure (μ (c ^ 2 • (1 : Mat d)) 1) :=
    hμ.isProbability (_, _) ⟨hs, PosSemidef.one, hs1⟩
  haveI h2 : IsProbabilityMeasure (μ 0 (c ^ 2 • (1 : Mat d))) :=
    hμ.isProbability _ (mem_pairs_zero hs)
  refine ⟨μ (c ^ 2 • (1 : Mat d)) 1, hρ, fun ξ => ?_⟩
  have hb := hμ.covariant (c • (1 : Mat d)) (glSet_isClosedSubgroupGL.2 c hc0) _
    (mem_pairs_zero PosSemidef.one)
  simp only [act_zero, act_smul_one] at hb
  have hc := congrArg (fun m => charFun m ξ) (hμ.cascade 0 _ 1 PosSemidef.zero hs PosSemidef.one
    (loewnerLE_zero_of_posSemidef hs) hs1)
  simp only [charFun_conv] at hc
  rw [hc, ← hb, charFun_push_smul_one, mul_comm]

/-- **`prop:affine-rigidity-boundary`(1)**: for `d ≥ 2`, a family with (K1), (K3) and (K4) is,
between positive definite apertures, the Gaussian family: there is `b > 0` such that `μ_Σ` is the
centred Gaussian law with covariance `2bΣ` for `Σ ∈ PD(d)`, `μ_{Σ,Σ'}` the one with covariance
`2b(Σ' - Σ)` for `Σ ≤ Σ'` in `PD(d)`, and `μ_I` the one with covariance `2bI`. -/
theorem affine_rigidity_interior (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsAffineCascadeFamilyNoK2 μ) :
    ∃ b : ℝ, 0 < b ∧
      (∀ S : Mat d, S.PosDef → μ 0 S = multivariateGaussian 0 ((2 * b) • S)) ∧
      (∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
        μ S S' = multivariateGaussian 0 ((2 * b) • (S' - S))) ∧
      μ 0 1 = multivariateGaussian 0 ((2 * b) • (1 : Mat d)) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI h1 : IsProbabilityMeasure (μ 0 1) := hμ.isProbability _ (mem_pairs_zero PosSemidef.one)
  have hprob0 : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (μ 0 S) := fun S hS =>
    hμ.isProbability _ (mem_pairs_zero hS)
  /- The radial form of `μ̂_I`, without zeros. -/
  obtain ⟨g, hgc, hgnn, hg0, hg⟩ := exists_exp_of_rotationInvariant (μ 0 1) hμ.rotationInvariant
    (selfDecomposable_charFun_ne_zero _ hμ.selfDecomposable).1
  /- `μ̂_Σ` for `Σ ∈ PD(d)`, by (K3) at `Σ^{1/2}`. -/
  have hPD : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d,
      charFun (μ 0 S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) := by
    intro S hS ω
    have hR := msqrt_mem_glSet hS
    have h := hμ.covariant (msqrt S) hR _ (mem_pairs_zero PosSemidef.one)
    simp only [act_zero, act_msqrt_one hS.posSemidef] at h
    have hq : ‖lin (msqrt S)ᵀ ω‖ ^ 2 = quad S ω := by
      have h2 := quad_act (msqrt S) 1 ω
      rw [act_msqrt_one hS.posSemidef, quad_one] at h2
      exact h2.symm
    rw [← h, charFun_push _ hR, hg, hq]
  /- The rank-one step `I ≤ I + P`, and `g` is linear. -/
  obtain ⟨P, hP, hrank, -⟩ := exists_rank_one_step hd
  have hIP : loewnerLE (1 : Mat d) (1 + P) := by
    rw [loewnerLE, add_sub_cancel_left]
    exact hP
  have hIPs : (1 + P : Mat d).PosSemidef := PosSemidef.one.add hP
  have hIPd : (1 + P : Mat d).PosDef := PosDef.add_posSemidef PosDef.one hP
  haveI hρ : IsProbabilityMeasure (μ 1 (1 + P)) :=
    hμ.isProbability (_, _) ⟨PosSemidef.one, hIPs, hIP⟩
  have hstep : ∀ ω : Rd d, ((Real.exp (-g (quad (1 + P) ω)) : ℝ) : ℂ) =
      ((Real.exp (-g (quad 1 ω)) : ℝ) : ℂ) * charFun (μ 1 (1 + P)) ω := by
    intro ω
    rw [← hPD _ hIPd, ← hPD _ PosDef.one, hμ.cascade 0 1 (1 + P) PosSemidef.zero PosSemidef.one hIPs
      (loewnerLE_zero_of_posSemidef PosSemidef.one) hIP, charFun_conv, mul_comm]
  obtain ⟨hlin, hb0, -⟩ := rank_deficient_step hd g hgnn (hgc 0 self_mem_Ici) hg0 1 P
    PosDef.one hP (by rw [hrank]; norm_num) (by rw [hrank]; omega) (μ 1 (1 + P)) hstep
  /- `b := g 1` is positive, by (K4). -/
  have hb : 0 < g 1 := by
    refine lt_of_le_of_ne hb0 fun h => hμ.nondegenerate ?_
    apply eq_dirac_of_charFun_one_near_zero _ 1 one_pos
    intro η _
    rw [hg, hlin _ (sq_nonneg _), ← h, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one]
  /- The transforms, in closed form. -/
  have hPD' : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d,
      charFun (μ 0 S) ω = ((Real.exp (-(g 1 * quad S ω)) : ℝ) : ℂ) := by
    intro S hS ω
    rw [hPD S hS, hlin _ (quad_nonneg hS.posSemidef ω)]
  have hkernel : ∀ S : Mat d, S.PosDef → μ 0 S = multivariateGaussian 0 ((2 * g 1) • S) := by
    intro S hS
    haveI := hprob0 S hS.posSemidef
    have hX : ((2 * g 1) • S).PosSemidef := hS.posSemidef.smul (by positivity)
    apply Measure.ext_of_charFun
    funext ω
    rw [hPD' S hS, charFun_multivariateGaussian_zero hX, quad_smul]
    congr 2
    ring
  refine ⟨g 1, hb, hkernel, ?_, hkernel 1 PosDef.one⟩
  /- The increments, dividing by `μ̂_Σ`, which has no zero. -/
  intro S S' hS hS' hle
  haveI := hprob0 S hS.posSemidef
  haveI hpair : IsProbabilityMeasure (μ S S') :=
    hμ.isProbability (_, _) ⟨hS.posSemidef, hS'.posSemidef, hle⟩
  have hX : ((2 * g 1) • (S' - S)).PosSemidef := PosSemidef.smul hle (by positivity)
  apply Measure.ext_of_charFun
  funext ω
  have hc := congrArg (fun m => charFun m ω) (hμ.cascade 0 S S' PosSemidef.zero hS.posSemidef
    hS'.posSemidef (loewnerLE_zero_of_posSemidef hS.posSemidef) hle)
  simp only [charFun_conv, hPD' S hS, hPD' S' hS'] at hc
  have hne : ((Real.exp (-(g 1 * quad S ω)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
  apply mul_right_cancel₀ hne
  rw [← hc, charFun_multivariateGaussian_zero hX, quad_smul, quad_sub, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  ring

/-! ## Clause (2) -/

open Classical in
/-- **The factor `θ` of `prop:affine-rigidity-boundary`(2)**: `1` on `PD(d)`, `θ₀` off it, which on
`PSD(d)` is the singular matrices. -/
noncomputable def boundaryTheta (θ₀ : ℝ) (S : Mat d) : ℝ := if S.PosDef then 1 else θ₀

/-- The matrix `θ(Σ')Σ' - θ(Σ)Σ`. -/
noncomputable def boundaryCov (θ₀ : ℝ) (S S' : Mat d) : Mat d :=
  boundaryTheta θ₀ S' • S' - boundaryTheta θ₀ S • S

/-- **The family of `prop:affine-rigidity-boundary`(2)**: `μ_{Σ,Σ'}` is the centred Gaussian law
with covariance `2b(θ(Σ')Σ' - θ(Σ)Σ)`. -/
noncomputable def boundaryFamily (b θ₀ : ℝ) (S S' : Mat d) : Measure (Rd d) :=
  multivariateGaussian 0 ((2 * b) • boundaryCov θ₀ S S')

private theorem boundaryTheta_of_posDef (θ₀ : ℝ) {S : Mat d} (hS : S.PosDef) :
    boundaryTheta θ₀ S = 1 := by
  simp [boundaryTheta, hS]

private theorem boundaryTheta_of_not_posDef (θ₀ : ℝ) {S : Mat d} (hS : ¬ S.PosDef) :
    boundaryTheta θ₀ S = θ₀ := by
  simp [boundaryTheta, hS]

/-- `GL(d)` preserves the rank, so `θ(AΣAᵀ) = θ(Σ)` on `PSD(d)`. -/
private theorem boundaryTheta_act (θ₀ : ℝ) {A S : Mat d} (hA : A ∈ glSet d) (hS : S.PosSemidef) :
    boundaryTheta θ₀ (act A S) = boundaryTheta θ₀ S := by
  have hiff : (act A S).PosDef ↔ S.PosDef := by
    rw [(posSemidef_act A hS).posDef_iff_det_ne_zero, hS.posDef_iff_det_ne_zero, act, det_mul,
      det_mul, det_transpose]
    have hA0 : A.det ≠ 0 := IsUnit.ne_zero hA
    simp [hA0]
  by_cases h : S.PosDef
  · rw [boundaryTheta_of_posDef θ₀ h, boundaryTheta_of_posDef θ₀ (hiff.2 h)]
  · rw [boundaryTheta_of_not_posDef θ₀ h, boundaryTheta_of_not_posDef θ₀ (fun h' => h (hiff.1 h'))]

private theorem boundaryCov_act (θ₀ : ℝ) {A S S' : Mat d} (hA : A ∈ glSet d) (hS : S.PosSemidef)
    (hS' : S'.PosSemidef) : boundaryCov θ₀ (act A S) (act A S') = act A (boundaryCov θ₀ S S') := by
  rw [boundaryCov, boundaryCov, boundaryTheta_act θ₀ hA hS, boundaryTheta_act θ₀ hA hS']
  simp only [act, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- **The covariances**: `θ(Σ')Σ' - θ(Σ)Σ` is positive semidefinite on every Loewner pair. -/
theorem boundaryCov_posSemidef {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1) {S S' : Mat d}
    (hS : S.PosSemidef) (hle : loewnerLE S S') : (boundaryCov θ₀ S S').PosSemidef := by
  by_cases hd : S.PosDef
  · have hd' : S'.PosDef := by
      have := PosDef.add_posSemidef hd hle
      rwa [add_sub_cancel] at this
    rw [boundaryCov, boundaryTheta_of_posDef θ₀ hd, boundaryTheta_of_posDef θ₀ hd', one_smul,
      one_smul]
    exact hle
  · rw [boundaryCov, boundaryTheta_of_not_posDef θ₀ hd]
    by_cases hd' : S'.PosDef
    · rw [boundaryTheta_of_posDef θ₀ hd', one_smul]
      have : S' - θ₀ • S = (S' - S) + (1 - θ₀) • S := by
        rw [sub_smul, one_smul]
        abel
      rw [this]
      exact PosSemidef.add hle (hS.smul (by linarith))
    · rw [boundaryTheta_of_not_posDef θ₀ hd', ← smul_sub]
      exact PosSemidef.smul hle hθ0

/-- The transform of the family on a Loewner pair. -/
theorem charFun_boundaryFamily {b θ₀ : ℝ} (hb : 0 < b) (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1) {S S' : Mat d}
    (hS : S.PosSemidef) (hle : loewnerLE S S') (ω : Rd d) :
    charFun (boundaryFamily b θ₀ S S') ω =
      ((Real.exp (-(b * quad (boundaryCov θ₀ S S') ω)) : ℝ) : ℂ) := by
  have hX : ((2 * b) • boundaryCov θ₀ S S').PosSemidef :=
    (boundaryCov_posSemidef hθ0 hθ1 hS hle).smul (by positivity)
  rw [boundaryFamily, charFun_multivariateGaussian_zero hX, quad_smul]
  congr 3
  ring

/-- `θ(0) 0 = 0`, whatever `θ(0)` is: the matrix of a pair from scale zero. -/
private theorem boundaryCov_zero (θ₀ : ℝ) (S : Mat d) :
    boundaryCov θ₀ 0 S = boundaryTheta θ₀ S • S := by
  rw [boundaryCov, smul_zero, sub_zero]

private theorem boundaryCov_zero_one (θ₀ : ℝ) : boundaryCov θ₀ 0 (1 : Mat d) = 1 := by
  rw [boundaryCov_zero, boundaryTheta_of_posDef θ₀ PosDef.one, one_smul]

private theorem exists_quad_one_pos (hd : 2 ≤ d) : ∃ ω : Rd d, 0 < quad 1 ω := by
  obtain ⟨P, -, -, ω, hω⟩ := exists_rank_one_step (d := d) hd
  refine ⟨ω, quad_pos PosDef.one fun h => ?_⟩
  rw [h, quad_eq_dotProduct] at hω
  simp at hω

/-- The family satisfies (K1), (K3) and (K4). -/
theorem boundaryFamily_isAffineCascadeFamilyNoK2 (hd : 2 ≤ d) {b θ₀ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1) : IsAffineCascadeFamilyNoK2 (boundaryFamily (d := d) b θ₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _
    unfold boundaryFamily
    infer_instance
  · intro S hS
    have hSS : loewnerLE S S := by
      rw [loewnerLE, sub_self]
      exact PosSemidef.zero
    haveI : IsProbabilityMeasure (boundaryFamily (d := d) b θ₀ S S) := by
      unfold boundaryFamily
      infer_instance
    apply Measure.ext_of_charFun
    funext ω
    rw [charFun_boundaryFamily hb hθ0 hθ1 hS hSS, charFun_dirac, boundaryCov, sub_self, quad_zero]
    simp
  · intro S S' S'' hS hS' _ h1 h2
    have h3 : loewnerLE S S'' := by
      have := PosSemidef.add h2 h1
      rwa [sub_add_sub_cancel] at this
    haveI : ∀ T T' : Mat d, IsProbabilityMeasure (boundaryFamily (d := d) b θ₀ T T') := by
      intro T T'
      unfold boundaryFamily
      infer_instance
    apply Measure.ext_of_charFun
    funext ω
    rw [charFun_conv, charFun_boundaryFamily hb hθ0 hθ1 hS h3,
      charFun_boundaryFamily hb hθ0 hθ1 hS' h2, charFun_boundaryFamily hb hθ0 hθ1 hS h1,
      ← Complex.ofReal_mul, ← Real.exp_add]
    have : boundaryCov θ₀ S S'' = boundaryCov θ₀ S' S'' + boundaryCov θ₀ S S' := by
      simp only [boundaryCov]
      abel
    rw [this, quad_add]
    congr 2
    ring
  · rintro A hA ⟨S, S'⟩ ⟨hS, hS', hle⟩
    simp only
    haveI : ∀ T T' : Mat d, IsProbabilityMeasure (boundaryFamily (d := d) b θ₀ T T') := by
      intro T T'
      unfold boundaryFamily
      infer_instance
    haveI : IsProbabilityMeasure (push A (boundaryFamily (d := d) b θ₀ S S')) := by
      unfold push
      exact Measure.isProbabilityMeasure_map (lin A).continuous.aemeasurable
    apply Measure.ext_of_charFun
    funext ω
    rw [charFun_push A hA, charFun_boundaryFamily hb hθ0 hθ1 hS hle,
      charFun_boundaryFamily hb hθ0 hθ1 (posSemidef_act A hS) (loewnerLE_act A hle),
      boundaryCov_act θ₀ hA hS hS', quad_act]
  · intro h
    obtain ⟨ω, hω⟩ := exists_quad_one_pos (d := d) hd
    have h1 := charFun_boundaryFamily hb hθ0 hθ1 PosSemidef.zero
      (loewnerLE_zero_of_posSemidef PosSemidef.one) ω
    rw [h, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      boundaryCov_zero_one] at h1
    have h2 : Real.exp (-(b * quad 1 ω)) = 1 := by exact_mod_cast h1.symm
    rw [Real.exp_eq_one_iff] at h2
    nlinarith [mul_pos hb hω]

/-- The transform of `affineGaussian` at a nonnegative constant, `charFun_affineGaussian` asking a
positive one. -/
private theorem charFun_affineGaussian_of_nonneg {b : ℝ} (hb : 0 ≤ b) {S S' : Mat d}
    (hle : loewnerLE S S') (ω : Rd d) :
    charFun (affineGaussian b S S') ω = ((Real.exp (-(b * quad (S' - S) ω)) : ℝ) : ℂ) := by
  have hX : ((2 * b) • (S' - S)).PosSemidef := PosSemidef.smul hle (by positivity)
  rw [affineGaussian, charFun_multivariateGaussian_zero hX, quad_smul]
  congr 3
  ring

/-- The exponents at `(0, P)` that `θ₀ < 1` separates. -/
private theorem exponent_ne {b θ₀ q : ℝ} (hb : 0 < b) (hθ1 : θ₀ < 1) (hq : 0 < q) :
    -(b * (θ₀ * q)) ≠ -(b * q) := fun h => by
  nlinarith [mul_pos (mul_pos hb hq) (sub_pos.2 hθ1)]

/-- **The family is not an affine Gaussian scale space**, with any constant: on the pair `(0, I)` a
negative constant gives a Dirac mass, against (K4), and a nonnegative one is `b`; and then the pair
`(0, P)` for the rank-one step `P` separates `2bθ₀P` from `2bP`. -/
theorem boundaryFamily_not_affineGaussian (hd : 2 ≤ d) {b θ₀ : ℝ} (hb : 0 < b) (hθ0 : 0 ≤ θ₀)
    (hθ1 : θ₀ < 1) (b' : ℝ) :
    ¬ EqOnPairs loewnerLE (boundaryFamily (d := d) b θ₀) (affineGaussian b') := by
  intro hEq
  obtain ⟨ω₁, hω₁⟩ := exists_quad_one_pos (d := d) hd
  have hle1 := loewnerLE_zero_of_posSemidef (PosSemidef.one (n := Fin d) (R := ℝ))
  have h01 : boundaryFamily b θ₀ 0 (1 : Mat d) = affineGaussian b' 0 1 :=
    hEq ((0 : Mat d), (1 : Mat d)) (mem_pairs_zero PosSemidef.one)
  /- A negative constant: `affineGaussian b' 0 1` is a Dirac mass. -/
  have hb'0 : 0 ≤ b' := by
    by_contra hneg
    push Not at hneg
    have hnot : ¬ ((2 * b') • ((1 : Mat d) - 0)).PosSemidef := fun hpsd => by
      have h := quad_nonneg hpsd ω₁
      rw [quad_smul, sub_zero] at h
      nlinarith
    apply (boundaryFamily_isAffineCascadeFamilyNoK2 (d := d) hd hb hθ0 hθ1).nondegenerate
    rw [h01, affineGaussian, multivariateGaussian_of_not_posSemidef _ hnot]
  /- The constant is `b`, by the pair `(0, I)`. -/
  have hbb' : b = b' := by
    have h := congrArg (fun m => charFun m ω₁) h01
    rw [charFun_boundaryFamily hb hθ0 hθ1 PosSemidef.zero hle1, boundaryCov_zero_one,
      charFun_affineGaussian_of_nonneg hb'0 hle1, sub_zero] at h
    have h' := Real.exp_injective (Complex.ofReal_injective h)
    have h'' : (b - b') * quad 1 ω₁ = 0 := by linarith
    rcases mul_eq_zero.1 h'' with h3 | h3
    · linarith
    · exact absurd h3 hω₁.ne'
  subst hbb'
  /- The pair `(0, P)`. -/
  obtain ⟨P, hP, hrank, ω, hω⟩ := exists_rank_one_step (d := d) hd
  have hPnd : ¬ P.PosDef := not_posDef_of_rank_lt (by rw [hrank]; omega)
  have hleP := loewnerLE_zero_of_posSemidef hP
  have h0P : boundaryFamily b θ₀ 0 P = affineGaussian b 0 P :=
    hEq ((0 : Mat d), P) (mem_pairs_zero hP)
  have h := congrArg (fun m => charFun m ω) h0P
  rw [charFun_boundaryFamily hb hθ0 hθ1 PosSemidef.zero hleP, boundaryCov_zero,
    boundaryTheta_of_not_posDef θ₀ hPnd, charFun_affineGaussian_of_nonneg hb.le hleP, sub_zero,
    quad_smul] at h
  exact exponent_ne hb hθ1 hω (Real.exp_injective (Complex.ofReal_injective h))

/-- **The family does not satisfy (K2)**: `μ̂_{0, P + εI}` tends, as `ε ↓ 0`, to the transform of
the Gaussian of covariance `2bP`, not to that of `μ_{0,P}`. -/
theorem boundaryFamily_not_continuous (hd : 2 ≤ d) {b θ₀ : ℝ} (hb : 0 < b) (hθ0 : 0 ≤ θ₀)
    (hθ1 : θ₀ < 1) :
    ¬ ∀ ω : Rd d, ContinuousOn
      (fun p : Mat d × Mat d => charFun (boundaryFamily b θ₀ p.1 p.2) ω)
      (wedgePairs loewnerLE) := by
  intro hK2
  obtain ⟨P, hP, hrank, ω, hω⟩ := exists_rank_one_step (d := d) hd
  have hPnd : ¬ P.PosDef := not_posDef_of_rank_lt (by rw [hrank]; omega)
  have hmem : ∀ ε : ℝ, 0 ≤ ε → ((0 : Mat d), P + ε • (1 : Mat d)) ∈ wedgePairs loewnerLE :=
    fun ε hε => mem_pairs_zero (hP.add (PosSemidef.one.smul hε))
  have hcurve : Continuous fun ε : ℝ => ((0 : Mat d), P + ε • (1 : Mat d)) := by fun_prop
  have hc : ContinuousOn ((fun p : Mat d × Mat d => charFun (boundaryFamily b θ₀ p.1 p.2) ω) ∘
      fun ε : ℝ => ((0 : Mat d), P + ε • (1 : Mat d))) (Ici 0) :=
    (hK2 ω).comp hcurve.continuousOn (fun ε hε => hmem ε hε)
  have h1 : Tendsto (fun ε : ℝ => charFun (boundaryFamily b θ₀ 0 (P + ε • (1 : Mat d))) ω) (𝓝[>] 0)
      (𝓝 (charFun (boundaryFamily b θ₀ 0 P) ω)) := by
    have := (hc 0 self_mem_Ici).tendsto
    simp only [Function.comp_def, zero_smul, add_zero] at this
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : Tendsto (fun ε : ℝ => ((Real.exp (-(b * quad (P + ε • (1 : Mat d)) ω)) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.exp (-(b * quad P ω)) : ℝ) : ℂ)) := by
    have hc2 : Continuous fun ε : ℝ => ((Real.exp (-(b * quad (P + ε • (1 : Mat d)) ω)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul ((continuous_quad ω).comp (by fun_prop))).neg))
    have := hc2.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have heq : (fun ε : ℝ => charFun (boundaryFamily b θ₀ 0 (P + ε • (1 : Mat d))) ω) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ((Real.exp (-(b * quad (P + ε • (1 : Mat d)) ω)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hd' : (P + ε • (1 : Mat d)).PosDef := PosDef.posSemidef_add hP (PosDef.one.smul hε)
    rw [charFun_boundaryFamily hb hθ0 hθ1 PosSemidef.zero
      (loewnerLE_zero_of_posSemidef hd'.posSemidef), boundaryCov_zero,
      boundaryTheta_of_posDef θ₀ hd', one_smul]
  have h3 := tendsto_nhds_unique (h1.congr' heq) h2
  rw [charFun_boundaryFamily hb hθ0 hθ1 PosSemidef.zero (loewnerLE_zero_of_posSemidef hP),
    boundaryCov_zero, boundaryTheta_of_not_posDef θ₀ hPnd, quad_smul] at h3
  exact exponent_ne hb hθ1 hω (Real.exp_injective (Complex.ofReal_injective h3))

/-- **`prop:affine-rigidity-boundary`(2)**: for `d ≥ 2`, `b > 0` and `0 ≤ θ₀ < 1`, the covariance
`2b(θ(Σ')Σ' - θ(Σ)Σ)` is positive semidefinite on every Loewner pair of `PSD(d)`; the family
`boundaryFamily b θ₀` of the centred Gaussian laws with these covariances satisfies (K1), (K3) and
(K4); it agrees with the affine Gaussian scale space with constant `b` on the pairs in `PD(d)`; its
kernel from scale zero at a nonzero singular `P` has covariance `2bθ₀P`; it is not an affine
Gaussian scale space with any constant; and it does not satisfy (K2), so it is not an affine
cascade family. -/
theorem affine_rigidity_boundary_family (hd : 2 ≤ d) {b θ₀ : ℝ} (hb : 0 < b) (hθ0 : 0 ≤ θ₀)
    (hθ1 : θ₀ < 1) :
    (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      ((2 * b) • boundaryCov θ₀ S S').PosSemidef) ∧
    IsAffineCascadeFamilyNoK2 (boundaryFamily (d := d) b θ₀) ∧
    (∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
      boundaryFamily b θ₀ S S' = affineGaussian b S S') ∧
    (∀ P : Mat d, P.PosSemidef → P ≠ 0 → P.det = 0 →
      boundaryFamily b θ₀ 0 P = multivariateGaussian 0 ((2 * b * θ₀) • P)) ∧
    (∀ b' : ℝ, ¬ EqOnPairs loewnerLE (boundaryFamily (d := d) b θ₀) (affineGaussian b')) ∧
    (¬ ∀ ω : Rd d, ContinuousOn
      (fun p : Mat d × Mat d => charFun (boundaryFamily b θ₀ p.1 p.2) ω)
      (wedgePairs loewnerLE)) ∧
    ¬ IsAffineCascadeFamily (boundaryFamily (d := d) b θ₀) := by
  have hK2 := boundaryFamily_not_continuous (d := d) hd hb hθ0 hθ1
  refine ⟨fun S S' hS _ hle => (boundaryCov_posSemidef hθ0 hθ1 hS hle).smul (by positivity),
    boundaryFamily_isAffineCascadeFamilyNoK2 hd hb hθ0 hθ1, ?_, ?_,
    boundaryFamily_not_affineGaussian hd hb hθ0 hθ1, hK2, fun h => hK2 h.continuous⟩
  · intro S S' hS hS' _
    rw [boundaryFamily, boundaryCov, boundaryTheta_of_posDef θ₀ hS, boundaryTheta_of_posDef θ₀ hS',
      one_smul, one_smul, affineGaussian]
  · intro P hP _ hdet
    have hPnd : ¬ P.PosDef := fun h => (hP.posDef_iff_det_ne_zero.1 h) hdet
    rw [boundaryFamily, boundaryCov_zero, boundaryTheta_of_not_posDef θ₀ hPnd, smul_smul]

end AffineHemigroup
