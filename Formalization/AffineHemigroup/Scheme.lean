/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Scheme
import AffineHemigroup.LoewnerWedge

/-!
# `lem:gw-scheme-claims` and `lem:affine-gaussian-transform`

Blueprint: `blueprint/src/parts/04-classical.tex`. The claims that `def:gw-cascade-family` and
`def:affine-cascade-family` display, proved: `(0, I) ∈ P_W` for every wedge datum, the Loewner and
ray orders as wedge data, `GL(d)` as a closed subgroup containing the dilations, the transform of
an image measure (`lem:gw-scheme-claims`), and the transform and support of the affine Gaussian
law (`lem:affine-gaussian-transform`). Lean core only.

Since Q-0452 this file holds the ray order and the affine Gaussian law. The matrix calculus every
later proof of chapter 4 reads (`lin` is a star algebra map, so `lin Aᵀ` is the adjoint of
`lin A`; the quadratic form `quad` is additive and homogeneous in the matrix, quadratic in the
vector, and transported by `act`) and the transform of an image measure, claim (3), are in
`AffineHemigroup.MatrixCalculus`; claim (1) and claim (2) for the Loewner order and the group are in
`AffineHemigroup.LoewnerWedge`, which this file imports.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## `lem:gw-scheme-claims`(2) -/

/-- **`lem:gw-scheme-claims`(2)**, the ray order: for every closed subgroup `G` of `GL(d)`
containing the dilations, `(G, rays)` is a wedge datum. -/
theorem isWedgeDatum_ray {G : Set (Mat d)} (hG : IsClosedSubgroupGL G)
    (hdil : ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G) : IsWedgeDatum G rayLE where
  closedSubgroup := hG
  dilations := hdil
  refl S _ := Or.inr ⟨1, le_rfl, (one_smul _ _).symm⟩
  antisymm S S' _ _ h1 h2 := by
    rcases h1 with rfl | ⟨c, hc, rfl⟩
    · rcases h2 with h2 | ⟨c', hc', h2⟩
      · exact h2.symm
      · rcases smul_eq_zero.1 h2.symm with h | h
        · linarith
        · exact h.symm
    · rcases h2 with h2 | ⟨c', hc', h2⟩
      · rcases smul_eq_zero.1 h2 with h | h
        · linarith
        · simp [h]
      · by_cases hS0 : S = 0
        · simp [hS0]
        have h3 : (c' * c - 1) • S = 0 := by
          rw [sub_smul, mul_smul, ← h2, one_smul, sub_self]
        rcases smul_eq_zero.1 h3 with h | h
        · have hc1 : c = 1 := by nlinarith
          simp [hc1]
        · exact absurd h hS0
  trans S S' S'' _ _ _ h1 h2 := by
    rcases h1 with rfl | ⟨c, hc, rfl⟩
    · exact Or.inl rfl
    · rcases h2 with h2 | ⟨c', hc', rfl⟩
      · rcases smul_eq_zero.1 h2 with h | h
        · linarith
        · exact Or.inl h
      · exact Or.inr ⟨c' * c, one_le_mul_of_one_le_of_one_le hc' hc, by rw [mul_smul]⟩
  invariant A _ S S' _ _ h := by
    rcases h with rfl | ⟨c, hc, rfl⟩
    · exact Or.inl (by simp [act])
    · exact Or.inr ⟨c, hc, by simp [act]⟩
  rays S _ c c' hc hcc' := by
    rcases eq_or_lt_of_le hc with rfl | hc0
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr ⟨c' / c, (one_le_div hc0).2 hcc', by rw [smul_smul, div_mul_cancel₀ _ hc0.ne']⟩

/-! ## `lem:affine-gaussian-transform` -/

/-- The transform of a centred Gaussian law in the form `quad` reads it. -/
theorem charFun_multivariateGaussian_zero {X : Mat d} (hX : X.PosSemidef) (ω : Rd d) :
    charFun (multivariateGaussian 0 X) ω = ((Real.exp (-(quad X ω / 2)) : ℝ) : ℂ) := by
  rw [charFun_multivariateGaussian hX, quad_eq_dotProduct]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The affine Gaussian laws are probability measures (for every `b`, `Σ`, `Σ'`). -/
instance isProbabilityMeasure_affineGaussian (b : ℝ) (S S' : Mat d) :
    IsProbabilityMeasure (affineGaussian b S S') := by
  unfold affineGaussian
  infer_instance

/-- **`lem:affine-gaussian-transform`**, `eq:affine-gaussian`: for `b > 0` and `Σ ≤ Σ'` in
`PSD(d)`, the centred Gaussian law with covariance `2b(Σ' - Σ)` has transform
`e^{-b⟨ω, (Σ' - Σ)ω⟩}`. -/
theorem charFun_affineGaussian {b : ℝ} (hb : 0 < b) {S S' : Mat d} (_hS : S.PosSemidef)
    (_hS' : S'.PosSemidef) (hle : loewnerLE S S') (ω : Rd d) :
    charFun (affineGaussian b S S') ω = ((Real.exp (-(b * quad (S' - S) ω)) : ℝ) : ℂ) := by
  have hX : ((2 * b) • (S' - S)).PosSemidef := PosSemidef.smul hle (by positivity)
  rw [affineGaussian, charFun_multivariateGaussian_zero hX, quad_smul]
  congr 3
  ring

/-- For a positive semidefinite `Y`, the range of `lin Y` is the orthogonal complement of its
kernel. -/
theorem mem_range_lin_of_orthogonal {Y : Mat d} (hY : Y.IsHermitian) {x : Rd d}
    (hx : ∀ v : Rd d, lin Y v = 0 → ⟪v, x⟫ = 0) :
    x ∈ LinearMap.range (lin Y : Rd d →ₗ[ℝ] Rd d) := by
  have hT : Yᵀ = Y := by
    have := hY.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hrange : (LinearMap.range (lin Y : Rd d →ₗ[ℝ] Rd d)) = (lin Y).range := rfl
  rw [hrange, ← Submodule.orthogonal_orthogonal (lin Y).range, ContinuousLinearMap.orthogonal_range,
    ← lin_transpose, hT]
  rw [Submodule.mem_orthogonal]
  intro v hv
  exact hx v hv

/-- **`lem:affine-gaussian-transform`**, the degenerate case: the law is carried by the range of
`Σ' - Σ`, which is a proper subspace exactly when that matrix is singular. -/
theorem affineGaussian_carried_by_range {b : ℝ} (hb : 0 < b) {S S' : Mat d}
    (_hS : S.PosSemidef) (_hS' : S'.PosSemidef) (hle : loewnerLE S S') :
    affineGaussian b S S'
      ((LinearMap.range (lin (S' - S) : Rd d →ₗ[ℝ] Rd d) : Set (Rd d))ᶜ) = 0 ∧
      (LinearMap.range (lin (S' - S) : Rd d →ₗ[ℝ] Rd d) ≠ ⊤ ↔ ¬ IsUnit (S' - S).det) := by
  set Y := S' - S with hYdef
  have hY : Y.PosSemidef := hle
  set X : Mat d := (2 * b) • Y with hXdef
  have hX : X.PosSemidef := PosSemidef.smul hY (by positivity)
  set R : Mat d := CFC.sqrt X with hRdef
  have hRR : R * R = X := CFC.sqrt_mul_sqrt_self X (nonneg_of_posSemidef hX)
  have hRsa : Rᵀ = R := by
    have h := (CFC.sqrt_nonneg X).isSelfAdjoint
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  -- the kernel of `Y` lies in the kernel of `R`
  have hker : ∀ v : Rd d, lin Y v = 0 → lin R v = 0 := by
    intro v hv
    have hXv : lin X v = 0 := by
      rw [hXdef, lin_smul, _root_.smul_apply, hv, smul_zero]
    have h0 : ⟪lin R v, lin R v⟫ = 0 := by
      rw [inner_lin_left, hRsa, ← mul_apply_eq_comp, ← lin_mul, hRR, hXv,
        inner_zero_right]
    exact inner_self_eq_zero.1 h0
  -- so the range of `R` lies in the range of `Y`
  have hrange : ∀ x : Rd d, lin R x ∈ LinearMap.range (lin Y : Rd d →ₗ[ℝ] Rd d) := by
    intro x
    refine mem_range_lin_of_orthogonal hY.isHermitian ?_
    intro v hv
    rw [real_inner_comm, inner_lin_left, hRsa, hker v hv, inner_zero_right]
  refine ⟨?_, ?_⟩
  · have hV : IsClosed ((LinearMap.range (lin Y : Rd d →ₗ[ℝ] Rd d) : Set (Rd d))) :=
      Submodule.closed_of_finiteDimensional _
    rw [affineGaussian, multivariateGaussian,
      Measure.map_apply (by fun_prop) hV.measurableSet.compl]
    have hempty : ((fun x : Rd d => (0 : Rd d) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt X) x) ⁻¹'
        ((LinearMap.range (lin Y : Rd d →ₗ[ℝ] Rd d) : Set (Rd d))ᶜ)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, zero_add,
        Set.mem_empty_iff_false, iff_false, not_not]
      exact hrange x
    rw [hempty, measure_empty]
  · rw [ne_eq, LinearMap.range_eq_top, ← Matrix.isUnit_iff_isUnit_det,
      ← Matrix.mulVec_surjective_iff_isUnit]
    apply not_congr
    constructor
    · intro h y
      obtain ⟨x, hx⟩ := h (WithLp.toLp 2 y)
      refine ⟨x.ofLp, ?_⟩
      have := congrArg WithLp.ofLp hx
      simpa [ContinuousLinearMap.coe_coe, ofLp_lin] using this
    · intro h y
      obtain ⟨x, hx⟩ := h y.ofLp
      refine ⟨WithLp.toLp 2 x, ?_⟩
      change lin Y (WithLp.toLp 2 x) = y
      apply (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).injective
      simp [ofLp_lin, hx]

end AffineHemigroup
