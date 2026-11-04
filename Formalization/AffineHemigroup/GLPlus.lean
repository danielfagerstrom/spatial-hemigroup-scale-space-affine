/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Rigidity
import AffineHemigroup.Defs.Spectral
import AffineHemigroup.KernelsFromOrigin
import AffineHemigroup.StableExponent
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# `prop:glplus-families`: covariance under `GL⁺(d)` is covariance under `GL(d)`

Blueprint: `blueprint/src/parts/05-landscape.tex`, `prop:glplus-families` (clauses (1), (2) for
kernels, (3)). Q-0281, wave M, phase 2. The operator half of (2), `lem:glplus-operator-families`,
is `AffineHemigroup.GLPlusOperators`.

## The route

* **(1), the joint reflection** (the proof of record was rewritten to this route; it
  diagonalized `Σ` and `Σ'` simultaneously by congruence). When `T = Σ + Σ'` is positive
  definite, an eigenvector `u` of `M = T^{-1/2} Σ T^{-1/2}` gives the Householder reflection
  `H_u`, which commutes with `M` and with `I - M = T^{-1/2} Σ' T^{-1/2}`, and
  `B = T^{1/2} H_u T^{-1/2}`; when `T` is singular, a `u` with `Tu = 0` has `Σu = Σ'u = 0`, and
  `B = H_u`. In both cases `det B = det H_u = -1` (`householder_det`, the matrix determinant
  lemma).
* **(2), kernels.** The blueprint's, as in `lem:affine-reduction`'s proof
  (`AffineHemigroup.Reduction`), with a general order `W` and the group `GL⁺(d)`: `μ̂_I` is
  radial because two reflections with the right determinant carry any vector to any other of the
  same length (`exists_isometry_det_pos`, `d ≥ 2`); the kernels from the origin follow through
  `Σ^{1/2} ∈ GL⁺(d)` and (K2); the transform has no zero (`ne_zero_of_cascade`); and the
  transforms of `A_* μ_{Σ,Σ'}` and `μ_{A·Σ, A·Σ'}` are the same quotient.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## (1): the group -/

/-- **`prop:glplus-families`(1)**, the group: `GL⁺(d)` is a closed subgroup of `GL(d)` containing
the dilations. -/
theorem glPlusSet_isClosedSubgroupGL (_hd : 1 ≤ d) :
    IsClosedSubgroupGL (glPlusSet d) ∧ ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ glPlusSet d := by
  refine ⟨⟨fun A hA => ?_, ?_, fun A hA B hB => ?_, fun A hA => ?_, fun A hA hu => ?_⟩,
    fun c hc => ?_⟩
  · exact isUnit_iff_ne_zero.mpr (ne_of_gt (show 0 < A.det from hA))
  · change 0 < (1 : Mat d).det
    simp
  · change 0 < (A * B).det
    rw [det_mul]
    exact mul_pos hA hB
  · change 0 < A⁻¹.det
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_pos.mpr hA
  · have hcl : closure (glPlusSet d) ⊆ {A : Mat d | 0 ≤ A.det} :=
      closure_minimal (fun A hA => le_of_lt (show 0 < A.det from hA))
        (isClosed_le continuous_const (continuous_id.matrix_det))
    exact lt_of_le_of_ne (hcl hA) (Ne.symm hu.ne_zero)
  · change 0 < (c • (1 : Mat d)).det
    rw [det_smul, det_one, mul_one]
    positivity

/-- `GL⁺(d) ⊆ GL(d)`. -/
theorem glPlusSet_subset_glSet : glPlusSet d ⊆ glSet d := fun A hA =>
  isUnit_iff_ne_zero.mpr (ne_of_gt (show 0 < A.det from hA))

/-! ## (1): the Householder reflection -/

/-- `⟨u, u⟩ > 0` for `u ≠ 0`. -/
theorem dotProduct_self_pos' {u : Fin d → ℝ} (hu : u ≠ 0) : 0 < u ⬝ᵥ u :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (u i))
    (Ne.symm (fun h => hu (dotProduct_self_eq_zero.mp h)))

/-- **The Householder reflection** `H_u = I - (2/⟨u,u⟩) u uᵀ`. -/
noncomputable def householder (u : Fin d → ℝ) : Mat d := 1 - (2 / (u ⬝ᵥ u)) • vecMulVec u u

/-- `H_u` is symmetric. -/
theorem householder_transpose (u : Fin d → ℝ) : (householder u)ᵀ = householder u := by
  simp [householder, transpose_sub, transpose_smul, transpose_vecMulVec]

/-- `det H_u = -1`, by the matrix determinant lemma. -/
theorem householder_det {u : Fin d → ℝ} (hu : u ≠ 0) : (householder u).det = -1 := by
  have hpos := dotProduct_self_pos' hu
  have h : householder u =
      1 + replicateCol Unit (-(2 / (u ⬝ᵥ u)) • u) * replicateRow Unit u := by
    rw [← vecMulVec_eq, householder, smul_vecMulVec, neg_smul, sub_eq_add_neg]
  rw [h, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- `H_u` commutes with a symmetric matrix of which `u` is an eigenvector. -/
theorem householder_mul_comm {M : Mat d} (hM : Mᵀ = M) {u : Fin d → ℝ} {c : ℝ}
    (hMu : M *ᵥ u = c • u) : householder u * M = M * householder u := by
  have h1 : u ᵥ* M = M *ᵥ u := by
    conv_lhs => rw [← hM]
    exact vecMul_transpose M u
  simp only [householder, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul, mul_vecMulVec, h1, hMu, vecMulVec_smul, smul_vecMulVec]

/-- `H_u² = I`. -/
theorem householder_mul_self {u : Fin d → ℝ} (hu : u ≠ 0) :
    householder u * householder u = 1 := by
  have hpos := dotProduct_self_pos' hu
  set c : ℝ := 2 / (u ⬝ᵥ u) with hc
  set P : Mat d := vecMulVec u u with hP
  have hPP : P * P = (u ⬝ᵥ u) • P := by
    rw [hP, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hcc : c * c * (u ⬝ᵥ u) = c + c := by rw [hc]; field_simp; ring
  calc householder u * householder u = (1 - c • P) * (1 - c • P) := rfl
    _ = 1 - (c + c) • P + (c * c * (u ⬝ᵥ u)) • P := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, Matrix.smul_mul,
          Matrix.mul_smul, hPP, smul_smul, smul_smul, add_smul]
        abel
    _ = 1 := by rw [hcc]; abel

/-- `H_u M H_uᵀ = M` for a symmetric `M` of which `u ≠ 0` is an eigenvector. -/
theorem householder_conj {M : Mat d} (hM : Mᵀ = M) {u : Fin d → ℝ} (hu : u ≠ 0) {c : ℝ}
    (hMu : M *ᵥ u = c • u) : householder u * M * (householder u)ᵀ = M := by
  rw [householder_transpose, householder_mul_comm hM hMu, Matrix.mul_assoc,
    householder_mul_self hu, Matrix.mul_one]

/-- A real positive semidefinite matrix is symmetric. -/
theorem transpose_eq_of_posSemidef {S : Mat d} (hS : S.PosSemidef) : Sᵀ = S := by
  have h := hS.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

/-- **`prop:glplus-families`(1)**, the joint reflection: for `Σ, Σ' ∈ PSD(d)` there is
`B ∈ GL(d)` with `det B = -1`, `BΣBᵀ = Σ` and `BΣ'Bᵀ = Σ'`. -/
theorem exists_joint_reflection (hd : 1 ≤ d) {S S' : Mat d} (hS : S.PosSemidef)
    (hS' : S'.PosSemidef) :
    ∃ B ∈ glSet d, B.det = -1 ∧ act B S = S ∧ act B S' = S' := by
  have hST := transpose_eq_of_posSemidef hS
  have hS'T := transpose_eq_of_posSemidef hS'
  have hdet : ∀ B : Mat d, B.det = -1 → B ∈ glSet d := fun B hB => by
    change IsUnit B.det
    rw [hB]
    exact isUnit_one.neg
  by_cases hT : (S + S').PosDef
  · set T : Mat d := S + S' with hTdef
    set R : Mat d := CFC.sqrt T with hRdef
    have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T (nonneg_of_posSemidef hT.posSemidef)
    have hRT : Rᵀ = R := by
      have h := (CFC.sqrt_nonneg T).isSelfAdjoint
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact h
    have hRu : IsUnit R.det := by
      have h1 : R.det * R.det = T.det := by rw [← det_mul, hRR]
      have h2 : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT.isUnit
      rw [← h1] at h2
      exact isUnit_of_mul_isUnit_left h2
    set Ri : Mat d := R⁻¹ with hRidef
    have hRiR : Ri * R = 1 := nonsing_inv_mul R hRu
    have hRRi : R * Ri = 1 := mul_nonsing_inv R hRu
    have hRiT : Riᵀ = Ri := by rw [hRidef, transpose_nonsing_inv, hRT]
    set M : Mat d := Ri * S * Ri with hMdef
    have hMT : Mᵀ = M := by
      rw [hMdef, transpose_mul, transpose_mul, hRiT, hST, Matrix.mul_assoc]
    have hMh : M.IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      exact hMT
    have hM' : Ri * S' * Ri = 1 - M := by
      have hS'eq : S' = R * R - S := by rw [hRR, hTdef]; abel
      rw [hS'eq, hMdef, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hRiR,
        Matrix.one_mul, Matrix.mul_assoc, hRRi]
    set i : Fin d := ⟨0, hd⟩
    set u : Fin d → ℝ := ⇑(hMh.eigenvectorBasis i) with hudef
    have hu : u ≠ 0 := by
      intro h0
      have hne := (hMh.eigenvectorBasis.orthonormal).ne_zero i
      apply hne
      ext j
      exact congrFun h0 j
    have hMu : M *ᵥ u = hMh.eigenvalues i • u := hMh.mulVec_eigenvectorBasis i
    have h1Mu : (1 - M) *ᵥ u = (1 - hMh.eigenvalues i) • u := by
      rw [sub_mulVec, one_mulVec, hMu, sub_smul, one_smul]
    have h1MT : (1 - M)ᵀ = 1 - M := by rw [transpose_sub, transpose_one, hMT]
    set H := householder u with hH
    have hconj : ∀ N : Mat d, (R * H * Ri) * N * (R * H * Ri)ᵀ
        = R * (H * (Ri * N * Ri) * Hᵀ) * R := by
      intro N
      rw [transpose_mul, transpose_mul, hRiT, hRT]
      simp only [Matrix.mul_assoc]
    refine ⟨R * H * Ri, hdet _ ?_, ?_, ?_, ?_⟩
    · rw [det_mul, det_mul, householder_det hu, mul_comm (R.det), mul_assoc, ← det_mul, hRRi,
        det_one, mul_one]
    · rw [det_mul, det_mul, householder_det hu, mul_comm (R.det), mul_assoc, ← det_mul, hRRi,
        det_one, mul_one]
    · rw [act, hconj S, householder_conj hMT hu hMu, hMdef]
      simp only [← Matrix.mul_assoc, hRRi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRiR, Matrix.mul_one]
    · rw [act, hconj S', hM', householder_conj h1MT hu h1Mu, ← hM']
      simp only [← Matrix.mul_assoc, hRRi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRiR, Matrix.mul_one]
  · have hTh : (S + S').IsHermitian := (hS.add hS').isHermitian
    rw [posDef_iff_dotProduct_mulVec] at hT
    push Not at hT
    obtain ⟨x, hx0, hx⟩ := hT hTh
    simp only [star_trivial] at hx
    have hxS := hS.dotProduct_mulVec_nonneg x
    have hxS' := hS'.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hxS hxS'
    rw [add_mulVec, dotProduct_add] at hx
    have h0 : x ⬝ᵥ (S *ᵥ x) = 0 := by linarith
    have h0' : x ⬝ᵥ (S' *ᵥ x) = 0 := by linarith
    have hSx : S *ᵥ x = (0 : ℝ) • x := by
      rw [zero_smul]
      exact (hS.dotProduct_mulVec_zero_iff x).mp (by simpa using h0)
    have hS'x : S' *ᵥ x = (0 : ℝ) • x := by
      rw [zero_smul]
      exact (hS'.dotProduct_mulVec_zero_iff x).mp (by simpa using h0')
    exact ⟨householder x, hdet _ (householder_det hx0), householder_det hx0,
      householder_conj hST hx0 hSx, householder_conj hS'T hx0 hS'x⟩

/-- `act` composes: `(AB) · Σ = A · (B · Σ)`. -/
theorem act_mul (A B S : Mat d) : act (A * B) S = act A (act B S) := by
  simp only [act, transpose_mul, Matrix.mul_assoc]

/-- **`prop:glplus-families`(1)**, consequently: a relation on `PSD(d)` invariant under
`Σ ↦ AΣAᵀ` for every `A ∈ GL⁺(d)` is invariant under it for every `A ∈ GL(d)`. -/
theorem invariant_gl_of_invariant_glPlus (hd : 1 ≤ d) (R : Mat d → Mat d → Prop)
    (hR : ∀ A ∈ glPlusSet d, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef →
      R S S' → R (act A S) (act A S')) :
    ∀ A ∈ glSet d, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef →
      R S S' → R (act A S) (act A S') := by
  intro A hA S S' hS hS' hRS
  rcases lt_or_gt_of_ne (show A.det ≠ 0 from hA.ne_zero) with hneg | hpos
  · obtain ⟨B, -, hBdet, hBS, hBS'⟩ := exists_joint_reflection hd hS hS'
    have hAB : A * B ∈ glPlusSet d := by
      change 0 < (A * B).det
      rw [det_mul, hBdet]
      linarith
    have := hR (A * B) hAB S S' hS hS' hRS
    rwa [act_mul, act_mul, hBS, hBS'] at this
  · exact hR A hpos S S' hS hS' hRS

/-- **`prop:glplus-families`(1)**: `(GL⁺(d), W)` is a wedge datum if and only if `(GL(d), W)` is
one. -/
theorem isWedgeDatum_glPlus_iff (hd : 1 ≤ d) (le : Mat d → Mat d → Prop) :
    IsWedgeDatum (glPlusSet d) le ↔ IsWedgeDatum (glSet d) le := by
  constructor
  · intro h
    exact ⟨glSet_isClosedSubgroupGL.1, glSet_isClosedSubgroupGL.2, h.refl, h.antisymm, h.trans,
      invariant_gl_of_invariant_glPlus hd le h.invariant, h.rays⟩
  · intro h
    exact ⟨(glPlusSet_isClosedSubgroupGL hd).1, (glPlusSet_isClosedSubgroupGL hd).2, h.refl,
      h.antisymm, h.trans, fun A hA => h.invariant A (glPlusSet_subset_glSet hA), h.rays⟩

/-! ## (2): kernels -/

/-- A reflection in a hyperplane has determinant `-1`. -/
theorem det_reflection_line {w : Rd d} (hw : w ≠ 0) :
    LinearMap.det (ℝ ∙ w)ᗮ.reflection.toLinearMap = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hw,
    pow_one]

/-- For `d ≥ 2` every vector has a nonzero orthogonal vector. -/
theorem exists_ne_zero_orthogonal (hd : 2 ≤ d) (ω : Rd d) : ∃ w : Rd d, w ≠ 0 ∧ ⟪ω, w⟫ = 0 := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ω)
  rw [finrank_euclideanSpace_fin] at h
  have h1 : Module.finrank ℝ (ℝ ∙ ω) ≤ 1 := by
    by_cases hω : ω = 0
    · rw [hω, Submodule.span_zero_singleton, finrank_bot]; omega
    · rw [finrank_span_singleton hω]
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ (ℝ ∙ ω)ᗮ by omega)
  refine ⟨x, fun h0 => hx (Subtype.ext h0), ?_⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.2

/-- **`SO(d)` is transitive on spheres**, `d ≥ 2`: for `|ω| = |ω'|` there is a linear isometry
of positive determinant mapping `ω'` to `ω`, a reflection or a product of two. -/
theorem exists_isometry_det_pos (hd : 2 ≤ d) {ω ω' : Rd d} (h : ‖ω‖ = ‖ω'‖) :
    ∃ e : Rd d ≃ₗᵢ[ℝ] Rd d, e ω' = ω ∧ 0 < LinearMap.det e.toLinearMap := by
  set r₁ := (ℝ ∙ (ω' - ω))ᗮ.reflection with hr₁
  have hr₁ω : r₁ ω' = ω := Submodule.reflection_sub h.symm
  have hdet₁ : LinearMap.det r₁.toLinearMap = 1 ∨
      LinearMap.det r₁.toLinearMap = -1 := by
    rw [hr₁, Submodule.det_reflection]
    exact neg_one_pow_eq_or ℝ _
  obtain ⟨w, hw, hωw⟩ := exists_ne_zero_orthogonal hd ω
  set r₂ := (ℝ ∙ w)ᗮ.reflection with hr₂
  have hr₂ω : r₂ ω = ω := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by rw [real_inner_comm]; exact hωw))
  rcases hdet₁ with h1 | h1
  · exact ⟨r₁, hr₁ω, by rw [h1]; norm_num⟩
  · refine ⟨r₁.trans r₂, by simp [hr₁ω, hr₂ω], ?_⟩
    have hcomp : (r₁.trans r₂).toLinearMap
        = r₂.toLinearMap ∘ₗ r₁.toLinearMap := rfl
    rw [hcomp, LinearMap.det_comp, h1, hr₂, det_reflection_line hw]
    norm_num

/-- **`prop:glplus-families`(2)**, the kernels: for `d ≥ 2` and a wedge datum `(GL⁺(d), W)`, a
family indexed by `P_W` is a `(GL⁺(d), W)`-cascade family of kernels if and only if it is a
`(GL(d), W)`-cascade family of kernels. -/
theorem gw_family_glPlus_iff (hd : 2 ≤ d) {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum (glPlusSet d) le) (μ : Mat d → Mat d → Measure (Rd d)) :
    IsGWCascadeFamily (glPlusSet d) le μ ↔ IsGWCascadeFamily (glSet d) le μ := by
  have hd1 : 1 ≤ d := by omega
  have hWgl : IsWedgeDatum (glSet d) le := (isWedgeDatum_glPlus_iff hd1 le).mp hW
  refine ⟨fun hμ => ?_, fun hμ => ⟨hμ.isProbability, hμ.diag, hμ.cascade, hμ.continuous,
    fun A hA => hμ.covariant A (glPlusSet_subset_glSet hA), hμ.nondegenerate⟩⟩
  refine ⟨hμ.isProbability, hμ.diag, hμ.cascade, hμ.continuous, ?_, hμ.nondegenerate⟩
  have hmem0 : ∀ S : Mat d, S.PosSemidef → ((0 : Mat d), S) ∈ wedgePairs le := fun S hS =>
    ⟨PosSemidef.zero, hS, wedge_zero_le hW hS⟩
  have hp01 := hmem0 1 PosSemidef.one
  haveI : IsProbabilityMeasure (μ 0 1) := hμ.isProbability _ hp01
  /- (K3) at the kernels from the origin, for `A ∈ GL⁺(d)`. -/
  have hcov : ∀ A ∈ glPlusSet d, ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      charFun (μ 0 (act A S)) ω = charFun (μ 0 S) (lin Aᵀ ω) := by
    intro A hA S hS ω
    have h := hμ.covariant A hA (0, S) (hmem0 S hS)
    have h0 : act A (0 : Mat d) = 0 := by simp [act]
    simp only [h0] at h
    rw [← h]
    exact charFun_map_lin A (μ 0 S) ω
  /- `μ̂_I` is radial: `SO(d)` is transitive on spheres. -/
  have hrad : ∀ ω ω' : Rd d, ‖ω‖ = ‖ω'‖ → charFun (μ 0 1) ω = charFun (μ 0 1) ω' := by
    intro ω ω' h
    obtain ⟨e, he, hdet⟩ := exists_isometry_det_pos hd h
    set A : Mat d :=
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (e : Rd d →L[ℝ] Rd d) with hAdef
    have hlinA : lin A = (e : Rd d →L[ℝ] Rd d) := by
      simp only [lin, hAdef, StarAlgEquiv.apply_symm_apply]
    have hlinAT : lin Aᵀ = (e.symm : Rd d →L[ℝ] Rd d) := by
      rw [lin_transpose, hlinA, LinearIsometryEquiv.adjoint_eq_symm]
    have hAAT : A * Aᵀ = 1 := by
      apply lin_injective
      rw [lin_mul, hlinA, hlinAT, lin_one]
      ext x
      simp
    have hA : A ∈ glPlusSet d := by
      change 0 < A.det
      rw [← det_lin, hlinA]
      exact hdet
    have h1 : act A (1 : Mat d) = 1 := by rw [act, mul_one, hAAT]
    have hc := hcov A hA 1 PosSemidef.one ω
    rw [h1, hlinAT] at hc
    rw [hc]
    congr 1
    rw [← he]
    simp
  set e₀ : Rd d := EuclideanSpace.single (⟨0, hd1⟩ : Fin d) (1 : ℝ) with he₀def
  have he₀ : ‖e₀‖ = 1 := by simp [he₀def]
  set φ : ℝ → ℂ := fun u => charFun (μ 0 1) (Real.sqrt u • e₀) with hφdef
  have hφ : ∀ ω : Rd d, charFun (μ 0 1) ω = φ (‖ω‖ ^ 2) := by
    intro ω
    apply hrad
    simp only [norm_smul, he₀, mul_one, Real.norm_eq_abs, Real.sqrt_sq (norm_nonneg ω),
      abs_norm]
  have hφcont : Continuous φ :=
    continuous_charFun.comp (Real.continuous_sqrt.smul continuous_const)
  /- The kernels from the origin, at `Σ ∈ PD(d)`: `Σ^{1/2} ∈ GL⁺(d)`. -/
  have hPD : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    set R : Mat d := CFC.sqrt S with hRdef
    have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S (nonneg_of_posSemidef hS.posSemidef)
    have hRT : Rᵀ = R := by
      have h := (CFC.sqrt_nonneg S).isSelfAdjoint
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact h
    have hR : R ∈ glPlusSet d := by
      change 0 < R.det
      have h1 : R.det * R.det = S.det := by rw [← det_mul, hRR]
      have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
      refine lt_of_le_of_ne hRpsd.det_nonneg fun h0 => ?_
      have := hS.det_pos
      rw [← h1, ← h0, zero_mul] at this
      exact lt_irrefl _ this
    have hact : act R 1 = S := by rw [act, mul_one, hRT, hRR]
    have h := hcov R hR 1 PosSemidef.one ω
    rw [hact] at h
    rw [h, hφ, hRT]
    congr 1
    rw [← real_inner_self_eq_norm_sq, inner_lin_left, hRT, ← hRR, quad, lin_mul]
    rfl
  /- At every `Σ ∈ PSD(d)`, by (K2) along `(0, Σ + εI) → (0, Σ)`. -/
  have hPSD : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    have hmem : ∀ ε : ℝ, 0 ≤ ε → ((0 : Mat d), S + ε • (1 : Mat d)) ∈ wedgePairs le :=
      fun ε hε => hmem0 _ (hS.add (PosSemidef.one.smul hε))
    have hcurve : Continuous fun ε : ℝ => ((0 : Mat d), S + ε • (1 : Mat d)) := by fun_prop
    have hc : ContinuousOn (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (Ici 0) :=
      (hμ.continuous ω).comp hcurve.continuousOn (fun ε hε => hmem ε hε)
    have h1 : Tendsto (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (𝓝[>] 0)
        (𝓝 (charFun (μ 0 S) ω)) := by
      have := (hc 0 self_mem_Ici).tendsto
      simp only [zero_smul, add_zero] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 : Tendsto (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) (𝓝[>] 0)
        (𝓝 (φ (quad S ω))) := by
      have hc2 : Continuous fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω) :=
        hφcont.comp ((continuous_quad ω).comp (by fun_prop))
      have := hc2.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have heq : (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hPD _ (PosDef.posSemidef_add hS (PosDef.one.smul hε)) ω
    exact tendsto_nhds_unique (h1.congr' heq) h2
  /- No zeros, by the cascade along the rays `sI ≤_W tI`. -/
  have hφne : ∀ u : ℝ, 0 ≤ u → φ u ≠ 0 := by
    have hmemT : ∀ p : ℝ × ℝ, 0 ≤ p.1 ∧ p.1 ≤ p.2 →
        (p.1 • (1 : Mat d), p.2 • (1 : Mat d)) ∈ wedgePairs le := fun p hp =>
      ⟨PosSemidef.one.smul hp.1, PosSemidef.one.smul (hp.1.trans hp.2),
        hW.rays 1 PosSemidef.one p.1 p.2 hp.1 hp.2⟩
    have hcontT : ContinuousOn (fun p : ℝ × ℝ => charFun (μ (p.1 • 1) (p.2 • 1)) e₀)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      (hμ.continuous e₀).comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 • (1 : Mat d), p.2 • (1 : Mat d))).continuousOn hmemT
    have hdiagT : ∀ t : ℝ, 0 ≤ t → charFun (μ (t • 1) (t • 1)) e₀ = 1 := by
      intro t ht
      rw [hμ.diag _ (PosSemidef.one.smul ht), charFun_dirac]
      simp
    have hcascT : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        charFun (μ ((0 : ℝ) • 1) (t • 1)) e₀ =
          charFun (μ (s • 1) (t • 1)) e₀ * charFun (μ ((0 : ℝ) • 1) (s • 1)) e₀ := by
      intro s t hs hst
      have m1 := hmemT (0, s) ⟨le_rfl, hs⟩
      have m2 := hmemT (s, t) ⟨hs, hst⟩
      haveI := hμ.isProbability _ m1
      haveI := hμ.isProbability _ m2
      rw [hμ.cascade _ _ _ m1.1 m1.2.1 m2.2.1 m1.2.2 m2.2.2, charFun_conv]
    have key := ne_zero_of_cascade (fun s t => charFun (μ (s • 1) (t • 1)) e₀) hcontT hdiagT
      hcascT
    intro u hu
    have := key u hu
    rwa [zero_smul, hPSD _ (PosSemidef.one.smul hu), quad_smul, quad_one, he₀, one_pow,
      mul_one] at this
  /- The increments, as quotients. -/
  have hinc : ∀ p ∈ wedgePairs le, ∀ ω : Rd d,
      charFun (μ p.1 p.2) ω = φ (quad p.2 ω) / φ (quad p.1 ω) := by
    intro p hp ω
    have m1 := hmem0 p.1 hp.1
    haveI := hμ.isProbability _ m1
    haveI := hμ.isProbability _ hp
    have hc := hμ.cascade 0 p.1 p.2 PosSemidef.zero hp.1 hp.2.1 m1.2.2 hp.2.2
    have h1 := congrArg (fun m => charFun m ω) hc
    rw [charFun_conv, hPSD _ hp.2.1, hPSD _ hp.1] at h1
    rw [h1, mul_div_assoc, div_self (hφne _ (quad_nonneg hp.1 ω)), mul_one]
  /- (K3) for every `A ∈ GL(d)`. -/
  intro A hA p hp
  have hq : (act A p.1, act A p.2) ∈ wedgePairs le :=
    ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1,
      hWgl.invariant A hA p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
  haveI := hμ.isProbability _ hp
  haveI := hμ.isProbability _ hq
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_push A hA, hinc p hp, hinc _ hq, quad_act, quad_act]

/-- **`prop:glplus-families`(2)**, in particular: for `d ≥ 2` and `W` the Loewner order, the
`(GL⁺(d), W)`-cascade families of kernels are the affine Gaussian scale spaces, `b > 0` (on the
Loewner pairs). -/
theorem glPlus_loewner_rigidity (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d)) :
    IsGWCascadeFamily (glPlusSet d) loewnerLE μ ↔
      ∃ b : ℝ, 0 < b ∧ EqOnPairs loewnerLE μ (affineGaussian b) := by
  have hd1 : 1 ≤ d := by omega
  rw [gw_family_glPlus_iff hd (isWedgeDatum_loewner (glPlusSet_isClosedSubgroupGL hd1).1
    (glPlusSet_isClosedSubgroupGL hd1).2) μ]
  exact affine_rigidity hd μ

/-! ## (3): the line -/

/-- On `ℝ¹`, a `1 × 1` matrix acts by multiplication by its entry. -/
theorem lin_single_mat_one (A : Mat 1) (c : ℝ) :
    lin A (EuclideanSpace.single 0 c) = EuclideanSpace.single 0 (A 0 0 * c) := by
  ext i
  fin_cases i
  have h2 := congrFun (ofLp_lin A (EuclideanSpace.single 0 c)) 0
  simp [mulVec, dotProduct] at h2
  simpa using h2

/-- On `PSD(1)`, `A · Σ` multiplies the entry by `A₀₀²`. -/
theorem act_mat_one_apply (A S : Mat 1) : act A S 0 0 = A 0 0 * S 0 0 * A 0 0 := by
  simp [act, Matrix.mul_apply]

/-- A symmetric `1 × 1` matrix is positive semidefinite exactly when its entry is nonnegative. -/
theorem posSemidef_mat_one_iff {M : Mat 1} (hM : M.IsHermitian) : M.PosSemidef ↔ 0 ≤ M 0 0 := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    have := h.2 (fun _ => 1)
    simpa [dotProduct, mulVec] using this
  · intro h
    refine ⟨hM, fun x => ?_⟩
    simp [dotProduct, mulVec]
    nlinarith [sq_nonneg (x 0)]

/-- The family of `prop:glplus-families`(3): `μ_{s,t} = δ_{√t - √s}`, read at the only entry. -/
theorem isGW_line_glPlus : IsGWCascadeFamily (glPlusSet 1) loewnerLE
    (fun S S' : Mat 1 =>
      Measure.dirac (EuclideanSpace.single 0 (Real.sqrt (S' 0 0) - Real.sqrt (S 0 0)))) where
  isProbability _ _ := inferInstance
  diag S _ := by
    simp only [sub_self]
    congr 1
    ext i
    fin_cases i
    simp
  cascade S S' S'' _ _ _ _ _ := by
    rw [Measure.dirac_conv_dirac, ← PiLp.single_add]
    congr 2
    ring
  continuous ω := by
    refine Continuous.continuousOn ?_
    simp only [charFun_dirac, EuclideanSpace.inner_single_left]
    have h1 : Continuous fun p : Mat 1 × Mat 1 => p.1 0 0 :=
      (continuous_apply 0).comp ((continuous_apply 0).comp continuous_fst)
    have h2 : Continuous fun p : Mat 1 × Mat 1 => p.2 0 0 :=
      (continuous_apply 0).comp ((continuous_apply 0).comp continuous_snd)
    have h3 := Real.continuous_sqrt.comp h1
    have h4 := Real.continuous_sqrt.comp h2
    simp only [starRingEnd_apply, star_trivial]
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ((h4.sub h3).mul
      continuous_const)).mul continuous_const)
  covariant A hA p hp := by
    have hA0 : 0 < A 0 0 := by
      have : 0 < A.det := hA
      simpa [det_unique] using this
    have hS : 0 ≤ p.1 0 0 := (posSemidef_mat_one_iff hp.1.isHermitian).mp hp.1
    have hS' : 0 ≤ p.2 0 0 := (posSemidef_mat_one_iff hp.2.1.isHermitian).mp hp.2.1
    simp only [push]
    simp only [Measure.map_dirac' (lin A).continuous.measurable, lin_single_mat_one,
      act_mat_one_apply]
    have hsq : ∀ s : ℝ, 0 ≤ s → Real.sqrt (A 0 0 * s * A 0 0) = A 0 0 * Real.sqrt s := by
      intro s hs
      rw [show A 0 0 * s * A 0 0 = A 0 0 ^ 2 * s by ring, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hA0.le]
    rw [hsq _ hS, hsq _ hS']
    congr 2
    ring
  nondegenerate := by
    simp only [Matrix.zero_apply, Matrix.one_apply_eq, Real.sqrt_zero, Real.sqrt_one, sub_zero]
    intro h
    have := MeasureTheory.dirac_eq_dirac_iff.mp h
    simp at this

/-- The family of `prop:glplus-families`(3) is not `GL(1)`-covariant: `-1` fixes `(0, 1)` and
moves `δ₁` to `δ_{-1}`. -/
theorem not_isGW_line_gl : ¬ IsGWCascadeFamily (glSet 1) loewnerLE
    (fun S S' : Mat 1 =>
      Measure.dirac (EuclideanSpace.single 0 (Real.sqrt (S' 0 0) - Real.sqrt (S 0 0)))) := by
  intro h
  have hA : (-1 : Mat 1) ∈ glSet 1 := by
    change IsUnit (-1 : Mat 1).det
    simp [det_unique]
  have hp : ((0 : Mat 1), (1 : Mat 1)) ∈ wedgePairs loewnerLE :=
    ⟨PosSemidef.zero, PosSemidef.one, by simp [loewnerLE, PosSemidef.one]⟩
  have hc := h.covariant (-1) hA _ hp
  have h0 : act (-1 : Mat 1) 0 = 0 := by simp [act]
  have h1 : act (-1 : Mat 1) 1 = 1 := by simp [act]
  simp only [h0, h1, push] at hc
  simp only [Measure.map_dirac' (lin (-1 : Mat 1)).continuous.measurable, lin_single_mat_one] at hc
  have := MeasureTheory.dirac_eq_dirac_iff.mp hc
  simp only [Matrix.zero_apply, Matrix.one_apply_eq, Real.sqrt_zero, Real.sqrt_one, sub_zero,
    Matrix.neg_apply, neg_mul, one_mul] at this
  have h2 := congrArg (fun x : Rd 1 => x 0) this
  simp at h2
  norm_num at h2

/-- **`prop:glplus-families`(3)**, the line: for `d = 1` the Loewner order on `PSD(1) = [0,∞)` is
the usual order, and the point masses `μ_{s,t} := δ_{√t - √s}` form a `(GL⁺(1), Loewner)`-cascade
family of kernels that is not a `(GL(1), Loewner)`-cascade family. -/
theorem glPlus_line_counterexample :
    let μ : Mat 1 → Mat 1 → Measure (Rd 1) := fun S S' =>
      Measure.dirac (EuclideanSpace.single 0 (Real.sqrt (S' 0 0) - Real.sqrt (S 0 0)))
    (∀ S S' : Mat 1, S.PosSemidef → S'.PosSemidef → (loewnerLE S S' ↔ S 0 0 ≤ S' 0 0)) ∧
      IsGWCascadeFamily (glPlusSet 1) loewnerLE μ ∧ ¬ IsGWCascadeFamily (glSet 1) loewnerLE μ := by
  intro μ
  refine ⟨fun S S' hS hS' => ?_, isGW_line_glPlus, not_isGW_line_gl⟩
  rw [loewnerLE, posSemidef_mat_one_iff (hS'.isHermitian.sub hS.isHermitian), Matrix.sub_apply,
    sub_nonneg]

end AffineHemigroup
