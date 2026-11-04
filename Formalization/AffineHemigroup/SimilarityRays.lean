/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilaritySpectrum
import AffineHemigroup.IsotropicCorner
import AffineHemigroup.ParameterSpace
import AffineHemigroup.StableOrder

/-!
# `prop:similarity-ray-families`: the cell (similarities, rays)

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-ray-families`. Wave 2,
group E, Q-0281. (1) the parameter set: the orbits of `S(d)` on `PSD(d) ∖ {0}` are indexed by
`σ(Σ) ∈ Δ_d` (through the sorted spectral theorem of `AffineHemigroup.SimilaritySpectrum`), the
simplex, the stabilizers; (2) the families and their symmetries; (3) the isotropic member and the
two families with the same member (the affine orbit and the shape-blind family, the latter also
along the Loewner order, through the monotonicity of `det` along the Loewner order); (4) the
isotropic members of the similarity row.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder

variable {d : ℕ}

/-! ## Similarities -/

/-- `A⁻¹ · (A · Σ) = Σ` for invertible `A`. -/
theorem act_inv_act {A : Mat d} (hA : A ∈ glSet d) (S : Mat d) : act A⁻¹ (act A S) = S := by
  have h : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  rw [act, act, transpose_nonsing_inv]
  calc A⁻¹ * (A * S * Aᵀ) * Aᵀ⁻¹ = (A⁻¹ * A) * S * (Aᵀ * Aᵀ⁻¹) := by simp only [Matrix.mul_assoc]
    _ = S := by
      rw [h, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hA), Matrix.one_mul,
        Matrix.mul_one]

/-- An orthogonal matrix is a similarity. -/
theorem orthSet_subset_simSet : orthSet d ⊆ simSet d := fun Q hQ =>
  ⟨1, one_pos, Q, hQ, (one_smul _ _).symm⟩

/-- `-I` is a similarity. -/
theorem neg_one_mem_simSet : (-1 : Mat d) ∈ simSet d :=
  orthSet_subset_simSet ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 (by simp))

/-- **`σ` is constant on the orbits of `S(d)`.** -/
theorem normSpec_act {A : Mat d} (hA : A ∈ simSet d) {S : Mat d} (hS : S.PosSemidef) :
    normSpec (act A S) = normSpec S := by
  obtain ⟨c, hc, Q, hQ, rfl⟩ := hA
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  rw [normSpec, normSpec, eigUp_act_smul_orth c hQQ hS.1, trace_act_smul_orth c hQQ]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
  funext i
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  field_simp

/-- **Equal `σ` gives one orbit**: for `Σ, Σ' ∈ PSD(d) ∖ {0}` with `σ(Σ) = σ(Σ')`, `Σ' = A · Σ` for
`A = (tr Σ'/tr Σ)^{1/2} V'Vᵀ`. -/
theorem exists_sim_of_normSpec_eq {S S' : Mat d} (hS : S.PosSemidef) (h0 : S ≠ 0)
    (hS' : S'.PosSemidef) (h0' : S' ≠ 0) (h : normSpec S = normSpec S') :
    ∃ A ∈ simSet d, S' = act A S := by
  have ht := trace_pos_of_posSemidef hS h0
  have ht' := trace_pos_of_posSemidef hS' h0'
  set k := S'.trace / S.trace with hk
  have hk0 : 0 < k := div_pos ht' ht
  have heig : eigUp S' = k • eigUp S := by
    funext j
    have hj := congrFun h (Fin.rev j)
    simp only [normSpec, Pi.smul_apply, Function.comp_apply, Fin.rev_rev, smul_eq_mul] at hj
    simp only [Pi.smul_apply, smul_eq_mul, hk]
    field_simp at hj ⊢
    linarith
  obtain ⟨V, hV, hSV⟩ := exists_orth_diag_eigUp hS.1
  obtain ⟨V', hV', hSV'⟩ := exists_orth_diag_eigUp hS'.1
  have hW : (V' * Vᵀ) * (V' * Vᵀ)ᵀ = 1 := by
    rw [Matrix.transpose_mul, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_assoc V',
      transpose_mul_self_of_mul_transpose hV, Matrix.mul_one, hV']
  refine ⟨Real.sqrt k • (V' * Vᵀ), ⟨Real.sqrt k, Real.sqrt_pos.2 hk0, V' * Vᵀ,
    (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hW, rfl⟩, ?_⟩
  rw [act_smul_left, Real.sq_sqrt hk0.le]
  have hVV := transpose_mul_self_of_mul_transpose hV
  calc S' = V' * diagonal (k • eigUp S) * V'ᵀ := by rw [← heig]; exact hSV'
    _ = k • (V' * (Vᵀ * (V * diagonal (eigUp S) * Vᵀ) * V) * V'ᵀ) := by
        rw [diagonal_smul]
        simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
        simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
    _ = _ := by
        rw [← hSV, Matrix.transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]

/-- **Each orbit meets the diagonal at `diag σ(Σ)`.** -/
theorem exists_sim_act_eq_diagonal {S : Mat d} (hS : S.PosSemidef) (h0 : S ≠ 0) :
    ∃ A ∈ simSet d, act A S = diagonal (normSpec S) := by
  have ht := trace_pos_of_posSemidef hS h0
  obtain ⟨V, hV, hSV⟩ := exists_orth_diag_eigUp hS.1
  set R : Mat d := permMat Fin.revPerm with hR
  have hRV : (R * Vᵀ) * (R * Vᵀ)ᵀ = 1 := by
    rw [Matrix.transpose_mul, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_assoc R,
      transpose_mul_self_of_mul_transpose hV, Matrix.mul_one, hR, permMat_mul_transpose]
  refine ⟨(Real.sqrt S.trace)⁻¹ • (R * Vᵀ), ⟨(Real.sqrt S.trace)⁻¹,
    inv_pos.2 (Real.sqrt_pos.2 ht), R * Vᵀ, (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hRV,
    rfl⟩, ?_⟩
  rw [act_smul_left, inv_pow, Real.sq_sqrt ht.le, normSpec, diagonal_smul]
  congr 1
  have hVV := transpose_mul_self_of_mul_transpose hV
  have hP := permMat_conj_diagonal Fin.revPerm (eigUp S)
  calc R * Vᵀ * S * (R * Vᵀ)ᵀ = R * (Vᵀ * V) * diagonal (eigUp S) * ((Vᵀ * V) * Rᵀ) := by
        conv_lhs => rw [hSV]
        rw [Matrix.transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]
    _ = diagonal (eigUp S ∘ Fin.rev) := by
        rw [hVV, Matrix.mul_one, Matrix.one_mul, hR, hP]
        rfl

/-- **`prop:similarity-ray-families`(1)**, the parameter set: `(S(d), W)` is a wedge datum; two
nonzero `Σ, Σ' ∈ PSD(d)` lie in one orbit exactly when `σ(Σ) = σ(Σ')`; each orbit contains exactly
one `diag(σ)` with `σ ∈ Δ_d`, a simplex of dimension `d - 1`; the stabilizer of `Σ ≠ 0` is
`{Q ∈ O(d) : QΣ = ΣQ}`, and it is `O(d)` exactly when `Σ` is a multiple of `I`. -/
theorem similarity_ray_parameter (hd : 1 ≤ d) :
    IsWedgeDatum (simSet d) rayLE ∧
      (∀ S S' : Mat d, S.PosSemidef → S ≠ 0 → S'.PosSemidef → S' ≠ 0 →
        ((∃ A ∈ simSet d, S' = act A S) ↔ normSpec S = normSpec S')) ∧
      (∀ S : Mat d, S.PosSemidef → S ≠ 0 →
        ∃! σ : Fin d → ℝ, σ ∈ simplexDesc d ∧ ∃ A ∈ simSet d, act A S = diagonal σ) ∧
      (∃ v : Fin d → Fin d → ℝ, AffineIndependent ℝ v ∧ simplexDesc d = convexHull ℝ (range v)) ∧
      (∀ S : Mat d, S.PosSemidef → S ≠ 0 →
        {A | A ∈ simSet d ∧ act A S = S} = {Q | Q ∈ orthSet d ∧ Q * S = S * Q}) ∧
      ∀ S : Mat d, S.PosSemidef → S ≠ 0 →
        ({A | A ∈ simSet d ∧ act A S = S} = orthSet d ↔ ∃ c : ℝ, S = c • (1 : Mat d)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hGs, hdils⟩ := simSet_isClosedSubgroupGL (d := d)
  -- the stabilizer
  have hstab : ∀ S : Mat d, S.PosSemidef → S ≠ 0 →
      {A | A ∈ simSet d ∧ act A S = S} = {Q | Q ∈ orthSet d ∧ Q * S = S * Q} := by
    intro S hS h0
    have ht := trace_pos_of_posSemidef hS h0
    ext A
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨⟨c, hc, Q, hQ, rfl⟩, hact⟩
      have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
      have htr := congrArg Matrix.trace hact
      rw [trace_act_smul_orth c hQQ] at htr
      have hc1 : c = 1 := by
        have h2 : c ^ 2 = 1 := by
          have := mul_right_cancel₀ ht.ne' (htr.trans (one_mul _).symm)
          exact this
        nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
      subst hc1
      rw [one_smul] at hact ⊢
      refine ⟨hQ, ?_⟩
      have hQtQ := transpose_mul_self_of_mul_transpose hQQ
      calc Q * S = Q * S * (Qᵀ * Q) := by rw [hQtQ, Matrix.mul_one]
        _ = act Q S * Q := by rw [act]; simp only [Matrix.mul_assoc]
        _ = S * Q := by rw [hact]
    · rintro ⟨hQ, hcomm⟩
      have hQQ : A * Aᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
      refine ⟨orthSet_subset_simSet hQ, ?_⟩
      rw [act, hcomm, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  refine ⟨isWedgeDatum_ray hGs hdils, fun S S' hS h0 hS' h0' => ⟨?_, ?_⟩,
    fun S hS h0 => ?_, ⟨simplexVtx, simplexDesc_simplex⟩, hstab, fun S hS h0 => ?_⟩
  · rintro ⟨A, hA, rfl⟩
    exact (normSpec_act hA hS).symm
  · exact exists_sim_of_normSpec_eq hS h0 hS' h0'
  · obtain ⟨A, hA, hAS⟩ := exists_sim_act_eq_diagonal hS h0
    refine ⟨normSpec S, ⟨normSpec_mem_simplexDesc hS h0, A, hA, hAS⟩, ?_⟩
    rintro σ ⟨hσ, B, hB, hBS⟩
    rw [← normSpec_diagonal hσ, ← hBS, normSpec_act hB hS]
  · rw [hstab S hS h0]
    constructor
    · intro h
      have hinv : ∀ Q ∈ orthSet d, act Q S = S := by
        intro Q hQ
        have hQ' : Q ∈ {Q | Q ∈ orthSet d ∧ Q * S = S * Q} := by rw [h]; exact hQ
        have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
        rw [act, hQ'.2, Matrix.mul_assoc, hQQ, Matrix.mul_one]
      exact ⟨S 0 0, eq_smul_one_of_orth_invariant hinv⟩
    · rintro ⟨c, rfl⟩
      ext Q
      simp only [mem_setOf_eq, and_iff_left_iff_imp]
      intro _
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-! ## Clause (2): the families -/

/-- `(S(d), W)` is a wedge datum. -/
theorem simSet_isWedgeDatum_ray [NeZero d] : IsWedgeDatum (simSet d) rayLE :=
  isWedgeDatum_ray simSet_isClosedSubgroupGL.1 simSet_isClosedSubgroupGL.2

/-- **`prop:similarity-ray-families`(2)**: the kernels from the origin of the
`(S(d), W)`-cascade families are the maps of `prop:gw-ray-families`(2) with `G = S(d)`. -/
theorem similarity_ray_families (hd : 1 ≤ d) (m : Mat d → Measure (Rd d))
    (hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S)) :
    IsKernelsFromOrigin (simSet d) rayLE m ↔
      IsOriginKernels (simSet d) m ∧ ∀ S : Mat d, S.PosSemidef → IsSelfDecomposable (m S) := by
  haveI : NeZero d := ⟨by omega⟩
  exact gw_ray_families simSet_isWedgeDatum_ray m hprob

/-- **`prop:similarity-ray-families`(2)**: in an `(S(d), W)`-cascade family every `μ_Σ` is
symmetric and invariant under the stabilizer of `Σ`, `μ_{cQ diag(σ) Qᵀ} = (√c Q)_*μ_{diag(σ)}`,
and the family is determined (on the pairs) by its kernels at the `diag(σ)`, `σ ∈ Δ_d`. -/
theorem similarity_ray_kernels (hd : 1 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (simSet d) rayLE μ) :
    (∀ S : Mat d, S.PosSemidef → push (-1) (μ 0 S) = μ 0 S) ∧
      (∀ S : Mat d, S.PosSemidef → ∀ A ∈ simSet d, act A S = S → push A (μ 0 S) = μ 0 S) ∧
      (∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d, ∀ σ ∈ simplexDesc d,
        μ 0 (c • (Q * diagonal σ * Qᵀ)) = push (Real.sqrt c • Q) (μ 0 (diagonal σ))) ∧
      ∀ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (simSet d) rayLE ν →
        (∀ σ ∈ simplexDesc d, ν 0 (diagonal σ) = μ 0 (diagonal σ)) → EqOnPairs rayLE μ ν := by
  haveI : NeZero d := ⟨by omega⟩
  have hW : IsWedgeDatum (simSet d) rayLE := simSet_isWedgeDatum_ray
  have hpair : ∀ S : Mat d, S.PosSemidef → ((0 : Mat d), S) ∈ wedgePairs rayLE :=
    fun S hS => ⟨PosSemidef.zero, hS, Or.inl rfl⟩
  have hcov : ∀ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (simSet d) rayLE ν →
      ∀ A ∈ simSet d, ∀ S : Mat d, S.PosSemidef → push A (ν 0 S) = ν 0 (act A S) := by
    intro ν hν A hA S hS
    have h := hν.covariant A hA _ (hpair S hS)
    dsimp only at h
    rw [h, act_zero]
  refine ⟨fun S hS => ?_, fun S hS A hA hAS => ?_, fun c hc Q hQ σ hσ => ?_, fun ν hν h => ?_⟩
  · rw [hcov μ hμ _ neg_one_mem_simSet S hS]
    congr 1
    simp [act]
  · rw [hcov μ hμ A hA S hS, hAS]
  · rw [hcov μ hμ _ ⟨Real.sqrt c, Real.sqrt_pos.2 hc, Q, hQ, rfl⟩ _
      (PosSemidef.diagonal hσ.2.1), act_smul_left, Real.sq_sqrt hc.le]
  · refine gw_family_determined_by_kernels hW μ ν hμ hν fun S hS => ?_
    by_cases h0 : S = 0
    · subst h0
      rw [hν.diag 0 PosSemidef.zero, hμ.diag 0 PosSemidef.zero]
    · obtain ⟨A, hA, hAS⟩ := exists_sim_act_eq_diagonal hS h0
      have hAinv := hGsinv hA
      have hSA : S = act A⁻¹ (diagonal (normSpec S)) := by
        rw [← hAS, act_inv_act (simSet_subset_glSet hA)]
      have hdiag := (diagonal_simplexDesc (normSpec_mem_simplexDesc hS h0)).1
      rw [hSA, ← hcov ν hν _ hAinv _ hdiag, ← hcov μ hμ _ hAinv _ hdiag,
        h _ (normSpec_mem_simplexDesc hS h0)]
where
  hGsinv {A : Mat d} [NeZero d] (hA : A ∈ simSet d) : A⁻¹ ∈ simSet d :=
    simSet_isClosedSubgroupGL.1.inv_mem A hA

/-! ## Clause (3): the isotropic member -/

/-- **`prop:similarity-ray-families`(3)**, the isotropic member: in an `(S(d), W)`-cascade family
`μ_{sI} = (√s I)_*μ_I` for `s ≥ 0`, and `μ_I` is rotation invariant, self-decomposable and not
`δ₀`. -/
theorem similarity_ray_isotropic (hd : 1 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (simSet d) rayLE μ) :
    (∀ s : ℝ, 0 ≤ s → μ 0 (s • (1 : Mat d)) = push (Real.sqrt s • (1 : Mat d)) (μ 0 1)) ∧
      IsRotationInvariant (μ 0 1) ∧ IsSelfDecomposable (μ 0 1) ∧ μ 0 1 ≠ Measure.dirac 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hW : IsWedgeDatum (simSet d) rayLE := simSet_isWedgeDatum_ray
  have h01 := wedge_zero_one_mem hW
  refine ⟨fun s hs => gw_kernel_smul_one hW μ hμ hs, fun Q hQ => ?_,
    gw_kernels_selfDecomposable hW μ hμ 1 PosSemidef.one, hμ.nondegenerate⟩
  have h := hμ.covariant Q (orthSet_subset_simSet hQ) _ h01
  dsimp only at h
  rw [h, act_zero, act_orth_one hQ]

/-- **`det` is monotone along the Loewner order** on `PSD(d)`. -/
theorem det_le_det_of_loewnerLE [NeZero d] {S S' : Mat d} (hS : S.PosSemidef)
    (hle : loewnerLE S S') : S.det ≤ S'.det := by
  have hS' : S'.PosSemidef := by
    have := hS.add hle
    rwa [add_sub_cancel] at this
  by_cases hpd : S.PosDef
  · have hS'pd : S'.PosDef := by
      have := hpd.add_posSemidef hle
      rwa [add_sub_cancel] at this
    set M := relStep S S' with hM
    have hMpd : M.PosDef := (posDef_relStep_iff hpd S').2 hS'pd
    have hM1 : (M - (1 : ℝ) • (1 : Mat d)).PosSemidef := by
      rw [one_smul, ← relStep_self hpd, hM, ← relStep_sub]
      exact (posSemidef_relStep_iff hpd _).2 hle
    have hlam : 1 ≤ lamMin M := by
      rw [← (eigUp_spec hMpd.1).2.2.1]
      exact (posSemidef_sub_smul_one_iff hMpd.1 1).1 hM1
    have hdetM : 1 ≤ M.det := by
      have := lamMin_pow_le_det hMpd
      calc (1 : ℝ) = 1 ^ d := (one_pow d).symm
        _ ≤ lamMin M ^ d := pow_le_pow_left₀ zero_le_one hlam d
        _ ≤ M.det := this
    rw [hM, det_relStep hpd] at hdetM
    rwa [le_div_iff₀ hpd.det_pos, one_mul] at hdetM
  · have h0 : S.det = 0 := by
      by_contra h
      exact hpd ((hS.posDef_iff_det_ne_zero).2 h)
    rw [h0]
    exact hS'.det_nonneg

/-- **Dilated increments of a self-decomposable law**: for `0 ≤ a ≤ b`,
`(bI)_*μ = (aI)_*μ * ρ` for a probability measure `ρ`. -/
theorem exists_dilation_increment (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsd : IsSelfDecomposable μ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      push (b • (1 : Mat d)) μ = push (a • (1 : Mat d)) μ ∗ ρ := by
  rcases ha.eq_or_lt with rfl | ha0
  · refine ⟨push (b • (1 : Mat d)) μ, inferInstance, ?_⟩
    rw [zero_smul, push_zero_mat]
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, charFun_dirac]
    simp
  rcases hab.eq_or_lt with rfl | hab'
  · refine ⟨Measure.dirac 0, inferInstance, ?_⟩
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, charFun_dirac]
    simp
  have hb : 0 < b := ha0.trans hab'
  obtain ⟨ρ, hρ, hfac⟩ := (isSelfDecomposable_iff_charFun _).1 hsd (a / b) (div_pos ha0 hb)
    ((div_lt_one hb).2 hab')
  refine ⟨push (b • (1 : Mat d)) ρ, inferInstance, eq_of_charFun_eq fun ω => ?_⟩
  rw [charFun_conv, charFun_push_smul_one, charFun_push_smul_one, charFun_push_smul_one,
    hfac (b • ω), smul_smul, div_mul_cancel₀ _ hb.ne']

/-- **`prop:similarity-ray-families`(3)**, the isotropic member does not determine the family:
for a rotation-invariant self-decomposable `μ_I ≠ δ₀`, (i) `Σ ↦ (Σ^{1/2})_*μ_I` and (ii)
`Σ ↦ ((det Σ)^{1/(2d)} I)_*μ_I` are the kernels from the origin of `(S(d), W)`-cascade families
with isotropic member `μ_I`, (ii) also of an `(S(d), Loewner)`-cascade family; for `d ≥ 2` the two
differ at every `Σ ∈ PD(d)` that is not a multiple of `I`. -/
theorem similarity_ray_two_families (hd : 1 ≤ d) (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI) (hne : μI ≠ Measure.dirac 0) :
    IsKernelsFromOrigin (simSet d) rayLE (affineOrbit μI) ∧ affineOrbit μI 1 = μI ∧
      IsKernelsFromOrigin (simSet d) rayLE (shapeBlind μI) ∧ shapeBlind μI 1 = μI ∧
      IsKernelsFromOrigin (simSet d) loewnerLE (shapeBlind μI) ∧
      (2 ≤ d → ∀ S : Mat d, S.PosDef → (∀ c : ℝ, S ≠ c • (1 : Mat d)) →
        affineOrbit μI S ≠ shapeBlind μI S) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hGs, hdils⟩ := simSet_isClosedSubgroupGL (d := d)
  have hW : IsWedgeDatum (simSet d) rayLE := isWedgeDatum_ray hGs hdils
  have hWL : IsWedgeDatum (simSet d) loewnerLE := isWedgeDatum_loewner hGs hdils
  -- (i) the affine orbit
  obtain ⟨⟨ν₁, hν₁gl, hν₁1⟩, -⟩ := gw_ray_families_gl_converse μI hrot hsd hne
  have hk₁ := (gw_ray_families_gl ν₁ hν₁gl).1
  have hi : IsKernelsFromOrigin (simSet d) rayLE (affineOrbit μI) :=
    ⟨ν₁, gw_family_of_subset simSet_subset_glSet ν₁ hν₁gl, fun S hS => by rw [hk₁ S hS, hν₁1]⟩
  -- (ii) the shape-blind family
  have hok := shapeBlind_isOriginKernels μI hrot hne
  have hsb1 : shapeBlind μI 1 = μI := by
    rw [shapeBlind, volScale, det_one, Real.one_rpow, one_smul, push_one]
  have hz : HasNoZeros (shapeBlind μI) := fun S _ ω => by
    rw [shapeBlind, charFun_push_smul_one]
    exact (selfDecomposable_charFun_ne_zero μI hsd).1 _
  have hii : IsKernelsFromOrigin (simSet d) rayLE (shapeBlind μI) :=
    (gw_ray_families hW (shapeBlind μI) fun S _ => isProbabilityMeasure_push _ _).2
      ⟨hok, fun S _ => (selfDecomposable_charFun_ne_zero μI hsd).2 _⟩
  have hinc : HasIncrements loewnerLE (shapeBlind μI) := by
    intro S S' hS hS' hle
    have hdet := det_le_det_of_loewnerLE hS hle
    have hv : volScale S ≤ volScale S' :=
      Real.rpow_le_rpow hS.det_nonneg hdet (by positivity)
    exact exists_dilation_increment μI hsd (Real.rpow_nonneg hS.det_nonneg _) hv
  have hiiL := (gw_kernels_from_origin_converse hWL (shapeBlind μI) hok hz hinc).1
  refine ⟨hi, by rw [← hν₁1, ← hk₁ 1 PosSemidef.one], hii, hsb1, hiiL, fun hd2 S hS hnot h => ?_⟩
  -- the two differ off the multiples of `I`: `Stab(μ_I) = O(d)`
  have hv : 0 < volScale S := Real.rpow_pos_of_pos hS.det_pos _
  have hstab := (isFull_of_isRotationInvariant hd μI hrot hne).2
  have hP : (volScale S)⁻¹ • msqrt S ∈ stab μI := by
    refine ⟨?_, ?_⟩
    · have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
      change IsUnit ((volScale S)⁻¹ • msqrt S).det
      rw [det_smul]
      exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (inv_ne_zero hv.ne'))).mul hU
    · rw [show (volScale S)⁻¹ • msqrt S = ((volScale S)⁻¹ • (1 : Mat d)) * msqrt S by
        rw [Matrix.smul_mul, Matrix.one_mul], ← push_push]
      change push _ (affineOrbit μI S) = _
      rw [h, shapeBlind, push_smul_one_inv_cancel hv.ne']
  rw [hstab] at hP
  have hPP := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
  change ((volScale S)⁻¹ • msqrt S) * ((volScale S)⁻¹ • msqrt S)ᵀ = 1 at hPP
  rw [transpose_smul, msqrt_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    msqrt_mul_self hS.posSemidef] at hPP
  apply hnot (volScale S ^ 2)
  have h2 := congrArg (fun M => (volScale S ^ 2) • M) hPP
  simp only [smul_smul] at h2
  rw [show volScale S ^ 2 * ((volScale S)⁻¹ * (volScale S)⁻¹) = 1 by field_simp, one_smul] at h2
  exact h2

/-! ## Clause (4): the similarity row -/

/-- **`prop:similarity-ray-families`(4)**, the isotropic members of the similarity row: for an
`S(d)`-invariant partial order `W'` on `PSD(d)` that contains the rays and is contained in the
Loewner order, the isotropic members of the `(S(d), W')`-cascade families are exactly the
rotation-invariant self-decomposable laws other than `δ₀`. -/
theorem similarity_row_isotropic_members (hd : 1 ≤ d) (le' : Mat d → Mat d → Prop)
    (hpo : IsPartialOrderOn (psdSet d) le')
    (hinv : ∀ A ∈ simSet d, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le' S S' →
      le' (act A S) (act A S'))
    (hrays : ∀ S : Mat d, S.PosSemidef → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → le' (c • S) (c' • S))
    (hsub : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le' S S' → loewnerLE S S')
    (μI : Measure (Rd d)) :
    (∃ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (simSet d) le' μ ∧ μ 0 1 = μI) ↔
      IsProbabilityMeasure μI ∧ IsRotationInvariant μI ∧ IsSelfDecomposable μI ∧
        μI ≠ Measure.dirac 0 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hGs, hdils⟩ := simSet_isClosedSubgroupGL (d := d)
  have hW : IsWedgeDatum (simSet d) rayLE := isWedgeDatum_ray hGs hdils
  have hWL : IsWedgeDatum (simSet d) loewnerLE := isWedgeDatum_loewner hGs hdils
  have hW' : IsWedgeDatum (simSet d) le' :=
    { closedSubgroup := hGs
      dilations := hdils
      refl := fun S hS => hpo.refl S hS
      antisymm := fun S S' hS hS' => hpo.antisymm S hS S' hS'
      trans := fun S S' S'' hS hS' hS'' => hpo.trans S hS S' hS' S'' hS''
      invariant := hinv
      rays := hrays }
  have hray_le : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → rayLE S S' → le' S S' := by
    rintro S S' hS hS' (rfl | ⟨c, hc, rfl⟩)
    · simpa using hrays S' hS' 0 1 le_rfl zero_le_one
    · simpa using hrays S hS 1 c zero_le_one hc
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have hμr := gw_family_restrict hW hW' subset_rfl hray_le μ hμ
    obtain ⟨-, hrot, hsd, hne⟩ := similarity_ray_isotropic hd μ hμr
    exact ⟨hμ.isProbability _ (wedge_zero_one_mem hW'), hrot, hsd, hne⟩
  · rintro ⟨hprob, hrot, hsd, hne⟩
    obtain ⟨μ, hμ, hμ0⟩ := (similarity_ray_two_families hd μI hrot hsd hne).2.2.2.2.1
    refine ⟨μ, gw_family_restrict hW' hWL subset_rfl hsub μ hμ, ?_⟩
    rw [hμ0 1 PosSemidef.one, shapeBlind, volScale, det_one, Real.one_rpow, one_smul, push_one]

end AffineHemigroup
