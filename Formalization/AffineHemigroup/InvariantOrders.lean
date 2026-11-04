/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PathCondition
import AffineHemigroup.ParameterSpace
import AffineHemigroup.StableOrderPSD
import AffineHemigroup.MatrixCalculus

/-!
# `prop:invariant-orders`: invariant relations on `PD(d)` and their steps

Blueprint: `blueprint/src/parts/05-wedges.tex`, `prop:invariant-orders` (wave 2, group D, Q-0281).
Cites nothing beyond the spectral theorem. Every factor `A` of `Σ = AAᵀ` is `Σ^{1/2}Q` with `Q`
orthogonal, which turns every clause into a statement about the relative step; the closedness
clause reads the continuity of `Σ ↦ Σ^{1/2}` on `PSD(d)`, proved here by compactness and the
uniqueness of the positive square root.
-/

namespace AffineHemigroup

open Set Filter Matrix
open scoped Topology MatrixOrder

variable {d : ℕ}

/-! ## The square root is continuous on `PSD(d)` -/

/-- `PSD(d)` is closed. Mathlib types only. -/
theorem isClosed_psdSet : IsClosed (psdSet d) := by
  have h : psdSet d = {M : Mat d | Mᴴ = M} ∩
      ⋂ x : Fin d → ℝ, {M : Mat d | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [psdSet, mem_setOf_eq, posSemidef_iff_dotProduct_mulVec, mem_inter_iff, mem_iInter,
      IsHermitian]
  rw [h]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun x => ?_)
  exact isClosed_le continuous_const (by fun_prop)

/-- `0 ≤ Σ` gives `Σ ∈ PSD(d)` under `MatrixOrder`. -/
theorem posSemidef_of_nonneg {S : Mat d} (hS : 0 ≤ S) : S.PosSemidef := by
  have h := (loewnerLE_iff_le (S := 0) (S' := S)).2 hS
  rwa [loewnerLE, sub_zero] at h

/-- The entries of `Σ^{1/2}` are bounded by the diagonal of `Σ`: `(Σ^{1/2})ᵢⱼ² ≤ Σᵢᵢ`. -/
theorem sq_msqrt_entry_le {S : Mat d} (hS : S.PosSemidef) (i j : Fin d) :
    msqrt S i j ^ 2 ≤ S i i := by
  have h := congrFun (congrFun (msqrt_mul_self hS) i) i
  rw [mul_apply] at h
  have hsymm : ∀ k, msqrt S k i = msqrt S i k := fun k => by
    rw [← transpose_apply (msqrt S) i k, msqrt_transpose]
  simp_rw [hsymm] at h
  rw [← h]
  calc msqrt S i j ^ 2 = msqrt S i j * msqrt S i j := sq _
    _ ≤ ∑ k, msqrt S i k * msqrt S i k :=
        Finset.single_le_sum (f := fun k => msqrt S i k * msqrt S i k)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)

/-- **`Σ ↦ Σ^{1/2}` is sequentially continuous on `PSD(d)`**: a bounded sequence whose every limit
point is a positive square root of the limit converges to the square root. Mathlib types only. -/
theorem tendsto_msqrt {S : ℕ → Mat d} {S₀ : Mat d} (hS : ∀ n, (S n).PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => msqrt (S n)) atTop (𝓝 (msqrt S₀)) := by
  -- the diagonal entries are bounded
  have hdiag : ∀ i, ∃ C, ∀ n, S n i i ≤ C := by
    intro i
    have hi : Tendsto (fun n => S n i i) atTop (𝓝 (S₀ i i)) :=
      (continuous_id.matrix_elem i i).continuousAt.tendsto.comp hlim
    obtain ⟨C, hC⟩ := hi.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  choose C hC using hdiag
  set B : ℝ := ∑ i, |C i| + 1 with hB
  have hbound : ∀ n i j, |msqrt (S n) i j| ≤ Real.sqrt B := by
    intro n i j
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ((sq_msqrt_entry_le (hS n) i j).trans ((hC i n).trans ?_))
    calc C i ≤ |C i| := le_abs_self _
      _ ≤ ∑ k, |C k| := Finset.single_le_sum (f := fun k => |C k|) (fun k _ => abs_nonneg _)
          (Finset.mem_univ i)
      _ ≤ B := by rw [hB]; linarith
  set Kc : Set (Mat d) := Set.pi univ fun _ => Set.pi univ fun _ => Icc (-Real.sqrt B) (Real.sqrt B)
    with hKc
  have hK : IsCompact Kc := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, msqrt (S n) ∈ Kc := fun n i _ j _ => abs_le.1 (hbound n i j)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨A, -, φ, hφ, hA⟩ := hK.tendsto_subseq (x := fun k => msqrt (S (ns k))) fun k => hmem _
  refine ⟨φ, ?_⟩
  -- the limit point is the positive square root of `S₀`
  have hSφ : Tendsto (fun k => S (ns (φ k))) atTop (𝓝 S₀) :=
    hlim.comp (hns.comp hφ.tendsto_atTop)
  have hAA : A * A = S₀ := by
    have h1 : Tendsto (fun k => msqrt (S (ns (φ k))) * msqrt (S (ns (φ k)))) atTop (𝓝 (A * A)) :=
      hA.mul hA
    have h2 : (fun k => msqrt (S (ns (φ k))) * msqrt (S (ns (φ k)))) = fun k => S (ns (φ k)) :=
      funext fun k => msqrt_mul_self (hS _)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hSφ
  have hApsd : A.PosSemidef :=
    isClosed_psdSet.mem_of_tendsto hA (Eventually.of_forall fun k =>
      posSemidef_of_nonneg (CFC.sqrt_nonneg _))
  have hAeq : msqrt S₀ = A := CFC.sqrt_unique hAA (nonneg_of_posSemidef hApsd)
  rw [hAeq]
  exact hA

/-! ## Factors and relative steps -/

/-- **Every factor is `Σ^{1/2}` times an orthogonal matrix**: if `AAᵀ = Σ ∈ PD(d)`, then
`Q := Σ^{-1/2}A ∈ O(d)`. -/
theorem msqrt_inv_mul_mem_orthSet {S A : Mat d} (hS : S.PosDef) (hAS : A * Aᵀ = S) :
    (msqrt S)⁻¹ * A ∈ orthSet d := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2
  change (msqrt S)⁻¹ * A * ((msqrt S)⁻¹ * A)ᵀ = 1
  rw [transpose_mul, msqrt_inv_transpose]
  calc (msqrt S)⁻¹ * A * (Aᵀ * (msqrt S)⁻¹) = (msqrt S)⁻¹ * (A * Aᵀ) * (msqrt S)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = relStep S S := by rw [hAS]; rfl
    _ = 1 := relStep_self hS

theorem orth_mul_transpose {Q : Mat d} (hQ : Q ∈ orthSet d) : Q * Qᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ

theorem orth_transpose_mul {Q : Mat d} (hQ : Q ∈ orthSet d) : Qᵀ * Q = 1 :=
  mul_eq_one_comm.1 (orth_mul_transpose hQ)

/-- **The step of a factor**: if `AAᵀ = Σ ∈ PD(d)`, then `A⁻¹Σ'A⁻ᵀ = QᵀMQ` with `M` the relative
step and `Q = Σ^{-1/2}A ∈ O(d)`. -/
theorem factor_step {S A : Mat d} (hS : S.PosDef) (hAS : A * Aᵀ = S) (S' : Mat d) :
    A⁻¹ * S' * A⁻¹ᵀ = ((msqrt S)⁻¹ * A)ᵀ * relStep S S' * ((msqrt S)⁻¹ * A) := by
  have hQ := msqrt_inv_mul_mem_orthSet hS hAS
  generalize hQdef : (msqrt S)⁻¹ * A = Q at hQ ⊢
  have hA : A = msqrt S * Q := by
    rw [← hQdef, ← Matrix.mul_assoc, msqrt_mul_inv hS, Matrix.one_mul]
  have hAinv : A⁻¹ = Qᵀ * (msqrt S)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc Q, orth_mul_transpose hQ, Matrix.one_mul,
      msqrt_mul_inv hS]
  rw [hAinv, transpose_mul, transpose_transpose, msqrt_inv_transpose, relStep]
  simp only [Matrix.mul_assoc]

/-- A step set is invariant under `M ↦ QᵀMQ`, `Q ∈ O(d)`, in both directions. -/
theorem IsStepSet.conj_iff {K : Set (Mat d)} (hK : IsStepSet K) {Q : Mat d} (hQ : Q ∈ orthSet d)
    (M : Mat d) : Qᵀ * M * Q ∈ K ↔ M ∈ K := by
  constructor
  · intro h
    have := hK.2 _ h Q hQ
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, orth_mul_transpose hQ, Matrix.one_mul,
      Matrix.mul_assoc, orth_mul_transpose hQ, Matrix.mul_one] at this
  · intro h
    have := hK.2 _ h Qᵀ (transpose_mem_orthSet hQ)
    rwa [transpose_transpose] at this

/-- **`prop:invariant-orders`(1)**: for `Σ, Σ' ∈ PD(d)` and every `A ∈ GL(d)` with `AAᵀ = Σ`,
`Σ ≤_𝒦 Σ'` if and only if `A⁻¹Σ'A⁻ᵀ ∈ 𝒦`. -/
theorem stepLE_iff_factor (_hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (A : Mat d) (_hA : A ∈ glSet d) (hAS : A * Aᵀ = S) :
    stepLE K S S' ↔ A⁻¹ * S' * (A⁻¹)ᵀ ∈ K := by
  rw [factor_step hS hAS, hK.conj_iff (msqrt_inv_mul_mem_orthSet hS hAS)]
  exact ⟨fun h => h.2.2, fun h => ⟨hS, hS', h⟩⟩

/-- `(BΣ^{1/2})(BΣ^{1/2})ᵀ = BΣBᵀ`. -/
theorem mul_msqrt_mul_transpose {S : Mat d} (hS : S.PosSemidef) (B : Mat d) :
    B * msqrt S * (B * msqrt S)ᵀ = act B S := by
  rw [transpose_mul, msqrt_transpose, act]
  calc B * msqrt S * (msqrt S * Bᵀ) = B * (msqrt S * msqrt S) * Bᵀ := by
        simp only [Matrix.mul_assoc]
    _ = B * S * Bᵀ := by rw [msqrt_mul_self hS]

/-- **`prop:invariant-orders`(1)**: `≤_𝒦` is `GL(d)`-invariant, `Σ ≤_𝒦 Σ'` if and only if
`BΣBᵀ ≤_𝒦 BΣ'Bᵀ`, for every `B ∈ GL(d)`. -/
theorem stepLE_invariant (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (B : Mat d) (hB : B ∈ glSet d) :
    stepLE K S S' ↔ stepLE K (act B S) (act B S') := by
  have hBS := (posDef_act_iff hB S).2 hS
  have hBS' := (posDef_act_iff hB S').2 hS'
  have hU : IsUnit B.det := hB
  have hUS : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  rw [stepLE_iff_factor hd hK hBS hBS' (B * msqrt S) (by
      change IsUnit (B * msqrt S).det; rw [det_mul]; exact hU.mul hUS)
    (mul_msqrt_mul_transpose hS.posSemidef B)]
  have h : (B * msqrt S)⁻¹ * act B S' * ((B * msqrt S)⁻¹)ᵀ = relStep S S' := by
    rw [Matrix.mul_inv_rev, transpose_mul, msqrt_inv_transpose, act, relStep]
    have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hU
    have h2 : Bᵀ * B⁻¹ᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
    calc (msqrt S)⁻¹ * B⁻¹ * (B * S' * Bᵀ) * (B⁻¹ᵀ * (msqrt S)⁻¹)
        = (msqrt S)⁻¹ * (B⁻¹ * B) * S' * (Bᵀ * B⁻¹ᵀ) * (msqrt S)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (msqrt S)⁻¹ * S' * (msqrt S)⁻¹ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
  rw [h]
  exact ⟨fun h => h.2.2, fun h => ⟨hS, hS', h⟩⟩

/-- `Σ^{-1/2} Σ Σ^{-1/2} = I` read as an action: `act Σ^{-1/2} Σ = I`. -/
theorem act_msqrt_inv_self {S : Mat d} (hS : S.PosDef) : act (msqrt S)⁻¹ S = 1 := by
  rw [act, msqrt_inv_transpose]; exact relStep_self hS

theorem act_msqrt_inv {S : Mat d} (S' : Mat d) : act (msqrt S)⁻¹ S' = relStep S S' := by
  rw [act, msqrt_inv_transpose]; rfl

theorem msqrt_inv_mem_glSet {S : Mat d} (hS : S.PosDef) : (msqrt S)⁻¹ ∈ glSet d := by
  change IsUnit ((msqrt S)⁻¹).det
  rw [det_nonsing_inv]
  exact (msqrt_mem_glSet hS).ringInverse

/-- **`prop:invariant-orders`(1)**: every `GL(d)`-invariant relation `R` on `PD(d)` is `≤_𝒦` for
exactly one step set, `𝒦 = {M ∈ PD(d) : I R M}`. -/
theorem invariant_relation_eq_stepLE (_hd : 1 ≤ d) (R : Mat d → Mat d → Prop)
    (hR : ∀ B ∈ glSet d, ∀ S S' : Mat d, S.PosDef → S'.PosDef → R S S' → R (act B S) (act B S')) :
    let K : Set (Mat d) := {M | M.PosDef ∧ R 1 M}
    IsStepSet K ∧ (∀ S S' : Mat d, S.PosDef → S'.PosDef → (R S S' ↔ stepLE K S S')) ∧
      ∀ K' : Set (Mat d), IsStepSet K' →
        (∀ S S' : Mat d, S.PosDef → S'.PosDef → (R S S' ↔ stepLE K' S S')) → K' = K := by
  intro K
  have hstep : IsStepSet K := by
    refine ⟨fun M hM => hM.1, fun M hM Q hQ => ⟨(posDef_act_iff (orthSet_subset_glSet hQ) M).2 hM.1,
      ?_⟩⟩
    have := hR Q (orthSet_subset_glSet hQ) 1 M Matrix.PosDef.one hM.1 hM.2
    rwa [act_orth_one hQ] at this
  have hiff : ∀ S S' : Mat d, S.PosDef → S'.PosDef → (R S S' ↔ stepLE K S S') := by
    intro S S' hS hS'
    have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
    constructor
    · intro h
      have := hR _ (msqrt_inv_mem_glSet hS) S S' hS hS' h
      rw [act_msqrt_inv_self hS, act_msqrt_inv] at this
      exact ⟨hS, hS', hM, this⟩
    · rintro ⟨-, -, -, h⟩
      have := hR _ (msqrt_mem_glSet hS) 1 _ Matrix.PosDef.one hM h
      rwa [act_msqrt_one hS.posSemidef, act, msqrt_transpose, msqrt_mul_relStep hS] at this
  refine ⟨hstep, hiff, fun K' hK' hR' => ?_⟩
  ext M
  constructor
  · intro hM
    have hMpd : M.PosDef := hK'.1 hM
    have h1 : stepLE K' 1 M := ⟨Matrix.PosDef.one, hMpd, by rwa [relStep_one_left]⟩
    exact ⟨hMpd, (hR' 1 M Matrix.PosDef.one hMpd).2 h1⟩
  · rintro ⟨hMpd, h⟩
    have := ((hR' 1 M Matrix.PosDef.one hMpd).1 h).2.2
    rwa [relStep_one_left] at this

/-- **The reversed step**: for `Σ, Σ' ∈ PD(d)`, `Σ' ≤_𝒦 Σ` if and only if `M⁻¹ ∈ 𝒦`, `M` the
relative step of `(Σ, Σ')` (through the factor `Σ^{1/2}M^{1/2}` of `Σ'`). -/
theorem stepLE_symm_iff (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) : stepLE K S' S ↔ (relStep S S')⁻¹ ∈ K := by
  set M := relStep S S' with hMdef
  have hM : M.PosDef := (posDef_relStep_iff hS S').2 hS'
  have hUM : IsUnit (msqrt M).det := msqrt_mem_glSet hM
  have hUS : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  have hfac : msqrt S * msqrt M * (msqrt S * msqrt M)ᵀ = S' := by
    rw [transpose_mul, msqrt_transpose, msqrt_transpose]
    calc msqrt S * msqrt M * (msqrt M * msqrt S) = msqrt S * (msqrt M * msqrt M) * msqrt S := by
          simp only [Matrix.mul_assoc]
      _ = S' := by rw [msqrt_mul_self hM.posSemidef, hMdef, msqrt_mul_relStep hS]
  rw [stepLE_iff_factor hd hK hS' hS _ (by
      change IsUnit (msqrt S * msqrt M).det; rw [det_mul]; exact hUS.mul hUM) hfac]
  have h : (msqrt S * msqrt M)⁻¹ * S * ((msqrt S * msqrt M)⁻¹)ᵀ = M⁻¹ := by
    rw [Matrix.mul_inv_rev, transpose_mul, msqrt_inv_transpose, msqrt_inv_transpose]
    calc (msqrt M)⁻¹ * (msqrt S)⁻¹ * S * ((msqrt S)⁻¹ * (msqrt M)⁻¹)
        = (msqrt M)⁻¹ * ((msqrt S)⁻¹ * S * (msqrt S)⁻¹) * (msqrt M)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (msqrt M)⁻¹ * (msqrt M)⁻¹ := by
          rw [show (msqrt S)⁻¹ * S * (msqrt S)⁻¹ = relStep S S from rfl, relStep_self hS,
            Matrix.mul_one]
      _ = (msqrt M * msqrt M)⁻¹ := (Matrix.mul_inv_rev _ _).symm
      _ = M⁻¹ := by rw [msqrt_mul_self hM.posSemidef]
  rw [h]

/-! ## Clause (2): order properties -/

/-- The inverse of an invertible matrix is continuous at it. -/
theorem continuousAt_inv_of_isUnit {A : Mat d} (hA : IsUnit A.det) : ContinuousAt Inv.inv A := by
  refine continuousAt_matrix_inv A ?_
  have h : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext fun x => Ring.inverse_eq_inv x
  rw [h]
  exact continuousAt_inv₀ hA.ne_zero

/-- **`prop:invariant-orders`(2)**: `≤_𝒦` is reflexive if and only if `I ∈ 𝒦`; antisymmetric if
and only if no `M ≠ I` has both `M` and `M⁻¹` in `𝒦`; closed in `PD(d) × PD(d)` if and only if
`𝒦` is closed in `PD(d)`. -/
theorem stepLE_order_props (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) :
    ((∀ S : Mat d, S.PosDef → stepLE K S S) ↔ (1 : Mat d) ∈ K) ∧
      ((∀ S S' : Mat d, S.PosDef → S'.PosDef → stepLE K S S' → stepLE K S' S → S = S') ↔
        ∀ M ∈ K, M⁻¹ ∈ K → M = 1) ∧
      (closure {p : Mat d × Mat d | stepLE K p.1 p.2} ∩ (pdSet d ×ˢ pdSet d) ⊆
          {p : Mat d × Mat d | stepLE K p.1 p.2} ↔
        closure K ∩ pdSet d ⊆ K) := by
  have h1K : ∀ N ∈ K, stepLE K 1 N := fun N hN =>
    ⟨Matrix.PosDef.one, hK.1 hN, by rwa [relStep_one_left]⟩
  refine ⟨⟨fun h => ?_, fun h S hS => ⟨hS, hS, by rw [relStep_self hS]; exact h⟩⟩,
    ⟨fun h M hM hMi => ?_, fun h S S' hS hS' h₁ h₂ => ?_⟩, ⟨fun h M hM => ?_, fun h p hp => ?_⟩⟩
  · have := (h 1 Matrix.PosDef.one).2.2
    rwa [relStep_one_left] at this
  · have hMpd := hK.1 hM
    have h₂ : stepLE K M 1 :=
      (stepLE_symm_iff hd hK Matrix.PosDef.one hMpd).2 (by rwa [relStep_one_left])
    exact (h 1 M Matrix.PosDef.one hMpd (h1K M hM) h₂).symm
  · have hM := h _ h₁.2.2 ((stepLE_symm_iff hd hK hS hS').1 h₂)
    exact (relStep_injective hS (hM.trans (relStep_self hS).symm)).symm
  · obtain ⟨hMc, hMpd⟩ := hM
    have hc : ((1 : Mat d), M) ∈ closure {p : Mat d × Mat d | stepLE K p.1 p.2} :=
      map_mem_closure (continuous_const.prodMk continuous_id) hMc fun N hN => h1K N hN
    have := (h ⟨hc, Matrix.PosDef.one, hMpd⟩).2.2
    rwa [relStep_one_left] at this
  · obtain ⟨hpc, hp1, hp2⟩ := hp
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hpc
    have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hlim
    have h2 : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hlim
    have hsq := tendsto_msqrt (fun n => (hu n).1.posSemidef) h1
    have hinv : Tendsto (fun n => (msqrt (u n).1)⁻¹) atTop (𝓝 (msqrt p.1)⁻¹) :=
      (continuousAt_inv_of_isUnit (msqrt_mem_glSet hp1)).tendsto.comp hsq
    have hstep : Tendsto (fun n => relStep (u n).1 (u n).2) atTop (𝓝 (relStep p.1 p.2)) :=
      (hinv.mul h2).mul hinv
    have hMc : relStep p.1 p.2 ∈ closure K :=
      mem_closure_of_tendsto hstep (Eventually.of_forall fun n => (hu n).2.2)
    exact ⟨hp1, hp2, h ⟨hMc, (posDef_relStep_iff hp1 p.2).2 hp2⟩⟩

/-! ## Clause (3): how steps compose -/

/-- **`prop:invariant-orders`(3)**, how steps compose: if `Σ ≤_𝒦 Σ' ≤_𝒦 Σ''` with relative steps
`M` and `N`, the relative step of `(Σ, Σ'')` is `M^{1/2} N' M^{1/2}` with `N' = QᵀNQ`,
`Q ∈ O(d)`, and its eigenvalues are those of `MN'`. -/
theorem stepLE_compose (_hd : 1 ≤ d) {K : Set (Mat d)} (_hK : IsStepSet K) {S S' S'' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (_hS'' : S''.PosDef) (_h₁ : stepLE K S S')
    (_h₂ : stepLE K S' S'') :
    ∃ Q ∈ orthSet d,
      relStep S S'' = msqrt (relStep S S') * (Qᵀ * relStep S' S'' * Q) * msqrt (relStep S S') ∧
        (relStep S S'').charpoly = (relStep S S' * (Qᵀ * relStep S' S'' * Q)).charpoly := by
  set M := relStep S S' with hMdef
  set N := relStep S' S'' with hNdef
  have hM : M.PosDef := (posDef_relStep_iff hS S').2 hS'
  set A := msqrt S * msqrt M with hAdef
  have hAA : A * Aᵀ = S' := by
    rw [hAdef, transpose_mul, msqrt_transpose, msqrt_transpose]
    calc msqrt S * msqrt M * (msqrt M * msqrt S) = msqrt S * (msqrt M * msqrt M) * msqrt S := by
          simp only [Matrix.mul_assoc]
      _ = S' := by rw [msqrt_mul_self hM.posSemidef, hMdef, msqrt_mul_relStep hS]
  have hQ := msqrt_inv_mul_mem_orthSet hS' hAA
  set Q := (msqrt S')⁻¹ * A with hQdef
  have hQQ := orth_mul_transpose hQ
  -- `Σ'^{1/2} = AQᵀ = QAᵀ`
  have hA : A = msqrt S' * Q := by
    rw [hQdef, ← Matrix.mul_assoc, msqrt_mul_inv hS', Matrix.one_mul]
  have hS'1 : msqrt S' = A * Qᵀ := by rw [hA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hS'2 : msqrt S' = Q * Aᵀ := by
    rw [← msqrt_transpose S', hS'1, transpose_mul, transpose_transpose]
  have hrel : relStep S S'' = msqrt M * (Qᵀ * N * Q) * msqrt M := by
    have hS'' : S'' = msqrt S' * N * msqrt S' := (msqrt_mul_relStep hS' S'').symm
    have hl : (msqrt S)⁻¹ * A = msqrt M := by
      rw [hAdef, ← Matrix.mul_assoc, msqrt_inv_mul hS, Matrix.one_mul]
    have hr : Aᵀ * (msqrt S)⁻¹ = msqrt M := by
      rw [hAdef, transpose_mul, msqrt_transpose, msqrt_transpose, Matrix.mul_assoc,
        msqrt_mul_inv hS, Matrix.mul_one]
    rw [relStep, hS'']
    conv_lhs => rw [show msqrt S' * N * msqrt S' = A * Qᵀ * N * (Q * Aᵀ) by
      rw [← hS'1, ← hS'2]]
    calc (msqrt S)⁻¹ * (A * Qᵀ * N * (Q * Aᵀ)) * (msqrt S)⁻¹
        = ((msqrt S)⁻¹ * A) * (Qᵀ * N * Q) * (Aᵀ * (msqrt S)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = msqrt M * (Qᵀ * N * Q) * msqrt M := by rw [hl, hr]
  refine ⟨Q, hQ, hrel, ?_⟩
  rw [hrel, charpoly_mul_comm, ← Matrix.mul_assoc, msqrt_mul_self hM.posSemidef]

/-- **`prop:invariant-orders`(3)**, conversely: for `M, N ∈ 𝒦` the triple `I`, `M`,
`M^{1/2} N M^{1/2}` is such a chain. -/
theorem stepLE_chain_of_mem (_hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) {M N : Mat d}
    (hM : M ∈ K) (hN : N ∈ K) :
    stepLE K 1 M ∧ stepLE K M (msqrt M * N * msqrt M) := by
  have hMpd := hK.1 hM
  have hNpd := hK.1 hN
  refine ⟨⟨Matrix.PosDef.one, hMpd, by rwa [relStep_one_left]⟩, hMpd, ?_, ?_⟩
  · have := (posDef_act_iff (msqrt_mem_glSet hMpd) N).2 hNpd
    rwa [act, msqrt_transpose] at this
  · rwa [relStep_msqrt_mul hMpd]

/-- **`prop:invariant-orders`(3)**: `≤_𝒦` is transitive if and only if `M^{1/2}NM^{1/2} ∈ 𝒦` for
all `M, N ∈ 𝒦`, if and only if `𝒮_𝒦` is closed under products. -/
theorem stepLE_trans_tfae (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) :
    List.TFAE
      [∀ S S' S'' : Mat d, S.PosDef → S'.PosDef → S''.PosDef →
          stepLE K S S' → stepLE K S' S'' → stepLE K S S'',
        ∀ M ∈ K, ∀ N ∈ K, msqrt M * N * msqrt M ∈ K,
        ∀ A ∈ stepSemigroup K, ∀ B ∈ stepSemigroup K, A * B ∈ stepSemigroup K] := by
  tfae_have 1 → 2 := by
    intro h M hM N hN
    obtain ⟨h1, h2⟩ := stepLE_chain_of_mem hd hK hM hN
    have := (h _ _ _ Matrix.PosDef.one h1.2.1 h2.2.1 h1 h2).2.2
    rwa [relStep_one_left] at this
  tfae_have 2 → 1 := by
    intro h S S' S'' hS hS' hS'' h₁ h₂
    obtain ⟨Q, hQ, hrel, -⟩ := stepLE_compose hd hK hS hS' hS'' h₁ h₂
    refine ⟨hS, hS'', ?_⟩
    rw [hrel]
    exact h _ h₁.2.2 _ ((hK.conj_iff hQ _).2 h₂.2.2)
  tfae_have 2 → 3 := by
    intro h A hA B hB
    obtain ⟨hAgl, hAK⟩ := hA
    obtain ⟨hBgl, hBK⟩ := hB
    set M := A * Aᵀ with hMdef
    have hMpd := hK.1 hAK
    have hQ := msqrt_inv_mul_mem_orthSet hMpd hMdef.symm
    set Q := (msqrt M)⁻¹ * A with hQdef
    have hA' : A = msqrt M * Q := by
      rw [hQdef, ← Matrix.mul_assoc, msqrt_mul_inv hMpd, Matrix.one_mul]
    refine ⟨?_, ?_⟩
    · change IsUnit (A * B).det
      rw [det_mul]
      exact IsUnit.mul hAgl hBgl
    · have hN : Q * (B * Bᵀ) * Qᵀ ∈ K := hK.2 _ hBK Q hQ
      have := h M hAK _ hN
      convert this using 1
      rw [transpose_mul, hA', transpose_mul, msqrt_transpose]
      simp only [Matrix.mul_assoc]
  tfae_have 3 → 2 := by
    intro h M hM N hN
    have hMpd := hK.1 hM
    have hNpd := hK.1 hN
    have hsM : msqrt M ∈ stepSemigroup K :=
      ⟨msqrt_mem_glSet hMpd, by rwa [msqrt_transpose, msqrt_mul_self hMpd.posSemidef]⟩
    have hsN : msqrt N ∈ stepSemigroup K :=
      ⟨msqrt_mem_glSet hNpd, by rwa [msqrt_transpose, msqrt_mul_self hNpd.posSemidef]⟩
    have := (h _ hsM _ hsN).2
    rw [transpose_mul, msqrt_transpose, msqrt_transpose] at this
    have e : msqrt M * N * msqrt M = msqrt M * msqrt N * (msqrt N * msqrt M) := by
      conv_lhs => rw [← msqrt_mul_self hNpd.posSemidef]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact this
  tfae_finish

/-- `(diag(4,1))^{1/2} = diag(2,1)`. -/
theorem msqrt_diag_four_one : msqrt (diagonal ![4, 1] : Mat 2) = diagonal ![2, 1] := by
  refine CFC.sqrt_unique ?_ (nonneg_of_posSemidef (Matrix.PosSemidef.diagonal ?_))
  · rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

/-- **`prop:invariant-orders`(3)**, the example: for `d = 2` the step `diag(4,1)` followed by
`diag(4,1)` gives `diag(16,1)`, and followed by `diag(1,4)` gives `4I`. -/
theorem step_composite_example :
    msqrt (diagonal ![4, 1] : Mat 2) * diagonal ![4, 1] * msqrt (diagonal ![4, 1]) =
        diagonal ![16, 1] ∧
      msqrt (diagonal ![4, 1] : Mat 2) * diagonal ![1, 4] * msqrt (diagonal ![4, 1]) =
        (4 : ℝ) • (1 : Mat 2) := by
  rw [msqrt_diag_four_one, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    fin_cases i <;> norm_num
  · rw [smul_one_eq_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num

/-! ## Clause (4): the infinitesimal cone -/

open scoped Norms.Operator in
/-- The matrix exponential is continuous. Mathlib types only. -/
theorem continuous_mexp : Continuous (mexp : Mat d → Mat d) := by
  unfold mexp
  exact NormedSpace.exp_continuous

/-- `e^{QXQᵀ} = Qe^XQᵀ` for `Q ∈ O(d)`. -/
theorem mexp_conj_orth {Q : Mat d} (hQ : Q ∈ orthSet d) (X : Mat d) :
    mexp (Q * X * Qᵀ) = Q * mexp X * Qᵀ := by
  have hinv : Q⁻¹ = Qᵀ := Matrix.inv_eq_right_inv (orth_mul_transpose hQ)
  have hU : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (orthSet_subset_glSet hQ)
  unfold mexp
  rw [← hinv, Matrix.exp_conj Q X hU]

theorem isHermitian_of_isSymm {X : Mat d} (hX : X.IsSymm) : X.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hX

/-- `e^X ∈ PD(d)` for `X ∈ Sym(d)`. -/
theorem posDef_mexp {X : Mat d} (hX : X.IsSymm) : (mexp X).PosDef := by
  obtain ⟨U, x, hUU, hXU⟩ := exists_udiag (isHermitian_of_isSymm hX)
  rw [hXU, mexp_udiag hUU]
  exact (udiag_posDef_iff hUU _).2 fun i => Real.exp_pos _

/-- **The exponential is injective at `0` on `Sym(d)`**: `e^X = I` forces `X = 0`. -/
theorem eq_zero_of_mexp_eq_one {X : Mat d} (hX : X.IsSymm) (h : mexp X = 1) : X = 0 := by
  obtain ⟨U, x, hUU, hXU⟩ := exists_udiag (isHermitian_of_isSymm hX)
  rw [hXU, mexp_udiag hUU, ← udiag_one hUU] at h
  have hx := udiag_injective hUU h
  have hx0 : x = 0 := funext fun i => by
    have := congrFun hx i
    simpa using this
  rw [hXU, hx0, udiag, show (0 : Fin d → ℝ) = fun _ => 0 from rfl, diagonal_zero, Matrix.mul_zero,
    Matrix.zero_mul]

/-- **`prop:invariant-orders`(4)**, the infinitesimal cone: `C(𝒦)` is invariant under
`X ↦ QXQᵀ`, `Q ∈ O(d)`, and under `X ↦ cX`, `c ≥ 0`; it is closed when `𝒦` is closed in `PD(d)`;
and if `≤_𝒦` is antisymmetric, `X, -X ∈ C(𝒦)` only for `X = 0`. -/
theorem infCone_props (_hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K) :
    IsOrthInvariant (infCone K) ∧ (∀ c : ℝ, 0 ≤ c → ∀ X ∈ infCone K, c • X ∈ infCone K) ∧
      (closure K ∩ pdSet d ⊆ K → IsClosed (infCone K)) ∧
      ((∀ S S' : Mat d, S.PosDef → S'.PosDef → stepLE K S S' → stepLE K S' S → S = S') →
        ∀ X ∈ infCone K, -X ∈ infCone K → X = 0) := by
  refine ⟨fun Q hQ X hX => ⟨?_, fun t ht => ?_⟩, fun c hc X hX => ⟨?_, fun t ht => ?_⟩,
    fun hKc => ?_, fun hanti X hX hXn => ?_⟩
  · have hs : X.IsSymm := hX.1
    unfold Matrix.IsSymm at hs ⊢
    rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc]
  · rw [show t • (Q * X * Qᵀ) = Q * (t • X) * Qᵀ by
      rw [Matrix.mul_smul, Matrix.smul_mul], mexp_conj_orth hQ]
    exact hK.2 _ (hX.2 t ht) Q hQ
  · have hs : X.IsSymm := hX.1
    unfold Matrix.IsSymm at hs ⊢
    rw [transpose_smul, hs]
  · rw [smul_smul]
    exact hX.2 _ (mul_nonneg ht hc)
  · -- `C(𝒦) = Sym(d) ∩ ⋂_{t ≥ 0} {X : e^{tX} ∈ closure 𝒦}`
    have h : infCone K = {X : Mat d | Xᵀ = X} ∩
        ⋂ t : Set.Ici (0 : ℝ), {X : Mat d | mexp ((t : ℝ) • X) ∈ closure K} := by
      ext X
      simp only [infCone, mem_setOf_eq, mem_inter_iff, mem_iInter, Subtype.forall, mem_Ici]
      constructor
      · rintro ⟨hs, h⟩
        exact ⟨hs, fun t ht => subset_closure (h t ht)⟩
      · rintro ⟨hs, h⟩
        refine ⟨hs, fun t ht => hKc ⟨h t ht, posDef_mexp ?_⟩⟩
        unfold Matrix.IsSymm
        rw [transpose_smul, hs]
    rw [h]
    refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun t => ?_)
    exact isClosed_closure.preimage (continuous_mexp.comp (continuous_const_smul _))
  · have h1 : mexp X ∈ K := by simpa using hX.2 1 zero_le_one
    have h2 : mexp (-X) ∈ K := by simpa using hXn.2 1 zero_le_one
    have hpd := hK.1 h1
    have hle1 : stepLE K 1 (mexp X) := ⟨Matrix.PosDef.one, hpd, by rwa [relStep_one_left]⟩
    have hle2 : stepLE K (mexp X) 1 := by
      refine ⟨hpd, Matrix.PosDef.one, ?_⟩
      rw [relStep_one_right hpd]
      unfold mexp at h2 ⊢
      rwa [← Matrix.exp_neg]
    exact eq_zero_of_mexp_eq_one hX.1 (hanti _ _ Matrix.PosDef.one hpd hle1 hle2).symm

end AffineHemigroup
