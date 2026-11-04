/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KyFan
import AffineHemigroup.SpectralProducts
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.Order.Rearrangement

/-!
# `lem:spectral-cones`(3)–(5): symmetric cones, invariant cones, exponentials

Blueprint: `blueprint/src/parts/05-wedges.tex`, `lem:spectral-cones` (wave 2, group F, Q-0281).
Clause (3): a permutation-symmetric closed convex cone `D ⊆ ℝ^d` is cut out by the functionals
`x ↦ ∑ᵢ w↓ᵢ x↑ᵢ`, `w ∈ D^#` (a separating functional from Mathlib's Hahn–Banach theorem, the
rearrangement inequality from Mathlib's `Antivary.sum_smul_le_sum_smul_comp_perm`), and is closed
under majorization (Abel summation). Clause (4): `C_D` is a closed convex cone, invariant under
`O(d)` (closed through the continuity of `λ↑` from clause (1), convex through `λ↑(X + Y) ≺
λ↑(X) + λ↑(Y)`), every invariant cone is `C_D` for `D = {x : diag(x) ∈ C}`, and a pointed one
has `I` or `-I` (the average over the cyclic shifts of a spectrum, in place of the sum over all
`d!` permutations). Clause (5): `exp C_D = {M : ℓ(M) ∈ D}`, a closed step set, closed under
`M^{1/2}NM^{1/2}`; the last needs `lem:spectral-cones-products`, hence ledger A9.
-/

namespace AffineHemigroup

open Matrix Filter Set
open scoped Topology

variable {d : ℕ}

/-! ## Cones in `ℝ^d` -/

theorem IsClosedConvexCone.add_mem {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {C : Set V} (hC : IsClosedConvexCone C) {x y : V} (hx : x ∈ C) (hy : y ∈ C) : x + y ∈ C := by
  have h := hC.2.1 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h2 := hC.2.2.2 2 (by norm_num) _ h
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at h2

theorem IsClosedConvexCone.sum_mem {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {C : Set V} (hC : IsClosedConvexCone C) {ι : Type*} (s : Finset ι) {f : ι → V}
    (hf : ∀ i ∈ s, f i ∈ C) : ∑ i ∈ s, f i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC.2.2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hC.add_mem (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- In a symmetric set, `x ∈ D ↔ x↑ ∈ D`. -/
theorem IsPermSymmetric.mem_sortUp_iff {D : Set (Fin d → ℝ)} (hsym : IsPermSymmetric D)
    (x : Fin d → ℝ) : sortUp x ∈ D ↔ x ∈ D := by
  obtain ⟨σ, hσ⟩ := exists_perm_sortUp x
  rw [hσ]
  refine ⟨fun h => ?_, fun h => hsym σ x h⟩
  have := hsym σ⁻¹ _ h
  simpa [Function.comp_assoc] using this

/-! ## Clause (3): the dual description -/

/-- **The rearrangement inequality**: `∑ᵢ w↓ᵢ x↑ᵢ ≤ ∑ᵢ wᵢxᵢ`. -/
theorem sum_sortDown_mul_sortUp_le (w x : Fin d → ℝ) :
    ∑ i, sortDown w i * sortUp x i ≤ ∑ i, w i * x i := by
  have hanti : Antitone (sortDown w) := fun i j hij =>
    sortUp_monotone w (Fin.rev_le_rev.2 hij)
  have hav : Antivary (sortDown w) (sortUp x) := hanti.antivary (sortUp_monotone x)
  have h := hav.sum_smul_le_sum_smul_comp_perm
    (σ := (Fin.revPerm.trans (Tuple.sort w)).trans (Tuple.sort x).symm)
  simp only [smul_eq_mul] at h
  have hr : ∑ i, sortDown w i *
      sortUp x (((Fin.revPerm.trans (Tuple.sort w)).trans (Tuple.sort x).symm) i) =
      ∑ i, w i * x i := by
    have := Equiv.sum_comp (Fin.revPerm.trans (Tuple.sort w)) (fun j => w j * x j)
    simpa [sortDown, sortUp] using this
  linarith

/-- `∑ᵢ w↓ᵢ x↑ᵢ` is a pairing of `w` with a rearrangement of `x`. -/
theorem exists_perm_sum_sortDown_mul_sortUp (w x : Fin d → ℝ) :
    ∃ σ : Equiv.Perm (Fin d), ∑ i, sortDown w i * sortUp x i = ∑ j, w j * (x ∘ σ) j := by
  set π := Fin.revPerm.trans (Tuple.sort w)
  refine ⟨π.symm.trans (Tuple.sort x), ?_⟩
  have := Equiv.sum_comp π (fun j => w j * x ((Tuple.sort x) (π.symm j)))
  simp only [Equiv.symm_apply_apply] at this
  calc ∑ i, sortDown w i * sortUp x i = ∑ i, w (π i) * x ((Tuple.sort x) i) := by
        simp [sortDown, sortUp, π]
    _ = _ := this

/-- **A separating functional**: for a closed convex cone `D` and `x ∉ D` there is `w ∈ D^#` with
`⟨w, x⟩ < 0` (Hahn–Banach). -/
theorem exists_dual_of_notMem {D : Set (Fin d → ℝ)} (hD : IsClosedConvexCone D)
    {x : Fin d → ℝ} (hx : x ∉ D) : ∃ w ∈ dualCone D, ∑ i, w i * x i < 0 := by
  obtain ⟨f, u, hfx, hfD⟩ := geometric_hahn_banach_point_closed hD.2.1 hD.1 hx
  have hu : u < 0 := by simpa using hfD 0 hD.2.2.1
  set w : Fin d → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hw
  have hf : ∀ y : Fin d → ℝ, f y = ∑ i, w i * y i := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨w, fun b hb => ?_, by rw [← hf]; linarith⟩
  rw [← hf]
  by_contra hneg'
  have hneg := not_le.1 hneg'
  have hc : 0 < u / f b := div_pos_of_neg_of_neg hu hneg
  have h1 := hfD _ (hD.2.2.2 _ hc.le b hb)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at h1
  exact lt_irrefl _ h1

/-- **`lem:spectral-cones`(3)**, the dual description: for a symmetric closed convex cone
`D ⊆ ℝ^d`, `x ∈ D` if and only if `∑ᵢ w↓ᵢ x↑ᵢ ≥ 0` for every `w ∈ D^#`. -/
theorem symCone_mem_iff (_hd : 1 ≤ d) {D : Set (Fin d → ℝ)} (hsym : IsPermSymmetric D)
    (hD : IsClosedConvexCone D) (x : Fin d → ℝ) :
    x ∈ D ↔ ∀ w ∈ dualCone D, 0 ≤ ∑ i, sortDown w i * sortUp x i := by
  refine ⟨fun hx w hw => ?_, fun h => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_sum_sortDown_mul_sortUp w x
    rw [hσ]
    exact hw _ (hsym σ x hx)
  · by_contra hx
    obtain ⟨w, hw, hwx⟩ := exists_dual_of_notMem hD hx
    have := sum_sortDown_mul_sortUp_le w x
    linarith [h w hw]

/-- **Abel summation**, on `ℕ`. -/
theorem sum_range_mul_abel (A E : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range m, A n * E n =
      ∑ n ∈ Finset.range m, (A n - A (n + 1)) * ∑ j ∈ Finset.range (n + 1), E j +
        A m * ∑ j ∈ Finset.range m, E j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun n => (A n - A (n + 1)) *
      ∑ j ∈ Finset.range (n + 1), E j), Finset.sum_range_succ (fun j => E j) m]
    ring

/-- **Abel summation against a decreasing sequence**: if the partial sums of `e` are nonnegative
and its total is `0`, then `∑ᵢ aᵢeᵢ ≥ 0` for `a` decreasing. -/
theorem sum_antitone_mul_nonneg {a e : Fin d → ℝ} (ha : Antitone a)
    (hS : ∀ k : ℕ, k < d → 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), e i)
    (htot : ∑ i, e i = 0) : 0 ≤ ∑ i, a i * e i := by
  set A : ℕ → ℝ := fun n => if h : n < d then a ⟨n, h⟩ else 0 with hA
  set E : ℕ → ℝ := fun n => if h : n < d then e ⟨n, h⟩ else 0 with hE
  have hsum : ∑ i, a i * e i = ∑ n ∈ Finset.range d, A n * E n := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => A n * E n)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hA, hE, i.2]
  have hpart : ∀ k, k ≤ d →
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), e i = ∑ n ∈ Finset.range k, E n := by
    intro k hk
    rw [Finset.sum_filter]
    have h1 : ∑ i : Fin d, (if i.val < k then e i else 0) =
        ∑ n ∈ Finset.range d, (if n < k then E n else 0) := by
      rw [← Fin.sum_univ_eq_sum_range (fun n => if n < k then E n else 0)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hE, i.2]
    rw [h1, ← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hEd : ∑ j ∈ Finset.range d, E j = 0 := by
    rw [← hpart d le_rfl, ← htot]
    congr 1
    ext i
    simp
  rw [hsum, sum_range_mul_abel A E d, hEd, mul_zero, add_zero]
  refine Finset.sum_nonneg fun n hn => ?_
  rw [Finset.mem_range] at hn
  by_cases hn1 : n + 1 < d
  · have hAn : A (n + 1) ≤ A n := by
      simp only [hA, dif_pos hn, dif_pos hn1]
      exact ha (Fin.le_def.2 (by simp))
    have hS' : 0 ≤ ∑ j ∈ Finset.range (n + 1), E j := by
      rw [← hpart (n + 1) hn1.le]
      exact hS (n + 1) hn1
    exact mul_nonneg (by linarith) hS'
  · have h' : n + 1 = d := by omega
    rw [h', hEd, mul_zero]

/-- **Majorization raises every `F_w`**: `x ≺ y` gives `∑ᵢ w↓ᵢ y↑ᵢ ≤ ∑ᵢ w↓ᵢ x↑ᵢ`. -/
theorem sum_sortDown_mul_sortUp_mono {x y : Fin d → ℝ} (hxy : IsMajorized x y) (w : Fin d → ℝ) :
    ∑ i, sortDown w i * sortUp y i ≤ ∑ i, sortDown w i * sortUp x i := by
  have hanti : Antitone (sortDown w) := fun i j hij =>
    sortUp_monotone w (Fin.rev_le_rev.2 hij)
  have h := sum_antitone_mul_nonneg (e := sortUp x - sortUp y) hanti (fun k hk => ?_) ?_
  · have : ∑ i, sortDown w i * (sortUp x - sortUp y) i =
        ∑ i, sortDown w i * sortUp x i - ∑ i, sortDown w i * sortUp y i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    linarith
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · have := hxy.1 k hpos hk
      rw [partialSumUp, partialSumUp] at this
      linarith
  · have := hxy.2
    rw [partialSumUp_card, partialSumUp_card, ← sum_sortUp x, ← sum_sortUp y] at this
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, this, sub_self]

/-- **`lem:spectral-cones`(3)**, consequently: `y ∈ D` and `x ≺ y` imply `x ∈ D`. -/
theorem symCone_majorization (hd : 1 ≤ d) {D : Set (Fin d → ℝ)} (hsym : IsPermSymmetric D)
    (hD : IsClosedConvexCone D) {x y : Fin d → ℝ} (hy : y ∈ D) (hxy : IsMajorized x y) :
    x ∈ D := by
  refine (symCone_mem_iff hd hsym hD x).2 fun w hw => ?_
  exact ((symCone_mem_iff hd hsym hD y).1 hy w hw).trans (sum_sortDown_mul_sortUp_mono hxy w)

/-! ## Clause (4): cones in `Sym(d)` and in eigenvalue space -/

theorem mem_orthSet_of {Q : Mat d} (h : Q * Qᵀ = 1) : Q ∈ orthSet d :=
  (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 h

theorem isSymm_of_isHermitian {X : Mat d} (hX : X.IsHermitian) : X.IsSymm := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at hX
  exact hX

theorem isClosed_symSet : IsClosed (symSet d) := by
  have : symSet d = {X : Mat d | Xᵀ = X} := rfl
  rw [this]
  exact isClosed_eq (Continuous.matrix_transpose continuous_id) continuous_id

/-- `λ↑(X) ∈ D`, `D` closed, passes to limits of symmetric matrices. -/
theorem isClosed_specCone {D : Set (Fin d → ℝ)} (hD : IsClosed D) : IsClosed (specCone D) := by
  refine isClosed_of_closure_subset fun X hX => ?_
  obtain ⟨Xs, hXs, hlim⟩ := mem_closure_iff_seq_limit.1 hX
  have hsymX : X.IsSymm := isClosed_symSet.mem_of_tendsto hlim
    (Eventually.of_forall fun n => (hXs n).1)
  exact ⟨hsymX, hD.mem_of_tendsto (tendsto_eigUp (fun n => (hXs n).1) hsymX hlim)
    (Eventually.of_forall fun n => (hXs n).2)⟩

/-- **`lem:spectral-cones`(4)**: for a symmetric closed convex cone `D`, `C_D` is a closed convex
cone invariant under orthogonal conjugation. -/
theorem specCone_isClosedConvexCone (hd : 1 ≤ d) {D : Set (Fin d → ℝ)}
    (hsym : IsPermSymmetric D) (hD : IsClosedConvexCone D) :
    IsClosedConvexCone (specCone D) ∧ IsOrthInvariant (specCone D) := by
  have hsmul : ∀ c : ℝ, 0 ≤ c → ∀ X ∈ specCone D, c • X ∈ specCone D := by
    rintro c hc X ⟨hX, hXD⟩
    refine ⟨hX.smul c, ?_⟩
    rw [eigUp_smul hc (isHermitian_of_isSymm hX)]
    exact hD.2.2.2 c hc _ hXD
  refine ⟨⟨isClosed_specCone hD.1, ?_, ⟨isSymm_zero, by rw [eigUp_zero]; exact hD.2.2.1⟩,
    hsmul⟩, ?_⟩
  · intro X hX Y hY a b ha hb _
    have hX' := hsmul a ha X hX
    have hY' := hsmul b hb Y hY
    refine ⟨hX'.1.add hY'.1, ?_⟩
    exact symCone_majorization hd hsym hD (hD.add_mem hX'.2 hY'.2)
      (eigUp_add_majorized hd hX'.1 hY'.1)
  · rintro Q hQ X ⟨hX, hXD⟩
    refine ⟨?_, by rwa [eigUp_conj_orth (orth_mul_transpose hQ)]⟩
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hX.eq, Matrix.mul_assoc]

/-- `diag(x ∘ σ) = P_σ diag(x) P_σᵀ` with `P_σ ∈ O(d)`. -/
theorem diagonal_comp_perm_mem {C : Set (Mat d)} (hO : IsOrthInvariant C) {x : Fin d → ℝ}
    (hx : diagonal x ∈ C) (σ : Equiv.Perm (Fin d)) : diagonal (x ∘ σ) ∈ C := by
  rw [← permMat_conj_diagonal]
  exact hO _ (mem_orthSet_of (permMat_mul_transpose σ)) _ hx

/-- For an invariant `C`: `X ∈ C ↔ diag(λ↑(X)) ∈ C`, for symmetric `X`. -/
theorem mem_iff_diagonal_eigUp {C : Set (Mat d)} (hO : IsOrthInvariant C) {X : Mat d}
    (hX : X.IsSymm) : X ∈ C ↔ diagonal (eigUp X) ∈ C := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hX)
  have hV' : Vᵀ * V = 1 := transpose_mul_self_of_mul_transpose hV
  constructor
  · intro h
    have h2 := hO Vᵀ (mem_orthSet_of (by rw [transpose_transpose]; exact hV')) X h
    rw [transpose_transpose] at h2
    have h3 : Vᵀ * X * V = diagonal (eigUp X) := by
      conv_lhs => rw [hXV]
      simp only [udiag, ← Matrix.mul_assoc, hV', Matrix.one_mul]
      rw [Matrix.mul_assoc, hV', Matrix.mul_one]
    rwa [h3] at h2
  · intro h
    have h2 := hO V (mem_orthSet_of hV) _ h
    rw [hXV]
    exact h2

theorem diagonal_zero' : diagonal (0 : Fin d → ℝ) = 0 := by
  ext i j
  simp [diagonal_apply]

theorem diagonal_neg' (x : Fin d → ℝ) : diagonal (-x) = -diagonal x := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem diagonal_lincomb (a b : ℝ) (x y : Fin d → ℝ) :
    diagonal (a • x + b • y) = a • diagonal x + b • diagonal y := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- **`lem:spectral-cones`(4)**: every closed convex cone `C ⊆ Sym(d)` invariant under orthogonal
conjugation is `C_D` for exactly one symmetric closed convex cone `D`, namely
`D = {x : diag(x) ∈ C}`, and `C ∩ (-C) = {0}` if and only if `D ∩ (-D) = {0}`. -/
theorem orthInvariant_cone_eq_specCone (_hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) :
    let D : Set (Fin d → ℝ) := {x | diagonal x ∈ C}
    IsPermSymmetric D ∧ IsClosedConvexCone D ∧ C = specCone D ∧
      (∀ D' : Set (Fin d → ℝ), IsPermSymmetric D' → IsClosedConvexCone D' → C = specCone D' →
        D' = D) ∧
      ((∀ X ∈ C, -X ∈ C → X = 0) ↔ ∀ x ∈ D, -x ∈ D → x = 0) := by
  intro D
  have hDsym : IsPermSymmetric D := fun σ x hx => diagonal_comp_perm_mem hO hx σ
  have hCD : C = specCone D := by
    ext X
    constructor
    · intro hX
      have hXs : X.IsSymm := hCsym hX
      exact ⟨hXs, (mem_iff_diagonal_eigUp hO hXs).1 hX⟩
    · rintro ⟨hXs, hXD⟩
      exact (mem_iff_diagonal_eigUp hO hXs).2 hXD
  refine ⟨hDsym, ⟨?_, ?_, ?_, ?_⟩, hCD, ?_, ?_⟩
  · exact hC.1.preimage (Continuous.matrix_diagonal continuous_id)
  · intro x hx y hy a b ha hb hab
    change diagonal (a • x + b • y) ∈ C
    rw [diagonal_lincomb]
    exact hC.2.1 hx hy ha hb hab
  · change diagonal 0 ∈ C
    rw [diagonal_zero']
    exact hC.2.2.1
  · intro c hc x hx
    change diagonal (c • x) ∈ C
    rw [diagonal_smul]
    exact hC.2.2.2 c hc _ hx
  · intro D' hD'sym _ hCD'
    ext x
    have hdx : (diagonal x).IsSymm := by rw [Matrix.IsSymm, diagonal_transpose]
    change x ∈ D' ↔ diagonal x ∈ C
    rw [hCD', ← hD'sym.mem_sortUp_iff]
    exact ⟨fun h => ⟨hdx, by rwa [eigUp_diagonal]⟩, fun h => by
      have := h.2; rwa [eigUp_diagonal] at this⟩
  · constructor
    · intro h x hx hnx
      have h1 : diagonal x = 0 := h _ hx (by
        change diagonal (-x) ∈ C at hnx
        rwa [diagonal_neg'] at hnx)
      funext i
      have := congrFun (congrFun h1 i) i
      simpa using this
    · intro h X hX hnX
      have hXs : X.IsSymm := hCsym hX
      obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hXs)
      have hx : eigUp X ∈ D := (mem_iff_diagonal_eigUp hO hXs).1 hX
      have hnXs : (-X).IsSymm := hXs.neg
      have hnx : eigUp (-X) ∈ D := (mem_iff_diagonal_eigUp hO hnXs).1 hnX
      have hneg : -X = udiag V (-eigUp X) := by
        conv_lhs => rw [hXV]
        rw [udiag, udiag, diagonal_neg', Matrix.mul_neg, Matrix.neg_mul]
      rw [hneg, eigUp_udiag hV, hDsym.mem_sortUp_iff] at hnx
      have h0 := h _ hx hnx
      rw [hXV, h0, udiag, diagonal_zero', Matrix.mul_zero, Matrix.zero_mul]

/-- **The average over cyclic shifts**: `∑ₘ x(· + m) = (∑ x) 𝟙`. -/
theorem sum_comp_addRight [NeZero d] (x : Fin d → ℝ) :
    ∑ m : Fin d, x ∘ Equiv.addRight m = fun _ => ∑ j, x j := by
  funext i
  rw [Finset.sum_apply]
  exact Equiv.sum_comp (Equiv.addLeft i) x

/-- The sign of a nonzero element of a pointed invariant cone: its trace is nonzero, and `I` or
`-I` lies in the cone according to that sign. -/
theorem orthInvariant_trace_sign [NeZero d] {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hpt : ∀ X ∈ C, -X ∈ C → X = 0)
    {X : Mat d} (hX : X ∈ C) (hX0 : X ≠ 0) :
    (0 < X.trace ∧ (1 : Mat d) ∈ C) ∨ (X.trace < 0 ∧ (-1 : Mat d) ∈ C) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  obtain ⟨hDsym, hDc, hCD, -, hpt'⟩ := orthInvariant_cone_eq_specCone hd hCsym hC hO
  set D : Set (Fin d → ℝ) := {x | diagonal x ∈ C}
  have hXs : X.IsSymm := hCsym hX
  set x := eigUp X
  have hx : x ∈ D := (mem_iff_diagonal_eigUp hO hXs).1 hX
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hXs)
    apply hX0
    rw [hXV, show eigUp X = 0 from h, udiag, diagonal_zero', Matrix.mul_zero, Matrix.zero_mul]
  have htr : X.trace = ∑ j, x j := (sum_eigUp (isHermitian_of_isSymm hXs)).symm
  have hsumD : (fun _ => ∑ j, x j : Fin d → ℝ) ∈ D := by
    rw [← sum_comp_addRight]
    exact hDc.sum_mem _ fun m _ => hDsym _ x hx
  have htr0 : X.trace ≠ 0 := by
    intro h0
    rw [htr] at h0
    have hsplit := Finset.add_sum_erase Finset.univ (fun m : Fin d => x ∘ Equiv.addRight m)
      (Finset.mem_univ 0)
    rw [sum_comp_addRight, h0] at hsplit
    have hx0' : x ∘ Equiv.addRight (0 : Fin d) = x := by funext i; simp
    rw [hx0'] at hsplit
    have hneg : -x = ∑ m ∈ Finset.univ.erase 0, x ∘ Equiv.addRight m := by
      rw [neg_eq_iff_add_eq_zero, hsplit]
      rfl
    have hnD : -x ∈ D := by
      rw [hneg]
      exact hDc.sum_mem _ fun m _ => hDsym _ x hx
    exact hx0 (hpt'.1 hpt x hx hnD)
  rcases lt_or_gt_of_ne htr0 with hneg | hpos
  · right
    refine ⟨hneg, ?_⟩
    have h1 := hDc.2.2.2 (-1 / X.trace) (div_nonneg_of_nonpos (by norm_num) hneg.le) _ hsumD
    have h2 : (-1 / X.trace) • (fun _ => ∑ j, x j : Fin d → ℝ) = fun _ => -1 := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, ← htr]
      field_simp
    rw [h2] at h1
    have h3 : diagonal (fun _ : Fin d => (-1 : ℝ)) = -1 := by
      rw [← diagonal_one, ← diagonal_neg']
      rfl
    change diagonal (fun _ => -1) ∈ C at h1
    rwa [h3] at h1
  · left
    refine ⟨hpos, ?_⟩
    have h1 := hDc.2.2.2 (1 / X.trace) (by positivity) _ hsumD
    have h2 : (1 / X.trace) • (fun _ => ∑ j, x j : Fin d → ℝ) = fun _ => 1 := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, ← htr]
      field_simp
    rw [h2] at h1
    change diagonal (fun _ => 1) ∈ C at h1
    rwa [diagonal_one] at h1

/-- **`lem:spectral-cones`(4)**, the last sentence: if moreover `C ≠ {0}` and `C ∩ (-C) = {0}`,
exactly one of `I` and `-I` lies in `C`, and `tr X` has that sign for every `X ∈ C ∖ {0}`. -/
theorem orthInvariant_pointed_cone_sign (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hne : C ≠ {0})
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) :
    Xor ((1 : Mat d) ∈ C) ((-1 : Mat d) ∈ C) ∧
      ((1 : Mat d) ∈ C → ∀ X ∈ C, X ≠ 0 → 0 < X.trace) ∧
      ((-1 : Mat d) ∈ C → ∀ X ∈ C, X ≠ 0 → X.trace < 0) := by
  haveI : NeZero d := ⟨by omega⟩
  have hnotboth : ¬ ((1 : Mat d) ∈ C ∧ (-1 : Mat d) ∈ C) := by
    rintro ⟨h1, h2⟩
    have := hpt 1 h1 h2
    exact one_ne_zero this
  obtain ⟨X, hX, hX0⟩ : ∃ X ∈ C, X ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    apply hne
    ext Y
    exact ⟨fun hY => h Y hY, fun hY => by rw [Set.mem_singleton_iff.1 hY]; exact hC.2.2.1⟩
  have hsign := fun {Y} (hY : Y ∈ C) (hY0 : Y ≠ 0) =>
    orthInvariant_trace_sign hCsym hC hO hpt hY hY0
  refine ⟨?_, fun h1 Y hY hY0 => ?_, fun h2 Y hY hY0 => ?_⟩
  · rcases hsign hX hX0 with ⟨-, h1⟩ | ⟨-, h2⟩
    · exact Or.inl ⟨h1, fun h2 => hnotboth ⟨h1, h2⟩⟩
    · exact Or.inr ⟨h2, fun h1 => hnotboth ⟨h1, h2⟩⟩
  · rcases hsign hY hY0 with ⟨h, -⟩ | ⟨-, h2⟩
    · exact h
    · exact absurd ⟨h1, h2⟩ hnotboth
  · rcases hsign hY hY0 with ⟨-, h1⟩ | ⟨h, -⟩
    · exact absurd ⟨h1, h2⟩ hnotboth
    · exact h

/-! ## Clause (5): exponentials -/

/-- `log M` is symmetric. -/
theorem mlog_isSymm (M : Mat d) : (mlog M).IsSymm := isSymm_of_isHermitian (mlog_isHermitian M)

/-- `exp C_D = {M ∈ PD(d) : ℓ(M) ∈ D}`. -/
theorem expSet_specCone_eq (D : Set (Fin d → ℝ)) :
    expSet (specCone D) = {M | M.PosDef ∧ logSpec M ∈ D} := by
  ext M
  constructor
  · rintro ⟨X, ⟨hX, hXD⟩, rfl⟩
    exact ⟨posDef_mexp hX, by rwa [logSpec_mexp (isHermitian_of_isSymm hX)]⟩
  · rintro ⟨hM, hMD⟩
    exact ⟨mlog M, ⟨mlog_isSymm M, hMD⟩, (mexp_mlog hM).symm⟩

/-- **`ℓ` is continuous on `PD(d)`**, read along sequences. -/
theorem tendsto_logSpec {Ms : ℕ → Mat d} {M : Mat d} (hMs : ∀ n, (Ms n).PosDef) (hM : M.PosDef)
    (h : Tendsto Ms atTop (𝓝 M)) : Tendsto (fun n => logSpec (Ms n)) atTop (𝓝 (logSpec M)) := by
  have he := tendsto_eigUp (fun n => isSymm_of_isHermitian (hMs n).isHermitian)
    (isSymm_of_isHermitian hM.isHermitian) h
  simp only [logSpec_eq hM, logSpec_eq (hMs _)]
  refine tendsto_pi_nhds.2 fun k => ?_
  exact ((Real.continuousAt_log (eigUp_pos hM k).ne').tendsto).comp
    ((continuous_apply k).continuousAt.tendsto.comp he)

/-- **`lem:spectral-cones`(5)**, exponentials: for `C = C_D` as in (4),
`exp C = {M ∈ PD(d) : ℓ(M) ∈ D}`; it is a step set, closed in `PD(d)`, and
`M^{1/2}NM^{1/2} ∈ exp C` whenever `M, N ∈ exp C`. -/
theorem expSet_specCone (hd : 1 ≤ d) {D : Set (Fin d → ℝ)} (hsym : IsPermSymmetric D)
    (hD : IsClosedConvexCone D) :
    expSet (specCone D) = {M | M.PosDef ∧ logSpec M ∈ D} ∧ IsStepSet (expSet (specCone D)) ∧
      closure (expSet (specCone D)) ∩ pdSet d ⊆ expSet (specCone D) ∧
      ∀ M ∈ expSet (specCone D), ∀ N ∈ expSet (specCone D),
        msqrt M * N * msqrt M ∈ expSet (specCone D) := by
  have heq := expSet_specCone_eq D
  have hinv := (specCone_isClosedConvexCone hd hsym hD).2
  refine ⟨heq, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [heq]; exact fun M hM => hM.1
  · rintro M ⟨X, hX, rfl⟩ Q hQ
    exact ⟨Q * X * Qᵀ, hinv Q hQ X hX, (mexp_conj_orth hQ X).symm⟩
  · rintro M ⟨hcl, hM⟩
    obtain ⟨Ms, hMs, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
    rw [heq] at hMs ⊢
    exact ⟨hM, hD.1.mem_of_tendsto (tendsto_logSpec (fun n => (hMs n).1) hM hlim)
      (Eventually.of_forall fun n => (hMs n).2)⟩
  · rw [heq]
    rintro M ⟨hM, hMD⟩ N ⟨hN, hND⟩
    exact ⟨posDef_msqrt_conj hM hN, symCone_majorization hd hsym hD (hD.add_mem hMD hND)
      (logSpec_product_majorized hd hM hN)⟩

end AffineHemigroup
