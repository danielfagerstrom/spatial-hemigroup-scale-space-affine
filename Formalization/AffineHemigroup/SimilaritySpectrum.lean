/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OrderedSpectrum
import AffineHemigroup.ScaleShape
import AffineHemigroup.Defs.SmallerGroups

/-!
# The ordered spectrum under similarities, and the simplex `Δ_d`

Toolbox of `prop:similarity-ray-families`(1) (wave 2, group E, Q-0281): the spectral theorem in
the sorted form `Σ = V diag(λ↑(Σ)) Vᵀ` with `V` orthogonal; `λ↑` of an orthogonal conjugate of a
diagonal matrix with increasing entries; `λ↑(c²QΣQᵀ) = c²λ↑(Σ)`; the trace as the sum of `λ↑`;
`σ(Σ) ∈ Δ_d` for `Σ ∈ PSD(d) ∖ {0}` and `σ(diag σ) = σ` for `σ ∈ Δ_d`; and `Δ_d` as the convex hull
of `d` affinely independent points.
-/

namespace AffineHemigroup

open Matrix Set Polynomial

variable {d : ℕ}

/-! ## Orthogonal conjugates of diagonal matrices -/

/-- `VᵀV = 1` from `VVᵀ = 1`. -/
theorem transpose_mul_self_of_mul_transpose {V : Mat d} (h : V * Vᵀ = 1) : Vᵀ * V = 1 :=
  mul_eq_one_comm.1 h

/-- The roots of the characteristic polynomial of `V diag(v) Vᵀ`, `V` orthogonal, are the entries
of `v`. -/
theorem roots_charpoly_conj_diagonal {V : Mat d} (hV : V * Vᵀ = 1) (v : Fin d → ℝ) :
    (V * diagonal v * Vᵀ).charpoly.roots = Multiset.map v Finset.univ.val := by
  have h1 : (V * diagonal v * Vᵀ).charpoly = (diagonal v).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, transpose_mul_self_of_mul_transpose hV,
      Matrix.one_mul]
  have h2 : (∏ i, (X - C (v i)) : ℝ[X]) =
      ((Multiset.map v Finset.univ.val).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [h1, charpoly_diagonal, h2, roots_multiset_prod_X_sub_C]

/-- **`λ↑` is read off the roots**: if `v` is increasing and lists the roots of the characteristic
polynomial of `X` with multiplicity, then `λ↑(X) = v`. -/
theorem eigUp_eq_of_roots {X : Mat d} {v : Fin d → ℝ} (hv : Monotone v)
    (h : Multiset.map v Finset.univ.val = X.charpoly.roots) : eigUp X = v := by
  have hsort : X.charpoly.roots.sort (· ≤ ·) = List.ofFn v := by
    rw [← h, Fin.univ_val_map, Multiset.coe_sort]
    exact List.mergeSort_eq_self (fun a b : ℝ => a ≤ b) (List.pairwise_ofFn.2 fun i j hij => hv hij.le)
  funext k
  simp [eigUp, hsort]

/-- `λ↑(V diag(v) Vᵀ) = v` for `V` orthogonal and `v` increasing. -/
theorem eigUp_conj_diagonal {V : Mat d} (hV : V * Vᵀ = 1) {v : Fin d → ℝ} (hv : Monotone v) :
    eigUp (V * diagonal v * Vᵀ) = v :=
  eigUp_eq_of_roots hv (roots_charpoly_conj_diagonal hV v).symm

/-- **The permutation matrix** of `τ`, `(P_τ)ᵢⱼ = 1` when `τ i = j`. -/
def permMat (τ : Equiv.Perm (Fin d)) : Mat d := Matrix.of fun i j => if τ i = j then 1 else 0

/-- `P_τ diag(v) P_τᵀ = diag(v ∘ τ)`. -/
theorem permMat_conj_diagonal (τ : Equiv.Perm (Fin d)) (v : Fin d → ℝ) :
    permMat τ * diagonal v * (permMat τ)ᵀ = diagonal (v ∘ τ) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · simp only [Matrix.mul_diagonal, permMat, Matrix.of_apply, Matrix.transpose_apply,
      if_true, one_mul, diagonal_apply, Function.comp_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm (τ.injective.ne h)]
  · intro b _ hb
    simp [Matrix.mul_diagonal, permMat, Ne.symm hb]
  · simp

/-- A permutation matrix is orthogonal. -/
theorem permMat_mul_transpose (τ : Equiv.Perm (Fin d)) : permMat τ * (permMat τ)ᵀ = 1 := by
  have h := permMat_conj_diagonal τ (fun _ => 1)
  rw [diagonal_one, Matrix.mul_one] at h
  rw [h]
  exact diagonal_one

/-- **The spectral theorem in sorted form**: a symmetric `Σ` is `V diag(λ↑(Σ)) Vᵀ` with `V`
orthogonal. -/
theorem exists_orth_diag_eigUp {S : Mat d} (hS : S.IsHermitian) :
    ∃ V : Mat d, V * Vᵀ = 1 ∧ S = V * diagonal (eigUp S) * Vᵀ := by
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin d), eigUp S = hS.eigenvalues ∘ π :=
    exists_perm_of_map_univ_eq (by rw [eigUp_map_univ hS, hS.roots_charpoly_eq_eigenvalues]; simp)
  set U : Mat d := (hS.eigenvectorUnitary : Mat d) with hUdef
  have hU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hS.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose] using this
  have hspec : S = U * diagonal hS.eigenvalues * Uᵀ := by
    have := hS.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hUdef, Matrix.star_eq_conjTranspose] using this
  refine ⟨U * permMat π⁻¹, ?_, ?_⟩
  · rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, permMat_mul_transpose,
      Matrix.mul_one, hU]
  · have h := permMat_conj_diagonal π⁻¹ (eigUp S)
    rw [hπ] at h ⊢
    have he : (hS.eigenvalues ∘ ⇑π) ∘ ⇑(π⁻¹) = hS.eigenvalues := by
      funext i; simp
    rw [he] at h
    rw [Matrix.transpose_mul]
    calc S = U * diagonal hS.eigenvalues * Uᵀ := hspec
      _ = U * (permMat π⁻¹ * diagonal (hS.eigenvalues ∘ π) * (permMat π⁻¹)ᵀ) * Uᵀ := by rw [h]
      _ = _ := by simp only [Matrix.mul_assoc]

/-! ## The ordered spectrum under similarities -/

/-- `(cQ) · Σ = c² QΣQᵀ`. -/
theorem act_smul_left (c : ℝ) (Q S : Mat d) : act (c • Q) S = c ^ 2 • (Q * S * Qᵀ) := by
  rw [act, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

/-- **`λ↑(c²QΣQᵀ) = c²λ↑(Σ)`** for `Q` orthogonal and `Σ` symmetric. -/
theorem eigUp_act_smul_orth (c : ℝ) {Q : Mat d} (hQ : Q * Qᵀ = 1) {S : Mat d}
    (hS : S.IsHermitian) : eigUp (act (c • Q) S) = c ^ 2 • eigUp S := by
  obtain ⟨V, hV, hSV⟩ := exists_orth_diag_eigUp hS
  have hW : (Q * V) * (Q * V)ᵀ = 1 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hV, Matrix.mul_one, hQ]
  have he : act (c • Q) S = (Q * V) * diagonal (c ^ 2 • eigUp S) * (Q * V)ᵀ := by
    rw [act_smul_left, diagonal_smul, Matrix.transpose_mul]
    conv_lhs => rw [hSV]
    simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  rw [he]
  refine eigUp_conj_diagonal hW fun i j hij => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (eigUp_monotone hS hij) (sq_nonneg c)

/-- `tr(c²QΣQᵀ) = c² tr Σ` for `Q` orthogonal. -/
theorem trace_act_smul_orth (c : ℝ) {Q : Mat d} (hQ : Q * Qᵀ = 1) (S : Mat d) :
    (act (c • Q) S).trace = c ^ 2 * S.trace := by
  rw [act_smul_left, trace_smul, Matrix.trace_mul_cycle, transpose_mul_self_of_mul_transpose hQ,
    Matrix.one_mul, smul_eq_mul]

/-- **The trace is the sum of `λ↑`.** -/
theorem sum_eigUp {S : Mat d} (hS : S.IsHermitian) : ∑ k, eigUp S k = S.trace := by
  obtain ⟨V, hV, hSV⟩ := exists_orth_diag_eigUp hS
  conv_rhs => rw [hSV]
  rw [Matrix.trace_mul_cycle, transpose_mul_self_of_mul_transpose hV, Matrix.one_mul,
    trace_diagonal]

/-- The entries of `λ↑` of a positive semidefinite matrix are nonnegative. -/
theorem eigUp_nonneg {S : Mat d} (hS : S.PosSemidef) (k : Fin d) : 0 ≤ eigUp S k := by
  obtain ⟨i, hi⟩ := eigUp_mem_eigenvalues hS.1 k
  rw [← hi]
  exact hS.eigenvalues_nonneg i

/-- The trace of a nonzero positive semidefinite matrix is positive. -/
theorem trace_pos_of_posSemidef {S : Mat d} (hS : S.PosSemidef) (h0 : S ≠ 0) : 0 < S.trace :=
  lt_of_le_of_ne hS.trace_nonneg fun h => h0 (hS.trace_eq_zero_iff.1 h.symm)

/-- **`λ↑(diag σ) = σ ∘ rev`** for a decreasing `σ`. -/
theorem eigUp_diagonal_antitone {σ : Fin d → ℝ} (hσ : Antitone σ) :
    eigUp (diagonal σ) = σ ∘ Fin.rev := by
  refine eigUp_eq_of_roots (fun i j hij => hσ (Fin.rev_le_rev.2 hij)) ?_
  have h := roots_charpoly_conj_diagonal (V := 1) (by simp) σ
  rw [Matrix.one_mul, transpose_one, Matrix.mul_one] at h
  rw [h, ← Multiset.map_map]
  congr 1
  exact Multiset.map_univ_val_equiv Fin.revPerm

/-! ## `σ(Σ)` and `Δ_d` -/

/-- **`σ(Σ) ∈ Δ_d`** for `Σ ∈ PSD(d) ∖ {0}`. -/
theorem normSpec_mem_simplexDesc {S : Mat d} (hS : S.PosSemidef) (h0 : S ≠ 0) :
    normSpec S ∈ simplexDesc d := by
  have ht := trace_pos_of_posSemidef hS h0
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · simp only [normSpec, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (eigUp_monotone hS.1 (Fin.rev_le_rev.2 hij))
      (inv_nonneg.2 ht.le)
  · simp only [normSpec, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.le) (eigUp_nonneg hS _)
  · simp only [normSpec, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Fintype.sum_equiv Fin.revPerm (fun i => eigUp S (Fin.rev i))
      (eigUp S) (fun i => rfl), sum_eigUp hS.1, inv_mul_cancel₀ ht.ne']

/-- **`σ(diag σ) = σ`** for `σ ∈ Δ_d`. -/
theorem normSpec_diagonal {σ : Fin d → ℝ} (hσ : σ ∈ simplexDesc d) : normSpec (diagonal σ) = σ := by
  rw [normSpec, trace_diagonal, hσ.2.2, inv_one, one_smul, eigUp_diagonal_antitone hσ.1]
  funext i
  simp

/-- `diag σ` for `σ ∈ Δ_d` is positive semidefinite and nonzero. -/
theorem diagonal_simplexDesc {σ : Fin d → ℝ} (hσ : σ ∈ simplexDesc d) :
    (diagonal σ).PosSemidef ∧ diagonal σ ≠ 0 := by
  refine ⟨PosSemidef.diagonal hσ.2.1, fun h => ?_⟩
  have := congrArg Matrix.trace h
  rw [trace_diagonal, hσ.2.2, trace_zero] at this
  exact one_ne_zero this

/-! ## `Δ_d` is a simplex of dimension `d - 1` -/

/-- **The vertices of `Δ_d`**: `v_k := (k+1)⁻¹(1, …, 1, 0, …, 0)`, with `k + 1` ones. -/
noncomputable def simplexVtx (k : Fin d) : Fin d → ℝ := fun i => if i ≤ k then ((k : ℝ) + 1)⁻¹ else 0

/-- The extension by `0` of the coefficients `gₖ/(k+1)` to `ℕ`. -/
noncomputable def vtxCoeff (g : Fin d → ℝ) (n : ℕ) : ℝ :=
  if h : n < d then g ⟨n, h⟩ * ((n : ℝ) + 1)⁻¹ else 0

/-- `(∑ₖ gₖ vₖ)ᵢ = ∑_{i ≤ n < d} gₙ/(n+1)`. -/
theorem sum_smul_simplexVtx_apply (g : Fin d → ℝ) (i : Fin d) :
    (∑ k, g k • simplexVtx k) i = ∑ n ∈ Finset.Ico (i : ℕ) d, vtxCoeff g n := by
  rw [Finset.sum_apply]
  have h1 : ∀ k : Fin d, (g k • simplexVtx k) i =
      (fun n : ℕ => if (i : ℕ) ≤ n then vtxCoeff g n else 0) k := by
    intro k
    simp only [Pi.smul_apply, simplexVtx, smul_eq_mul, vtxCoeff, dif_pos k.2, Fin.le_def]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun k _ => h1 k, Fin.sum_univ_eq_sum_range
    (fun n => if (i : ℕ) ≤ n then vtxCoeff g n else 0), ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- `Δ_d` is convex. -/
theorem convex_simplexDesc : Convex ℝ (simplexDesc d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.1 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.1 hij) hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.2.1 i)) (mul_nonneg hb (hy.2.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2.2, hy.2.2, mul_one,
      mul_one, hab]

/-- Each vertex lies in `Δ_d`. -/
theorem simplexVtx_mem (k : Fin d) : simplexVtx k ∈ simplexDesc d := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · simp only [simplexVtx]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (hij.trans h1) h2
    · exact (inv_pos.2 hk).le
    · exact le_rfl
  · simp only [simplexVtx]
    split_ifs
    · exact (inv_pos.2 hk).le
    · exact le_rfl
  · simp only [simplexVtx]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (Finset.univ.filter fun i : Fin d => i ≤ k).card = (k : ℕ) + 1 := by
      rw [show (Finset.univ.filter fun i : Fin d => i ≤ k) = Finset.Iic k by ext; simp]
      exact Fin.card_Iic k
    rw [hc]
    push_cast
    exact mul_inv_cancel₀ hk.ne'

/-- The weights of `σ ∈ Δ_d` in the vertices, telescoped. -/
theorem sum_range_weight (S : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (S k - S (k + 1)) =
      ∑ k ∈ Finset.range n, S k - n * S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- **`Δ_d` is the convex hull of `d` affinely independent points**, a simplex of dimension
`d - 1`. -/
theorem simplexDesc_simplex :
    AffineIndependent ℝ (simplexVtx (d := d)) ∧
      simplexDesc d = convexHull ℝ (Set.range (simplexVtx (d := d))) := by
  have hli : LinearIndependent ℝ (simplexVtx (d := d)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    -- the coordinates of `∑ gₖ vₖ` vanish, and so do their differences
    have hc : ∀ j : Fin d, ∑ n ∈ Finset.Ico (j : ℕ) d, vtxCoeff g n = 0 := by
      intro j
      rw [← sum_smul_simplexVtx_apply, hg]
      rfl
    have hnext : ∑ n ∈ Finset.Ico ((i : ℕ) + 1) d, vtxCoeff g n = 0 := by
      by_cases h : (i : ℕ) + 1 < d
      · exact hc ⟨(i : ℕ) + 1, h⟩
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have h := hc i
    rw [Finset.sum_eq_sum_Ico_succ_bot i.2, hnext, add_zero] at h
    simp only [vtxCoeff, dif_pos i.2] at h
    have hi : ((i : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simpa [hi] using h
  refine ⟨hli.affineIndependent, ?_⟩
  · refine Set.Subset.antisymm (fun σ hσ => ?_)
      (convexHull_min (Set.range_subset_iff.2 simplexVtx_mem) convex_simplexDesc)
    set S : ℕ → ℝ := fun n => if h : n < d then σ ⟨n, h⟩ else 0 with hS
    set w : Fin d → ℝ := fun k => ((k : ℝ) + 1) * (S k - S ((k : ℕ) + 1)) with hw
    have hSk : ∀ k : Fin d, S k = σ k := fun k => by simp [hS, k.2]
    have hw0 : ∀ k ∈ Finset.univ, 0 ≤ w k := by
      intro k _
      refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
      rw [hSk]
      by_cases h : (k : ℕ) + 1 < d
      · simp only [hS, dif_pos h]
        exact hσ.1 (Fin.le_def.2 (Nat.le_succ _))
      · simp only [hS, dif_neg h]
        exact hσ.2.1 k
    have hw1 : ∑ k ∈ Finset.univ, w k = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun n => ((n : ℝ) + 1) * (S n - S (n + 1))) d,
        sum_range_weight]
      have hSd : S d = 0 := by simp [hS]
      rw [hSd, mul_zero, sub_zero, ← Fin.sum_univ_eq_sum_range S d]
      simp only [hSk]
      exact hσ.2.2
    have hσw : σ = ∑ k, w k • simplexVtx k := by
      funext i
      rw [sum_smul_simplexVtx_apply]
      have hcoef : ∀ n ∈ Finset.Ico (i : ℕ) d, vtxCoeff w n = -(S (n + 1) - S n) := by
        intro n hn
        have hnd : n < d := (Finset.mem_Ico.1 hn).2
        simp only [vtxCoeff, dif_pos hnd, hw]
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [Finset.sum_congr rfl hcoef, Finset.sum_neg_distrib,
        Finset.sum_Ico_sub (f := S) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2))]
      simp [hS, i.2]
    rw [hσw]
    exact (convex_convexHull ℝ _).sum_mem hw0 hw1 fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩

end AffineHemigroup
