/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Gauge
import AffineHemigroup.Defs.Spectral
import Mathlib.Analysis.Matrix.PosDef

/-!
# `lem:loewner-scale-shape` — the Loewner order in scale–shape coordinates

Blueprint: `blueprint/src/parts/05-landscape.tex`, `lem:loewner-scale-shape`. Lean core only.

## The route

The blueprint's, step for step. The first section is the calculus of the ordered spectrum `eigUp`
of a symmetric matrix that this node and `prop:shape-adapted-apertures` read: it is a
rearrangement of Mathlib's eigenvalues, increasing, its product is the determinant, and
`X - cI ≥ 0` exactly when `c ≤ λ↑₁(X)` (through the continuous functional calculus, whose order on
matrices is the Loewner order). The second is the calculus of the volume scale, the shape and the
relative step `S^{-1/2} S' S^{-1/2}`: congruence by `R := S₁(Σ₁)^{-1/2}` carries `Σ₁` to `t₁² I` and
`Σ₂` to `t₂² N`, which is clause (1).
-/

namespace AffineHemigroup

open Matrix
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## The ordered spectrum of a symmetric matrix -/

/-- A symmetric matrix has exactly `d` roots of its characteristic polynomial. -/
theorem card_roots_charpoly {X : Mat d} (hX : X.IsHermitian) : X.charpoly.roots.card = d := by
  rw [hX.roots_charpoly_eq_eigenvalues]
  simp

/-- `eigUp X` lists the roots of the characteristic polynomial, with multiplicity. -/
theorem eigUp_map_univ {X : Mat d} (hX : X.IsHermitian) :
    Multiset.map (eigUp X) Finset.univ.val = X.charpoly.roots := by
  set L := X.charpoly.roots.sort (· ≤ ·) with hL
  have hlen : L.length = d := by rw [hL, Multiset.length_sort, card_roots_charpoly hX]
  have h : List.ofFn (eigUp X) = L := by
    apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    rw [List.getElem_ofFn]
    simp only [eigUp, ← hL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  rw [Fin.univ_val_map, h, hL, Multiset.sort_eq]

/-- The ordered spectrum of a symmetric matrix is increasing. -/
theorem eigUp_monotone {X : Mat d} (hX : X.IsHermitian) : Monotone (eigUp X) := by
  set L := X.charpoly.roots.sort (· ≤ ·) with hL
  have hlen : L.length = d := by rw [hL, Multiset.length_sort, card_roots_charpoly hX]
  have hs : L.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  intro i j hij
  have hi : (i : ℕ) < L.length := by rw [hlen]; exact i.2
  have hj : (j : ℕ) < L.length := by rw [hlen]; exact j.2
  simp only [eigUp, ← hL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some]
  rcases eq_or_lt_of_le hij with h | h
  · subst h
    exact le_rfl
  · exact List.pairwise_iff_getElem.1 hs _ _ hi hj (Fin.lt_def.1 h)

/-- The product of the ordered spectrum is the determinant. -/
theorem prod_eigUp {X : Mat d} (hX : X.IsHermitian) : ∏ k, eigUp X k = X.det := by
  rw [Finset.prod_eq_multiset_prod, eigUp_map_univ hX,
    det_eq_prod_roots_charpoly_of_splits hX.splits_charpoly]

/-- Every entry of the ordered spectrum is an eigenvalue. -/
theorem eigUp_mem_eigenvalues {X : Mat d} (hX : X.IsHermitian) (k : Fin d) :
    ∃ i, hX.eigenvalues i = eigUp X k := by
  have h : eigUp X k ∈ Multiset.map (eigUp X) Finset.univ.val :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
  rw [eigUp_map_univ hX, hX.roots_charpoly_eq_eigenvalues] at h
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h
  exact ⟨i, by simpa using hi⟩

/-- Every eigenvalue is an entry of the ordered spectrum. -/
theorem eigenvalues_mem_eigUp {X : Mat d} (hX : X.IsHermitian) (i : Fin d) :
    ∃ k, eigUp X k = hX.eigenvalues i := by
  have h : (hX.eigenvalues i : ℝ) ∈ X.charpoly.roots := by
    rw [hX.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, by simp⟩
  rw [← eigUp_map_univ hX] at h
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h
  exact ⟨k, hk⟩

/-- The least entry `λ↑₁` is at most every eigenvalue. -/
theorem eigUp_zero_le [NeZero d] {X : Mat d} (hX : X.IsHermitian) (i : Fin d) :
    eigUp X 0 ≤ hX.eigenvalues i := by
  obtain ⟨k, hk⟩ := eigenvalues_mem_eigUp hX i
  rw [← hk]
  exact eigUp_monotone hX (Fin.zero_le k)

/-- Every index is at most the last one, `Fin.rev 0`. -/
theorem le_rev_zero [NeZero d] (k : Fin d) : k ≤ Fin.rev 0 := by
  rw [Fin.le_def, Fin.val_rev, Fin.val_zero]
  omega

/-- The greatest entry `λ↑_d` is at least every eigenvalue. -/
theorem le_eigUp_rev_zero [NeZero d] {X : Mat d} (hX : X.IsHermitian) (i : Fin d) :
    hX.eigenvalues i ≤ eigUp X (Fin.rev 0) := by
  obtain ⟨k, hk⟩ := eigenvalues_mem_eigUp hX i
  rw [← hk]
  exact eigUp_monotone hX (le_rev_zero k)

/-- The spectrum of a symmetric matrix, as a set, is the set of entries of its ordered spectrum. -/
theorem spectrum_eq_range_eigUp {X : Mat d} (hX : X.IsHermitian) :
    spectrum ℝ X = Set.range (eigUp X) := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := eigenvalues_mem_eigUp hX i
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨i, hi⟩ := eigUp_mem_eigenvalues hX k
    exact ⟨i, hi⟩

/-- **`X - cI ≥ 0` exactly when `c ≤ λ↑₁(X)`**, for symmetric `X`. -/
theorem posSemidef_sub_smul_one_iff [NeZero d] {X : Mat d} (hX : X.IsHermitian) (c : ℝ) :
    (X - c • (1 : Mat d)).PosSemidef ↔ c ≤ eigUp X 0 := by
  have hsa : IsSelfAdjoint X := hX
  have h := algebraMap_le_iff_le_spectrum (r := c) (a := X) hsa
  rw [Algebra.algebraMap_eq_smul_one, spectrum_eq_range_eigUp hX] at h
  rw [← Matrix.le_iff, h]
  constructor
  · intro h'
    exact h' _ ⟨0, rfl⟩
  · rintro h' _ ⟨k, rfl⟩
    exact h'.trans (eigUp_monotone hX (Fin.zero_le k))

/-- **`cI - X ≥ 0` exactly when `λ↑_d(X) ≤ c`**, for symmetric `X`. -/
theorem posSemidef_smul_one_sub_iff [NeZero d] {X : Mat d} (hX : X.IsHermitian) (c : ℝ) :
    (c • (1 : Mat d) - X).PosSemidef ↔ eigUp X (Fin.rev 0) ≤ c := by
  have hsa : IsSelfAdjoint X := hX
  have h := le_algebraMap_iff_spectrum_le (r := c) (a := X) hsa
  rw [Algebra.algebraMap_eq_smul_one, spectrum_eq_range_eigUp hX] at h
  rw [← Matrix.le_iff, h]
  constructor
  · intro h'
    exact h' _ ⟨_, rfl⟩
  · rintro h' _ ⟨k, rfl⟩
    exact (eigUp_monotone hX (le_rev_zero k)).trans h'

/-- The entries of the ordered spectrum of a positive definite matrix are positive. -/
theorem eigUp_pos {X : Mat d} (hX : X.PosDef) (k : Fin d) : 0 < eigUp X k := by
  obtain ⟨i, hi⟩ := eigUp_mem_eigenvalues hX.isHermitian k
  rw [← hi]
  exact hX.eigenvalues_pos i


/-- A positive multiple of a matrix is positive semidefinite exactly when the matrix is. -/
theorem posSemidef_smul_iff {c : ℝ} (hc : 0 < c) (X : Mat d) :
    (c • X).PosSemidef ↔ X.PosSemidef := by
  refine ⟨fun h => ?_, fun h => h.smul hc.le⟩
  have := h.smul (inv_pos.2 hc).le
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

/-- An index-free form of the "largest entry" bound: if `n` is increasing, positive, with product
`1` and `c ≤ n₀`, `c > 0`, then `n_d c^{d-1} ≤ 1`. -/
theorem last_mul_pow_le_one [NeZero d] {n : Fin d → ℝ} (hmono : Monotone n)
    (hprod : ∏ k, n k = 1) {c : ℝ} (hc : 0 < c) (hcn : c ≤ n 0) :
    n (Fin.rev 0) * c ^ (d - 1) ≤ 1 := by
  have hpos : ∀ k, 0 < n k := fun k => hc.trans_le (hcn.trans (hmono (Fin.zero_le k)))
  have hsplit := Finset.mul_prod_erase Finset.univ n (Finset.mem_univ (Fin.rev (0 : Fin d)))
  rw [hprod] at hsplit
  have hcard : (Finset.univ.erase (Fin.rev (0 : Fin d))).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hle : c ^ (d - 1) ≤ ∏ k ∈ Finset.univ.erase (Fin.rev (0 : Fin d)), n k := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hc.le)
      (fun k _ => hcn.trans (hmono (Fin.zero_le k)))
  rw [← hsplit]
  exact mul_le_mul_of_nonneg_left hle (hpos _).le

/-! ## The volume scale, the shape, and the relative step -/

/-- `t(Σ) > 0` on `PD(d)`. -/
theorem volScale_pos {S : Mat d} (hS : S.PosDef) : 0 < volScale S :=
  Real.rpow_pos_of_pos hS.det_pos _

/-- `t(Σ)^{2d} = det Σ` on `PD(d)`. -/
theorem volScale_pow [NeZero d] {S : Mat d} (hS : S.PosDef) : volScale S ^ (2 * d) = S.det := by
  rw [volScale, ← Real.rpow_natCast, ← Real.rpow_mul hS.det_pos.le]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [this, Real.rpow_one]

/-- `t(cΣ) = √c t(Σ)` for `c > 0`. -/
theorem volScale_smul [NeZero d] {c : ℝ} (hc : 0 < c) {S : Mat d} (hS : S.PosDef) :
    volScale (c • S) = Real.sqrt c * volScale S := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [volScale, volScale, det_smul, Fintype.card_fin,
    Real.mul_rpow (pow_nonneg hc.le _) hS.det_pos.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hc.le, Real.sqrt_eq_rpow]
  congr 2
  field_simp

/-- `t(Σ) = 1` when `det Σ = 1`. -/
theorem volScale_of_det_eq_one {S : Mat d} (h : S.det = 1) : volScale S = 1 := by
  rw [volScale, h, Real.one_rpow]

/-- `Σ = t(Σ)² S(Σ)`. -/
theorem smul_shapeOf {S : Mat d} (hS : S.PosDef) : volScale S ^ 2 • shapeOf S = S := by
  rw [shapeOf, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ (volScale_pos hS).ne'), one_smul]

/-- The shape of `Σ ∈ PD(d)` is in `PD(d)`. -/
theorem shapeOf_posDef {S : Mat d} (hS : S.PosDef) : (shapeOf S).PosDef :=
  hS.smul (inv_pos.2 (pow_pos (volScale_pos hS) 2))

/-- `det S(Σ) = 1`. -/
theorem det_shapeOf [NeZero d] {S : Mat d} (hS : S.PosDef) : (shapeOf S).det = 1 := by
  rw [shapeOf, det_smul, Fintype.card_fin, inv_pow, ← pow_mul, volScale_pow hS,
    inv_mul_cancel₀ hS.det_pos.ne']

/-- The shape is blind to scale: `S(cΣ) = S(Σ)` for `c > 0`. -/
theorem shapeOf_smul [NeZero d] {c : ℝ} (hc : 0 < c) {S : Mat d} (hS : S.PosDef) :
    shapeOf (c • S) = shapeOf S := by
  rw [shapeOf, shapeOf, volScale_smul hc hS, mul_pow, Real.sq_sqrt hc.le, smul_smul]
  congr 1
  have := (volScale_pos hS).ne'
  field_simp

/-- A matrix of determinant `1` in `PD(d)` is its own shape. -/
theorem shapeOf_of_det_eq_one {S : Mat d} (h : S.det = 1) : shapeOf S = S := by
  rw [shapeOf, volScale_of_det_eq_one h, one_pow, inv_one, one_smul]

/-- `Σ^{1/2}` is invertible on `PD(d)`. -/
theorem isUnit_msqrt {A : Mat d} (hA : A.PosDef) : IsUnit (msqrt A) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (msqrt_mem_glSet hA)

/-- `Σ^{-1/2} Σ^{1/2} = I`. -/
theorem msqrt_inv_mul {A : Mat d} (hA : A.PosDef) : (msqrt A)⁻¹ * msqrt A = 1 :=
  Matrix.nonsing_inv_mul _ (msqrt_mem_glSet hA)

/-- `Σ^{1/2} Σ^{-1/2} = I`. -/
theorem msqrt_mul_inv {A : Mat d} (hA : A.PosDef) : msqrt A * (msqrt A)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (msqrt_mem_glSet hA)

/-- `Σ^{-1/2}` is symmetric. -/
theorem msqrt_inv_transpose (A : Mat d) : ((msqrt A)⁻¹)ᵀ = (msqrt A)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, msqrt_transpose]

/-- `star Σ^{-1/2} = Σ^{-1/2}`. -/
theorem star_msqrt_inv (A : Mat d) : star ((msqrt A)⁻¹) = (msqrt A)⁻¹ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    msqrt_inv_transpose]

/-- `star Σ^{1/2} = Σ^{1/2}`. -/
theorem star_msqrt (A : Mat d) : star (msqrt A) = msqrt A := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, msqrt_transpose]

/-- The relative step of `Σ` to itself is `I`. -/
theorem relStep_self {A : Mat d} (hA : A.PosDef) : relStep A A = 1 := by
  have h := msqrt_mul_self hA.posSemidef
  calc relStep A A = (msqrt A)⁻¹ * (msqrt A * msqrt A) * (msqrt A)⁻¹ := by rw [relStep, h]
    _ = 1 := by rw [← mul_assoc, msqrt_inv_mul hA, one_mul, msqrt_mul_inv hA]

/-- `Σ^{1/2} (Σ^{-1/2} B Σ^{-1/2}) Σ^{1/2} = B`. -/
theorem msqrt_mul_relStep {A : Mat d} (hA : A.PosDef) (B : Mat d) :
    msqrt A * relStep A B * msqrt A = B := by
  rw [relStep, ← mul_assoc, ← mul_assoc, msqrt_mul_inv hA, one_mul, mul_assoc,
    msqrt_inv_mul hA, mul_one]

/-- `Σ^{-1/2} (Σ^{1/2} N Σ^{1/2}) Σ^{-1/2} = N`. -/
theorem relStep_msqrt_mul {A : Mat d} (hA : A.PosDef) (N : Mat d) :
    relStep A (msqrt A * N * msqrt A) = N := by
  rw [relStep, ← mul_assoc, ← mul_assoc, msqrt_inv_mul hA, one_mul, mul_assoc,
    msqrt_mul_inv hA, mul_one]

/-- The relative step is linear in its second argument (scalars). -/
theorem relStep_smul (A : Mat d) (c : ℝ) (B : Mat d) : relStep A (c • B) = c • relStep A B := by
  simp only [relStep, Matrix.mul_smul, Matrix.smul_mul]

/-- The relative step is linear in its second argument (differences). -/
theorem relStep_sub (A B B' : Mat d) : relStep A (B - B') = relStep A B - relStep A B' := by
  simp only [relStep, Matrix.mul_sub, Matrix.sub_mul]

/-- The relative step is injective in its second argument. -/
theorem relStep_injective {A : Mat d} (hA : A.PosDef) {B B' : Mat d}
    (h : relStep A B = relStep A B') : B = B' := by
  rw [← msqrt_mul_relStep hA B, h, msqrt_mul_relStep hA B']

/-- The relative step of a symmetric matrix is symmetric. -/
theorem relStep_isHermitian (A : Mat d) {B : Mat d} (hB : B.IsHermitian) :
    (relStep A B).IsHermitian := by
  have h := isHermitian_conjTranspose_mul_mul (msqrt A)⁻¹ hB
  rwa [← Matrix.star_eq_conjTranspose, star_msqrt_inv] at h

/-- Congruence by `Σ^{-1/2}` preserves positive semidefiniteness in both directions. -/
theorem posSemidef_relStep_iff {A : Mat d} (hA : A.PosDef) (B : Mat d) :
    (relStep A B).PosSemidef ↔ B.PosSemidef := by
  have hU : IsUnit (msqrt A)⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 (isUnit_msqrt hA)
  have h := hU.posSemidef_star_left_conjugate_iff (x := B)
  rwa [star_msqrt_inv] at h

/-- Congruence by `Σ^{-1/2}` preserves positive definiteness in both directions. -/
theorem posDef_relStep_iff {A : Mat d} (hA : A.PosDef) (B : Mat d) :
    (relStep A B).PosDef ↔ B.PosDef := by
  have hU : IsUnit (msqrt A)⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 (isUnit_msqrt hA)
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff hU (x := B)
  rwa [star_msqrt_inv] at h

/-- `Σ^{1/2} N Σ^{1/2} ∈ PD(d)` for `N ∈ PD(d)`. -/
theorem posDef_msqrt_conj {A : Mat d} (hA : A.PosDef) {N : Mat d} (hN : N.PosDef) :
    (msqrt A * N * msqrt A).PosDef := by
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (isUnit_msqrt hA) (x := N)
  rw [star_msqrt] at h
  exact h.2 hN

/-- `det(Σ^{-1/2} B Σ^{-1/2}) = det B / det Σ`. -/
theorem det_relStep {A : Mat d} (hA : A.PosDef) (B : Mat d) :
    (relStep A B).det = B.det / A.det := by
  have hRQ : ((msqrt A)⁻¹).det * (msqrt A).det = 1 := by
    rw [← det_mul, msqrt_inv_mul hA, det_one]
  have hQ : (msqrt A).det * (msqrt A).det = A.det := by
    rw [← det_mul, msqrt_mul_self hA.posSemidef]
  have h : (relStep A B).det * A.det = B.det := by
    rw [relStep, det_mul, det_mul, ← hQ]
    calc ((msqrt A)⁻¹).det * B.det * ((msqrt A)⁻¹).det * ((msqrt A).det * (msqrt A).det)
        = (((msqrt A)⁻¹).det * (msqrt A).det) * (((msqrt A)⁻¹).det * (msqrt A).det) *
            B.det := by ring
      _ = B.det := by rw [hRQ]; ring
  rw [← h, mul_div_cancel_right₀ _ hA.det_pos.ne']

/-- `det(Σ^{1/2} N Σ^{1/2}) = det Σ · det N`. -/
theorem det_msqrt_conj {A : Mat d} (hA : A.PosDef) (N : Mat d) :
    (msqrt A * N * msqrt A).det = A.det * N.det := by
  have hQ : (msqrt A).det * (msqrt A).det = A.det := by
    rw [← det_mul, msqrt_mul_self hA.posSemidef]
  rw [det_mul, det_mul, ← hQ]
  ring

/-! ## `lem:loewner-scale-shape` -/

/-- **`lem:loewner-scale-shape`**, the coordinates: for `Σ ∈ PD(d)` the shape has determinant `1`,
and the eigenvalues of the relative shape `N = S₁^{-1/2} S₂ S₁^{-1/2}` multiply to `1`. -/
theorem scale_shape_coords [NeZero d] {S₁ S₂ : Mat d} (h₁ : S₁.PosDef) (h₂ : S₂.PosDef) :
    (shapeOf S₁).det = 1 ∧
      ∏ i, eigUp (relStep (shapeOf S₁) (shapeOf S₂)) i = 1 := by
  refine ⟨det_shapeOf h₁, ?_⟩
  rw [prod_eigUp (relStep_isHermitian _ (shapeOf_posDef h₂).isHermitian),
    det_relStep (shapeOf_posDef h₁), det_shapeOf h₁, det_shapeOf h₂, div_one]

/-- The relative shape `N` of a pair in `PD(d)` is in `PD(d)`. -/
theorem relShape_posDef {S₁ S₂ : Mat d} (h₁ : S₁.PosDef) (h₂ : S₂.PosDef) :
    (relStep (shapeOf S₁) (shapeOf S₂)).PosDef :=
  (posDef_relStep_iff (shapeOf_posDef h₁) _).2 (shapeOf_posDef h₂)

/-- **`lem:loewner-scale-shape`(1)**: `Σ₁ ≤ Σ₂` if and only if `n₁ ≥ (t₁/t₂)²`. -/
theorem loewner_iff_scale_shape [NeZero d] {S₁ S₂ : Mat d} (h₁ : S₁.PosDef) (h₂ : S₂.PosDef) :
    loewnerLE S₁ S₂ ↔
      (volScale S₁ / volScale S₂) ^ 2 ≤ eigUp (relStep (shapeOf S₁) (shapeOf S₂)) 0 := by
  set A := shapeOf S₁ with hAdef
  have hA : A.PosDef := shapeOf_posDef h₁
  set N := relStep A (shapeOf S₂) with hNdef
  set t₁ := volScale S₁ with ht₁
  set t₂ := volScale S₂ with ht₂
  have ht₁pos : 0 < t₁ := volScale_pos h₁
  have ht₂pos : 0 < t₂ := volScale_pos h₂
  have hR1 : relStep A S₁ = t₁ ^ 2 • (1 : Mat d) := by
    conv_lhs => rw [← smul_shapeOf h₁]
    rw [relStep_smul, ← hAdef, relStep_self hA]
  have hR2 : relStep A S₂ = t₂ ^ 2 • N := by
    conv_lhs => rw [← smul_shapeOf h₂]
    rw [relStep_smul]
  have hkey : relStep A (S₂ - S₁) =
      t₂ ^ 2 • (N - (t₁ / t₂) ^ 2 • (1 : Mat d)) := by
    rw [relStep_sub, hR1, hR2, smul_sub, smul_smul]
    congr 2
    field_simp
  rw [loewnerLE, ← posSemidef_relStep_iff hA, hkey, posSemidef_smul_iff (pow_pos ht₂pos 2),
    posSemidef_sub_smul_one_iff (relStep_isHermitian _ (shapeOf_posDef h₂).isHermitian)]

/-- **`lem:loewner-scale-shape`(2)**, no order within a scale: `Σ₁ ≤ Σ₂` gives `t₁ ≤ t₂`, with
equality only if `Σ₁ = Σ₂`; and `Σ₁ ≤ Σ₂` with `S₁ = S₂` holds exactly when `Σ₂ = λ²Σ₁` with
`λ ≥ 1`. -/
theorem loewner_no_order_within_scale [NeZero d] {S₁ S₂ : Mat d} (h₁ : S₁.PosDef)
    (h₂ : S₂.PosDef) :
    (loewnerLE S₁ S₂ → volScale S₁ ≤ volScale S₂ ∧ (volScale S₁ = volScale S₂ → S₁ = S₂)) ∧
      (loewnerLE S₁ S₂ ∧ shapeOf S₁ = shapeOf S₂ ↔ ∃ lam : ℝ, 1 ≤ lam ∧ S₂ = lam ^ 2 • S₁) := by
  set A := shapeOf S₁ with hAdef
  have hA : A.PosDef := shapeOf_posDef h₁
  set N := relStep A (shapeOf S₂) with hNdef
  have hN : N.PosDef := relShape_posDef h₁ h₂
  set t₁ := volScale S₁ with ht₁
  set t₂ := volScale S₂ with ht₂
  have ht₁pos : 0 < t₁ := volScale_pos h₁
  have ht₂pos : 0 < t₂ := volScale_pos h₂
  have hprod : ∏ k, eigUp N k = 1 := (scale_shape_coords h₁ h₂).2
  have hmono : Monotone (eigUp N) := eigUp_monotone hN.isHermitian
  /- The first sentence. -/
  have hfirst : loewnerLE S₁ S₂ → t₁ ≤ t₂ ∧ (t₁ = t₂ → S₁ = S₂) := by
    intro hle
    have hc := (loewner_iff_scale_shape h₁ h₂).1 hle
    set c := (t₁ / t₂) ^ 2 with hcdef
    have hcpos : 0 < c := by positivity
    have hcd : c ^ d ≤ 1 := by
      calc c ^ d = ∏ _k : Fin d, c := by simp
        _ ≤ ∏ k, eigUp N k :=
            Finset.prod_le_prod (fun _ _ => hcpos.le) (fun k _ => hc.trans (hmono (Fin.zero_le k)))
        _ = 1 := hprod
    have hc1 : c ≤ 1 := (pow_le_one_iff_of_nonneg hcpos.le (NeZero.ne d)).1 hcd
    have hq1 : t₁ / t₂ ≤ 1 :=
      (pow_le_one_iff_of_nonneg (div_pos ht₁pos ht₂pos).le two_ne_zero).1 hc1
    refine ⟨(div_le_one ht₂pos).1 hq1, fun heq => ?_⟩
    have hc1' : c = 1 := by rw [hcdef, heq, div_self ht₂pos.ne', one_pow]
    rw [hc1'] at hc
    have hlast : eigUp N (Fin.rev 0) ≤ 1 := by
      have := last_mul_pow_le_one hmono hprod one_pos hc
      rwa [one_pow, mul_one] at this
    have hge : (1 : Mat d) ≤ N := by
      rw [Matrix.le_iff, ← one_smul ℝ (1 : Mat d)]
      exact (posSemidef_sub_smul_one_iff hN.isHermitian 1).2 hc
    have hle' : N ≤ (1 : Mat d) := by
      rw [Matrix.le_iff, ← one_smul ℝ (1 : Mat d)]
      exact (posSemidef_smul_one_sub_iff hN.isHermitian 1).2 hlast
    have hN1 : N = 1 := le_antisymm hle' hge
    have hshape : shapeOf S₂ = A := by
      rw [← msqrt_mul_relStep hA (shapeOf S₂), ← hNdef, hN1, mul_one, msqrt_mul_self hA.posSemidef]
    rw [← smul_shapeOf h₁, ← smul_shapeOf h₂, hshape, ← ht₁, ← ht₂, heq]
  refine ⟨hfirst, ⟨fun ⟨hle, hsh⟩ => ?_, fun ⟨lam, hlam, hS₂⟩ => ?_⟩⟩
  · refine ⟨t₂ / t₁, (one_le_div ht₁pos).2 (hfirst hle).1, ?_⟩
    calc S₂ = t₂ ^ 2 • shapeOf S₂ := (smul_shapeOf h₂).symm
      _ = t₂ ^ 2 • ((t₁ ^ 2)⁻¹ • S₁) := by rw [← hsh]; rfl
      _ = (t₂ / t₁) ^ 2 • S₁ := by
          rw [smul_smul]
          congr 1
          field_simp
  · have hlam0 : 0 < lam ^ 2 := by positivity
    refine ⟨?_, ?_⟩
    · rw [loewnerLE, hS₂]
      have : lam ^ 2 • S₁ - S₁ = (lam ^ 2 - 1) • S₁ := by rw [sub_smul, one_smul]
      rw [this]
      exact h₁.posSemidef.smul (by nlinarith)
    · rw [hS₂, shapeOf_smul hlam0 h₁]

/-- **`lem:loewner-scale-shape`(3)**, a speed limit on shape: `Σ₁ ≤ Σ₂` gives
`(t₁/t₂)² ≤ n₁ ≤ n_d ≤ (t₂/t₁)^{2(d-1)}`, so `√(n_d/n₁) ≤ (t₂/t₁)^d`. -/
theorem loewner_speed_limit [NeZero d] {S₁ S₂ : Mat d} (h₁ : S₁.PosDef) (h₂ : S₂.PosDef)
    (hle : loewnerLE S₁ S₂) :
    let n := eigUp (relStep (shapeOf S₁) (shapeOf S₂))
    let t₁ := volScale S₁
    let t₂ := volScale S₂
    (t₁ / t₂) ^ 2 ≤ n 0 ∧ n 0 ≤ n (Fin.rev 0) ∧ n (Fin.rev 0) ≤ (t₂ / t₁) ^ (2 * (d - 1)) ∧
      Real.sqrt (n (Fin.rev 0) / n 0) ≤ (t₂ / t₁) ^ d := by
  intro n t₁ t₂
  have hN : (relStep (shapeOf S₁) (shapeOf S₂)).PosDef := relShape_posDef h₁ h₂
  have hmono : Monotone n := eigUp_monotone hN.isHermitian
  have hprod : ∏ k, n k = 1 := (scale_shape_coords h₁ h₂).2
  have ht₁pos : 0 < t₁ := volScale_pos h₁
  have ht₂pos : 0 < t₂ := volScale_pos h₂
  have hc : (t₁ / t₂) ^ 2 ≤ n 0 := (loewner_iff_scale_shape h₁ h₂).1 hle
  set r := t₂ / t₁ with hr
  have hrpos : 0 < r := div_pos ht₂pos ht₁pos
  have hinv : t₁ / t₂ = r⁻¹ := by rw [hr, inv_div]
  rw [hinv] at hc
  have hn0 : 0 < n 0 := (by positivity : (0 : ℝ) < r⁻¹ ^ 2).trans_le hc
  have hlast := last_mul_pow_le_one hmono hprod (by positivity) hc
  have hmax : n (Fin.rev 0) ≤ r ^ (2 * (d - 1)) := by
    have hpow : (r⁻¹ ^ 2) ^ (d - 1) * r ^ (2 * (d - 1)) = 1 := by
      rw [← pow_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hrpos.ne')]
    calc n (Fin.rev 0) = n (Fin.rev 0) * (r⁻¹ ^ 2) ^ (d - 1) * r ^ (2 * (d - 1)) := by
          rw [mul_assoc, hpow, mul_one]
      _ ≤ 1 * r ^ (2 * (d - 1)) :=
          mul_le_mul_of_nonneg_right hlast (pow_nonneg hrpos.le _)
      _ = r ^ (2 * (d - 1)) := one_mul _
  refine ⟨by rw [hinv]; exact hc, hmono (Fin.zero_le _), hmax, ?_⟩
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hratio : n (Fin.rev 0) / n 0 ≤ (r ^ d) ^ 2 := by
    rw [div_le_iff₀ hn0]
    calc n (Fin.rev 0) ≤ r ^ (2 * (d - 1)) := hmax
      _ = (r ^ d) ^ 2 * r⁻¹ ^ 2 := by
          rw [← pow_mul, inv_pow]
          have : d * 2 = 2 * (d - 1) + 2 := by omega
          rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hrpos.ne'), mul_one]
      _ ≤ (r ^ d) ^ 2 * n 0 := mul_le_mul_of_nonneg_left hc (by positivity)
  calc Real.sqrt (n (Fin.rev 0) / n 0) ≤ Real.sqrt ((r ^ d) ^ 2) := Real.sqrt_le_sqrt hratio
    _ = r ^ d := Real.sqrt_sq (pow_nonneg hrpos.le _)

/-- The construction of the converse of clause (3), with everything it gives. -/
theorem speed_limit_converse_aux [NeZero d] {S₁ : Mat d} (h₁ : S₁.PosDef) {t₂ : ℝ} (ht₂ : 0 < t₂)
    {N : Mat d} (hN : N.PosDef) (hdet : N.det = 1) :
    let S₂ := t₂ ^ 2 • (msqrt (shapeOf S₁) * N * msqrt (shapeOf S₁))
    S₂.PosDef ∧ volScale S₂ = t₂ ∧ shapeOf S₂ = msqrt (shapeOf S₁) * N * msqrt (shapeOf S₁) ∧
      relStep (shapeOf S₁) (shapeOf S₂) = N := by
  intro S₂
  set A := shapeOf S₁ with hAdef
  have hA : A.PosDef := shapeOf_posDef h₁
  set K := msqrt A * N * msqrt A with hKdef
  have hK : K.PosDef := posDef_msqrt_conj hA hN
  have hKdet : K.det = 1 := by rw [hKdef, det_msqrt_conj hA, det_shapeOf h₁, hdet, one_mul]
  have ht2 : 0 < t₂ ^ 2 := by positivity
  have hS₂ : S₂.PosDef := hK.smul ht2
  have hvol : volScale S₂ = t₂ := by
    rw [volScale_smul ht2 hK, volScale_of_det_eq_one hKdet, mul_one, Real.sqrt_sq ht₂.le]
  have hshape : shapeOf S₂ = K := by rw [shapeOf_smul ht2 hK, shapeOf_of_det_eq_one hKdet]
  exact ⟨hS₂, hvol, hshape, by rw [hshape, hKdef, relStep_msqrt_mul hA]⟩

/-- **`lem:loewner-scale-shape`(3)**, the converse: for `t₂ ≥ t₁` and `N ∈ PD(d)` with `det N = 1`
and least eigenvalue at least `(t₁/t₂)²`, `Σ₂ := t₂² S₁^{1/2} N S₁^{1/2}` satisfies `Σ₁ ≤ Σ₂`,
`t(Σ₂) = t₂`, and has relative shape `N`. -/
theorem loewner_speed_limit_converse [NeZero d] {S₁ : Mat d} (h₁ : S₁.PosDef) (t₂ : ℝ)
    (ht : volScale S₁ ≤ t₂) (N : Mat d) (hN : N.PosDef) (hdet : N.det = 1)
    (hmin : (volScale S₁ / t₂) ^ 2 ≤ eigUp N 0) :
    let S₂ := t₂ ^ 2 • (msqrt (shapeOf S₁) * N * msqrt (shapeOf S₁))
    loewnerLE S₁ S₂ ∧ volScale S₂ = t₂ ∧ relStep (shapeOf S₁) (shapeOf S₂) = N := by
  intro S₂
  have ht₂ : 0 < t₂ := (volScale_pos h₁).trans_le ht
  obtain ⟨hS₂, hvol, -, hrel⟩ := speed_limit_converse_aux h₁ ht₂ hN hdet
  refine ⟨?_, hvol, hrel⟩
  rw [loewner_iff_scale_shape h₁ hS₂, hvol, hrel]
  exact hmin

/-- In the plane, for `N ∈ PD(2)` with `det N = 1` and `t₁, t₂ > 0`:
`δ ≤ 2√2 log(t₂/t₁)` exactly when `n₁ ≥ (t₁/t₂)²`. -/
theorem plane_delta_le_iff {N : Mat 2} (hN : N.PosDef) (hdet : N.det = 1) {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    Real.sqrt (Real.log (eigUp N 0) ^ 2 + Real.log (eigUp N 1) ^ 2) ≤
        2 * Real.sqrt 2 * Real.log (t₂ / t₁) ↔ (t₁ / t₂) ^ 2 ≤ eigUp N 0 := by
  have hprod : eigUp N 0 * eigUp N 1 = 1 := by
    rw [← Fin.prod_univ_two, prod_eigUp hN.isHermitian, hdet]
  have hn0 : 0 < eigUp N 0 := eigUp_pos hN 0
  have hn1 : 0 < eigUp N 1 := eigUp_pos hN 1
  have hlog1 : Real.log (eigUp N 1) = -Real.log (eigUp N 0) := by
    have := Real.log_mul hn0.ne' hn1.ne'
    rw [hprod, Real.log_one] at this
    linarith
  have hle : eigUp N 0 ≤ eigUp N 1 := eigUp_monotone hN.isHermitian (Fin.zero_le 1)
  have hn0le : eigUp N 0 ≤ 1 := by nlinarith
  have hlog0 : Real.log (eigUp N 0) ≤ 0 := Real.log_nonpos hn0.le hn0le
  have hδ : Real.sqrt (Real.log (eigUp N 0) ^ 2 + Real.log (eigUp N 1) ^ 2) =
      Real.sqrt 2 * (-Real.log (eigUp N 0)) := by
    rw [hlog1, neg_sq, ← two_mul, Real.sqrt_mul zero_le_two, ← abs_of_nonpos hlog0,
      Real.sqrt_sq_eq_abs]
  have hlogq : Real.log ((t₁ / t₂) ^ 2) = -(2 * Real.log (t₂ / t₁)) := by
    rw [Real.log_pow, ← inv_div, Real.log_inv]
    push_cast
    ring
  rw [hδ, ← Real.log_le_log_iff (by positivity) hn0, hlogq, mul_comm 2 (Real.sqrt 2), mul_assoc,
    mul_le_mul_iff_of_pos_left (Real.sqrt_pos.2 zero_lt_two)]
  constructor <;> intro h <;> linarith

/-- **`lem:loewner-scale-shape`(4)**, the plane: for `d = 2`, `δ(S₁, S₂) := ((log n₁)² +
(log n₂)²)^{1/2}` and `t₂ ≥ t₁`, the shapes of the `Σ₂ ≥ Σ₁` with `t(Σ₂) = t₂` are exactly the
`S ∈ PD(2)` with `det S = 1` and `δ(S₁, S) ≤ 2√2 log(t₂/t₁)`. -/
theorem loewner_plane_disc {S₁ : Mat 2} (h₁ : S₁.PosDef) (t₂ : ℝ) (ht : volScale S₁ ≤ t₂) :
    let δ : Mat 2 → Mat 2 → ℝ := fun A B =>
      Real.sqrt (Real.log (eigUp (relStep A B) 0) ^ 2 + Real.log (eigUp (relStep A B) 1) ^ 2)
    shapeOf '' {S₂ : Mat 2 | S₂.PosDef ∧ loewnerLE S₁ S₂ ∧ volScale S₂ = t₂} =
      {S : Mat 2 | S.PosDef ∧ S.det = 1 ∧
        δ (shapeOf S₁) S ≤ 2 * Real.sqrt 2 * Real.log (t₂ / volScale S₁)} := by
  intro δ
  have ht₁ : 0 < volScale S₁ := volScale_pos h₁
  have ht₂ : 0 < t₂ := ht₁.trans_le ht
  have hA : (shapeOf S₁).PosDef := shapeOf_posDef h₁
  ext S
  constructor
  · rintro ⟨S₂, ⟨hS₂, hle, hvol⟩, rfl⟩
    have hN := relShape_posDef h₁ hS₂
    have hdet : (relStep (shapeOf S₁) (shapeOf S₂)).det = 1 := by
      rw [det_relStep hA, det_shapeOf h₁, det_shapeOf hS₂, div_one]
    refine ⟨shapeOf_posDef hS₂, det_shapeOf hS₂, ?_⟩
    have hc := (loewner_iff_scale_shape h₁ hS₂).1 hle
    rw [hvol] at hc
    exact (plane_delta_le_iff hN hdet ht₁ ht₂).2 hc
  · rintro ⟨hS, hSdet, hδ⟩
    set N := relStep (shapeOf S₁) S with hNdef
    have hN : N.PosDef := (posDef_relStep_iff hA S).2 hS
    have hdet : N.det = 1 := by rw [hNdef, det_relStep hA, det_shapeOf h₁, hSdet, div_one]
    have hc := (plane_delta_le_iff hN hdet ht₁ ht₂).1 hδ
    obtain ⟨hS₂, hvol, -, hrel⟩ := speed_limit_converse_aux h₁ ht₂ hN hdet
    refine ⟨_, ⟨hS₂, ?_, hvol⟩, relStep_injective hA (hrel.trans hNdef)⟩
    exact (loewner_speed_limit_converse h₁ t₂ ht N hN hdet hc).1

end AffineHemigroup
