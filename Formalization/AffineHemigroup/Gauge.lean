/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Scheme
import Mathlib.LinearAlgebra.Matrix.Permutation
import AffineHemigroup.MatrixCalculus

/-!
# `lem:affine-gauge` — the affine gauge is a constant

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:affine-gauge`. Lean core only.

## The route

The blueprint's: `H := h(I)` commutes with every orthogonal matrix, so the sign changes
`diag(1, …, -1, …, 1)` make it diagonal and the transpositions make its diagonal constant; then
`h(Σ) = Σ^{1/2} h(I) Σ^{1/2}`. The first section is the calculus of the square root `Σ^{1/2}` and
of `O(d)` inside `GL(d)` that this proof and the ray column (`prop:gw-ray-families`(3)) read.
-/

namespace AffineHemigroup

open Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-! ## The square root of a positive semidefinite matrix, and `O(d)` -/

/-- `Σ^{1/2} Σ^{1/2} = Σ` for `Σ ∈ PSD(d)`. -/
theorem msqrt_mul_self {S : Mat d} (hS : S.PosSemidef) : msqrt S * msqrt S = S :=
  CFC.sqrt_mul_sqrt_self S (nonneg_of_posSemidef hS)

/-- `Σ^{1/2}` is symmetric. -/
theorem msqrt_transpose (S : Mat d) : (msqrt S)ᵀ = msqrt S := by
  have h := (CFC.sqrt_nonneg S).isSelfAdjoint
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- `Σ^{1/2} ∈ GL(d)` for `Σ ∈ PD(d)`. -/
theorem msqrt_mem_glSet {S : Mat d} (hS : S.PosDef) : msqrt S ∈ glSet d := by
  change IsUnit (msqrt S).det
  have h1 : (msqrt S).det * (msqrt S).det = S.det := by
    rw [← det_mul, msqrt_mul_self hS.posSemidef]
  have h2 : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit
  rw [← h1] at h2
  exact isUnit_of_mul_isUnit_left h2

/-- `Σ^{1/2} · I = Σ` for `Σ ∈ PSD(d)`. -/
theorem act_msqrt_one {S : Mat d} (hS : S.PosSemidef) : act (msqrt S) 1 = S := by
  rw [act, mul_one, msqrt_transpose, msqrt_mul_self hS]

/-- A matrix with `A Aᵀ = I` is invertible. -/
theorem mem_glSet_of_mul_transpose {A : Mat d} (h : A * Aᵀ = 1) : A ∈ glSet d := by
  change IsUnit A.det
  have : A.det * Aᵀ.det = 1 := by rw [← det_mul, h, det_one]
  exact isUnit_iff_exists_inv.2 ⟨_, this⟩

/-- `O(d) ⊆ GL(d)`. -/
theorem orthSet_subset_glSet : orthSet d ⊆ glSet d := fun _ hQ =>
  mem_glSet_of_mul_transpose ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ)

/-- The dilation `λI` acts by `λ²`: `(λI) · Σ = λ² Σ`. -/
theorem act_smul_one (lam : ℝ) (S : Mat d) : act (lam • (1 : Mat d)) S = (lam ^ 2) • S := by
  simp only [act, transpose_smul, transpose_one, smul_mul_assoc, Matrix.one_mul, Matrix.mul_one,
    mul_smul_comm, smul_smul, sq]

/-! ## A matrix commuting with `O(d)` is a multiple of `I` -/

/-- The sign change `diag(1, …, -1, …, 1)`, `-1` at `i`. -/
private def signFlip (i : Fin d) : Mat d := diagonal fun j => if j = i then -1 else 1

private theorem signFlip_mem (i : Fin d) : signFlip i ∈ orthSet d := by
  change signFlip i ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff, signFlip, diagonal_transpose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  ext j
  split_ifs <;> norm_num

private theorem perm_mem (σ : Equiv.Perm (Fin d)) : σ.permMatrix ℝ ∈ orthSet d := by
  change σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff, transpose_permMatrix, ← permMatrix_mul, inv_mul_cancel,
    permMatrix_one]

/-- **A matrix fixed by the action of `O(d)` is a multiple of `I`**: if `Q H Qᵀ = H` for every
`Q ∈ O(d)`, then `H = H₀₀ I` (for `d ≥ 1`). -/
theorem eq_smul_one_of_orth_invariant [NeZero d] {H : Mat d}
    (hH : ∀ Q ∈ orthSet d, act Q H = H) : H = H 0 0 • (1 : Mat d) := by
  have hoff : ∀ j k : Fin d, j ≠ k → H j k = 0 := by
    intro j k hjk
    have h := congrFun (congrFun (hH _ (signFlip_mem j)) j) k
    simp only [act, signFlip, diagonal_transpose, diagonal_mul, mul_diagonal,
      if_neg (Ne.symm hjk), if_true, mul_one, neg_mul, one_mul] at h
    linarith
  have hdiag : ∀ k : Fin d, H k k = H 0 0 := by
    intro k
    have h := congrFun (congrFun (hH _ (perm_mem (Equiv.swap 0 k))) 0) 0
    simp only [act, transpose_permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, id, Equiv.Perm.inv_def, Equiv.symm_symm,
      Equiv.swap_apply_left] at h
    exact h
  ext j k
  rw [Matrix.smul_apply, one_apply, smul_eq_mul]
  split_ifs with hjk
  · subst hjk
    rw [hdiag, mul_one]
  · rw [hoff j k hjk, mul_zero]

/-! ## `lem:affine-gauge` -/

/-- **`lem:affine-gauge`**: a map `h : PD(d) → PD(d)` with `h(AΣAᵀ) = A h(Σ) Aᵀ` for every
`A ∈ GL(d)` is `h(Σ) = cΣ` for some `c > 0`. -/
theorem affine_gauge (h : Mat d → Mat d) (hpd : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hcov : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → h (act A S) = act A (h S)) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : Mat d, S.PosDef → h S = c • S := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, one_pos, fun S _ => ?_⟩
    ext i
    exact i.elim0
  haveI : NeZero d := ⟨hd.ne'⟩
  set H := h 1 with hHdef
  have hHpd : H.PosDef := hpd 1 PosDef.one
  have hinv : ∀ Q ∈ orthSet d, act Q H = H := by
    intro Q hQ
    have := hcov Q (orthSet_subset_glSet hQ) 1 PosDef.one
    rw [act_orth_one hQ] at this
    exact this.symm
  have hH := eq_smul_one_of_orth_invariant hinv
  refine ⟨H 0 0, hHpd.diag_pos, fun S hS => ?_⟩
  have h1 := hcov (msqrt S) (msqrt_mem_glSet hS) 1 PosDef.one
  rw [act_msqrt_one hS.posSemidef, ← hHdef, hH] at h1
  rw [h1, act, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, msqrt_transpose,
    msqrt_mul_self hS.posSemidef]

/-- **`lem:affine-gauge`**, last sentence: on the isotropic slice the dilation `λI` acts by
`s ↦ λ² s`. -/
theorem affine_gauge_slice (lam s : ℝ) (_hlam : 0 < lam) (_hs : 0 < s) :
    act (lam • (1 : Mat d)) (s • 1) = (lam ^ 2 * s) • (1 : Mat d) := by
  rw [act_smul_one, smul_smul]

end AffineHemigroup
