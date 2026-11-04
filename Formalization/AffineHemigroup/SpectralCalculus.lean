/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PathCondition
import AffineHemigroup.SimilaritySpectrum
import AffineHemigroup.InvariantOrders

/-!
# The spectral calculus of real symmetric matrices (§ 5.3's toolbox)

Toolbox of `lem:spectral-cones`, `lem:spectral-cones-products` and `thm:cone-orders` (wave 2,
group F, Q-0281): rearrangements (`sortUp`) and their partial sums; the ordered spectrum of
`U diag(w) Uᵀ` is the increasing rearrangement of `w`; every function of a symmetric matrix in the
continuous functional calculus is computed in *any* orthogonal diagonalization
(`cfc_udiag`, from the entrywise identity `W diag(l) = diag(w) W` for `W = VᵀU`), so that `log`,
`M^s` and `M^{1/2}` are read in the spectral form; `log` and `exp` are inverse between `Sym(d)` and
`PD(d)`; and `ℓ(M) = log λ↑(M)`. Lean core only.
-/

namespace AffineHemigroup

open Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-! ## Rearrangements -/

/-- `x↑` is increasing. -/
theorem sortUp_monotone (x : Fin d → ℝ) : Monotone (sortUp x) := Tuple.monotone_sort x

/-- An increasing vector is its own increasing rearrangement. -/
theorem sortUp_of_monotone {x : Fin d → ℝ} (hx : Monotone x) : sortUp x = x := by
  unfold sortUp
  rw [(Tuple.sort_eq_refl_iff_monotone).2 hx]
  rfl

/-- `(x ∘ σ)↑ = x↑`. -/
theorem sortUp_comp_perm (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    sortUp (x ∘ σ) = sortUp x :=
  Tuple.comp_perm_comp_sort_eq_comp_sort

/-- The increasing rearrangement is a rearrangement. -/
theorem exists_perm_sortUp (x : Fin d → ℝ) : ∃ σ : Equiv.Perm (Fin d), sortUp x = x ∘ σ :=
  ⟨Tuple.sort x, rfl⟩

/-- A vector with the multiset of values of `x` that is increasing is `x↑`. -/
theorem sortUp_eq_of_map {x v : Fin d → ℝ} (hv : Monotone v)
    (h : Multiset.map v Finset.univ.val = Multiset.map x Finset.univ.val) : sortUp x = v := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_univ_eq h
  rw [← sortUp_of_monotone hv, hσ, sortUp_comp_perm]

/-- `x↑` has the multiset of values of `x`. -/
theorem map_sortUp (x : Fin d → ℝ) :
    Multiset.map (sortUp x) Finset.univ.val = Multiset.map x Finset.univ.val := by
  obtain ⟨σ, hσ⟩ := exists_perm_sortUp x
  rw [hσ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- `∑ᵢ x↑ᵢ = ∑ᵢ xᵢ`. -/
theorem sum_sortUp (x : Fin d → ℝ) : ∑ i, sortUp x i = ∑ i, x i := by
  obtain ⟨σ, hσ⟩ := exists_perm_sortUp x
  rw [hσ]
  exact Equiv.sum_comp σ x

/-- `(g ∘ x)↑ = g ∘ x↑` for `g` monotone. -/
theorem sortUp_comp_monotone {g : ℝ → ℝ} (hg : Monotone g) (x : Fin d → ℝ) :
    sortUp (g ∘ x) = g ∘ sortUp x := by
  obtain ⟨σ, hσ⟩ := exists_perm_sortUp x
  refine sortUp_eq_of_map (hg.comp (sortUp_monotone x)) ?_
  rw [hσ, ← Function.comp_assoc, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- `s_k(x)` of an increasing `x` is the sum of its first `k` entries. -/
theorem partialSumUp_of_monotone {x : Fin d → ℝ} (hx : Monotone x) (k : ℕ) :
    partialSumUp k x = ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), x i := by
  rw [partialSumUp, sortUp_of_monotone hx]

/-- `s_k((x ∘ σ)) = s_k(x)`. -/
theorem partialSumUp_comp_perm (k : ℕ) (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    partialSumUp k (x ∘ σ) = partialSumUp k x := by
  rw [partialSumUp, partialSumUp, sortUp_comp_perm]

/-- `s_d(x) = ∑ᵢ xᵢ`. -/
theorem partialSumUp_card (x : Fin d → ℝ) : partialSumUp d x = ∑ i, x i := by
  rw [partialSumUp, ← sum_sortUp]
  congr 1
  ext i
  simp

/-- The sum of the `k` largest entries of `x` and the sum of its `d - k` smallest make the total:
`∑_{i < k} x(rev i) + ∑_{i < d-k} x i = ∑ x`. -/
theorem sum_filter_rev_add (x : Fin d → ℝ) {k : ℕ} (hk : k ≤ d) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), x (Fin.rev i) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < d - k), x i = ∑ i, x i := by
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), x (Fin.rev i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < d - k), x i := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
    have := i.2
    by_cases h : (i : ℕ) < d - k
    · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_pos (by omega), if_pos (by omega)]
  rw [h1, add_comm, Finset.sum_filter_add_sum_filter_not]

/-! ## Functions of a symmetric matrix in any orthogonal diagonalization -/

/-- **Two orthogonal diagonalizations give the same function of the matrix**: if
`U diag(l) Uᵀ = V diag(w) Vᵀ` with `U`, `V` orthogonal, then `U diag(f ∘ l) Uᵀ = V diag(f ∘ w) Vᵀ`
for every `f`. Entrywise, `W = VᵀU` has `W_ij l_j = w_i W_ij`, so `W_ij ≠ 0` forces `l_j = w_i`. -/
theorem udiag_comp_eq {U V : Mat d} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) {l w : Fin d → ℝ}
    (h : udiag U l = udiag V w) (f : ℝ → ℝ) : udiag U (f ∘ l) = udiag V (f ∘ w) := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  have hV' : Vᵀ * V = 1 := mul_eq_one_comm.1 hV
  have hW : (Vᵀ * U) * diagonal l = diagonal w * (Vᵀ * U) := by
    have h2 := congrArg (fun N => Vᵀ * N * U) h
    simp only [udiag] at h2
    calc (Vᵀ * U) * diagonal l = Vᵀ * (U * diagonal l * Uᵀ) * U := by
          simp only [Matrix.mul_assoc, hU', Matrix.mul_one]
      _ = Vᵀ * (V * diagonal w * Vᵀ) * U := h2
      _ = diagonal w * (Vᵀ * U) := by
          simp only [← Matrix.mul_assoc, hV', Matrix.one_mul]
  have hWf : (Vᵀ * U) * diagonal (f ∘ l) = diagonal (f ∘ w) * (Vᵀ * U) := by
    ext i j
    have h3 := congrFun (congrFun hW i) j
    simp only [mul_diagonal, diagonal_mul, Function.comp_apply] at h3 ⊢
    by_cases h0 : (Vᵀ * U) i j = 0
    · rw [h0, zero_mul, mul_zero]
    · have hlw : l j = w i := by
        have h4 : (Vᵀ * U) i j * (l j - w i) = 0 := by rw [mul_sub]; linarith
        have := (mul_eq_zero.1 h4).resolve_left h0
        linarith
      rw [hlw, mul_comm]
  calc udiag U (f ∘ l) = V * ((Vᵀ * U) * diagonal (f ∘ l)) * Uᵀ := by
        simp only [udiag, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    _ = V * (diagonal (f ∘ w) * (Vᵀ * U)) * Uᵀ := by rw [hWf]
    _ = udiag V (f ∘ w) := by
        simp only [udiag, Matrix.mul_assoc, hU, Matrix.mul_one]

/-- **`f(U diag(w) Uᵀ) = U diag(f ∘ w) Uᵀ`** in the continuous functional calculus, for every
orthogonal `U`. -/
theorem cfc_udiag {V : Mat d} (hV : V * Vᵀ = 1) (w : Fin d → ℝ) (f : ℝ → ℝ) :
    cfc f (udiag V w) = udiag V (f ∘ w) := by
  have hA := udiag_isHermitian V w
  obtain ⟨hU, hAU⟩ := spectral_udiag hA
  have h1 : cfc f (udiag V w) =
      udiag (hA.eigenvectorUnitary : Mat d) (f ∘ hA.eigenvalues) := by
    rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [udiag, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      Function.comp_def]
  rw [h1]
  exact udiag_comp_eq hU hV hAU.symm f

/-- `log(U diag(w) Uᵀ) = U diag(log w) Uᵀ`. -/
theorem mlog_udiag {V : Mat d} (hV : V * Vᵀ = 1) (w : Fin d → ℝ) :
    mlog (udiag V w) = udiag V (fun i => Real.log (w i)) :=
  cfc_udiag hV w Real.log

/-- `(U diag(w) Uᵀ)^s = U diag(wˢ) Uᵀ` for `w ≥ 0`. -/
theorem mrpow_udiag {V : Mat d} (hV : V * Vᵀ = 1) {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) (s : ℝ) :
    mrpow (udiag V w) s = udiag V (fun i => w i ^ s) := by
  have h0 : (0 : Mat d) ≤ udiag V w := nonneg_of_posSemidef ((udiag_posSemidef_iff hV w).2 hw)
  unfold mrpow
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real h0]
  exact cfc_udiag hV w _

/-- `(U diag(w) Uᵀ)^{1/2} = U diag(√w) Uᵀ` for `w ≥ 0`. -/
theorem msqrt_udiag {V : Mat d} (hV : V * Vᵀ = 1) {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) :
    msqrt (udiag V w) = udiag V (fun i => Real.sqrt (w i)) := by
  refine CFC.sqrt_unique ?_ (nonneg_of_posSemidef
    ((udiag_posSemidef_iff hV _).2 fun i => Real.sqrt_nonneg _))
  rw [udiag_mul hV]
  congr 1
  funext i
  exact Real.mul_self_sqrt (hw i)

/-! ## The ordered spectrum -/

/-- `λ↑` reads only the characteristic polynomial. -/
theorem eigUp_congr_charpoly {X Y : Mat d} (h : X.charpoly = Y.charpoly) : eigUp X = eigUp Y := by
  unfold eigUp
  rw [h]

/-- **`λ↑(AB) = λ↑(BA)`**: the characteristic polynomial of `AB` is that of `BA`. -/
theorem eigUp_mul_comm (A B : Mat d) : eigUp (A * B) = eigUp (B * A) :=
  eigUp_congr_charpoly (Matrix.charpoly_mul_comm A B)

/-- `λ↑(QXQᵀ) = λ↑(X)` for `Q` orthogonal. -/
theorem eigUp_conj_orth {Q : Mat d} (hQ : Q * Qᵀ = 1) (X : Mat d) :
    eigUp (Q * X * Qᵀ) = eigUp X := by
  rw [eigUp_mul_comm, ← Matrix.mul_assoc, transpose_mul_self_of_mul_transpose hQ, Matrix.one_mul]

/-- **`λ↑(U diag(w) Uᵀ) = w↑`.** -/
theorem eigUp_udiag {V : Mat d} (hV : V * Vᵀ = 1) (w : Fin d → ℝ) :
    eigUp (udiag V w) = sortUp w :=
  eigUp_eq_of_roots (sortUp_monotone w)
    (by rw [map_sortUp]; exact (roots_charpoly_conj_diagonal hV w).symm)

/-- `λ↑(diag w) = w↑`. -/
theorem eigUp_diagonal (w : Fin d → ℝ) : eigUp (diagonal w) = sortUp w := by
  have h := eigUp_udiag (V := 1) (by simp) w
  simpa [udiag] using h

/-- `λ↑(cX) = c λ↑(X)` for `c ≥ 0` and symmetric `X`. -/
theorem eigUp_smul {c : ℝ} (hc : 0 ≤ c) {X : Mat d} (hX : X.IsHermitian) :
    eigUp (c • X) = c • eigUp X := by
  have h := eigUp_act_smul_orth (Real.sqrt c) (Q := 1) (by simp) hX
  rw [act_smul_left, Real.sq_sqrt hc] at h
  simpa using h

/-- `λ↑(0) = 0`. -/
theorem eigUp_zero : eigUp (0 : Mat d) = 0 := by
  have h := eigUp_diagonal (d := d) 0
  rw [show diagonal (0 : Fin d → ℝ) = 0 by ext i j; simp [diagonal_apply]] at h
  rw [h, sortUp_of_monotone (fun _ _ _ => le_rfl)]

/-- The spectral form `X = V diag(λ↑(X)) Vᵀ` as a `udiag`. -/
theorem exists_udiag_eigUp {X : Mat d} (hX : X.IsHermitian) :
    ∃ V : Mat d, V * Vᵀ = 1 ∧ X = udiag V (eigUp X) := by
  obtain ⟨V, hV, h⟩ := exists_orth_diag_eigUp hX
  exact ⟨V, hV, h⟩

/-! ## `exp` and `log` between `Sym(d)` and `PD(d)` -/

/-- `log M` is symmetric. -/
theorem mlog_isHermitian (M : Mat d) : (mlog M).IsHermitian := by
  unfold mlog
  exact (cfc_predicate Real.log M : IsSelfAdjoint _)

/-- `e^{log M} = M` for `M ∈ PD(d)`. -/
theorem mexp_mlog {M : Mat d} (hM : M.PosDef) : mexp (mlog M) = M := by
  obtain ⟨V, hV, hMV⟩ := exists_udiag_eigUp hM.isHermitian
  have hpos := eigUp_pos hM
  rw [hMV, mlog_udiag hV, mexp_udiag hV]
  congr 1
  funext i
  exact Real.exp_log (hpos i)

/-- `log e^X = X` for symmetric `X`. -/
theorem mlog_mexp {X : Mat d} (hX : X.IsHermitian) : mlog (mexp X) = X := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hX
  rw [hXV, mexp_udiag hV, mlog_udiag hV]
  congr 1
  funext i
  exact Real.log_exp _

/-- `e^X = e^Y` for symmetric `X`, `Y` forces `X = Y`. -/
theorem mexp_injOn {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : mexp X = mexp Y) : X = Y := by
  rw [← mlog_mexp hX, ← mlog_mexp hY, h]

/-- `λ↑(e^X) = e^{λ↑(X)}` for symmetric `X`. -/
theorem eigUp_mexp {X : Mat d} (hX : X.IsHermitian) :
    eigUp (mexp X) = fun i => Real.exp (eigUp X i) := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hX
  conv_lhs => rw [hXV, mexp_udiag hV, eigUp_udiag hV]
  exact sortUp_of_monotone fun i j hij => Real.exp_le_exp.2 (eigUp_monotone hX hij)

/-- **`ℓ(M) = log λ↑(M)`** for `M ∈ PD(d)`. -/
theorem logSpec_eq {M : Mat d} (hM : M.PosDef) :
    logSpec M = fun i => Real.log (eigUp M i) := by
  obtain ⟨V, hV, hMV⟩ := exists_udiag_eigUp hM.isHermitian
  have hpos := eigUp_pos hM
  unfold logSpec
  conv_lhs => rw [hMV, mlog_udiag hV, eigUp_udiag hV]
  exact sortUp_of_monotone fun i j hij =>
    Real.log_le_log (hpos i) (eigUp_monotone hM.isHermitian hij)

/-- `ℓ(M)` is increasing. -/
theorem logSpec_monotone {M : Mat d} (hM : M.PosDef) : Monotone (logSpec M) := by
  rw [logSpec_eq hM]
  exact fun i j hij => Real.log_le_log (eigUp_pos hM i) (eigUp_monotone hM.isHermitian hij)

/-- `ℓ(e^X) = λ↑(X)` for symmetric `X`. -/
theorem logSpec_mexp {X : Mat d} (hX : X.IsHermitian) : logSpec (mexp X) = eigUp X := by
  unfold logSpec
  rw [mlog_mexp hX]

/-- `M^s = e^{s log M}` for `M ∈ PD(d)`. -/
theorem mrpow_eq_mexp {M : Mat d} (hM : M.PosDef) (s : ℝ) :
    mrpow M s = mexp (s • mlog M) := by
  obtain ⟨V, hV, hMV⟩ := exists_udiag_eigUp hM.isHermitian
  have hpos := eigUp_pos hM
  rw [hMV, mrpow_udiag hV (fun i => (hpos i).le), mlog_udiag hV]
  have : s • udiag V (fun i => Real.log (eigUp M i)) =
      udiag V (fun i => s * Real.log (eigUp M i)) := by
    rw [show (fun i => s * Real.log (eigUp M i)) = s • fun i => Real.log (eigUp M i) from rfl,
      udiag, udiag, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [this, mexp_udiag hV]
  congr 1
  funext i
  rw [Real.rpow_def_of_pos (hpos i), mul_comm]

/-- `M^{1/2} = e^{½ log M}` for `M ∈ PD(d)`. -/
theorem msqrt_eq_mexp {M : Mat d} (hM : M.PosDef) :
    msqrt M = mexp ((1 / 2 : ℝ) • mlog M) := by
  obtain ⟨V, hV, hMV⟩ := exists_udiag_eigUp hM.isHermitian
  have hpos := eigUp_pos hM
  rw [← mrpow_eq_mexp hM, hMV, mrpow_udiag hV (fun i => (hpos i).le),
    msqrt_udiag hV (fun i => (hpos i).le)]
  congr 1
  funext i
  rw [Real.sqrt_eq_rpow]

end AffineHemigroup
