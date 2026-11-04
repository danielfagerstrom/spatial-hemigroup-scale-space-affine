/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ShapeAdapted

/-!
# The ordered spectrum: `eigUp_spec` (`lem:spectral-cones`' notation)

Blueprint: `blueprint/src/parts/05-wedges.tex`, the notation of `lem:spectral-cones` (wave 1,
group D, Q-0281). `eigUp X`, the roots of the characteristic polynomial sorted increasingly, is
for a symmetric `X` increasing, a rearrangement of Mathlib's `eigenvalues`, and its first and last
entries are the Rayleigh forms `λ_min(X)` and `λ_max(X)`. The rearrangement is built fibre by fibre
(`Equiv.ofFiberEquiv`), the two functions having the same multiset of values. Lean core only.
-/

namespace AffineHemigroup

open Matrix
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Two functions on a finite type with the same multiset of values differ by a permutation. -/
theorem exists_perm_of_map_univ_eq {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Equiv.Perm ι, f = g ∘ σ := by
  classical
  have hcard : ∀ c : ℝ, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have hc := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card_def, Finset.filter_val]
    convert hc using 3 <;> exact eq_comm
  let e : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hcard c)
  refine ⟨Equiv.ofFiberEquiv e, funext fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map e a).symm

/-- A unit eigenvector for every entry `λ↑_k` of the ordered spectrum. -/
theorem exists_unit_eigvec_eigUp {X : Mat d} (hX : X.IsHermitian) (k : Fin d) :
    ∃ v : Rd d, ‖v‖ = 1 ∧ lin X v = eigUp X k • v := by
  obtain ⟨i, hi⟩ := eigUp_mem_eigenvalues hX k
  have hn : ‖(hX.eigenvectorBasis i : Rd d)‖ = 1 := hX.eigenvectorBasis.orthonormal.norm_eq_one i
  have h : lin X (hX.eigenvectorBasis i) = hX.eigenvalues i • (hX.eigenvectorBasis i : Rd d) := by
    apply WithLp.ofLp_injective 2
    have h := hX.mulVec_eigenvectorBasis i
    rw [ofLp_lin, WithLp.ofLp_smul]
    exact h
  exact ⟨_, hn, by rw [h, hi]⟩

/-- **`λ_max(X) = λ↑_d(X)`** for symmetric `X` (`d ≥ 1`). -/
theorem lamMax_eq_eigUp_last [NeZero d] {X : Mat d} (hX : X.IsHermitian) :
    lamMax X = eigUp X (Fin.rev 0) := by
  have hup : ∀ x : Rd d, ⟪x, lin X x⟫ ≤ eigUp X (Fin.rev 0) * ‖x‖ ^ 2 := by
    intro x
    have h := quad_nonneg ((posSemidef_smul_one_sub_iff hX (eigUp X (Fin.rev 0))).2 le_rfl) x
    rw [quad_sub, quad_smul, quad_one] at h
    unfold quad at h
    linarith
  obtain ⟨v, hvn, hXv⟩ := exists_unit_eigvec_eigUp hX (Fin.rev 0)
  have hval : ⟪v, lin X v⟫ = eigUp X (Fin.rev 0) := by
    rw [hXv, inner_smul_right, real_inner_self_eq_norm_sq, hvn, one_pow, mul_one]
  have hup' : ∀ x : {x : Rd d // ‖x‖ = 1}, ⟪(x : Rd d), lin X x⟫ ≤ eigUp X (Fin.rev 0) := by
    intro x
    have h := hup x
    rwa [x.2, one_pow, mul_one] at h
  haveI : Nonempty {x : Rd d // ‖x‖ = 1} := ⟨⟨v, hvn⟩⟩
  unfold lamMax
  apply le_antisymm
  · exact ciSup_le hup'
  · have hb : BddAbove (Set.range fun x : {x : Rd d // ‖x‖ = 1} => ⟪(x : Rd d), lin X x⟫) :=
      ⟨eigUp X (Fin.rev 0), by rintro _ ⟨x, rfl⟩; exact hup' x⟩
    exact hval.symm.trans_le (le_ciSup hb ⟨v, hvn⟩)

/-- **The ordered spectrum**: for symmetric `X` (`d ≥ 1`), `λ↑(X)` is increasing, is a
rearrangement of Mathlib's eigenvalues, and its first and last entries are `λ_min(X)` and
`λ_max(X)`. Tagged with `lem:spectral-cones`, whose notation it fixes. -/
theorem eigUp_spec [NeZero d] {X : Mat d} (hX : X.IsHermitian) :
    Monotone (eigUp X) ∧ (∃ σ : Equiv.Perm (Fin d), eigUp X = hX.eigenvalues ∘ σ) ∧
      eigUp X 0 = lamMin X ∧ eigUp X (Fin.rev 0) = lamMax X := by
  refine ⟨eigUp_monotone hX, exists_perm_of_map_univ_eq ?_,
    (lamMin_eq_eigUp_zero hX).symm, (lamMax_eq_eigUp_last hX).symm⟩
  rw [eigUp_map_univ hX, hX.roots_charpoly_eq_eigenvalues]
  simp

end AffineHemigroup
