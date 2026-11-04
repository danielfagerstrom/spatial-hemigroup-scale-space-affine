/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SpectralCalculus
import AffineHemigroup.Interfaces

/-!
# `lem:spectral-cones-products`: the logarithmic spectrum of a product

Blueprint: `blueprint/src/parts/05-wedges.tex`, `lem:spectral-cones-products` (wave 2, group F,
Q-0281). For `M, N ∈ PD(d)`, `ℓ(M^{1/2}NM^{1/2}) ≺ ℓ(M) + ℓ(N)`. The partial sums of the largest
entries are ledger **A9** (`gelfand_naimark_logMajorized`, the weak form, read with `λ(MN)` as
`λ↑(MN) = λ↑(M^{1/2}NM^{1/2})`); the equality of the totals is `det(M^{1/2}NM^{1/2}) = det M det N`,
proved here; and the module's `≺`, which reads the partial sums of the smallest entries, follows by
subtracting from the totals. `#print axioms`: A9 and Lean core.
-/

namespace AffineHemigroup

open Matrix

variable {d : ℕ}

/-- **`λ(MN)` is the spectrum of `M^{1/2}NM^{1/2}`**: the characteristic polynomial of `MN` is that
of `M^{1/2}(M^{1/2}N)`, hence of `(M^{1/2}N)M^{1/2}`. -/
theorem eigUp_mul_eq_msqrt_conj {M : Mat d} (hM : M.PosSemidef) (N : Mat d) :
    eigUp (M * N) = eigUp (msqrt M * N * msqrt M) := by
  conv_lhs => rw [← msqrt_mul_self hM]
  rw [Matrix.mul_assoc, eigUp_mul_comm]

/-- The total of `ℓ(M^{1/2}NM^{1/2})` is that of `ℓ(M) + ℓ(N)`: `det(M^{1/2}NM^{1/2}) = det M det N`. -/
theorem sum_logSpec_msqrt_conj {M N : Mat d} (hM : M.PosDef) (hN : N.PosDef) :
    ∑ i, logSpec (msqrt M * N * msqrt M) i = ∑ i, (logSpec M + logSpec N) i := by
  have hP := posDef_msqrt_conj hM hN
  have hlog : ∀ {A : Mat d}, A.PosDef → ∑ i, logSpec A i = Real.log A.det := fun {A} hA => by
    rw [logSpec_eq hA, ← Real.log_prod (fun i _ => (eigUp_pos hA i).ne'), prod_eigUp hA.isHermitian]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [hlog hP, hlog hM, hlog hN, det_msqrt_conj hM, Real.log_mul hM.det_pos.ne' hN.det_pos.ne']

/-- **`lem:spectral-cones-products`** (`lem:spectral-cones`(2)): for `M, N ∈ PD(d)`,
`ℓ(M^{1/2}NM^{1/2}) ≺ ℓ(M) + ℓ(N)`. Spends ledger A9 for the partial sums; the totals are a
determinant. -/
theorem logSpec_product_majorized (_hd : 1 ≤ d) {M N : Mat d} (hM : M.PosDef) (hN : N.PosDef) :
    IsMajorized (logSpec (msqrt M * N * msqrt M)) (logSpec M + logSpec N) := by
  set P := msqrt M * N * msqrt M with hPdef
  have hP : P.PosDef := posDef_msqrt_conj hM hN
  have hmP := logSpec_monotone hP
  have hmMN : Monotone (logSpec M + logSpec N) := (logSpec_monotone hM).add (logSpec_monotone hN)
  have htot := sum_logSpec_msqrt_conj hM hN
  have htop : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), logSpec P (Fin.rev i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
          (logSpec M + logSpec N) (Fin.rev i) := by
    intro k hk hkd
    have h := gelfand_naimark_logMajorized hM hN k hk hkd
    rw [eigUp_mul_eq_msqrt_conj hM.posSemidef N] at h
    simpa only [logSpec_eq hP, logSpec_eq hM, logSpec_eq hN, Pi.add_apply] using h
  refine ⟨fun k hk hkd => ?_, ?_⟩
  · rw [partialSumUp_of_monotone hmP, partialSumUp_of_monotone hmMN]
    have h1 := sum_filter_rev_add (logSpec P) (k := d - k) (by omega)
    have h2 := sum_filter_rev_add (logSpec M + logSpec N) (k := d - k) (by omega)
    rw [Nat.sub_sub_self hkd.le] at h1 h2
    have h3 := htop (d - k) (by omega) (by omega)
    linarith
  · rw [partialSumUp_card, partialSumUp_card]
    exact htot

end AffineHemigroup
