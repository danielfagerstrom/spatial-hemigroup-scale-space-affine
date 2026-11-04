/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableOrderPSD

/-!
# `lem:path-condition-orders`: orders with the path condition

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:path-condition-orders`
(`thm:cascade-infinitely-divisible`(3), split; wave 2, group C, Q-0281). Lean core only.

## The route

(a) and (b) are the blueprint's. For (c) the power `M^s` is Mathlib's `CFC.rpow`, read in the
spectral form `M^s = U diag(m^s) Uᵀ` (`mrpow_eq_spectral`), from which `s ↦ M^s` is continuous
and `M^a M^b = M^{a+b}`. The monotonicity of the chain `ζ(s) = Σ^{1/2}M^sΣ^{1/2}` does **not**
go through the orthogonal conjugacy of isospectral symmetric matrices, as the blueprint's proof
does: with `B := Σ^{1/2}M^{s/2}` one has `ζ(s) = BBᵀ` and `ζ(t) = B M^{t-s} Bᵀ`, so the relative
step of `(ζ(s), ζ(t))` is `Q M^{t-s} Qᵀ` with `Q := ζ(s)^{-1/2}B`, and `QQᵀ = I` is the relative
step of `ζ(s)` to itself. The three step sets are handled through the matrices
`U diag(w) Uᵀ` with `U` orthogonal (`udiag`), whose least Rayleigh quotient is the least `wᵢ`.
-/

namespace AffineHemigroup

open Matrix Set Real
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## `U diag(w) Uᵀ` with `U` orthogonal -/

/-- **`U diag(w) Uᵀ`**. -/
def udiag (U : Mat d) (w : Fin d → ℝ) : Mat d := U * diagonal w * Uᵀ

theorem udiag_transpose (U : Mat d) (w : Fin d → ℝ) : (udiag U w)ᵀ = udiag U w := by
  simp only [udiag, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

theorem udiag_isHermitian (U : Mat d) (w : Fin d → ℝ) : (udiag U w).IsHermitian := by
  change (udiag U w)ᴴ = udiag U w
  rw [conjTranspose_eq_transpose_of_trivial, udiag_transpose]

theorem udiag_mul {U : Mat d} (hU : U * Uᵀ = 1) (w w' : Fin d → ℝ) :
    udiag U w * udiag U w' = udiag U (w * w') := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  simp only [udiag]
  rw [show U * diagonal w * Uᵀ * (U * diagonal w' * Uᵀ) =
    U * (diagonal w * (Uᵀ * U) * diagonal w') * Uᵀ by simp only [Matrix.mul_assoc], hU',
    Matrix.mul_one, diagonal_mul_diagonal]
  rfl

theorem udiag_one {U : Mat d} (hU : U * Uᵀ = 1) : udiag U (fun _ => 1) = 1 := by
  rw [udiag, diagonal_one, Matrix.mul_one, hU]

theorem mem_glSet_of_orth {U : Mat d} (hU : U * Uᵀ = 1) : U ∈ glSet d :=
  mem_glSet_of_mul_transpose hU

theorem udiag_posDef_iff {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) :
    (udiag U w).PosDef ↔ ∀ i, 0 < w i := by
  change (act U (diagonal w)).PosDef ↔ _
  rw [posDef_act_iff (mem_glSet_of_orth hU), posDef_diagonal_iff]

theorem udiag_posSemidef_iff {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) :
    (udiag U w).PosSemidef ↔ ∀ i, 0 ≤ w i := by
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 (mem_glSet_of_orth hU)
  have h := hUu.posSemidef_star_right_conjugate_iff (x := diagonal w)
  rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  change (U * diagonal w * Uᵀ).PosSemidef ↔ _
  rw [h, posSemidef_diagonal_iff]

theorem det_udiag {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) :
    (udiag U w).det = ∏ i, w i := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  rw [udiag, det_mul, det_mul, det_diagonal, mul_comm U.det, mul_assoc, ← det_mul, hU, det_one,
    mul_one]

theorem trace_udiag {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) :
    (udiag U w).trace = ∑ i, w i := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  rw [udiag, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU', Matrix.one_mul, trace_diagonal]

/-- `⟨y, U diag(w) Uᵀ y⟩ = ∑ wᵢ ((Uᵀy)ᵢ)²`, and `∑ ((Uᵀy)ᵢ)² = |y|²`. -/
theorem sum_sq_lin_transpose {U : Mat d} (hU : U * Uᵀ = 1) (y : Rd d) :
    ∑ i, ((lin Uᵀ y) i) ^ 2 = ‖y‖ ^ 2 := by
  have h := quad_orth_diag U (fun _ => 1) y
  rw [diagonal_one, Matrix.mul_one, hU, quad_one] at h
  simpa using h.symm

/-- A lower bound for every `wᵢ` bounds `λ_min(U diag(w) Uᵀ)` below. -/
theorem le_lamMin_udiag [NeZero d] {U : Mat d} (hU : U * Uᵀ = 1) {w : Fin d → ℝ} {c : ℝ}
    (hc : ∀ i, c ≤ w i) : c ≤ lamMin (udiag U w) := by
  haveI : Nonempty {x : Rd d // ‖x‖ = 1} := by
    obtain ⟨v, hv, -⟩ := exists_unit_eigvec_eigUp_zero (udiag_isHermitian U w)
    exact ⟨⟨v, hv⟩⟩
  unfold lamMin
  refine le_ciInf fun x => ?_
  have hq := quad_orth_diag U w (x : Rd d)
  have hn := sum_sq_lin_transpose hU (x : Rd d)
  rw [x.2, one_pow] at hn
  change c ≤ quad (udiag U w) x
  rw [udiag, hq]
  calc c = ∑ i, c * ((lin Uᵀ (x : Rd d)) i) ^ 2 := by rw [← Finset.mul_sum, hn, mul_one]
    _ ≤ ∑ i, w i * ((lin Uᵀ (x : Rd d)) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- `λ_min(U diag(w) Uᵀ) ≤ wᵢ`. -/
theorem lamMin_udiag_le [NeZero d] {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (i : Fin d) :
    lamMin (udiag U w) ≤ w i := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  set e : Rd d := EuclideanSpace.single i 1
  set x : Rd d := lin U e
  have hx : lin Uᵀ x = e := by
    simp only [x, ← mul_apply_eq_comp, ← lin_mul, hU', lin_one]
    rfl
  have hsq : ∀ j, (e j) ^ 2 = if j = i then 1 else 0 := fun j => by
    simp only [e, PiLp.single_apply]
    split_ifs <;> norm_num
  have hn : ‖x‖ = 1 := by
    have h := sum_sq_lin_transpose hU x
    rw [hx] at h
    simp only [hsq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h0 := norm_nonneg x
    nlinarith
  have h := lamMin_le_inner (udiag_isHermitian U w) hn
  change lamMin (udiag U w) ≤ quad (udiag U w) x at h
  rw [udiag, quad_orth_diag, hx] at h
  simpa [udiag, hsq] using h

/-- **`M^s` in the spectral form**: `M^s = U diag(m^s) Uᵀ` for `M ∈ PSD(d)`, `U` the eigenvector
matrix and `m` the eigenvalues. -/
theorem mrpow_eq_spectral {M : Mat d} (hM : M.PosSemidef) (s : ℝ) :
    mrpow M s = udiag (hM.isHermitian.eigenvectorUnitary : Mat d)
      (fun i => hM.isHermitian.eigenvalues i ^ s) := by
  have h0 : (0 : Mat d) ≤ M := nonneg_of_posSemidef hM
  unfold mrpow udiag
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real h0, hM.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, Function.comp_def]

/-- The spectral decomposition `M = U diag(m) Uᵀ` with `U` orthogonal, in the `udiag` form. -/
theorem spectral_udiag {M : Mat d} (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Mat d) * (hM.eigenvectorUnitary : Mat d)ᵀ = 1 ∧
      M = udiag (hM.eigenvectorUnitary : Mat d) hM.eigenvalues := by
  have hstar : star (hM.eigenvectorUnitary : Mat d) = (hM.eigenvectorUnitary : Mat d)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨by rw [← hstar]; exact Unitary.coe_mul_star_self _, ?_⟩
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simp at h
  rw [udiag, ← hstar]
  exact h

/-! ## (a) and (b): the Loewner and the ray order on `PSD(d)` -/

/-- **`lem:path-condition-orders`(a)**: the Loewner order on `PSD(d)`; the chain
`ζ(s) = Σ + s(Σ' - Σ)`. -/
theorem chain_loewner (S S' : Mat d) (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (hle : loewnerLE S S') :
    IsWChain (psdSet d) loewnerLE (fun s => S + s • (S' - S)) S S' := by
  refine ⟨by fun_prop, fun s hs => ?_, fun s _ t _ hst => ?_, by simp, by simp⟩
  · change (S + s • (S' - S)).PosSemidef
    rw [show S + s • (S' - S) = (1 - s) • S + s • S' by
      rw [smul_sub, sub_smul, one_smul]; abel]
    exact (hS.smul (by linarith [hs.2])).add (hS'.smul hs.1)
  · unfold loewnerLE
    rw [show S + t • (S' - S) - (S + s • (S' - S)) = (t - s) • (S' - S) by
      rw [sub_smul]; abel]
    exact hle.smul (by linarith)

/-- The rays: `cΣ ≤ c'Σ` in the ray order for `0 ≤ c ≤ c'`. -/
theorem rayLE_smul (S : Mat d) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c') :
    rayLE (c • S) (c' • S) := by
  rcases hc.lt_or_eq with hc | rfl
  · exact Or.inr ⟨c' / c, (one_le_div hc).2 hcc', by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩
  · exact Or.inl (zero_smul _ _)

/-- **`lem:path-condition-orders`(b)**, from the origin: the ray order on `PSD(d)`; the chain
`ζ(s) = sΣ'`. -/
theorem chain_ray_zero (S' : Mat d) (hS' : S'.PosSemidef) :
    IsWChain (psdSet d) rayLE (fun s => s • S') 0 S' :=
  ⟨by fun_prop, fun s hs => hS'.smul hs.1, fun s hs _ _ hst => rayLE_smul S' hs.1 hst, by simp,
    by simp⟩

/-- **`lem:path-condition-orders`(b)**, from `Σ` to `cΣ`, `c ≥ 1`: the chain
`ζ(s) = (1 + s(c - 1))Σ`. -/
theorem chain_ray (S : Mat d) (hS : S.PosSemidef) (c : ℝ) (hc : 1 ≤ c) :
    IsWChain (psdSet d) rayLE (fun s => (1 + s * (c - 1)) • S) S (c • S) :=
  ⟨by fun_prop, fun s hs => hS.smul (by nlinarith [hs.1]),
    fun s hs t _ hst => rayLE_smul S (by nlinarith [hs.1]) (by nlinarith), by simp,
    by simp⟩

/-! ## (c): the chain `Σ^{1/2}M^sΣ^{1/2}` -/

/-- **`lem:path-condition-orders`(c)**: on `PD(d)`, for a set `𝒦 ⊆ PD(d)` closed under
orthogonal conjugation and under `M ↦ M^τ`, `τ ∈ [0,1]`, whose relation `≤_𝒦` is a partial
order, the chain `ζ(s) = Σ^{1/2} M^s Σ^{1/2}`, `M = Σ^{-1/2}Σ'Σ^{-1/2}`. -/
theorem chain_stepSet (K : Set (Mat d)) (hK : IsStepSet K)
    (hpow : ∀ M ∈ K, ∀ τ ∈ Icc (0 : ℝ) 1, mrpow M τ ∈ K)
    (_hpo : IsPartialOrderOn (pdSet d) (stepLE K)) (S S' : Mat d) (hle : stepLE K S S') :
    IsWChain (pdSet d) (stepLE K) (fun s => msqrt S * mrpow (relStep S S') s * msqrt S) S S' := by
  obtain ⟨hS, -, hMK⟩ := hle
  set A := msqrt S with hA
  set M := relStep S S' with hMdef
  have hM : M.PosDef := hK.1 hMK
  obtain ⟨hUU, -⟩ := spectral_udiag hM.isHermitian
  set U : Mat d := (hM.isHermitian.eigenvectorUnitary : Mat d) with hU
  set m := hM.isHermitian.eigenvalues with hm
  have hmpos : ∀ i, 0 < m i := hM.eigenvalues_pos
  set P : ℝ → Mat d := fun s => udiag U (fun i => m i ^ s) with hP
  have hMP : ∀ s, mrpow M s = P s := fun s => mrpow_eq_spectral hM.posSemidef s
  have hPpd : ∀ s, (P s).PosDef := fun s =>
    (udiag_posDef_iff hUU _).2 fun i => rpow_pos_of_pos (hmpos i) s
  have hPadd : ∀ a b, P a * P b = P (a + b) := fun a b => by
    simp only [hP, udiag_mul hUU]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rw [← rpow_add (hmpos i)]
  have hPT : ∀ s, (P s)ᵀ = P s := fun s => udiag_transpose _ _
  have hγpd : ∀ s, (A * P s * A).PosDef := fun s => posDef_msqrt_conj hS (hPpd s)
  simp only [hMP]
  refine ⟨?_, fun s _ => hγpd s, fun s hs t ht hst => ?_, ?_, ?_⟩
  · -- continuity
    apply Continuous.continuousOn
    simp only [hP, udiag]
    refine (continuous_const.matrix_mul (Continuous.matrix_mul (continuous_const.matrix_mul
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const)).matrix_mul
      continuous_const
    exact continuous_const.rpow continuous_id fun _ => Or.inl (hmpos i).ne'
  · -- monotonicity: the relative step of `(ζ(s), ζ(t))` is `Q M^{t-s} Qᵀ`, `Q` orthogonal
    refine ⟨hγpd s, hγpd t, ?_⟩
    set B := A * P (s / 2) with hB
    have hBT : Bᵀ = P (s / 2) * A := by
      rw [hB, transpose_mul, hPT, hA, msqrt_transpose]
    have hγs : A * P s * A = B * Bᵀ := by
      rw [hBT, hB, show A * P (s / 2) * (P (s / 2) * A) = A * (P (s / 2) * P (s / 2)) * A by
        simp only [Matrix.mul_assoc], hPadd, add_halves]
    have hγt : A * P t * A = B * P (t - s) * Bᵀ := by
      rw [hBT, hB, show A * P (s / 2) * P (t - s) * (P (s / 2) * A) =
        A * (P (s / 2) * P (t - s) * P (s / 2)) * A by simp only [Matrix.mul_assoc], hPadd, hPadd,
        show s / 2 + (t - s) + s / 2 = t by ring]
    set R := msqrt (A * P s * A) with hR
    set Q := R⁻¹ * B with hQ
    have hQT : Qᵀ = Bᵀ * R⁻¹ := by rw [hQ, transpose_mul, hR, msqrt_inv_transpose]
    have hQQ : Q * Qᵀ = 1 := by
      have h := relStep_self (hγs ▸ hγpd s)
      rw [relStep, ← hγs] at h
      rw [hQT, hQ, ← h, ← hR]
      simp only [hγs, Matrix.mul_assoc]
    have hQo : Q ∈ orthSet d := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hQQ
    have hstep : relStep (A * P s * A) (A * P t * A) = Q * P (t - s) * Qᵀ := by
      rw [relStep, ← hR, hγt, hQT, hQ]
      simp only [Matrix.mul_assoc]
    rw [hstep, ← hMP]
    exact hK.2 _ (hpow M hMK (t - s) ⟨by linarith, by linarith [hs.1, ht.2]⟩) Q hQo
  · simp only [hP, rpow_zero, udiag_one hUU, Matrix.mul_one, hA, msqrt_mul_self hS.posSemidef]
  · rw [← hMP, mrpow, CFC.rpow_eq_pow, CFC.rpow_one M (nonneg_of_posSemidef hM.posSemidef), hA,
      hMdef, msqrt_mul_relStep hS]

/-! ## The three step sets -/

theorem orth_mul_udiag (Q U : Mat d) (w : Fin d → ℝ) : Q * udiag U w * Qᵀ = udiag (Q * U) w := by
  simp only [udiag, transpose_mul, Matrix.mul_assoc]

theorem orth_mul_orth {Q U : Mat d} (hQ : Q * Qᵀ = 1) (hU : U * Uᵀ = 1) :
    (Q * U) * (Q * U)ᵀ = 1 := by
  rw [transpose_mul, show Q * U * (Uᵀ * Qᵀ) = Q * (U * Uᵀ) * Qᵀ by simp only [Matrix.mul_assoc],
    hU, Matrix.mul_one, hQ]

theorem udiag_sub (U : Mat d) (w w' : Fin d → ℝ) : udiag U w - udiag U w' = udiag U (w - w') := by
  rw [udiag, udiag, udiag, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rfl

theorem udiag_const {U : Mat d} (hU : U * Uᵀ = 1) (a : ℝ) : udiag U (fun _ => a) = a • 1 := by
  rw [udiag, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

theorem udiag_injective {U : Mat d} (hU : U * Uᵀ = 1) {w w' : Fin d → ℝ}
    (h : udiag U w = udiag U w') : w = w' := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  have hback : ∀ v, Uᵀ * udiag U v * U = diagonal v := fun v => by
    rw [udiag, show Uᵀ * (U * diagonal v * Uᵀ) * U = (Uᵀ * U) * diagonal v * (Uᵀ * U) by
      simp only [Matrix.mul_assoc], hU', Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun N => Uᵀ * N * U) h
  simp only [hback] at this
  exact diagonal_injective this

/-- `λ_min(U diag(w) Uᵀ)` does not depend on the orthogonal `U`. -/
theorem lamMin_udiag_eq [NeZero d] {U V : Mat d} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (w : Fin d → ℝ) : lamMin (udiag U w) = lamMin (udiag V w) :=
  le_antisymm (le_lamMin_udiag hV fun i => lamMin_udiag_le hU w i)
    (le_lamMin_udiag hU fun i => lamMin_udiag_le hV w i)

/-- `e^{U diag(x) Uᵀ} = U diag(eˣ) Uᵀ`. -/
theorem mexp_udiag {U : Mat d} (hU : U * Uᵀ = 1) (x : Fin d → ℝ) :
    mexp (udiag U x) = udiag U (fun i => Real.exp (x i)) := by
  have hinv : U⁻¹ = Uᵀ := Matrix.inv_eq_right_inv hU
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 (mem_glSet_of_orth hU)
  unfold mexp udiag
  rw [← hinv, Matrix.exp_conj U _ hUu, Matrix.exp_diagonal, Pi.exp_def, Real.exp_eq_exp_ℝ]

/-- **The spectral form, without dependent data**: a symmetric `M` is `U diag(m) Uᵀ` with `U`
orthogonal. -/
theorem exists_udiag {M : Mat d} (hM : M.IsHermitian) :
    ∃ U : Mat d, ∃ m : Fin d → ℝ, U * Uᵀ = 1 ∧ M = udiag U m :=
  ⟨_, _, spectral_udiag hM⟩

/-- The spectral form of `M ∈ PSD(d)` together with that of its powers. -/
theorem exists_udiag_rpow {M : Mat d} (hM : M.PosSemidef) :
    ∃ U : Mat d, ∃ m : Fin d → ℝ, U * Uᵀ = 1 ∧ M = udiag U m ∧
      ∀ s : ℝ, mrpow M s = udiag U (fun i => m i ^ s) :=
  ⟨_, _, (spectral_udiag hM.isHermitian).1, (spectral_udiag hM.isHermitian).2,
    mrpow_eq_spectral hM⟩

/-- **`lem:path-condition-orders`(c)**, the Loewner order on `PD(d)`:
`𝒦 = {M : M ≥ I}` satisfies the hypotheses of `chain_stepSet`, and `≤_𝒦` is the Loewner
order on `PD(d)`. -/
theorem stepSet_loewner :
    IsStepSet {M : Mat d | M.PosDef ∧ loewnerLE 1 M} ∧
      (∀ M ∈ {M : Mat d | M.PosDef ∧ loewnerLE 1 M}, ∀ τ ∈ Icc (0 : ℝ) 1,
        mrpow M τ ∈ {M : Mat d | M.PosDef ∧ loewnerLE 1 M}) ∧
      IsPartialOrderOn (pdSet d) (stepLE {M : Mat d | M.PosDef ∧ loewnerLE 1 M}) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (stepLE {M : Mat d | M.PosDef ∧ loewnerLE 1 M} S S' ↔ loewnerLE S S') := by
  set K := {M : Mat d | M.PosDef ∧ loewnerLE 1 M}
  have hiff : ∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ loewnerLE S S') := by
    intro S S' hS hS'
    have hsub : relStep S S' - 1 = relStep S (S' - S) := by
      rw [relStep_sub, relStep_self hS]
    refine ⟨fun h => ?_, fun h => ⟨hS, hS', (posDef_relStep_iff hS S').2 hS', ?_⟩⟩
    · have h2 := h.2.2.2
      unfold loewnerLE at h2 ⊢
      rwa [hsub, posSemidef_relStep_iff hS] at h2
    · unfold loewnerLE
      rwa [hsub, posSemidef_relStep_iff hS]
  refine ⟨⟨fun M h => h.1, fun M hM Q hQ => ?_⟩, fun M hM τ hτ => ?_, ?_, hiff⟩
  · have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    refine ⟨(posDef_act_iff (orthSet_subset_glSet hQ) M).2 hM.1, ?_⟩
    have h := hM.2.mul_mul_conjTranspose_same Q
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hQQ] at h
    exact h
  · obtain ⟨hMpd, hM1⟩ := hM
    obtain ⟨U, m, hUU, hMU, hpow⟩ := exists_udiag_rpow hMpd.posSemidef
    have hmpos : ∀ i, 0 < m i := (udiag_posDef_iff hUU m).1 (hMU ▸ hMpd)
    have hm1 : ∀ i, 1 ≤ m i := by
      unfold loewnerLE at hM1
      rw [hMU, ← udiag_one hUU, udiag_sub, udiag_posSemidef_iff hUU] at hM1
      intro i
      have := hM1 i
      simp only [Pi.sub_apply] at this
      linarith
    rw [hpow]
    refine ⟨(udiag_posDef_iff hUU _).2 fun i => rpow_pos_of_pos (hmpos i) τ, ?_⟩
    unfold loewnerLE
    rw [← udiag_one hUU, udiag_sub, udiag_posSemidef_iff hUU]
    intro i
    simp only [Pi.sub_apply, sub_nonneg]
    exact one_le_rpow (hm1 i) hτ.1
  · refine ⟨fun S hS => (hiff S S hS hS).2 (by simp [loewnerLE, PosSemidef.zero]),
      fun S hS S' hS' h h' => ?_, fun S hS S' hS' S'' hS'' h h' => ?_⟩
    · exact le_antisymm ((loewnerLE_iff_le _ _).1 ((hiff S S' hS hS').1 h))
        ((loewnerLE_iff_le _ _).1 ((hiff S' S hS' hS).1 h'))
    · exact (hiff S S'' hS hS'').2 ((loewnerLE_iff_le _ _).2 (le_trans
        ((loewnerLE_iff_le _ _).1 ((hiff S S' hS hS').1 h))
        ((loewnerLE_iff_le _ _).1 ((hiff S' S'' hS' hS'').1 h'))))

/-- **`lem:path-condition-orders`(c)**, the ray order on `PD(d)`: `𝒦 = {cI : c ≥ 1}` satisfies
the hypotheses of `chain_stepSet`, and `≤_𝒦` is the ray order on `PD(d)`. -/
theorem stepSet_ray :
    IsStepSet {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1} ∧
      (∀ M ∈ {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1}, ∀ τ ∈ Icc (0 : ℝ) 1,
        mrpow M τ ∈ {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1}) ∧
      IsPartialOrderOn (pdSet d) (stepLE {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1}) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (stepLE {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1} S S' ↔ rayLE S S') := by
  set K := {M : Mat d | ∃ c : ℝ, 1 ≤ c ∧ M = c • 1}
  have hiff : ∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ rayLE S S') := by
    intro S S' hS hS'
    refine ⟨fun h => ?_, fun h => ⟨hS, hS', ?_⟩⟩
    · obtain ⟨c, hc, hcM⟩ := h.2.2
      refine Or.inr ⟨c, hc, ?_⟩
      rw [← msqrt_mul_relStep hS S', hcM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        msqrt_mul_self hS.posSemidef]
    · rcases h with h0 | ⟨c, hc, rfl⟩
      · rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd
          exact ⟨1, le_rfl, Subsingleton.elim _ _⟩
        · haveI : NeZero d := ⟨hd.ne'⟩
          exact absurd h0 (PosDef_ne_zero' hS)
      · exact ⟨c, hc, by rw [relStep_smul, relStep_self hS]⟩
  have hW := isWedgeDatum_ray glSet_isClosedSubgroupGL.1 (d := d) glSet_isClosedSubgroupGL.2
  refine ⟨⟨fun M h => ?_, fun M hM Q hQ => ?_⟩, fun M hM τ hτ => ?_, ?_, hiff⟩
  · obtain ⟨c, hc, rfl⟩ := h
    exact PosDef.one.smul (by linarith)
  · obtain ⟨c, hc, rfl⟩ := hM
    refine ⟨c, hc, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ]
  · obtain ⟨c, hc, rfl⟩ := hM
    have hpd : (c • (1 : Mat d)).PosDef := PosDef.one.smul (by linarith)
    obtain ⟨U, m, hUU, hMU, hpow⟩ := exists_udiag_rpow hpd.posSemidef
    have hm : m = fun _ => c := by
      apply udiag_injective hUU
      rw [← hMU, udiag_const hUU]
    refine ⟨c ^ τ, one_le_rpow hc hτ.1, ?_⟩
    rw [hpow, ← udiag_const hUU, hm]
  · refine ⟨fun S hS => (hiff S S hS hS).2 (hW.refl S hS.posSemidef),
      fun S hS S' hS' h h' => hW.antisymm S S' hS.posSemidef hS'.posSemidef
        ((hiff S S' hS hS').1 h) ((hiff S' S hS' hS).1 h'),
      fun S hS S' hS' S'' hS'' h h' => (hiff S S'' hS hS'').2 (hW.trans S S' S'' hS.posSemidef
        hS'.posSemidef hS''.posSemidef ((hiff S S' hS hS').1 h) ((hiff S' S'' hS' hS'').1 h'))⟩

/-- **`lem:path-condition-orders`(c)**, the stable step cone, `0 < α < 2`:
`𝒦_α = {M ∈ PD(d) : λ_min(M)^{d+α} ≥ det M}` satisfies the hypotheses of `chain_stepSet` (its
partial order being `prop:stable-step-cone`(2)), and is the set of `e^X` with `X` symmetric and
`(d+α)λ_min(X) ≥ tr X`. `d ≥ 1` is the node's (blind review R1-1): at `d = 0` the unit sphere is
empty, `λ_min = 0` and `det = 1`, so `𝒦_α = ∅` and the third and fourth conjuncts fail. -/
theorem stepSet_stable [NeZero d] (α : ℝ) (hα0 : 0 < α) (hα2 : α < 2) :
    IsStepSet (stableStepSet d α) ∧
      (∀ M ∈ stableStepSet d α, ∀ τ ∈ Icc (0 : ℝ) 1, mrpow M τ ∈ stableStepSet d α) ∧
      IsPartialOrderOn (pdSet d) (stableLE α) ∧
      stableStepSet d α = expSet (stableSymCone d α) := by
  have hdα : 0 < (d : ℝ) + α := by positivity
  refine ⟨⟨fun M h => h.1, fun M hM Q hQ => ?_⟩, fun M hM τ hτ => ?_,
    (stableLE_partialOrder hα0 hα2).1, ?_⟩
  · have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    obtain ⟨hMpd, h⟩ := hM
    obtain ⟨U, m, hUU, hMU⟩ := exists_udiag hMpd.isHermitian
    refine ⟨(posDef_act_iff (orthSet_subset_glSet hQ) M).2 hMpd, ?_⟩
    rw [hMU, orth_mul_udiag, det_udiag (orth_mul_orth hQQ hUU),
      lamMin_udiag_eq (orth_mul_orth hQQ hUU) hUU]
    rwa [hMU, det_udiag hUU] at h
  · obtain ⟨hMpd, hMc⟩ := hM
    obtain ⟨U, m, hUU, hMU, hpow⟩ := exists_udiag_rpow hMpd.posSemidef
    have hmpos : ∀ i, 0 < m i := (udiag_posDef_iff hUU m).1 (hMU ▸ hMpd)
    have hl := lamMin_pos hMpd
    have hml : ∀ i, lamMin M ≤ m i := fun i => by
      rw [hMU]; exact lamMin_udiag_le hUU m i
    rw [hpow]
    refine ⟨(udiag_posDef_iff hUU _).2 fun i => rpow_pos_of_pos (hmpos i) τ, ?_⟩
    have hlow : lamMin M ^ τ ≤ lamMin (udiag U fun i => m i ^ τ) :=
      le_lamMin_udiag hUU fun i => rpow_le_rpow hl.le (hml i) hτ.1
    have hdet : (udiag U fun i => m i ^ τ).det = M.det ^ τ := by
      rw [det_udiag hUU, Real.finsetProd_rpow _ _ (fun i _ => (hmpos i).le), hMU, det_udiag hUU]
    rw [hdet]
    calc M.det ^ τ ≤ (lamMin M ^ ((d : ℝ) + α)) ^ τ :=
          rpow_le_rpow hMpd.det_pos.le hMc hτ.1
      _ = (lamMin M ^ τ) ^ ((d : ℝ) + α) := by
          rw [← rpow_mul hl.le, ← rpow_mul hl.le, mul_comm]
      _ ≤ _ := rpow_le_rpow (rpow_nonneg hl.le _) hlow hdα.le
  · ext M
    constructor
    · rintro ⟨hMpd, hMc⟩
      obtain ⟨U, m, hUU, hMU⟩ := exists_udiag hMpd.isHermitian
      have hmpos : ∀ i, 0 < m i := (udiag_posDef_iff hUU m).1 (hMU ▸ hMpd)
      have hl := lamMin_pos hMpd
      have hml : ∀ i, lamMin M ≤ m i := fun i => by
        rw [hMU]; exact lamMin_udiag_le hUU m i
      refine ⟨udiag U fun i => Real.log (m i), ⟨udiag_transpose _ _, ?_⟩, ?_⟩
      · have hlow : Real.log (lamMin M) ≤ lamMin (udiag U fun i => Real.log (m i)) :=
          le_lamMin_udiag hUU fun i => Real.log_le_log hl (hml i)
        have htr : (udiag U fun i => Real.log (m i)).trace = Real.log M.det := by
          rw [trace_udiag hUU, ← Real.log_prod (fun i _ => (hmpos i).ne'), hMU, det_udiag hUU]
        rw [htr]
        calc Real.log M.det ≤ Real.log (lamMin M ^ ((d : ℝ) + α)) :=
              Real.log_le_log hMpd.det_pos hMc
          _ = ((d : ℝ) + α) * Real.log (lamMin M) := Real.log_rpow hl _
          _ ≤ _ := mul_le_mul_of_nonneg_left hlow hdα.le
      · rw [mexp_udiag hUU, hMU]
        congr 1
        funext i
        rw [Real.exp_log (hmpos i)]
    · rintro ⟨X, ⟨hXs, hXtr⟩, rfl⟩
      have hXh : X.IsHermitian := by
        change Xᴴ = X
        rw [conjTranspose_eq_transpose_of_trivial]; exact hXs
      obtain ⟨U, x, hUU, hXU⟩ := exists_udiag hXh
      have hxl : ∀ i, lamMin X ≤ x i := fun i => by
        rw [hXU]; exact lamMin_udiag_le hUU x i
      have htr : X.trace = ∑ i, x i := by rw [hXU, trace_udiag hUU]
      rw [hXU, mexp_udiag hUU]
      refine ⟨(udiag_posDef_iff hUU _).2 fun i => Real.exp_pos _, ?_⟩
      have hlow : Real.exp (lamMin X) ≤ lamMin (udiag U fun i => Real.exp (x i)) :=
        le_lamMin_udiag hUU fun i => Real.exp_le_exp.2 (hxl i)
      rw [det_udiag hUU, ← Real.exp_sum, ← htr]
      calc Real.exp X.trace ≤ Real.exp (lamMin X * ((d : ℝ) + α)) :=
            Real.exp_le_exp.2 (by rw [mul_comm]; exact hXtr)
        _ = Real.exp (lamMin X) ^ ((d : ℝ) + α) := Real.exp_mul _ _
        _ ≤ _ := rpow_le_rpow (Real.exp_pos _).le hlow hdα.le

end AffineHemigroup
