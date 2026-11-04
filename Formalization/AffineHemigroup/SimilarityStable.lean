/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableTail
import AffineHemigroup.EllipticalStable
import AffineHemigroup.StableOrderPSD
import AffineHemigroup.StableOrderGenerated
import AffineHemigroup.SimilaritySpectrum
import AffineHemigroup.LogOrbitRays
import AffineHemigroup.ParameterSpace

/-!
# `prop:similarity-stable-family`: similarity-covariant families with a stable part

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-stable-family`.

For maps `h : PD(d) → PD(d)` and `C : PD(d) → PSD(d)` put `μ_Σ := N(0, C(Σ)) * S_α(h(Σ))`.
(1) a positive finite increment `μ_{Σ'} = μ_Σ * ρ` orders the stable parts, `h(Σ) ≼_α h(Σ')`;
(2) under similarity equivariance, a continuous extension of `h` to `PSD(d) ∖ {0}` with values in
`PD(d)` and increments on every Loewner step of `PD(d)`, `ecc(h(Σ)) ≤ (h₀/c₁)^α`; (3) the family
`h(Σ) = Σ + κ tr(Σ) I`, `C(Σ) = 2bΣ` with `ακ² - (d+1)κ - 1 ≥ 0` has increments on every Loewner
step of `PSD(d)` forming a family with (K1), (K2), (K4) and (K3) for the similarities, and its
stable part is rotation invariant only on the multiples of `I`.

## Routes

* **(1)** is `lem:stable-tail` with `G = (C(Σ') - C(Σ))/2`, then `lem:stable-step-order`'s
  criterion (b).
* **(2)** follows the blueprint: the sandwich `Σ_ε ≤ Σ ≤ I` through a reflection carrying `e₁` to a
  unit eigenvector of `Σ` for `λ_max(Σ) = 1`, the limit `ε → 0` read on the quadratic forms, and
  condition (c) read through `t_α` (`stablePlusLE_le_smul_one_iff`).
* **(3)**, the stable increments, **without a derivative** (`% CHANGED Q-0281 wave 2, group G` in
  the blueprint): condition (c) of the relative step `M = H₀^{-1/2}H₁H₀^{-1/2}` is checked in one
  step, `det M ≤ (tr M/d)^d` (the arithmetic–geometric mean inequality on the spectrum),
  `tr M ≤ d + (1+dκ)u/κ`, `λ_min(M) ≥ 1 + κu/(1+κ)`, `u = tr P/tr Σ`, and Bernoulli's inequality
  `(1 + Bu)^{(d+α)/d} ≥ 1 + (d+α)Bu/d`, which the hypothesis on `κ` makes at least `1 + Au/d`.
  The increments are then the laws with the telescoping transform, chosen pair by pair.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The largest eigenvalue -/

/-- `⟨x, Mx⟩ ≤ λ_max(M)|x|²` for symmetric `M`. -/
theorem quad_le_lamMax_mul [NeZero d] {M : Mat d} (hM : M.IsHermitian) (x : Rd d) :
    quad M x ≤ lamMax M * ‖x‖ ^ 2 := by
  rw [lamMax_eq_eigUp_last hM]
  have h := quad_nonneg ((posSemidef_smul_one_sub_iff hM (eigUp M (Fin.rev 0))).2 le_rfl) x
  rw [quad_sub, quad_smul, quad_one] at h
  linarith

/-- `⟨u, Mu⟩ ≤ λ_max(M)` on unit vectors. -/
theorem quad_le_lamMax [NeZero d] {M : Mat d} (hM : M.IsHermitian) {u : Rd d} (hu : ‖u‖ = 1) :
    quad M u ≤ lamMax M := by
  have h := quad_le_lamMax_mul hM u
  rwa [hu, one_pow, mul_one] at h

/-- `λ_max(M) ≤ c` iff `⟨x, Mx⟩ ≤ c` on the unit sphere. -/
theorem lamMax_le_iff [NeZero d] {M : Mat d} (hM : M.IsHermitian) (c : ℝ) :
    lamMax M ≤ c ↔ ∀ x : Rd d, ‖x‖ = 1 → quad M x ≤ c := by
  constructor
  · intro h x hx
    exact (quad_le_lamMax hM hx).trans h
  · intro h
    haveI : Nonempty {x : Rd d // ‖x‖ = 1} := by
      obtain ⟨v, hv, -⟩ := exists_unit_eigvec_eigUp_zero hM
      exact ⟨⟨v, hv⟩⟩
    exact ciSup_le fun x => h x x.2

/-- `λ_max(tM) = tλ_max(M)` for `t ≥ 0`. -/
theorem lamMax_smul {t : ℝ} (ht : 0 ≤ t) (M : Mat d) : lamMax (t • M) = t * lamMax M := by
  unfold lamMax
  rw [Real.mul_iSup_of_nonneg ht]
  congr 1
  ext x
  rw [lin_smul, _root_.smul_apply, inner_smul_right]

/-- `λ_max > 0` on `PD(d)`. -/
theorem lamMax_pos [NeZero d] {M : Mat d} (hM : M.PosDef) : 0 < lamMax M := by
  rw [lamMax_eq_eigUp_last hM.isHermitian]; exact eigUp_pos hM _

/-- `λ_min(M) ≤ λ_max(M)` for symmetric `M`. -/
theorem lamMin_le_lamMax [NeZero d] {M : Mat d} (hM : M.IsHermitian) : lamMin M ≤ lamMax M := by
  rw [lamMin_eq_eigUp_zero hM, lamMax_eq_eigUp_last hM]
  exact eigUp_monotone hM (Fin.zero_le _)

/-- `λ_min ≥ 0` on `PSD(d)`. -/
theorem lamMin_nonneg [NeZero d] {M : Mat d} (hM : M.PosSemidef) : 0 ≤ lamMin M :=
  (le_lamMin_iff hM.isHermitian 0).2 fun x _ => quad_nonneg hM x

/-- `det M ≤ λ_min(M) λ_max(M)^{d-1}` on `PD(d)`. -/
theorem det_le_lamMin_mul_lamMax_pow [NeZero d] {M : Mat d} (hM : M.PosDef) :
    M.det ≤ lamMin M * lamMax M ^ (d - 1) := by
  have hH := hM.isHermitian
  rw [lamMin_eq_eigUp_zero hH, lamMax_eq_eigUp_last hH, ← prod_eigUp hH,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
  refine mul_le_mul_of_nonneg_left ?_ (eigUp_pos hM 0).le
  calc ∏ k ∈ Finset.univ.erase 0, eigUp M k ≤ ∏ _k ∈ Finset.univ.erase (0 : Fin d),
        eigUp M (Fin.rev 0) :=
        Finset.prod_le_prod (fun k _ => (eigUp_pos hM k).le)
          (fun k _ => eigUp_monotone hH (le_rev_zero k))
    _ = eigUp M (Fin.rev 0) ^ (d - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]

/-- `λ_max(Σ) ≤ tr Σ` on `PSD(d)`. -/
theorem lamMax_le_trace [NeZero d] {S : Mat d} (hS : S.PosSemidef) : lamMax S ≤ S.trace := by
  rw [lamMax_eq_eigUp_last hS.isHermitian, ← sum_eigUp hS.isHermitian]
  exact Finset.single_le_sum (fun k _ => eigUp_nonneg hS k) (Finset.mem_univ _)

/-- `ecc(tH) = ecc(H)` for `t > 0`. -/
theorem ecc_smul {t : ℝ} (ht : 0 < t) (H : Mat d) : ecc (t • H) = ecc H := by
  unfold ecc
  rw [lamMax_smul ht.le, lamMin_smul ht.le, mul_div_mul_left _ _ ht.ne']

/-- `λ_min(Σ⁻¹) = λ_max(Σ)⁻¹` on `PD(d)`. -/
theorem lamMin_inv_eq [NeZero d] {S : Mat d} (hS : S.PosDef) : lamMin S⁻¹ = (lamMax S)⁻¹ := by
  rw [lamMax_eq_inv_lamMin_inv hS, inv_inv]

/-! ## The trace of a relative step -/

/-- The trace is monotone along the Loewner order. -/
theorem trace_le_of_loewnerLE {A B : Mat d} (h : loewnerLE A B) : A.trace ≤ B.trace := by
  have := h.trace_nonneg
  rw [trace_sub] at this
  linarith

/-- `Σ⁻¹ ≤ λ_min(Σ)⁻¹ I` on `PD(d)`. -/
theorem inv_loewnerLE_smul_one [NeZero d] {S : Mat d} (hS : S.PosDef) :
    loewnerLE S⁻¹ ((lamMin S)⁻¹ • (1 : Mat d)) := by
  have hl := lamMin_pos hS
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg
    ((isHermitian_one.smul (IsSelfAdjoint.all _)).sub hS.inv.isHermitian) fun y => ?_
  rw [quad_sub, quad_smul, quad_one]
  have h := lamMin_mul_quad_inv_le hS y
  have : quad S⁻¹ y ≤ (lamMin S)⁻¹ * ‖y‖ ^ 2 := by
    rw [le_inv_mul_iff₀ hl]; exact h
  linarith

/-- **The trace of a relative step**: `tr(Σ^{-1/2} P Σ^{-1/2}) ≤ tr P / λ_min(Σ)` for `Σ ∈ PD(d)`
and `P ∈ PSD(d)`. -/
theorem trace_relStep_le [NeZero d] {S P : Mat d} (hS : S.PosDef) (hP : P.PosSemidef) :
    (relStep S P).trace ≤ P.trace / lamMin S := by
  have hl := lamMin_pos hS
  set R := (msqrt S)⁻¹ with hR
  set W := msqrt P with hW
  have hRR : R * R = S⁻¹ := by
    rw [hR]
    conv_rhs => rw [← msqrt_mul_self hS.posSemidef]
    exact (Matrix.mul_inv_rev _ _).symm
  have hWW : W * W = P := msqrt_mul_self hP
  have htr : (relStep S P).trace = (act W S⁻¹).trace := by
    rw [relStep, ← hR, ← hWW, act, msqrt_transpose, ← hW,
      show R * (W * W) * R = (R * W) * (W * R) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show W * R * (R * W) = W * (R * R) * W by
        simp only [Matrix.mul_assoc], hRR]
  have hle := loewnerLE_act W (inv_loewnerLE_smul_one hS)
  have h2 : act W ((lamMin S)⁻¹ • (1 : Mat d)) = (lamMin S)⁻¹ • P := by
    rw [act, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, msqrt_transpose, ← hW, hWW]
  rw [htr]
  refine (trace_le_of_loewnerLE hle).trans ?_
  rw [h2, trace_smul, smul_eq_mul, div_eq_inv_mul]

/-! ## The arithmetic–geometric mean inequality for the determinant -/

/-- `∏ zᵢ ≤ ((∑ zᵢ)/n)^n` for `n` nonnegative reals. -/
theorem prod_le_mean_pow {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / n) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (n : ℝ)⁻¹) z
    (fun _ _ => (inv_pos.2 hn').le) (by simp [Finset.card_univ, hn'.ne']) (fun i _ => hz i)
  have hprod : ∏ i, z i ^ (n : ℝ)⁻¹ = (∏ i, z i) ^ (n : ℝ)⁻¹ :=
    Real.finsetProd_rpow _ _ (fun i _ => hz i) _
  rw [hprod, ← Finset.mul_sum] at h
  have hP : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hP _) h n
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hn'.ne', Real.rpow_one,
    inv_mul_eq_div] at h2

/-- `det M ≤ (tr M/d)^d` on `PD(d)`. -/
theorem det_le_trace_div_pow [NeZero d] {M : Mat d} (hM : M.PosDef) :
    M.det ≤ (M.trace / d) ^ d := by
  rw [← prod_eigUp hM.isHermitian, ← sum_eigUp hM.isHermitian]
  exact prod_le_mean_pow (NeZero.pos d) _ fun k => (eigUp_pos hM k).le

/-! ## Clause (1) -/

/-- **`prop:similarity-stable-family`(1)**, the stable parts are ordered: for
`μ_Σ := N(0, C(Σ)) * S_α(h(Σ))`, a positive finite increment `μ_{Σ'} = μ_Σ * ρ` between
`Σ, Σ' ∈ PD(d)` gives `h(Σ) ≼_α h(Σ')`. -/
theorem sim_stable_parts_ordered (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef) (σ : Mat d → Measure (Rd d))
    (hσ : ∀ S : Mat d, S.PosDef → IsEllipticalStable α (h S) (σ S)) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
      multivariateGaussian 0 (C S') ∗ σ S' = (multivariateGaussian 0 (C S) ∗ σ S) ∗ ρ →
      stableLE α (h S) (h S') := by
  haveI : NeZero d := ⟨by omega⟩
  intro S S' hS hS' ρ hρ heq
  haveI := hρ
  have hH := hh S hS
  have hH' := hh S' hS'
  haveI := (hσ S hS).1
  haveI := (hσ S' hS').1
  rw [stableLE_iff_density hα0 hα2 hH hH']
  refine (stable_tail hα0 hα2 hH hH' ρ (G := (1 / 2 : ℝ) • (C S' - C S)) fun ω => ?_).2.2
  have h2 := congrArg (fun m => charFun m ω) heq
  simp only [charFun_conv, charFun_multivariateGaussian_zero (hC _ hS),
    charFun_multivariateGaussian_zero (hC _ hS'), (hσ S hS).2, (hσ S' hS').2] at h2
  have hne : ((Real.exp (-(quad (C S) ω / 2)) : ℝ) : ℂ) *
      ((Real.exp (-stableExp α (h S) ω) : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_mul]; exact_mod_cast (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  apply mul_left_cancel₀ hne
  rw [← h2]
  simp only [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  rw [quad_smul, quad_sub]
  ring

/-! ## Clause (2) -/

/-- `Σ_ε = εI + diag((1-ε)e₁)`. -/
theorem sigmaEps_eq [NeZero d] (ε : ℝ) :
    sigmaEps d ε = ε • (1 : Mat d) + diagonal (Pi.single 0 (1 - ε)) := by
  ext i j
  simp only [sigmaEps, Matrix.add_apply, Matrix.smul_apply, one_apply, diagonal_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0
    · subst hi; simp
    · have : ¬ ((i : ℕ) = 0) := fun h => hi (Fin.ext h)
      simp [this, hi]
  · simp [hij]

/-- `⟨y, Σ_ε y⟩ = ε|y|² + (1-ε)y₁²`. -/
theorem quad_sigmaEps [NeZero d] (ε : ℝ) (y : Rd d) :
    quad (sigmaEps d ε) y = ε * ‖y‖ ^ 2 + (1 - ε) * y 0 ^ 2 := by
  rw [sigmaEps_eq, quad_add, quad_smul, quad_one, quad_diagonal_single]

/-- `Σ_ε ∈ PSD(d) ∖ {0}` for `ε ≥ 0`, and `Σ_ε ∈ PD(d)` for `ε > 0`. -/
theorem sigmaEps_props [NeZero d] {ε : ℝ} (hε : 0 ≤ ε) :
    (sigmaEps d ε).PosSemidef ∧ sigmaEps d ε ≠ 0 := by
  refine ⟨posSemidef_of_quad_nonneg ?_ fun y => ?_, fun h => ?_⟩
  · unfold sigmaEps
    exact isHermitian_diagonal _
  · rw [quad_sigmaEps]
    rcases le_or_gt ε 1 with h1 | h1
    · positivity
    · have hy : y 0 ^ 2 ≤ ‖y‖ ^ 2 := by
        have := PiLp.norm_apply_le y 0
        rw [Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (y 0), sq_abs (y 0), norm_nonneg y]
      nlinarith
  · have := congrFun (congrFun h 0) 0
    simp [sigmaEps] at this

theorem sigmaEps_posDef [NeZero d] {ε : ℝ} (hε : 0 < ε) : (sigmaEps d ε).PosDef := by
  unfold sigmaEps
  refine Matrix.posDef_diagonal_iff.2 fun i => ?_
  split_ifs <;> [exact one_pos; exact hε]

theorem continuous_sigmaEps : Continuous fun ε : ℝ => sigmaEps d ε := by
  unfold sigmaEps
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  split_ifs <;> fun_prop

/-! ### The gauge's sandwich, shared by `prop:similarity-stable-family`(2) and
`prop:similarity-orbit-family`(2) -/

/-- `Σ ≤ I` when `λ_max(Σ) = 1`. -/
theorem loewnerLE_one_of_lamMax [NeZero d] {S : Mat d} (hSh : S.IsHermitian)
    (hSmax : lamMax S = 1) : loewnerLE S 1 := by
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg (isHermitian_one.sub hSh) fun x => ?_
  rw [quad_sub, quad_one]
  have := quad_le_lamMax_mul hSh x
  rw [hSmax, one_mul] at this
  linarith

/-- **An `O(d)`-equivariant gauge is a multiple of `I` at `I`**: `h(I) = h₀I` with `h₀ = h(I)₁₁ > 0`
(the proof of `lem:affine-gauge`). -/
theorem gauge_one [NeZero d] (h : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ)) :
    0 < h 1 0 0 ∧ h 1 = h 1 0 0 • (1 : Mat d) := by
  have hinvI : ∀ Q ∈ orthSet d, act Q (h 1) = h 1 := fun Q hQ => by
    have := hequiv 1 PosDef.one 1 one_pos Q hQ
    simp only [one_smul] at this
    rw [show Q * 1 * Qᵀ = act Q 1 by rfl, act_orth_one hQ] at this
    exact this.symm
  exact ⟨(hh 1 PosDef.one).diag_pos, eq_smul_one_of_orth_invariant hinvI⟩

/-- **The rescaling**: `h(Σ) = λ_max(Σ) h(Σ/λ_max(Σ))` for a similarity-equivariant `h`. -/
theorem gauge_rescale [NeZero d] (h : Mat d → Mat d)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ)) {S : Mat d} (hS : S.PosDef) :
    0 < lamMax S ∧ ((lamMax S)⁻¹ • S).PosDef ∧ lamMax ((lamMax S)⁻¹ • S) = 1 ∧
      h S = lamMax S • h ((lamMax S)⁻¹ • S) := by
  have ht : 0 < lamMax S := lamMax_pos hS
  have hS1 : ((lamMax S)⁻¹ • S).PosDef := hS.smul (inv_pos.2 ht)
  refine ⟨ht, hS1, by rw [lamMax_smul (inv_pos.2 ht).le, inv_mul_cancel₀ ht.ne'], ?_⟩
  have h1o : (1 : Mat d) ∈ orthSet d := (Matrix.orthogonalGroup (Fin d) ℝ).one_mem
  have := hequiv _ hS1 _ ht 1 h1o
  rwa [transpose_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this

/-- **`Q Σ_ε Qᵀ ≤ Σ`**: for `Σ ∈ PD(d)` and a unit eigenvector `v = Qe₁` of `Σ` for the eigenvalue
`1`, `Q diag(1, ε, …, ε) Qᵀ ≤ Σ` whenever `0 < ε ≤ λ_min(Σ)` and `ε ≤ 1`. -/
theorem sigmaEps_conj_le [NeZero d] {S Q : Mat d} (hSh : S.IsHermitian) (hQ : Q ∈ orthSet d)
    (hQv : lin S (lin Q (ebasis 0)) = lin Q (ebasis 0)) {ε : ℝ} (hε : 0 < ε)
    (hεl : ε ≤ lamMin S) (_hε1 : ε ≤ 1) : loewnerLE (act Q (sigmaEps d ε)) S := by
  set v := lin Q (ebasis 0) with hvdef
  have hQQ : Qᵀ * Q = 1 := orth_transpose_mul hQ
  have hnorm : ∀ x, ‖lin Qᵀ x‖ = ‖x‖ := fun x => norm_lin_transpose_of_orth hQ x
  have hv1 : ‖v‖ = 1 := by
    have h1 : lin Qᵀ v = ebasis 0 := by
      rw [hvdef, show lin Qᵀ (lin Q (ebasis 0)) = lin (Qᵀ * Q) (ebasis 0) by rw [lin_mul]; rfl,
        hQQ, lin_one]; rfl
    rw [← hnorm v, h1]; simp [ebasis]
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg (hSh.sub ?_) fun x => ?_
  · exact (posSemidef_act Q (sigmaEps_props hε.le).1).isHermitian
  rw [quad_sub, quad_act, quad_sigmaEps, hnorm]
  have hx0 : (lin Qᵀ x) 0 = ⟪v, x⟫ := by
    have h1 : ⟪(ebasis 0 : Rd d), lin Qᵀ x⟫ = (lin Qᵀ x) 0 := by
      simp [ebasis, EuclideanSpace.inner_single_left]
    rw [← h1, ← inner_lin_left]
  rw [hx0]
  set a := ⟪v, x⟫ with ha
  set w := x - a • v with hw
  have hwv : ⟪w, v⟫ = 0 := by
    rw [hw, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hv1,
      real_inner_comm, ← ha]
    simp
  have hxw : x = a • v + w := by rw [hw]; abel
  have hT : Sᵀ = S := by
    have := hSh.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hcross : ⟪v, lin S w⟫ = 0 := by
    conv_lhs => rw [← hT]
    rw [← inner_lin_left, hQv, real_inner_comm, hwv]
  have hqS : quad S x = a ^ 2 + quad S w := by
    have hq1 : quad S v = 1 := by
      rw [quad, hQv, real_inner_self_eq_norm_sq, hv1, one_pow]
    rw [hxw, quad_add_vec hSh, quad_smul_vec, hq1, inner_smul_left, hcross]
    simp
  have hnx : ‖x‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
    rw [hxw, norm_add_sq_real, inner_smul_left, real_inner_comm, hwv, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hv1]
    simp
  have hqw : lamMin S * ‖w‖ ^ 2 ≤ quad S w := lamMin_mul_norm_sq_le hSh w
  rw [hqS, hnx]
  nlinarith [sq_nonneg ‖w‖]

/-- **An orthogonal `Q` whose first column is a unit eigenvector of `Σ` for `λ_max(Σ)`**. -/
theorem exists_orth_top_eigvec [NeZero d] {S : Mat d} (hSh : S.IsHermitian) :
    ∃ Q ∈ orthSet d, lin S (lin Q (ebasis 0)) = lamMax S • lin Q (ebasis 0) := by
  obtain ⟨v, hv1, hSv⟩ := exists_unit_eigvec_eigUp hSh (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hSh] at hSv
  have he1 : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  set R : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (ebasis 0 - v))ᗮ with hRdef
  have hRe : R (ebasis 0) = v := Submodule.reflection_sub (he1.trans hv1.symm)
  refine ⟨isoMat R, isoMat_mem_orthSet R, ?_⟩
  rw [lin_isoMat]
  change lin S (R (ebasis 0)) = lamMax S • R (ebasis 0)
  rw [hRe, hSv]

/-- **The sandwich of a similarity-equivariant gauge** (`prop:similarity-stable-family`(2),
`prop:similarity-orbit-family`(2)): if `h` carries the Loewner steps of `PD(d)` to Loewner steps
and extends continuously to `PSD(d) ∖ {0}` with values in `PD(d)`, then
`λ_max(h(Σ)) ≥ c₁ := λ_max(h(e₁e₁ᵀ))` whenever `λ_max(Σ) = 1`. -/
theorem gauge_sandwich [NeZero d] (h : Mat d → Mat d)
    (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ))
    (hbar : Mat d → Mat d) (hbar_eq : ∀ S : Mat d, S.PosDef → hbar S = h S)
    (hbar_cont : ContinuousOn hbar {S | S.PosSemidef ∧ S ≠ 0})
    (hbar_pd : ∀ S : Mat d, S.PosSemidef → S ≠ 0 → (hbar S).PosDef)
    (hmono : ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' → loewnerLE (h S) (h S'))
    {S : Mat d} (hS : S.PosDef) (hSmax : lamMax S = 1) :
    lamMax (hbar (sigmaEps d 0)) ≤ lamMax (h S) := by
  have hSh := hS.isHermitian
  have hconj : ∀ S : Mat d, S.PosDef → ∀ Q ∈ orthSet d, h (act Q S) = act Q (h S) := by
    intro S hS Q hQ
    have := hequiv S hS 1 one_pos Q hQ
    simpa only [one_smul, act] using this
  obtain ⟨Q, hQ, hQv⟩ := exists_orth_top_eigvec hSh
  rw [hSmax, one_smul] at hQv
  have hsig0 := sigmaEps_props (d := d) le_rfl
  have hl := lamMin_pos hS
  have hhε : ∀ ε : ℝ, 0 < ε → ε ≤ lamMin S → ε ≤ 1 →
      loewnerLE (act Q (hbar (sigmaEps d ε))) (h S) := by
    intro ε hε hεl hε1
    have hpd : (act Q (sigmaEps d ε)).PosDef :=
      (posDef_act_iff (orthSet_subset_glSet hQ) _).2 (sigmaEps_posDef hε)
    have := hmono _ _ hpd hS (sigmaEps_conj_le hSh hQ hQv hε hεl hε1)
    rwa [hconj _ (sigmaEps_posDef hε) Q hQ, ← hbar_eq _ (sigmaEps_posDef hε)] at this
  have hlim : ∀ x : Rd d, quad (hbar (sigmaEps d 0)) (lin Qᵀ x) ≤ quad (h S) x := by
    intro x
    have h1 : ContinuousWithinAt (fun ε : ℝ => hbar (sigmaEps d ε)) (Ici 0) 0 :=
      (hbar_cont.continuousWithinAt hsig0).comp continuous_sigmaEps.continuousWithinAt
        fun ε hε => sigmaEps_props hε
    have hcont : ContinuousWithinAt (fun ε : ℝ => quad (hbar (sigmaEps d ε)) (lin Qᵀ x))
        (Ici 0) 0 :=
      (continuous_quad _).continuousAt.comp_continuousWithinAt h1
    have htend := (hcont.mono Ioi_subset_Ici_self).tendsto
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hl one_pos)] with ε hε
    have := hhε ε hε.1 (hε.2.le.trans (min_le_left _ _)) (hε.2.le.trans (min_le_right _ _))
    have hq := quad_nonneg this x
    rw [quad_sub, quad_act] at hq
    linarith
  have hQQ : Qᵀ * Q = 1 := orth_transpose_mul hQ
  rw [lamMax_le_iff (hbar_pd _ hsig0.1 hsig0.2).isHermitian]
  intro u hu
  have := hlim (lin Q u)
  rw [show lin Qᵀ (lin Q u) = lin (Qᵀ * Q) u by rw [lin_mul]; rfl, hQQ, lin_one] at this
  refine this.trans (quad_le_lamMax (hh S hS).isHermitian ?_)
  have h2 := norm_lin_transpose_of_orth (transpose_mem_orthSet hQ) u
  rwa [transpose_transpose, hu] at h2

/-- **`prop:similarity-stable-family`(2)**, bounded shape: if `h` is similarity-equivariant, extends
continuously to `PSD(d) ∖ {0}` with values in `PD(d)` (the extension `hbar`), and every
Loewner step in `PD(d)` has a positive finite increment, then `h(I) = h₀I` with `h₀ > 0`,
`c₁ := λ_max(h(e₁e₁ᵀ)) > 0`, and `ecc(h(Σ)) ≤ (h₀/c₁)^α` for every `Σ ∈ PD(d)`. -/
theorem sim_stable_bounded_shape (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef) (σ : Mat d → Measure (Rd d))
    (hσ : ∀ S : Mat d, S.PosDef → IsEllipticalStable α (h S) (σ S))
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ))
    (hbar : Mat d → Mat d) (hbar_eq : ∀ S : Mat d, S.PosDef → hbar S = h S)
    (hbar_cont : ContinuousOn hbar {S | S.PosSemidef ∧ S ≠ 0})
    (hbar_pd : ∀ S : Mat d, S.PosSemidef → S ≠ 0 → (hbar S).PosDef)
    (hinc : HasFiniteLoewnerIncrements fun S => multivariateGaussian 0 (C S) ∗ σ S) :
    ∃ h0 : ℝ, 0 < h0 ∧ h 1 = h0 • (1 : Mat d) ∧ 0 < lamMax (hbar (sigmaEps d 0)) ∧
      ∀ S : Mat d, S.PosDef → ecc (h S) ≤ (h0 / lamMax (hbar (sigmaEps d 0))) ^ α := by
  haveI : NeZero d := ⟨by omega⟩
  have hstep : ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
      stableLE α (h S) (h S') := by
    intro S S' hS hS' hle
    obtain ⟨ρ, hρ, heq⟩ := hinc S S' hS hS' hle
    exact sim_stable_parts_ordered hd hα0 hα2 h C hh hC σ hσ S S' hS hS' ρ hρ heq
  have hloew : ∀ S S' : Mat d, stableLE α S S' → loewnerLE S S' :=
    (stableLE_partialOrder (d := d) hα0 hα2).2.1
  obtain ⟨hh0, hH1⟩ := gauge_one h hh hequiv
  set h0 := h 1 0 0 with hh0def
  have hsig0 := sigmaEps_props (d := d) le_rfl
  set c1 := lamMax (hbar (sigmaEps d 0)) with hc1def
  have hc1 : 0 < c1 := lamMax_pos (hbar_pd _ hsig0.1 hsig0.2)
  refine ⟨h0, hh0, hH1, hc1, ?_⟩
  -- the claim at `λ_max(Σ) = 1`
  have hmain : ∀ S : Mat d, S.PosDef → lamMax S = 1 → ecc (h S) ≤ (h0 / c1) ^ α := by
    intro S hS hSmax
    have hHpd := hh S hS
    have hc1le : c1 ≤ lamMax (h S) :=
      gauge_sandwich h hh hequiv hbar hbar_eq hbar_cont hbar_pd
        (fun S S' hS hS' hle => hloew _ _ (hstep S S' hS hS' hle)) hS hSmax
    have hst := hstep S 1 hS PosDef.one (loewnerLE_one_of_lamMax hS.isHermitian hSmax)
    rw [hH1] at hst
    have htA : tAlpha α (h S) ≤ h0 :=
      (stablePlusLE_le_smul_one_iff hα0 hα2 hHpd hh0.le).1
        (Or.inr (Or.inr ⟨hHpd, PosDef.one.smul hh0, hst⟩))
    -- the arithmetic
    have hη : 0 < lamMax (h S) := lamMax_pos hHpd
    have hη1 : 0 < lamMin (h S) := lamMin_pos hHpd
    have hD := hHpd.det_pos
    have hdet := det_le_lamMin_mul_lamMax_pow hHpd
    have h1 : lamMax (h S) ^ ((d : ℝ) + α) / (h S).det ≤ h0 ^ α := by
      have hnn : 0 ≤ lamMax (h S) ^ ((d : ℝ) + α) / (h S).det := by positivity
      have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) htA hα0.le
      rwa [← Real.rpow_mul hnn, one_div_mul_cancel hα0.ne', Real.rpow_one] at this
    have hsplit : lamMax (h S) ^ ((d : ℝ) + α) =
        lamMax (h S) ^ (d - 1) * (lamMax (h S) * lamMax (h S) ^ α) := by
      have hd1 : ((d : ℝ) + α) = ((d - 1 : ℕ) : ℝ) + (1 + α) := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
      rw [hd1, Real.rpow_add hη, Real.rpow_natCast, Real.rpow_add hη, Real.rpow_one]
    rw [div_le_iff₀ hD, hsplit] at h1
    have hpow : 0 < lamMax (h S) ^ (d - 1) := pow_pos hη _
    have h2 : lamMax (h S) * lamMax (h S) ^ α ≤ h0 ^ α * lamMin (h S) := by
      have h3 : lamMax (h S) ^ (d - 1) * (lamMax (h S) * lamMax (h S) ^ α) ≤
          lamMax (h S) ^ (d - 1) * (h0 ^ α * lamMin (h S)) := by
        calc _ ≤ h0 ^ α * (h S).det := h1
          _ ≤ h0 ^ α * (lamMin (h S) * lamMax (h S) ^ (d - 1)) :=
              mul_le_mul_of_nonneg_left hdet (by positivity)
          _ = _ := by ring
      exact le_of_mul_le_mul_left h3 hpow
    have hηα : 0 < lamMax (h S) ^ α := Real.rpow_pos_of_pos hη _
    unfold ecc
    calc lamMax (h S) / lamMin (h S) ≤ h0 ^ α / lamMax (h S) ^ α := by
          rw [div_le_div_iff₀ hη1 hηα]; linarith
      _ = (h0 / lamMax (h S)) ^ α := (Real.div_rpow hh0.le hη.le _).symm
      _ ≤ (h0 / c1) ^ α :=
          Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hh0.le hc1 hc1le) hα0.le
  intro S hS
  obtain ⟨ht, hS1, hS1max, hhS⟩ := gauge_rescale h hequiv hS
  rw [hhS, ecc_smul ht]
  exact hmain _ hS1 hS1max

/-! ## Clause (3) -/

/-- **The gauge of clause (3)**, `h(Σ) := Σ + κ tr(Σ) I`. -/
noncomputable def traceGauge (κ : ℝ) (S : Mat d) : Mat d := S + (κ * S.trace) • (1 : Mat d)

theorem traceGauge_zero (κ : ℝ) : traceGauge κ (0 : Mat d) = 0 := by
  simp [traceGauge]

theorem traceGauge_isHermitian (κ : ℝ) {S : Mat d} (hS : S.IsHermitian) :
    (traceGauge κ S).IsHermitian :=
  hS.add (isHermitian_one.smul (IsSelfAdjoint.all _))

theorem traceGauge_posDef [NeZero d] {κ : ℝ} (hκ : 0 < κ) {S : Mat d} (hS : S.PosSemidef)
    (h0 : S ≠ 0) : (traceGauge κ S).PosDef :=
  Matrix.PosDef.posSemidef_add hS (PosDef.one.smul (mul_pos hκ (trace_pos_of_posSemidef hS h0)))

theorem act_add (A S S' : Mat d) : act A (S + S') = act A S + act A S' := by
  simp [act, Matrix.mul_add, Matrix.add_mul]

/-- `h(AΣAᵀ) = A h(Σ) Aᵀ` for every similarity `A = cQ`. -/
theorem traceGauge_act_sim (κ : ℝ) {A : Mat d} (hA : A ∈ simSet d) (S : Mat d) :
    traceGauge κ (act A S) = act A (traceGauge κ S) := by
  obtain ⟨c, -, Q, hQ, rfl⟩ := hA
  have hQ' : Q ∈ orthSet d := hQ
  have h1 : ∀ X : Mat d, act (c • Q) X = (c ^ 2) • (Q * X * Qᵀ) := fun X => by
    simp only [act, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  have hI : act (c • Q) (1 : Mat d) = (c ^ 2) • (1 : Mat d) := by
    rw [h1, Matrix.mul_one, orth_mul_transpose hQ']
  rw [traceGauge, traceGauge, act_add, act_smul, hI, h1, trace_smul, trace_conj_orth hQ',
    smul_smul, smul_eq_mul]
  congr 2
  ring

/-- `ψ_{AHAᵀ}(ω) = ψ_H(Aᵀω)`. -/
theorem stableExp_act (α : ℝ) (A H : Mat d) (ω : Rd d) :
    stableExp α (act A H) ω = stableExp α H (lin Aᵀ ω) := by
  rw [stableExp, stableExp, quad_act]

/-- **Condition (c) along the trace gauge**: for `Σ ≤ Σ'` in `PSD(d)`, `Σ ≠ 0`, and
`ακ² - (d+1)κ - 1 ≥ 0`, the relative step `M` of `h(Σ)` to `h(Σ')` has
`det M ≤ λ_min(M)^{d+α}`. -/
theorem traceGauge_step [NeZero d] {α κ : ℝ} (hα0 : 0 < α) (hκ : 0 < κ)
    (hκα : 0 ≤ α * κ ^ 2 - ((d : ℝ) + 1) * κ - 1) {S S' : Mat d} (hS : S.PosSemidef)
    (hS0 : S ≠ 0) (hle : loewnerLE S S') :
    (relStep (traceGauge κ S) (traceGauge κ S')).det ≤
      lamMin (relStep (traceGauge κ S) (traceGauge κ S')) ^ ((d : ℝ) + α) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  set τ := S.trace with hτ
  have hτpos : 0 < τ := trace_pos_of_posSemidef hS hS0
  set P := S' - S with hP
  have hPpsd : P.PosSemidef := hle
  set p := P.trace with hp
  have hp0 : 0 ≤ p := hPpsd.trace_nonneg
  set H := traceGauge κ S with hH
  have hHpd : H.PosDef := traceGauge_posDef hκ hS hS0
  have hS'eq : S' = S + P := by rw [hP]; abel
  have hH1 : traceGauge κ S' = H + (P + (κ * p) • (1 : Mat d)) := by
    rw [hH, traceGauge, traceGauge, hS'eq, trace_add, ← hτ, ← hp]
    rw [show (κ * (τ + p)) • (1 : Mat d) = (κ * τ) • 1 + (κ * p) • 1 by rw [← add_smul]; ring_nf]
    abel
  have hM : relStep H (traceGauge κ S') =
      (relStep H P + (κ * p) • H⁻¹) + (1 : ℝ) • (1 : Mat d) := by
    rw [hH1, relStep_add, relStep_add, relStep_self hHpd, relStep_smul, relStep_one_right hHpd,
      one_smul]
    abel
  set M := relStep H (traceGauge κ S') with hMdef
  have hMpd : M.PosDef := (posDef_relStep_iff hHpd _).2 (by
    rw [hH1]; exact hHpd.add_posSemidef (hPpsd.add (PosSemidef.one.smul (by positivity))))
  have hRP : (relStep H P).PosSemidef := (posSemidef_relStep_iff hHpd P).2 hPpsd
  -- the bounds on `h(Σ)`
  have hlH : κ * τ ≤ lamMin H := by
    rw [hH, traceGauge, lamMin_add_smul_one hS.isHermitian]
    linarith [lamMin_nonneg hS]
  have hlHpos : 0 < lamMin H := lamMin_pos hHpd
  have hmH : lamMax H ≤ (1 + κ) * τ := by
    rw [lamMax_le_iff hHpd.isHermitian]
    intro x hx
    rw [hH, traceGauge, quad_add, quad_smul, quad_one, hx]
    have := (quad_le_lamMax hS.isHermitian hx).trans (lamMax_le_trace hS)
    linarith
  have hmHpos : 0 < lamMax H := lamMax_pos hHpd
  -- `λ_min(M) ≥ 1 + Bu`
  have hlM : 1 + κ * p / ((1 + κ) * τ) ≤ lamMin M := by
    rw [hM, lamMin_add_smul_one ((hRP.isHermitian).add (hHpd.inv.isHermitian.smul
      (IsSelfAdjoint.all _)))]
    have h1 := lamMin_add_ge hRP.isHermitian (hHpd.inv.isHermitian.smul (IsSelfAdjoint.all (κ * p)))
    rw [lamMin_smul (by positivity), lamMin_inv_eq hHpd] at h1
    have h2 := lamMin_nonneg hRP
    have h3 : κ * p / ((1 + κ) * τ) ≤ κ * p * (lamMax H)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (by positivity) hmHpos).2 hmH) (by positivity)
    linarith
  -- `tr M ≤ d + Au`
  have htM : M.trace ≤ d + (1 + d * κ) / κ * (p / τ) := by
    rw [hM, trace_add, trace_add, trace_smul, trace_smul, trace_one, Fintype.card_fin, one_smul,
      smul_eq_mul]
    have h1 := trace_relStep_le hHpd hPpsd
    have h2 := trace_relStep_le hHpd (PosDef.one (n := Fin d)).posSemidef
    rw [relStep_one_right hHpd, trace_one, Fintype.card_fin] at h2
    have h1' : P.trace / lamMin H ≤ p / (κ * τ) := div_le_div_of_nonneg_left hp0 (by positivity) hlH
    have h2' : (d : ℝ) / lamMin H ≤ d / (κ * τ) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) hlH
    have h3 : κ * p * (H⁻¹).trace ≤ κ * p * (d / (κ * τ)) :=
      mul_le_mul_of_nonneg_left (h2.trans h2') (by positivity)
    have h4 : (1 + d * κ) / κ * (p / τ) = p / (κ * τ) + κ * p * (d / (κ * τ)) := by
      field_simp
    rw [h4]
    have := h1.trans h1'
    linarith
  -- the arithmetic–geometric mean inequality and Bernoulli's
  set u := p / τ with hu
  have hu0 : 0 ≤ u := div_nonneg hp0 hτpos.le
  set A := (1 + d * κ) / κ with hA
  set B := κ / (1 + κ) with hB
  have hAB : A ≤ ((d : ℝ) + α) * B := by
    rw [hA, hB, div_le_iff₀ hκ,
      show ((d : ℝ) + α) * (κ / (1 + κ)) * κ = ((d : ℝ) + α) * κ ^ 2 / (1 + κ) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith
  have hlM' : 1 + B * u ≤ lamMin M := by
    have : κ * p / ((1 + κ) * τ) = B * u := by rw [hB, hu]; field_simp
    linarith
  have hBu : 0 ≤ B * u := mul_nonneg (by positivity) hu0
  have hq : 1 ≤ ((d : ℝ) + α) / d := by rw [le_div_iff₀ hdpos]; linarith
  have hbern := one_add_mul_self_le_rpow_one_add (by linarith : (-1 : ℝ) ≤ B * u) hq
  have hstep1 : M.trace / d ≤ 1 + A * u / d := by
    rw [div_le_iff₀ hdpos]
    have : (1 + A * u / d) * d = d + A * u := by field_simp
    linarith
  have hstep2 : 1 + A * u / d ≤ (1 + B * u) ^ (((d : ℝ) + α) / d) := by
    refine le_trans ?_ hbern
    have hAu : A * u ≤ ((d : ℝ) + α) * (B * u) := by
      have := mul_le_mul_of_nonneg_right hAB hu0
      linarith
    have : A * u / d ≤ ((d : ℝ) + α) / d * (B * u) := by
      calc A * u / d ≤ ((d : ℝ) + α) * (B * u) / d := div_le_div_of_nonneg_right hAu hdpos.le
        _ = ((d : ℝ) + α) / d * (B * u) := by ring
    linarith
  have htr0 : 0 ≤ M.trace / d := div_nonneg (by
    rw [← sum_eigUp hMpd.isHermitian]; exact Finset.sum_nonneg fun k _ => (eigUp_pos hMpd k).le)
    hdpos.le
  calc M.det ≤ (M.trace / d) ^ d := det_le_trace_div_pow hMpd
    _ ≤ ((1 + B * u) ^ (((d : ℝ) + α) / d)) ^ d :=
        pow_le_pow_left₀ htr0 (hstep1.trans hstep2) d
    _ = (1 + B * u) ^ ((d : ℝ) + α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), div_mul_cancel₀ _ hdpos.ne']
    _ ≤ lamMin M ^ ((d : ℝ) + α) := Real.rpow_le_rpow (by linarith) hlM' (by positivity)

/-- **The transform of the increments** of clause (3):
`e^{-b⟨ω,(Σ'-Σ)ω⟩ - ψ_{h(Σ')}(ω) + ψ_{h(Σ)}(ω)}`. -/
noncomputable def tgTransform (α κ b : ℝ) (S S' : Mat d) (ω : Rd d) : ℝ :=
  Real.exp (-(b * quad (S' - S) ω) - stableExp α (traceGauge κ S') ω +
    stableExp α (traceGauge κ S) ω)

theorem stableExp_zero_mat {α : ℝ} (hα : 0 < α) (ω : Rd d) : stableExp α (0 : Mat d) ω = 0 := by
  rw [stableExp, quad_zero, Real.zero_rpow (by positivity)]

theorem loewnerLE_trans' {S S' S'' : Mat d} (h : loewnerLE S S') (h' : loewnerLE S' S'') :
    loewnerLE S S'' := by
  unfold loewnerLE at *
  have := h'.add h
  rwa [sub_add_sub_cancel] at this

/-- **The increments of clause (3) exist**: for `Σ ≤ Σ'` in `PSD(d)` there is a probability
measure with transform `tgTransform`. Spends A3(iii) (`exists_stable_increment`,
`exists_ellipticalStable`). -/
theorem exists_traceGauge_increment [NeZero d] {α κ b : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hκ : 0 < κ) (hκα : 0 ≤ α * κ ^ 2 - ((d : ℝ) + 1) * κ - 1) (hb : 0 ≤ b) {S S' : Mat d}
    (hS : S.PosSemidef) (hS' : S'.PosSemidef) (hle : loewnerLE S S') :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      ∀ ω : Rd d, charFun ρ ω = ((tgTransform α κ b S S' ω : ℝ) : ℂ) := by
  obtain ⟨τ, hτ, hτc⟩ : ∃ τ : Measure (Rd d), IsProbabilityMeasure τ ∧ ∀ ω : Rd d,
      charFun τ ω = ((Real.exp (-(stableExp α (traceGauge κ S') ω -
        stableExp α (traceGauge κ S) ω)) : ℝ) : ℂ) := by
    by_cases hS0 : S = 0
    · subst hS0
      by_cases hS'0 : S' = 0
      · subst hS'0
        refine ⟨Measure.dirac 0, inferInstance, fun ω => ?_⟩
        simp [charFun_dirac, traceGauge_zero, stableExp_zero_mat hα0]
      · obtain ⟨μ, hμ, -⟩ := exists_ellipticalStable hα0 hα2 (traceGauge_posDef hκ hS' hS'0)
        refine ⟨μ, hμ.1, fun ω => ?_⟩
        rw [hμ.2, traceGauge_zero, stableExp_zero_mat hα0, sub_zero]
    · have hS'0 : S' ≠ 0 := by
        rintro rfl
        unfold loewnerLE at hle
        rw [zero_sub] at hle
        exact hS0 (eq_zero_of_posSemidef_neg hS hle)
      have hH := traceGauge_posDef hκ hS hS0
      have hH' := traceGauge_posDef hκ hS' hS'0
      have hord := (stable_density_order_iff hα0 hα2 hH hH').1.2
        (traceGauge_step hα0 hκ hκα hS hS0 hle)
      obtain ⟨ρ, hρ, -, -, hc⟩ := exists_stable_increment hα0 hα2 hH hH' hord
      exact ⟨ρ, hρ, hc⟩
  refine ⟨multivariateGaussian 0 ((2 * b) • (S' - S)) ∗ τ, inferInstance, fun ω => ?_⟩
  have hP : ((2 * b) • (S' - S)).PosSemidef := PosSemidef.smul hle (by positivity)
  rw [charFun_conv, charFun_multivariateGaussian_zero hP, hτc, ← Complex.ofReal_mul,
    ← Real.exp_add, tgTransform, quad_smul]
  congr 2
  ring

theorem continuous_traceGauge (κ : ℝ) : Continuous fun S : Mat d => traceGauge κ S := by
  unfold traceGauge
  exact continuous_id.add ((continuous_const.mul continuous_id.matrix_trace).smul continuous_const)

theorem continuous_stableExp_traceGauge {α : ℝ} (hα : 0 < α) (κ : ℝ) (ω : Rd d) :
    Continuous fun S : Mat d => stableExp α (traceGauge κ S) ω := by
  unfold stableExp
  exact (Real.continuous_rpow_const (by positivity)).comp
    ((continuous_quad ω).comp (continuous_traceGauge κ))

/-- **`prop:similarity-stable-family`(3)**, a family that is not shape-blind: for `b ≥ 0`, `κ > 0`
with `ακ² - (d+1)κ - 1 ≥ 0`, `h(Σ) := Σ + κ tr(Σ) I` and `C(Σ) := 2bΣ` on `PSD(d)`, every Loewner
step `Σ ≤ Σ'` in `PSD(d)` has a probability increment `ρ_{Σ,Σ'}`, the increments satisfy (K1), (K2),
(K4) and (K3) for every similarity, and the stable part `S_α(h(Σ))` is rotation invariant only when
`Σ` is a multiple of `I`. Spends A3(iii). -/
theorem sim_stable_not_shape_blind (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (b κ : ℝ)
    (hb : 0 ≤ b) (hκ : 0 < κ) (hκα : 0 ≤ α * κ ^ 2 - ((d : ℝ) + 1) * κ - 1)
    (σ : Mat d → Measure (Rd d))
    (hσ : ∀ S : Mat d, S.PosSemidef →
      IsEllipticalStable α (S + (κ * S.trace) • (1 : Mat d)) (σ S)) :
    ∃ ρ : Mat d → Mat d → Measure (Rd d),
      (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
        IsProbabilityMeasure (ρ S S') ∧
        multivariateGaussian 0 ((2 * b) • S') ∗ σ S' =
          (multivariateGaussian 0 ((2 * b) • S) ∗ σ S) ∗ ρ S S') ∧
      IsGWCascadeFamily (simSet d) loewnerLE ρ ∧
      ∀ S : Mat d, S.PosSemidef → IsRotationInvariant (σ S) → ∃ c : ℝ, S = c • (1 : Mat d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hσ' : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable α (traceGauge κ S) (σ S) := hσ
  classical
  let ρ : Mat d → Mat d → Measure (Rd d) := fun S S' =>
    if h : S.PosSemidef ∧ S'.PosSemidef ∧ loewnerLE S S' then
      Classical.choose (exists_traceGauge_increment hα0 hα2 hκ hκα hb h.1 h.2.1 h.2.2)
    else Measure.dirac 0
  have hρ : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      IsProbabilityMeasure (ρ S S') ∧
        ∀ ω : Rd d, charFun (ρ S S') ω = ((tgTransform α κ b S S' ω : ℝ) : ℂ) := by
    intro S S' hS hS' hle
    have h : S.PosSemidef ∧ S'.PosSemidef ∧ loewnerLE S S' := ⟨hS, hS', hle⟩
    simp only [ρ, dif_pos h]
    exact Classical.choose_spec (exists_traceGauge_increment hα0 hα2 hκ hκα hb hS hS' hle)
  have hrefl : ∀ S : Mat d, loewnerLE S S := fun S => by
    unfold loewnerLE; rw [sub_self]; exact PosSemidef.zero
  refine ⟨ρ, fun S S' hS hS' hle => ⟨(hρ S S' hS hS' hle).1, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the increment identity
    haveI := (hρ S S' hS hS' hle).1
    haveI := (hσ' S hS).1
    haveI := (hσ' S' hS').1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, charFun_conv, charFun_conv, (hρ S S' hS hS' hle).2,
      charFun_multivariateGaussian_zero (hS.smul (by positivity)),
      charFun_multivariateGaussian_zero (hS'.smul (by positivity)), (hσ' S hS).2, (hσ' S' hS').2,
      tgTransform]
    simp only [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    rw [quad_smul, quad_smul, quad_sub]
    ring
  · exact fun p hp => (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).1
  · intro S hS
    haveI := (hρ S S hS hS (hrefl S)).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [(hρ S S hS hS (hrefl S)).2, charFun_dirac, tgTransform, sub_self, quad_zero]
    simp
  · intro S S' S'' hS hS' hS'' h h'
    have h'' := loewnerLE_trans' h h'
    haveI := (hρ S S'' hS hS'' h'').1
    haveI := (hρ S' S'' hS' hS'' h').1
    haveI := (hρ S S' hS hS' h).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, (hρ S S'' hS hS'' h'').2, (hρ S' S'' hS' hS'' h').2, (hρ S S' hS hS' h).2,
      ← Complex.ofReal_mul, tgTransform, tgTransform, tgTransform, ← Real.exp_add]
    congr 2
    rw [quad_sub, quad_sub, quad_sub]
    ring
  · intro ω
    have hc : Continuous fun p : Mat d × Mat d => ((tgTransform α κ b p.1 p.2 ω : ℝ) : ℂ) := by
      unfold tgTransform
      refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
      refine ((((continuous_quad ω).comp (continuous_snd.sub continuous_fst)).const_mul b).neg.sub
        ((continuous_stableExp_traceGauge hα0 κ ω).comp continuous_snd)).add
        ((continuous_stableExp_traceGauge hα0 κ ω).comp continuous_fst)
    refine hc.continuousOn.congr fun p hp => ?_
    exact (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).2 ω
  · intro A hA p hp
    have hAgl : A ∈ glSet d := by
      obtain ⟨c, hc, Q, hQ, rfl⟩ := hA
      change IsUnit (c • Q).det
      rw [det_smul]
      refine isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hc.ne') ?_)
      have := orth_mul_transpose (show Q ∈ orthSet d from hQ)
      intro h0
      have h1 := congrArg Matrix.det this
      rw [det_mul, h0, zero_mul, det_one] at h1
      exact zero_ne_one h1
    have hp' : (act A p.1, act A p.2) ∈ wedgePairs (loewnerLE (d := d)) :=
      ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1, loewnerLE_act A hp.2.2⟩
    haveI := (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).1
    haveI := (hρ _ _ hp'.1 hp'.2.1 hp'.2.2).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).2,
      (hρ _ _ hp'.1 hp'.2.1 hp'.2.2).2, tgTransform, tgTransform, act_sub, quad_act,
      traceGauge_act_sim κ hA, traceGauge_act_sim κ hA, stableExp_act, stableExp_act]
  · intro h0
    have hpair : (0 : Mat d).PosSemidef ∧ (1 : Mat d).PosSemidef ∧ loewnerLE (0 : Mat d) 1 :=
      ⟨PosSemidef.zero, PosSemidef.one, by unfold loewnerLE; rw [sub_zero]; exact PosSemidef.one⟩
    have h1 := congrArg (fun m => charFun m (ebasis (0 : Fin d))) h0
    rw [(hρ 0 1 hpair.1 hpair.2.1 hpair.2.2).2, charFun_dirac] at h1
    have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
    have hq : stableExp α (traceGauge κ (1 : Mat d)) (ebasis 0) = (1 + κ * d) ^ (α / 2) := by
      rw [stableExp, traceGauge, quad_add, quad_smul, quad_one, he, trace_one, Fintype.card_fin]
      ring_nf
    have hpos : 0 < (1 + κ * d) ^ (α / 2) := Real.rpow_pos_of_pos (by positivity) _
    rw [tgTransform, hq, traceGauge_zero, stableExp_zero_mat hα0, sub_zero, quad_one, he] at h1
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
    have h2 : Real.exp (-(b * 1 ^ 2) - (1 + κ * d) ^ (α / 2) + 0) = 1 := by exact_mod_cast h1
    rw [Real.exp_eq_one_iff] at h2
    nlinarith
  · intro S hS hrot
    have hSeq : S = traceGauge κ S - (κ * S.trace) • (1 : Mat d) := by
      rw [traceGauge]; abel
    set H := traceGauge κ S with hHdef
    have hHh : H.IsHermitian := traceGauge_isHermitian κ hS.isHermitian
    have hHpsd : H.PosSemidef := hS.add (PosSemidef.one.smul (mul_nonneg hκ.le hS.trace_nonneg))
    have hinv : ∀ Q ∈ orthSet d, act Q H = H := by
      intro Q hQ
      have hQH : (act Q H).IsHermitian := (posSemidef_act Q hHpsd).isHermitian
      refine eq_of_quad_eq hQH hHh fun ω => ?_
      haveI := (hσ' S hS).1
      have h1 := congrArg (fun m => charFun m ω) (hrot Q hQ)
      simp only [push, charFun_map_lin, (hσ' S hS).2] at h1
      have h2 : stableExp α H (lin Qᵀ ω) = stableExp α H ω := by
        have := Complex.ofReal_injective h1
        simpa using this
      rw [stableExp, stableExp, Real.rpow_left_inj (quad_nonneg hHpsd _) (quad_nonneg hHpsd _)
        (by positivity)] at h2
      rw [quad_act, h2]
    have hH := eq_smul_one_of_orth_invariant hinv
    refine ⟨H 0 0 - κ * S.trace, ?_⟩
    calc S = H - (κ * S.trace) • (1 : Mat d) := hSeq
      _ = (H 0 0 - κ * S.trace) • (1 : Mat d) := by rw [sub_smul, ← hH]

end AffineHemigroup
