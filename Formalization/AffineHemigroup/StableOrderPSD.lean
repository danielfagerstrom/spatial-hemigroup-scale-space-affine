/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableOrder
import AffineHemigroup.OrderedSpectrum
import AffineHemigroup.Defs.SmallerGroups

/-!
# `lem:stable-order-psd`: the stable order on `PSD(d)`

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `lem:stable-order-psd` (wave 1, group D,
Q-0281), `prop:similarity-stable-order-families`(1): `Σ ≤_α Σ'` when `Σ = 0`, or `Σ' = cΣ` with
`c ≥ 1`, or `Σ, Σ' ∈ PD(d)` with `Σ ≼_α Σ'`. `stablePlusLE_order` collects the node: a partial order
on `PSD(d)`, `GL(d)`-invariant, with the rays, inside the Loewner order, with the path condition,
a wedge datum for every closed subgroup containing the dilations, monotone in `α`, and the two
thresholds `ε_α(Σ)`, `t_α(Σ)` with `t_α/ε_α = ecc(Σ)^{(d+α)/α}`.

**The chains** (the path condition) are the blueprint's: `γ(s) = sΣ'` from `0`,
`γ(s) = (1 + s(c-1))Σ` along a ray, and `γ(s) = Σ^{1/2}M^sΣ^{1/2}` on `PD(d)`. The power `M^s` is
written through Mathlib's spectral theorem, `M^s = U diag(m^s) Uᵀ`, rather than through
`lem:path-condition-orders` (not proved yet), and the monotonicity of the chain is read from the
densities (`stableLE_iff_density`): with `x = Σ^{1/2}y` and `z = Uᵀy`, `n_{γ(s)}(x)` is a positive
multiple of `(det M)^{-s/2}(∑ m_i^{-s}z_i²)^{-(d+α)/2}`, and
`∑ m_i^{-t}z_i² ≤ λ_min^{-(t-s)} ∑ m_i^{-s}z_i²`
with `det M ≤ λ_min^{d+α}` gives the order. Lean core only.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ### The order on `PSD(d)`, by cases -/

/-- A positive definite matrix is not `0` (`d ≥ 1`). -/
theorem PosDef_ne_zero' [NeZero d] {S : Mat d} (hS : S.PosDef) : S ≠ 0 := by
  intro h
  have := hS.det_pos
  rw [h, Matrix.det_zero ⟨0⟩] at this
  exact lt_irrefl _ this

/-- On `PD(d)`, `≤_α` is `≼_α`. -/
theorem stablePlusLE_iff_of_posDef [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) : stablePlusLE α S S' ↔ stableLE α S S' := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr ⟨hS, hS', h⟩)⟩
  rcases h with h0 | ⟨c, hc, rfl⟩ | ⟨-, -, h⟩
  · exact absurd h0 (PosDef_ne_zero' hS)
  · have := (stableLE_rays_not_rank_deficient (d := d) hα0 hα2).1 S hS (Real.sqrt c)
      (Real.one_le_sqrt.2 hc)
    rwa [Real.sq_sqrt (by linarith)] at this
  · exact h

/-- `≤_α` contains the rays: `cΣ ≤_α c'Σ` for `0 ≤ c ≤ c'`. -/
theorem stablePlusLE_rays (α : ℝ) (S : Mat d) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c') :
    stablePlusLE α (c • S) (c' • S) := by
  rcases hc.lt_or_eq with hc | rfl
  · refine Or.inr (Or.inl ⟨c' / c, (one_le_div hc).2 hcc', ?_⟩)
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']
  · exact Or.inl (zero_smul _ _)

/-- `≤_α` is contained in the Loewner order on `PSD(d)`. -/
theorem stablePlusLE_loewner [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' : Mat d}
    (hS : S.PosSemidef) (hS' : S'.PosSemidef) (h : stablePlusLE α S S') : loewnerLE S S' := by
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · simpa [loewnerLE] using hS'
  · unfold loewnerLE
    rw [show c • S - S = (c - 1) • S by rw [sub_smul, one_smul]]
    exact hS.smul (by linarith)
  · exact (stable_density_order_iff hα0 hα2 h1 h2).2 h.2.2.2

/-- `≤_α` is transitive on `PSD(d)`. -/
theorem stablePlusLE_trans [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' S'' : Mat d}
    (hS : S.PosSemidef) (h : stablePlusLE α S S') (h' : stablePlusLE α S' S'') :
    stablePlusLE α S S'' := by
  have htr := (stableLE_partialOrder (d := d) hα0 hα2).1.trans
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · exact Or.inl rfl
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨h1', h2', h'⟩
    · rcases smul_eq_zero.1 h0 with h | h
      · linarith
      · exact Or.inl h
    · exact Or.inr (Or.inl ⟨c' * c, one_le_mul_of_one_le_of_one_le hc' hc, by rw [smul_smul]⟩)
    · -- `cΣ` is definite, so `Σ` is
      have hSpd : S.PosDef := by
        have := h1'.smul (inv_pos.2 (by linarith : (0 : ℝ) < c))
        rwa [smul_smul, inv_mul_cancel₀ (by linarith : c ≠ 0), one_smul] at this
      have hray : stableLE α S (c • S) := by
        have := (stableLE_rays_not_rank_deficient (d := d) hα0 hα2).1 S hSpd (Real.sqrt c)
          (Real.one_le_sqrt.2 hc)
        rwa [Real.sq_sqrt (by linarith)] at this
      exact Or.inr (Or.inr ⟨hSpd, h2', htr S hSpd _ h1' S'' h2' hray h'⟩)
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨-, h2', h'⟩
    · exact absurd h0 (PosDef_ne_zero' h2)
    · have hray : stableLE α S' (c' • S') := by
        have := (stableLE_rays_not_rank_deficient (d := d) hα0 hα2).1 S' h2 (Real.sqrt c')
          (Real.one_le_sqrt.2 hc')
        rwa [Real.sq_sqrt (by linarith)] at this
      exact Or.inr (Or.inr ⟨h1, hray.2.1, htr S h1 S' h2 _ hray.2.1 h hray⟩)
    · exact Or.inr (Or.inr ⟨h1, h2', htr S h1 S' h2 _ h2' h h'⟩)

/-- `≤_α` is `GL(d)`-invariant. -/
theorem stablePlusLE_act [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {A : Mat d}
    (hA : A ∈ glSet d) {S S' : Mat d} (h : stablePlusLE α S S') :
    stablePlusLE α (act A S) (act A S') := by
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · exact Or.inl (by simp [act])
  · exact Or.inr (Or.inl ⟨c, hc, act_smul A c S⟩)
  · refine Or.inr (Or.inr ⟨(posDef_act_iff hA S).2 h1, (posDef_act_iff hA S').2 h2, ?_⟩)
    exact ((stableLE_partialOrder (d := d) hα0 hα2).2.2 A hA S S' h1 h2).1 h

/-! ### The chains -/

/-- The spectral theorem in the form used here: `M = U diag(m) Uᵀ` with `U` orthogonal and `m`
Mathlib's eigenvalues. -/
theorem exists_orth_diag {M : Mat d} (hM : M.IsHermitian) :
    ∃ U : Mat d, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ M = U * diagonal hM.eigenvalues * Uᵀ := by
  set U : Mat d := (hM.eigenvectorUnitary : Mat d)
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [← hstar]; exact Unitary.coe_mul_star_self _
  · rw [← hstar]; exact Unitary.coe_star_mul_self _
  · have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simp at h
    rw [← hstar]
    exact h

/-- `⟨y, U diag(w) Uᵀ y⟩ = ∑ wᵢ ((Uᵀy)ᵢ)²`. -/
theorem quad_orth_diag (U : Mat d) (w : Fin d → ℝ) (y : Rd d) :
    quad (U * diagonal w * Uᵀ) y = ∑ i, w i * ((lin Uᵀ y) i) ^ 2 := by
  have : quad (U * diagonal w * Uᵀ) y = quad (diagonal w) (lin Uᵀ y) := by
    rw [← quad_act]; rfl
  rw [this, quad_eq_dotProduct]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The chain on `PD(d)`**: for `Σ ≼_α Σ'`, `γ(s) = Σ^{1/2}U diag(m^s)Uᵀ Σ^{1/2}` is a chain. -/
theorem stableLE_chain [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' : Mat d}
    (h : stableLE α S S') : ∃ γ : ℝ → Mat d, IsWChain (psdSet d) (stablePlusLE α) γ S S' := by
  obtain ⟨hS, hS', hMK⟩ := h
  set A := msqrt S with hA
  set M := relStep S S' with hMdef
  have hM : M.PosDef := hMK.1
  have hcond : M.det ≤ lamMin M ^ ((d : ℝ) + α) := hMK.2
  obtain ⟨U, hUU, hUU', hMdiag⟩ := exists_orth_diag hM.isHermitian
  set m := hM.isHermitian.eigenvalues with hm
  have hmpos : ∀ i, 0 < m i := hM.eigenvalues_pos
  have hl := lamMin_pos hM
  have hml : ∀ i, lamMin M ≤ m i := fun i => by
    rw [lamMin_eq_eigUp_zero hM.isHermitian]; exact eigUp_zero_le hM.isHermitian i
  have hUgl : U ∈ glSet d := by
    change IsUnit U.det
    have h1 : U.det * Uᵀ.det = 1 := by rw [← det_mul, hUU, det_one]
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1)
  -- the powers of `M`
  set P : ℝ → Mat d := fun s => U * diagonal (fun i => m i ^ s) * Uᵀ with hP
  have hPpd : ∀ s, (P s).PosDef := fun s => by
    change (act U (diagonal fun i => m i ^ s)).PosDef
    rw [posDef_act_iff hUgl, posDef_diagonal_iff]
    exact fun i => rpow_pos_of_pos (hmpos i) s
  have hPinv : ∀ s, (P s)⁻¹ = P (-s) := fun s => by
    apply Matrix.inv_eq_right_inv
    simp only [hP]
    rw [show U * diagonal (fun i => m i ^ s) * Uᵀ * (U * diagonal (fun i => m i ^ (-s)) * Uᵀ) =
      U * (diagonal (fun i => m i ^ s) * (Uᵀ * U) * diagonal (fun i => m i ^ (-s))) * Uᵀ by
        simp only [Matrix.mul_assoc], hUU', Matrix.mul_one, diagonal_mul_diagonal]
    rw [show (fun i => m i ^ s * m i ^ (-s)) = fun _ => (1 : ℝ) by
      funext i; rw [← rpow_add (hmpos i), add_neg_cancel, rpow_zero]]
    simp [hUU]
  have hPdet : ∀ s, (P s).det = M.det ^ s := fun s => by
    simp only [hP]
    rw [det_mul, det_mul, det_diagonal, mul_comm (U.det), mul_assoc, ← det_mul, hUU, det_one,
      mul_one, Real.finsetProd_rpow _ _ (fun i _ => (hmpos i).le),
      hM.isHermitian.det_eq_prod_eigenvalues]
    rfl
  have hP0 : P 0 = 1 := by
    simp [hP, hUU]
  have hP1 : P 1 = M := by
    simp only [hP, rpow_one]
    exact hMdiag.symm
  set γ : ℝ → Mat d := fun s => A * P s * A with hγ
  have hγpd : ∀ s, (γ s).PosDef := fun s => posDef_msqrt_conj hS (hPpd s)
  refine ⟨γ, ⟨?_, fun s _ => (hγpd s).posSemidef, fun s _ t _ hst => ?_, ?_, ?_⟩⟩
  · -- continuity
    apply Continuous.continuousOn
    refine (continuous_const.matrix_mul (Continuous.matrix_mul (continuous_const.matrix_mul
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const)).matrix_mul
      continuous_const
    exact continuous_const.rpow continuous_id fun _ => Or.inl (hmpos i).ne'
  · -- monotonicity, through the densities
    refine Or.inr (Or.inr ⟨hγpd s, hγpd t, ?_⟩)
    rw [stableLE_iff_density hα0 hα2 (hγpd s) (hγpd t),
      forall_ne_zero_lin_iff (msqrt_mem_glSet hS)]
    intro y hy
    have hAU : IsUnit A.det := msqrt_mem_glSet hS
    -- the quadratic form of `γ(s)⁻¹` at `Ay` is that of `P(-s)` at `y`
    have hq : ∀ r, quad (γ r)⁻¹ (lin A y) = quad (P (-r)) y := fun r => by
      have hinv : (γ r)⁻¹ = act A⁻¹ (P (-r)) := by
        simp only [hγ]
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hPinv, act, hA, msqrt_inv_transpose]
        simp only [hP, Matrix.mul_assoc]
      rw [hinv, quad_act, hA, msqrt_inv_transpose, ← hA, lin_inv_mul_apply hAU]
    have hdet : ∀ r, (γ r).det = S.det * M.det ^ r := fun r => by
      simp only [hγ]; rw [hA, det_msqrt_conj hS, hPdet]
    set z := lin Uᵀ y with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hy
      have := congrArg (lin U) h0
      rw [hz, show lin U (lin Uᵀ y) = lin (U * Uᵀ) y by rw [lin_mul]; rfl, hUU, lin_one,
        map_zero] at this
      exact this
    have hQ : ∀ r, quad (P (-r)) y = ∑ i, m i ^ (-r) * z i ^ 2 := fun r => by
      simp only [hP]; rw [quad_orth_diag]
    have hQpos : ∀ r, 0 < quad (P (-r)) y := fun r => quad_pos (hPpd _) hy
    -- `Q_t ≤ λ_min^{-(t-s)} Q_s`
    have hQts : quad (P (-t)) y ≤ lamMin M ^ (-(t - s)) * quad (P (-s)) y := by
      rw [hQ, hQ, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : m i ^ (-t) = m i ^ (-(t - s)) * m i ^ (-s) := by
        rw [← rpow_add (hmpos i)]; ring_nf
      have h2 : m i ^ (-(t - s)) ≤ lamMin M ^ (-(t - s)) :=
        rpow_le_rpow_of_nonpos hl (hml i) (by linarith)
      rw [h1, mul_assoc]
      exact mul_le_mul_of_nonneg_right h2
        (mul_nonneg (rpow_pos_of_pos (hmpos i) _).le (sq_nonneg _))
    have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
    unfold stableDensity
    rw [hq, hq, hdet, hdet]
    set p := ((d : ℝ) + α) / 2 with hp
    have hp0 : 0 < p := by positivity
    have hD := hM.det_pos
    set Qs := quad (P (-s)) y
    set Qt := quad (P (-t)) y
    have hQs := hQpos s
    have hQt := hQpos t
    -- compare through logarithms
    have key : (M.det ^ s) ^ (-(1 : ℝ) / 2) * Qs ^ (-((d : ℝ) + α) / 2) ≤
        (M.det ^ t) ^ (-(1 : ℝ) / 2) * Qt ^ (-((d : ℝ) + α) / 2) := by
      rw [← rpow_mul hD.le, ← rpow_mul hD.le,
        ← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hD,
        Real.log_rpow hD, Real.log_rpow hQs, Real.log_rpow hQt]
      have h1 : Real.log Qt ≤ -(t - s) * Real.log (lamMin M) + Real.log Qs := by
        have := Real.log_le_log hQt hQts
        rwa [Real.log_mul (by positivity) hQs.ne', Real.log_rpow hl] at this
      have h2 : Real.log M.det ≤ ((d : ℝ) + α) * Real.log (lamMin M) := by
        have := Real.log_le_log hD hcond
        rwa [Real.log_rpow hl] at this
      have hts : 0 ≤ t - s := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hts
      have hq0 : 0 < (d : ℝ) + α := by positivity
      have h4 := mul_le_mul_of_nonneg_left h1 hq0.le
      nlinarith
    have hK : 0 < (stableConst (d := d) α)⁻¹ * S.det ^ (-(1 : ℝ) / 2) :=
      mul_pos (inv_pos.2 hc) (rpow_pos_of_pos hS.det_pos _)
    rw [mul_rpow hS.det_pos.le (by positivity), mul_rpow hS.det_pos.le (by positivity)]
    calc (stableConst (d := d) α)⁻¹ * (S.det ^ (-(1 : ℝ) / 2) * (M.det ^ s) ^ (-(1 : ℝ) / 2)) *
          Qs ^ (-((d : ℝ) + α) / 2)
        = ((stableConst (d := d) α)⁻¹ * S.det ^ (-(1 : ℝ) / 2)) *
          ((M.det ^ s) ^ (-(1 : ℝ) / 2) * Qs ^ (-((d : ℝ) + α) / 2)) := by ring
      _ ≤ ((stableConst (d := d) α)⁻¹ * S.det ^ (-(1 : ℝ) / 2)) *
          ((M.det ^ t) ^ (-(1 : ℝ) / 2) * Qt ^ (-((d : ℝ) + α) / 2)) :=
          mul_le_mul_of_nonneg_left key hK.le
      _ = _ := by ring
  · simp only [hγ, hP0, Matrix.mul_one, hA, msqrt_mul_self hS.posSemidef]
  · simp only [hγ, hP1, hA, hMdef, msqrt_mul_relStep hS]

/-- **The path condition (P)** for `≤_α`. -/
theorem stablePlusLE_hasPathCondition [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    HasPathCondition (stablePlusLE (d := d) α) := by
  intro S S' hS hS' h
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨-, -, h⟩
  · refine ⟨fun s => s • S', ⟨by fun_prop, fun s hs => hS'.smul hs.1, fun s hs t _ hst =>
      stablePlusLE_rays α S' hs.1 hst, by simp, by simp⟩⟩
  · refine ⟨fun s => (1 + s * (c - 1)) • S, ⟨by fun_prop, fun s hs => hS.smul (by nlinarith [hs.1]),
      fun s hs t _ hst => stablePlusLE_rays α S (by nlinarith [hs.1]) (by nlinarith), by simp,
      by simp⟩⟩
  · exact stableLE_chain hα0 hα2 h

/-! ### The thresholds `ε_α(Σ)` and `t_α(Σ)` -/

/-- `λ_max(Σ) = λ_min(Σ⁻¹)⁻¹` on `PD(d)`. -/
theorem lamMax_eq_inv_lamMin_inv [NeZero d] {S : Mat d} (hS : S.PosDef) :
    lamMax S = (lamMin S⁻¹)⁻¹ := by
  have hSi : S⁻¹.PosDef := hS.inv
  have hl := lamMin_pos hSi
  have hii : S⁻¹⁻¹ = S := nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det S).1 hS.isUnit)
  have hup : ∀ u : {x : Rd d // ‖x‖ = 1}, ⟪(u : Rd d), lin S u⟫ ≤ (lamMin S⁻¹)⁻¹ := by
    intro u
    have h := lamMin_mul_quad_inv_le hSi u
    rw [hii, u.2, one_pow] at h
    have := mul_le_mul_of_nonneg_left h (inv_pos.2 hl).le
    rwa [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul, mul_one] at this
  obtain ⟨v, hv, hqv⟩ := exists_quad_inv_eq hSi
  rw [hii] at hqv
  haveI : Nonempty {x : Rd d // ‖x‖ = 1} := ⟨⟨v, hv⟩⟩
  unfold lamMax
  refine le_antisymm (ciSup_le hup) ?_
  have hb : BddAbove (Set.range fun x : {x : Rd d // ‖x‖ = 1} => ⟪(x : Rd d), lin S x⟫) :=
    ⟨_, by rintro _ ⟨x, rfl⟩; exact hup x⟩
  exact hqv.symm.trans_le (le_ciSup hb ⟨v, hv⟩)

/-- `I^{-1/2} Σ I^{-1/2} = Σ`. -/
theorem relStep_one_left (S : Mat d) : relStep 1 S = S := by
  rw [relStep, msqrt, CFC.sqrt_one, inv_one, Matrix.one_mul, Matrix.mul_one]

/-- `Σ^{-1/2} I Σ^{-1/2} = Σ⁻¹` on `PD(d)`. -/
theorem relStep_one_right {S : Mat d} (hS : S.PosDef) : relStep S 1 = S⁻¹ := by
  rw [relStep, Matrix.mul_one]
  conv_rhs => rw [← msqrt_mul_self hS.posSemidef]
  rw [Matrix.mul_inv_rev]

/-- `det Σ⁻¹ = (det Σ)⁻¹` on `PD(d)`. -/
theorem det_inv_of_posDef {S : Mat d} (hS : S.PosDef) : S⁻¹.det = S.det⁻¹ := by
  have h : S.det * S⁻¹.det = 1 := by
    rw [← det_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).1 hS.isUnit), det_one]
  exact eq_inv_of_mul_eq_one_right h

/-- **`ε I ≤_α Σ ⇔ ε ≤ ε_α(Σ)`** for `Σ ∈ PD(d)` and `ε ≥ 0`. -/
theorem stablePlusLE_smul_one_iff [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S : Mat d}
    (hS : S.PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    stablePlusLE α (ε • (1 : Mat d)) S ↔ ε ≤ epsAlpha α S := by
  have hl := lamMin_pos hS
  have hD := hS.det_pos
  rcases hε.lt_or_eq with hε | rfl
  · have hεpd : (ε • (1 : Mat d)).PosDef := PosDef.one.smul hε
    rw [stablePlusLE_iff_of_posDef hα0 hα2 hεpd hS]
    have hM : relStep (ε • (1 : Mat d)) S = ε⁻¹ • S := by
      rw [relStep_smul_left hε PosDef.one, relStep_one_left]
    have hMpd : (ε⁻¹ • S).PosDef := hS.smul (inv_pos.2 hε)
    unfold stableLE stepLE stableStepSet
    simp only [mem_setOf_eq, hM]
    rw [det_smul, Fintype.card_fin, lamMin_smul (inv_pos.2 hε).le]
    unfold epsAlpha
    have hq : 0 < (d : ℝ) + α := by positivity
    have hiff : (ε⁻¹ ^ d * S.det ≤ (ε⁻¹ * lamMin S) ^ ((d : ℝ) + α)) ↔
        ε ≤ (lamMin S ^ ((d : ℝ) + α) / S.det) ^ (1 / α) := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity),
        ← Real.log_le_log_iff hε (by positivity), Real.log_mul (by positivity) hD.ne',
        Real.log_pow, Real.log_rpow (by positivity), Real.log_mul (by positivity) hl.ne',
        Real.log_inv, Real.log_rpow (by positivity), Real.log_div (by positivity) hD.ne',
        Real.log_rpow hl,
        show 1 / α * (((d : ℝ) + α) * Real.log (lamMin S) - Real.log S.det) =
          (((d : ℝ) + α) * Real.log (lamMin S) - Real.log S.det) / α by ring,
        le_div_iff₀ hα0]
      constructor <;> intro h <;> nlinarith
    rw [← hiff]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hεpd, hS, hMpd, h⟩⟩
  · simp only [zero_smul]
    exact ⟨fun _ => rpow_nonneg (div_nonneg (rpow_nonneg hl.le _) hD.le) _,
      fun _ => Or.inl rfl⟩

/-- **`Σ ≤_α tI ⇔ t ≥ t_α(Σ)`** for `Σ ∈ PD(d)` and `t ≥ 0`. -/
theorem stablePlusLE_le_smul_one_iff [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {S : Mat d} (hS : S.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    stablePlusLE α S (t • (1 : Mat d)) ↔ tAlpha α S ≤ t := by
  have hD := hS.det_pos
  have hSi : S⁻¹.PosDef := hS.inv
  have hlmax : lamMax S = (lamMin S⁻¹)⁻¹ := lamMax_eq_inv_lamMin_inv hS
  have hli := lamMin_pos hSi
  have hlpos : 0 < lamMax S := by rw [hlmax]; exact inv_pos.2 hli
  have htA : 0 < tAlpha α S := by unfold tAlpha; positivity
  rcases ht.lt_or_eq with ht | rfl
  · have htpd : (t • (1 : Mat d)).PosDef := PosDef.one.smul ht
    rw [stablePlusLE_iff_of_posDef hα0 hα2 hS htpd]
    have hM : relStep S (t • (1 : Mat d)) = t • S⁻¹ := by
      rw [relStep_smul, relStep_one_right hS]
    have hMpd : (t • S⁻¹).PosDef := hSi.smul ht
    unfold stableLE stepLE stableStepSet
    simp only [mem_setOf_eq, hM]
    rw [det_smul, Fintype.card_fin, lamMin_smul ht.le, det_inv_of_posDef hS,
      show lamMin S⁻¹ = (lamMax S)⁻¹ by rw [hlmax, inv_inv]]
    unfold tAlpha
    have hiff : (t ^ d * S.det⁻¹ ≤ (t * (lamMax S)⁻¹) ^ ((d : ℝ) + α)) ↔
        (lamMax S ^ ((d : ℝ) + α) / S.det) ^ (1 / α) ≤ t := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity),
        ← Real.log_le_log_iff (by positivity) ht, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_inv, Real.log_rpow (by positivity),
        Real.log_mul ht.ne' (by positivity), Real.log_inv, Real.log_rpow (by positivity),
        Real.log_div (by positivity) hD.ne', Real.log_rpow hlpos,
        show 1 / α * (((d : ℝ) + α) * Real.log (lamMax S) - Real.log S.det) =
          (((d : ℝ) + α) * Real.log (lamMax S) - Real.log S.det) / α by ring,
        div_le_iff₀ hα0]
      constructor <;> intro h <;> nlinarith
    rw [← hiff]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hS, htpd, hMpd, h⟩⟩
  · simp only [zero_smul]
    refine ⟨fun h => ?_, fun h => absurd h (not_le.2 htA)⟩
    exfalso
    rcases h with h0 | ⟨c, hc, h0⟩ | ⟨-, h0, -⟩
    · exact PosDef_ne_zero' hS h0
    · rcases smul_eq_zero.1 h0.symm with h | h
      · linarith
      · exact PosDef_ne_zero' hS h
    · exact PosDef_ne_zero' h0 rfl

/-- **`t_α(Σ)/ε_α(Σ) = ecc(Σ)^{(d+α)/α}`** on `PD(d)`. -/
theorem tAlpha_div_epsAlpha [NeZero d] {α : ℝ} {S : Mat d} (hS : S.PosDef) :
    tAlpha α S / epsAlpha α S = ecc S ^ (((d : ℝ) + α) / α) := by
  have hD := hS.det_pos
  have hl := lamMin_pos hS
  have hlmax : 0 < lamMax S := by
    rw [lamMax_eq_inv_lamMin_inv hS]; exact inv_pos.2 (lamMin_pos hS.inv)
  unfold tAlpha epsAlpha ecc
  rw [← div_rpow (by positivity) (by positivity), div_div_div_cancel_right₀ hD.ne',
    ← div_rpow hlmax.le hl.le, ← rpow_mul (by positivity)]
  congr 1
  ring

/-! ### The node -/

/-- **`lem:stable-order-psd`** (`prop:similarity-stable-order-families`(1)): `≤_α` is a partial
order on `PSD(d)`, invariant under `GL(d)`, containing the rays and contained in the Loewner order,
with the path condition (P); `(G, ≤_α)` is a wedge datum for every closed subgroup `G` of `GL(d)`
containing the dilations; `≤_α` implies `≤_β` for `α ≤ β < 2`; and for `Σ ∈ PD(d)`,
`εI ≤_α Σ ⇔ ε ≤ ε_α(Σ)`, `Σ ≤_α tI ⇔ t ≥ t_α(Σ)` (`ε, t ≥ 0`), with
`t_α(Σ)/ε_α(Σ) = ecc(Σ)^{(d+α)/α}`. -/
theorem stablePlusLE_order (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    IsPartialOrderOn (psdSet d) (stablePlusLE α) ∧
      (∀ A ∈ glSet d, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → stablePlusLE α S S' →
        stablePlusLE α (act A S) (act A S')) ∧
      (∀ S : Mat d, S.PosSemidef → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' →
        stablePlusLE α (c • S) (c' • S)) ∧
      (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → stablePlusLE α S S' → loewnerLE S S') ∧
      HasPathCondition (stablePlusLE (d := d) α) ∧
      (∀ G : Set (Mat d), IsClosedSubgroupGL G → (∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G) →
        IsWedgeDatum G (stablePlusLE α)) ∧
      (∀ β : ℝ, α ≤ β → β < 2 → ∀ S S' : Mat d, stablePlusLE α S S' → stablePlusLE β S S') ∧
      (∀ S : Mat d, S.PosDef → ∀ ε : ℝ, 0 ≤ ε →
        (stablePlusLE α (ε • (1 : Mat d)) S ↔ ε ≤ epsAlpha α S)) ∧
      (∀ S : Mat d, S.PosDef → ∀ t : ℝ, 0 ≤ t →
        (stablePlusLE α S (t • (1 : Mat d)) ↔ tAlpha α S ≤ t)) ∧
      ∀ S : Mat d, S.PosDef → tAlpha α S / epsAlpha α S = ecc S ^ (((d : ℝ) + α) / α) := by
  haveI : NeZero d := ⟨by omega⟩
  have hrefl : ∀ S : Mat d, stablePlusLE α S S := fun S =>
    Or.inr (Or.inl ⟨1, le_rfl, (one_smul ℝ S).symm⟩)
  have hanti : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → stablePlusLE α S S' →
      stablePlusLE α S' S → S = S' := fun S S' hS hS' h h' =>
    le_antisymm ((loewnerLE_iff_le _ _).1 (stablePlusLE_loewner hα0 hα2 hS hS' h))
      ((loewnerLE_iff_le _ _).1 (stablePlusLE_loewner hα0 hα2 hS' hS h'))
  refine ⟨⟨fun S _ => hrefl S, fun S hS S' hS' h h' => hanti S S' hS hS' h h',
    fun S hS _ _ _ _ h h' => stablePlusLE_trans hα0 hα2 hS h h'⟩,
    fun A hA S S' _ _ h => stablePlusLE_act hα0 hα2 hA h,
    fun S _ c c' hc hcc' => stablePlusLE_rays α S hc hcc',
    fun S S' hS hS' h => stablePlusLE_loewner hα0 hα2 hS hS' h,
    stablePlusLE_hasPathCondition hα0 hα2,
    fun G hG hdil => ⟨hG, hdil, fun S _ => hrefl S, hanti,
      fun S _ _ hS _ _ h h' => stablePlusLE_trans hα0 hα2 hS h h',
      fun A hA S S' _ _ h => stablePlusLE_act hα0 hα2 (hG.subset_gl hA) h,
      fun S _ c c' hc hcc' => stablePlusLE_rays α S hc hcc'⟩,
    fun β hαβ hβ2 S S' h => ?_,
    fun S hS ε hε => stablePlusLE_smul_one_iff hα0 hα2 hS hε,
    fun S hS t ht => stablePlusLE_le_smul_one_iff hα0 hα2 hS ht,
    fun S hS => tAlpha_div_epsAlpha hS⟩
  rcases h with h | h | ⟨h1, h2, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h1, h2, h1, h2, h.2.2.1, ?_⟩)
    have hM := h.2.2.1
    have hl := one_le_lamMin_of_stable hα0 hM h.2.2.2
    exact h.2.2.2.trans (rpow_le_rpow_of_exponent_le hl (by linarith))

end AffineHemigroup
