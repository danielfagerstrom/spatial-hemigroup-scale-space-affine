/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableDensity
import AffineHemigroup.ShapeAdapted
import AffineHemigroup.Defs.Cones

/-!
# `lem:stable-step-order`: the stable step order

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:stable-step-order` (wave 1, group D, Q-0281),
the matrix analysis of `prop:stable-step-cone`: for `Σ, Σ' ∈ PD(d)` and `M = Σ^{-1/2}Σ'Σ^{-1/2}`,

* `stable_density_order_iff`: `n_Σ ≤ n_{Σ'}` off the origin iff `λ_min(M)^{d+α} ≥ det M`, and
  then `Σ ≤ Σ'`;
* `stableLE_partialOrder`: `≼_α` is a partial order on `PD(d)`, inside the Loewner order, and
  `GL(d)`-invariant;
* `stableLE_rays_not_rank_deficient`: the rays are steps, rank-deficient steps are not;
* `stableLE_scale_shape`, `stableLE_scale_shape_converse`, `stableLE_any_eigenframe`: the order
  in the coordinates of `lem:loewner-scale-shape`.

The route is the blueprint's: the substitution `x = Σ^{1/2}y` carries `n_Σ ≤ n_{Σ'}` to
`|y|^{-(d+α)} ≤ (det M)^{-1/2}⟨y, M⁻¹y⟩^{-(d+α)/2}`, and the largest value of `⟨y, M⁻¹y⟩/|y|²` is
`1/λ_min(M)`, attained at an eigenvector for `λ_min(M)`. Lean core only: no ledger entry is read.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ### Rayleigh quotients -/

/-- `λ_min(M)|x|² ≤ ⟨x, Mx⟩` for symmetric `M`. -/
theorem lamMin_mul_norm_sq_le [NeZero d] {M : Mat d} (hM : M.IsHermitian) (x : Rd d) :
    lamMin M * ‖x‖ ^ 2 ≤ ⟪x, lin M x⟫ := by
  rw [lamMin_eq_eigUp_zero hM]
  have h := quad_nonneg ((posSemidef_sub_smul_one_iff hM (eigUp M 0)).2 le_rfl) x
  rw [quad_sub, quad_smul, quad_one] at h
  unfold quad at h
  linarith

/-- `λ_min(M) ≤ ⟨u, Mu⟩` for a unit vector `u` and symmetric `M`. -/
theorem lamMin_le_inner [NeZero d] {M : Mat d} (hM : M.IsHermitian) {u : Rd d} (hu : ‖u‖ = 1) :
    lamMin M ≤ ⟪u, lin M u⟫ := by
  have hb : BddBelow (Set.range fun x : {x : Rd d // ‖x‖ = 1} => ⟪(x : Rd d), lin M x⟫) :=
    ⟨lamMin M, by
      rintro _ ⟨x, rfl⟩
      have := lamMin_mul_norm_sq_le hM (x : Rd d)
      rwa [x.2, one_pow, mul_one] at this⟩
  exact ciInf_le hb ⟨u, hu⟩

/-- `λ_min(M) > 0` on `PD(d)`. -/
theorem lamMin_pos [NeZero d] {M : Mat d} (hM : M.PosDef) : 0 < lamMin M := by
  rw [lamMin_eq_eigUp_zero hM.isHermitian]; exact eigUp_pos hM 0

/-- `λ_min(I) = 1`. -/
theorem lamMin_one [NeZero d] : lamMin (1 : Mat d) = 1 := by
  apply le_antisymm
  · have hu : ‖(EuclideanSpace.single 0 1 : Rd d)‖ = 1 := by simp
    have := lamMin_le_inner (isHermitian_one (n := Fin d) (α := ℝ)) hu
    have e : ⟪(EuclideanSpace.single 0 1 : Rd d), lin 1 (EuclideanSpace.single 0 1)⟫ = 1 := by
      rw [lin_one]
      exact (real_inner_self_eq_norm_sq _).trans (by rw [hu, one_pow])
    rwa [e] at this
  · rw [lamMin_eq_eigUp_zero isHermitian_one]
    exact (posSemidef_sub_smul_one_iff isHermitian_one (1 : ℝ)).1
      (by rw [one_smul, sub_self]; exact PosSemidef.zero)

/-- `M M⁻¹ = I` as linear maps, for invertible `M`. -/
theorem lin_mul_inv_apply {M : Mat d} (hM : IsUnit M.det) (y : Rd d) :
    lin M (lin M⁻¹ y) = y := by
  have : lin M (lin M⁻¹ y) = lin (M * M⁻¹) y := by rw [lin_mul]; rfl
  rw [this, mul_nonsing_inv _ hM, lin_one]; rfl

/-- `M⁻¹ M = I` as linear maps, for invertible `M`. -/
theorem lin_inv_mul_apply {M : Mat d} (hM : IsUnit M.det) (y : Rd d) :
    lin M⁻¹ (lin M y) = y := by
  have : lin M⁻¹ (lin M y) = lin (M⁻¹ * M) y := by rw [lin_mul]; rfl
  rw [this, nonsing_inv_mul _ hM, lin_one]; rfl

/-- **The inverse Rayleigh bound**: `λ_min(M) ⟨y, M⁻¹y⟩ ≤ |y|²` on `PD(d)`. -/
theorem lamMin_mul_quad_inv_le [NeZero d] {M : Mat d} (hM : M.PosDef) (y : Rd d) :
    lamMin M * quad M⁻¹ y ≤ ‖y‖ ^ 2 := by
  have hl := lamMin_pos hM
  set z := lin M⁻¹ y with hz
  have hyz : lin M z = y := lin_mul_inv_apply ((isUnit_iff_isUnit_det M).1 hM.isUnit) y
  have hq : quad M⁻¹ y = ⟪z, lin M z⟫ := by
    rw [quad, ← hz, hyz, real_inner_comm]
  have h1 : lamMin M * ‖z‖ ^ 2 ≤ quad M⁻¹ y := hq ▸ lamMin_mul_norm_sq_le hM.isHermitian z
  have h2 : quad M⁻¹ y ≤ ‖y‖ * ‖z‖ := by
    rw [quad, ← hz]; exact real_inner_le_norm _ _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  -- `λ‖z‖ ≤ ‖y‖`
  have h3 : lamMin M * ‖z‖ ≤ ‖y‖ := by
    rcases hz0.lt_or_eq with hzp | hzp
    · have : lamMin M * ‖z‖ * ‖z‖ ≤ ‖y‖ * ‖z‖ := by nlinarith
      exact le_of_mul_le_mul_right this hzp
    · rw [← hzp, mul_zero]; exact hy0
  nlinarith

/-- At a unit eigenvector `v` for `λ_min(M)`, `⟨v, M⁻¹v⟩ = 1/λ_min(M)`. -/
theorem exists_quad_inv_eq [NeZero d] {M : Mat d} (hM : M.PosDef) :
    ∃ v : Rd d, ‖v‖ = 1 ∧ quad M⁻¹ v = (lamMin M)⁻¹ := by
  obtain ⟨v, hv, hMv⟩ := exists_unit_eigvec_eigUp_zero hM.isHermitian
  rw [← lamMin_eq_eigUp_zero hM.isHermitian] at hMv
  have hl := lamMin_pos hM
  have hinv : lin M⁻¹ v = (lamMin M)⁻¹ • v := by
    have h := lin_inv_mul_apply ((isUnit_iff_isUnit_det M).1 hM.isUnit) v
    rw [hMv, map_smul] at h
    calc lin M⁻¹ v = (lamMin M)⁻¹ • (lamMin M • lin M⁻¹ v) := by
          rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
      _ = (lamMin M)⁻¹ • v := by rw [h]
  refine ⟨v, hv, ?_⟩
  rw [quad, hinv, inner_smul_right, real_inner_self_eq_norm_sq, hv]
  ring

/-! ### The core equivalence, in the coordinates of `M` -/

/-- **The stable condition in the coordinates of `M`**: for `M ∈ PD(d)` and `p > 0`,
`|y|^{-2p} ≤ (det M)^{-1/2}⟨y, M⁻¹y⟩^{-p}` for every `y ≠ 0` exactly when
`det M ≤ λ_min(M)^{2p}`. -/
theorem stable_core_iff [NeZero d] {M : Mat d} (hM : M.PosDef) {p : ℝ} (hp : 0 < p) :
    (∀ y : Rd d, y ≠ 0 → (‖y‖ ^ 2) ^ (-p) ≤ M.det ^ (-(1 : ℝ) / 2) * quad M⁻¹ y ^ (-p)) ↔
      M.det ≤ lamMin M ^ (2 * p) := by
  have hD := hM.det_pos
  have hl := lamMin_pos hM
  have hMinv : M⁻¹.PosDef := hM.inv
  -- the condition through square roots
  have hcond : M.det ≤ lamMin M ^ (2 * p) ↔ M.det ^ ((1 : ℝ) / 2) ≤ lamMin M ^ p := by
    rw [← rpow_le_rpow_iff hD.le (rpow_nonneg hl.le _) (by norm_num : (0 : ℝ) < 1 / 2),
      ← rpow_mul hl.le]
    ring_nf
  -- the pointwise inequality, rearranged
  have hpt : ∀ y : Rd d, y ≠ 0 → ((‖y‖ ^ 2) ^ (-p) ≤ M.det ^ (-(1 : ℝ) / 2) * quad M⁻¹ y ^ (-p) ↔
      M.det ^ ((1 : ℝ) / 2) * quad M⁻¹ y ^ p ≤ (‖y‖ ^ 2) ^ p) := by
    intro y hy
    have ha : 0 < ‖y‖ ^ 2 := by positivity
    have hq : 0 < quad M⁻¹ y := quad_pos hMinv hy
    rw [rpow_neg ha.le, rpow_neg hq.le, show -(1 : ℝ) / 2 = -(1 / 2) by ring, rpow_neg hD.le,
      ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
  rw [hcond]
  constructor
  · intro h
    obtain ⟨v, hv, hqv⟩ := exists_quad_inv_eq hM
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have := (hpt v hv0).1 (h v hv0)
    rw [hv, hqv, one_pow, one_rpow, inv_rpow hl.le, ← div_eq_mul_inv,
      div_le_one (rpow_pos_of_pos hl _)] at this
    exact this
  · intro h y hy
    rw [hpt y hy]
    have ha : 0 < ‖y‖ ^ 2 := by positivity
    have hq : 0 < quad M⁻¹ y := quad_pos hMinv hy
    have hqa : quad M⁻¹ y ≤ ‖y‖ ^ 2 / lamMin M := by
      rw [le_div_iff₀ hl, mul_comm]; exact lamMin_mul_quad_inv_le hM y
    calc M.det ^ ((1 : ℝ) / 2) * quad M⁻¹ y ^ p
        ≤ lamMin M ^ p * (‖y‖ ^ 2 / lamMin M) ^ p :=
          mul_le_mul h (rpow_le_rpow hq.le hqa hp.le) (by positivity) (by positivity)
      _ = (‖y‖ ^ 2) ^ p := by
          rw [div_rpow ha.le hl.le, mul_div_cancel₀ _ (rpow_pos_of_pos hl _).ne']

/-! ### The substitution `x = Σ^{1/2}y` -/

/-- `⟨Σ^{1/2}y, Σ⁻¹Σ^{1/2}y⟩ = |y|²` on `PD(d)`. -/
theorem quad_inv_lin_msqrt {S : Mat d} (hS : S.PosDef) (y : Rd d) :
    quad S⁻¹ (lin (msqrt S) y) = ‖y‖ ^ 2 := by
  have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  have hSi : S⁻¹ = (msqrt S)⁻¹ * (msqrt S)⁻¹ := by
    conv_lhs => rw [← msqrt_mul_self hS.posSemidef]
    rw [Matrix.mul_inv_rev]
  have hact : act (msqrt S) S⁻¹ = 1 := by
    rw [act, msqrt_transpose, hSi, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hU,
      Matrix.mul_one, mul_nonsing_inv _ hU]
  rw [← msqrt_transpose S, ← quad_act, hact, quad_one]

/-- `(Σ^{-1/2}Σ'Σ^{-1/2})⁻¹ = Σ^{1/2}Σ'⁻¹Σ^{1/2}`, so `⟨y, M⁻¹y⟩ = ⟨Σ^{1/2}y, Σ'⁻¹Σ^{1/2}y⟩`. -/
theorem quad_relStep_inv {S : Mat d} (hS : S.PosDef) (S' : Mat d) (y : Rd d) :
    quad (relStep S S')⁻¹ y = quad S'⁻¹ (lin (msqrt S) y) := by
  have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  have hinv : (relStep S S')⁻¹ = act (msqrt S) S'⁻¹ := by
    rw [relStep, Matrix.mul_inv_rev, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hU, act,
      msqrt_transpose, mul_assoc]
  rw [hinv, quad_act, msqrt_transpose]

/-- A statement about every `x ≠ 0` is one about every `y ≠ 0` through `x = Ay`, `A` invertible. -/
theorem forall_ne_zero_lin_iff {A : Mat d} (hA : IsUnit A.det) (P : Rd d → Prop) :
    (∀ x : Rd d, x ≠ 0 → P x) ↔ ∀ y : Rd d, y ≠ 0 → P (lin A y) := by
  constructor
  · intro h y hy
    refine h _ fun h0 => hy ?_
    rw [← lin_inv_mul_apply hA y, h0, map_zero]
  · intro h x hx
    have := h (lin A⁻¹ x) fun h0 => hx (by rw [← lin_mul_inv_apply hA x, h0, map_zero])
    rwa [lin_mul_inv_apply hA x] at this

/-- `λ_min(M)^d ≤ det M` on `PD(d)`. -/
theorem lamMin_pow_le_det [NeZero d] {M : Mat d} (hM : M.PosDef) : lamMin M ^ d ≤ M.det := by
  rw [lamMin_eq_eigUp_zero hM.isHermitian, ← prod_eigUp hM.isHermitian]
  calc eigUp M 0 ^ d = ∏ _k : Fin d, eigUp M 0 := by simp
    _ ≤ ∏ k, eigUp M k := Finset.prod_le_prod (fun _ _ => (eigUp_pos hM 0).le)
        (fun k _ => eigUp_monotone hM.isHermitian (Fin.zero_le k))

/-- **The stable condition gives `λ_min(M) ≥ 1`**: `det M ≤ λ_min(M)^{d+α}` with `α > 0`. -/
theorem one_le_lamMin_of_stable [NeZero d] {α : ℝ} (hα0 : 0 < α) {M : Mat d} (hM : M.PosDef)
    (h : M.det ≤ lamMin M ^ ((d : ℝ) + α)) : 1 ≤ lamMin M := by
  have hl := lamMin_pos hM
  by_contra hlt
  have hlt' : lamMin M < 1 := lt_of_not_ge hlt
  have h1 : lamMin M ^ ((d : ℝ) + α) < lamMin M ^ (d : ℝ) :=
    rpow_lt_rpow_of_exponent_gt hl hlt' (by linarith)
  have h2 := lamMin_pow_le_det hM
  rw [← rpow_natCast] at h2
  linarith

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(1), (b)⇔(c), and "then `Σ ≤ Σ'`"):
`n_Σ ≤ n_{Σ'}` off the origin if and only if `λ_min(M)^{d+α} ≥ det M`, and then `Σ ≤ Σ'`. -/
theorem stable_density_order_iff [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) :
    ((∀ x : Rd d, x ≠ 0 → stableDensity α S x ≤ stableDensity α S' x) ↔
        (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α)) ∧
      ((relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α) → loewnerLE S S') := by
  set M := relStep S S' with hMdef
  have hM : M.PosDef := (posDef_relStep_iff hS S').2 hS'
  have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
  have hdS := hS.det_pos
  have hDM : S'.det = M.det * S.det := by
    rw [hMdef, det_relStep hS, div_mul_cancel₀ _ hdS.ne']
  set p : ℝ := ((d : ℝ) + α) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; positivity
  refine ⟨?_, fun h => ?_⟩
  · rw [show (d : ℝ) + α = 2 * p by rw [hp]; ring, ← stable_core_iff hM hp0,
      forall_ne_zero_lin_iff (msqrt_mem_glSet hS)]
    refine forall₂_congr fun y _ => ?_
    have hK : 0 < (stableConst (d := d) α)⁻¹ * S.det ^ (-(1 : ℝ) / 2) := by positivity
    unfold stableDensity
    rw [quad_inv_lin_msqrt hS, ← quad_relStep_inv hS, ← hMdef, hDM,
      mul_rpow hM.det_pos.le hdS.le, show -((d : ℝ) + α) / 2 = -p by rw [hp]; ring]
    rw [show (stableConst (d := d) α)⁻¹ * (M.det ^ (-(1 : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2)) *
        quad M⁻¹ y ^ (-p) = ((stableConst (d := d) α)⁻¹ * S.det ^ (-(1 : ℝ) / 2)) *
          (M.det ^ (-(1 : ℝ) / 2) * quad M⁻¹ y ^ (-p)) by ring]
    exact mul_le_mul_iff_right₀ hK
  · have h1 := one_le_lamMin_of_stable hα0 hM h
    rw [loewnerLE, ← posSemidef_relStep_iff hS, relStep_sub, ← hMdef, relStep_self hS,
      ← one_smul ℝ (1 : Mat d), posSemidef_sub_smul_one_iff hM.isHermitian,
      ← lamMin_eq_eigUp_zero hM.isHermitian]
    exact h1

/-- On `PD(d)`, `Σ ≼_α Σ'` is the pointwise order of the densities, `n_Σ ≤ n_{Σ'}` off `0`. -/
theorem stableLE_iff_density [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) :
    stableLE α S S' ↔ ∀ x : Rd d, x ≠ 0 → stableDensity α S x ≤ stableDensity α S' x := by
  rw [(stable_density_order_iff hα0 hα2 hS hS').1]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hS, hS', (posDef_relStep_iff hS S').2 hS', h⟩⟩

/-- `AΣAᵀ ∈ PD(d)` exactly when `Σ ∈ PD(d)`, for `A ∈ GL(d)`. -/
theorem posDef_act_iff {A : Mat d} (hA : A ∈ glSet d) (S : Mat d) :
    (act A S).PosDef ↔ S.PosDef := by
  have h := Matrix.IsUnit.posDef_star_right_conjugate_iff ((isUnit_iff_isUnit_det A).2 hA)
    (x := S)
  rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- `I ≼_α`-reflexivity: the relative step of `Σ` to itself is `I`, which is a stable step. -/
theorem stableLE_refl [NeZero d] (α : ℝ) {S : Mat d} (hS : S.PosDef) : stableLE α S S := by
  refine ⟨hS, hS, ?_⟩
  rw [relStep_self hS]
  refine ⟨PosDef.one, ?_⟩
  rw [det_one, lamMin_one, one_rpow]

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(2)), the order: `≼_α` is a partial order
on `PD(d)`, contained in the Loewner order, and `Σ ≼_α Σ'` if and only if `AΣAᵀ ≼_α AΣ'Aᵀ`, for
every `A ∈ GL(d)`. -/
theorem stableLE_partialOrder [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    IsPartialOrderOn (pdSet d) (stableLE α) ∧
      (∀ S S' : Mat d, stableLE α S S' → loewnerLE S S') ∧
      ∀ A ∈ glSet d, ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (stableLE α S S' ↔ stableLE α (act A S) (act A S')) := by
  have hloew : ∀ S S' : Mat d, stableLE α S S' → loewnerLE S S' := fun S S' h =>
    (stable_density_order_iff hα0 hα2 h.1 h.2.1).2 h.2.2.2
  refine ⟨⟨fun S hS => stableLE_refl α hS, fun S _ S' _ h h' => ?_,
    fun S hS S' hS' S'' hS'' h h' => ?_⟩, hloew, fun A hA S S' hS hS' => ?_⟩
  · exact le_antisymm ((loewnerLE_iff_le _ _).1 (hloew _ _ h))
      ((loewnerLE_iff_le _ _).1 (hloew _ _ h'))
  · rw [stableLE_iff_density hα0 hα2 hS hS''] at *
    rw [stableLE_iff_density hα0 hα2 hS hS'] at h
    rw [stableLE_iff_density hα0 hα2 hS' hS''] at h'
    exact fun x hx => (h x hx).trans (h' x hx)
  · have hAS := (posDef_act_iff hA S).2 hS
    have hAS' := (posDef_act_iff hA S').2 hS'
    have hAinv : IsUnit A⁻¹.det := isUnit_nonsing_inv_det A hA
    have hdA : 0 < |A.det|⁻¹ := inv_pos.2 (abs_pos.2 hA.ne_zero)
    rw [stableLE_iff_density hα0 hα2 hS hS', stableLE_iff_density hα0 hα2 hAS hAS',
      forall_ne_zero_lin_iff hAinv]
    refine forall₂_congr fun y hy => ?_
    rw [stableDensity_act hα0 hα2 A hA hS y hy, stableDensity_act hα0 hα2 A hA hS' y hy]
    exact (mul_le_mul_iff_right₀ hdA).symm

/-! ### Which steps -/

/-- The relative step is additive in its second argument. -/
theorem relStep_add (A B B' : Mat d) : relStep A (B + B') = relStep A B + relStep A B' := by
  simp only [relStep, Matrix.mul_add, Matrix.add_mul]

/-- `det(cI) = c^d`. -/
theorem det_smul_one (c : ℝ) : (c • (1 : Mat d)).det = c ^ d := by
  rw [det_smul, det_one, Fintype.card_fin, mul_one]

/-- A rank-deficient `P ∈ PSD(d)` has a nonzero vector in its kernel, and `Σ + P` then has the
relative step `M = I + Σ^{-1/2}PΣ^{-1/2}` with `λ_min(M) ≤ 1`. -/
theorem lamMin_relStep_add_le_one [NeZero d] {S P : Mat d} (hS : S.PosDef) (hPs : P.PosSemidef)
    (hP : P.rank < d) :
    lamMin (relStep S (S + P)) ≤ 1 := by
  have hdet : P.det = 0 := by
    by_contra h
    have := rank_of_isUnit P ((isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 h))
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨v, hv0, hPv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  set A := msqrt S
  have hU : IsUnit A.det := msqrt_mem_glSet hS
  set y : Rd d := lin A (WithLp.toLp 2 v) with hy
  have hy0 : y ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (lin A⁻¹) h
    rw [hy, lin_inv_mul_apply hU, map_zero] at this
    simpa using congrArg WithLp.ofLp this
  have hPy : lin (relStep S P) y = 0 := by
    have h1 : lin P (WithLp.toLp 2 v) = 0 := by
      apply WithLp.ofLp_injective 2
      rw [ofLp_lin]
      simpa using hPv
    simp only [relStep, lin_mul]
    change lin A⁻¹ (lin P (lin A⁻¹ (lin A (WithLp.toLp 2 v)))) = 0
    rw [lin_inv_mul_apply hU, h1, map_zero]
  have hMy : lin (relStep S (S + P)) y = y := by
    rw [relStep_add, relStep_self hS, lin_add, lin_one, _root_.add_apply, hPy,
      add_zero]
    rfl
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set u := ‖y‖⁻¹ • y with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hMu : lin (relStep S (S + P)) u = u := by rw [hu, map_smul, hMy]
  have hM : (relStep S (S + P)).IsHermitian :=
    relStep_isHermitian S (hS.isHermitian.add hPs.isHermitian)
  have := lamMin_le_inner hM hu1
  rwa [hMu, real_inner_self_eq_norm_sq, hu1, one_pow] at this

/-- `det(I + N) > 1` for `N ∈ PSD(d)`, `N ≠ 0`. -/
theorem one_lt_det_one_add [NeZero d] {N : Mat d} (hN : N.PosSemidef) (hN0 : N ≠ 0) :
    1 < (1 + N).det := by
  have hH : (1 + N).IsHermitian := isHermitian_one.add hN.isHermitian
  have hge : ∀ k, 1 ≤ eigUp (1 + N) k := fun k => by
    have h0 : (1 : ℝ) ≤ eigUp (1 + N) 0 := (posSemidef_sub_smul_one_iff hH 1).1
      (by rw [one_smul, add_sub_cancel_left]; exact hN)
    exact h0.trans (eigUp_monotone hH (Fin.zero_le k))
  have hlast : 1 < eigUp (1 + N) (Fin.rev 0) := by
    by_contra h
    have hle : eigUp (1 + N) (Fin.rev 0) ≤ 1 := le_of_not_gt h
    have h1 := (posSemidef_smul_one_sub_iff hH 1).2 hle
    rw [one_smul, sub_add_cancel_left] at h1
    apply hN0
    exact le_antisymm (by rw [Matrix.le_iff, zero_sub]; exact h1)
      (by rw [Matrix.le_iff, sub_zero]; exact hN)
  rw [← prod_eigUp hH, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (Fin.rev 0))]
  have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase (Fin.rev (0 : Fin d)), eigUp (1 + N) k :=
    calc (1 : ℝ) = ∏ _k ∈ Finset.univ.erase (Fin.rev (0 : Fin d)), (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun k _ => hge k)
  nlinarith

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(3)), which steps: every ray
`Σ' = λ²Σ`, `λ ≥ 1`, satisfies `Σ ≼_α Σ'`, and no step `Σ' = Σ + P` with `P ∈ PSD(d)` and
`0 < rank P < d` does. -/
theorem stableLE_rays_not_rank_deficient [NeZero d] {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) :
    (∀ S : Mat d, S.PosDef → ∀ lam : ℝ, 1 ≤ lam → stableLE α S (lam ^ 2 • S)) ∧
      ∀ S P : Mat d, S.PosDef → P.PosSemidef → 0 < P.rank → P.rank < d →
        ¬ stableLE α S (S + P) := by
  refine ⟨fun S hS lam hlam => ?_, fun S P hS hP hr0 hrd h => ?_⟩
  · have hl2 : 1 ≤ lam ^ 2 := by nlinarith
    have hl2p : 0 < lam ^ 2 := by linarith
    refine ⟨hS, hS.smul hl2p, ?_⟩
    rw [relStep_smul, relStep_self hS]
    refine ⟨PosDef.one.smul hl2p, ?_⟩
    rw [det_smul_one, lamMin_smul hl2p.le, lamMin_one, mul_one, ← rpow_natCast]
    exact rpow_le_rpow_of_exponent_le hl2 (by linarith)
  · set N := relStep S P with hN
    have hNpsd : N.PosSemidef := (posSemidef_relStep_iff hS P).2 hP
    have hN0 : N ≠ 0 := by
      intro h0
      have : P = 0 := relStep_injective hS (by rw [← hN, h0]; simp [relStep])
      rw [this, rank_zero] at hr0
      exact lt_irrefl 0 hr0
    have hM : relStep S (S + P) = 1 + N := by rw [relStep_add, relStep_self hS]
    have hdet := one_lt_det_one_add hNpsd hN0
    have hlam := lamMin_relStep_add_le_one hS hP hrd
    have hlpos : 0 < lamMin (relStep S (S + P)) := by
      rw [hM]
      exact lamMin_pos (PosDef.one.add_posSemidef hNpsd)
    have hstep := h.2.2.2
    rw [hM] at hstep hlam hlpos
    have : lamMin (1 + N) ^ ((d : ℝ) + α) ≤ 1 :=
      rpow_le_one hlpos.le hlam (by positivity)
    linarith

/-! ### Scale and shape -/

/-- `(cA)^{1/2} = √c A^{1/2}` for `c ≥ 0` and `A ∈ PSD(d)`. -/
theorem msqrt_smul {c : ℝ} (hc : 0 ≤ c) {A : Mat d} (hA : A.PosSemidef) :
    msqrt (c • A) = Real.sqrt c • msqrt A := by
  refine CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg A))
  rw [smul_mul_smul, msqrt_mul_self hA, ← sq, Real.sq_sqrt hc]

/-- `(cA)^{-1/2} B (cA)^{-1/2} = c⁻¹ A^{-1/2} B A^{-1/2}` for `c > 0`, `A ∈ PD(d)`. -/
theorem relStep_smul_left {c : ℝ} (hc : 0 < c) {A : Mat d} (hA : A.PosDef) (B : Mat d) :
    relStep (c • A) B = c⁻¹ • relStep A B := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hinv : (Real.sqrt c • msqrt A)⁻¹ = (Real.sqrt c)⁻¹ • (msqrt A)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul, msqrt_mul_inv hA, mul_inv_cancel₀ hs.ne', one_smul]
  rw [relStep, msqrt_smul hc.le hA.posSemidef, hinv, relStep]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [← mul_inv, Real.mul_self_sqrt hc.le]

/-- **The relative step in scale–shape coordinates**: `Σ₁^{-1/2}Σ₂Σ₁^{-1/2} = (t₂/t₁)² N`. -/
theorem relStep_eq_scale_shape [NeZero d] {S₁ S₂ : Mat d} (h₁ : S₁.PosDef) (h₂ : S₂.PosDef) :
    relStep S₁ S₂ = (volScale S₂ / volScale S₁) ^ 2 • relStep (shapeOf S₁) (shapeOf S₂) := by
  have ht₁ := volScale_pos h₁
  conv_lhs => rw [← smul_shapeOf h₁, ← smul_shapeOf h₂]
  rw [relStep_smul_left (by positivity) (shapeOf_posDef h₁), relStep_smul, smul_smul]
  congr 1
  field_simp

/-- The stable condition in scale–shape coordinates: with `c = (t₂/t₁)²`, `q = d + α`,
`c^d ≤ (c n₁)^q` exactly when `(t₁/t₂)^{2α/q} ≤ n₁`. -/
theorem stable_scale_shape_iff {t₁ t₂ n₀ α : ℝ} (d : ℕ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hn₀ : 0 < n₀) (hα0 : 0 < α) :
    ((t₂ / t₁) ^ 2) ^ d ≤ ((t₂ / t₁) ^ 2 * n₀) ^ ((d : ℝ) + α) ↔
      (t₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) ≤ n₀ := by
  have hq : 0 < (d : ℝ) + α := by positivity
  have hc : 0 < (t₂ / t₁) ^ 2 := by positivity
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    ← Real.log_le_log_iff (by positivity) hn₀, Real.log_pow, Real.log_rpow (by positivity),
    Real.log_mul hc.ne' hn₀.ne', Real.log_rpow (by positivity), Real.log_pow]
  have hL : Real.log (t₂ / t₁) = -Real.log (t₁ / t₂) := by
    rw [← Real.log_inv, inv_div]
  rw [hL, div_mul_eq_mul_div, div_le_iff₀ hq]
  constructor <;> intro h <;> push_cast at h ⊢ <;> nlinarith

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(3)), scale–shape coordinates:
`Σ₁ ≼_α Σ₂` if and only if `n₁ ≥ (t₁/t₂)^{2α/(d+α)}`, and then the anisotropy gained,
`√(n_d/n₁)`, is at most `(t₂/t₁)^{dα/(d+α)}`. -/
theorem stableLE_scale_shape [NeZero d] {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) {S₁ S₂ : Mat d}
    (h₁ : S₁.PosDef) (h₂ : S₂.PosDef) :
    let n := eigUp (relStep (shapeOf S₁) (shapeOf S₂))
    let t₁ := volScale S₁
    let t₂ := volScale S₂
    (stableLE α S₁ S₂ ↔ (t₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) ≤ n 0) ∧
      (stableLE α S₁ S₂ →
        Real.sqrt (n (Fin.rev 0) / n 0) ≤ (t₂ / t₁) ^ ((d : ℝ) * α / ((d : ℝ) + α))) := by
  intro n t₁ t₂
  set N := relStep (shapeOf S₁) (shapeOf S₂) with hNdef
  have hN : N.PosDef := relShape_posDef h₁ h₂
  have hNdet : N.det = 1 := by
    rw [hNdef, det_relStep (shapeOf_posDef h₁), det_shapeOf h₁, det_shapeOf h₂, div_one]
  have ht₁ : 0 < t₁ := volScale_pos h₁
  have ht₂ : 0 < t₂ := volScale_pos h₂
  have hn0 : 0 < n 0 := eigUp_pos hN 0
  have hc : 0 < (t₂ / t₁) ^ 2 := by positivity
  have hM : relStep S₁ S₂ = (t₂ / t₁) ^ 2 • N := relStep_eq_scale_shape h₁ h₂
  have hiff : stableLE α S₁ S₂ ↔ (t₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) ≤ n 0 := by
    rw [← stable_scale_shape_iff d ht₁ ht₂ hn0 hα0]
    constructor
    · intro h
      have h' := h.2.2.2
      rwa [hM, det_smul, Fintype.card_fin, hNdet, mul_one, lamMin_smul hc.le,
        lamMin_eq_eigUp_zero hN.isHermitian] at h'
    · intro h
      refine ⟨h₁, h₂, (posDef_relStep_iff h₁ S₂).2 h₂, ?_⟩
      rwa [hM, det_smul, Fintype.card_fin, hNdet, mul_one, lamMin_smul hc.le,
        lamMin_eq_eigUp_zero hN.isHermitian]
  refine ⟨hiff, fun h => ?_⟩
  have hb := hiff.1 h
  set b := (t₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) with hbdef
  have hbpos : 0 < b := by positivity
  have hmono : Monotone n := eigUp_monotone hN.isHermitian
  have hprod : ∏ k, n k = 1 := (scale_shape_coords h₁ h₂).2
  have hlast := last_mul_pow_le_one hmono hprod hbpos hb
  set T := (t₂ / t₁) ^ ((d : ℝ) * α / ((d : ℝ) + α)) with hT
  have hTpos : 0 < T := by positivity
  -- `b^d T² = 1`
  have hbT : b ^ d * T ^ 2 = 1 := by
    rw [hbdef, hT, ← rpow_natCast, ← rpow_natCast, ← rpow_mul (by positivity),
      ← rpow_mul (by positivity)]
    have : (t₁ / t₂) ^ (2 * α / ((d : ℝ) + α) * (d : ℝ)) =
        (t₁ / t₂) ^ ((d : ℝ) * α / ((d : ℝ) + α) * ((2 : ℕ) : ℝ)) := by
      congr 1; push_cast; ring
    rw [this, ← mul_rpow (by positivity) (by positivity), div_mul_div_comm, mul_comm t₁ t₂,
      div_self (by positivity), one_rpow]
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hbd : b ^ d = b ^ (d - 1) * b := by
    rw [← pow_succ, Nat.sub_add_cancel hd1]
  have hratio : n (Fin.rev 0) / n 0 ≤ T ^ 2 := by
    rw [div_le_iff₀ hn0]
    have h1 : n (Fin.rev 0) ≤ b * T ^ 2 := by
      have hbd1 : 0 < b ^ (d - 1) := by positivity
      have : b ^ (d - 1) * (b * T ^ 2) = 1 := by rw [← mul_assoc, ← hbd, hbT]
      nlinarith
    calc n (Fin.rev 0) ≤ b * T ^ 2 := h1
      _ ≤ T ^ 2 * n 0 := by nlinarith
  calc Real.sqrt (n (Fin.rev 0) / n 0) ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hratio
    _ = T := Real.sqrt_sq hTpos.le

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(3)), the converse: for `t₂ ≥ t₁` and
`N ∈ PD(d)` with `det N = 1` and least eigenvalue at least `(t₁/t₂)^{2α/(d+α)}`,
`Σ₂ := t₂² S₁^{1/2} N S₁^{1/2}` satisfies `Σ₁ ≼_α Σ₂`. -/
theorem stableLE_scale_shape_converse [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {S₁ : Mat d} (h₁ : S₁.PosDef) (t₂ : ℝ) (ht : volScale S₁ ≤ t₂) (N : Mat d) (hN : N.PosDef)
    (hdet : N.det = 1) (hmin : (volScale S₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) ≤ eigUp N 0) :
    stableLE α S₁ (t₂ ^ 2 • (msqrt (shapeOf S₁) * N * msqrt (shapeOf S₁))) := by
  have ht₂ : 0 < t₂ := (volScale_pos h₁).trans_le ht
  obtain ⟨hS₂, hvol, -, hrel⟩ := speed_limit_converse_aux h₁ ht₂ hN hdet
  refine ((stableLE_scale_shape hα0 hα2 h₁ hS₂).1).2 ?_
  rw [hvol, hrel]
  exact hmin

/-- **`lem:stable-step-order`** (`prop:stable-step-cone`(3)), in particular: for `d ≥ 2` and
`t₂ > t₁` the relative shape of a step in the cone may be an `N ≠ I` in that range with any
eigenvectors: for every `Q ∈ O(d)` there is such an `N = Q diag(v) Qᵀ`, and the step
`Σ₂ := t₂² S₁^{1/2} N S₁^{1/2}` it builds has volume scale `t₂` and relative shape `N`.
The witness is `v = (a, a^{-1/(d-1)}, …, a^{-1/(d-1)})` with `a = (t₁/t₂)^{2α/(d+α)}`. -/
theorem stableLE_any_eigenframe [NeZero d] (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {S₁ : Mat d} (h₁ : S₁.PosDef) (t₂ : ℝ) (ht : volScale S₁ < t₂) (Q : Mat d)
    (hQ : Q ∈ orthSet d) :
    ∃ v : Fin d → ℝ, Q * diagonal v * Qᵀ ≠ 1 ∧ (Q * diagonal v * Qᵀ).PosDef ∧
      (Q * diagonal v * Qᵀ).det = 1 ∧
      (volScale S₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) ≤ eigUp (Q * diagonal v * Qᵀ) 0 ∧
      stableLE α S₁ (t₂ ^ 2 • (msqrt (shapeOf S₁) * (Q * diagonal v * Qᵀ) * msqrt (shapeOf S₁))) ∧
      volScale (t₂ ^ 2 • (msqrt (shapeOf S₁) * (Q * diagonal v * Qᵀ) * msqrt (shapeOf S₁))) = t₂ ∧
      relStep (shapeOf S₁)
          (shapeOf (t₂ ^ 2 • (msqrt (shapeOf S₁) * (Q * diagonal v * Qᵀ) * msqrt (shapeOf S₁)))) =
        Q * diagonal v * Qᵀ := by
  have ht₁ := volScale_pos h₁
  have ht₂ : 0 < t₂ := ht₁.trans ht
  set a := (volScale S₁ / t₂) ^ (2 * α / ((d : ℝ) + α)) with ha
  have hapos : 0 < a := by positivity
  have ha1 : a < 1 := rpow_lt_one (by positivity) ((div_lt_one ht₂).2 ht) (by positivity)
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := -(1 : ℝ) / ((d : ℝ) - 1) with he
  have hae : 1 < a ^ e := one_lt_rpow_of_pos_of_lt_one_of_neg hapos ha1
    (by rw [he]; exact div_neg_of_neg_of_pos (by norm_num) (by linarith))
  set v : Fin d → ℝ := fun i => if i = 0 then a else a ^ e with hv
  have hvpos : ∀ i, 0 < v i := fun i => by
    simp only [hv]; split_ifs
    · exact hapos
    · linarith
  have hva : ∀ i, a ≤ v i := fun i => by
    simp only [hv]; split_ifs
    · exact le_rfl
    · linarith
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  have hQQ' : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hQ
  have hQgl : Q ∈ glSet d := orthSet_subset_glSet hQ
  set N := Q * diagonal v * Qᵀ with hNdef
  have hNact : N = act Q (diagonal v) := rfl
  have hN : N.PosDef := by
    rw [hNact, posDef_act_iff hQgl, posDef_diagonal_iff]; exact hvpos
  have hprod : ∏ i, v i = 1 := by
    rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ 0)]
    have hrest : ∏ i ∈ Finset.univ.erase (0 : Fin d), v i = (a ^ e) ^ (d - 1) := by
      rw [Finset.prod_congr rfl (g := fun _ => a ^ e) (fun i hi => by
        simp only [hv, if_neg (Finset.ne_of_mem_erase hi)]), Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [hrest]
    simp only [hv, if_pos rfl]
    rw [← rpow_natCast, ← rpow_mul hapos.le, Nat.cast_sub (by omega), Nat.cast_one,
      show e * ((d : ℝ) - 1) = -1 by rw [he, div_mul_cancel₀ _ (by linarith)], rpow_neg_one,
      mul_inv_cancel₀ hapos.ne']
  have hdet : N.det = 1 := by
    rw [hNdef, det_mul, det_mul, det_diagonal, hprod, mul_one, ← det_mul, hQQ, det_one]
  have hmin : a ≤ eigUp N 0 := by
    rw [← posSemidef_sub_smul_one_iff hN.isHermitian]
    have : N - a • (1 : Mat d) = act Q (diagonal fun i => v i - a) := by
      rw [hNact, ← act_orth_one hQ, ← act_smul, act_sub]
      congr 1
      rw [smul_one_eq_diagonal, diagonal_sub]
    rw [this]
    exact posSemidef_act Q (posSemidef_diagonal_iff.2 fun i => sub_nonneg.2 (hva i))
  have hN1 : N ≠ 1 := by
    intro h1
    have hD : diagonal v = 1 := by
      have : Qᵀ * N * Q = diagonal v := by
        rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul,
          Matrix.mul_assoc, hQQ', Matrix.mul_one]
      rw [← this, h1, Matrix.mul_one, hQQ']
    have := congrFun (congrFun hD 0) 0
    simp only [diagonal_apply_eq, one_apply_eq, hv, if_true] at this
    linarith
  obtain ⟨-, hvol, -, hrel⟩ := speed_limit_converse_aux h₁ ht₂ hN hdet
  exact ⟨v, hN1, hN, hdet, hmin,
    stableLE_scale_shape_converse hα0 hα2 h₁ t₂ ht.le N hN hdet hmin, hvol, hrel⟩

end AffineHemigroup
