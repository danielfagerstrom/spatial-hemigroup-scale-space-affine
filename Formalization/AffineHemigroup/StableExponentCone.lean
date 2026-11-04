/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.EllipticalStable
import AffineHemigroup.PathCondition
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# `prop:stable-exponent-cone`: the exponent cone of the isotropic stable law

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:stable-exponent-cone` (wave 2, group C,
Q-0281). Spends A3(iii) through `prop:stable-step-cone`, in both directions.

## The route

The blueprint's, with one fact Mathlib lacks written out first: **`det e^{tA} = e^{t tr A}`**
(`det_mexp_smul`; a TODO of Mathlib's `MatrixExponential`). The derivative of
`φ(t) = det e^{tA}` at `0` is `tr A`, by the Leibniz formula and the product rule, since every
permutation other than the identity moves two points; `φ(s + t) = φ(s)φ(t)` makes
`φ' = (tr A)φ`, and `φ(t)e^{-t tr A}` has derivative `0`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

section OperatorNorm

open scoped Norms.Operator

/-- `t ↦ e^{tA}` has derivative `e^{tA}A`. -/
theorem hasDerivAt_mexp_smul (A : Mat d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => mexp (u • A)) (mexp (t • A) * A) t :=
  hasDerivAt_exp_smul_const A t

/-- `t ↦ e^{tA}` has derivative `Ae^{tA}`. -/
theorem hasDerivAt_mexp_smul' (A : Mat d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => mexp (u • A)) (A * mexp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t

/-- The entries of `t ↦ e^{tA}` have derivative `(e^{tA}A)ᵢⱼ`. -/
theorem hasDerivAt_mexp_smul_apply (A : Mat d) (t : ℝ) (i j : Fin d) :
    HasDerivAt (fun u : ℝ => mexp (u • A) i j) ((mexp (t • A) * A) i j) t := by
  let L : Mat d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.proj j).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin d → ℝ) i))
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_mexp_smul A t)

/-- `t ↦ e^{tA}v` has derivative `Ae^{tA}v` (coordinates). -/
theorem hasDerivAt_mexp_smul_mulVec (A : Mat d) (v : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => mexp (u • A) *ᵥ v) (A *ᵥ (mexp (t • A) *ᵥ v)) t := by
  let Lin : Mat d →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  let L : Mat d →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap Lin
  have h := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_mexp_smul' A t)
  have hval : L (A * mexp (t • A)) = A *ᵥ (mexp (t • A) *ᵥ v) := by
    change (A * mexp (t • A)) *ᵥ v = _
    rw [Matrix.mulVec_mulVec]
  exact (h.congr_deriv hval : _)

/-- `e^{(s+t)A} = e^{sA}e^{tA}`. -/
theorem mexp_add_smul (A : Mat d) (s t : ℝ) : mexp ((s + t) • A) = mexp (s • A) * mexp (t • A) := by
  unfold mexp
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t)

end OperatorNorm

theorem mexp_zero : mexp (0 : Mat d) = 1 := by
  unfold mexp; exact NormedSpace.exp_zero

/-! ## `det e^{tA} = e^{t tr A}` -/

/-- For a permutation `σ ≠ 1` and a point `i`, some `j ≠ i` is moved by `σ`. -/
theorem exists_moved_ne {σ : Equiv.Perm (Fin d)} (hσ : σ ≠ 1) (i : Fin d) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  by_cases hji : j = i
  · subst hji
    refine ⟨σ j, hj, fun h => hj (σ.injective h)⟩
  · exact ⟨j, hji, hj⟩

/-- `∏_{j ≠ i} I_{σ j, j}` is `1` for `σ = 1` and `0` otherwise. -/
theorem prod_erase_one_perm (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    ∏ j ∈ Finset.univ.erase i, (1 : Mat d) (σ j) j = if σ = 1 then 1 else 0 := by
  split_ifs with hσ
  · rw [hσ]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Equiv.Perm.one_apply, Matrix.one_apply_eq]
  · obtain ⟨j, hji, hj⟩ := exists_moved_ne hσ i
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
      (by rw [one_apply_ne hj])

/-- **The derivative of `det e^{tA}` at `0` is `tr A`.** -/
theorem hasDerivAt_det_mexp_zero (A : Mat d) :
    HasDerivAt (fun t : ℝ => (mexp (t • A)).det) A.trace 0 := by
  have hfun : (fun t : ℝ => (mexp (t • A)).det) =
      fun t => ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℝ) *
        ∏ i, mexp (t • A) (σ i) i := by
    funext t; rw [det_apply']
  rw [hfun]
  have h0 : mexp ((0 : ℝ) • A) = 1 := by rw [zero_smul, mexp_zero]
  have hprod : ∀ σ : Equiv.Perm (Fin d), HasDerivAt (fun t : ℝ => ∏ i, mexp (t • A) (σ i) i)
      (∑ i, (∏ j ∈ Finset.univ.erase i, mexp ((0 : ℝ) • A) (σ j) j) •
        (mexp ((0 : ℝ) • A) * A) (σ i) i) 0 := fun σ =>
    HasDerivAt.fun_finsetProd fun i _ => hasDerivAt_mexp_smul_apply A 0 (σ i) i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => (hprod σ).const_mul
    (Equiv.Perm.sign σ : ℝ)
  refine hsum.congr_deriv ?_
  simp only [h0, prod_erase_one_perm, smul_eq_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin d))]
  · simp [trace]
  · intro σ _ hσ
    simp [hσ]
  · simp

/-- **`det e^{tA} = e^{t tr A}`** (a TODO of Mathlib's `MatrixExponential`). -/
theorem det_mexp_smul (A : Mat d) (t : ℝ) : (mexp (t • A)).det = Real.exp (t * A.trace) := by
  set φ : ℝ → ℝ := fun t => (mexp (t • A)).det with hφ
  have hmul : ∀ s u : ℝ, φ (s + u) = φ s * φ u := fun s u => by
    simp only [hφ, mexp_add_smul, det_mul]
  have h0 := hasDerivAt_det_mexp_zero A
  have hder : ∀ s : ℝ, HasDerivAt φ (φ s * A.trace) s := by
    intro s
    have hc : HasDerivAt (fun u : ℝ => φ (u - s)) A.trace s := by
      have h0' : HasDerivAt φ A.trace (s - s) := by rw [sub_self]; exact h0
      exact h0'.comp_sub_const s s
    have h2 := hc.const_mul (φ s)
    have heq : (fun u => φ s * φ (u - s)) = φ := by
      funext u
      rw [← hmul, add_sub_cancel]
    rwa [heq] at h2
  set g : ℝ → ℝ := fun u => φ u * Real.exp (-(u * A.trace)) with hg
  have hgd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have hexp : HasDerivAt (fun u => Real.exp (-(u * A.trace)))
        (Real.exp (-(u * A.trace)) * (-A.trace)) u := by
      have := (((hasDerivAt_id u).mul_const A.trace).neg).exp
      simpa using this
    exact ((hder u).mul hexp).congr_deriv (by ring)
  have hmono : Monotone g := monotone_of_hasDerivAt_nonneg hgd (fun _ => le_rfl)
  have hanti : Monotone (fun u => -g u) :=
    monotone_of_hasDerivAt_nonneg (fun u => (hgd u).neg) (fun _ => by simp)
  have hg0 : g t = g 0 := by
    rcases le_total 0 t with h | h
    · exact le_antisymm (by have := hanti h; simp only [neg_le_neg_iff] at this; exact this)
        (hmono h)
    · exact le_antisymm (hmono h) (by have := hanti h; simp only [neg_le_neg_iff] at this; exact this)
  have hg00 : g 0 = 1 := by
    simp [hg, hφ, mexp_zero]
  have h1 : φ t * Real.exp (-(t * A.trace)) = 1 := hg0.trans hg00
  calc (mexp (t • A)).det = φ t := rfl
    _ = φ t * Real.exp (-(t * A.trace)) * Real.exp (t * A.trace) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = Real.exp (t * A.trace) := by rw [h1, one_mul]

/-! ## The growth of `|e^{tB}x|` -/

theorem symPart_isHermitian (B : Mat d) : (symPart B).IsHermitian := by
  change (symPart B)ᴴ = symPart B
  rw [conjTranspose_eq_transpose_of_trivial, symPart, transpose_smul, transpose_add,
    transpose_transpose, add_comm]

/-- `⟨y, (sym B) y⟩ = ⟨y, By⟩`. -/
theorem quad_symPart (B : Mat d) (y : Rd d) : quad (symPart B) y = quad B y := by
  have hT : quad Bᵀ y = quad B y := by
    unfold quad
    rw [← inner_lin_left, real_inner_comm]
  rw [symPart, quad_smul, quad_add, hT]
  ring

theorem norm_sq_eq_sum (y : Rd d) : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- `t ↦ |e^{tB}x|²` has derivative `2⟨y, By⟩`, `y = e^{tB}x`. -/
theorem hasDerivAt_norm_sq_mexp (B : Mat d) (x : Rd d) (u : ℝ) :
    HasDerivAt (fun u : ℝ => ‖lin (mexp (u • B)) x‖ ^ 2)
      (2 * quad B (lin (mexp (u • B)) x)) u := by
  set v : ℝ → Fin d → ℝ := fun u => mexp (u • B) *ᵥ x.ofLp with hv
  have hfun : (fun u : ℝ => ‖lin (mexp (u • B)) x‖ ^ 2) = fun u => ∑ i, (v u i) ^ 2 := by
    funext u
    rw [norm_sq_eq_sum]
    rfl
  have hvd := hasDerivAt_mexp_smul_mulVec B x.ofLp u
  have hcomp : ∀ i, HasDerivAt (fun u => v u i) ((B *ᵥ v u) i) u := fun i =>
    hasDerivAt_pi.1 hvd i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hcomp i).pow 2
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [quad_eq_dotProduct]
  simp only [dotProduct, Finset.mul_sum, ofLp_lin]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hv]
  norm_num
  ring

/-- **`|e^{tB}x|² ≥ e^{2λt}|x|²`** for `t ≥ 0`, `λ = λ_min(sym B)`. -/
theorem exp_mul_le_norm_sq_mexp [NeZero d] (B : Mat d) (x : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (2 * lamMin (symPart B) * t) * ‖x‖ ^ 2 ≤ ‖lin (mexp (t • B)) x‖ ^ 2 := by
  set l := lamMin (symPart B) with hl
  set f : ℝ → ℝ := fun u => ‖lin (mexp (u • B)) x‖ ^ 2 with hf
  set g : ℝ → ℝ := fun u => Real.exp (-(2 * l * u)) * f u with hg
  have hexp : ∀ u, HasDerivAt (fun u => Real.exp (-(2 * l * u)))
      (Real.exp (-(2 * l * u)) * (-(2 * l))) u := fun u => by
    have := (((hasDerivAt_id u).const_mul (2 * l)).neg).exp
    simpa using this
  have hgd : ∀ u, HasDerivAt g (Real.exp (-(2 * l * u)) * (-(2 * l)) * f u +
      Real.exp (-(2 * l * u)) * (2 * quad B (lin (mexp (u • B)) x))) u := fun u =>
    (hexp u).mul (hasDerivAt_norm_sq_mexp B x u)
  have hnn : ∀ u, 0 ≤ Real.exp (-(2 * l * u)) * (-(2 * l)) * f u +
      Real.exp (-(2 * l * u)) * (2 * quad B (lin (mexp (u • B)) x)) := by
    intro u
    have hq : l * f u ≤ quad B (lin (mexp (u • B)) x) := by
      rw [← quad_symPart]
      exact lamMin_mul_norm_sq_le (symPart_isHermitian B) _
    have he := Real.exp_pos (-(2 * l * u))
    nlinarith
  have hmono := monotone_of_hasDerivAt_nonneg hgd hnn
  have h0 : g 0 = ‖x‖ ^ 2 := by
    simp [hg, hf, mexp_zero, lin_one]
  have h1 := hmono ht
  rw [h0] at h1
  have hpos := Real.exp_pos (2 * l * t)
  calc Real.exp (2 * l * t) * ‖x‖ ^ 2 ≤ Real.exp (2 * l * t) * g t :=
        mul_le_mul_of_nonneg_left h1 hpos.le
    _ = f t := by
        rw [hg]; simp only
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-! ## `prop:stable-exponent-cone` -/

/-- `c ≤ λ_min(M)` iff `c ≤ ⟨x, Mx⟩` on the unit sphere (`M` symmetric, `d ≥ 1`). -/
theorem le_lamMin_iff [NeZero d] {M : Mat d} (hM : M.IsHermitian) (c : ℝ) :
    c ≤ lamMin M ↔ ∀ x : Rd d, ‖x‖ = 1 → c ≤ quad M x := by
  constructor
  · intro h x hx
    exact h.trans (lamMin_le_inner hM hx)
  · intro h
    haveI : Nonempty {x : Rd d // ‖x‖ = 1} := by
      obtain ⟨v, hv, -⟩ := exists_unit_eigvec_eigUp_zero hM
      exact ⟨⟨v, hv⟩⟩
    exact le_ciInf fun x => h x x.2

theorem lamMin_zero_mat [NeZero d] : lamMin (0 : Mat d) = 0 := by
  have h := lamMin_smul (le_refl (0 : ℝ)) (1 : Mat d)
  rwa [zero_smul, zero_mul] at h

theorem trace_symPart (B : Mat d) : (symPart B).trace = B.trace := by
  rw [symPart, trace_smul, trace_add, trace_transpose, smul_eq_mul]
  ring

/-- **`prop:stable-exponent-cone`**: for `0 < α < 2`, `S_α(I)` is `B`-self-decomposable if and only
if `(d+α) λ_min(sym B) ≥ tr B`. -/
theorem stable_exponent_cone [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (B : Mat d)
    (μ : Measure (Rd d)) (hμ : IsEllipticalStable α 1 μ) :
    IsBSelfDecomposable B μ ↔ B ∈ stableExpCone d α := by
  have hdα : 0 < (d : ℝ) + α := by positivity
  set l := lamMin (symPart B) with hl
  -- the orbit of `μ`
  set μf : Mat d → Measure (Rd d) := fun S => affineOrbit μ S with hμf
  have hμf : ∀ S : Mat d, S.PosDef → IsEllipticalStable α S (μf S) := fun S hS =>
    (ellipticalStable_orbit hα0 hα2 μ hμ).2.2.2.2 S hS
  -- the matrices of the curve
  have hEF : ∀ t : ℝ, mexp ((-t) • B) * mexp (t • B) = 1 := fun t => by
    rw [← mexp_add_smul, neg_add_cancel, zero_smul, mexp_zero]
  have hEgl : ∀ t : ℝ, mexp ((-t) • B) ∈ glSet d := fun t => by
    change IsUnit (mexp ((-t) • B)).det
    rw [det_mexp_smul]; exact isUnit_iff_ne_zero.2 (Real.exp_pos _).ne'
  -- `Σ_t := E_t E_tᵀ` with `E_t = e^{-tB}`, `Σ_t⁻¹ = F_tᵀF_t` with `F_t = e^{tB}`
  have hSig : ∀ t : ℝ, (act (mexp ((-t) • B)) 1).PosDef := fun t =>
    (posDef_act_iff (hEgl t) 1).2 PosDef.one
  have hSiginv : ∀ t : ℝ, (act (mexp ((-t) • B)) 1)⁻¹ = (mexp (t • B))ᵀ * mexp (t • B) := by
    intro t
    have hinv : (mexp ((-t) • B))⁻¹ = mexp (t • B) := Matrix.inv_eq_right_inv (hEF t)
    rw [act, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hinv]
  have hM : ∀ t : ℝ, relStep (act (mexp ((-t) • B)) 1) 1 = (mexp (t • B))ᵀ * mexp (t • B) :=
    fun t => by rw [relStep_one_right (hSig t), hSiginv]
  have hquadM : ∀ (t : ℝ) (x : Rd d),
      quad ((mexp (t • B))ᵀ * mexp (t • B)) x = ‖lin (mexp (t • B)) x‖ ^ 2 := by
    intro t x
    have : (mexp (t • B))ᵀ * mexp (t • B) = act (mexp (t • B))ᵀ 1 := by
      rw [act, Matrix.mul_one, transpose_transpose]
    rw [this, quad_act, quad_one, transpose_transpose]
  have hdetM : ∀ t : ℝ, ((mexp (t • B))ᵀ * mexp (t • B)).det = Real.exp (2 * t * B.trace) := by
    intro t
    rw [det_mul, det_transpose, det_mexp_smul, ← Real.exp_add]; ring_nf
  have hpush : ∀ t : ℝ, μf (act (mexp ((-t) • B)) 1) = push (mexp ((-t) • B)) μ := fun t =>
    (hμf _ (hSig t)).eq (hμ.push (hEgl t))
  have hμ1 : μf 1 = μ := (hμf 1 PosDef.one).eq hμ
  rw [isBSelfDecomposable_iff]
  constructor
  · -- necessity, through an eigenvector of `sym B`
    intro hSD
    obtain ⟨x, hx1, hxv⟩ := exists_unit_eigvec_eigUp_zero (symPart_isHermitian B)
    rw [← lamMin_eq_eigUp_zero (symPart_isHermitian B), ← hl] at hxv
    set c := B.trace / ((d : ℝ) + α) with hc
    -- `e^{2ct} ≤ |e^{tB}x|²` for `t > 0`
    have hbound : ∀ t : ℝ, 0 < t → Real.exp (2 * c * t) ≤ ‖lin (mexp (t • B)) x‖ ^ 2 := by
      intro t ht
      obtain ⟨ρ, hρ, hdec⟩ := hSD t ht
      have ha : ∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧
          μf 1 = μf (act (mexp ((-t) • B)) 1) ∗ ρ := by
        refine ⟨ρ, inferInstance, ?_⟩
        rw [hμ1, hpush]
        exact hdec
      have hcond := ((stable_step_cone_tfae hα0 hα2 μf hμf (hSig t) PosDef.one).out 0 2).1 ha
      rw [hM, hdetM] at hcond
      have hle : lamMin ((mexp (t • B))ᵀ * mexp (t • B)) ≤ ‖lin (mexp (t • B)) x‖ ^ 2 := by
        have hH : ((mexp (t • B))ᵀ * mexp (t • B)).IsHermitian := by
          rw [← hSiginv]; exact (hSig t).inv.isHermitian
        have := lamMin_le_inner hH hx1
        rwa [← quad, hquadM] at this
      have hlpos : 0 < lamMin ((mexp (t • B))ᵀ * mexp (t • B)) := by
        have hP : ((mexp (t • B))ᵀ * mexp (t • B)).PosDef := by
          rw [← hSiginv]; exact (hSig t).inv
        exact lamMin_pos hP
      have h2 : Real.exp (2 * t * B.trace) ≤
          (‖lin (mexp (t • B)) x‖ ^ 2) ^ ((d : ℝ) + α) :=
        hcond.trans (Real.rpow_le_rpow hlpos.le hle hdα.le)
      have h3 := Real.rpow_le_rpow (Real.exp_pos _).le h2 (inv_pos.2 hdα).le
      rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hdα.ne', Real.rpow_one,
        ← Real.exp_mul] at h3
      calc Real.exp (2 * c * t) = Real.exp (2 * t * B.trace * ((d : ℝ) + α)⁻¹) := by
            rw [hc]; ring_nf
        _ ≤ _ := h3
    -- the derivative at `0`
    set h : ℝ → ℝ := fun t => ‖lin (mexp (t • B)) x‖ ^ 2 - Real.exp (2 * c * t) with hh
    have hd0 : HasDerivAt h (2 * l - 2 * c) 0 := by
      have h1 := hasDerivAt_norm_sq_mexp B x 0
      rw [zero_smul, mexp_zero, lin_one, one_apply_eq_self, ← quad_symPart] at h1
      have hq : quad (symPart B) x = l := by
        rw [quad, hxv, inner_smul_right, real_inner_self_eq_norm_sq, hx1]; ring
      rw [hq] at h1
      have h2 : HasDerivAt (fun t => Real.exp (2 * c * t)) (2 * c) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * c)).exp
        simpa using this
      exact (h1.sub h2).congr_deriv (by ring)
    have hslope := hd0.tendsto_slope_zero_right
    have hge : 0 ≤ 2 * l - 2 * c := by
      refine ge_of_tendsto hslope ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h00 : h 0 = 0 := by simp [hh, mexp_zero, lin_one, hx1]
      simp only [zero_add, h00, sub_zero, smul_eq_mul]
      exact mul_nonneg (inv_pos.2 ht).le (by simp only [hh]; linarith [hbound t ht])
    show B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B)
    have : c ≤ l := by linarith
    rw [hc, div_le_iff₀ hdα] at this
    linarith
  · -- sufficiency
    intro hB t ht
    have hB' : B.trace ≤ ((d : ℝ) + α) * l := hB
    have hlow : Real.exp (2 * l * t) ≤ lamMin ((mexp (t • B))ᵀ * mexp (t • B)) := by
      have hH : ((mexp (t • B))ᵀ * mexp (t • B)).IsHermitian := by
        rw [← hSiginv]; exact (hSig t).inv.isHermitian
      refine (le_lamMin_iff hH _).2 fun x hx => ?_
      have := exp_mul_le_norm_sq_mexp B x ht.le
      rwa [hx, one_pow, mul_one, ← hquadM] at this
    have hcond : (relStep (act (mexp ((-t) • B)) 1) 1).det ≤
        lamMin (relStep (act (mexp ((-t) • B)) 1) 1) ^ ((d : ℝ) + α) := by
      rw [hM, hdetM]
      calc Real.exp (2 * t * B.trace) ≤ Real.exp (2 * l * t * ((d : ℝ) + α)) := by
            refine Real.exp_le_exp.2 ?_
            nlinarith
        _ = Real.exp (2 * l * t) ^ ((d : ℝ) + α) := Real.exp_mul _ _
        _ ≤ _ := Real.rpow_le_rpow (Real.exp_pos _).le hlow hdα.le
    obtain ⟨ρ, hρ, hdec⟩ :=
      ((stable_step_cone_tfae hα0 hα2 μf hμf (hSig t) PosDef.one).out 2 0).1 hcond
    have hprob := ((stable_step_cone_increment hα0 hα2 μf hμf (hSig t) PosDef.one hcond).2 ρ hρ
      hdec).1
    refine ⟨ρ, hprob, ?_⟩
    rw [hμ1, hpush] at hdec
    exact hdec

theorem symPart_add (B C : Mat d) : symPart (B + C) = symPart B + symPart C := by
  simp only [symPart, transpose_add, ← smul_add]; congr 1; abel

theorem symPart_smul (c : ℝ) (B : Mat d) : symPart (c • B) = c • symPart B := by
  simp only [symPart, transpose_smul, ← smul_add, smul_comm c]

theorem symPart_zero : symPart (0 : Mat d) = 0 := by simp [symPart]

theorem symPart_one : symPart (1 : Mat d) = 1 := by
  rw [symPart, transpose_one, ← two_smul ℝ (1 : Mat d), smul_smul]; norm_num

/-- Membership in `𝔨_α` is a family of linear inequalities, one for each unit vector. -/
theorem mem_stableExpCone_iff [NeZero d] {α : ℝ} (hα : 0 < (d : ℝ) + α) (B : Mat d) :
    B ∈ stableExpCone d α ↔
      ∀ x : Rd d, ‖x‖ = 1 → B.trace ≤ ((d : ℝ) + α) * quad (symPart B) x := by
  change B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B) ↔ _
  rw [← div_le_iff₀' hα, le_lamMin_iff (symPart_isHermitian B)]
  exact forall₂_congr fun x _ => div_le_iff₀' hα

theorem continuous_quad_symPart (x : Rd d) : Continuous fun B : Mat d => quad (symPart B) x := by
  simp only [quad_eq_dotProduct, symPart]
  exact continuous_const.dotProduct
    ((continuous_const.smul (continuous_id.add continuous_id.matrix_transpose)).matrix_mulVec
      continuous_const)

/-- **`prop:stable-exponent-cone`**, the cone: `𝔨_α` is a closed convex cone invariant under
`B ↦ QBQᵀ`, `Q ∈ O(d)`; it contains every skew-symmetric matrix and `I`; and every `B ∈ 𝔨_α` has
`sym B ≥ 0`, with `λ_min(sym B) > 0` unless `B` is skew-symmetric. -/
theorem stableExpCone_props [NeZero d] {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) :
    IsClosedConvexCone (stableExpCone d α) ∧ IsOrthInvariant (stableExpCone d α) ∧
      (∀ B : Mat d, Bᵀ = -B → B ∈ stableExpCone d α) ∧ (1 : Mat d) ∈ stableExpCone d α ∧
      ∀ B ∈ stableExpCone d α, (symPart B).PosSemidef ∧ (0 < lamMin (symPart B) ∨ Bᵀ = -B) := by
  have hdα : 0 < (d : ℝ) + α := by positivity
  have hiInter : stableExpCone d α = ⋂ x : {x : Rd d // ‖x‖ = 1},
      {B : Mat d | B.trace ≤ ((d : ℝ) + α) * quad (symPart B) x} := by
    ext B
    rw [mem_stableExpCone_iff hdα, mem_iInter]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
  have hskew : ∀ B : Mat d, Bᵀ = -B → symPart B = 0 ∧ B.trace = 0 := by
    intro B hB
    refine ⟨by rw [symPart, hB, add_neg_cancel, smul_zero], ?_⟩
    have h := trace_transpose B
    rw [hB, trace_neg] at h
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hiInter]
    refine isClosed_iInter fun x => ?_
    have h1 : Continuous fun B : Mat d => B.trace := continuous_id.matrix_trace
    have h2 : Continuous fun B : Mat d => ((d : ℝ) + α) * quad (symPart B) x.1 :=
      continuous_const.mul (continuous_quad_symPart x.1)
    exact isClosed_le h1 h2
  · rw [hiInter]
    refine convex_iInter fun x => ?_
    intro B hB C hC a b ha hb hab
    simp only [mem_setOf_eq] at hB hC ⊢
    rw [trace_add, trace_smul, trace_smul, symPart_add, symPart_smul, symPart_smul, quad_add,
      quad_smul, quad_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  · change (0 : Mat d).trace ≤ ((d : ℝ) + α) * lamMin (symPart 0)
    rw [symPart_zero, lamMin_zero_mat, trace_zero, mul_zero]
  · intro c hc B hB
    change (c • B).trace ≤ ((d : ℝ) + α) * lamMin (symPart (c • B))
    have hB' : B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B) := hB
    rw [trace_smul, symPart_smul, lamMin_smul hc, smul_eq_mul]
    nlinarith
  · intro Q hQ B hB
    have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    have hB' : B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B) := hB
    change (Q * B * Qᵀ).trace ≤ ((d : ℝ) + α) * lamMin (symPart (Q * B * Qᵀ))
    have htr : (Q * B * Qᵀ).trace = B.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.1 hQQ, Matrix.one_mul]
    have hsym : symPart (Q * B * Qᵀ) = Q * symPart B * Qᵀ := by
      simp only [symPart, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    obtain ⟨U, w, hUU, hBU⟩ := exists_udiag (symPart_isHermitian B)
    rw [htr, hsym, hBU, orth_mul_udiag, lamMin_udiag_eq (orth_mul_orth hQQ hUU) hUU, ← hBU]
    exact hB'
  · intro B hB
    obtain ⟨h1, h2⟩ := hskew B hB
    change B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B)
    rw [h1, h2, lamMin_zero_mat, mul_zero]
  · change (1 : Mat d).trace ≤ ((d : ℝ) + α) * lamMin (symPart 1)
    rw [symPart_one, lamMin_one, trace_one, Fintype.card_fin, mul_one]
    linarith
  · intro B hB
    have hB' : B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B) := hB
    obtain ⟨U, w, hUU, hBU⟩ := exists_udiag (symPart_isHermitian B)
    set l := lamMin (symPart B) with hl
    have hwl : ∀ i, l ≤ w i := fun i => by rw [hl, hBU]; exact lamMin_udiag_le hUU w i
    have htr : B.trace = ∑ i, w i := by rw [← trace_symPart, hBU, trace_udiag hUU]
    have hsum : (d : ℝ) * l ≤ ∑ i, w i := by
      calc (d : ℝ) * l = ∑ _i : Fin d, l := by simp
        _ ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => hwl i
    have hl0 : 0 ≤ l := by nlinarith
    refine ⟨?_, ?_⟩
    · rw [hBU, udiag_posSemidef_iff hUU]
      exact fun i => hl0.trans (hwl i)
    · rcases hl0.lt_or_eq with hpos | hzero
      · exact Or.inl hpos
      · right
        have hw0 : ∀ i, w i = 0 := by
          have hnn : ∀ i ∈ Finset.univ, 0 ≤ w i := fun i _ => hzero ▸ hwl i
          have hs0 : ∑ i, w i = 0 := by
            refine le_antisymm ?_ (Finset.sum_nonneg hnn)
            rw [← htr]; nlinarith
          exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs0 i (Finset.mem_univ i)
        have hS0 : symPart B = 0 := by
          rw [hBU, show w = fun _ => (0 : ℝ) from funext hw0, udiag_const hUU, zero_smul]
        have h2 : B + Bᵀ = 0 := by
          have := congrArg (fun M => (2 : ℝ) • M) hS0
          simp only [symPart, smul_smul, smul_zero] at this
          norm_num at this
          exact this
        exact (neg_eq_of_add_eq_zero_right h2).symm

end AffineHemigroup
