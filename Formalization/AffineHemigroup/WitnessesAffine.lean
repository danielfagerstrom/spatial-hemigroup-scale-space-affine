/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ConeOrders
import AffineHemigroup.RankDeficient
import AffineHemigroup.Rigidity
import AffineHemigroup.RigidityOperators
import AffineHemigroup.DiagonalStable
import AffineHemigroup.ShapeAdapted
import AffineHemigroup.WedgeAxis
import AffineHemigroup.WedgeAxisChain
import AffineHemigroup.Witnesses

/-!
# Witnesses of the affine paper: the headline theorems' hypotheses are jointly satisfiable

The fidelity review's P1 (article-kit `fidelity-review` skill, § 3.2; `blueprint/REVIEW-fidelity.md`,
section "Witnesses") for the theorems of chapters 4 and 5. Each theorem below instantiates
**all** the hypotheses of one headline theorem at once, at a concrete model, so that no
headline theorem is true only because nothing satisfies its hypotheses (failure mode F1). They
are named theorems, not `example`s, so that `CIAxiomGuard.lean` can print their axioms; nothing
in the library imports this file.

The general linear row is witnessed by the affine Gaussian scale space, which
`thm:affine-rigidity` makes an affine cascade family on Lean core.

The declarations stood in `AffineHemigroup.Witnesses` until Q-0452, which left there the
witnesses of the isotropic paper (chapter 3); they are here unchanged.
-/

namespace AffineHemigroup

/-! ## The general linear row -/

section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- The rank-one step `P = e₁e₁ᵀ`. -/
noncomputable def stepE1 (hd : 1 ≤ d) : Mat d := diagonal (Pi.single ⟨0, hd⟩ 1)

theorem stepE1_posSemidef (hd : 1 ≤ d) : (stepE1 hd).PosSemidef :=
  PosSemidef.diagonal fun i => by
    by_cases h : i = ⟨0, hd⟩
    · subst h; simp
    · simp [h]

theorem stepE1_rank (hd : 1 ≤ d) : (stepE1 hd).rank = 1 := by
  rw [stepE1, rank_diagonal]
  have : ∀ i : Fin d, ((Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Fin d → ℝ) i ≠ 0 ↔ i = ⟨0, hd⟩) := by
    intro i
    by_cases h : i = ⟨0, hd⟩
    · subst h; simp
    · simp [h]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight this), Fintype.card_subtype_eq]

/-- **Witness, `thm:rank-deficient-step`**: `g = id`, `Σ = I`, `P = e₁e₁ᵀ` of rank `1 < d`, and the
centred Gaussian of covariance `2P` satisfy every hypothesis at once. Lean core. -/
theorem witness_rank_deficient_step (hd : 2 ≤ d) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ id u) ∧ ContinuousWithinAt (id : ℝ → ℝ) (Ici 0) 0 ∧ id (0 : ℝ) = 0 ∧
      (1 : Mat d).PosDef ∧ (stepE1 (d := d) (by omega)).PosSemidef ∧
      0 < (stepE1 (d := d) (by omega)).rank ∧ (stepE1 (d := d) (by omega)).rank < d ∧
      ∀ ω : Rd d, ((Real.exp (-id (quad (1 + stepE1 (by omega)) ω)) : ℝ) : ℂ) =
        ((Real.exp (-id (quad 1 ω)) : ℝ) : ℂ) *
          charFun (ProbabilityTheory.multivariateGaussian 0 (((2 : ℝ) * 1) • stepE1 (d := d) (by omega))) ω := by
  refine ⟨fun u hu => hu, continuousWithinAt_id, rfl, PosDef.one, stepE1_posSemidef _, ?_, ?_, ?_⟩
  · rw [stepE1_rank]; exact one_pos
  · rw [stepE1_rank]; omega
  · intro ω
    exact rank_deficient_step_converse hd id 1 zero_le_one (fun u _ => by simp) 1 _ PosSemidef.one
      (stepE1_posSemidef _) ω

/-- **Witness, `thm:affine-rigidity`, `thm:affine-rigidity-operators`,
`thm:cascade-infinitely-divisible`(2)–(4)**: the affine Gaussian scale space with constant `1` is
an affine cascade family, its convolution operators are a `(GL(d), Loewner)`-cascade family of
operators, `(GL(d), Loewner)` is a wedge datum with the path condition, and the heat family is an
isotropic cascade family whose restriction to `0 ≤ s ≤ t ≤ 1` meets clause (1)'s hypotheses.
Lean core. -/
theorem witness_affine_rigidity (hd : 2 ≤ d) :
    IsAffineCascadeFamily (affineGaussian (d := d) 1) ∧
      IsGWOperatorFamily (glSet d) loewnerLE
        (fun S S' => ScaleSpace.mconvL1E (affineGaussian (d := d) 1 S S')) ∧
      IsWedgeDatum (glSet d) loewnerLE ∧ HasPathCondition (loewnerLE (d := d)) ∧
      IsIsotropicCascadeFamily (heatFamily d) (fun lam t => lam * t) ∧
      ∀ ω : Rd d, ContinuousOn (fun p : ℝ × ℝ => charFun (heatFamily d p.1 p.2) ω)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
  have hfam : IsAffineCascadeFamily (affineGaussian (d := d) 1) :=
    (affine_rigidity hd _).2 ⟨1, one_pos, fun _ _ => rfl⟩
  have hiso := (witness_isotropic_classification (d := d) (by omega)).2.1
  refine ⟨hfam, ((affine_rigidity_operators hd _).1).2 ⟨1, one_pos, fun _ _ => rfl⟩,
    isWedgeDatum_loewner glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2,
    fun S S' hS hS' hle => ⟨_, chain_loewner S S' hS hS' hle⟩, hiso, fun ω => ?_⟩
  exact (hiso.continuous ω).mono fun p hp => ⟨hp.1, hp.2.1⟩

/-- **Witness, `thm:cone-orders`**: `C = PSD(d)` meets the hypotheses of clauses (1) and (4), and
the step set of clause (3) meets those of clause (2). Lean core. -/
theorem witness_cone_orders (hd : 1 ≤ d) :
    (psdSet d ⊆ symSet d ∧ IsClosedConvexCone (psdSet d) ∧ IsOrthInvariant (psdSet d) ∧
      (1 : Mat d) ∈ psdSet d ∧ ∀ X ∈ psdSet d, -X ∈ psdSet d → X = 0) ∧
    let K : Set (Mat d) := {1} ∪ {M | M.PosDef ∧ 2 ≤ eigUp M ⟨0, by omega⟩}
    IsStepSet K ∧ closure K ∩ pdSet d ⊆ K ∧ IsPartialOrderOn (pdSet d) (stepLE K) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := psdSet_cone_props (d := d) hd
  obtain ⟨k1, k2, k3, -⟩ := closed_order_without_cone (d := d) hd
  exact ⟨⟨h1, h3, h2, h4, h5⟩, k1, k2, k3⟩

/-- The shape-adapted aperture matrix `M = diag(2, 1, …, 1)`. -/
noncomputable def apertureM (hd : 1 ≤ d) : Mat d :=
  diagonal fun i => if i = (⟨0, hd⟩ : Fin d) then 2 else 1

/-- **Witness, `prop:shape-adapted-apertures`**: `M = diag(2,1,…,1)` is positive definite with least
eigenvalue `1` and `M ≠ I`; `g = id` with `μ_I = N(0, 2I)` meets clause (2)'s hypotheses; and
`(GL(d), Loewner)` with the affine Gaussian family meets clause (3)'s, with `tI ≤ tM` at `t = 1`.
Lean core. -/
theorem witness_shape_adapted (hd : 2 ≤ d) :
    (apertureM (d := d) (by omega)).PosDef ∧ lamMin (apertureM (d := d) (by omega)) = 1 ∧
      apertureM (d := d) (by omega) ≠ 1 ∧
      (∀ ω : Rd d, charFun (gaussVar d 2) ω = ((Real.exp (-id (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      IsWedgeDatum (glSet d) loewnerLE ∧
      loewnerLE ((1 : ℝ) • (1 : Mat d)) ((1 : ℝ) • apertureM (d := d) (by omega)) ∧
      IsGWCascadeFamily (glSet d) loewnerLE (affineGaussian (d := d) 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hM : (apertureM (d := d) (by omega)).PosDef := by
    rw [apertureM, posDef_diagonal_iff]
    intro i; split_ifs <;> norm_num
  refine ⟨hM, ?_, ?_, fun ω => ?_, isWedgeDatum_loewner glSet_isClosedSubgroupGL.1
    glSet_isClosedSubgroupGL.2, ?_, (witness_affine_rigidity hd).1⟩
  · rw [apertureM, lamMin_diagonal]
    refine le_antisymm (ciInf_le_of_le (Finite.bddBelow_range _) ⟨1, by omega⟩ ?_) ?_
    · simp [Fin.ext_iff]
    · exact le_ciInf fun i => by split_ifs <;> norm_num
  · intro h
    have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [apertureM] at this
  · rw [charFun_gaussVar (by norm_num)]
    congr 2
    simp only [id]
    ring
  · rw [one_smul, one_smul, loewnerLE]
    have : apertureM (d := d) (by omega) - 1 = diagonal fun i =>
        if i = (⟨0, by omega⟩ : Fin d) then (1 : ℝ) else 0 := by
      rw [apertureM, ← diagonal_one, diagonal_sub]
      congr 1; funext i; split_ifs <;> norm_num
    rw [this]
    exact PosSemidef.diagonal fun i => by
      show (0 : ℝ) ≤ if i = (⟨0, by omega⟩ : Fin d) then 1 else 0
      split_ifs <;> norm_num

/-- **Witness, `thm:wedge-axis`**: the cones `C_α`, `0 ≤ α < ∞`, and `C_∞ = PSD(d)` meet the
standing hypotheses of clause (2), `PSD(d)` in case (b) (it contains the nonzero singular
`e₁e₁ᵀ`) and every `C_α`, `α < ∞`, in case (c) (its nonzero members are positive definite).
Lean core. The stable law `S_γ(I)` that clause (2)(c) and clause (3) quantify over exists by
`lem:elliptical-stable`(2), which spends A3(iii). -/
theorem witness_wedge_axis (hd : 2 ≤ d) {α : ℝ} (hα : 0 ≤ α) :
    (stableGenCone d α ⊆ symSet d ∧ IsClosedConvexCone (stableGenCone d α) ∧
      IsOrthInvariant (stableGenCone d α) ∧ (1 : Mat d) ∈ stableGenCone d α ∧
      (∀ X ∈ stableGenCone d α, -X ∈ stableGenCone d α → X = 0) ∧
      stableGenCone d α ⊆ psdSet d ∧ ∀ X ∈ stableGenCone d α, X ≠ 0 → X.det ≠ 0) ∧
    (∃ X ∈ psdSet d, X ≠ 0 ∧ X.det = 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stableGenCone_props (d := d) (by omega) hα
  refine ⟨⟨h1, h3, h2, h4, h5, fun X hX => hX.1, fun X hX hX0 => ?_⟩, ?_⟩
  · exact ((wedge_axis_chain hd).2.1 α hα X hX hX0).det_pos.ne'
  · refine ⟨stepE1 (by omega), stepE1_posSemidef _, fun h => ?_, ?_⟩
    · have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [stepE1] at this
    · rw [stepE1, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨1, by omega⟩ : Fin d))
        (by simp [Fin.ext_iff])

end

/-! ## `thm:wedge-axis`(2)(a): a cone not inside `PSD(d)` (the fresh-agent passes' coverage, Q-0376) -/

section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- **The cone `{X ∈ Sym(d) : λ_min(X) + tr X ≥ 0}`**: an `O(d)`-invariant pointed closed convex
cone containing `I` which, for `d ≥ 2`, is not inside `PSD(d)` (it contains
`diag(-1/2, 1, …, 1)`). The model of `thm:wedge-axis`(2)(a). -/
def nonpsdCone (d : ℕ) : Set (Mat d) := {X | X.IsSymm ∧ 0 ≤ lamMin X + X.trace}

/-- **Witness, `thm:wedge-axis`(2)(a)** (`lem:wedge-axis-chain`, `wedge_axis_not_psd`): the cone
`{X ∈ Sym(d) : λ_min(X) + tr X ≥ 0}` meets every hypothesis of case (a) — symmetric, closed,
convex, a cone, `O(d)`-invariant, containing `I`, `C ∩ (-C) = {0}` — and is not inside `PSD(d)`.
Lean core. -/
theorem witness_wedge_axis_nonpsd (hd : 2 ≤ d) :
    nonpsdCone d ⊆ symSet d ∧ IsClosedConvexCone (nonpsdCone d) ∧
      IsOrthInvariant (nonpsdCone d) ∧ (1 : Mat d) ∈ nonpsdCone d ∧
      (∀ X ∈ nonpsdCone d, -X ∈ nonpsdCone d → X = 0) ∧ ¬ nonpsdCone d ⊆ psdSet d := by
  haveI : NeZero d := ⟨by omega⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨fun X hX => hX.1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- closed
    refine isClosed_of_closure_subset fun X hX => ?_
    obtain ⟨Xs, hXs, hlim⟩ := mem_closure_iff_seq_limit.1 hX
    have hXsym : X.IsSymm := isClosed_symSet.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hXs n).1)
    refine ⟨hXsym, ?_⟩
    have he := tendsto_eigUp (fun n => (hXs n).1) hXsym hlim
    have he0 : Tendsto (fun n => lamMin (Xs n)) atTop (𝓝 (lamMin X)) := by
      rw [lamMin_eq_eigUp_zero (isHermitian_of_isSymm hXsym)]
      refine (((continuous_apply (0 : Fin d)).tendsto _).comp he).congr fun n => ?_
      exact (lamMin_eq_eigUp_zero (isHermitian_of_isSymm (hXs n).1)).symm
    have htr : Tendsto (fun n => (Xs n).trace) atTop (𝓝 X.trace) :=
      (continuous_id.matrix_trace.tendsto X).comp hlim
    exact ge_of_tendsto' (he0.add htr) fun n => (hXs n).2
  · -- convex
    intro X hX Y hY a b ha hb _
    refine ⟨(hX.1.smul a).add (hY.1.smul b), ?_⟩
    have h1 := lamMin_add_ge (isHermitian_of_isSymm (hX.1.smul a))
      (isHermitian_of_isSymm (hY.1.smul b))
    rw [lamMin_smul ha, lamMin_smul hb] at h1
    rw [trace_add, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [mul_nonneg ha hX.2, mul_nonneg hb hY.2]
  · -- contains 0
    exact ⟨Matrix.isSymm_zero, by rw [lamMin_zero_mat, trace_zero, add_zero]⟩
  · -- a cone
    intro c hc X hX
    refine ⟨hX.1.smul c, ?_⟩
    rw [lamMin_smul hc, trace_smul, smul_eq_mul]
    nlinarith [mul_nonneg hc hX.2]
  · -- `O(d)`-invariant
    intro Q hQ X hX
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hX.1.eq,
        Matrix.mul_assoc]
    · rw [trace_conj_orth hQ, lamMin_conj_orth hQ (isHermitian_of_isSymm hX.1)]
      exact hX.2
  · -- contains `I`
    refine ⟨Matrix.isSymm_one, ?_⟩
    rw [lamMin_one, trace_one, Fintype.card_fin]
    linarith
  · -- pointed
    intro X hX hnX
    have h1 := card_mul_lamMin_le_trace hX.1
    have h2 := card_mul_lamMin_le_trace hnX.1
    have hX2 := hX.2
    have hnX2 := hnX.2
    rw [trace_neg] at h2 hnX2
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have htr : X.trace = 0 := by nlinarith
    rw [htr] at hX2 hnX2
    exact eq_zero_of_posSemidef_neg
      (posSemidef_of_lamMin_nonneg (isHermitian_of_isSymm hX.1) (by linarith))
      (posSemidef_of_lamMin_nonneg (isHermitian_of_isSymm hnX.1) (by linarith))
  · -- not inside `PSD(d)`: `diag(-1/2, 1, …, 1)`
    set i₀ : Fin d := ⟨0, by omega⟩
    set v : Fin d → ℝ := fun i => 1 - if i = i₀ then 3 / 2 else 0 with hv
    intro hsub
    have hmem : diagonal v ∈ nonpsdCone d := by
      refine ⟨isSymm_diagonal v, ?_⟩
      have hmin : -(1 / 2 : ℝ) ≤ lamMin (diagonal v) := by
        rw [lamMin_diagonal]
        exact le_ciInf fun i => by simp only [hv]; split_ifs <;> norm_num
      have htr : (diagonal v).trace = (d : ℝ) - 3 / 2 := by
        rw [trace_diagonal, hv, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i₀]
        simp
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      rw [htr]
      linarith
    have hpsd := hsub hmem
    have := hpsd.diag_nonneg (i := i₀)
    simp [hv, diagonal_apply_eq] at this
    norm_num at this

end

end AffineHemigroup
