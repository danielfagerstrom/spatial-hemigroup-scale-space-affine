/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.WedgeAxisChain
import AffineHemigroup.AnisotropyBudget
import AffineHemigroup.AnisotropyConverse
import AffineHemigroup.SimilarityStableOrder

/-!
# `thm:wedge-axis` — the wedge axis of the general linear row, clauses (2)(c) and (3)

Blueprint: `blueprint/src/parts/05-table.tex`, `thm:wedge-axis` (Q-0281 wave 2, group H). Clauses
(1), (2)(a) and (2)(b) are `lem:wedge-axis-chain` (`AffineHemigroup.WedgeAxisChain`).

## The entry-free route (the author's decision on W2F-1)

As in the child, nothing here reads an order property of `≼_C` that spends ledger A9: `C ⊆ C_γ`
makes every `C`-causal curve `C_γ`-causal, and `≼_γ` is identified by
`prop:stable-order-generated`(1) (Lean core); the restrictions are `gw_family_restrict_of_le`. The
node spends A5 and A3(i)–(ii) through `prop:anisotropy-budget`(1), in the necessity half of the
non-Gaussian clause, and A3(iii) for the stable laws (`lem:elliptical-stable`(2),
`prop:stable-step-cone`(1), `prop:similarity-stable-order-families`(2)).

## The number `β(C)`

The largest value of `f(X) = tr X/λ_min(X) - d` is read on the compact slice
`{X ∈ C : tr X = 1}`, whose entries lie in `[-1, 1]` (`X = V diag(x) Vᵀ` with `x ≥ 0`, `∑ x = 1`,
`|Vᵢₖ| ≤ 1`); `λ_min` is continuous on `Sym(d)` (`tendsto_eigUp'`, Ky Fan), and `f` is invariant
under positive scaling, so its largest value on the slice is its largest value on `C ∖ {0}`. The
norm `‖X‖` of the blueprint's slice is replaced by the trace, which is positive on `C ∖ {0}`.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## Helpers -/

/-- **`e^{-tB} → 0` when `λ_min(sym B) > 0`** (`|e^{-tB}x| ≤ e^{-λt}|x|`). -/
theorem isExpContracting_of_lamMin_pos [NeZero d] (B : Mat d) (hl0 : 0 < lamMin (symPart B)) :
    IsExpContracting B := by
  set l := lamMin (symPart B) with hl
  change Tendsto (fun t : ℝ => mexp (-t • B)) atTop (𝓝 0)
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hbound : ∀ t : ℝ, 0 ≤ t → |mexp (-t • B) i j| ≤ Real.exp (-(l * t)) := by
    intro t ht
    have h1 := norm_sq_mexp_neg_le B (ebasis j) ht
    rw [show t • (-B) = -t • B by rw [smul_neg, neg_smul]] at h1
    have hn : ‖ebasis j‖ = (1 : ℝ) := by simp [ebasis]
    rw [hn, one_pow, mul_one] at h1
    have hentry : |mexp (-t • B) i j| ≤ ‖lin (mexp (-t • B)) (ebasis j)‖ := by
      have : mexp (-t • B) i j = (lin (mexp (-t • B)) (ebasis j)) i := by
        change _ = (mexp (-t • B) *ᵥ (ebasis j).ofLp) i
        simp [ebasis, mulVec, dotProduct]
      rw [this]
      have := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ)
        (lin (mexp (-t • B)) (ebasis j)) i
      rwa [Real.norm_eq_abs] at this
    have hsq : ‖lin (mexp (-t • B)) (ebasis j)‖ ≤ Real.exp (-(l * t)) := by
      have he : Real.exp (-(2 * l * t)) = Real.exp (-(l * t)) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [he] at h1
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h1
    exact hentry.trans hsq
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(l * t))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl0)
    simpa [Function.comp_def] using this
  refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
  exact squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _)
    (eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩) hexp

/-- **`S_γ(I)` is not Gaussian** for `0 < γ < 2` (`prop:anisotropy-budget-converse` at `B = I`). -/
theorem not_isGaussian_ellipticalStable (hd : 1 ≤ d) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {σ : Measure (Rd d)} (hσ : IsEllipticalStable γ 1 σ) : ¬ IsGaussian σ := by
  haveI : NeZero d := ⟨by omega⟩
  have hs : symPart (1 : Mat d) = 1 := symPart_of_isSymm isSymm_one
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := anisotropy_budget_converse hd (1 : Mat d) (by
    rw [hs, lamMin_one, trace_one, Fintype.card_fin]; linarith)
  refine (h.2.2 γ hγ0 hγ2 ?_ σ hσ).2.1
  rw [hs, lamMin_one, trace_one, Fintype.card_fin, div_one, sub_self]
  exact hγ0.le

/-- `≼⁺_C ⊆ ≤_γ` when `C ⊆ C_γ`, `γ > 0` (`prop:stable-order-generated`(1); entry-free). -/
theorem causalPlusLE_stablePlusLE (hd : 1 ≤ d) {γ : ℝ} (hγ0 : 0 < γ) {C : Set (Mat d)}
    (hsub : C ⊆ stableGenCone d γ) {S S' : Mat d} (h : causalPlusLE C S S') :
    stablePlusLE γ S S' := by
  rcases h with h | h | ⟨h1, h2, γc, hγc, h0, h1'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, h2,
      (((stable_order_pos hd hγ0).2 S S' h1 h2).1).1 ⟨γc, hγc.mono hsub, h0, h1'⟩⟩)

/-- `|Xᵢⱼ| ≤ tr X` for `X ∈ PSD(d)`. -/
theorem abs_apply_le_trace {X : Mat d} (hX : X.PosSemidef) (i j : Fin d) : |X i j| ≤ X.trace := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hX.isHermitian
  have hx := eigUp_nonneg hX
  have hrow : ∀ a k, |V a k| ≤ 1 := by
    intro a k
    have h := congrFun (congrFun hV a) a
    rw [Matrix.mul_apply, one_apply_eq] at h
    simp only [transpose_apply] at h
    have hle : V a k * V a k ≤ ∑ l, V a l * V a l :=
      Finset.single_le_sum (f := fun l => V a l * V a l) (fun l _ => mul_self_nonneg _)
        (Finset.mem_univ k)
    rw [h] at hle
    rw [← abs_mul_abs_self] at hle
    nlinarith [abs_nonneg (V a k)]
  rw [← sum_eigUp hX.isHermitian]
  conv_lhs => rw [hXV, udiag_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hx k)]
  have h1 := hrow i k
  have h2 := hrow j k
  have := hx k
  calc |V i k| * eigUp X k * |V j k| ≤ 1 * eigUp X k * 1 := by gcongr
    _ = eigUp X k := by ring

/-! ## `thm:wedge-axis`(2)(c), the number `β(C)` -/

/-- **`thm:wedge-axis`(2)(c)**, the number `β(C)`: for an `O(d)`-invariant closed convex cone
`C ⊆ PSD(d)` with `I ∈ C`, `C ∩ (-C) = {0}` and no nonzero singular member, every nonzero member is
positive definite, the largest value `β(C)` of `tr X/λ_min(X) - d` over `X ∈ C ∖ {0}` is attained,
and `β(C) ∈ [0, ∞)` is the least `α` with `C ⊆ C_α`. -/
theorem wedge_axis_index (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (_hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (_hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) :
    (∀ X ∈ C, X ≠ 0 → X.PosDef) ∧
      IsGreatest ((fun X : Mat d => X.trace / lamMin X - d) '' (C \ {0})) (coneIndex C) ∧
      0 ≤ coneIndex C ∧ IsLeast {α : ℝ | 0 ≤ α ∧ C ⊆ stableGenCone d α} (coneIndex C) := by
  haveI : NeZero d := ⟨by omega⟩
  set f : Mat d → ℝ := fun X => X.trace / lamMin X - d with hfdef
  /- The nonzero members are positive definite. -/
  have hpdC : ∀ X ∈ C, X ≠ 0 → X.PosDef := by
    intro X hX h0
    have hXp : X.PosSemidef := hpsd hX
    obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hXp.isHermitian
    rw [hXV]
    refine (udiag_posDef_iff hV _).2 fun i =>
      lt_of_le_of_ne (eigUp_nonneg hXp i) fun h => hdef X hX h0 ?_
    rw [← prod_eigUp hXp.isHermitian]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm
  have hlpos : ∀ X ∈ C, X ≠ 0 → 0 < lamMin X := fun X hX h0 => lamMin_pos (hpdC X hX h0)
  have hfnn : ∀ X ∈ C, X ≠ 0 → 0 ≤ f X := by
    intro X hX h0
    have hl := hlpos X hX h0
    have := card_mul_lamMin_le_trace (hCsym hX)
    simp only [hfdef, sub_nonneg, le_div_iff₀ hl]
    exact this
  /- The slice `T = {X ∈ C : tr X = 1}`: compact, nonempty, `f` continuous on it. -/
  set T : Set (Mat d) := C ∩ {X | X.trace = 1} with hTdef
  have hT0 : ∀ X ∈ T, X ≠ 0 := by
    rintro X ⟨-, hX1⟩ rfl
    rw [mem_setOf_eq, trace_zero] at hX1
    exact zero_ne_one hX1
  have hTcpt : IsCompact T := by
    set Kc : Set (Mat d) := Set.pi univ fun _ => Set.pi univ fun _ => Icc (-1 : ℝ) 1
    have hK : IsCompact Kc := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    refine hK.of_isClosed_subset (hC.1.inter (isClosed_eq continuous_id.matrix_trace
      continuous_const)) fun X hX i _ j _ => ?_
    have h := abs_apply_le_trace (hpsd hX.1) i j
    rw [hX.2] at h
    exact abs_le.1 h
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hTne : T.Nonempty := by
    refine ⟨(d : ℝ)⁻¹ • (1 : Mat d), hC.2.2.2 _ (inv_nonneg.2 hdpos.le) _ hI, ?_⟩
    rw [mem_setOf_eq, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
      inv_mul_cancel₀ hdpos.ne']
  have hlcont : ContinuousOn (fun X : Mat d => lamMin X) T := by
    intro X hX
    have hXs : X.IsSymm := hCsym hX.1
    have he := tendsto_eigUp' (l := 𝓝[T] X) (Xs := id)
      (eventually_nhdsWithin_of_forall fun Y hY => hCsym hY.1) hXs
      (tendsto_id.mono_left nhdsWithin_le_nhds)
    have h0 := ((continuous_apply (0 : Fin d)).tendsto _).comp he
    rw [ContinuousWithinAt, lamMin_eq_eigUp_zero (isHermitian_of_isSymm hXs)]
    refine h0.congr' (eventually_nhdsWithin_of_forall fun Y hY => ?_)
    exact (lamMin_eq_eigUp_zero (isHermitian_of_isSymm (hCsym hY.1))).symm
  have hfcont : ContinuousOn f T :=
    ((continuous_id.matrix_trace.continuousOn).div hlcont
      fun X hX => (hlpos X hX.1 (hT0 X hX)).ne').sub continuousOn_const
  obtain ⟨Xs, hXsT, hmax⟩ := hTcpt.exists_isMaxOn hTne hfcont
  /- `f` is invariant under positive scaling, so its maximum on `T` is its maximum on `C ∖ {0}`. -/
  have hscale : ∀ X ∈ C, X ≠ 0 → (X.trace)⁻¹ • X ∈ T ∧ f ((X.trace)⁻¹ • X) = f X := by
    intro X hX h0
    have htr := trace_pos_of_posSemidef (hpsd hX) h0
    refine ⟨⟨hC.2.2.2 _ (inv_nonneg.2 htr.le) _ hX, ?_⟩, ?_⟩
    · rw [mem_setOf_eq, trace_smul, smul_eq_mul, inv_mul_cancel₀ htr.ne']
    · simp only [hfdef, trace_smul, lamMin_smul (inv_nonneg.2 htr.le), smul_eq_mul]
      rw [mul_div_mul_left _ _ (inv_ne_zero htr.ne')]
  have hbound : ∀ X ∈ C, X ≠ 0 → f X ≤ f Xs := by
    intro X hX h0
    obtain ⟨hT, hf⟩ := hscale X hX h0
    rw [← hf]
    exact hmax hT
  have hgreat : IsGreatest (f '' (C \ {0})) (f Xs) :=
    ⟨⟨Xs, ⟨hXsT.1, hT0 Xs hXsT⟩, rfl⟩, by
      rintro _ ⟨X, ⟨hX, hX0⟩, rfl⟩
      exact hbound X hX hX0⟩
  have hidx : coneIndex C = f Xs := hgreat.csSup_eq
  have hβ0 : 0 ≤ f Xs := hfnn Xs hXsT.1 (hT0 Xs hXsT)
  refine ⟨hpdC, hidx ▸ hgreat, hidx ▸ hβ0, ?_⟩
  rw [hidx]
  refine ⟨⟨hβ0, fun X hX => ?_⟩, fun α ⟨hα, hsub⟩ => ?_⟩
  · by_cases h0 : X = 0
    · subst h0
      exact (stableGenCone_props (by omega) hβ0).2.2.1.2.2.1
    · have hl := hlpos X hX h0
      refine ⟨hpsd hX, ?_⟩
      have := hbound X hX h0
      simp only [hfdef, sub_le_iff_le_add, div_le_iff₀ hl] at this
      linarith
  · have hXsC := hsub hXsT.1
    have hl := hlpos Xs hXsT.1 (hT0 Xs hXsT)
    simp only [hfdef, sub_le_iff_le_add, div_le_iff₀ hl]
    linarith [hXsC.2]

/-! ## `thm:wedge-axis`(2)(c), the stable orbits -/

/-- **`thm:wedge-axis`(2)(c)**, the stable orbits: in the setting of `wedge_axis_index`, for
`0 < γ < 2`, `Σ ↦ (Σ^{1/2})_*S_γ(I)` is the family of kernels from the origin of a
`(GL(d), ≼⁺_C)`-cascade family if and only if `γ ≥ β(C)`. Spends A3(iii) through
`lem:elliptical-stable`(2), `prop:stable-step-cone`(1) and
`prop:similarity-stable-order-families`(2). -/
theorem wedge_axis_stable (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (σ : Measure (Rd d)) (hσ : IsEllipticalStable γ 1 σ) :
    IsKernelsFromOrigin (glSet d) (causalPlusLE C) (affineOrbit σ) ↔ coneIndex C ≤ γ := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hidx := wedge_axis_index hd hCsym hC hO hI hpt hpsd hdef
  constructor
  · rintro ⟨μ, hμ, hμm⟩
    refine hidx.2.2.2.2 ⟨hγ0.le, fun X hX => ?_⟩
    have hXs := hCsym hX
    have hM := posDef_mexp hXs
    have h1M := causalPlusLE_one_mexp hCsym hO hX
    haveI := hμ.isProbability (1, mexp X) ⟨PosSemidef.one, hM.posSemidef, h1M⟩
    have hcasc := hμ.cascade 0 1 (mexp X) PosSemidef.zero PosSemidef.one hM.posSemidef
      (causalPlusLE_zero_left 1) h1M
    rw [hμm _ hM.posSemidef, hμm _ PosSemidef.one] at hcasc
    have hfam : ∀ S : Mat d, S.PosDef → IsEllipticalStable γ S (affineOrbit σ S) :=
      (ellipticalStable_orbit hγ0 hγ2 σ hσ).2.2.2.2
    haveI := (hfam 1 PosDef.one).1
    have htfae := (stable_step_cone_tfae hγ0 hγ2 (affineOrbit σ) hfam PosDef.one hM).out 0 2
    have hdet := htfae.1 ⟨μ 1 (mexp X), inferInstance, by rw [hcasc, Measure.conv_comm]⟩
    rw [relStep_one_left] at hdet
    exact mem_of_mexp_mem_expSet (stableGenCone_props hd1 hγ0.le).1 hXs
      ((mem_expSet_stableGenCone_iff hd1 hγ0 hM).2 hdet)
  · intro hβ
    have hsub : C ⊆ stableGenCone d γ := hidx.2.2.2.1.2.trans (stableGenCone_mono hd1 hβ)
    obtain ⟨μ, hμ, hμm⟩ := (stable_order_gl_row_examples hd hγ0 hγ2).1 γ le_rfl hγ2 σ hσ
    exact ⟨μ, gw_family_restrict_of_le subset_rfl
      (fun S S' _ _ h => causalPlusLE_stablePlusLE hd1 hγ0 hsub h) μ hμ, hμm⟩

/-! ## `thm:wedge-axis`(2)(c), the non-Gaussian families -/

/-- **`thm:wedge-axis`(2)(c)**, the non-Gaussian families: in the setting of `wedge_axis_index`, a
`(GL(d), ≼⁺_C)`-cascade family whose `μ_I` is not Gaussian exists if and only if `β(C) < 2`; and if
`β(C) ≥ 2`, the families are those of (b), the restrictions of the affine Gaussian scale spaces.
Spends A5 and A3(i)–(ii) through `prop:anisotropy-budget`(1). -/
theorem wedge_axis_non_gaussian (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) :
    ((∃ μ : Mat d → Mat d → Measure (Rd d),
        IsGWCascadeFamily (glSet d) (causalPlusLE C) μ ∧ ¬ IsGaussian (μ 0 1)) ↔
        coneIndex C < 2) ∧
      (2 ≤ coneIndex C → ∀ μ : Mat d → Mat d → Measure (Rd d),
        IsGWCascadeFamily (glSet d) (causalPlusLE C) μ ↔
          ∃ b : ℝ, 0 < b ∧ EqOnPairs (causalPlusLE C) μ (affineGaussian b)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hidx := wedge_axis_index hd hCsym hC hO hI hpt hpsd hdef
  obtain ⟨hpdC, ⟨⟨Xs, ⟨hXsC, hXs0⟩, hfXs⟩, -⟩, -, -⟩ := hidx
  have hfXs' : Xs.trace / lamMin Xs - d = coneIndex C := hfXs
  have hray : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → rayLE S S' → causalPlusLE C S S' :=
    fun S S' _ _ h => causalPlusLE_of_rayLE h
  /- The budget: a family with a non-Gaussian `μ_I` has `f(X) < 2` on `C ∖ {0}`. -/
  have hbudget : ∀ μ : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (glSet d) (causalPlusLE C) μ → ¬ IsGaussian (μ 0 1) →
      ∀ X ∈ C, X ≠ 0 → X.trace / lamMin X - d < 2 := by
    intro μ hμ hng X hX hX0
    obtain ⟨hp, hrot, -, -, horb, -⟩ := gl_kernels_of_rays hray hμ
    have hXpd := hpdC X hX hX0
    have hXs := hCsym hX
    have hl := lamMin_pos hXpd
    set B : Mat d := (1 / 2 : ℝ) • X with hBdef
    have hBs : symPart B = B := symPart_of_isSymm (hXs.smul _)
    have hlB : lamMin B = 1 / 2 * lamMin X := lamMin_smul (by norm_num) X
    have hB : IsExpContracting B :=
      isExpContracting_of_lamMin_pos B (by rw [hBs, hlB]; positivity)
    have hsd : IsBSelfDecomposable B (μ 0 1) := by
      rw [isBSelfDecomposable_iff]
      intro t ht
      have htX : t • X ∈ C := hC.2.2.2 t ht.le X hX
      have hM := posDef_mexp (hCsym htX)
      have h1M := causalPlusLE_one_mexp hCsym hO htX
      haveI := hμ.isProbability (1, mexp (t • X)) ⟨PosSemidef.one, hM.posSemidef, h1M⟩
      have hcasc := hμ.cascade 0 1 (mexp (t • X)) PosSemidef.zero PosSemidef.one hM.posSemidef
        (causalPlusLE_zero_left 1) h1M
      rw [horb _ hM.posSemidef] at hcasc
      have hsq : msqrt (mexp (t • X)) = mexp (t • B) := by
        rw [msqrt_eq_mexp hM, mlog_mexp (isHermitian_of_isSymm (hCsym htX)), hBdef, smul_smul,
          smul_smul, mul_comm]
      refine ⟨push (mexp (-t • B)) (μ 1 (mexp (t • X))), inferInstance, ?_⟩
      have h := congrArg (push (mexp (-t • B))) hcasc
      rw [affineOrbit, hsq, push_push, mexp_neg_mul_mexp, push_one, push_conv] at h
      conv_rhs => rw [Measure.conv_comm]
      exact h
    obtain ⟨-, htr⟩ := anisotropy_budget hd1 B hB (μ 0 1) hrot hsd hng
    rw [hBs, hlB, hBdef, trace_smul, smul_eq_mul] at htr
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hl]
    linarith
  refine ⟨⟨fun ⟨μ, hμ, hng⟩ => ?_, fun hβ2 => ?_⟩, fun hβ2 μ => ⟨fun hμ => ?_, ?_⟩⟩
  · rw [← hfXs]
    exact hbudget μ hμ hng Xs hXsC hXs0
  · /- `S_γ(I)` with `γ = max(β(C), 1)`. -/
    set γ := max (coneIndex C) 1 with hγ
    have hγ0 : 0 < γ := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hγ2 : γ < 2 := max_lt hβ2 (by norm_num)
    obtain ⟨σ, hσ, -⟩ := exists_ellipticalStable hγ0 hγ2 (PosDef.one (n := Fin d))
    obtain ⟨μ, hμ, hμm⟩ := (wedge_axis_stable hd hCsym hC hO hI hpt hpsd hdef hγ0 hγ2 σ hσ).2
      (le_max_left _ _)
    refine ⟨μ, hμ, ?_⟩
    rw [hμm 1 PosSemidef.one, affineOrbit_one]
    exact not_isGaussian_ellipticalStable hd1 hγ0 hγ2 hσ
  · /- `μ_I` is Gaussian, so `g(u) = bu`. -/
    have hG : IsGaussian (μ 0 1) := by
      by_contra hng
      have := hbudget μ hμ hng Xs hXsC hXs0
      rw [hfXs'] at this
      linarith
    obtain ⟨hp, -, -, -, -, g, -, hgnn, -, ⟨u₀, hu₀, hgu₀⟩, hg⟩ := gl_kernels_of_rays hray hμ
    have hmap := hG.map_eq_gaussianReal (EuclideanSpace.proj (0 : Fin d))
    set v := (Var[(EuclideanSpace.proj (0 : Fin d) : Rd d →L[ℝ] ℝ); μ 0 1]).toNNReal
    have hlin : ∀ u : ℝ, 0 ≤ u → g u = (v : ℝ) / 2 * u := by
      intro u hu
      have h1 := charFun_map_proj (μ 0 1) (Real.sqrt u)
      rw [hmap, charFun_gaussianReal, hg 1 PosSemidef.one, quad_one] at h1
      have hn : ‖Real.sqrt u • ebasis (0 : Fin d)‖ ^ 2 = u := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        simp [ebasis, Real.sq_sqrt hu]
      rw [hn] at h1
      have h2 := congrArg (fun z : ℂ => ‖z‖) h1
      rw [Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
      have hre : ((Real.sqrt u : ℂ) * (μ 0 1)[(EuclideanSpace.proj (0 : Fin d) : Rd d →L[ℝ] ℝ)] *
          Complex.I - ((v : ℝ) : ℂ) * (Real.sqrt u : ℂ) ^ 2 / 2).re = -((v : ℝ) * u / 2) := by
        simp [Complex.mul_re, Complex.sub_re, pow_two, Real.mul_self_sqrt hu]
      rw [hre] at h2
      have := Real.exp_injective h2
      linarith
    have hb : 0 < (v : ℝ) / 2 := by
      have hv : 0 ≤ (v : ℝ) / 2 := by positivity
      refine lt_of_le_of_ne hv fun h => hgu₀ ?_
      rw [hlin u₀ hu₀, ← h, zero_mul]
    refine ⟨(v : ℝ) / 2, hb, eqOnPairs_affineGaussian_of_charFun hpsd hμ hb fun S hS ω => ?_⟩
    rw [hg S hS ω, hlin _ (quad_nonneg hS ω)]
  · rintro ⟨b, hb, h⟩
    exact family_of_eqOnPairs_affineGaussian hd hCsym hC hO hI hpsd hb h


/-! ## `thm:wedge-axis`(3), the row along the chain -/

theorem stableGenConeTop_coe (a : ℝ) : stableGenConeTop d (a : WithTop ℝ) = stableGenCone d a :=
  rfl

/-- `C_a`, `0 ≤ a < ∞`, is in case (2)(c): its nonzero members are definite. -/
theorem stableGenCone_det_ne_zero (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    ∀ X ∈ stableGenCone d a, X ≠ 0 → X.det ≠ 0 := by
  haveI : NeZero d := ⟨by omega⟩
  intro X hX h0
  exact (posDef_of_lamMin_pos hX.1.isHermitian
    (lamMin_pos_of_mem_stableGenCone hd ha hX h0)).det_pos.ne'

/-- **`β(C_a) = a`** for `0 ≤ a < ∞`. -/
theorem coneIndex_stableGenCone (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    coneIndex (stableGenCone d a) = a := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 ha
  have hidx := wedge_axis_index hd hCsym hC hO hI hpt (fun X hX => hX.1)
    (stableGenCone_det_ne_zero hd1 ha)
  refine le_antisymm (hidx.2.2.2.2 ⟨ha, subset_rfl⟩) ?_
  obtain ⟨hWp, htr, hl⟩ := witness_props hd ha
  have hW := hidx.2.2.2.1.2 ⟨hWp, by rw [htr, hl, mul_one]⟩
  have := hW.2
  rw [htr, hl, mul_one] at this
  linarith

/-- **`𝔉_α` is read through the kernels from the origin**: `m ∈ 𝔉_α` if and only if
`Σ ↦ (Σ^{1/2})_*m` is the family of kernels from the origin of a `(GL(d), ≼⁺_{C_α})`-family. -/
theorem mem_rowLaws_iff (hd : 1 ≤ d) (α : WithTop ℝ) (m : Measure (Rd d)) :
    m ∈ rowLaws d α ↔
      IsKernelsFromOrigin (glSet d) (causalPlusLE (stableGenConeTop d α)) (affineOrbit m) := by
  haveI : NeZero d := ⟨by omega⟩
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨μ, hμ, (gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ).2.2.2.2.1⟩
  · rintro ⟨μ, hμ, hμm⟩
    exact ⟨μ, hμ, by rw [hμm 1 PosSemidef.one, affineOrbit_one]⟩

/-- **`𝔉_α` for `2 ≤ α ≤ ∞`** (the Gaussian end of the row). -/
theorem rowLaws_gaussian (hd : 2 ≤ d) {α : WithTop ℝ} (hα : 2 ≤ α) :
    rowLaws d α = {m : Measure (Rd d) |
      ∃ b : ℝ, 0 < b ∧ m = multivariateGaussian 0 ((2 * b) • (1 : Mat d))} := by
  have hd1 : 1 ≤ d := by omega
  have hα0 : 0 ≤ α := le_trans (by exact_mod_cast zero_le_two) hα
  obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenConeTop_props hd1 hα0
  have hpsd := stableGenConeTop_subset_psd (d := d) α
  /- Every family is a restricted affine Gaussian scale space. -/
  have hfam : ∀ μ : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (glSet d) (causalPlusLE (stableGenConeTop d α)) μ →
      ∃ b : ℝ, 0 < b ∧ EqOnPairs (causalPlusLE (stableGenConeTop d α)) μ (affineGaussian b) := by
    intro μ hμ
    induction α using WithTop.recTopCoe with
    | top =>
      refine (wedge_axis_singular hd hCsym hC hO hI hpt hpsd ⟨projE ⟨0, by omega⟩,
        projE_posSemidef _, fun h => ?_, ?_⟩ μ).1 hμ
      · have := congrArg Matrix.trace h
        rw [projE_trace, trace_zero] at this
        exact one_ne_zero this
      · rw [projE, det_diagonal]
        exact Finset.prod_eq_zero (Finset.mem_univ (⟨1, by omega⟩ : Fin d))
          (by simp [Fin.ext_iff])
    | coe a =>
      have ha : 2 ≤ a := WithTop.coe_le_coe.1 hα
      have ha0 : 0 ≤ a := by linarith
      exact ((wedge_axis_non_gaussian hd hCsym hC hO hI hpt hpsd
        (stableGenCone_det_ne_zero hd1 ha0)).2
        (by rw [stableGenConeTop_coe, coneIndex_stableGenCone hd ha0]; exact ha) μ).1 hμ
  ext m
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨b, hb, h⟩ := hfam μ hμ
    refine ⟨b, hb, ?_⟩
    rw [h (0, 1) ⟨PosSemidef.zero, PosSemidef.one, causalPlusLE_zero_left 1⟩]
    simp [affineGaussian]
  · rintro ⟨b, hb, rfl⟩
    have hν : IsAffineCascadeFamily (affineGaussian (d := d) b) :=
      (affine_rigidity hd _).2 ⟨b, hb, fun _ _ => rfl⟩
    exact ⟨affineGaussian b, gw_family_restrict_of_le subset_rfl
      (fun S S' _ hS' h => causalPlusLE_loewner hpsd hS' h) _ hν, by simp [affineGaussian]⟩

/-- **`thm:wedge-axis`(3)**, the row along the chain, its shape: `𝔉₀` is the set of
rotation-invariant self-decomposable laws other than `δ₀`; `𝔉_β ⊆ 𝔉_α` for `0 ≤ α ≤ β ≤ ∞`, strictly
when `α < β ≤ 2`. Spends A5 at `β = 2` (through (2)(c)) and A3(iii) (the stable laws). -/
theorem wedge_axis_row (hd : 2 ≤ d) :
    rowLaws d 0 = {m : Measure (Rd d) | IsProbabilityMeasure m ∧ IsRotationInvariant m ∧
        IsSelfDecomposable m ∧ m ≠ Measure.dirac 0} ∧
      (∀ α β : WithTop ℝ, 0 ≤ α → α ≤ β → rowLaws d β ⊆ rowLaws d α) ∧
      ∀ α β : WithTop ℝ, 0 ≤ α → α < β → β ≤ 2 → rowLaws d β ⊂ rowLaws d α := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hmono : ∀ α β : WithTop ℝ, 0 ≤ α → α ≤ β → rowLaws d β ⊆ rowLaws d α := by
    rintro α β - hαβ m ⟨μ, hμ, rfl⟩
    exact ⟨μ, gw_family_restrict_of_le subset_rfl
      (fun S S' _ _ h => causalPlusLE_mono (stableGenConeTop_mono hd1 hαβ) h) μ hμ, rfl⟩
  refine ⟨?_, hmono, fun α β hα hαβ hβ2 => ?_⟩
  · /- `𝔉₀`: the ray order. -/
    ext m
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      obtain ⟨hp, hrot, hsd, hne, -⟩ :=
        gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ
      exact ⟨hp, hrot, hsd, hne⟩
    · rintro ⟨hp, hrot, hsd, hne⟩
      haveI := hp
      obtain ⟨μ, hμ, hμ1⟩ := (gw_ray_families_gl_converse m hrot hsd hne).1
      refine ⟨μ, gw_family_restrict_of_le subset_rfl (fun S S' _ _ h => ?_) μ hμ, hμ1⟩
      rcases h with h | h | ⟨h1, h2, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr ((((stable_order_zero hd1).2 S S' h1 h2).1).1 h)
  · /- Strictness, by a stable law of index `γ ∈ [α, β)`. -/
    induction α using WithTop.recTopCoe with
    | top => exact absurd hαβ not_top_lt
    | coe a =>
    induction β using WithTop.recTopCoe with
    | top => exact absurd hβ2 (by simp)
    | coe b =>
    have ha : 0 ≤ a := WithTop.coe_nonneg.1 hα
    have hab : a < b := WithTop.coe_lt_coe.1 hαβ
    have hb2 : b ≤ 2 := WithTop.coe_le_coe.1 hβ2
    obtain ⟨γ, hγ0, hγ2, haγ, hγb⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 2 ∧ a ≤ γ ∧ γ < b := by
      rcases ha.lt_or_eq with ha' | rfl
      · exact ⟨a, ha', by linarith, le_rfl, hab⟩
      · exact ⟨b / 2, by linarith, by linarith, by linarith, by linarith⟩
    obtain ⟨σ, hσ, -⟩ := exists_ellipticalStable hγ0 hγ2 (PosDef.one (n := Fin d))
    have hcase : ∀ c : ℝ, 0 ≤ c → (σ ∈ rowLaws d (c : WithTop ℝ) ↔ c ≤ γ) := by
      intro c hc
      obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 hc
      rw [mem_rowLaws_iff hd1, stableGenConeTop_coe,
        wedge_axis_stable hd hCsym hC hO hI hpt (fun X hX => hX.1)
          (stableGenCone_det_ne_zero hd1 hc) hγ0 hγ2 σ hσ, coneIndex_stableGenCone hd hc]
    refine (ssubset_iff_of_subset (hmono _ _ hα hαβ.le)).2 ⟨σ, (hcase a ha).2 haγ, fun hσb => ?_⟩
    rcases hb2.lt_or_eq with hb2' | rfl
    · exact absurd ((hcase b (by linarith)).1 hσb) (not_le.2 hγb)
    · /- At `β = 2`: `𝔉₂` holds only Gaussian laws. -/
      obtain ⟨μ, hμ, hμσ⟩ := hσb
      obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 (zero_le_two : (0 : ℝ) ≤ 2)
      have h := ((wedge_axis_non_gaussian hd hCsym hC hO hI hpt (fun X hX => hX.1)
        (stableGenCone_det_ne_zero hd1 zero_le_two)).1).1
        ⟨μ, hμ, by rw [hμσ]; exact not_isGaussian_ellipticalStable hd1 hγ0 hγ2 hσ⟩
      rw [coneIndex_stableGenCone hd zero_le_two] at h
      exact lt_irrefl _ h

/-- **`thm:wedge-axis`(3)**, the members: for `0 < α < 2`, `𝔉_α` contains `S_γ(I)`, `0 < γ < 2`, if
and only if `γ ≥ α`, and contains the law `μ_I` of `prop:orbit-step-cone`(1) for every profile whose
dilation ratio has `R(λ) ≥ λ^α` for `λ ≥ 1`; and for `2 ≤ α ≤ ∞`, `𝔉_α` is the set of centred
Gaussian laws with covariance `2bI`, `b > 0`. Spends A3(iii), and A5 for `2 ≤ α < ∞`. -/
theorem wedge_axis_row_members (hd : 2 ≤ d) :
    (∀ α : ℝ, 0 < α → α < 2 → ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ σ : Measure (Rd d),
        IsEllipticalStable γ 1 σ → (σ ∈ rowLaws d (α : WithTop ℝ) ↔ α ≤ γ)) ∧
      (∀ α : ℝ, 0 < α → α < 2 → ∀ K : RadialProfile d,
        (∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam) →
          ∀ μI : Measure (Rd d), IsProfileLaw K μI → μI ∈ rowLaws d (α : WithTop ℝ)) ∧
      ∀ α : WithTop ℝ, 2 ≤ α →
        rowLaws d α = {m : Measure (Rd d) |
          ∃ b : ℝ, 0 < b ∧ m = multivariateGaussian 0 ((2 * b) • (1 : Mat d))} := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨fun α hα0 _ γ hγ0 hγ2 σ hσ => ?_, fun α hα0 hα2 K hR μI hμI => ?_,
    fun α hα => rowLaws_gaussian hd hα⟩
  · obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 hα0.le
    rw [mem_rowLaws_iff hd1, stableGenConeTop_coe,
      wedge_axis_stable hd hCsym hC hO hI hpt (fun X hX => hX.1)
        (stableGenCone_det_ne_zero hd1 hα0.le) hγ0 hγ2 σ hσ, coneIndex_stableGenCone hd hα0.le]
  · obtain ⟨μ, hμ, hμm⟩ := stable_order_gl_row hd hα0 hα2 K hR μI hμI
    refine ⟨μ, gw_family_restrict_of_le subset_rfl
      (fun S S' _ _ h => causalPlusLE_stablePlusLE hd1 hα0 subset_rfl h) μ hμ, ?_⟩
    rw [hμm 1 PosSemidef.one, affineOrbit_one]

end AffineHemigroup
