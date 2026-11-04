/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ConeOrdersClosed
import AffineHemigroup.StableOrderPSD
import AffineHemigroup.KernelsFromOrigin

/-!
# `lem:cone-orders-psd`: a closed order without a cone, and the orders on `PSD(d)`

Blueprint: `blueprint/src/parts/05-wedges.tex`, `lem:cone-orders-psd` (`thm:cone-orders`(3)–(4);
wave 2, group F, Q-0281).

* **(3)** `𝒦 = {I} ∪ {M : λ↑₁(M) ≥ 2}`: closed (the continuity of `λ↑` on `Sym(d)`), a partial
  order (`⟨x, M^{1/2}NM^{1/2}x⟩ ≥ 2|M^{1/2}x|² ≥ 4` for unit `x`; `λ↑₁(M⁻¹) = 1/λ_max(M) ≤ 1/2`),
  and `C(𝒦) = {0}` (`λ↑₁(e^{tX}) = e^{tλ↑₁(X)} < 2` for small `t`). A `{0}`-causal curve has
  derivative `0` almost everywhere, so it is constant (Mathlib's `const_of_ae_hasDerivAt_zero`).
  That no cone generates `≤_𝒦` is read through the geodesic of `thm:cone-orders`(1), which spends
  nothing: every `X ∈ C'` has `e^{tX} ∈ 𝒦`, so `C' ⊆ C(𝒦) = {0}`, and then `I ≤_𝒦 2I` would make
  `I = 2I`. Lean core.
* **(4)** `≼⁺_C` on `PSD(d)`, as `lem:stable-order-psd` treats `≤_α`, with `≼_C` in place of `≼_α`:
  `thm:cone-orders`(1) supplies the order on `PD(d)`, hence ledger A9; the chains on `PD(d)` are
  `lem:path-condition-orders`(c) for `𝒦 = exp C`.
-/

namespace AffineHemigroup

open Matrix Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace MatrixOrder

variable {d : ℕ}

/-! ## Cones with `I`: the rays inside `≼_C` -/

/-- `e^{a I} = e^a I`. -/
theorem mexp_smul_one (a : ℝ) : mexp (a • (1 : Mat d)) = Real.exp a • (1 : Mat d) := by
  have h1 : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
  have := mexp_udiag h1 (fun _ => a)
  rwa [udiag_const h1, udiag_const h1] at this

/-- **The rays lie in `≼_C`** when `I ∈ C`: `Σ ≼_C cΣ` for `c ≥ 1`. -/
theorem causalLE_ray (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C) {S : Mat d}
    (hS : S.PosDef) {c : ℝ} (hc : 1 ≤ c) : causalLE C S (c • S) := by
  have hc0 : 0 < c := by linarith
  rw [(causalLE_iff_expSet hd hCsym hC hO hS (hS.smul hc0)).1]
  refine ⟨Real.log c • (1 : Mat d), hC.2.2.2 _ (Real.log_nonneg hc) _ hI, ?_⟩
  rw [mexp_smul_one, Real.exp_log hc0, relStep_smul, relStep_self hS]

/-! ## Clause (4): `≼⁺_C` on `PSD(d)` -/

section PSD

variable {C : Set (Mat d)}

theorem causalPlusLE_rays (S : Mat d) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c') :
    causalPlusLE C (c • S) (c' • S) := by
  rcases hc.lt_or_eq with hc | rfl
  · refine Or.inr (Or.inl ⟨c' / c, (one_le_div hc).2 hcc', ?_⟩)
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']
  · exact Or.inl (zero_smul _ _)

variable (hd : 1 ≤ d) (hCsym : C ⊆ symSet d) (hC : IsClosedConvexCone C)
  (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
include hd hCsym hC hO

/-- On `PD(d)`, `≼_C` is transitive. -/
theorem causalLE_trans' {S S' S'' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hS'' : S''.PosDef)
    (h : causalLE C S S') (h' : causalLE C S' S'') : causalLE C S S'' := by
  have hord := causalLE_order hd hCsym hC hO
  rw [hord.1 S S' hS hS'] at h
  rw [hord.1 S' S'' hS' hS''] at h'
  rw [hord.1 S S'' hS hS'']
  exact hord.2.2.2.2.1 S S' S'' hS hS' hS'' h h'

include hI in
/-- `≼⁺_C` is transitive on `PSD(d)`. -/
theorem causalPlusLE_trans {S S' S'' : Mat d} (h : causalPlusLE C S S')
    (h' : causalPlusLE C S' S'') : causalPlusLE C S S'' := by
  haveI : NeZero d := ⟨by omega⟩
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · exact Or.inl rfl
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨h1', h2', h'⟩
    · rcases smul_eq_zero.1 h0 with h | h
      · linarith
      · exact Or.inl h
    · exact Or.inr (Or.inl ⟨c' * c, one_le_mul_of_one_le_of_one_le hc' hc, by rw [smul_smul]⟩)
    · have hSpd : S.PosDef := by
        have := h1'.smul (inv_pos.2 (by linarith : (0 : ℝ) < c))
        rwa [smul_smul, inv_mul_cancel₀ (by linarith : c ≠ 0), one_smul] at this
      exact Or.inr (Or.inr ⟨hSpd, h2', causalLE_trans' hd hCsym hC hO hSpd h1' h2'
        (causalLE_ray hd hCsym hC hO hI hSpd hc) h'⟩)
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨-, h2', h'⟩
    · exact absurd h0 (PosDef_ne_zero' h2)
    · have hc0 : (0 : ℝ) < c' := by linarith
      exact Or.inr (Or.inr ⟨h1, h2.smul hc0, causalLE_trans' hd hCsym hC hO h1 h2 (h2.smul hc0) h
        (causalLE_ray hd hCsym hC hO hI h2 hc')⟩)
    · exact Or.inr (Or.inr ⟨h1, h2', causalLE_trans' hd hCsym hC hO h1 h2 h2' h h'⟩)

/-- `≼⁺_C` is `GL(d)`-invariant. -/
theorem causalPlusLE_act {A : Mat d} (hA : A ∈ glSet d) {S S' : Mat d}
    (h : causalPlusLE C S S') : causalPlusLE C (act A S) (act A S') := by
  have hord := causalLE_order hd hCsym hC hO
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · exact Or.inl (by simp [act])
  · exact Or.inr (Or.inl ⟨c, hc, act_smul A c S⟩)
  · have hA1 := (posDef_act_iff hA S).2 h1
    have hA2 := (posDef_act_iff hA S').2 h2
    refine Or.inr (Or.inr ⟨hA1, hA2, ?_⟩)
    rw [hord.1 _ _ hA1 hA2, ← hord.2.2.1 A hA S S' h1 h2, ← hord.1 _ _ h1 h2]
    exact h

include hI in
/-- `≼⁺_C` is antisymmetric on `PSD(d)` when `C ∩ (-C) = {0}`. -/
theorem causalPlusLE_antisymm (hpt : ∀ X ∈ C, -X ∈ C → X = 0) {S S' : Mat d}
    (h : causalPlusLE C S S') (h' : causalPlusLE C S' S) : S = S' := by
  haveI : NeZero d := ⟨by omega⟩
  have hord := causalLE_order hd hCsym hC hO
  have hanti : ∀ T T' : Mat d, T.PosDef → T'.PosDef → causalLE C T T' → causalLE C T' T →
      T = T' := fun T T' hT hT' h1 h2 =>
    (hord.2.2.2.2.2.1.2 hpt) T T' hT hT' ((hord.1 T T' hT hT').1 h1) ((hord.1 T' T hT' hT).1 h2)
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · rcases h' with h0 | ⟨c', hc', hc'e⟩ | ⟨-, h0, -⟩
    · exact h0.symm
    · rcases smul_eq_zero.1 hc'e.symm with h | h
      · linarith
      · exact h.symm
    · exact absurd rfl (PosDef_ne_zero' h0)
  · rcases h' with h0 | ⟨c', hc', hS⟩ | ⟨h1', h2', h'⟩
    · rcases smul_eq_zero.1 h0 with h | h
      · linarith
      · rw [h, smul_zero]
    · rw [smul_smul] at hS
      have h1 : (1 - c' * c) • S = 0 := by rw [sub_smul, one_smul, ← hS, sub_self]
      rcases smul_eq_zero.1 h1 with h | h
      · have : c = 1 := by nlinarith
        rw [this, one_smul]
      · rw [h, smul_zero]
    · exact (hanti _ _ h2' h1' (causalLE_ray hd hCsym hC hO hI h2' hc) h')
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨-, -, h'⟩
    · exact absurd h0 (PosDef_ne_zero' h2)
    · exact (hanti _ _ h2 h1 (causalLE_ray hd hCsym hC hO hI h2 hc') h).symm
    · exact hanti _ _ h1 h2 h h'

/-- **The path condition (P)** for `≼⁺_C`. -/
theorem causalPlusLE_hasPathCondition (hpt : ∀ X ∈ C, -X ∈ C → X = 0) :
    HasPathCondition (causalPlusLE C) := by
  have hord := causalLE_order hd hCsym hC hO
  obtain ⟨hK, -, -⟩ := expSet_props hd hCsym hC hO
  intro S S' hS hS' h
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · refine ⟨fun s => s • S', ⟨by fun_prop, fun s hs => hS'.smul hs.1, fun s hs t _ hst =>
      causalPlusLE_rays S' hs.1 hst, by simp, by simp⟩⟩
  · refine ⟨fun s => (1 + s * (c - 1)) • S, ⟨by fun_prop, fun s hs => hS.smul (by nlinarith [hs.1]),
      fun s hs t _ hst => causalPlusLE_rays S (by nlinarith [hs.1]) (by nlinarith), by simp,
      by simp⟩⟩
  · have hpow : ∀ M ∈ expSet C, ∀ τ ∈ Icc (0 : ℝ) 1, mrpow M τ ∈ expSet C := by
      rintro M ⟨X, hX, rfl⟩ τ hτ
      refine ⟨τ • X, hC.2.2.2 τ hτ.1 X hX, ?_⟩
      rw [mrpow_eq_mexp (posDef_mexp (hCsym hX)), mlog_mexp (isHermitian_of_isSymm (hCsym hX))]
    have hpo : IsPartialOrderOn (pdSet d) (stepLE (expSet C)) :=
      ⟨fun T hT => hord.2.2.2.1 T hT,
        fun T hT T' hT' h1 h2 => (hord.2.2.2.2.2.1.2 hpt) T T' hT hT' h1 h2,
        fun T hT T' hT' T'' hT'' h1 h2 => hord.2.2.2.2.1 T T' T'' hT hT' hT'' h1 h2⟩
    have hch := chain_stepSet (expSet C) hK hpow hpo S S' ((hord.1 S S' h1 h2).1 h)
    refine ⟨_, ⟨hch.continuousOn, fun s hs => (hch.mem s hs).posSemidef,
      fun s hs t ht hst => ?_, hch.start, hch.finish⟩⟩
    have hs' : (stepGeodesic S S' s).PosDef := hch.mem s hs
    have ht' := hch.mem t ht
    exact Or.inr (Or.inr ⟨hs', ht', (hord.1 _ _ hs' ht').2 (hch.mono s hs t ht hst)⟩)

end PSD

/-- `e^X - I ⪰ 0` iff `X ⪰ 0`, for symmetric `X`. -/
theorem mexp_sub_one_posSemidef_iff {X : Mat d} (hX : X.IsSymm) :
    (mexp X - 1).PosSemidef ↔ X.PosSemidef := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hX)
  have he : mexp X - 1 = udiag V (fun i => Real.exp (eigUp X i) - 1) := by
    conv_lhs => rw [hXV]
    rw [mexp_udiag hV, ← udiag_one hV, udiag_sub]
    rfl
  rw [he, udiag_posSemidef_iff hV]
  conv_rhs => rw [hXV, udiag_posSemidef_iff hV]
  refine forall_congr' fun i => ?_
  rw [sub_nonneg, Real.one_le_exp_iff]

/-- **`lem:cone-orders-psd`** (`thm:cone-orders`(4)), on `PSD(d)`: for `I ∈ C` and
`C ∩ (-C) = {0}`, `≼⁺_C` is a `GL(d)`-invariant partial order on `PSD(d)` containing the rays,
every pair is joined by a chain (the path condition (P)), and `(G, ≼⁺_C)` is a wedge datum for
every closed subgroup `G` of `GL(d)` containing the dilations; it is contained in the Loewner order
if and only if `C ⊆ PSD(d)`. -/
theorem causalPlus_wedge (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) :
    IsWedgeDatum (glSet d) (causalPlusLE C) ∧ HasPathCondition (causalPlusLE C) ∧
      (∀ G : Set (Mat d), IsClosedSubgroupGL G → (∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G) →
        IsWedgeDatum G (causalPlusLE C)) ∧
      ((∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → causalPlusLE C S S' → loewnerLE S S') ↔
        C ⊆ psdSet d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hwedge : ∀ G : Set (Mat d), IsClosedSubgroupGL G → (∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G) →
      IsWedgeDatum G (causalPlusLE C) := fun G hG hdil =>
    ⟨hG, hdil, fun S _ => Or.inr (Or.inl ⟨1, le_rfl, (one_smul ℝ S).symm⟩),
      fun S S' _ _ h h' => causalPlusLE_antisymm hd hCsym hC hO hI hpt h h',
      fun S S' S'' _ _ _ h h' => causalPlusLE_trans hd hCsym hC hO hI h h',
      fun A hA S S' _ _ h => causalPlusLE_act hd hCsym hC hO (hG.subset_gl hA) h,
      fun S _ c c' hc hcc' => causalPlusLE_rays S hc hcc'⟩
  refine ⟨hwedge _ glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2,
    causalPlusLE_hasPathCondition hd hCsym hC hO hpt, hwedge, ⟨fun h X hX => ?_, fun hCp => ?_⟩⟩
  · have hXs : X.IsSymm := hCsym hX
    have hle := h 1 (mexp X) Matrix.PosSemidef.one (posDef_mexp hXs).posSemidef
      (Or.inr (Or.inr ⟨Matrix.PosDef.one, posDef_mexp hXs,
        (causalLE_iff_expSet hd hCsym hC hO Matrix.PosDef.one (posDef_mexp hXs)).1.2
          (by rw [relStep_one_left]; exact ⟨X, hX, rfl⟩)⟩))
    exact (mexp_sub_one_posSemidef_iff hXs).1 hle
  · rintro S S' hS hS' (rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩)
    · simpa [loewnerLE] using hS'
    · unfold loewnerLE
      rw [show c • S - S = (c - 1) • S by rw [sub_smul, one_smul]]
      exact hS.smul (by linarith)
    · obtain ⟨X, hX, hMX⟩ := (causalLE_iff_expSet hd hCsym hC hO h1 h2).1.1 h
      unfold loewnerLE
      rw [← posSemidef_relStep_iff h1, relStep_sub, relStep_self h1, hMX]
      exact (mexp_sub_one_posSemidef_iff (hCsym hX)).2 (hCp hX)

/-! ## The ray order -/

/-- `{cI : c ≥ 0}` is an `O(d)`-invariant closed convex cone in `Sym(d)` containing `I`. -/
theorem rayCone_props (hd : 1 ≤ d) :
    let C₀ : Set (Mat d) := {X | ∃ c : ℝ, 0 ≤ c ∧ X = c • 1}
    C₀ ⊆ symSet d ∧ IsClosedConvexCone C₀ ∧ IsOrthInvariant C₀ ∧ (1 : Mat d) ∈ C₀ ∧
      ∀ X ∈ C₀, -X ∈ C₀ → X = 0 := by
  intro C₀
  have i0 : Fin d := ⟨0, by omega⟩
  have hchar : C₀ = {X | X = X i0 i0 • (1 : Mat d)} ∩ {X | 0 ≤ X i0 i0} := by
    ext X
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩ <;> simp [hc]
    · rintro ⟨h1, h2⟩
      exact ⟨X i0 i0, h2, h1⟩
  refine ⟨?_, ⟨?_, ?_, ⟨0, le_rfl, (zero_smul _ _).symm⟩, ?_⟩, ?_, ⟨1, zero_le_one,
    (one_smul _ _).symm⟩, ?_⟩
  · rintro X ⟨c, -, rfl⟩
    change (c • (1 : Mat d))ᵀ = c • 1
    rw [transpose_smul, transpose_one]
  · rw [hchar]
    refine IsClosed.inter (isClosed_eq continuous_id ?_) (isClosed_le continuous_const ?_)
    · exact (continuous_apply_apply i0 i0).smul continuous_const
    · exact continuous_apply_apply i0 i0
  · rintro X ⟨c, hc, rfl⟩ Y ⟨c', hc', rfl⟩ a b ha hb _
    exact ⟨a * c + b * c', by positivity, by rw [smul_smul, smul_smul, add_smul]⟩
  · rintro c hc X ⟨c', hc', rfl⟩
    exact ⟨c * c', mul_nonneg hc hc', by rw [smul_smul]⟩
  · rintro Q hQ X ⟨c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, orth_mul_transpose hQ]
  · rintro X ⟨c, hc, rfl⟩ ⟨c', hc', hneg⟩
    have h1 : (c + c') • (1 : Mat d) = 0 := by rw [add_smul, ← hneg, add_neg_cancel]
    have hcc : c + c' = 0 := by
      have := congrFun (congrFun h1 i0) i0
      simpa using this
    have : c = 0 := by linarith
    rw [this, zero_smul]

/-- **`lem:cone-orders-psd`** (`thm:cone-orders`(4)), the last sentence: for `C = {cI : c ≥ 0}`,
`≼⁺_C` is the ray order. -/
theorem causalPlus_ray (hd : 1 ≤ d) :
    ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef →
      (causalPlusLE {X : Mat d | ∃ c : ℝ, 0 ≤ c ∧ X = c • 1} S S' ↔ rayLE S S') := by
  obtain ⟨hCsym, hC, hO, -, -⟩ := rayCone_props (d := d) hd
  intro S S' _ _
  constructor
  · rintro (h | h | ⟨h1, h2, h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨X, ⟨c, hc, rfl⟩, hMX⟩ := (causalLE_iff_expSet hd hCsym hC hO h1 h2).1.1 h
      refine Or.inr ⟨Real.exp c, Real.one_le_exp_iff.2 hc, ?_⟩
      rw [mexp_smul_one] at hMX
      rw [← msqrt_mul_relStep h1 S', hMX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        msqrt_mul_self h1.posSemidef]
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ## Clause (3): a closed order without a cone -/

/-- A constant curve is `C`-causal when `0 ∈ C`. -/
theorem isCausalCurve_const {C : Set (Mat d)} (h0 : (0 : Mat d) ∈ C) {S : Mat d}
    (hS : S.PosDef) : IsCausalCurve C (fun _ => S) := by
  refine ⟨fun _ _ => hS, fun i j => ?_, Eventually.of_forall fun t => ?_⟩
  · exact (LipschitzWith.const (S i j)).lipschitzOnWith.absolutelyContinuousOnInterval
  · have : mderiv (fun _ : ℝ => S) t = 0 := by
      ext i j
      simp [mderiv]
    rw [this, show relStep S 0 = 0 by simp [relStep]]
    exact h0

/-- **A `{0}`-causal curve is constant**: its derivative vanishes almost everywhere. -/
theorem IsCausalCurve.eq_of_zero {γ : ℝ → Mat d} (hγ : IsCausalCurve {0} γ) : γ 0 = γ 1 := by
  ext i j
  have hcaus : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → relStep (γ s) (mderiv γ s) ∈ ({0} : Set (Mat d)) :=
    (ae_restrict_iff' measurableSet_Icc).1 hγ.causal
  have hae : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (fun t => γ t i j) 0 x := by
    filter_upwards [(hγ.absolutelyContinuous i j).ae_differentiableAt, hcaus] with s hs1 hs2 hsI
    have hsI' : s ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at hsI
    have hzero : mderiv γ s = 0 := by
      have h : relStep (γ s) (mderiv γ s) = relStep (γ s) 0 := by
        rw [Set.mem_singleton_iff.1 (hs2 hsI')]
        simp [relStep]
      exact relStep_injective (hγ.mem_pd s hsI') h
    have hder := (hs1 hsI).hasDerivAt
    have : deriv (fun t => γ t i j) s = 0 := by
      have := congrFun (congrFun hzero i) j
      simpa [mderiv] using this
    rwa [this] at hder
  obtain ⟨c, hc⟩ := (hγ.absolutelyContinuous i j).const_of_ae_hasDerivAt_zero hae
  rw [hc 0 (by simp), hc 1 (by simp)]

/-- **`≼_{{0}}` is equality** on `PD(d)`. -/
theorem causalLE_zero_iff {S S' : Mat d} (hS : S.PosDef) :
    causalLE ({0} : Set (Mat d)) S S' ↔ S = S' := by
  constructor
  · rintro ⟨γ, hγ, rfl, rfl⟩
    exact hγ.eq_of_zero
  · rintro rfl
    exact ⟨fun _ => S, isCausalCurve_const (C := {0}) (Set.mem_singleton 0) hS, rfl, rfl⟩

/-- `λ↑(cI) = c`. -/
theorem eigUp_smul_one (c : ℝ) : eigUp (c • (1 : Mat d)) = fun _ => c := by
  rw [smul_one_eq_diagonal, eigUp_diagonal]
  exact sortUp_of_monotone fun _ _ _ => le_rfl

/-- **`lem:cone-orders-psd`** (`thm:cone-orders`(3)), a closed order without a cone:
`𝒦 := {I} ∪ {M ∈ PD(d) : λ↑₁(M) ≥ 2}` is a closed step set, `≤_𝒦` is a partial order, and
`C(𝒦) = {0}`, so that `≼_{C(𝒦)}` is equality; hence `≤_𝒦` is `≼_{C'}` for no cone `C'`. -/
theorem closed_order_without_cone (hd : 1 ≤ d) :
    let K : Set (Mat d) := {1} ∪ {M | M.PosDef ∧ 2 ≤ eigUp M ⟨0, by omega⟩}
    IsStepSet K ∧ closure K ∩ pdSet d ⊆ K ∧ IsPartialOrderOn (pdSet d) (stepLE K) ∧
      infCone K = {0} ∧
      (∀ S S' : Mat d, S.PosDef → S'.PosDef → (causalLE (infCone K) S S' ↔ S = S')) ∧
      ¬ ∃ C' : Set (Mat d), C' ⊆ symSet d ∧ IsClosedConvexCone C' ∧ IsOrthInvariant C' ∧
        ∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ causalLE C' S S') := by
  intro K
  haveI : NeZero d := ⟨by omega⟩
  set i0 : Fin d := ⟨0, by omega⟩
  have hi0 : i0 = 0 := Fin.ext (by simp [i0])
  have hlam : ∀ {M : Mat d}, M.IsHermitian → lamMin M = eigUp M i0 := fun hM => by
    rw [hi0]; exact lamMin_eq_eigUp_zero hM
  have hKpd : K ⊆ pdSet d := by
    rintro M (hM | hM)
    · rw [Set.mem_singleton_iff.1 hM]; exact Matrix.PosDef.one
    · exact hM.1
  have hK : IsStepSet K := by
    refine ⟨hKpd, fun M hM Q hQ => ?_⟩
    rcases hM with hM | ⟨hMpd, hM2⟩
    · left
      rw [Set.mem_singleton_iff.1 hM, Matrix.mul_one, orth_mul_transpose hQ]
      rfl
    · right
      refine ⟨?_, by rwa [eigUp_conj_orth (orth_mul_transpose hQ)]⟩
      have := (posDef_act_iff (orthSet_subset_glSet hQ) M).2 hMpd
      rwa [act] at this
  have h1K : (1 : Mat d) ∈ K := Or.inl rfl
  -- products stay in `K`
  have hprod : ∀ M ∈ K, ∀ N ∈ K, msqrt M * N * msqrt M ∈ K := by
    intro M hM N hN
    rcases hM with hM | ⟨hMpd, hM2⟩
    · rw [Set.mem_singleton_iff.1 hM, msqrt, CFC.sqrt_one, Matrix.one_mul, Matrix.mul_one]
      exact hN
    rcases hN with hN | ⟨hNpd, hN2⟩
    · rw [Set.mem_singleton_iff.1 hN, Matrix.mul_one, msqrt_mul_self hMpd.posSemidef]
      exact Or.inr ⟨hMpd, hM2⟩
    · have hP := posDef_msqrt_conj hMpd hNpd
      refine Or.inr ⟨hP, ?_⟩
      rw [← hlam hP.isHermitian]
      refine le_trans (by norm_num : (2 : ℝ) ≤ 4)
        ((le_lamMin_iff hP.isHermitian 4).2 fun x hx => ?_)
      have hq : quad (msqrt M * N * msqrt M) x = quad N (lin (msqrt M) x) := by
        have := quad_act (msqrt M) N x
        rwa [act, msqrt_transpose] at this
      rw [hq]
      have h1 := lamMin_mul_norm_sq_le hNpd.isHermitian (lin (msqrt M) x)
      have h2 := lamMin_mul_norm_sq_le hMpd.isHermitian x
      rw [norm_sq_lin_msqrt hMpd.posSemidef] at h1
      rw [hx, one_pow, mul_one] at h2
      rw [← hlam hNpd.isHermitian] at hN2
      rw [← hlam hMpd.isHermitian] at hM2
      change 4 ≤ ⟪lin (msqrt M) x, lin N (lin (msqrt M) x)⟫
      have h3 : 0 ≤ quad M x := le_trans (by linarith) h2
      change lamMin M ≤ quad M x at h2
      nlinarith
  have hpo : IsPartialOrderOn (pdSet d) (stepLE K) := by
    have hprops := stepLE_order_props hd hK
    have htrans := ((stepLE_trans_tfae hd hK).out 1 0).1 hprod
    refine ⟨fun S hS => hprops.1.2 h1K S hS, fun S hS S' hS' h h' =>
      hprops.2.1.2 ?_ S S' hS hS' h h', fun S hS S' hS' S'' hS'' h h' =>
      htrans S S' S'' hS hS' hS'' h h'⟩
    intro M hM hMi
    rcases hM with hM | ⟨hMpd, hM2⟩
    · exact Set.mem_singleton_iff.1 hM
    rcases hMi with hMi | ⟨hMipd, hMi2⟩
    · have hMi' := Set.mem_singleton_iff.1 hMi
      have hU : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hMpd.isUnit
      calc M = M⁻¹⁻¹ := (nonsing_inv_nonsing_inv M hU).symm
        _ = 1 := by rw [hMi', inv_one]
    · exfalso
      have hmax := lamMax_eq_inv_lamMin_inv hMpd
      rw [hlam hMipd.isHermitian] at hmax
      have hle : lamMin M ≤ lamMax M := by
        obtain ⟨hmono, -, h0, hl⟩ := eigUp_spec hMpd.isHermitian
        rw [← h0, ← hl]
        exact hmono (Fin.zero_le _)
      rw [hlam hMpd.isHermitian, hmax] at hle
      have h1 : (eigUp M⁻¹ i0)⁻¹ ≤ 1 / 2 := by
        rw [one_div]
        exact inv_anti₀ (by norm_num) hMi2
      linarith
  have hclosed : closure K ∩ pdSet d ⊆ K := by
    rintro M ⟨hcl, hM⟩
    rw [closure_union, closure_singleton] at hcl
    rcases hcl with h | h
    · exact Or.inl h
    · obtain ⟨Ms, hMs, hlim⟩ := mem_closure_iff_seq_limit.1 h
      have he := tendsto_eigUp (fun n => isSymm_of_isHermitian (hMs n).1.isHermitian)
        (isSymm_of_isHermitian hM.isHermitian) hlim
      have he0 := ((continuous_apply i0).tendsto _).comp he
      exact Or.inr ⟨hM, ge_of_tendsto he0 (Eventually.of_forall fun n => (hMs n).2)⟩
  have hinf : infCone K = {0} := by
    ext X
    constructor
    · rintro ⟨hXs, hX⟩
      by_contra hX0
      have hX0' : X ≠ 0 := hX0
      set x0 := eigUp X i0
      set t := Real.log 2 / (|x0| + 1)
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have ht : 0 < t := div_pos hl2 (by positivity)
      have htx : t * x0 < Real.log 2 := by
        have h1 : t * x0 ≤ t * |x0| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.le
        have h2 : t * |x0| < t * (|x0| + 1) := by nlinarith
        have h3 : t * (|x0| + 1) = Real.log 2 := by
          simp only [t]; field_simp
        linarith
      have hmem := hX t ht.le
      have htXs : (t • X).IsSymm := hXs.smul t
      have heig : eigUp (mexp (t • X)) i0 = Real.exp (t * x0) := by
        rw [eigUp_mexp (isHermitian_of_isSymm htXs), eigUp_smul ht.le (isHermitian_of_isSymm hXs)]
        rfl
      rcases hmem with h1 | ⟨-, h2⟩
      · have := eq_zero_of_mexp_eq_one htXs (Set.mem_singleton_iff.1 h1)
        rcases smul_eq_zero.1 this with h | h
        · exact ht.ne' h
        · exact hX0' h
      · rw [heig] at h2
        have : Real.exp (t * x0) < 2 := by
          calc Real.exp (t * x0) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 htx
            _ = 2 := Real.exp_log (by norm_num)
        linarith
    · intro hX
      rw [Set.mem_singleton_iff.1 hX]
      exact ⟨isSymm_zero, fun t _ => by rw [smul_zero, mexp_zero]; exact h1K⟩
  refine ⟨hK, hclosed, hpo, hinf, fun S S' hS _ => by rw [hinf]; exact causalLE_zero_iff hS, ?_⟩
  rintro ⟨C', hC'sym, hC', hO', hiff⟩
  -- every `X ∈ C'` has `e^{tX} ∈ K`, through the geodesic
  have hsub : C' ⊆ infCone K := by
    intro X hX
    refine ⟨hC'sym hX, fun t ht => ?_⟩
    have htX : t • X ∈ C' := hC'.2.2.2 t ht X hX
    have hpd := posDef_mexp (hC'sym htX)
    have hc : causalLE C' 1 (mexp (t • X)) := by
      obtain ⟨hcurve, h0, h1⟩ := stepGeodesic_causal hC'sym hO' Matrix.PosDef.one hpd
        (by rw [relStep_one_left]; exact ⟨t • X, htX, rfl⟩)
      exact ⟨_, hcurve, h0, h1⟩
    have := ((hiff 1 _ Matrix.PosDef.one hpd).2 hc).2.2
    rwa [relStep_one_left] at this
  have hC'0 : C' = {0} := by
    refine Set.Subset.antisymm (hinf ▸ hsub) ?_
    rintro X hX
    rw [Set.mem_singleton_iff.1 hX]
    exact hC'.2.2.1
  have h2K : (2 : ℝ) • (1 : Mat d) ∈ K := by
    refine Or.inr ⟨Matrix.PosDef.one.smul (by norm_num), ?_⟩
    rw [eigUp_smul_one]
  have h2pd : ((2 : ℝ) • (1 : Mat d)).PosDef := Matrix.PosDef.one.smul (by norm_num)
  have hstep : stepLE K 1 ((2 : ℝ) • (1 : Mat d)) :=
    ⟨Matrix.PosDef.one, h2pd, by rw [relStep_one_left]; exact h2K⟩
  have := (hiff 1 _ Matrix.PosDef.one h2pd).1 hstep
  rw [hC'0, causalLE_zero_iff Matrix.PosDef.one] at this
  have h11 := congrFun (congrFun this i0) i0
  simp at h11

end AffineHemigroup
