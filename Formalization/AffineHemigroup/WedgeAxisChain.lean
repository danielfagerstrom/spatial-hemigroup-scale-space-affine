/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ConeOrdersPSD
import AffineHemigroup.StableOrderGenerated
import AffineHemigroup.Rigidity
import AffineHemigroup.RankDeficient
import AffineHemigroup.RayFamilies
import AffineHemigroup.SimilarityStable
import AffineHemigroup.Defs.Table

/-!
# `lem:wedge-axis-chain` — the chain of cones, and the cones that carry only the Gaussian

Blueprint: `blueprint/src/parts/05-table.tex`, `lem:wedge-axis-chain` (`thm:wedge-axis`(1), (2)(a)
and (2)(b); Q-0281 wave 2, group H). Lean core only.

## The entry-free route (the author's decision on W2F-1)

Nothing here reads `thm:cone-orders`(1)–(2) or `lem:cone-orders-psd`, whose order properties spend
ledger A9 (`gelfand_naimark_logMajorized`). What the proofs need of `≼_C` and `≼⁺_C` is proved here
from causal curves directly:

* **the geodesic** (`stepGeodesic_causal`, Lean core): `X ∈ C` gives `I ≼_C e^X`, and `I ∈ C` gives
  the rays;
* **transitivity**: two `C`-causal curves run one after the other at double speed form a `C`-causal
  curve (`IsCausalCurve.concatHalf`); absolute continuity of the concatenation is read through the
  fundamental theorem of calculus for absolutely continuous functions (Mathlib's
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`);
* **`GL(d)`-invariance**: `A γ Aᵀ` is `C`-causal when `γ` is, its relative derivative being an
  orthogonal conjugate of `γ`'s (`IsCausalCurve.act`);
* **inclusion in the Loewner order** for `C ⊆ PSD(d)`: a `PSD(d)`-causal curve is Loewner-monotone
  (`IsCausalCurve.loewnerLE_psd`, `prop:stable-order-generated`'s fact (a));
* **the stable orders** `≼_α` through `prop:stable-order-generated`(1) (Lean core).

Antisymmetry of `≼⁺_C`, the one order property that needs the entry, is never used.

## The family toolkit

`gw_family_restrict` (`lem:gw-kernels-from-origin`(1)) carries two wedge-datum hypotheses it does
not read; for `≼⁺_C` the datum would be `lem:cone-orders-psd`, which spends A9. The restriction is
restated here without them (`gw_family_restrict_of_le`). A family that agrees on the pairs with a
family is one, for a relation that is reflexive, transitive and `G`-invariant on `PSD(d)`
(`IsGWCascadeFamily.of_eqOnPairs`). The kernels from the origin of a `(GL(d), ≼)`-family, for any
`≼` containing the rays, are read through `prop:gw-ray-families`(3) after restriction to the rays,
with `μ̂_Σ(ω) = e^{-g(⟨ω,Σω⟩)}` (`gl_kernels_of_rays`), the ray-family form of
`lem:affine-reduction`.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## Absolute continuity of a concatenation -/

/-- Absolute continuity on `[a, b]` reads only the values on `[a, b]`. -/
theorem AbsolutelyContinuousOnInterval.congr_uIcc {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (h : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have := H E hE hlen
  convert this using 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h (hE.1 i hi).1, h (hE.1 i hi).2]

/-- **Two curves on `[0, 1]` run one after the other at double speed**: `f₁(2t)` for `t ≤ 1/2`,
`f₂(2t - 1)` after. -/
noncomputable def concatHalf {X : Type*} (f₁ f₂ : ℝ → X) (t : ℝ) : X :=
  if t ≤ 1 / 2 then f₁ (2 * t) else f₂ (2 * t - 1)

/-- **The concatenation of absolutely continuous functions is absolutely continuous**: it is
`f₁(0)` plus the integral of the derivatives run at double speed. -/
theorem absolutelyContinuousOnInterval_concatHalf {f₁ f₂ : ℝ → ℝ}
    (h₁ : AbsolutelyContinuousOnInterval f₁ 0 1) (h₂ : AbsolutelyContinuousOnInterval f₂ 0 1)
    (h12 : f₁ 1 = f₂ 0) : AbsolutelyContinuousOnInterval (concatHalf f₁ f₂) 0 1 := by
  set k : ℝ → ℝ := fun s =>
    if s ≤ 1 / 2 then 2 * deriv f₁ (2 * s) else 2 * deriv f₂ (2 * s - 1) with hk
  have hi₁ : IntervalIntegrable (fun s => 2 * deriv f₁ (2 * s)) volume 0 (1 / 2) := by
    have := (h₁.intervalIntegrable_deriv.comp_mul_left (c := 2)).const_mul 2
    simpa using this
  have hi₂ : IntervalIntegrable (fun s => 2 * deriv f₂ (2 * s - 1)) volume (1 / 2) 1 := by
    have h := (h₂.intervalIntegrable_deriv.comp_sub_right 1).comp_mul_left (c := 2)
    have := h.const_mul 2
    norm_num at this
    exact this
  have hk₁ : IntervalIntegrable k volume 0 (1 / 2) := by
    refine (intervalIntegrable_congr fun s hs => ?_).1 hi₁
    rw [uIoc_of_le (by norm_num)] at hs
    rw [hk]; dsimp only; rw [if_pos hs.2]
  have hk₂ : IntervalIntegrable k volume (1 / 2) 1 := by
    refine (intervalIntegrable_congr fun s hs => ?_).1 hi₂
    rw [uIoc_of_le (by norm_num)] at hs
    rw [hk]; dsimp only; rw [if_neg (not_le.2 hs.1)]
  have hk01 : IntervalIntegrable k volume 0 1 := hk₁.trans hk₂
  /- The integral of `k` up to `t ≤ 1/2`. -/
  have hfirst : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∫ s in (0 : ℝ)..t, k s = f₁ (2 * t) - f₁ 0 := by
    intro t ht
    have hc : ∫ s in (0 : ℝ)..t, k s = ∫ s in (0 : ℝ)..t, 2 * deriv f₁ (2 * s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      rw [hk]; dsimp only; rw [if_pos (hs.2.trans ht.2)]
    rw [hc, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun s => deriv f₁ s) two_ne_zero, mul_zero,
      ((h₁.mono (by
        rw [uIcc_of_le (by linarith [ht.1]), uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (by linarith [ht.2]))).integral_deriv_eq_sub)]
    simp
  have hrep : EqOn (fun t => f₁ 0 + ∫ s in (0 : ℝ)..t, k s) (concatHalf f₁ f₂) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simp only [concatHalf]
    split_ifs with h
    · rw [hfirst t ⟨ht.1, h⟩]; ring
    · push Not at h
      have hk2t : IntervalIntegrable k volume (1 / 2) t :=
        hk₂.mono_set (by
          rw [uIcc_of_le h.le, uIcc_of_le (by norm_num)]
          exact Icc_subset_Icc le_rfl ht.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals hk₁ hk2t,
        hfirst (1 / 2) ⟨by norm_num, le_rfl⟩]
      have hc : ∫ s in (1 / 2 : ℝ)..t, k s = ∫ s in (1 / 2 : ℝ)..t, 2 * deriv f₂ (2 * s - 1) := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
        rw [uIoc_of_le h.le] at hs
        rw [hk]; dsimp only; rw [if_neg (not_le.2 hs.1)]
      rw [hc, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_sub (fun s => deriv f₂ s) two_ne_zero,
        ((h₂.mono (by
          rw [uIcc_of_le (by linarith : (2 : ℝ) * (1 / 2) - 1 ≤ 2 * t - 1), uIcc_of_le zero_le_one]
          exact Icc_subset_Icc (by norm_num) (by linarith [ht.2]))).integral_deriv_eq_sub)]
      norm_num
      rw [h12]
      ring
  have hac : AbsolutelyContinuousOnInterval (fun t => f₁ 0 + ∫ s in (0 : ℝ)..t, k s) 0 1 :=
    ((LipschitzWith.const (f₁ 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hk01.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  exact AbsolutelyContinuousOnInterval.congr_uIcc hac hrep


/-! ## Causal curves: concatenation, transitivity, invariance, the rays -/

/-- A null set pulled back along `t ↦ 2t`, read on the almost-everywhere statements. -/
theorem ae_comp_two_mul {p : ℝ → Prop} (h : ∀ᵐ s : ℝ, p s) : ∀ᵐ t : ℝ, p (2 * t) := by
  rw [ae_iff] at h ⊢
  have hset : {t : ℝ | ¬p (2 * t)} = (fun t : ℝ => 2 * t) ⁻¹' {s | ¬p s} := rfl
  rw [hset, Real.volume_preimage_mul_left two_ne_zero, h, mul_zero]

/-- A null set pulled back along `t ↦ 2t - 1`. -/
theorem ae_comp_two_mul_sub_one {p : ℝ → Prop} (h : ∀ᵐ s : ℝ, p s) :
    ∀ᵐ t : ℝ, p (2 * t - 1) := by
  have h' : ∀ᵐ s : ℝ, p (s - 1) := by
    rw [ae_iff] at h ⊢
    have hset : {s : ℝ | ¬p (s - 1)} = (fun s : ℝ => s + (-1)) ⁻¹' {s | ¬p s} := by
      ext s; simp [sub_eq_add_neg]
    rw [hset, measure_preimage_add_right, h]
  exact ae_comp_two_mul h'

/-- **The concatenation of two `C`-causal curves is `C`-causal**, for a cone `C` closed under
doubling: on each half the curve is one of the two, run at double speed, so its relative
derivative is twice theirs. -/
theorem IsCausalCurve.concatHalf {C : Set (Mat d)} (hC2 : ∀ X ∈ C, (2 : ℝ) • X ∈ C)
    {γ₁ γ₂ : ℝ → Mat d} (h₁ : IsCausalCurve C γ₁) (h₂ : IsCausalCurve C γ₂) (h12 : γ₁ 1 = γ₂ 0) :
    IsCausalCurve C (AffineHemigroup.concatHalf γ₁ γ₂) := by
  refine ⟨fun t ht => ?_, fun i j => ?_, ?_⟩
  · unfold AffineHemigroup.concatHalf
    split_ifs with h
    · exact h₁.mem_pd _ ⟨by linarith [ht.1], by linarith⟩
    · push Not at h
      exact h₂.mem_pd _ ⟨by linarith, by linarith [ht.2]⟩
  · have he : (fun t => AffineHemigroup.concatHalf γ₁ γ₂ t i j) =
        AffineHemigroup.concatHalf (fun s => γ₁ s i j) (fun s => γ₂ s i j) := by
      funext t
      unfold AffineHemigroup.concatHalf
      split_ifs <;> rfl
    rw [he]
    exact absolutelyContinuousOnInterval_concatHalf (h₁.absolutelyContinuous i j)
      (h₂.absolutelyContinuous i j) (by rw [h12])
  · rw [ae_restrict_iff' measurableSet_Icc]
    have A₁ := (ae_restrict_iff' measurableSet_Icc).1 h₁.causal
    have A₂ := (ae_restrict_iff' measurableSet_Icc).1 h₂.causal
    have B₁ := ae_comp_two_mul A₁
    have B₂ := ae_comp_two_mul_sub_one A₂
    have B₃ : ∀ᵐ t : ℝ, t ≠ 1 / 2 := by
      rw [ae_iff]
      simp
    filter_upwards [B₁, B₂, B₃] with t hb₁ hb₂ hb₃ htI
    rcases lt_or_gt_of_ne hb₃ with hlt | hgt
    · have heq : ∀ i j, (fun s => AffineHemigroup.concatHalf γ₁ γ₂ s i j) =ᶠ[𝓝 t]
          (fun s => γ₁ (2 * s) i j) := by
        intro i j
        filter_upwards [Iio_mem_nhds hlt] with s hs
        simp only [AffineHemigroup.concatHalf, if_pos (le_of_lt (Set.mem_Iio.1 hs))]
      have hm : mderiv (AffineHemigroup.concatHalf γ₁ γ₂) t = (2 : ℝ) • mderiv γ₁ (2 * t) := by
        ext i j
        simp only [mderiv, of_apply, Matrix.smul_apply, smul_eq_mul]
        rw [(heq i j).deriv_eq]
        exact deriv_comp_mul_left (f := fun u => γ₁ u i j) (c := (2 : ℝ)) (x := t)
      have hc : AffineHemigroup.concatHalf γ₁ γ₂ t = γ₁ (2 * t) := if_pos hlt.le
      rw [hm, hc, relStep_smul]
      exact hC2 _ (hb₁ ⟨by linarith [htI.1], by linarith⟩)
    · have heq : ∀ i j, (fun s => AffineHemigroup.concatHalf γ₁ γ₂ s i j) =ᶠ[𝓝 t]
          (fun s => γ₂ (2 * s - 1) i j) := by
        intro i j
        filter_upwards [Ioi_mem_nhds hgt] with s hs
        simp only [AffineHemigroup.concatHalf, if_neg (not_le.2 (Set.mem_Ioi.1 hs))]
      have hm : mderiv (AffineHemigroup.concatHalf γ₁ γ₂) t =
          (2 : ℝ) • mderiv γ₂ (2 * t - 1) := by
        ext i j
        simp only [mderiv, of_apply, Matrix.smul_apply, smul_eq_mul]
        rw [(heq i j).deriv_eq]
        have h1 := deriv_comp_mul_left (f := fun u => γ₂ (u - 1) i j) (c := (2 : ℝ)) (x := t)
        have h2 := deriv_comp_sub_const (f := fun u => γ₂ u i j) (a := (1 : ℝ)) (x := 2 * t)
        simp only [smul_eq_mul] at h1
        rw [h1, h2]
      have hc : AffineHemigroup.concatHalf γ₁ γ₂ t = γ₂ (2 * t - 1) := if_neg (not_le.2 hgt)
      rw [hm, hc, relStep_smul]
      exact hC2 _ (hb₂ ⟨by linarith, by linarith [htI.2]⟩)

/-- **`≼_C` is transitive** for a cone `C` closed under doubling (entry-free: concatenation). -/
theorem causalLE_trans_of_two_smul {C : Set (Mat d)} (hC2 : ∀ X ∈ C, (2 : ℝ) • X ∈ C)
    {S S' S'' : Mat d} (h : causalLE C S S') (h' : causalLE C S' S'') : causalLE C S S'' := by
  obtain ⟨γ₁, hγ₁, h0, h1⟩ := h
  obtain ⟨γ₂, hγ₂, h0', h1'⟩ := h'
  refine ⟨AffineHemigroup.concatHalf γ₁ γ₂, hγ₁.concatHalf hC2 hγ₂ (h1.trans h0'.symm), ?_, ?_⟩
  · simp [AffineHemigroup.concatHalf, h0]
  · norm_num [AffineHemigroup.concatHalf, h1']

/-- `Σ'^{-1/2}(AYAᵀ)Σ'^{-1/2} = Q (Σ^{-1/2}YΣ^{-1/2}) Qᵀ` for `Σ' = AΣAᵀ`, with
`Q = Σ'^{-1/2}AΣ^{1/2}`. -/
theorem relStep_act_eq {S : Mat d} (hS : S.PosDef) (A Y : Mat d) :
    relStep (act A S) (act A Y) = ((msqrt (act A S))⁻¹ * (A * msqrt S)) * relStep S Y *
      ((msqrt (act A S))⁻¹ * (A * msqrt S))ᵀ := by
  have hY : act A Y = (A * msqrt S) * relStep S Y * (A * msqrt S)ᵀ := by
    rw [transpose_mul, msqrt_transpose, act]
    conv_lhs => rw [← msqrt_mul_relStep hS Y]
    simp only [Matrix.mul_assoc]
  rw [hY, relStep_factor]

/-- **`A γ Aᵀ` is `C`-causal when `γ` is**, for an `O(d)`-invariant `C` and `A ∈ GL(d)`: its
relative derivative is an orthogonal conjugate of `γ`'s (entry-free). -/
theorem IsCausalCurve.glAct {C : Set (Mat d)} (hO : IsOrthInvariant C) {γ : ℝ → Mat d}
    (hγ : IsCausalCurve C γ) {A : Mat d} (hA : A ∈ glSet d) :
    IsCausalCurve C (fun t => act A (γ t)) := by
  have hfun : ∀ i j, (fun t => act A (γ t) i j) =
      fun t => ∑ p : Fin d × Fin d, (A i p.1 * A j p.2) * γ t p.1 p.2 := by
    intro i j
    funext t
    simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  refine ⟨fun t ht => (posDef_act_iff hA _).2 (hγ.mem_pd t ht), fun i j => ?_, ?_⟩
  · rw [hfun i j]
    exact AbsolutelyContinuousOnInterval.linear_comb (ι := Fin d × Fin d)
      (fs := fun p t => γ t p.1 p.2) (fun p => A i p.1 * A j p.2)
      (fun p => hγ.absolutelyContinuous p.1 p.2)
  · rw [ae_restrict_iff' measurableSet_Icc]
    have hdiffs : ∀ᵐ t : ℝ, ∀ p : Fin d × Fin d, t ∈ uIcc (0 : ℝ) 1 →
        DifferentiableAt ℝ (fun u => γ u p.1 p.2) t :=
      ae_all_iff.2 fun p => (hγ.absolutelyContinuous p.1 p.2).ae_differentiableAt
    have hcaus := (ae_restrict_iff' measurableSet_Icc).1 hγ.causal
    filter_upwards [hdiffs, hcaus] with t h1 h2 htI
    have hpd := hγ.mem_pd t htI
    have htI' : t ∈ uIcc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one]
    have hm : mderiv (fun t => act A (γ t)) t = act A (mderiv γ t) := by
      ext i j
      simp only [mderiv, of_apply]
      rw [hfun i j]
      have hd : HasDerivAt (fun u => ∑ p : Fin d × Fin d, (A i p.1 * A j p.2) * γ u p.1 p.2)
          (∑ p : Fin d × Fin d, (A i p.1 * A j p.2) * deriv (fun u => γ u p.1 p.2) t) t := by
        exact HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
          ((h1 p htI').hasDerivAt).const_mul (A i p.1 * A j p.2))
      rw [hd.deriv]
      simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
        Finset.sum_mul, of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [hm, relStep_act_eq hpd]
    have hQ : (msqrt (act A (γ t)))⁻¹ * (A * msqrt (γ t)) ∈ orthSet d :=
      msqrt_inv_mul_mem_orthSet ((posDef_act_iff hA _).2 hpd)
        (mul_msqrt_mul_transpose hpd.posSemidef A)
    exact hO _ hQ _ (h2 htI)

/-- `≼_C` is `GL(d)`-invariant (entry-free). -/
theorem causalLE_act {C : Set (Mat d)} (hO : IsOrthInvariant C) {A : Mat d} (hA : A ∈ glSet d)
    {S S' : Mat d} (h : causalLE C S S') : causalLE C (act A S) (act A S') := by
  obtain ⟨γ, hγ, h0, h1⟩ := h
  exact ⟨_, hγ.glAct hO hA, by simp only [h0], by simp only [h1]⟩

/-- **`I ≼_C e^X` for `X ∈ C`**, by the geodesic (entry-free). -/
theorem causalLE_one_mexp {C : Set (Mat d)} (hCsym : C ⊆ symSet d) (hO : IsOrthInvariant C)
    {X : Mat d} (hX : X ∈ C) : causalLE C 1 (mexp X) := by
  obtain ⟨hc, h0, h1⟩ := stepGeodesic_causal hCsym hO PosDef.one (posDef_mexp (hCsym hX))
    ⟨X, hX, by rw [relStep_one_left]⟩
  exact ⟨_, hc, h0, h1⟩

/-- **The rays lie in `≼_C`** when `I ∈ C`, by the geodesic (entry-free). -/
theorem causalLE_ray_of_one_mem {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C) {S : Mat d}
    (hS : S.PosDef) {c : ℝ} (hc : 1 ≤ c) : causalLE C S (c • S) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hcur, h0, h1⟩ := stepGeodesic_causal hCsym hO hS (hS.smul hc0)
    ⟨Real.log c • (1 : Mat d), hC.2.2.2 _ (Real.log_nonneg hc) _ hI, by
      rw [mexp_smul_one, Real.exp_log hc0, relStep_smul, relStep_self hS]⟩
  exact ⟨_, hcur, h0, h1⟩

/-! ## `≼⁺_C` on `PSD(d)` without the entry -/

section PlusOrder

variable {C : Set (Mat d)}

theorem causalPlusLE_refl (S : Mat d) : causalPlusLE C S S :=
  Or.inr (Or.inl ⟨1, le_rfl, (one_smul ℝ S).symm⟩)

theorem causalPlusLE_zero_left (S : Mat d) : causalPlusLE C 0 S := Or.inl rfl

/-- The rays are `≼⁺_C`-related. -/
theorem causalPlusLE_of_rayLE {S S' : Mat d} (h : rayLE S S') : causalPlusLE C S S' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- `≼⁺_C` grows with `C`. -/
theorem causalPlusLE_mono {C' : Set (Mat d)} (hCC' : C ⊆ C') {S S' : Mat d}
    (h : causalPlusLE C S S') : causalPlusLE C' S S' := by
  rcases h with h | h | ⟨h1, h2, γ, hγ, h0, h1'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, h2, γ, hγ.mono hCC', h0, h1'⟩)

/-- **`≼⁺_C` is contained in the Loewner order when `C ⊆ PSD(d)`**: a `PSD(d)`-causal curve is
Loewner-monotone (`prop:stable-order-generated`'s fact (a); entry-free). -/
theorem causalPlusLE_loewner (hpsd : C ⊆ psdSet d) {S S' : Mat d} (hS' : S'.PosSemidef)
    (h : causalPlusLE C S S') : loewnerLE S S' := by
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨-, -, γ, hγ, rfl, rfl⟩
  · simpa [loewnerLE] using hS'
  · unfold loewnerLE
    rw [show c • S - S = (c - 1) • S by rw [sub_smul, one_smul]]
    have hS : S.PosSemidef := by
      rcases eq_or_lt_of_le (show (1 : ℝ) ≤ c from hc) with rfl | hc1
      · simpa using hS'
      · have := hS'.smul (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ c))
        rwa [smul_smul, inv_mul_cancel₀ (by linarith : c ≠ 0), one_smul] at this
    exact hS.smul (by linarith)
  · exact (hγ.mono hpsd).loewnerLE_psd

variable (hd : 1 ≤ d) (hCsym : C ⊆ symSet d) (hC : IsClosedConvexCone C)
  (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
include hd hCsym hC hO hI

/-- **`≼⁺_C` is transitive on `PSD(d)`** (entry-free). -/
theorem causalPlusLE_trans_of_cone {S S' S'' : Mat d} (h : causalPlusLE C S S')
    (h' : causalPlusLE C S' S'') : causalPlusLE C S S'' := by
  haveI : NeZero d := ⟨by omega⟩
  have hC2 : ∀ X ∈ C, (2 : ℝ) • X ∈ C := fun X hX => hC.2.2.2 2 (by norm_num) X hX
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
      exact Or.inr (Or.inr ⟨hSpd, h2', causalLE_trans_of_two_smul hC2
        (causalLE_ray_of_one_mem hCsym hC hO hI hSpd hc) h'⟩)
  · rcases h' with h0 | ⟨c', hc', rfl⟩ | ⟨-, h2', h'⟩
    · exact absurd h0 (PosDef_ne_zero' h2)
    · have hc0 : (0 : ℝ) < c' := by linarith
      exact Or.inr (Or.inr ⟨h1, h2.smul hc0, causalLE_trans_of_two_smul hC2 h
        (causalLE_ray_of_one_mem hCsym hC hO hI h2 hc')⟩)
    · exact Or.inr (Or.inr ⟨h1, h2', causalLE_trans_of_two_smul hC2 h h'⟩)

omit hd hCsym hC hI in
/-- **`≼⁺_C` is `GL(d)`-invariant** (entry-free). -/
theorem causalPlusLE_act_of_cone {A : Mat d} (hA : A ∈ glSet d) {S S' : Mat d}
    (h : causalPlusLE C S S') : causalPlusLE C (act A S) (act A S') := by
  rcases h with rfl | ⟨c, hc, rfl⟩ | ⟨h1, h2, h⟩
  · exact Or.inl (act_zero A)
  · exact Or.inr (Or.inl ⟨c, hc, act_smul A c S⟩)
  · exact Or.inr (Or.inr ⟨(posDef_act_iff hA S).2 h1, (posDef_act_iff hA S').2 h2,
      causalLE_act hO hA h⟩)

end PlusOrder

/-! ## The family toolkit -/

/-- **`lem:gw-kernels-from-origin`(1) without the wedge-datum hypotheses**, which it does not
read: a `(G', W')`-family is a `(G, W)`-family when `G ⊆ G'` and `≤_W ⊆ ≤_{W'}` on `PSD(d)`. -/
theorem gw_family_restrict_of_le {G G' : Set (Mat d)} {le le' : Mat d → Mat d → Prop}
    (hG : G ⊆ G') (hle : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → le' S S')
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G' le' μ) :
    IsGWCascadeFamily G le μ := by
  have hsub : wedgePairs le ⊆ wedgePairs le' :=
    fun p hp => ⟨hp.1, hp.2.1, hle _ _ hp.1 hp.2.1 hp.2.2⟩
  exact
    { isProbability := fun p hp => hμ.isProbability p (hsub hp)
      diag := hμ.diag
      cascade := fun S S' S'' hS hS' hS'' h1 h2 =>
        hμ.cascade S S' S'' hS hS' hS'' (hle _ _ hS hS' h1) (hle _ _ hS' hS'' h2)
      continuous := fun ω => (hμ.continuous ω).mono hsub
      covariant := fun A hA p hp => hμ.covariant A (hG hA) p (hsub hp)
      nondegenerate := hμ.nondegenerate }

/-- **A function that agrees on the pairs with a family is a family**, for a relation that is
reflexive, transitive and `G`-invariant on `PSD(d)` and relates `0` to `I`. -/
theorem IsGWCascadeFamily.of_eqOnPairs {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hrefl : ∀ S : Mat d, S.PosSemidef → le S S)
    (htrans : ∀ S S' S'' : Mat d, S.PosSemidef → S'.PosSemidef → S''.PosSemidef →
      le S S' → le S' S'' → le S S'')
    (hinv : ∀ A ∈ G, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' →
      le (act A S) (act A S'))
    (h01 : le 0 1) {μ ν : Mat d → Mat d → Measure (Rd d)} (hν : IsGWCascadeFamily G le ν)
    (h : EqOnPairs le μ ν) : IsGWCascadeFamily G le μ := by
  refine ⟨fun p hp => ?_, fun S hS => ?_, fun S S' S'' hS hS' hS'' h1 h2 => ?_, fun ω => ?_,
    fun A hA p hp => ?_, ?_⟩
  · rw [h p hp]; exact hν.isProbability p hp
  · rw [show μ S S = ν S S from h (S, S) ⟨hS, hS, hrefl S hS⟩]; exact hν.diag S hS
  · rw [show μ S S'' = ν S S'' from h (S, S'') ⟨hS, hS'', htrans S S' S'' hS hS' hS'' h1 h2⟩,
      show μ S' S'' = ν S' S'' from h (S', S'') ⟨hS', hS'', h2⟩,
      show μ S S' = ν S S' from h (S, S') ⟨hS, hS', h1⟩]
    exact hν.cascade S S' S'' hS hS' hS'' h1 h2
  · exact (hν.continuous ω).congr fun p hp => by simp only; rw [h p hp]
  · rw [h p hp, show μ (act A p.1) (act A p.2) = ν (act A p.1) (act A p.2) from
      h (act A p.1, act A p.2) ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1,
        hinv A hA p.1 p.2 hp.1 hp.2.1 hp.2.2⟩]
    exact hν.covariant A hA p hp
  · rw [show μ 0 1 = ν 0 1 from h (0, 1) ⟨PosSemidef.zero, PosSemidef.one, h01⟩]
    exact hν.nondegenerate

/-- The cascade from the origin, read on transforms: `μ̂_{Σ'} = μ̂_{Σ,Σ'} μ̂_Σ` for `Σ ≤_W Σ'`,
when `0 ≤_W Σ` for every `Σ`. -/
theorem IsGWCascadeFamily.charFun_origin {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsGWCascadeFamily G le μ)
    (h0 : ∀ S : Mat d, S.PosSemidef → le 0 S) {S S' : Mat d} (hS : S.PosSemidef)
    (hS' : S'.PosSemidef) (h : le S S') (ω : Rd d) :
    charFun (μ 0 S') ω = charFun (μ S S') ω * charFun (μ 0 S) ω := by
  haveI := hμ.isProbability (S, S') ⟨hS, hS', h⟩
  haveI := hμ.isProbability (0, S) ⟨PosSemidef.zero, hS, h0 S hS⟩
  rw [hμ.cascade 0 S S' PosSemidef.zero hS hS' (h0 S hS) h, charFun_conv]

/-! ## The kernels from the origin along an order containing the rays -/

/-- **The radial exponent of a rotation-invariant self-decomposable law** (the ray-family form of
`lem:affine-reduction`): `μ̂_I(ω) = e^{-g(|ω|²)}` with `g` continuous on `[0,∞)`, `g ≥ 0`,
`g(0) = 0` and `g ≢ 0` when `μ_I ≠ δ₀`. -/
theorem radial_exponent [NeZero d] (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI)
    (hne : μI ≠ Measure.dirac 0) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∃ u : ℝ, 0 ≤ u ∧ g u ≠ 0) ∧
      ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  set φ : ℝ → ℂ := fun u => charFun μI (Real.sqrt u • ebasis 0) with hφdef
  have hφ : ∀ ω : Rd d, charFun μI ω = φ (‖ω‖ ^ 2) := by
    intro ω
    simp only [hφdef, Real.sqrt_sq (norm_nonneg ω)]
    exact charFun_eq_norm_smul_ebasis hrot ω
  have hφcont : Continuous φ :=
    continuous_charFun.comp (Real.continuous_sqrt.smul continuous_const)
  have hreal : ∀ ω : Rd d, (charFun μI ω).im = 0 := by
    intro ω
    have h1 : charFun μI (-ω) = charFun μI ω := charFun_eq_of_norm_eq hrot (norm_neg ω)
    rw [charFun_neg] at h1
    exact Complex.conj_eq_iff_im.1 h1
  have hφne : ∀ u : ℝ, φ u ≠ 0 := fun u => (selfDecomposable_charFun_ne_zero μI hsd).1 _
  set φr : ℝ → ℝ := fun u => (φ u).re with hφrdef
  have hφr : ∀ u : ℝ, φ u = (φr u : ℂ) := by
    intro u
    apply Complex.ext
    · simp [hφrdef]
    · simp only [Complex.ofReal_im]
      exact hreal _
  have hφr0 : φr 0 = 1 := by simp [hφrdef, hφdef, charFun_zero]
  have hφrcont : Continuous φr := Complex.continuous_re.comp hφcont
  have hφrle : ∀ u : ℝ, φr u ≤ 1 := fun u =>
    (Complex.re_le_norm _).trans (norm_charFun_le_one _)
  have hφrpos : ∀ u : ℝ, 0 ≤ u → 0 < φr u := by
    intro u hu
    by_contra hneg
    push Not at hneg
    obtain ⟨v, -, hv0⟩ := intermediate_value_Icc' hu hφrcont.continuousOn
      ⟨hneg, by rw [hφr0]; norm_num⟩
    apply hφne v
    rw [hφr, hv0, Complex.ofReal_zero]
  set g : ℝ → ℝ := fun u => -Real.log (φr u) with hgdef
  have hexp : ∀ u : ℝ, 0 ≤ u → φ u = ((Real.exp (-g u) : ℝ) : ℂ) := by
    intro u hu
    rw [hφr, hgdef, neg_neg, Real.exp_log (hφrpos u hu)]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hφrcont.continuousOn.log fun u hu => (hφrpos u hu).ne').neg
  · intro u hu
    simp only [hgdef, neg_nonneg]
    exact Real.log_nonpos (hφrpos u hu).le (hφrle u)
  · simp [hgdef, hφr0]
  · by_contra hcon
    push Not at hcon
    apply hne
    apply eq_dirac_of_charFun_one_near_zero _ 1 one_pos
    intro η _
    rw [hφ, hexp _ (sq_nonneg _), hcon _ (sq_nonneg _)]
    simp
  · intro ω
    rw [hφ, hexp _ (sq_nonneg _)]

/-- **The kernels from the origin of a `(GL(d), W)`-family, for an order containing the rays**
(`prop:gw-ray-families`(3) after restriction to the rays, and the radial exponent): `μ_I` is a
rotation-invariant self-decomposable probability law other than `δ₀`, `μ_Σ = (Σ^{1/2})_*μ_I`, and
`μ̂_Σ(ω) = e^{-g(⟨ω,Σω⟩)}` with `g` continuous on `[0,∞)`, `g ≥ 0`, `g(0) = 0`, `g ≢ 0`. -/
theorem gl_kernels_of_rays [NeZero d] {le : Mat d → Mat d → Prop}
    (hray : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → rayLE S S' → le S S')
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsGWCascadeFamily (glSet d) le μ) :
    IsProbabilityMeasure (μ 0 1) ∧ IsRotationInvariant (μ 0 1) ∧ IsSelfDecomposable (μ 0 1) ∧
      μ 0 1 ≠ Measure.dirac 0 ∧ (∀ S : Mat d, S.PosSemidef → μ 0 S = affineOrbit (μ 0 1) S) ∧
      ∃ g : ℝ → ℝ, ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
        (∃ u : ℝ, 0 ≤ u ∧ g u ≠ 0) ∧
        ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
          charFun (μ 0 S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) := by
  have hμr := gw_family_restrict_of_le subset_rfl hray μ hμ
  obtain ⟨horb, hrot, hsd, hne, hcf⟩ := gw_ray_families_gl μ hμr
  haveI hp : IsProbabilityMeasure (μ 0 1) :=
    hμ.isProbability (0, 1) ⟨PosSemidef.zero, PosSemidef.one,
      hray 0 1 PosSemidef.zero PosSemidef.one (Or.inl rfl)⟩
  obtain ⟨g, hgc, hgnn, hg0, hgne, hg⟩ := radial_exponent (μ 0 1) hrot hsd hne
  refine ⟨hp, hrot, hsd, hne, horb, g, hgc, hgnn, hg0, hgne, fun S hS ω => ?_⟩
  rw [hcf S hS ω, hg]
  have hn : ‖Real.sqrt (quad S ω) • ebasis (0 : Fin d)‖ ^ 2 = quad S ω := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp [ebasis, Real.sq_sqrt (quad_nonneg hS ω)]
  rw [hn]


/-! ## Matrix facts for the chain -/

/-- `λ_min(M) ≤ Mᵢᵢ` for a symmetric `M`. -/
theorem lamMin_le_diag [NeZero d] {M : Mat d} (hM : M.IsHermitian) (i : Fin d) :
    lamMin M ≤ M i i := by
  have h := lamMin_le_inner hM (u := ebasis i) (by simp [ebasis])
  have hq := quad_ebasis M i
  rw [quad] at hq
  rwa [hq] at h

/-- A symmetric matrix with `λ_min > 0` is positive definite. -/
theorem posDef_of_lamMin_pos [NeZero d] {X : Mat d} (hX : X.IsHermitian) (h : 0 < lamMin X) :
    X.PosDef := by
  have hs := (posSemidef_sub_smul_one_iff hX (lamMin X)).2 (lamMin_eq_eigUp_zero hX).le
  have := PosDef.posSemidef_add hs (PosDef.one.smul h)
  rwa [sub_add_cancel] at this

/-- A symmetric matrix with `λ_min ≥ 0` is positive semidefinite. -/
theorem posSemidef_of_lamMin_nonneg [NeZero d] {X : Mat d} (hX : X.IsHermitian)
    (h : 0 ≤ lamMin X) : X.PosSemidef := by
  have := (posSemidef_sub_smul_one_iff hX 0).2 (by rwa [← lamMin_eq_eigUp_zero hX])
  simpa using this

/-- `sym X = X` for a symmetric `X`. -/
theorem symPart_of_isSymm {X : Mat d} (hX : X.IsSymm) : symPart X = X := by
  rw [symPart, hX.eq, ← two_smul ℝ X, smul_smul]
  norm_num

/-- `d λ_min(X) ≤ tr X` for a symmetric `X`. -/
theorem card_mul_lamMin_le_trace [NeZero d] {X : Mat d} (hX : X.IsSymm) :
    (d : ℝ) * lamMin X ≤ X.trace := by
  have := trace_ge_card_mul_lamMin X
  rwa [symPart_of_isSymm hX] at this

/-- `e^X ∈ exp C` forces `X ∈ C` for a symmetric `X` and `C ⊆ Sym(d)` (the exponential is injective
on `Sym(d)`). -/
theorem mem_of_mexp_mem_expSet {C : Set (Mat d)} (hCsym : C ⊆ symSet d) {X : Mat d}
    (hX : X.IsSymm) (h : mexp X ∈ expSet C) : X ∈ C := by
  obtain ⟨Y, hY, he⟩ := h
  have : X = Y := by
    rw [← mlog_mexp (isHermitian_of_isSymm hX), he,
      mlog_mexp (isHermitian_of_isSymm (hCsym hY))]
  rwa [this]

/-- **`I ≼_α e^X` forces `X ∈ C_α`** for finite `α ≥ 0` (`prop:stable-order-generated`(1), which
identifies `≼_α` without the entry). -/
theorem mem_of_causalLE_one_mexp (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) {X : Mat d} (hX : X.IsSymm)
    (h : causalLE (stableGenCone d a) 1 (mexp X)) : X ∈ stableGenCone d a := by
  haveI : NeZero d := ⟨by omega⟩
  have hM := posDef_mexp hX
  rcases ha.lt_or_eq with ha | rfl
  · have h' := (((stable_order_pos hd ha).2 1 (mexp X) PosDef.one hM).1).1 h
    obtain ⟨-, -, -, hdet⟩ := h'
    rw [relStep_one_left] at hdet
    exact mem_of_mexp_mem_expSet (stableGenCone_props hd ha.le).1 hX
      ((mem_expSet_stableGenCone_iff hd ha hM).2 hdet)
  · obtain ⟨hC0, hiff⟩ := stable_order_zero hd
    obtain ⟨c, hc, he⟩ := ((hiff 1 (mexp X) PosDef.one hM).1).1 h
    rw [smul_one_eq_diagonal] at he
    have hc0 : 0 < c := by linarith
    have hX' : X = Real.log c • (1 : Mat d) := by
      rw [← mlog_mexp (isHermitian_of_isSymm hX), he, ← smul_one_eq_diagonal,
        ← Real.exp_log hc0, ← mexp_smul_one, Real.exp_log hc0,
        mlog_mexp (isHermitian_of_isSymm ((isSymm_one).smul _))]
    rw [hC0]
    exact ⟨Real.log c, Real.log_nonneg hc, hX'⟩

/-- `C_a ⊆ C_b` for `0 ≤ a ≤ b`. -/
theorem stableGenCone_mono (hd : 1 ≤ d) {a b : ℝ} (hab : a ≤ b) :
    stableGenCone d a ⊆ stableGenCone d b := by
  haveI : NeZero d := ⟨by omega⟩
  intro X hX
  refine ⟨hX.1, hX.2.trans ?_⟩
  have := lamMin_nonneg hX.1
  nlinarith

/-- `C_α ⊆ C_β` for `0 ≤ α ≤ β ≤ ∞`. -/
theorem stableGenConeTop_mono (hd : 1 ≤ d) {α β : WithTop ℝ} (hαβ : α ≤ β) :
    stableGenConeTop d α ⊆ stableGenConeTop d β := by
  induction β using WithTop.recTopCoe with
  | top =>
    induction α using WithTop.recTopCoe with
    | top => exact subset_rfl
    | coe a => exact fun X hX => hX.1
  | coe b =>
    induction α using WithTop.recTopCoe with
    | top => exact absurd hαβ (by simp)
    | coe a => exact stableGenCone_mono hd (WithTop.coe_le_coe.1 hαβ)

/-- `C_α ⊆ PSD(d)`. -/
theorem stableGenConeTop_subset_psd (α : WithTop ℝ) : stableGenConeTop d α ⊆ psdSet d := by
  induction α using WithTop.recTopCoe with
  | top => exact subset_rfl
  | coe a => exact fun X hX => hX.1

/-- **The cones `C_α`, `0 ≤ α ≤ ∞`**: `O(d)`-invariant closed convex cones in `Sym(d)`, with
`I ∈ C_α` and `C_α ∩ (-C_α) = {0}`. -/
theorem stableGenConeTop_props (hd : 1 ≤ d) {α : WithTop ℝ} (hα : 0 ≤ α) :
    stableGenConeTop d α ⊆ symSet d ∧ IsOrthInvariant (stableGenConeTop d α) ∧
      IsClosedConvexCone (stableGenConeTop d α) ∧ (1 : Mat d) ∈ stableGenConeTop d α ∧
      ∀ X ∈ stableGenConeTop d α, -X ∈ stableGenConeTop d α → X = 0 := by
  induction α using WithTop.recTopCoe with
  | top => exact psdSet_cone_props hd
  | coe a => exact stableGenCone_props hd (WithTop.coe_nonneg.1 hα)

/-- The rank-one projection `e_{i₀}e_{i₀}ᵀ`. -/
noncomputable def projE (i₀ : Fin d) : Mat d := diagonal (Pi.single i₀ 1)

theorem projE_posSemidef (i₀ : Fin d) : (projE i₀).PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  by_cases h : i = i₀
  · subst h; simp
  · simp [h]

theorem projE_trace (i₀ : Fin d) : (projE i₀).trace = 1 := by
  simp [projE, trace_diagonal]

theorem projE_apply_ne {i₀ i₁ : Fin d} (h : i₁ ≠ i₀) : projE i₀ i₁ i₁ = 0 := by
  simp [projE, h]

/-- **The witness `I + b e_{i₀}e_{i₀}ᵀ`**: trace `d + b`, `λ_min = 1` (for `b ≥ 0`, `d ≥ 2`). -/
theorem witness_props (hd : 2 ≤ d) {b : ℝ} (hb : 0 ≤ b) :
    let X : Mat d := 1 + b • projE (⟨0, by omega⟩ : Fin d)
    X.PosSemidef ∧ X.trace = d + b ∧ lamMin X = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  intro X
  have hne : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have hP := projE_posSemidef (⟨0, by omega⟩ : Fin d)
  have hXp : X.PosSemidef := PosSemidef.one.add (hP.smul hb)
  refine ⟨hXp, ?_, le_antisymm ?_ ?_⟩
  · simp only [X, trace_add, trace_one, Fintype.card_fin, trace_smul, projE_trace, smul_eq_mul,
      mul_one]
  · have h := lamMin_le_diag hXp.isHermitian ⟨1, by omega⟩
    have h1 : X ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by
      simp only [X, Matrix.add_apply, Matrix.smul_apply, projE_apply_ne hne, one_apply_eq,
        smul_eq_mul, mul_zero, add_zero]
    linarith
  · rw [lamMin_eq_eigUp_zero hXp.isHermitian, ← posSemidef_sub_smul_one_iff hXp.isHermitian]
    have h : X - (1 : ℝ) • (1 : Mat d) = b • projE ⟨0, by omega⟩ := by
      simp only [X, one_smul, add_sub_cancel_left]
    rw [h]
    exact hP.smul hb

/-- `λ_min(e_{i₀}e_{i₀}ᵀ) = 0` for `d ≥ 2`. -/
theorem lamMin_projE (hd : 2 ≤ d) : lamMin (projE (⟨0, by omega⟩ : Fin d)) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hP := projE_posSemidef (⟨0, by omega⟩ : Fin d)
  refine le_antisymm ?_ (lamMin_nonneg hP)
  have := lamMin_le_diag hP.isHermitian (⟨1, by omega⟩ : Fin d)
  rwa [projE_apply_ne (by simp [Fin.ext_iff])] at this

/-- **Nonzero members of `C_a`, `a < ∞`, are positive definite**, with `λ_min > 0`. -/
theorem lamMin_pos_of_mem_stableGenCone (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) {X : Mat d}
    (hX : X ∈ stableGenCone d a) (h0 : X ≠ 0) : 0 < lamMin X := by
  haveI : NeZero d := ⟨by omega⟩
  have htr := trace_pos_of_posSemidef hX.1 h0
  have hda : 0 < (d : ℝ) + a := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_contra hneg
  push Not at hneg
  have := hX.2
  nlinarith

/-! ## `lem:wedge-axis-chain` (1), the chain -/

/-- **`lem:wedge-axis-chain`** (`thm:wedge-axis`(1)), the chain: for `0 ≤ α < β ≤ ∞`,
`C_α ⊊ C_β` and `≼_α ⊊ ≼_β`; for `α < ∞` every nonzero member of `C_α` is positive definite, while
`C_∞ = PSD(d)` contains every nonzero singular positive semidefinite matrix; and the union of the
`C_α`, `0 ≤ α < 2`, is `{0} ∪ {X ∈ Sym(d) : (d+2)λ_min(X) > tr X}`, a proper subset of `C₂`. -/
theorem wedge_axis_chain (hd : 2 ≤ d) :
    (∀ α β : WithTop ℝ, 0 ≤ α → α < β →
      stableGenConeTop d α ⊂ stableGenConeTop d β ∧
        {p : Mat d × Mat d | causalLE (stableGenConeTop d α) p.1 p.2} ⊂
          {p : Mat d × Mat d | causalLE (stableGenConeTop d β) p.1 p.2}) ∧
      (∀ α : ℝ, 0 ≤ α → ∀ X ∈ stableGenCone d α, X ≠ 0 → X.PosDef) ∧
      (∀ X : Mat d, X.PosSemidef → X ≠ 0 → X.det = 0 → X ∈ stableGenConeTop d ⊤) ∧
      (⋃ α ∈ Ico (0 : ℝ) 2, stableGenCone d α) =
        {0} ∪ {X : Mat d | X.IsSymm ∧ X.trace < ((d : ℝ) + 2) * lamMin X} ∧
      (⋃ α ∈ Ico (0 : ℝ) 2, stableGenCone d α) ⊂ stableGenCone d 2 := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set i₀ : Fin d := ⟨0, by omega⟩
  /- Positive definiteness of the nonzero members of a finite `C_a`. -/
  have hpd : ∀ a : ℝ, 0 ≤ a → ∀ X ∈ stableGenCone d a, X ≠ 0 → X.PosDef := fun a ha X hX h0 =>
    posDef_of_lamMin_pos hX.1.isHermitian (lamMin_pos_of_mem_stableGenCone hd1 ha hX h0)
  /- The union. -/
  have hunion : (⋃ α ∈ Ico (0 : ℝ) 2, stableGenCone d α) =
      {0} ∪ {X : Mat d | X.IsSymm ∧ X.trace < ((d : ℝ) + 2) * lamMin X} := by
    ext X
    simp only [mem_iUnion, mem_union, mem_singleton_iff, mem_setOf_eq, mem_Ico, exists_prop]
    constructor
    · rintro ⟨a, ⟨ha0, ha2⟩, hX⟩
      by_cases h0 : X = 0
      · exact Or.inl h0
      · have hl := lamMin_pos_of_mem_stableGenCone hd1 ha0 hX h0
        refine Or.inr ⟨isSymm_of_isHermitian hX.1.isHermitian, ?_⟩
        nlinarith [hX.2]
    · rintro (rfl | ⟨hXs, hlt⟩)
      · exact ⟨0, ⟨le_rfl, two_pos⟩, (stableGenCone_props hd1 le_rfl).2.2.1.2.2.1⟩
      · have hle := card_mul_lamMin_le_trace hXs
        have hl : 0 < lamMin X := by nlinarith
        refine ⟨X.trace / lamMin X - d, ⟨?_, ?_⟩, ?_, ?_⟩
        · rw [sub_nonneg, le_div_iff₀ hl]; exact hle
        · rw [sub_lt_iff_lt_add, div_lt_iff₀ hl]; linarith
        · exact posSemidef_of_lamMin_nonneg (isHermitian_of_isSymm hXs) hl.le
        · rw [add_sub_cancel, div_mul_cancel₀ _ hl.ne']
  refine ⟨fun α β hα hαβ => ?_, hpd, fun X hX _ _ => hX, hunion, ?_⟩
  · /- (1), the strict inclusions. -/
    have hβ : 0 ≤ β := hα.trans hαβ.le
    obtain ⟨hCsymβ, hOβ, -, -, -⟩ := stableGenConeTop_props hd1 hβ
    have hsub : stableGenConeTop d α ⊆ stableGenConeTop d β := stableGenConeTop_mono hd1 hαβ.le
    induction α using WithTop.recTopCoe with
    | top => exact absurd hαβ (not_top_lt)
    | coe a =>
      have ha : 0 ≤ a := WithTop.coe_nonneg.1 hα
      /- A witness `W ∈ C_β ∖ C_a`. -/
      obtain ⟨W, hWβ, hWa⟩ : ∃ W ∈ stableGenConeTop d β, W ∉ stableGenCone d a := by
        induction β using WithTop.recTopCoe with
        | top =>
          refine ⟨projE i₀, projE_posSemidef i₀, fun hW => ?_⟩
          have := hW.2
          rw [projE_trace, lamMin_projE hd, mul_zero] at this
          linarith
        | coe b =>
          have hab : a < b := WithTop.coe_lt_coe.1 hαβ
          obtain ⟨hWp, htr, hl⟩ := witness_props hd (b := b) (by linarith)
          refine ⟨_, ⟨hWp, by rw [htr, hl, mul_one]⟩, fun hW => ?_⟩
          have := hW.2
          rw [htr, hl, mul_one] at this
          linarith
      have hWs : W.IsSymm := hCsymβ hWβ
      refine ⟨(ssubset_iff_of_subset hsub).2 ⟨W, hWβ, hWa⟩,
        (ssubset_iff_of_subset fun p hp => ?_).2 ⟨(1, mexp W), ?_, fun h => hWa ?_⟩⟩
      · obtain ⟨γ, hγ, h0, h1⟩ := hp
        exact ⟨γ, hγ.mono hsub, h0, h1⟩
      · exact causalLE_one_mexp hCsymβ hOβ hWβ
      · exact mem_of_causalLE_one_mexp hd1 ha hWs h
  · /- The union is a proper subset of `C₂`. -/
    have hsub : (⋃ α ∈ Ico (0 : ℝ) 2, stableGenCone d α) ⊆ stableGenCone d 2 :=
      iUnion₂_subset fun a ha => stableGenCone_mono hd1 ha.2.le
    obtain ⟨hWp, htr, hl⟩ := witness_props hd (b := 2) (by norm_num)
    refine (ssubset_iff_of_subset hsub).2 ⟨_, ⟨hWp, by rw [htr, hl, mul_one]⟩, fun hW => ?_⟩
    rw [hunion] at hW
    rcases hW with hW | ⟨-, hlt⟩
    · have := congrArg Matrix.trace (mem_singleton_iff.1 hW)
      rw [htr, trace_zero] at this
      linarith
    · rw [htr, hl, mul_one] at hlt
      exact lt_irrefl _ hlt


/-! ## `lem:wedge-axis-chain` (2), the families -/

/-- `I ≼⁺_C e^X` for `X ∈ C` (entry-free). -/
theorem causalPlusLE_one_mexp {C : Set (Mat d)} (hCsym : C ⊆ symSet d) (hO : IsOrthInvariant C)
    {X : Mat d} (hX : X ∈ C) : causalPlusLE C 1 (mexp X) :=
  Or.inr (Or.inr ⟨PosDef.one, posDef_mexp (hCsym hX), causalLE_one_mexp hCsym hO hX⟩)

/-- **The one-step identity at `I ≼⁺_C e^X`**: `e^{-g(⟨ω,e^Xω⟩)} = ρ̂(ω)e^{-g(|ω|²)}` with
`ρ = μ_{I,e^X}`, for the radial exponent `g` of `gl_kernels_of_rays`. -/
theorem charFun_step_mexp {C : Set (Mat d)} (hCsym : C ⊆ symSet d) (hO : IsOrthInvariant C)
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsGWCascadeFamily (glSet d) (causalPlusLE C) μ)
    {g : ℝ → ℝ} (hg : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      charFun (μ 0 S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ))
    {X : Mat d} (hX : X ∈ C) (ω : Rd d) :
    ((Real.exp (-g (quad (mexp X) ω)) : ℝ) : ℂ) =
      charFun (μ 1 (mexp X)) ω * ((Real.exp (-g (quad 1 ω)) : ℝ) : ℂ) := by
  have hM := (posDef_mexp (hCsym hX)).posSemidef
  rw [← hg _ hM, ← hg _ PosSemidef.one]
  exact hμ.charFun_origin (fun S _ => causalPlusLE_zero_left S) PosSemidef.one hM
    (causalPlusLE_one_mexp hCsym hO hX) ω

/-- **`lem:wedge-axis-chain`** (`thm:wedge-axis`(2)(a)): for an `O(d)`-invariant closed convex cone
`C ⊆ Sym(d)` with `I ∈ C` and `C ∩ (-C) = {0}`, if `C ⊄ PSD(d)` there is no
`(GL(d), ≼⁺_C)`-cascade family of kernels. -/
theorem wedge_axis_not_psd (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (_hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (_hI : (1 : Mat d) ∈ C)
    (_hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hnot : ¬ C ⊆ psdSet d) :
    ¬ ∃ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) (causalPlusLE C) μ := by
  haveI : NeZero d := ⟨by omega⟩
  rintro ⟨μ, hμ⟩
  obtain ⟨-, -, -, -, -, g, hgc, hgnn, hg0, ⟨u₀, hu₀, hgu₀⟩, hg⟩ :=
    gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ
  obtain ⟨X, hXC, hXnot⟩ := not_subset.1 hnot
  have hXs : X.IsSymm := hCsym hXC
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hXs)
  set x := eigUp X with hx
  /- An eigenvalue `λ < 0`, with eigenvector `v = V eᵢ`. -/
  obtain ⟨i, hi⟩ : ∃ i, x i < 0 := by
    by_contra h
    push Not at h
    exact hXnot (by rw [hXV]; exact (udiag_posSemidef_iff hV x).2 h)
  set v : Rd d := lin V (EuclideanSpace.single i 1)
  set m := Real.exp (x i)
  have hm0 : 0 < m := Real.exp_pos _
  have hm1 : m < 1 := Real.exp_lt_one_iff.2 hi
  have hqM : quad (mexp X) v = m := by
    rw [hXV, mexp_udiag hV]; exact quad_udiag_lin_single hV _ i
  have hq1 : quad 1 v = 1 := by
    rw [← udiag_one hV]; exact quad_udiag_lin_single hV (fun _ => 1) i
  /- `g(u) ≤ g(mu)` for `u ≥ 0`, from `|ρ̂| ≤ 1`. -/
  have hmono : ∀ u : ℝ, 0 ≤ u → g u ≤ g (m * u) := by
    intro u hu
    have h := charFun_step_mexp hCsym hO hμ hg hXC (Real.sqrt u • v)
    rw [quad_smul_vec, quad_smul_vec, hqM, hq1, Real.sq_sqrt hu, mul_one] at h
    have hn := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hn
    haveI := hμ.isProbability (1, mexp X) ⟨PosSemidef.one, (posDef_mexp hXs).posSemidef,
      causalPlusLE_one_mexp hCsym hO hXC⟩
    have hle : Real.exp (-g (u * m)) ≤ Real.exp (-g u) := by
      rw [hn]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (norm_charFun_le_one _)
    rw [mul_comm] at hle
    linarith [Real.exp_le_exp.1 hle]
  have hiter : ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ, g u ≤ g (m ^ n * u) := by
    intro u hu n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hmono (m ^ n * u) (mul_nonneg (pow_nonneg hm0.le n) hu)
      rw [pow_succ', mul_assoc]
      exact ih.trans this
  /- `m^n u → 0`, so `g(u) ≤ g(0) = 0`. -/
  have hzero : ∀ u : ℝ, 0 ≤ u → g u ≤ 0 := by
    intro u hu
    have ht : Tendsto (fun n : ℕ => m ^ n * u) atTop (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mul_nonneg (pow_nonneg hm0.le n) hu⟩
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hm0.le hm1).mul_const u
    have hlim := ((hgc 0 self_mem_Ici).tendsto).comp ht
    rw [hg0] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n => hiter u hu n
  exact hgu₀ (le_antisymm (hzero u₀ hu₀) (hgnn u₀ hu₀))

/-- `rank(V diag(w) Vᵀ) = #{i : wᵢ ≠ 0}` for an orthogonal `V`. -/
theorem rank_udiag {V : Mat d} (hV : V * Vᵀ = 1) (w : Fin d → ℝ) :
    (udiag V w).rank = Fintype.card {i // w i ≠ 0} := by
  classical
  have hdet : IsUnit V.det := mem_glSet_of_orth hV
  have hdetT : IsUnit Vᵀ.det := by rw [det_transpose]; exact hdet
  rw [udiag, rank_mul_eq_left_of_isUnit_det _ _ hdetT, rank_mul_eq_right_of_isUnit_det _ _ hdet,
    rank_diagonal]

/-- **The transforms decide the family** (the end of `thm:wedge-axis`(2)(b)): for `C ⊆ PSD(d)`,
a `(GL(d), ≼⁺_C)`-family with `μ̂_Σ(ω) = e^{-b⟨ω,Σω⟩}`, `b > 0`, agrees on the pairs with the affine
Gaussian scale space. -/
theorem eqOnPairs_affineGaussian_of_charFun {C : Set (Mat d)} (hpsd : C ⊆ psdSet d)
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsGWCascadeFamily (glSet d) (causalPlusLE C) μ)
    {b : ℝ} (hb : 0 < b)
    (h : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      charFun (μ 0 S) ω = ((Real.exp (-(b * quad S ω)) : ℝ) : ℂ)) :
    EqOnPairs (causalPlusLE C) μ (affineGaussian b) := by
  rintro ⟨S, S'⟩ ⟨hS, hS', hle⟩
  haveI := hμ.isProbability (S, S') ⟨hS, hS', hle⟩
  refine eq_of_charFun_eq fun ω => ?_
  have hc := hμ.charFun_origin (fun S _ => causalPlusLE_zero_left S) hS hS' hle ω
  rw [h S' hS', h S hS] at hc
  simp only
  rw [charFun_affineGaussian hb hS hS' (causalPlusLE_loewner hpsd hS' hle), quad_sub]
  have hne : ((Real.exp (-(b * quad S ω)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  apply mul_right_cancel₀ hne
  rw [← hc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- **The restrictions of the affine Gaussian scale spaces are families** (the converse in
`thm:wedge-axis`(2)(b)): for `C ⊆ PSD(d)`, a function that agrees on the pairs of `≼⁺_C` with the
affine Gaussian scale space with constant `b > 0` is a `(GL(d), ≼⁺_C)`-cascade family
(`thm:affine-rigidity`, restriction, and the order properties of `≼⁺_C` proved without the
entry). -/
theorem family_of_eqOnPairs_affineGaussian (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpsd : C ⊆ psdSet d) {b : ℝ} (hb : 0 < b) {μ : Mat d → Mat d → Measure (Rd d)}
    (h : EqOnPairs (causalPlusLE C) μ (affineGaussian b)) :
    IsGWCascadeFamily (glSet d) (causalPlusLE C) μ := by
  have hd1 : 1 ≤ d := by omega
  have hν : IsAffineCascadeFamily (affineGaussian (d := d) b) :=
    (affine_rigidity hd _).2 ⟨b, hb, fun _ _ => rfl⟩
  have hνC := gw_family_restrict_of_le subset_rfl
    (fun S S' _ hS' h => causalPlusLE_loewner hpsd hS' h) _ hν
  exact IsGWCascadeFamily.of_eqOnPairs (fun S _ => causalPlusLE_refl S)
    (fun S S' S'' _ _ _ h h' => causalPlusLE_trans_of_cone hd1 hCsym hC hO hI h h')
    (fun A hA S S' _ _ h => causalPlusLE_act_of_cone hO hA h) (causalPlusLE_zero_left 1) hνC h

/-- **`lem:wedge-axis-chain`** (`thm:wedge-axis`(2)(b)): if moreover `C ⊆ PSD(d)` and `C` contains a
nonzero singular matrix, the `(GL(d), ≼⁺_C)`-cascade families of kernels are exactly the
restrictions to the pairs `Σ ≼⁺_C Σ'` of the affine Gaussian scale spaces, `b > 0`. -/
theorem wedge_axis_singular (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (_hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hsing : ∃ X ∈ C, X ≠ 0 ∧ X.det = 0) (μ : Mat d → Mat d → Measure (Rd d)) :
    IsGWCascadeFamily (glSet d) (causalPlusLE C) μ ↔
      ∃ b : ℝ, 0 < b ∧ EqOnPairs (causalPlusLE C) μ (affineGaussian b) := by
  haveI : NeZero d := ⟨by omega⟩
  constructor
  · intro hμ
    obtain ⟨-, -, -, -, -, g, hgc, hgnn, hg0, ⟨u₀, hu₀, hgu₀⟩, hg⟩ :=
      gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ
    obtain ⟨X, hXC, hX0, hdet⟩ := hsing
    have hXs : X.IsSymm := hCsym hXC
    have hXp : X.PosSemidef := hpsd hXC
    obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hXp.isHermitian
    set x := eigUp X with hx
    have hxnn : ∀ i, 0 ≤ x i := eigUp_nonneg hXp
    /- `P = e^X - I`, positive semidefinite with `0 < rank P < d`. -/
    set P : Mat d := mexp X - 1 with hPdef
    have hPV : P = udiag V (fun i => Real.exp (x i) - 1) := by
      rw [hPdef, hXV, mexp_udiag hV, ← udiag_one hV, udiag_sub]
      rfl
    have hP : P.PosSemidef := by
      rw [hPV]
      exact (udiag_posSemidef_iff hV _).2 fun i => sub_nonneg.2 (Real.one_le_exp (hxnn i))
    have hrank : P.rank = Fintype.card {i // x i ≠ 0} := by
      rw [hPV, rank_udiag hV]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
        rw [sub_ne_zero, Ne, Real.exp_eq_one_iff])
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      apply hX0
      rw [hXV, show x = fun _ => (0 : ℝ) from funext h, udiag_const hV, zero_smul]
    obtain ⟨j, hj⟩ : ∃ j, x j = 0 := by
      have hprod : ∏ k, x k = 0 := by rw [hx, prod_eigUp hXp.isHermitian, hdet]
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hprod
      exact ⟨j, hj⟩
    have hrank_pos : 0 < P.rank := by
      rw [hrank]; exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    have hrank_lt : P.rank < d := by
      rw [hrank]
      have := Fintype.card_subtype_lt (p := fun k => x k ≠ 0) (x := j) (by simpa using hj)
      simpa using this
    /- `thm:rank-deficient-step` at `Σ = I`. -/
    set ρ := μ 1 (mexp X)
    haveI : IsProbabilityMeasure ρ :=
      hμ.isProbability (1, mexp X) ⟨PosSemidef.one, (posDef_mexp hXs).posSemidef,
        causalPlusLE_one_mexp hCsym hO hXC⟩
    have hstep : ∀ ω : Rd d, ((Real.exp (-g (quad (1 + P) ω)) : ℝ) : ℂ) =
        ((Real.exp (-g (quad 1 ω)) : ℝ) : ℂ) * charFun ρ ω := by
      intro ω
      rw [hPdef, add_sub_cancel, charFun_step_mexp hCsym hO hμ hg hXC ω, mul_comm]
    obtain ⟨hlin, hb0, -⟩ := rank_deficient_step hd g hgnn (hgc 0 self_mem_Ici) hg0 1 P PosDef.one
      hP hrank_pos hrank_lt ρ hstep
    have hb : 0 < g 1 := by
      refine lt_of_le_of_ne hb0 fun h => hgu₀ ?_
      rw [hlin u₀ hu₀, ← h, zero_mul]
    refine ⟨g 1, hb, eqOnPairs_affineGaussian_of_charFun hpsd hμ hb fun S hS ω => ?_⟩
    rw [hg S hS ω, hlin _ (quad_nonneg hS ω)]
  · rintro ⟨b, hb, h⟩
    exact family_of_eqOnPairs_affineGaussian hd hCsym hC hO hI hpsd hb h

end AffineHemigroup
