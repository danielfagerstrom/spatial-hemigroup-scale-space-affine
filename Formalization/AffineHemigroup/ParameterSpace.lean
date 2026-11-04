/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PathCondition
import AffineHemigroup.PolarReading
import AffineHemigroup.KernelsFromOrigin
import AffineHemigroup.ShapeAdapted
import AffineHemigroup.MatrixCalculus

/-!
# `lem:parameter-space`: stabilizers, orbits, and the parameter space `PD(d)`

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:parameter-space` (clauses (1)–(2)), with
its split children `lem:parameter-space-indexing` (clause (3)) and `lem:parameter-space-examples`
(clauses (4)–(5)). Wave 2, group C, Q-0281. Lean core only.

## The route

The blueprint's, with the compactness of a full law's stabilizer read in the space of operators
`L(ℝ^d)` (normed and proper), to which `lin` is a continuous linear equivalence: the bound
`‖A‖ ≤ T` on `Stab(μ)` comes from the continuous positive function
`B ↦ ∫ min(1, |Bx|) μ(dx)` on the unit sphere of `L(ℝ^d)` (in place of a convergent subsequence),
and closedness in the matrices from the bound `|det A⁻¹| ≤ C` on the bounded set.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- `lin` as a continuous linear equivalence of `Mat d` with the operators on `ℝ^d`. -/
noncomputable def linE : Mat d ≃L[ℝ] (Rd d →L[ℝ] Rd d) :=
  LinearEquiv.toContinuousLinearEquiv
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).toAlgEquiv.toLinearEquiv

theorem linE_apply (A : Mat d) : linE A = lin A := rfl

theorem push_mem_stab_iff {μ : Measure (Rd d)} {A : Mat d} :
    A ∈ stab μ ↔ A ∈ glSet d ∧ push A μ = μ := Iff.rfl

/-- **`lem:parameter-space`(1)**: `Stab(μ)` is a closed subgroup of `GL(d)`. -/
theorem stab_isClosedSubgroupGL (_hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    IsClosedSubgroupGL (stab μ) := by
  have hgl := (glSet_isClosedSubgroupGL (d := d)).1
  refine ⟨fun A h => h.1, ⟨hgl.one_mem, push_one μ⟩, fun A hA B hB => ⟨hgl.mul_mem A hA.1 B hB.1,
    by rw [← push_push, hB.2, hA.2]⟩, fun A hA => ⟨hgl.inv_mem A hA.1, ?_⟩, fun A hA hdet => ?_⟩
  · have hU : IsUnit A.det := hA.1
    conv_lhs => rw [← hA.2]
    rw [push_push, Matrix.nonsing_inv_mul _ hU, push_one]
  · -- closedness: `μ̂(Aᵀω) = μ̂(ω)` is a closed condition in `A`
    refine ⟨hdet, eq_of_charFun_eq fun ω => ?_⟩
    have hclosed : IsClosed {B : Mat d | charFun μ (lin Bᵀ ω) = charFun μ ω} := by
      refine isClosed_eq ?_ continuous_const
      have hc : Continuous fun B : Mat d => lin Bᵀ ω := by
        have he : (fun B : Mat d => lin Bᵀ ω) = fun B => WithLp.toLp 2 (Bᵀ *ᵥ ω.ofLp) := rfl
        rw [he]
        exact (PiLp.continuous_toLp 2 _).comp
          (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
      exact continuous_charFun.comp hc
    have hsub : stab μ ⊆ {B : Mat d | charFun μ (lin Bᵀ ω) = charFun μ ω} := by
      intro B hB
      have : charFun (push B μ) ω = charFun μ ω := by rw [hB.2]
      rwa [push, charFun_map_lin] at this
    have hmem : A ∈ {B : Mat d | charFun μ (lin Bᵀ ω) = charFun μ ω} :=
      closure_minimal hsub hclosed hA
    rw [push, charFun_map_lin]
    exact hmem

/-! ## Compactness of the stabilizer of a full law -/

/-- `B ↦ ∫ min(1, |Bx|) μ(dx)` is continuous on the operators. -/
theorem continuous_integral_min_norm (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    Continuous fun B : Rd d →L[ℝ] Rd d => ∫ x, min 1 ‖B x‖ ∂μ := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun B => ?_) (fun B => ?_)
    (integrable_const 1) ?_
  · exact (continuous_const.min B.continuous.norm).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (le_min zero_le_one (norm_nonneg _))]; exact min_le_left _ _
  · exact Eventually.of_forall fun x =>
      continuous_const.min ((continuous_id.clm_apply continuous_const).norm)

/-- **A full law has a bounded stabilizer**: `‖A‖ ≤ T` on `Stab(μ)`. -/
theorem stab_bounded (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hμ : IsFull μ) :
    ∃ T : ℝ, 0 < T ∧ ∀ A ∈ stab μ, ‖lin A‖ ≤ T := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  set f : (Rd d →L[ℝ] Rd d) → ℝ := fun B => ∫ x, min 1 ‖B x‖ ∂μ with hf
  have hfc : Continuous f := continuous_integral_min_norm μ
  have hS1 : (Metric.sphere (0 : Rd d →L[ℝ] Rd d) 1).Nonempty :=
    ⟨ContinuousLinearMap.id ℝ (Rd d), by simp [ContinuousLinearMap.norm_id]⟩
  obtain ⟨B0, hB0, hmin⟩ := (isCompact_sphere (0 : Rd d →L[ℝ] Rd d) 1).exists_isMinOn hS1
    hfc.continuousOn
  set c := f B0 with hc
  have hnn : ∀ (B : Rd d →L[ℝ] Rd d) x, 0 ≤ min 1 ‖B x‖ := fun B x =>
    le_min zero_le_one (norm_nonneg _)
  -- `c > 0` by fullness
  have hcpos : 0 < c := by
    rcases (integral_nonneg (f := fun x => min 1 ‖B0 x‖) (fun x => hnn B0 x)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hint : Integrable (fun x => min 1 ‖B0 x‖) μ :=
        Integrable.of_bound ((continuous_const.min B0.continuous.norm).aestronglyMeasurable) 1
          (Eventually.of_forall fun x => by
            rw [Real.norm_of_nonneg (hnn B0 x)]; exact min_le_left _ _)
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => hnn B0 x) hint).1 h.symm
      have hker : ∀ᵐ x ∂μ, x ∈ (LinearMap.ker (B0 : Rd d →ₗ[ℝ] Rd d) : Set (Rd d)) := by
        filter_upwards [hae] with x hx
        simp only [Pi.zero_apply] at hx
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have : ‖B0 x‖ = 0 := by
          rcases le_total 1 ‖B0 x‖ with h1 | h1
          · rw [min_eq_left h1] at hx; norm_num at hx
          · rw [min_eq_right h1] at hx; exact hx
        simpa using this
      have hne : LinearMap.ker (B0 : Rd d →ₗ[ℝ] Rd d) ≠ ⊤ := by
        intro htop
        have h0 : B0 = 0 := by
          refine ContinuousLinearMap.ext fun x => ?_
          have : x ∈ LinearMap.ker (B0 : Rd d →ₗ[ℝ] Rd d) := htop ▸ Submodule.mem_top
          simpa using this
        rw [h0] at hB0
        simp at hB0
      have h1 : μ (LinearMap.ker (B0 : Rd d →ₗ[ℝ] Rd d) : Set (Rd d)) = 1 := by
        rw [← prob_compl_eq_zero_iff (Submodule.closed_of_finiteDimensional _).measurableSet]
        exact ae_iff.1 hker
      exact absurd h1 (hμ _ hne).ne
  -- `g(t) = ∫ min(1, |y|/t) μ(dy) → 0`
  have hg : Tendsto (fun t : ℝ => ∫ y, min 1 (‖y‖ / t) ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun (t : ℝ) y => min 1 (‖y‖ / t)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (Eventually.of_forall fun t => (continuous_const.min
        (continuous_norm.div_const t)).aestronglyMeasurable)
      (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (le_min zero_le_one (by positivity))]; exact min_le_left _ _)
      (integrable_const 1)
      (Eventually.of_forall fun y => by
        have h1 : Tendsto (fun t : ℝ => ‖y‖ / t) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 : Tendsto (fun n : ℝ => min 1 (‖y‖ / n)) atTop (𝓝 (min 1 0)) :=
          ((continuous_const.min continuous_id).tendsto (0 : ℝ)).comp h1
        rw [min_eq_right zero_le_one] at h2
        exact h2)
    simpa using this
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hg.eventually (gt_mem_nhds hcpos))
  refine ⟨max T0 1, by positivity, fun A hA => ?_⟩
  by_contra hlt
  push Not at hlt
  set t := ‖lin A‖ with ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hlt.le)
  have hB : t⁻¹ • lin A ∈ Metric.sphere (0 : Rd d →L[ℝ] Rd d) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ htpos.ne']
  have h1 := hmin hB
  have h2 : f (t⁻¹ • lin A) = ∫ y, min 1 (‖y‖ / t) ∂μ := by
    simp only [hf, _root_.smul_apply, norm_smul, norm_inv, Real.norm_of_nonneg
      htpos.le]
    conv_rhs => rw [← hA.2]
    rw [push, integral_map (lin A).continuous.aemeasurable
      ((continuous_const.min (continuous_norm.div_const t)).aestronglyMeasurable)]
    congr 1; funext x; rw [inv_mul_eq_div]
  have h3 := hT0 t ((le_max_left _ _).trans hlt.le)
  simp only [mem_setOf_eq] at h1
  rw [h2] at h1
  change c ≤ _ at h1
  linarith

/-- **`lem:parameter-space`(1)**: if `μ` is full, `Stab(μ)` is compact. -/
theorem stab_isCompact_of_isFull (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsFull μ) : IsCompact (stab μ) := by
  obtain ⟨T, hT, hbound⟩ := stab_bounded hd μ hμ
  have hG := stab_isClosedSubgroupGL hd μ
  set K : Set (Mat d) := linE.symm '' Metric.closedBall 0 T with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 T).image linE.symm.continuous
  have hsub : stab μ ⊆ K := fun A hA =>
    ⟨lin A, by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound A hA,
      by rw [← linE_apply, ContinuousLinearEquiv.symm_apply_apply]⟩
  -- `|det| ≤ C` on `K`, so `|det A| ≥ 1/C` on the stabilizer
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun M : Mat d => M.det)
    (continuous_id.matrix_det).continuousOn
  set C' := max C 1 with hC'
  have hdet : ∀ A ∈ stab μ, 1 / C' ≤ |A.det| := by
    intro A hA
    have hAinv := hG.inv_mem A hA
    have h1 : |A⁻¹.det| ≤ C' := by
      have := hC _ (hsub hAinv)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hU : IsUnit A.det := hA.1
    have h2 : A.det * A⁻¹.det = 1 := by
      rw [← det_mul, Matrix.mul_nonsing_inv _ hU, det_one]
    have h3 : |A.det| * |A⁻¹.det| = 1 := by rw [← abs_mul, h2, abs_one]
    have hpos : 0 < |A⁻¹.det| := by
      rcases (abs_nonneg A⁻¹.det).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at h3; norm_num at h3
    rw [div_le_iff₀ (by positivity)]
    calc 1 = |A.det| * |A⁻¹.det| := h3.symm
      _ ≤ |A.det| * C' := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hclosed : IsClosed (stab μ) := by
    refine isClosed_of_closure_subset fun A hA => ?_
    have hF : IsClosed {M : Mat d | 1 / C' ≤ |M.det|} :=
      isClosed_le continuous_const (continuous_id.matrix_det.abs)
    have hA' : 1 / C' ≤ |A.det| := closure_minimal (fun B hB => hdet B hB) hF hA
    have hpos : 0 < |A.det| := lt_of_lt_of_le (by positivity) hA'
    exact hG.isClosed A hA (isUnit_iff_ne_zero.2 (abs_pos.1 hpos))
  exact hKc.of_isClosed_subset hclosed hsub

/-- **`lem:parameter-space`(1)**: a law whose stabilizer is not compact is carried by a proper
linear subspace. -/
theorem carried_by_subspace_of_not_isCompact (hd : 1 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (h : ¬ IsCompact (stab μ)) :
    ∃ V : Submodule ℝ (Rd d), V ≠ ⊤ ∧ μ (V : Set (Rd d)) = 1 := by
  by_contra hcon
  push Not at hcon
  exact h (stab_isCompact_of_isFull hd μ fun V hV =>
    lt_of_le_of_ne prob_le_one (hcon V hV))

/-- **`lem:parameter-space`(1)**, the example: for `d ≥ 2` such a law need not be `δ₀`; the
stabilizer of `δ_{e₁}` contains every `A ∈ GL(d)` with `Ae₁ = e₁`, and is not compact. -/
theorem stab_dirac_ebasis (hd : 2 ≤ d) :
    (∀ A ∈ glSet d, lin A (ebasis ⟨0, by omega⟩) = ebasis ⟨0, by omega⟩ →
      A ∈ stab (Measure.dirac (ebasis (⟨0, by omega⟩ : Fin d)))) ∧
    ¬ IsCompact (stab (Measure.dirac (ebasis (⟨0, by omega⟩ : Fin d)))) ∧
    Measure.dirac (ebasis (⟨0, by omega⟩ : Fin d)) ≠ Measure.dirac 0 := by
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have hfix : ∀ A ∈ glSet d, lin A (ebasis i₀) = ebasis i₀ →
      A ∈ stab (Measure.dirac (ebasis i₀)) := fun A hA hAe =>
    ⟨hA, by
      ext s hs
      rw [push, Measure.map_apply (lin A).continuous.measurable hs,
        Measure.dirac_apply' _ ((lin A).continuous.measurable hs), Measure.dirac_apply' _ hs]
      by_cases h : ebasis i₀ ∈ s <;> simp [h, hAe, Set.indicator]⟩
  refine ⟨hfix, fun hcomp => ?_, fun h => ?_⟩
  · -- the transvections `I + t E₀₁` fix `e₁` and are unbounded
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (f := fun M : Mat d => M i₀ i₁)
      ((continuous_apply i₁).comp (continuous_apply i₀)).continuousOn
    set t := C + 1
    have hmem : Matrix.transvection i₀ i₁ t ∈ stab (Measure.dirac (ebasis i₀)) := by
      refine hfix _ ?_ ?_
      · change IsUnit (Matrix.transvection i₀ i₁ t).det
        rw [Matrix.det_transvection_of_ne _ _ h01]; exact isUnit_one
      · apply WithLp.ofLp_injective 2
        rw [ofLp_lin]
        ext k
        simp [Matrix.transvection, ebasis, Matrix.mulVec, dotProduct,
          Matrix.single_apply, h01.symm, Matrix.one_apply]
    have := hC _ hmem
    simp [Matrix.transvection, h01, Real.norm_eq_abs] at this
    have h2 : C + 1 ≤ |C + 1| := le_abs_self _
    linarith
  · have := congrArg (fun m : Measure (Rd d) => m {0}) h
    rw [Measure.dirac_apply' _ (measurableSet_singleton 0),
      Measure.dirac_apply' _ (measurableSet_singleton 0)] at this
    have he : ebasis i₀ ≠ (0 : Rd d) := by
      intro h0
      have := congrArg (fun y : Rd d => y i₀) h0
      simp [ebasis] at this
    simp [he] at this

/-! ## Rotation-invariant laws (`lem:parameter-space`(2)) -/

/-- The matrix of a linear isometry is orthogonal. -/
theorem isoMat_mem_orthSet (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : isoMat Q ∈ orthSet d := by
  change isoMat Q ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff]
  apply lin_injective
  rw [lin_mul, lin_isoMat, lin_isoMat_transpose, lin_one]
  refine ContinuousLinearMap.ext fun x => ?_
  simp

/-- `⟨y, U diag(w) Uᵀ y⟩ = wᵢ` at `y = Ueᵢ`. -/
theorem quad_udiag_lin_single {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (i : Fin d) :
    quad (udiag U w) (lin U (EuclideanSpace.single i 1)) = w i := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  have hx : lin Uᵀ (lin U (EuclideanSpace.single i 1)) = EuclideanSpace.single i 1 := by
    rw [show lin Uᵀ (lin U (EuclideanSpace.single i 1)) =
      lin (Uᵀ * U) (EuclideanSpace.single i 1) by rw [lin_mul]; rfl, hU', lin_one]; rfl
  rw [udiag, quad_orth_diag, hx]
  simp [PiLp.single_apply]

theorem udiag_pow {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (n : ℕ) :
    udiag U w ^ n = udiag U (fun i => w i ^ n) := by
  induction n with
  | zero => simp [udiag_one hU]
  | succ n ih => rw [pow_succ, ih, udiag_mul hU]; congr 1

/-- **`lem:parameter-space`(2)**: a rotation-invariant law other than `δ₀` is full, and its
stabilizer is `O(d)`. -/
theorem isFull_of_isRotationInvariant (hd : 1 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hrot : IsRotationInvariant μ) (hne : μ ≠ Measure.dirac 0) :
    IsFull μ ∧ stab μ = orthSet d := by
  haveI : NeZero d := ⟨by omega⟩
  have hfull : IsFull μ := by
    intro V hV
    by_contra hlt
    push Not at hlt
    have hV1 : μ (V : Set (Rd d)) = 1 := le_antisymm prob_le_one hlt
    -- a unit normal `u` to `V`
    have hperp : Vᗮ ≠ ⊥ := fun h => hV (Submodule.orthogonal_eq_bot_iff.1 h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    set u := ‖v‖⁻¹ • v with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
    have huV : u ∈ Vᗮ := Submodule.smul_mem _ _ hv
    have hslab : ∀ w : Rd d, ‖w‖ = 1 → μ {x | ⟪w, x⟫ = 0} = 1 := by
      intro w hw
      set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (u - w))ᗮ with hQ
      have hQu : Q u = w := Submodule.reflection_sub (hu1.trans hw.symm)
      have hpush := hrot _ (isoMat_mem_orthSet Q)
      have hmeas : MeasurableSet {x : Rd d | ⟪w, x⟫ = 0} :=
        measurableSet_eq_fun (by fun_prop) measurable_const
      have hpre : lin (isoMat Q) ⁻¹' {x : Rd d | ⟪w, x⟫ = 0} = {x | ⟪u, x⟫ = 0} := by
        ext x
        simp only [mem_preimage, mem_setOf_eq, lin_isoMat]
        rw [← hQu]
        simp [LinearIsometryEquiv.inner_map_map]
      have h1 : μ {x | ⟪u, x⟫ = 0} = 1 :=
        le_antisymm prob_le_one (hV1 ▸ measure_mono fun x hx =>
          (Submodule.mem_orthogonal' V u).1 huV x hx)
      rw [← hpush, push, Measure.map_apply (lin _).continuous.measurable hmeas, hpre, h1]
    -- every coordinate vanishes `μ`-a.e.
    have hzero : μ ({0}ᶜ : Set (Rd d)) = 0 := by
      have hsub : ({0}ᶜ : Set (Rd d)) ⊆ ⋃ j : Fin d, {x | ⟪ebasis j, x⟫ = 0}ᶜ := by
        intro x hx
        by_contra hcon
        simp only [mem_iUnion, mem_compl_iff, mem_setOf_eq, not_exists, not_not] at hcon
        apply hx
        ext j
        have := hcon j
        simp [ebasis, EuclideanSpace.inner_single_left] at this
        simpa using this
      refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
      have hj : ‖ebasis j‖ = 1 := by simp [ebasis]
      rw [prob_compl_eq_zero_iff (measurableSet_eq_fun (by fun_prop) measurable_const)]
      exact hslab _ hj
    apply hne
    have hae : ∀ᵐ x ∂μ, x ∈ ({0} : Set (Rd d)) := by
      rw [ae_iff]; exact hzero
    have h1 : μ {0} = 1 := by
      rw [← prob_compl_eq_zero_iff (measurableSet_singleton 0)]; exact hzero
    rw [← Measure.restrict_eq_self_of_ae_mem hae, Measure.restrict_singleton, h1, one_smul]
  refine ⟨hfull, Set.Subset.antisymm (fun A hA => ?_) fun Q hQ =>
    ⟨orthSet_subset_glSet hQ, hrot Q hQ⟩⟩
  -- `A = PQ` with `P = (AAᵀ)^{1/2}`; `P ∈ Stab(μ)`, compact, forces `P = I`
  have hG := stab_isClosedSubgroupGL hd μ
  have hcomp := stab_isCompact_of_isFull hd μ hfull
  have horth : orthSet d ⊆ stab μ := fun Q hQ => ⟨orthSet_subset_glSet hQ, hrot Q hQ⟩
  set S := A * Aᵀ with hS
  have hSpd : S.PosDef := by
    have := (posDef_act_iff hA.1 1).2 PosDef.one
    simpa [act] using this
  set P := msqrt S with hP
  set Q := P⁻¹ * A with hQ
  have hQQ : Q * Qᵀ = 1 := by
    have h := relStep_self hSpd
    calc Q * Qᵀ = P⁻¹ * S * P⁻¹ := by
          rw [hQ, transpose_mul, hP, msqrt_inv_transpose, hS]; simp only [Matrix.mul_assoc]
      _ = 1 := h
  have hQo : Q ∈ orthSet d := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hQQ
  have hPA : P * Q = A := by
    rw [hQ, ← Matrix.mul_assoc, msqrt_mul_inv hSpd, Matrix.one_mul]
  have hPmem : P ∈ stab μ := by
    have hP' : P = A * Qᵀ := by
      rw [← hPA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [hP']
    exact hG.mul_mem A hA _ (horth (transpose_mem_orthSet hQo))
  -- `S = P² ∈ Stab(μ)`, compact, forces `S = I`
  have hSmem : S ∈ stab μ := by
    have := hG.mul_mem P hPmem P hPmem
    rwa [hP, msqrt_mul_self hSpd.posSemidef] at this
  obtain ⟨U, s, hUU, hSU⟩ := exists_udiag hSpd.isHermitian
  have hspos : ∀ i, 0 < s i := (udiag_posDef_iff hUU s).1 (hSU ▸ hSpd)
  have hpowmem : ∀ (M : Mat d), M ∈ stab μ → ∀ n : ℕ, M ^ n ∈ stab μ := by
    intro M hM n
    induction n with
    | zero => rw [pow_zero]; exact hG.one_mem
    | succ n ih => rw [pow_succ]; exact hG.mul_mem _ ih _ hM
  have hSinv : S⁻¹ = udiag U (fun i => (s i)⁻¹) := by
    rw [hSU]
    refine Matrix.inv_eq_right_inv ?_
    rw [udiag_mul hUU]
    rw [show (s * fun i => (s i)⁻¹) = fun _ => (1 : ℝ) by
      funext i; simp [mul_inv_cancel₀ (hspos i).ne']]
    exact udiag_one hUU
  have hs1 : ∀ i, s i = 1 := by
    intro i
    set v : Rd d := lin U (EuclideanSpace.single i 1) with hv
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (f := fun M : Mat d => quad M v)
      (by
        have : Continuous fun M : Mat d => quad M v := by
          simp only [quad_eq_dotProduct]
          exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
        exact this.continuousOn)
    have hbig : ∀ w : ℝ, 1 < w → (∀ n : ℕ, w ^ n ≤ C) → False := fun w hw h => by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hw
      exact absurd (h n) (not_le.2 hn)
    rcases lt_trichotomy (s i) 1 with hlt | heq | hgt
    · exfalso
      refine hbig (s i)⁻¹ (one_lt_inv_iff₀.2 ⟨hspos i, hlt⟩) fun n => ?_
      have := hC _ (hpowmem _ (hG.inv_mem S hSmem) n)
      rw [hSinv, udiag_pow hUU, quad_udiag_lin_single hUU, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    · exact heq
    · exfalso
      refine hbig (s i) hgt fun n => ?_
      have := hC _ (hpowmem _ hSmem n)
      rw [hSU, udiag_pow hUU, quad_udiag_lin_single hUU, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
  have hS1 : S = 1 := by
    rw [hSU, show s = fun _ => (1 : ℝ) from funext hs1, udiag_one hUU]
  exact (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hS1

/-! ## `lem:parameter-space-indexing` (`lem:parameter-space`(3)) -/

/-- The image of a full law under `B ∈ GL(d)` is full. -/
theorem isFull_push {μ : Measure (Rd d)} (hμ : IsFull μ) {B : Mat d} (hB : B ∈ glSet d) :
    IsFull (push B μ) := by
  intro V hV
  have hU : IsUnit B.det := hB
  set W : Submodule ℝ (Rd d) := Submodule.comap (lin B : Rd d →ₗ[ℝ] Rd d) V with hW
  have hWne : W ≠ ⊤ := by
    intro htop
    apply hV
    rw [eq_top_iff]
    intro y _
    have : lin B⁻¹ y ∈ W := htop ▸ Submodule.mem_top
    rw [hW, Submodule.mem_comap] at this
    simpa [lin_mul_inv_apply hU] using this
  rw [push, Measure.map_apply (lin B).continuous.measurable
    (Submodule.closed_of_finiteDimensional V).measurableSet]
  exact hμ W hWne

/-- `δ₀` is not full (`d ≥ 1`). -/
theorem not_isFull_dirac_zero (hd : 1 ≤ d) : ¬ IsFull (Measure.dirac (0 : Rd d)) := by
  haveI : NeZero d := ⟨by omega⟩
  intro h
  have hne : (⊥ : Submodule ℝ (Rd d)) ≠ ⊤ := by
    intro hb
    have : ebasis (0 : Fin d) ∈ (⊥ : Submodule ℝ (Rd d)) := hb ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at this
    have := congrArg (fun y : Rd d => y 0) this
    simp [ebasis] at this
  have := h ⊥ hne
  rw [Submodule.bot_coe, Measure.dirac_apply' _ (measurableSet_singleton 0)] at this
  simp at this

/-- `A ∈ Stab(B_*μ)` exactly when `B⁻¹AB ∈ Stab(μ)`. -/
theorem mem_stab_push_iff {μ : Measure (Rd d)} {B : Mat d} (hB : B ∈ glSet d) (A : Mat d) :
    A ∈ stab (push B μ) ↔ B⁻¹ * A * B ∈ stab μ := by
  have hU : IsUnit B.det := hB
  have hgl := (glSet_isClosedSubgroupGL (d := d)).1
  constructor
  · rintro ⟨hA, h⟩
    refine ⟨hgl.mul_mem _ (hgl.mul_mem _ (hgl.inv_mem B hB) A hA) B hB, ?_⟩
    rw [← push_push, ← push_push, h, push_push, Matrix.nonsing_inv_mul _ hU, push_one]
  · rintro ⟨hA, h⟩
    have hA' : A = B * (B⁻¹ * A * B) * B⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
    refine ⟨?_, ?_⟩
    · rw [hA']
      exact hgl.mul_mem _ (hgl.mul_mem _ hB _ hA) _ (hgl.inv_mem B hB)
    · rw [hA', ← push_push, ← push_push, push_push B⁻¹ B, Matrix.nonsing_inv_mul _ hU,
        push_one, h]

/-- The relative orthogonal factor: `Q := (AΣAᵀ)^{-1/2} A Σ^{1/2}` is orthogonal. -/
theorem msqrt_conj_orth {A S : Mat d} (hA : A ∈ glSet d) (hS : S.PosDef) :
    (msqrt (act A S))⁻¹ * A * msqrt S ∈ orthSet d := by
  have hAS : (act A S).PosDef := (posDef_act_iff hA S).2 hS
  have h := relStep_self hAS
  apply (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2
  change (msqrt (act A S))⁻¹ * A * msqrt S * ((msqrt (act A S))⁻¹ * A * msqrt S)ᵀ = 1
  rw [transpose_mul, transpose_mul, msqrt_transpose, msqrt_inv_transpose]
  calc (msqrt (act A S))⁻¹ * A * msqrt S * (msqrt S * (Aᵀ * (msqrt (act A S))⁻¹))
      = (msqrt (act A S))⁻¹ * (A * (msqrt S * msqrt S) * Aᵀ) * (msqrt (act A S))⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [msqrt_mul_self hS.posSemidef]; exact h

/-- The covariant map built from a law with stabilizer `O(d)`: `Σ ↦ (Σ^{1/2})_*ν`. -/
theorem push_msqrt_covariant {ν : Measure (Rd d)} (hν : ∀ Q ∈ orthSet d, push Q ν = ν)
    {A S : Mat d} (hA : A ∈ glSet d) (hS : S.PosDef) :
    push A (push (msqrt S) ν) = push (msqrt (act A S)) ν := by
  have hAS : (act A S).PosDef := (posDef_act_iff hA S).2 hS
  have hQ := msqrt_conj_orth hA hS
  have hfac : A * msqrt S = msqrt (act A S) * ((msqrt (act A S))⁻¹ * A * msqrt S) := by
    simp only [← Matrix.mul_assoc, msqrt_mul_inv hAS, Matrix.one_mul]
  rw [push_push, hfac, ← push_push, hν _ hQ]

/-- **`lem:parameter-space-indexing`**, the equivalence: for a full `μ₀`, (a) `Orb(μ₀)` has a
rotation-invariant member; (b) `Stab(μ₀) = C O(d) C⁻¹` for some `C ∈ GL(d)`; (c) there is a map
`Σ ↦ μ_Σ` from `PD(d)` into `Orb(μ₀)` with `A_*μ_Σ = μ_{AΣAᵀ}`. -/
theorem parameter_space_tfae (hd : 1 ≤ d) (μ₀ : Measure (Rd d)) [IsProbabilityMeasure μ₀]
    (hfull : IsFull μ₀) :
    List.TFAE
      [∃ ν ∈ orb μ₀, IsRotationInvariant ν,
       ∃ C ∈ glSet d, stab μ₀ = {A : Mat d | ∃ Q ∈ orthSet d, A = C * Q * C⁻¹},
       ∃ m : Mat d → Measure (Rd d), (∀ S : Mat d, S.PosDef → m S ∈ orb μ₀) ∧
         ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (m S) = m (act A S)] := by
  have hgl := (glSet_isClosedSubgroupGL (d := d)).1
  tfae_have 1 → 2 := by
    rintro ⟨ν, ⟨B, hB, rfl⟩, hrot⟩
    have hU : IsUnit B.det := hB
    have hfullν := isFull_push hfull hB
    have hne : push B μ₀ ≠ Measure.dirac 0 := fun h => not_isFull_dirac_zero hd (h ▸ hfullν)
    have hstab := (isFull_of_isRotationInvariant hd _ hrot hne).2
    refine ⟨B⁻¹, hgl.inv_mem B hB, Set.ext fun A => ?_⟩
    have key : A ∈ stab μ₀ ↔ B * A * B⁻¹ ∈ stab (push B μ₀) := by
      rw [mem_stab_push_iff hB]
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    rw [key, hstab]
    constructor
    · intro h
      refine ⟨_, h, ?_⟩
      simp only [Matrix.nonsing_inv_nonsing_inv _ hU, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    · rintro ⟨Q, hQ, rfl⟩
      simp only [Matrix.nonsing_inv_nonsing_inv _ hU, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
  tfae_have 2 → 3 := by
    rintro ⟨C, hC, hstab⟩
    have hU : IsUnit C.det := hC
    set ν := push C⁻¹ μ₀ with hν
    have hνrot : ∀ Q ∈ orthSet d, push Q ν = ν := by
      intro Q hQ
      have hmem : Q ∈ stab ν := by
        rw [hν, mem_stab_push_iff (hgl.inv_mem C hC), Matrix.nonsing_inv_nonsing_inv _ hU, hstab]
        exact ⟨Q, hQ, rfl⟩
      exact hmem.2
    refine ⟨fun S => push (msqrt S) ν, fun S hS => ⟨msqrt S * C⁻¹,
      hgl.mul_mem _ (msqrt_mem_glSet hS) _ (hgl.inv_mem C hC), by
        show push (msqrt S) (push C⁻¹ μ₀) = push (msqrt S * C⁻¹) μ₀
        rw [push_push]⟩,
      fun A hA S hS => push_msqrt_covariant hνrot hA hS⟩
  tfae_have 3 → 1 := by
    rintro ⟨m, hm, hcov⟩
    refine ⟨m 1, hm 1 PosDef.one, fun Q hQ => ?_⟩
    rw [hcov Q (orthSet_subset_glSet hQ) 1 PosDef.one, act_orth_one hQ]
  tfae_finish

/-- The member `μ_I` of a map as in (c), and `μ_Σ = (Σ^{1/2})_*μ_I`. -/
theorem index_props (hd : 1 ≤ d) {μ₀ : Measure (Rd d)} [IsProbabilityMeasure μ₀]
    (hfull : IsFull μ₀) {m : Mat d → Measure (Rd d)}
    (hm : ∀ S : Mat d, S.PosDef → m S ∈ orb μ₀)
    (hcov : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (m S) = m (act A S)) :
    IsProbabilityMeasure (m 1) ∧ IsFull (m 1) ∧ stab (m 1) = orthSet d ∧
      ∀ S : Mat d, S.PosDef → m S = push (msqrt S) (m 1) := by
  obtain ⟨B, hB, hB1⟩ := hm 1 PosDef.one
  haveI : IsProbabilityMeasure (m 1) := by rw [hB1]; infer_instance
  have hfull1 : IsFull (m 1) := hB1 ▸ isFull_push hfull hB
  have hrot : IsRotationInvariant (m 1) := fun Q hQ => by
    rw [hcov Q (orthSet_subset_glSet hQ) 1 PosDef.one, act_orth_one hQ]
  have hne : m 1 ≠ Measure.dirac 0 := fun h => not_isFull_dirac_zero hd (h ▸ hfull1)
  refine ⟨inferInstance, hfull1, (isFull_of_isRotationInvariant hd _ hrot hne).2, fun S hS => ?_⟩
  rw [hcov _ (msqrt_mem_glSet hS) 1 PosDef.one, act_msqrt_one hS.posSemidef]

/-- **`lem:parameter-space-indexing`**: every map as in (c) is a bijection of `PD(d)` onto
`Orb(μ₀)`. -/
theorem parameter_space_index_bijOn (hd : 1 ≤ d) (μ₀ : Measure (Rd d))
    [IsProbabilityMeasure μ₀] (hfull : IsFull μ₀) (m : Mat d → Measure (Rd d))
    (hm : ∀ S : Mat d, S.PosDef → m S ∈ orb μ₀)
    (hcov : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (m S) = m (act A S)) :
    BijOn m (pdSet d) (orb μ₀) := by
  have hgl := (glSet_isClosedSubgroupGL (d := d)).1
  obtain ⟨hprob, -, hstab, hform⟩ := index_props hd hfull hm hcov
  refine ⟨fun S hS => hm S hS, fun S hS S' hS' h => ?_, fun ν hν => ?_⟩
  · -- `(Σ'^{-1/2}Σ^{1/2})_*μ_I = μ_I`, so the factor is orthogonal
    have hU' : IsUnit (msqrt S').det := msqrt_mem_glSet hS'
    have hR : (msqrt S')⁻¹ * msqrt S ∈ stab (m 1) := by
      refine ⟨hgl.mul_mem _ (hgl.inv_mem _ (msqrt_mem_glSet hS')) _ (msqrt_mem_glSet hS), ?_⟩
      rw [← push_push, ← hform S hS, h, hform S' hS', push_push, Matrix.nonsing_inv_mul _ hU',
        push_one]
    rw [hstab] at hR
    have hRR := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hR
    change (msqrt S')⁻¹ * msqrt S * ((msqrt S')⁻¹ * msqrt S)ᵀ = 1 at hRR
    rw [transpose_mul, msqrt_transpose, msqrt_inv_transpose] at hRR
    have : relStep S' S = 1 := by
      rw [relStep, ← msqrt_mul_self hS.posSemidef]
      simpa only [Matrix.mul_assoc] using hRR
    calc S = msqrt S' * relStep S' S * msqrt S' := (msqrt_mul_relStep hS' S).symm
      _ = S' := by rw [this, Matrix.mul_one, msqrt_mul_self hS'.posSemidef]
  · obtain ⟨A, hA, rfl⟩ := hν
    obtain ⟨B, hB, hB1⟩ := hm 1 PosDef.one
    have hUB : IsUnit B.det := hB
    have hAB := hgl.mul_mem _ hA _ (hgl.inv_mem B hB)
    refine ⟨act (A * B⁻¹) 1, (posDef_act_iff hAB 1).2 PosDef.one, ?_⟩
    rw [← hcov _ hAB 1 PosDef.one, hB1, push_push, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUB,
      Matrix.mul_one]

/-- **`lem:parameter-space-indexing`**: two maps as in (c) differ by a constant,
`μ'_Σ = μ_{cΣ}` with `c > 0`. -/
theorem parameter_space_index_unique (hd : 1 ≤ d) (μ₀ : Measure (Rd d))
    [IsProbabilityMeasure μ₀] (hfull : IsFull μ₀) (m m' : Mat d → Measure (Rd d))
    (hm : ∀ S : Mat d, S.PosDef → m S ∈ orb μ₀)
    (hcov : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (m S) = m (act A S))
    (hm' : ∀ S : Mat d, S.PosDef → m' S ∈ orb μ₀)
    (hcov' : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → push A (m' S) = m' (act A S)) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : Mat d, S.PosDef → m' S = m (c • S) := by
  have hbij := parameter_space_index_bijOn hd μ₀ hfull m hm hcov
  -- `h := m⁻¹ ∘ m'` on `PD(d)`
  set h : Mat d → Mat d := fun S => Function.invFunOn m (pdSet d) (m' S) with hh
  have hspec : ∀ S : Mat d, S.PosDef → h S ∈ pdSet d ∧ m (h S) = m' S := fun S hS =>
    ⟨Function.invFunOn_mem (hbij.surjOn (hm' S hS)),
      Function.invFunOn_eq (hbij.surjOn (hm' S hS))⟩
  have hcovh : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef → h (act A S) = act A (h S) := by
    intro A hA S hS
    have hAS : (act A S).PosDef := (posDef_act_iff hA S).2 hS
    obtain ⟨h1, h2⟩ := hspec S hS
    obtain ⟨h3, h4⟩ := hspec _ hAS
    refine hbij.injOn h3 ((posDef_act_iff hA _).2 h1) ?_
    rw [h4, ← hcov' A hA S hS, ← h2, hcov A hA _ h1]
  obtain ⟨c, hc, hcS⟩ := affine_gauge h (fun S hS => (hspec S hS).1) hcovh
  refine ⟨c, hc, fun S hS => ?_⟩
  rw [← (hspec S hS).2, hcS S hS]

/-! ## `lem:parameter-space-examples` (`lem:parameter-space`(4)–(5)) -/

/-- **`lem:parameter-space-examples`(5)**: `{AAᵀ : A ∈ GL(d)} = PD(d)`. -/
theorem gram_glSet_eq_pdSet : {S : Mat d | ∃ A ∈ glSet d, S = A * Aᵀ} = pdSet d := by
  ext S
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := (posDef_act_iff hA 1).2 PosDef.one
    simp only [act, Matrix.mul_one] at this
    exact this
  · intro hS
    refine ⟨msqrt S, msqrt_mem_glSet hS, ?_⟩
    rw [msqrt_transpose, msqrt_mul_self (show S.PosDef from hS).posSemidef]

/-- **`lem:parameter-space-examples`(5)**: for a wedge datum with `O(d) ⊆ G` and a
`(G, W)`-cascade family of kernels, `μ_I` is rotation invariant and full,
`Stab(μ_I) = O(d)`, and `Σ ↦ μ_Σ` is injective on `{AAᵀ : A ∈ G}`. -/
theorem parameter_space_scheme (hd : 1 ≤ d) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (hO : orthSet d ⊆ G) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) :
    IsRotationInvariant (μ 0 1) ∧ IsFull (μ 0 1) ∧ stab (μ 0 1) = orthSet d ∧
      InjOn (fun S => μ 0 S) {S : Mat d | ∃ A ∈ G, S = A * Aᵀ} := by
  have h01 := wedge_zero_one_mem hW
  haveI : IsProbabilityMeasure (μ 0 1) := hμ.isProbability _ h01
  have hcov1 : ∀ A ∈ G, push A (μ 0 1) = μ 0 (A * Aᵀ) := fun A hA => by
    have := hμ.covariant A hA _ h01
    simpa [act] using this
  have hrot : IsRotationInvariant (μ 0 1) := fun Q hQ => by
    rw [hcov1 Q (hO hQ)]
    have := act_orth_one hQ
    simp only [act, Matrix.mul_one] at this
    rw [this]
  obtain ⟨hfull, hstab⟩ := isFull_of_isRotationInvariant hd _ hrot hμ.nondegenerate
  refine ⟨hrot, hfull, hstab, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ h
  have hAgl := hW.closedSubgroup.subset_gl hA
  have hBgl := hW.closedSubgroup.subset_gl hB
  have hUB : IsUnit B.det := hBgl
  simp only at h
  rw [← hcov1 A hA, ← hcov1 B hB] at h
  have hR : B⁻¹ * A ∈ stab (μ 0 1) := by
    have hgl := (glSet_isClosedSubgroupGL (d := d)).1
    refine ⟨hgl.mul_mem _ (hgl.inv_mem B hBgl) A hAgl, ?_⟩
    rw [← push_push, h, push_push, Matrix.nonsing_inv_mul _ hUB, push_one]
  rw [hstab] at hR
  have hRR := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hR
  change B⁻¹ * A * (B⁻¹ * A)ᵀ = 1 at hRR
  calc A * Aᵀ = B * (B⁻¹ * A * (B⁻¹ * A)ᵀ) * Bᵀ := by
        rw [transpose_mul, Matrix.transpose_nonsing_inv]
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUB, Matrix.one_mul]
        rw [Matrix.mul_assoc, Matrix.mul_assoc,
          show (Bᵀ)⁻¹ * Bᵀ = 1 from Matrix.nonsing_inv_mul _ (by rw [det_transpose]; exact hUB),
          Matrix.mul_one]
    _ = B * Bᵀ := by rw [hRR, Matrix.mul_one]

/-! ### The orbit of a finite sum of point masses (`lem:parameter-space-examples`(4)) -/

section Atoms

open Classical

theorem ebasis_injective : Function.Injective (ebasis : Fin d → Rd d) := by
  intro i j h
  by_contra hij
  have := congrArg (fun y : Rd d => y i) h
  simp [ebasis, hij] at this

/-- The mass of a set under `∑ⱼ pⱼ δ_{xⱼ}`. -/
theorem atoms_apply (p : Fin d → ℝ) (x : Fin d → Rd d) (s : Set (Rd d)) :
    (∑ j, ENNReal.ofReal (p j) • Measure.dirac (x j)) s =
      ∑ j, if x j ∈ s then ENNReal.ofReal (p j) else 0 := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : x j ∈ s <;> simp [h]

/-- The image of `∑ⱼ pⱼ δ_{xⱼ}` under `A`. -/
theorem push_atoms (A : Mat d) (p : Fin d → ℝ) (x : Fin d → Rd d) :
    push A (∑ j, ENNReal.ofReal (p j) • Measure.dirac (x j)) =
      ∑ j, ENNReal.ofReal (p j) • Measure.dirac (lin A (x j)) := by
  ext s hs
  rw [push, Measure.map_apply (lin A).continuous.measurable hs, atoms_apply, atoms_apply]
  simp only [Set.mem_preimage]

/-- **`lem:parameter-space-examples`(4)**: for distinct `p_j > 0` with `∑ p_j = 1`,
`μ₀ = ∑_j p_j δ_{e_j}` is full with trivial stabilizer, `A ↦ A_*μ₀` is a bijection of `GL(d)`
onto `Orb(μ₀)`, and no member of the orbit is rotation invariant. -/
theorem parameter_space_atoms (hd : 1 ≤ d) (p : Fin d → ℝ) (hp : ∀ j, 0 < p j)
    (hinj : Function.Injective p) (hsum : ∑ j, p j = 1) :
    let μ₀ : Measure (Rd d) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac (ebasis j)
    IsFull μ₀ ∧ stab μ₀ = {1} ∧ BijOn (fun A => push A μ₀) (glSet d) (orb μ₀) ∧
      ∀ ν ∈ orb μ₀, ¬ IsRotationInvariant ν := by
  intro μ₀
  haveI : NeZero d := ⟨by omega⟩
  have hgl := (glSet_isClosedSubgroupGL (d := d)).1
  have hmass : ∀ (A : Mat d) (s : Set (Rd d)), push A μ₀ s =
      ∑ j, if lin A (ebasis j) ∈ s then ENNReal.ofReal (p j) else 0 := fun A s => by
    rw [push_atoms, atoms_apply]
  have hμ₀ : ∀ s, μ₀ s = ∑ j, if ebasis j ∈ s then ENNReal.ofReal (p j) else 0 := fun s =>
    atoms_apply p ebasis s
  haveI hprob : IsProbabilityMeasure μ₀ := ⟨by
    rw [hμ₀]
    simp only [Set.mem_univ, if_true]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hp j).le), hsum, ENNReal.ofReal_one]⟩
  -- the atom at `y` of `A_*μ₀`
  have hatom : ∀ (A : Mat d), A ∈ glSet d → ∀ j, push A μ₀ {lin A (ebasis j)} = ENNReal.ofReal (p j) := by
    intro A hA j
    have hinjA : Function.Injective fun k => lin A (ebasis k) := by
      intro k l h
      have hU : IsUnit A.det := hA
      have := congrArg (lin A⁻¹) h
      simp only [lin_inv_mul_apply hU] at this
      exact ebasis_injective this
    rw [hmass, Finset.sum_eq_single j (fun k _ hk => by
      rw [if_neg]; intro h; exact hk (hinjA h)) (by simp)]
    simp
  have hpos_atom : ∀ (A : Mat d) (y : Rd d), 0 < push A μ₀ {y} →
      ∃ j, lin A (ebasis j) = y := by
    intro A y hy
    rw [hmass] at hy
    by_contra h
    push Not at h
    simp [Set.mem_singleton_iff, h] at hy
  -- the stabilizer is trivial
  have hstab : stab μ₀ = {1} := by
    ext A
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hA, hpush⟩
      have hfix : ∀ j, lin A (ebasis j) = ebasis j := by
        intro j
        have h1 := hatom A hA j
        rw [hpush] at h1
        have hpos : 0 < μ₀ {lin A (ebasis j)} := by rw [h1]; exact ENNReal.ofReal_pos.2 (hp j)
        obtain ⟨k, hk⟩ := hpos_atom 1 _ (by rw [push_one]; exact hpos)
        rw [lin_one] at hk
        have h2 : μ₀ {ebasis k} = ENNReal.ofReal (p k) := by
          have := hatom 1 hgl.one_mem k
          rwa [push_one, lin_one] at this
        simp only [one_apply_eq_self] at hk
        rw [← hk, h2] at h1
        have hpk : p k = p j := by
          rwa [ENNReal.ofReal_eq_ofReal_iff (hp k).le (hp j).le] at h1
        rw [← hk, hinj hpk]
      ext i j
      have := congrArg (fun y : Rd d => y i) (hfix j)
      simp only at this
      rw [show (lin A (ebasis j)) i = A i j by
        rw [ofLp_lin]
        simp [ebasis, Matrix.mulVec, dotProduct]] at this
      rw [this, Matrix.one_apply]
      simp [ebasis, PiLp.single_apply]
    · rintro rfl
      exact ⟨hgl.one_mem, push_one μ₀⟩
  refine ⟨?_, hstab, ⟨fun A hA => ⟨A, hA, rfl⟩, fun A hA B hB h => ?_,
    fun ν ⟨A, hA, h⟩ => ⟨A, hA, h.symm⟩⟩, ?_⟩
  · -- full
    intro V hV
    obtain ⟨j0, hj0⟩ : ∃ j, ebasis j ∉ V := by
      by_contra h
      push Not at h
      apply hV
      rw [eq_top_iff]
      intro x _
      have hx : x = ∑ j, x j • ebasis j := by
        ext i
        simp [ebasis, Finset.sum_apply, Pi.single_apply]
      rw [hx]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h j)
    have hle : μ₀ (V : Set (Rd d)) ≤ μ₀ {ebasis j0}ᶜ :=
      measure_mono fun x hx hx0 => hj0 (by rw [mem_singleton_iff] at hx0; rw [← hx0]; exact hx)
    rw [prob_compl_eq_one_sub (measurableSet_singleton _)] at hle
    have h1 : μ₀ {ebasis j0} = ENNReal.ofReal (p j0) := by
      have := hatom 1 hgl.one_mem j0
      rwa [push_one, lin_one] at this
    rw [h1] at hle
    refine lt_of_le_of_lt hle (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_)
    exact (ENNReal.ofReal_pos.2 (hp j0)).ne'
  · -- injective
    have hU : IsUnit B.det := hB
    have hR : B⁻¹ * A ∈ stab μ₀ := by
      refine ⟨hgl.mul_mem _ (hgl.inv_mem B hB) A hA, ?_⟩
      simp only at h
      rw [← push_push, h, push_push, Matrix.nonsing_inv_mul _ hU, push_one]
    rw [hstab, Set.mem_singleton_iff] at hR
    calc A = B * (B⁻¹ * A) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
      _ = B := by rw [hR, Matrix.mul_one]
  · -- no rotation-invariant member: the sphere through an atom is covered by `d` atoms
    rintro ν ⟨A, hA, rfl⟩ hrot
    set i0 : Fin d := ⟨0, by omega⟩
    set x := lin A (ebasis i0) with hx
    have hU : IsUnit A.det := hA
    have hx0 : x ≠ 0 := by
      intro h0
      have := congrArg (lin A⁻¹) h0
      rw [hx, lin_inv_mul_apply hU, map_zero] at this
      have := congrArg (fun y : Rd d => y i0) this
      simp [ebasis] at this
    set r := ‖x‖ with hr
    have hrpos : 0 < r := norm_pos_iff.2 hx0
    -- every `y` with `|y| = r` carries an atom
    have hcover : ∀ y : Rd d, ‖y‖ = r → ∃ j, lin A (ebasis j) = y := by
      intro y hy
      set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (x - y))ᗮ with hQ
      have hQx : Q x = y := Submodule.reflection_sub (hr.symm.trans hy.symm)
      have hpush := hrot _ (isoMat_mem_orthSet Q)
      have hpre : lin (isoMat Q) ⁻¹' {y} = {x} := by
        ext z
        simp only [mem_preimage, mem_singleton_iff, lin_isoMat]
        constructor
        · intro hz
          rw [← hQx] at hz
          exact Q.injective hz
        · rintro rfl; exact hQx
      have hval : push A μ₀ {y} = push A μ₀ {x} := by
        conv_lhs => rw [← hpush]
        rw [push, Measure.map_apply (lin _).continuous.measurable (measurableSet_singleton _),
          hpre]
      apply hpos_atom A y
      rw [hval, hx, hatom A hA i0]
      exact ENNReal.ofReal_pos.2 (hp i0)
    -- the `2d` points `±r eⱼ` are covered by `d` atoms
    set pt : Fin d ⊕ Fin d → Rd d := fun s => Sum.elim (fun j => r • ebasis j)
      (fun j => (-r) • ebasis j) s with hpt
    have hpt_norm : ∀ s, ‖pt s‖ = r := by
      rintro (j | j) <;> simp [hpt, norm_smul, ebasis, abs_of_pos hrpos]
    have hpt_inj : Function.Injective pt := by
      rintro (i | i) (j | j) h <;> simp only [hpt, Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg Sum.inl (ebasis_injective (smul_right_injective _ hrpos.ne' h))
      · exfalso
        have := congrArg (fun y : Rd d => y i) h
        by_cases hij : i = j
        · subst hij; simp [ebasis] at this; linarith
        · simp [ebasis, hij] at this; linarith
      · exfalso
        have := congrArg (fun y : Rd d => y j) h
        by_cases hij : i = j
        · subst hij; simp [ebasis] at this; linarith
        · simp [ebasis, Ne.symm hij] at this; linarith
      · exact congrArg Sum.inr (ebasis_injective (smul_right_injective _ (by linarith) h))
    choose g hg using fun s => hcover (pt s) (hpt_norm s)
    have hginj : Function.Injective g := fun s t h => hpt_inj (by rw [← hg s, ← hg t, h])
    have := Fintype.card_le_of_injective g hginj
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega

end Atoms

/-! ### The diagonal example (`lem:parameter-space-examples`(5)) -/

section DiagExample

open ProbabilityTheory

/-- The invertible diagonal matrices form a closed subgroup of `GL(d)` containing the dilations. -/
theorem diagGLSet_isClosedSubgroupGL :
    IsClosedSubgroupGL (diagGLSet d) ∧ ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ diagGLSet d := by
  refine ⟨⟨?_, ⟨fun _ => 1, fun _ => one_ne_zero, diagonal_one.symm⟩, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    change IsUnit (diagonal v).det
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hv i)
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact ⟨v * w, fun i => mul_ne_zero (hv i) (hw i), by rw [diagonal_mul_diagonal]; rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨fun i => (v i)⁻¹, fun i => inv_ne_zero (hv i), ?_⟩
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hv i)
  · intro A hA hdet
    have hD : IsClosed {M : Mat d | ∀ i j, i ≠ j → M i j = 0} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
    have hsub : diagGLSet d ⊆ {M : Mat d | ∀ i j, i ≠ j → M i j = 0} := by
      rintro _ ⟨v, -, rfl⟩ i j hij
      exact diagonal_apply_ne _ hij
    have hAd := closure_minimal hsub hD hA
    have hAeq : A = diagonal fun i => A i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [diagonal_apply_ne _ hij]; exact hAd i j hij
    refine ⟨fun i => A i i, fun i => ?_, hAeq⟩
    have h := hdet
    rw [hAeq, det_diagonal] at h
    exact (Finset.prod_ne_zero_iff.1 (isUnit_iff_ne_zero.1 h)) i (Finset.mem_univ _)
  · intro c hc
    exact ⟨fun _ => c, fun _ => hc.ne', by rw [smul_one_eq_diagonal]⟩

/-- `⟨ω, diag(c eᵢ) ω⟩ = c ωᵢ²`. -/
theorem quad_diagonal_single (i : Fin d) (c : ℝ) (ω : Rd d) :
    quad (diagonal (Pi.single i c)) ω = c * ω i ^ 2 := by
  rw [quad_eq_dotProduct]
  simp [dotProduct, mulVec_diagonal, Pi.single_apply, sq]
  ring

/-- **`lem:parameter-space-examples`(5)**, the example: for `d ≥ 2`, `G` the invertible
diagonal matrices and `W` the Loewner order, the centred Gaussian laws with transform
`exp[-½(Σ' - Σ)₁₁ ω₁²]` form a `(G, W)`-cascade family of kernels whose `μ_I` is carried by the
first axis and has a stabilizer that is not compact. -/
theorem parameter_space_diag_example (hd : 2 ≤ d) :
    let i₀ : Fin d := ⟨0, by omega⟩
    let μ : Mat d → Mat d → Measure (Rd d) := fun S S' =>
      multivariateGaussian 0 (diagonal (Pi.single i₀ ((S' - S) i₀ i₀)))
    IsWedgeDatum (diagGLSet d) loewnerLE ∧ IsGWCascadeFamily (diagGLSet d) loewnerLE μ ∧
      (∀ S S' : Mat d, loewnerLE S S' → ∀ ω : Rd d,
        charFun (μ S S') ω = ((Real.exp (-((S' - S) i₀ i₀ * ω i₀ ^ 2 / 2)) : ℝ) : ℂ)) ∧
      μ 0 1 ((Submodule.span ℝ {ebasis i₀} : Set (Rd d))ᶜ) = 0 ∧
      ¬ IsCompact (stab (μ 0 1)) := by
  intro i₀ μ
  obtain ⟨hG, hdil⟩ := diagGLSet_isClosedSubgroupGL (d := d)
  have hW := isWedgeDatum_loewner hG hdil
  have hpsd : ∀ c : ℝ, 0 ≤ c → (diagonal (Pi.single i₀ c) : Mat d).PosSemidef := fun c hc => by
    rw [posSemidef_diagonal_iff]
    intro i
    by_cases h : i = i₀
    · subst h; simp [hc]
    · simp [h]
  have hchar : ∀ S S' : Mat d, loewnerLE S S' → ∀ ω : Rd d,
      charFun (μ S S') ω = ((Real.exp (-((S' - S) i₀ i₀ * ω i₀ ^ 2 / 2)) : ℝ) : ℂ) := by
    intro S S' hle ω
    have hc : 0 ≤ (S' - S) i₀ i₀ := hle.diag_nonneg
    simp only [μ]
    rw [charFun_multivariateGaussian_zero (hpsd _ hc), quad_diagonal_single]
  have hprob : ∀ S S' : Mat d, IsProbabilityMeasure (μ S S') := fun S S' => inferInstance
  have hdiag : ∀ S : Mat d, μ S S = Measure.dirac 0 := by
    intro S
    refine eq_of_charFun_eq fun ω => ?_
    rw [hchar S S (by simp [loewnerLE, PosSemidef.zero]) ω, charFun_dirac]
    simp
  refine ⟨hW, ⟨fun p _ => hprob _ _, fun S _ => hdiag S, fun S S' S'' _ _ _ h h' => ?_,
    fun ω => ?_, fun A hA p hp => ?_, fun h => ?_⟩, hchar, ?_, ?_⟩
  · -- the cascade
    have h'' : loewnerLE S S'' := by
      unfold loewnerLE at h h' ⊢
      have := h.add h'
      rwa [show S' - S + (S'' - S') = S'' - S by abel] at this
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, hchar _ _ h'' ω, hchar _ _ h' ω, hchar _ _ h ω, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    simp only [Matrix.sub_apply]
    ring
  · -- continuity on the pairs
    refine ContinuousOn.congr (f := fun p : Mat d × Mat d =>
      ((Real.exp (-((p.2 - p.1) i₀ i₀ * ω i₀ ^ 2 / 2)) : ℝ) : ℂ)) ?_ fun p hp => hchar _ _ hp.2.2 ω
    refine Continuous.continuousOn ?_
    have : Continuous fun p : Mat d × Mat d => (p.2 - p.1) i₀ i₀ :=
      (continuous_snd.sub continuous_fst).matrix_elem i₀ i₀
    fun_prop
  · -- covariance under the diagonal matrices
    obtain ⟨v, hv, rfl⟩ := hA
    have hgl : diagonal v ∈ glSet d := hG.subset_gl ⟨v, hv, rfl⟩
    have hp' : loewnerLE (act (diagonal v) p.1) (act (diagonal v) p.2) :=
      hW.invariant _ ⟨v, hv, rfl⟩ _ _ hp.1 hp.2.1 hp.2.2
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_push _ hgl, hchar _ _ hp.2.2, hchar _ _ hp']
    congr 3
    simp only [act, diagonal_transpose, ← Matrix.mul_sub, ← Matrix.sub_mul, diagonal_mul,
      mul_diagonal]
    have hω : (lin (diagonal v) ω) i₀ = v i₀ * ω i₀ := by
      rw [ofLp_lin, mulVec_diagonal]
    rw [hω]
    ring
  · -- nondegeneracy
    have := congrArg (fun m => charFun m (ebasis i₀)) h
    rw [hchar 0 1 (by simp [loewnerLE, PosSemidef.one]), charFun_dirac] at this
    simp [ebasis] at this
    have h3 : Real.exp (-2⁻¹) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_exp]
      push_cast
      exact this
    rw [Real.exp_eq_one_iff] at h3
    norm_num at h3
  · -- carried by the first axis
    have hc := gaussian_carried_by_range (hpsd 1 zero_le_one) (b := 1 / 2) (by norm_num)
    rw [show (2 * (1 / 2 : ℝ)) • (diagonal (Pi.single i₀ (1 : ℝ)) : Mat d) =
      diagonal (Pi.single i₀ 1) by norm_num] at hc
    have hμ01 : μ 0 1 = multivariateGaussian 0 (diagonal (Pi.single i₀ (1 : ℝ))) := by
      simp [μ]
    rw [hμ01]
    refine measure_mono_null (compl_subset_compl.2 ?_) hc
    rintro _ ⟨x, rfl⟩
    have hx : lin (diagonal (Pi.single i₀ (1 : ℝ))) x = x i₀ • ebasis i₀ := by
      apply WithLp.ofLp_injective 2
      rw [ofLp_lin]
      ext k
      rw [mulVec_diagonal]
      simp [ebasis, Pi.single_apply]
      by_cases hk : k = i₀ <;> simp [hk]
    change lin (diagonal (Pi.single i₀ (1 : ℝ))) x ∈ Submodule.span ℝ {ebasis i₀}
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · -- the stabilizer contains `diag(1, t, 1, …)`, unbounded
    set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
    have h01 : i₀ ≠ i₁ := by simp [i₀, hi₁, Fin.ext_iff]
    intro hcomp
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (f := fun M : Mat d => M i₁ i₁)
      ((continuous_apply i₁).comp (continuous_apply i₁)).continuousOn
    set t := |C| + 1 with ht
    have htpos : 0 < t := by positivity
    set D : Mat d := diagonal (Function.update (fun _ => (1 : ℝ)) i₁ t) with hD
    have hDgl : D ∈ glSet d := hG.subset_gl ⟨_, fun i => by
      by_cases h : i = i₁
      · subst h; simp [htpos.ne']
      · simp [Function.update_of_ne h], rfl⟩
    have hmem : D ∈ stab (μ 0 1) := by
      refine ⟨hDgl, eq_of_charFun_eq fun ω => ?_⟩
      have h01' : loewnerLE (0 : Mat d) 1 := by simp [loewnerLE, PosSemidef.one]
      rw [charFun_push _ hDgl, hchar _ _ h01', hchar _ _ h01']
      have hω : (lin Dᵀ ω) i₀ = ω i₀ := by
        rw [hD, diagonal_transpose, ofLp_lin, mulVec_diagonal, Function.update_of_ne h01, one_mul]
      rw [hω]
    have := hC D hmem
    rw [hD, diagonal_apply_eq, Function.update_self, Real.norm_eq_abs, abs_of_pos htpos] at this
    have := le_abs_self C
    linarith

end DiagExample

end AffineHemigroup
