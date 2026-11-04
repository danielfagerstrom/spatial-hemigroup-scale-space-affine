/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.BochnerConvolutionSpace
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The operators are convolutions, over a finite-dimensional space

Blueprint: `lem:operators-to-kernels`(1), the representation
(`blueprint/src/parts/04-classical.tex`). Q-0281, wave M, phase 2.

Under (A1), (A2), (A4), (A5) a bounded operator on `L¹(E)`, `E` a finite-dimensional real normed
space with an additive Haar measure, is convolution by a probability measure. The argument is
[V, Lem. 4.1]'s, in `ScaleSpaceCore.Representation` on the line, with balls in place of intervals,
as the blueprint's proof says: the interchange identity (`ScaleSpace.map_bconvE`), the approximate
identity `ρ_ε = |B_ε|⁻¹ 1_{B_ε}`, tightness, Prokhorov, and identification against the bounded
functionals of `L¹(E)`. Every statement here mentions only Mathlib's and the shared library's types,
so the file is a second-demand candidate for `scale-space-lean` (it is the `d`-dimensional
`ScaleSpaceCore.Representation`).

The three pieces of `ScaleSpaceCore.BochnerConvolution` that
`ScaleSpaceCore.BochnerConvolutionSpace` leaves on the line, `bconv_comm`, `bconv_congr_ae` and
`setIntegral_bconv`, are ported first.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open ScaleSpace (transL1E bconvE mconvL1E IsNonnegE setIntegralCLME)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-! ## Three facts on `bconvE`, ported from the line -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `bconvE` respects a.e. equality of the scalar factor. -/
theorem bconvE_congr_ae {f₁ f₂ : E → ℝ} (h : f₁ =ᵐ[volume] f₂) (g : E →₁[volume] ℝ) :
    bconvE f₁ g = bconvE f₂ g := by
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- **Convolution is commutative**, by the change of variables `y ↦ x - y`. -/
theorem bconvE_comm {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    bconvE f g = bconvE (g : E → ℝ) (hf.toL1 f) := by
  refine Lp.ext ((ScaleSpace.coeFn_bconvE hf g).trans ?_)
  refine Filter.EventuallyEq.symm
    ((ScaleSpace.coeFn_bconvE (L1.integrable_coeFn g) (hf.toL1 f)).trans ?_)
  filter_upwards with x
  have hswap : ∫ y, (g : E → ℝ) y * ((hf.toL1 f : E →₁[volume] ℝ) : E → ℝ) (x - y)
      = ∫ y, (g : E → ℝ) y * f (x - y) := by
    refine integral_congr_ae ?_
    filter_upwards [((volume : Measure E).measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (Integrable.coeFn_toL1 hf)] with y hy
    rw [hy]
  have hkey : ∫ y, (g : E → ℝ) y * f (x - y) = ∫ y, f y * (g : E → ℝ) (x - y) := by
    rw [← integral_sub_left_eq_self (fun y => f y * (g : E → ℝ) (x - y)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change (g : E → ℝ) y * f (x - y) = f (x - y) * (g : E → ℝ) (x - (x - y))
    rw [sub_sub_cancel, mul_comm]
  rw [hswap, hkey]

/-- Pairing `bconvE` against a set integral. -/
theorem setIntegral_bconvE (A : Set E) {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    ∫ x in A, (bconvE f g : E → ℝ) x = ∫ y, f y * ∫ x in A, (g : E → ℝ) (x - y) := by
  rw [← ScaleSpace.setIntegralCLME_apply A (bconvE f g), bconvE,
    ← ContinuousLinearMap.integral_comp_comm _ (ScaleSpace.integrable_smul_transL1E hf g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change setIntegralCLME A (f y • transL1E y g) = f y * ∫ x in A, (g : E → ℝ) (x - y)
  rw [ContinuousLinearMap.map_smul, ScaleSpace.setIntegralCLME_apply, smul_eq_mul]
  congr 1
  exact integral_congr_ae ((ScaleSpace.coeFn_transL1E y g).restrict)

/-- The integrand of `setIntegral_bconvE` is integrable. -/
theorem integrable_setIntegral_bconvE (A : Set E) {f : E → ℝ} (hf : Integrable f)
    (g : E →₁[volume] ℝ) :
    Integrable (fun y => f y * ∫ x in A, (g : E → ℝ) (x - y)) := by
  refine ((setIntegralCLME A).integrable_comp (ScaleSpace.integrable_smul_transL1E hf g)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  change setIntegralCLME A (f y • transL1E y g) = f y * ∫ x in A, (g : E → ℝ) (x - y)
  rw [ContinuousLinearMap.map_smul, ScaleSpace.setIntegralCLME_apply, smul_eq_mul]
  congr 1
  exact integral_congr_ae ((ScaleSpace.coeFn_transL1E y g).restrict)

/-- `bconvE f` is linear in its `L¹` argument. -/
theorem bconvE_sub {f : E → ℝ} (hf : Integrable f) (u v : E →₁[volume] ℝ) :
    bconvE f (u - v) = bconvE f u - bconvE f v := by
  rw [bconvE, bconvE, bconvE, ← integral_sub (ScaleSpace.integrable_smul_transL1E hf u)
    (ScaleSpace.integrable_smul_transL1E hf v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [map_sub, smul_sub]

/-- `‖f * u‖₁ ≤ ‖f‖₁ ‖u‖₁`. -/
theorem norm_bconvE_le {f : E → ℝ} (hf : Integrable f) (u : E →₁[volume] ℝ) :
    ‖bconvE f u‖ ≤ (∫ y, ‖f y‖) * ‖u‖ := by
  rw [bconvE, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono
    (ScaleSpace.integrable_smul_transL1E hf u).norm (hf.norm.mul_const _) fun y => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ScaleSpace.norm_transL1E_le y u) (norm_nonneg _)

/-! ## The approximate identity `ρ_ε = |B_ε|⁻¹ 1_{B_ε}` -/

/-- `ρ_ε = |B_ε|⁻¹ 1_{B_ε}`, `B_ε` the open ball of radius `ε` about `0`. -/
noncomputable def approxIdE (ε : ℝ) : E → ℝ :=
  fun x => (volume.real (ball (0 : E) ε))⁻¹ * (ball (0 : E) ε).indicator (fun _ => (1 : ℝ)) x

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `ρ_ε` vanishes off the ball `B_ε`. -/
lemma approxIdE_eq_zero {ε : ℝ} {x : E} (hx : x ∉ ball (0 : E) ε) : approxIdE ε x = 0 := by
  simp [approxIdE, Set.indicator_of_notMem hx]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `ρ_ε ≥ 0`. -/
lemma approxIdE_nonneg (ε : ℝ) (x : E) : 0 ≤ approxIdE ε x :=
  mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

/-- `ρ_ε` is integrable: a constant on a ball of finite measure. -/
lemma integrable_approxIdE (ε : ℝ) : Integrable (approxIdE (E := E) ε) :=
  (IntegrableOn.integrable_indicator (integrableOn_const measure_ball_lt_top.ne)
    measurableSet_ball).const_mul _

/-- `∫ ρ_ε = 1` for `ε > 0`: the ball has positive finite measure. -/
lemma integral_approxIdE {ε : ℝ} (hε : 0 < ε) : ∫ x, approxIdE (E := E) ε x = 1 := by
  simp only [approxIdE]
  rw [integral_const_mul, integral_indicator_const _ measurableSet_ball, smul_eq_mul, mul_one]
  refine inv_mul_cancel₀ ?_
  rw [measureReal_def]
  exact (ENNReal.toReal_pos (measure_ball_pos volume 0 hε).ne' measure_ball_lt_top.ne).ne'

/-- `ρ_ε` as an element of `L¹(E)`. -/
noncomputable def approxIdL1E (ε : ℝ) : E →₁[volume] ℝ := (integrable_approxIdE ε).toL1 _

/-- The representative of `ρ_ε` in `L¹(E)`. -/
lemma coeFn_approxIdL1E (ε : ℝ) :
    ((approxIdL1E ε : E →₁[volume] ℝ) : E → ℝ) =ᵐ[volume] approxIdE ε :=
  Integrable.coeFn_toL1 _

/-- `ρ_ε` is in the positive cone of `L¹(E)`. -/
lemma isNonnegE_approxIdL1E (ε : ℝ) : IsNonnegE (approxIdL1E (E := E) ε) := by
  filter_upwards [coeFn_approxIdL1E ε] with x hx
  simp only [Pi.zero_apply, hx]
  exact approxIdE_nonneg ε x

/-- `∫ ρ_ε = 1` for `ε > 0`, read in `L¹(E)`. -/
lemma integral_approxIdL1E {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ((approxIdL1E ε : E →₁[volume] ℝ) : E → ℝ) x = 1 := by
  rw [integral_congr_ae (coeFn_approxIdL1E ε)]
  exact integral_approxIdE hε

/-- **`ρ_ε * g → g` in `L¹(E)`.** -/
theorem tendsto_bconvE_approxIdE (g : E →₁[volume] ℝ) :
    Tendsto (fun ε => bconvE (approxIdE ε) g) (𝓝[>] 0) (𝓝 g) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hcont : ContinuousAt (fun y => transL1E y g) 0 :=
    (ScaleSpace.continuous_transL1E g).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, hηb⟩ := hcont (δ / 2) (by linarith)
  refine ⟨η, hη, fun {ε} hε hd => ?_⟩
  have hε0 : 0 < ε := hε
  have hεη : ε < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hd
    exact hd
  have hint0 : Integrable (fun y => approxIdE ε y • (transL1E y g - g)) := by
    simp only [smul_sub]
    exact (ScaleSpace.integrable_smul_transL1E (integrable_approxIdE ε) g).sub
      ((integrable_approxIdE ε).smul_const g)
  have hsub : bconvE (approxIdE ε) g - g = ∫ y, approxIdE ε y • (transL1E y g - g) := by
    have hsplit : ∫ y, approxIdE ε y • (transL1E y g - g)
        = (∫ y : E, approxIdE ε y • transL1E y g) - ∫ y : E, approxIdE ε y • g := by
      simp only [smul_sub]
      exact integral_sub (ScaleSpace.integrable_smul_transL1E (integrable_approxIdE ε) g)
        ((integrable_approxIdE ε).smul_const g)
    rw [hsplit, bconvE, integral_smul_const, integral_approxIdE hε0, one_smul]
  have hbound : ∀ y, ‖approxIdE ε y • (transL1E y g - g)‖ ≤ approxIdE ε y * (δ / 2) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (approxIdE_nonneg ε y)]
    by_cases hy : y ∈ ball (0 : E) ε
    · refine mul_le_mul_of_nonneg_left ?_ (approxIdE_nonneg ε y)
      have hdy : dist y 0 < η := lt_trans (mem_ball.mp hy) hεη
      have := hηb hdy
      rw [ScaleSpace.transL1E_zero, ContinuousLinearMap.id_apply, dist_eq_norm] at this
      exact this.le
    · rw [approxIdE_eq_zero hy]
      simp
  calc dist (bconvE (approxIdE ε) g) g = ‖bconvE (approxIdE ε) g - g‖ := dist_eq_norm _ _
    _ = ‖∫ y, approxIdE ε y • (transL1E y g - g)‖ := by rw [hsub]
    _ ≤ ∫ y, ‖approxIdE ε y • (transL1E y g - g)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, approxIdE ε y * (δ / 2) :=
        integral_mono hint0.norm ((integrable_approxIdE ε).mul_const _) hbound
    _ = δ / 2 := by rw [integral_mul_const, integral_approxIdE hε0, one_mul]
    _ < δ := by linarith

/-- **`f * ρ_ε → f`**, with the approximate identity in the second slot. -/
theorem tendsto_bconvE_approxIdL1E {f : E → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconvE f (approxIdL1E ε)) (𝓝[>] 0) (𝓝 (hf.toL1 f)) := by
  have hcongr : ∀ ε : ℝ, bconvE f (approxIdL1E ε) = bconvE (approxIdE ε) (hf.toL1 f) :=
    fun ε => by
      rw [bconvE_comm hf (approxIdL1E ε)]
      exact bconvE_congr_ae (Integrable.coeFn_toL1 (integrable_approxIdE ε)) _
  simp only [hcongr]
  exact tendsto_bconvE_approxIdE _

/-! ## The approximants `h_ε = Φ ρ_ε` -/

/-- `h_ε = Φ ρ_ε`. -/
noncomputable def approxE (L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) (ε : ℝ) :
    E →₁[volume] ℝ :=
  L (approxIdL1E ε)

/-- `ν_ε = h_ε dx`. -/
noncomputable def approxMeasureE (L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) (ε : ℝ) :
    Measure E :=
  volume.withDensity fun x => ENNReal.ofReal ((approxE L ε : E →₁[volume] ℝ) x)

variable {L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)}

/-- (A4): `h_ε ≥ 0`. -/
lemma isNonnegE_approxE (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f)) (ε : ℝ) :
    IsNonnegE (approxE L ε) := hpos _ (isNonnegE_approxIdL1E ε)

/-- (A5): `∫ h_ε = 1` for `ε > 0`. -/
lemma integral_approxE
    (hmass : ∀ f, IsNonnegE f →
      ∫ x, ((L f : E →₁[volume] ℝ) : E → ℝ) x = ∫ x, (f : E → ℝ) x)
    {ε : ℝ} (hε : 0 < ε) : ∫ x, ((approxE L ε : E →₁[volume] ℝ) : E → ℝ) x = 1 := by
  rw [approxE, hmass _ (isNonnegE_approxIdL1E ε)]
  exact integral_approxIdL1E hε

/-- **`f * h_ε = Φ (f * ρ_ε)`**, by `map_bconvE` with (A2). -/
theorem bconvE_approxE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    {f : E → ℝ} (hf : Integrable f) (ε : ℝ) :
    bconvE f (approxE L ε) = L (bconvE f (approxIdL1E ε)) :=
  (ScaleSpace.map_bconvE L htrans hf (approxIdL1E ε)).symm

/-- **`f * h_ε → Φ f`.** -/
theorem tendsto_bconvE_approxE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    {f : E → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconvE f (approxE L ε)) (𝓝[>] 0) (𝓝 (L (hf.toL1 f))) := by
  simp only [bconvE_approxE htrans hf]
  exact (L.continuous.tendsto _).comp (tendsto_bconvE_approxIdL1E hf)

/-- (A4) and (A5) make `ν_ε = h_ε dx` a probability measure. -/
lemma isProbabilityMeasure_approxMeasureE (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f))
    (hmass : ∀ f, IsNonnegE f →
      ∫ x, ((L f : E →₁[volume] ℝ) : E → ℝ) x = ∫ x, (f : E → ℝ) x)
    {ε : ℝ} (hε : 0 < ε) : IsProbabilityMeasure (approxMeasureE L ε) := by
  constructor
  rw [approxMeasureE, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _) (isNonnegE_approxE hpos ε),
    integral_approxE hmass hε, ENNReal.ofReal_one]

/-! ## Tightness -/

/-- The tail `{‖x‖ > R}`. -/
def tailSetE (R : ℝ) : Set E := {x : E | R < ‖x‖}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma measurableSet_tailSetE (R : ℝ) : MeasurableSet (tailSetE (E := E) R) :=
  measurableSet_lt measurable_const measurable_norm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- The tails decrease as the radius grows. -/
lemma tailSetE_antitone {R R' : ℝ} (h : R ≤ R') : tailSetE (E := E) R' ⊆ tailSetE R :=
  fun _ hx => lt_of_le_of_lt h hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translating a restricted integral: `∫_A φ(x - y) dx = ∫_{A - y} φ`. -/
theorem setIntegral_comp_sub_rightE (φ : E → ℝ) {A : Set E} (hA : MeasurableSet A) (y : E) :
    ∫ x in A, φ (x - y) = ∫ u in (fun u : E => u + y) ⁻¹' A, φ u := by
  have hA2 : MeasurableSet ((fun u : E => u + y) ⁻¹' A) := hA.preimage (measurable_add_const y)
  rw [← integral_indicator hA, ← integral_indicator hA2,
    ← integral_add_right_eq_self (fun x : E => A.indicator (fun z => φ (z - y)) x) y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change A.indicator (fun z => φ (z - y)) (u + y)
      = ((fun u : E => u + y) ⁻¹' A).indicator φ u
  by_cases hu : u + y ∈ A
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u ∈ _ from hu), add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show u ∉ _ from hu)]

/-- **The tail of `ν_ε` beyond `R + 1` is dominated by the tail of `ρ₁ * h_ε` beyond `R`.** -/
theorem tail_le_tail_bconvE {h : E →₁[volume] ℝ} (hnn : IsNonnegE h) (R : ℝ) :
    ∫ u in tailSetE (R + 1), (h : E → ℝ) u
      ≤ ∫ x in tailSetE R, ((bconvE (approxIdE 1) h : E →₁[volume] ℝ) : E → ℝ) x := by
  have hpass := setIntegral_bconvE (tailSetE R) (integrable_approxIdE (E := E) 1) h
  have hintg := integrable_setIntegral_bconvE (tailSetE R) (integrable_approxIdE (E := E) 1) h
  have hmono : ∀ y, approxIdE 1 y * (∫ u in tailSetE (R + 1), (h : E → ℝ) u)
      ≤ approxIdE 1 y * ∫ x in tailSetE R, (h : E → ℝ) (x - y) := by
    intro y
    by_cases hy : y ∈ ball (0 : E) 1
    · refine mul_le_mul_of_nonneg_left ?_ (approxIdE_nonneg 1 y)
      rw [setIntegral_comp_sub_rightE _ (measurableSet_tailSetE R) y]
      refine setIntegral_mono_set (L1.integrable_coeFn h).integrableOn
        (ae_restrict_of_ae hnn) (HasSubset.Subset.eventuallyLE fun u hu => ?_)
      simp only [tailSetE, Set.mem_setOf_eq, Set.mem_preimage] at hu ⊢
      have h1 : ‖u‖ - ‖y‖ ≤ ‖u + y‖ := by
        have := norm_sub_norm_le u (-y)
        simpa [sub_neg_eq_add, norm_neg] using this
      have h2 : ‖y‖ < 1 := by simpa using hy
      linarith
    · rw [approxIdE_eq_zero hy, zero_mul, zero_mul]
  rw [hpass]
  calc ∫ u in tailSetE (R + 1), (h : E → ℝ) u
      = ∫ y, approxIdE 1 y * ∫ u in tailSetE (R + 1), (h : E → ℝ) u := by
        rw [integral_mul_const, integral_approxIdE one_pos, one_mul]
    _ ≤ ∫ y, approxIdE 1 y * ∫ x in tailSetE R, (h : E → ℝ) (x - y) :=
        integral_mono ((integrable_approxIdE 1).mul_const _) hintg hmono

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The tail of a finite measure can be made as small as wanted. -/
theorem exists_measure_tailSetE_le (ν : Measure E) [IsFiniteMeasure ν] {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, ν (tailSetE R) ≤ η := by
  have hmono : Antitone fun n : ℕ => tailSetE (E := E) (n : ℝ) := fun m n hmn =>
    tailSetE_antitone (by exact_mod_cast hmn)
  have hinter : (⋂ n : ℕ, tailSetE (E := E) (n : ℝ)) = ∅ := by
    ext x
    simp only [Set.mem_iInter, tailSetE, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact ⟨n, hn.le⟩
  have h := tendsto_measure_iInter_atTop
    (fun n : ℕ => (measurableSet_tailSetE (E := E) (n : ℝ)).nullMeasurableSet) hmono
    ⟨0, measure_ne_top ν _⟩
  rw [hinter, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hη)).exists
  exact ⟨n, hn.le⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The tail of `|k|` for an integrable `k` can be made as small as wanted. -/
theorem exists_setIntegral_abs_tailSetE_le {k : E → ℝ} (hk : Integrable k) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∫ u in tailSetE R, |k u| ≤ η := by
  set ν : Measure E := volume.withDensity fun x => ‖k x‖ₑ with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hk.2
  obtain ⟨R, hR⟩ := exists_measure_tailSetE_le ν (η := ENNReal.ofReal η)
    (by simp only [ENNReal.ofReal_pos]; linarith)
  refine ⟨R, ?_⟩
  have hval : ν (tailSetE R) = ∫⁻ u in tailSetE R, ‖k u‖ₑ :=
    withDensity_apply _ (measurableSet_tailSetE R)
  have heq : ∫ u in tailSetE R, |k u| = (∫⁻ u in tailSetE R, ‖k u‖ₑ).toReal := by
    simpa [Real.norm_eq_abs] using
      integral_norm_eq_lintegral_enorm (hk.aestronglyMeasurable.restrict)
  rw [heq, ← hval]
  calc (ν (tailSetE R)).toReal ≤ (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hR
    _ = η := ENNReal.toReal_ofReal hη.le

/-- The sequence `ε n = 1/(n+1)`. -/
noncomputable def epsSeqE (n : ℕ) : ℝ := 1 / (n + 1)

/-- `ε n > 0`. -/
lemma epsSeqE_pos (n : ℕ) : 0 < epsSeqE n := by
  rw [epsSeqE]; positivity

/-- `ε n → 0` from the right. -/
lemma tendsto_epsSeqE : Tendsto epsSeqE atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => epsSeqE_pos n)

/-- **The tails of `ν_{ε n}` are small uniformly in `n`.** -/
theorem exists_uniform_tailE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f)) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ n : ℕ, ∫ u in tailSetE R, ((approxE L (epsSeqE n) : E →₁[volume] ℝ) : E → ℝ) u
      ≤ η := by
  set k : E →₁[volume] ℝ := L ((integrable_approxIdE (E := E) 1).toL1 (approxIdE 1)) with hk
  obtain ⟨R₁, hR₁⟩ := exists_setIntegral_abs_tailSetE_le (L1.integrable_coeFn k) (η := η / 2)
    (by linarith)
  have hconv : Tendsto (fun n => bconvE (approxIdE 1) (approxE L (epsSeqE n))) atTop (𝓝 k) :=
    (tendsto_bconvE_approxE htrans (integrable_approxIdE 1)).comp tendsto_epsSeqE
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (η / 2) (by linarith)
  have hfin : ∀ m : ℕ, ∃ R : ℝ, ∫ u in tailSetE R,
      ((approxE L (epsSeqE m) : E →₁[volume] ℝ) : E → ℝ) u ≤ η := by
    intro m
    obtain ⟨R, hR⟩ := exists_setIntegral_abs_tailSetE_le
      (L1.integrable_coeFn (approxE L (epsSeqE m))) hη
    refine ⟨R, le_trans ?_ hR⟩
    exact setIntegral_mono_on (L1.integrable_coeFn _).integrableOn
      (L1.integrable_coeFn (approxE L (epsSeqE m))).abs.integrableOn (measurableSet_tailSetE R)
      fun u _ => le_abs_self _
  choose Rsmall hRsmall using hfin
  obtain ⟨M, hM⟩ := Finset.exists_le ((Finset.range N).image Rsmall)
  refine ⟨max (max R₁ M + 1) M, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hd := hN n hn
    rw [dist_eq_norm] at hd
    set F : E →₁[volume] ℝ := bconvE (approxIdE 1) (approxE L (epsSeqE n)) with hF
    have hstep : ∫ x in tailSetE (max R₁ M), (F : E → ℝ) x ≤ η := by
      have hdiff : Integrable (fun x => (F : E → ℝ) x - (k : E → ℝ) x) :=
        (L1.integrable_coeFn F).sub (L1.integrable_coeFn k)
      have habsk : Integrable (fun x => |(k : E → ℝ) x|) := (L1.integrable_coeFn k).abs
      calc ∫ x in tailSetE (max R₁ M), (F : E → ℝ) x
          ≤ ∫ x in tailSetE (max R₁ M),
              (|(k : E → ℝ) x| + |(F : E → ℝ) x - (k : E → ℝ) x|) := by
            refine setIntegral_mono_on (L1.integrable_coeFn F).integrableOn
              (habsk.add hdiff.abs).integrableOn (measurableSet_tailSetE _) fun u _ => ?_
            calc (F : E → ℝ) u = (k : E → ℝ) u + ((F : E → ℝ) u - (k : E → ℝ) u) := by ring
              _ ≤ |(k : E → ℝ) u| + |(F : E → ℝ) u - (k : E → ℝ) u| :=
                  add_le_add (le_abs_self _) (le_abs_self _)
        _ = (∫ x in tailSetE (max R₁ M), |(k : E → ℝ) x|)
              + ∫ x in tailSetE (max R₁ M), |(F : E → ℝ) x - (k : E → ℝ) x| :=
            integral_add habsk.integrableOn hdiff.abs.integrableOn
        _ ≤ η / 2 + η / 2 := by
            refine add_le_add (le_trans ?_ hR₁) ?_
            · exact setIntegral_mono_set habsk.integrableOn
                (ae_restrict_of_ae (Filter.Eventually.of_forall fun u => abs_nonneg _))
                (HasSubset.Subset.eventuallyLE (tailSetE_antitone (le_max_left _ _)))
            · calc ∫ x in tailSetE (max R₁ M), |(F : E → ℝ) x - (k : E → ℝ) x|
                  ≤ ∫ x, |(F : E → ℝ) x - (k : E → ℝ) x| :=
                    setIntegral_le_integral hdiff.abs
                      (Filter.Eventually.of_forall fun u => abs_nonneg _)
                _ = ‖F - k‖ := by
                    have hnorm : ‖F - k‖
                        = (∫⁻ x, ‖(F : E → ℝ) x - (k : E → ℝ) x‖ₑ).toReal := by
                      rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
                      congr 1
                      refine lintegral_congr_ae ?_
                      filter_upwards [Lp.coeFn_sub F k] with x hx
                      rw [hx]
                      rfl
                    rw [hnorm, ← integral_norm_eq_lintegral_enorm
                      (f := fun x => (F : E → ℝ) x - (k : E → ℝ) x)
                      hdiff.aestronglyMeasurable]
                    simp only [Real.norm_eq_abs]
                _ ≤ η / 2 := hd.le
        _ = η := by ring
    refine le_trans (le_trans ?_ (tail_le_tail_bconvE (isNonnegE_approxE hpos (epsSeqE n))
      (max R₁ M))) hstep
    exact setIntegral_mono_set (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonnegE_approxE hpos _))
      (HasSubset.Subset.eventuallyLE (tailSetE_antitone (le_max_left _ _)))
  · rw [not_le] at hn
    refine le_trans ?_ (hRsmall n)
    exact setIntegral_mono_set (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonnegE_approxE hpos _))
      (HasSubset.Subset.eventuallyLE
        (tailSetE_antitone (le_trans
          (hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)))
          (le_max_right _ _))))

/-- The tail of `ν_ε`, in terms of the density. -/
lemma approxMeasureE_tailSetE (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f)) (ε R : ℝ) :
    approxMeasureE L ε (tailSetE R)
      = ENNReal.ofReal (∫ u in tailSetE R, ((approxE L ε : E →₁[volume] ℝ) : E → ℝ) u) := by
  rw [approxMeasureE, withDensity_apply _ (measurableSet_tailSetE R),
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonnegE_approxE hpos ε))]

/-- **The approximants are tight**, with the closed balls as compacts. -/
theorem isTightMeasureSet_approxMeasureE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f)) :
    IsTightMeasureSet {ν : Measure E | ∃ n : ℕ, ν = approxMeasureE L (epsSeqE n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨∅, isCompact_empty, fun ν _ => le_top⟩
  have hη0 : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨R, hR⟩ := exists_uniform_tailE htrans hpos hη0
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (closedBall (0 : E) R)ᶜ ⊆ tailSetE R := by
    intro u hu
    simpa [tailSetE] using hu
  calc approxMeasureE L (epsSeqE n) ((closedBall 0 R)ᶜ)
      ≤ approxMeasureE L (epsSeqE n) (tailSetE R) := measure_mono hsub
    _ ≤ η := by
        rw [approxMeasureE_tailSetE hpos]
        calc ENNReal.ofReal (∫ u in tailSetE R,
              ((approxE L (epsSeqE n) : E →₁[volume] ℝ) : E → ℝ) u)
            ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (hR n)
          _ = η := ENNReal.ofReal_toReal hηtop

/-! ## The limit measure -/

/-- **A weak limit exists** (Prokhorov). -/
theorem exists_weak_limitE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f))
    (hmass : ∀ f, IsNonnegE f →
      ∫ x, ((L f : E →₁[volume] ℝ) : E → ℝ) x = ∫ x, (f : E → ℝ) x) :
    ∃ (μ : Measure E) (_ : IsProbabilityMeasure μ),
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ φ : BoundedContinuousFunction E ℝ,
        Tendsto (fun j => ∫ x, φ x ∂(approxMeasureE L (epsSeqE (σ j)))) atTop
          (𝓝 (∫ x, φ x ∂μ)) := by
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (approxMeasureE L (epsSeqE n)) := fun n =>
    isProbabilityMeasure_approxMeasureE hpos hmass (epsSeqE_pos n)
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨approxMeasureE L (epsSeqE n), hprob n⟩ with hP
  have hsetEq : {ν : Measure E | ∃ Q ∈ Set.range P, (Q : Measure E) = ν}
      = {ν : Measure E | ∃ n : ℕ, ν = approxMeasureE L (epsSeqE n)} := by
    ext ν
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  have hset : IsTightMeasureSet {ν : Measure E | ∃ Q ∈ Set.range P, (Q : Measure E) = ν} := by
    rw [hsetEq]
    exact isTightMeasureSet_approxMeasureE htrans hpos
  have hcompact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet hset
  obtain ⟨Q, -, σ, hσ, hQ⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨(Q : Measure E), Q.2, σ, hσ,
    fun φ => (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ) φ⟩

/-! ## The identification -/

/-- Integration against `ν_ε` is integration against the density `h_ε`. -/
theorem integral_approxMeasureE (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f)) (ε : ℝ)
    (G : BoundedContinuousFunction E ℝ) :
    ∫ y, G y ∂(approxMeasureE L ε) = ∫ y, ((approxE L ε : E →₁[volume] ℝ) : E → ℝ) y * G y := by
  rw [approxMeasureE, integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable (approxE L ε)).aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [isNonnegE_approxE hpos ε] with y hy
  rw [smul_eq_mul, ENNReal.toReal_ofReal hy]

/-- **The pairing identity in the limit.** -/
theorem apply_eq_integral_pairTransE (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f))
    {μ : Measure E} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hweak : ∀ φ : BoundedContinuousFunction E ℝ,
      Tendsto (fun j => ∫ x, φ x ∂(approxMeasureE L (epsSeqE (σ j)))) atTop
        (𝓝 (∫ x, φ x ∂μ)))
    (Ψ : (E →₁[volume] ℝ) →L[ℝ] ℝ) (f : E →₁[volume] ℝ) :
    Ψ (L f) = ∫ y, ScaleSpace.pairTransE Ψ f y ∂μ := by
  have hfL : (L1.integrable_coeFn f).toL1 (f : E → ℝ) = f :=
    Integrable.toL1_coeFn f (L1.integrable_coeFn f)
  have h1 : Tendsto (fun j => Ψ (bconvE (f : E → ℝ) (approxE L (epsSeqE (σ j))))) atTop
      (𝓝 (Ψ (L f))) := by
    have hlim := (tendsto_bconvE_approxE htrans (L := L) (L1.integrable_coeFn f)).comp
      (tendsto_epsSeqE.comp hσ.tendsto_atTop)
    rw [hfL] at hlim
    exact (Ψ.continuous.tendsto _).comp hlim
  have h2 : ∀ j : ℕ, Ψ (bconvE (f : E → ℝ) (approxE L (epsSeqE (σ j))))
      = ∫ y, ScaleSpace.pairTransE Ψ f y ∂(approxMeasureE L (epsSeqE (σ j))) := by
    intro j
    rw [bconvE_comm (L1.integrable_coeFn f) (approxE L (epsSeqE (σ j))), hfL,
      ScaleSpace.apply_bconvE Ψ (L1.integrable_coeFn _) f, integral_approxMeasureE hpos]
  refine tendsto_nhds_unique h1 ?_
  simpa only [h2] using hweak (ScaleSpace.pairTransE Ψ f)

/-- **The representation, existence**: a bounded operator on `L¹(E)` satisfying (A2), (A4) and
(A5) is convolution by a probability measure. -/
theorem exists_isProbabilityMeasure_eq_mconvL1E
    (htrans : ∀ a f, L (transL1E a f) = transL1E a (L f))
    (hpos : ∀ f, IsNonnegE f → IsNonnegE (L f))
    (hmass : ∀ f, IsNonnegE f →
      ∫ x, ((L f : E →₁[volume] ℝ) : E → ℝ) x = ∫ x, (f : E → ℝ) x) :
    ∃ (μ : Measure E) (_ : IsProbabilityMeasure μ), L = mconvL1E μ := by
  obtain ⟨μ, hprob, σ, hσ, hweak⟩ := exists_weak_limitE htrans hpos hmass
  refine ⟨μ, hprob, ContinuousLinearMap.ext fun f => Lp.ext ?_⟩
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (L f)).integrableOn)
    (fun A _ _ => (L1.integrable_coeFn (mconvL1E μ f)).integrableOn) fun A _ _ => ?_
  rw [← ScaleSpace.setIntegralCLME_apply A (L f), ← ScaleSpace.setIntegralCLME_apply A
    (mconvL1E μ f), apply_eq_integral_pairTransE htrans hpos hσ hweak, ScaleSpace.apply_mconvL1E]

end AffineHemigroup
