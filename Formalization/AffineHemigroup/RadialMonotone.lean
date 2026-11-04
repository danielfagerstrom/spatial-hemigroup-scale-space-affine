/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KanterRadial
import AffineHemigroup.Interfaces
import AffineHemigroup.RotationInvariant
import AffineHemigroup.PositiveTransform
import AffineHemigroup.OriginDecay
import AffineHemigroup.OriginBoundedness
import AffineHemigroup.PolarReading
import AffineHemigroup.PolarClassification
import AffineHemigroup.IsotropicClassification
import AffineHemigroup.RadialTransform

/-!
# `prop:isotropic-radial-monotone`: a radially nonincreasing density

Blueprint: `prop:isotropic-radial-monotone` (`blueprint/src/parts/03-isotropic.tex`). Wave 2,
group B (Q-0281). Spends ledger A8 (`wolfe_symmetric_unimodal`), and for clause (2) A2 and
A3(iii) through `polar_reading_converse`; clause (1) reads the classification of
`thm:isotropic-classification`, which prints A3(ii)-(iii) (through `line_levy_unique`; it printed
Paper V's `fourier_toolbox_levy_unique` until Q-0365).

## The route

The argument reads four properties of a law `μ` on `ℝ^d` (`radial_monotone_of_selfDecomposable`):
it is invariant under every linear isometry, self-decomposable, its transform is real, and
`|μ̂(ξ)| → 0` as `|ξ| → ∞`. Then:

* **no atom at the origin** (`measure_singleton_zero_of_tendsto`): `μ{0} ≤ ∫ e^{-R²|x|²/2} dμ`,
  which by `integral_heatKernel_eq` and the substitution `ξ = R y` is
  `(2π)^{-d/2} ∫ μ̂(Ry) e^{-|y|²/2} dy`, and that tends to `0` as `R → ∞` by dominated convergence;
* **the mixture** (ledger A8): `μ = ∫ u_K Λ(du_K)`, `μ` being symmetric (the isometry `-I`) and
  self-decomposable;
* **the distribution function in the volume coordinate** `G(v) = μ(B(v))`, `B(v) = φ⁻¹((0,v])`,
  `φ(x) = ω_d|x|^d`, is the `Λ`-mixture of the `u_K(B(v))`, each concave
  (`concaveENN_kanterUniform`), so it is concave (`ConcaveENN.lintegral`);
* **the density** (`exists_antitone_density_of_concave`): the image `m = φ_*μ` is `D · Lebesgue`
  on `(0,∞)` with `D` nonincreasing; put `q(r) := D(ω_d r^d)`;
* **back to `ℝ^d`**: `φ_*(Lebesgue) = Lebesgue|_{(0,∞)}` (`map_volume_volCoord`, the volume of a
  ball), so `φ_*(q(|x|) dx) = D · Lebesgue = m = φ_*μ`; the image under `|x| = (φ(x)/ω_d)^{1/d}`
  is then the same for `μ` and `q(|x|) dx`, and a rotation-invariant measure is determined by that
  image (`eq_of_rotationInvariant`).

This replaces the blueprint's right derivative of `G` *and* its reversed substitution by the
pushforward of Lebesgue measure under `φ`, which needs no change-of-variables formula.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ProbabilityTheory Complex
open scoped ENNReal Topology RealInnerProductSpace

variable {d : ℕ}

/-! ## Lebesgue measure in the volume coordinate -/

/-- `φ⁻¹((-∞, t])` has volume `t⁺`: it is the closed ball of volume `t` (empty for `t < 0`). -/
theorem volume_volCoord_Iic (hd : 1 ≤ d) (t : ℝ) :
    volume (volCoord d ⁻¹' Iic t) = ENNReal.ofReal t := by
  have hω := (ballVol_pos (d := d))
  rcases lt_or_ge t 0 with ht | ht
  · have : volCoord d ⁻¹' Iic t = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have : 0 ≤ volCoord d x := by unfold volCoord; positivity
      exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt hx ht)) (lt_irrefl 0)
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos ht.le]
  have hset : volCoord d ⁻¹' Iic t = closedBall (0 : Rd d) ((t / ballVol d) ^ ((d : ℝ)⁻¹)) := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_closedBall, dist_zero_right, volCoord]
    exact volCoord_le_iff hd (norm_nonneg x) ht
  have hr : 0 ≤ (t / ballVol d) ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg (div_nonneg ht hω.le) _
  rw [hset, Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin,
    Real.rpow_inv_natCast_pow (div_nonneg ht hω.le) (by omega)]
  have hb : volume (ball (0 : Rd d) 1) = ENNReal.ofReal (ballVol d) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  rw [hb, ← ENNReal.ofReal_mul (div_nonneg ht hω.le), div_mul_cancel₀ _ hω.ne']

/-- **Lebesgue measure in the volume coordinate**: `φ_*(Lebesgue on ℝ^d) = Lebesgue on (0,∞)`. -/
theorem map_volume_volCoord (hd : 1 ≤ d) :
    (volume : Measure (Rd d)).map (volCoord d) = volume.restrict (Ioi 0) := by
  have hIoc : ∀ a b : ℝ, a < b →
      (volume : Measure (Rd d)).map (volCoord d) (Ioc a b)
        = ENNReal.ofReal b - ENNReal.ofReal a := by
    intro a b hab
    have hdiff : Ioc a b = Iic b \ Iic a := by
      ext x; simp only [mem_Ioc, Set.mem_sdiff, mem_Iic, not_le]; exact and_comm
    rw [Measure.map_apply measurable_volCoord measurableSet_Ioc, hdiff, preimage_sdiff,
      measure_sdiff (preimage_mono (Iic_subset_Iic.mpr hab.le))
        (measurable_volCoord measurableSet_Iic).nullMeasurableSet
        (by rw [volume_volCoord_Iic hd]; exact ENNReal.ofReal_ne_top),
      volume_volCoord_Iic hd, volume_volCoord_Iic hd]
  have hfin : ∀ ⦃a b : ℝ⦄, a < b → (volume : Measure (Rd d)).map (volCoord d) (Ioc a b) ≠ ⊤ := by
    intro a b hab
    rw [hIoc a b hab]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
  refine Measure.ext_of_Ioc' _ _ hfin fun a b hab => ?_
  rw [hIoc a b hab, Measure.restrict_apply measurableSet_Ioc]
  rcases le_or_gt 0 a with ha | ha
  · rw [show Ioc a b ∩ Ioi 0 = Ioc a b from inter_eq_left.mpr fun x hx => lt_of_le_of_lt ha hx.1,
      Real.volume_Ioc,
      ENNReal.ofReal_sub _ ha]
  · have : Ioc a b ∩ Ioi 0 = Ioc 0 b := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_trans ha h1, h2⟩, h1⟩
    rw [this, Real.volume_Ioc, sub_zero, ENNReal.ofReal_of_nonpos ha.le, tsub_zero]

/-- The image of a density composed with the map: `(μ.withDensity (f ∘ g)).map g =
(μ.map g).withDensity f`. Mathlib types only. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {g : α → β} (hg : Measurable g) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun x => f (g x))).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]

/-- A density invariant under a linear isometry gives a measure invariant under it. -/
theorem map_withDensity_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) {f : Rd d → ℝ≥0∞} (hf : Measurable f)
    (hfQ : ∀ x, f (Q x) = f x) :
    ((volume : Measure (Rd d)).withDensity f).map Q = (volume : Measure (Rd d)).withDensity f := by
  have hQ := Q.measurePreserving
  ext s hs
  rw [Measure.map_apply Q.continuous.measurable hs,
    withDensity_apply _ (Q.continuous.measurable hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hQ.map_eq, setLIntegral_map hs hf Q.continuous.measurable]
  simp_rw [hfQ]

/-! ## No atom at the origin -/

/-- `‖Rξ‖ → ∞` as `R → ∞`, for `ξ ≠ 0`. -/
theorem tendsto_smul_cocompact {ξ : Rd d} (hξ : ξ ≠ 0) :
    Tendsto (fun R : ℝ => R • ξ) atTop (cocompact (Rd d)) := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, tendsto_comap_iff]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  refine (tendsto_id.atTop_mul_const hn).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp [norm_smul, Real.norm_of_nonneg hR]

/-- **No atom at the origin** (`prop:isotropic-radial-monotone`, the paragraph of that name): a
probability measure on `ℝ^d` with real transform tending to `0` at infinity does not charge the
origin. Heat-kernel smoothing at variance `R⁻²` and the substitution `ξ = Ry`. -/
theorem measure_singleton_zero_of_tendsto (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hreal : ∀ ξ : Rd d, (charFun μ ξ).im = 0)
    (hlim : Tendsto (fun ξ => ‖charFun μ ξ‖) (cocompact (Rd d)) (𝓝 0)) : μ {0} = 0 := by
  set re : Rd d → ℝ := fun ξ => (charFun μ ξ).re with hre
  have hre_le : ∀ ξ, |re ξ| ≤ ‖charFun μ ξ‖ := fun ξ => Complex.abs_re_le_norm _
  have hre_cont : Continuous re := Complex.continuous_re.comp continuous_charFun
  have hpi : 0 < 2 * Real.pi := by positivity
  set C : ℝ := (2 * Real.pi) ^ ((d : ℝ) / 2) * (2 * Real.pi) ^ (-(d : ℝ)) with hC
  set J : ℝ → ℝ := fun R => ∫ y : Rd d, re (R • y) * Real.exp (-‖y‖ ^ 2 / 2) with hJ
  -- the bound at one scale
  have hbound : ∀ R : ℝ, 0 < R → (μ {0}).toReal ≤ C * J R := by
    intro R hR
    set t : ℝ := (R ^ 2)⁻¹ with ht
    have ht0 : 0 < t := by positivity
    have hint1 : Integrable (fun x : Rd d => Real.exp (-‖x‖ ^ 2 / (2 * t))) μ :=
      Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        have : 0 ≤ ‖x‖ ^ 2 / (2 * t) := by positivity
        rw [neg_div]; linarith)
    have h1 : (μ {0}).toReal ≤ ∫ x, Real.exp (-‖x‖ ^ 2 / (2 * t)) ∂μ := by
      rw [← measureReal_def, ← integral_indicator_one (measurableSet_singleton 0)]
      refine integral_mono ((integrable_const 1).indicator (measurableSet_singleton 0)) hint1
        fun x => ?_
      by_cases hx : x = 0
      · subst hx; simp
      · rw [indicator_of_notMem (by simpa using hx)]; exact (Real.exp_pos _).le
    have h2 : ∫ x, Real.exp (-‖x‖ ^ 2 / (2 * t)) ∂μ
        = (2 * Real.pi * t) ^ ((d : ℝ) / 2) * ∫ x, heatKernel d t x ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [heatKernel]
      rw [← mul_assoc, ← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
        Real.rpow_zero, one_mul]
    have h3 := integral_heatKernel_eq μ hreal ht0
    -- the substitution `ξ = R y`
    have h4 : ∫ ξ, re ξ * Real.exp (-(t * ‖ξ‖ ^ 2) / 2) = R ^ d * J R := by
      have hs := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Rd d))
        (fun ξ => re ξ * Real.exp (-(t * ‖ξ‖ ^ 2) / 2)) R
      rw [finrank_euclideanSpace_fin] at hs
      have hJR : J R = ∫ y : Rd d, re (R • y) * Real.exp (-(t * ‖R • y‖ ^ 2) / 2) := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only
        congr 2
        rw [norm_smul, Real.norm_of_nonneg hR.le, mul_pow, ← mul_assoc, ht,
          inv_mul_cancel₀ (by positivity), one_mul]
      rw [hJR, hs, smul_eq_mul, ← mul_assoc, abs_of_pos (by positivity), mul_inv_cancel₀
        (by positivity), one_mul]
    rw [h2, h3, h4] at h1
    have hRd : ((R ^ 2 : ℝ)) ^ ((d : ℝ) / 2) = R ^ d := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R d]
      congr 1; push_cast; ring
    have key : (2 * Real.pi * t) ^ ((d : ℝ) / 2) * R ^ d = (2 * Real.pi) ^ ((d : ℝ) / 2) := by
      rw [Real.mul_rpow hpi.le ht0.le, ht, Real.inv_rpow (by positivity), hRd, mul_assoc,
        inv_mul_cancel₀ (by positivity), mul_one]
    calc (μ {0}).toReal ≤ _ := h1
      _ = ((2 * Real.pi * t) ^ ((d : ℝ) / 2) * R ^ d) * (2 * Real.pi) ^ (-(d : ℝ)) * J R := by ring
      _ = C * J R := by rw [key, hC]
  -- the limit
  have hlimJ : Tendsto J atTop (𝓝 0) := by
    have hg := integrable_rexp_neg_mul_sq_norm_Rd d (by norm_num : (0 : ℝ) < 1 / 2)
    have h0 : (0 : ℝ) = ∫ y : Rd d, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => Real.exp (-(1 / 2) * ‖y‖ ^ 2)) (Eventually.of_forall fun R => ?_)
      (Eventually.of_forall fun R => ae_of_all _ fun y => ?_) hg ?_
    · exact ((hre_cont.comp (continuous_const.smul continuous_id)).mul
        (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |re (R • y)| * Real.exp (-‖y‖ ^ 2 / 2) ≤ 1 * Real.exp (-‖y‖ ^ 2 / 2) := by
            gcongr
            exact (hre_le _).trans (norm_charFun_le_one _)
        _ = Real.exp (-(1 / 2) * ‖y‖ ^ 2) := by ring_nf
    · have hne : ∀ᵐ y ∂(volume : Measure (Rd d)), y ≠ 0 := by
        haveI : Nontrivial (Rd d) := by
          haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
          infer_instance
        rw [ae_iff]
        simp only [ne_eq, not_not, setOf_eq_eq_singleton]
        exact measure_singleton 0
      filter_upwards [hne] with y hy
      have hT := hlim.comp (tendsto_smul_cocompact hy)
      have hT' : Tendsto (fun R : ℝ => re (R • y)) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun R => ?_) hT
        rw [Real.norm_eq_abs]
        exact hre_le _
      simpa using hT'.mul_const (Real.exp (-‖y‖ ^ 2 / 2))
  have hlim2 : Tendsto (fun R => C * J R) atTop (𝓝 0) := by simpa using hlimJ.const_mul C
  have hle : (μ {0}).toReal ≤ 0 :=
    ge_of_tendsto hlim2 ((eventually_gt_atTop 0).mono fun R hR => hbound R hR)
  have h0 : (μ {0}).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-! ## The density from the mixture -/

/-- `φ(x) ≤ 0` only at the origin. -/
theorem volCoord_preimage_Iic_zero (hd : 1 ≤ d) : volCoord d ⁻¹' Iic 0 = {0} := by
  ext x
  simp only [mem_preimage, mem_Iic, mem_singleton_iff, volCoord]
  constructor
  · intro h
    by_contra hx
    have : 0 < ballVol d * ‖x‖ ^ d := mul_pos ballVol_pos (pow_pos (norm_pos_iff.mpr hx) d)
    linarith
  · rintro rfl
    simp [zero_pow (by omega : d ≠ 0)]

/-- `|x| = (φ(x)/ω_d)^{1/d}`. -/
theorem norm_eq_volCoord (hd : 1 ≤ d) (x : Rd d) :
    ‖x‖ = (volCoord d x / ballVol d) ^ ((d : ℝ)⁻¹) := by
  rw [volCoord, mul_div_cancel_left₀ _ ballVol_pos.ne',
    Real.pow_rpow_inv_natCast (norm_nonneg x) (by omega)]

/-- **`prop:isotropic-radial-monotone`, the density**: a probability measure on `ℝ^d`, invariant
under every linear isometry, null at the origin, and a mixture `∫ u_K Λ(du_K)` of Kanter's uniform
laws, has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`. -/
theorem radial_density_of_mixture (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, μ.map Q = μ) (h0 : μ {0} = 0)
    (Λ : Measure (Measure (Rd d))) (hΛ : ∀ᵐ ν ∂Λ, IsKanterUniform ν) (hjoin : Λ.join = μ) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hω := ballVol_pos (d := d)
  set m := μ.map (volCoord d) with hm
  have hm0 : m (Iic 0) = 0 := by
    rw [hm, Measure.map_apply measurable_volCoord measurableSet_Iic,
      volCoord_preimage_Iic_zero hd, h0]
  -- the distribution function in the volume coordinate is a mixture of concave functions
  have hG : ∀ v, m (Ioc 0 v) = ∫⁻ ν, ν (volCoord d ⁻¹' Ioc 0 v) ∂Λ := by
    intro v
    rw [hm, Measure.map_apply measurable_volCoord measurableSet_Ioc, ← hjoin,
      Measure.join_apply (measurable_volCoord measurableSet_Ioc)]
  have hconcE : ConcaveENN fun v => m (Ioc 0 v) := by
    have : (fun v => m (Ioc 0 v)) = fun v => ∫⁻ ν, ν (volCoord d ⁻¹' Ioc 0 v) ∂Λ := funext hG
    rw [this]
    refine ConcaveENN.lintegral ?_
    filter_upwards [hΛ] with ν hν
    obtain ⟨K, hKne, hKc, hKcv, hKs, rfl⟩ := hν
    exact concaveENN_kanterUniform hd hKne hKc hKcv hKs
  have hconc := hconcE.concaveOn_toReal fun v => measure_ne_top _ _
  obtain ⟨D, hDnn, hDanti, hmD⟩ := exists_antitone_density_of_concave m hm0 hconc
  -- a measurable version of the density
  set D' : ℝ → ℝ := (Ioi (0 : ℝ)).indicator D with hD'
  have hD'm : Measurable D' := measurable_indicator_Ioi_of_antitoneOn hDanti
  have hmD' : m = (volume.restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal (D' v) := by
    rw [hmD]
    refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun v (hv : v ∈ Ioi 0) => ?_))
    simp only [hD', indicator_of_mem hv]
  set q : ℝ → ℝ := fun r => D' (ballVol d * r ^ d) with hq
  have hqpos : ∀ r, 0 < r → ballVol d * r ^ d ∈ Ioi (0 : ℝ) := fun r hr => mul_pos hω (pow_pos hr d)
  refine ⟨q, fun r hr => ?_, fun r hr s hs hrs => ?_, ?_⟩
  · simp only [hq, hD', indicator_of_mem (hqpos r hr)]
    exact hDnn _ (hqpos r hr)
  · simp only [hq, hD', indicator_of_mem (hqpos r hr), indicator_of_mem (hqpos s hs)]
    exact hDanti (hqpos r hr) (hqpos s hs)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr) hrs d) hω.le)
  -- the candidate `q(|x|) dx` has the image `m` in the volume coordinate
  set f : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (q ‖x‖) with hf
  have hfD : f = fun x => (fun v => ENNReal.ofReal (D' v)) (volCoord d x) := rfl
  have hfm : Measurable f := by
    rw [hfD]; exact (hD'm.comp measurable_volCoord).ennreal_ofReal
  set ν' := (volume : Measure (Rd d)).withDensity f with hν'
  have hmap : ν'.map (volCoord d) = m := by
    rw [hν', hfD, map_withDensity_comp _ measurable_volCoord hD'm.ennreal_ofReal,
      map_volume_volCoord hd, hmD']
  -- so the same radial image
  have hψ : Measurable fun t : ℝ => (t / ballVol d) ^ ((d : ℝ)⁻¹) :=
    (measurable_id.div_const _).pow_const _
  have hnorm : (fun x : Rd d => ‖x‖) = (fun t => (t / ballVol d) ^ ((d : ℝ)⁻¹)) ∘ volCoord d := by
    funext x; exact norm_eq_volCoord hd x
  have hrad : μ.map (fun x => ‖x‖) = ν'.map (fun x => ‖x‖) := by
    rw [hnorm, ← Measure.map_map hψ measurable_volCoord, ← Measure.map_map hψ measurable_volCoord,
      hmap]
  haveI : IsFiniteMeasure ν' := ⟨by
    have h := congrArg (fun m' : Measure ℝ => m' univ) hmap
    simp only [Measure.map_apply measurable_volCoord MeasurableSet.univ, preimage_univ] at h
    rw [h]; exact measure_lt_top _ _⟩
  have hν'0 : ν' {0} = 0 := by
    rw [hν', withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_eq_zero.mpr (measure_singleton 0), lintegral_zero_measure]
  exact eq_of_rotationInvariant hd hrot
    (fun Q => map_withDensity_isometry Q hfm fun x => by
      simp only [hf, LinearIsometryEquiv.norm_map])
    h0 hν'0 (fun _ _ => measure_ne_top _ _) (fun _ _ => measure_ne_top _ _) hrad

/-- **`prop:isotropic-radial-monotone`, from the four properties**: a probability measure on
`ℝ^d`, invariant under every linear isometry, self-decomposable, with real transform tending to `0`
at infinity, has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`. Spends A8. -/
theorem radial_monotone_of_selfDecomposable (hd : 1 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, μ.map Q = μ)
    (hsd : IsSelfDecomposableSato μ) (hreal : ∀ ξ : Rd d, (charFun μ ξ).im = 0)
    (hlim : Tendsto (fun ξ => ‖charFun μ ξ‖) (cocompact (Rd d)) (𝓝 0)) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) := by
  have hsym : μ.map (fun x => -x) = μ := by
    have h := hrot (LinearIsometryEquiv.neg ℝ)
    rwa [LinearIsometryEquiv.coe_neg] at h
  obtain ⟨Λ, -, hΛ, hjoin⟩ := wolfe_symmetric_unimodal μ hsym hsd
  exact radial_density_of_mixture hd μ hrot (measure_singleton_zero_of_tendsto hd μ hreal hlim)
    Λ hΛ hjoin

/-! ## The decay of the transform -/

/-- A datum whose profile is not almost everywhere `0` has `c = k_d(0+) > 0`. -/
theorem OriginDatum.profileAtOrigin_pos_of_nontrivial (D : OriginDatum d)
    (hk : ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0) : 0 < D.profileAtOrigin := by
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  apply hk
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun r (hr : 0 < r) => ?_)
  have h1 : ENNReal.ofReal (D.k r) ≤ D.profileAtOrigin := D.ofReal_k_le hr
  rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (D.k_nonneg r hr)

/-- **The transform of a nontrivial datum's law tends to `0` at infinity**: through the Gaussian
part when `a > 0`, and through `lem:origin-decay-exponent` when `a = 0`. -/
theorem IsLawOf.tendsto_norm_charFun (hd : 1 ≤ d) {D : OriginDatum d} {μ : Measure (Rd d)}
    (hμ : IsLawOf D μ) (hD : 0 < D.a ∨ ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0) :
    Tendsto (fun ξ => ‖charFun μ ξ‖) (cocompact (Rd d)) (𝓝 0) := by
  by_cases ha : 0 < D.a
  · have hle : ∀ ξ : Rd d, ‖charFun μ ξ‖ ≤ Real.exp (-(D.a / 2 * ‖ξ‖ ^ 2)) := by
      intro ξ
      rw [hμ.norm_charFun]
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      have hfin := (ENNReal.add_ne_top.mp (D.exponentL_ne_top hd ξ)).2
      rw [OriginDatum.exponent, OriginDatum.exponentL,
        ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
        ENNReal.toReal_ofReal (by positivity)]
      have : 0 ≤ (∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) ∂D.levyMeasure).toReal :=
        ENNReal.toReal_nonneg
      linarith
    have hT : Tendsto (fun ξ : Rd d => Real.exp (-(D.a / 2 * ‖ξ‖ ^ 2))) (cocompact (Rd d))
        (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => D.a / 2 * r ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)
      exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).comp tendsto_norm_cocompact_atTop
    exact squeeze_zero (fun ξ => norm_nonneg _) hle hT
  · have ha0 : D.a = 0 := le_antisymm (not_lt.mp ha) D.a_nonneg
    have hc := D.profileAtOrigin_pos_of_nontrivial (hD.resolve_left ha)
    obtain ⟨β, -, hβpos, hβc⟩ := ENNReal.lt_iff_exists_real_btwn.mp hc
    have hβ : 0 < β := ENNReal.ofReal_pos.mp hβpos
    obtain ⟨C, hC⟩ := origin_decay_exponent hd D ha0 hc μ hμ β hβc
    have hT : Tendsto (fun ξ : Rd d => C * (1 + ‖ξ‖) ^ (-β)) (cocompact (Rd d)) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => C * (1 + r) ^ (-β)) atTop (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop hβ).comp
          (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_mul C
        simpa using this
      exact h1.comp tendsto_norm_cocompact_atTop
    exact squeeze_zero (fun ξ => norm_nonneg _) hC hT

/-! ## Clause (2): the law of a nontrivial origin datum -/

/-- **`prop:isotropic-radial-monotone`(2)**: the law of a nontrivial isotropic origin datum
(`a > 0`, or `k_d` not a.e. `0`) has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on
`(0,∞)`. Spends A8, and A2 and A3(iii) through `polar_reading_converse`. -/
theorem radial_monotone_law (hd : 1 ≤ d) (D : OriginDatum d)
    (hD : 0 < D.a ∨ ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0)
    (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) := by
  haveI := hμ.1
  have hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, μ.map Q = μ := by
    intro Q
    refine Measure.ext_of_charFun (funext fun z => ?_)
    rw [charFun_map_isometry, hμ.2, hμ.2,
      D.exponent_eq_of_norm_eq (LinearIsometryEquiv.norm_map _ _)]
  obtain ⟨μ', hprob', hsd', -, hchar'⟩ := polar_reading_converse hd D
  haveI := hprob'
  have hμμ' : μ = μ' := Measure.ext_of_charFun (funext fun ξ => by rw [hμ.2, hchar'])
  have hsd : IsSelfDecomposableSato μ := by
    rw [hμμ', ← isSelfDecomposable_iff_sato]; exact hsd'
  exact radial_monotone_of_selfDecomposable hd μ hrot hsd hμ.charFun_im
    (hμ.tendsto_norm_charFun hd hD)

/-! ## Clause (1): the kernels from scale zero -/

/-- **An admissible exponent on the line is an origin datum in dimension `1`**: `[V, (2.3)]` with
coefficient `a_V` and profile `k` is the datum `(2a_V, k)`, the converse of
`OriginDatum.toSDProfile`. -/
noncomputable def sdProfileDatum (P : ScaleSpace.SDProfile) : OriginDatum 1 where
  a := 2 * P.a
  k := P.k
  a_nonneg := by have := P.a_nonneg; positivity
  k_nonneg := P.k_nonneg
  k_antitone := P.k_antitone
  integrable_near_zero := by
    refine ne_top_of_le_ne_top P.integrable_near_zero
      (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun x _ => by rw [mul_comm]))
  integrable_at_top := P.integrable_at_top

theorem sdProfileDatum_exponent (P : ScaleSpace.SDProfile) (ω : Rd 1) :
    (sdProfileDatum P).exponent ω = P.exponent ‖ω‖ := by
  have he : ‖‖ω‖ • ebasis (0 : Fin 1)‖ = ‖ω‖ := by simp [norm_smul, ebasis]
  rw [(sdProfileDatum P).exponent_eq_of_norm_eq he.symm, OriginDatum.exponent,
    OriginDatum.exponentL_line, ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponentL,
    cosProfileL]
  congr 1
  congr 1
  · show ENNReal.ofReal (2 * P.a * ‖ω‖ ^ 2 / 2) = ENNReal.ofReal (P.a * ‖ω‖ ^ 2)
    ring_nf
  · refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
    show ENNReal.ofReal (1 - Real.cos (x * ‖ω‖)) * ENNReal.ofReal (P.k x / x)
      = ENNReal.ofReal ((1 - Real.cos (‖ω‖ * x)) * P.k x / x)
    rw [mul_div_assoc, ENNReal.ofReal_mul (by linarith [Real.cos_le_one (‖ω‖ * x)]), mul_comm x]

/-- **A nonzero exponent of `𝒜_d` tends to infinity**: `e^{-F(r)} → 0` as `r → ∞`, read through
the datum `(2a_V, k)` in dimension `1`, whose law is the image of the law in `𝒜_d`'s definition on
a line, and `IsLawOf.tendsto_norm_charFun` at `d = 1`. -/
theorem tendsto_exp_neg_classA (hd : 1 ≤ d) {F : ℝ → ℝ} (hF : classA d F)
    (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) :
    Tendsto (fun r => Real.exp (-F r)) atTop (𝓝 0) := by
  obtain ⟨⟨P, hP⟩, μ', hprob', -, hchar'⟩ := hF
  haveI := hprob'
  haveI : NeZero d := ⟨by omega⟩
  set D₁ := sdProfileDatum P with hD₁
  have hed : ‖ebasis (0 : Fin d)‖ = 1 := by simp [ebasis]
  have he1 : ‖ebasis (0 : Fin 1)‖ = 1 := by simp [ebasis]
  have hμ₁ : IsLawOf D₁ (μ'.map (toLine d)) := by
    refine ⟨Measure.isProbabilityMeasure_map continuous_toLine.measurable.aemeasurable,
      fun ω => ?_⟩
    have hn : ‖⟪ebasis (0 : Fin 1), ω⟫ • ebasis (0 : Fin d)‖ = ‖ω‖ := by
      rw [norm_smul, hed, mul_one, Real.norm_eq_abs, ← norm_eq_abs_inner_ebasis_one]
    rw [charFun_map_toLine, hchar', hn, hP _ (norm_nonneg ω), hD₁, sdProfileDatum_exponent]
  have hrn : ∀ r : ℝ, 0 ≤ r → ‖r • ebasis (0 : Fin 1)‖ = r := fun r hr => by
    rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr]
  have hD₁nt : 0 < D₁.a ∨ ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D₁.k r = 0 := by
    by_contra hcon
    rw [not_or, not_lt, not_not] at hcon
    obtain ⟨r, hr, hFr⟩ := hFne
    apply hFr
    have ha : D₁.a = 0 := le_antisymm hcon.1 D₁.a_nonneg
    have h := D₁.exponent_eq_zero_of_trivial le_rfl ha hcon.2 (r • ebasis (0 : Fin 1))
    rw [hD₁, sdProfileDatum_exponent, hrn r hr] at h
    rw [hP r hr]; exact h
  have hT := hμ₁.tendsto_norm_charFun le_rfl hD₁nt
  have he0 : ebasis (0 : Fin 1) ≠ 0 := by
    rw [← norm_ne_zero_iff, he1]; exact one_ne_zero
  refine (hT.comp (tendsto_smul_cocompact he0)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with r hr
  simp only [Function.comp]
  rw [hμ₁.norm_charFun, hD₁, sdProfileDatum_exponent, hrn r hr, ← hP r hr]

/-- **`prop:isotropic-radial-monotone`(1)**: for an isotropic cascade family and `t > 0`, `μ_{0,t}`
has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`. Spends A8, and A3(ii)–(iii)
through `thm:isotropic-classification` (Paper V's interface until Q-0365). -/
theorem radial_monotone_family (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ)
    (hμ : IsIsotropicCascadeFamily μ S) {t : ℝ} (ht : 0 < t) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ 0 t = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) := by
  obtain ⟨χ, F, hχ, hF, hFne, hrep⟩ :=
    (isotropic_classification hd μ hμ.isProbability).mp ⟨S, hμ⟩
  have h0t := isotropic_classification_origin hd μ hμ.isProbability χ F hχ hF hrep t ht.le
  haveI := hμ.isProbability 0 t le_rfl ht.le
  set s := χ t with hsdef
  have hs : 0 < s := by
    have h := hχ.2.1 (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (mem_Ici.mpr ht.le) ht
    rwa [hχ.1] at h
  have hFlim := tendsto_exp_neg_classA hd hF hFne
  obtain ⟨-, μ', hprob', hsd', hchar'⟩ := hF
  haveI := hprob'
  have hform : ∀ ξ : Rd d, charFun (μ 0 t) ξ = charFun μ' (s • ξ) := by
    intro ξ; rw [h0t ξ, hchar', norm_smul, Real.norm_of_nonneg hs.le]
  have hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, (μ 0 t).map Q = μ 0 t := by
    intro Q
    refine Measure.ext_of_charFun (funext fun z => ?_)
    rw [charFun_map_isometry, h0t, h0t, LinearIsometryEquiv.norm_map]
  have hsd : IsSelfDecomposableSato (μ 0 t) := by
    rw [← isSelfDecomposable_iff_sato, ScaleSpace.isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    obtain ⟨ρ, hρ, hρeq⟩ := (ScaleSpace.isSelfDecomposable_iff_charFun μ').1 hsd' c hc0 hc1
    haveI := hρ
    refine ⟨push (s • (1 : Mat d)) ρ,
      Measure.isProbabilityMeasure_map (lin _).continuous.measurable.aemeasurable, fun ξ => ?_⟩
    rw [hform, hform, charFun_push_smul_one, hρeq (s • ξ), smul_comm c s ξ]
  have hreal : ∀ ξ : Rd d, (charFun (μ 0 t) ξ).im = 0 := fun ξ => by
    rw [h0t]; exact Complex.ofReal_im _
  have hlim : Tendsto (fun ξ => ‖charFun (μ 0 t) ξ‖) (cocompact (Rd d)) (𝓝 0) := by
    have h2 : Tendsto (fun ξ : Rd d => s * ‖ξ‖) (cocompact (Rd d)) atTop :=
      tendsto_norm_cocompact_atTop.const_mul_atTop hs
    refine (hFlim.comp h2).congr' (Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp]
    rw [h0t, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact radial_monotone_of_selfDecomposable hd (μ 0 t) hrot hsd hreal hlim

end AffineHemigroup
