/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SlowFactor
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The layer-cake identity of `prop:isotropic-exponent-profile`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, the proof of `prop:isotropic-exponent-profile`,
the steps headed *the layer-cake identity* and *the sphere average* (Q-0427).

For a nonincreasing profile `k` with `k(r) → 0` at infinity, put
`τ(y) = sup{r > 0 : k(r) > y}` (`OriginDatum.levelRadius`; `0` when the set is empty, which is the
case for `y ≥ c`). The superlevel set `{r > 0 : k(r) > y}` lies between `(0, τ(y))` and
`(0, τ(y)]`, so for every measurable `w ≥ 0`

  `∫_0^∞ w(r) k(r) dr = ∫_0^∞ (∫_0^{τ(y)} w(r) dr) dy`  (`OriginDatum.lintegral_mul_k`),

which is Mathlib's layer-cake formula `lintegral_eq_lintegral_meas_lt` for the measure `w(r) dr`.
With `w(r) = (1 - cos rs)/r` the inner integral is `Cin(s τ(y))`, and with
`w(r) = 1_{r > 1/ρ}/r` it is `log⁺(ρ τ(y))`. Hence, for `ρ > 0` and a real `s`
(`OriginDatum.cosProfile_sub_tail`),

  `φ(s) - ∫_{1/ρ}^∞ k(r) dr/r = ∫_0^c [Cin(s τ(y)) - log⁺(ρ τ(y))] dy`.

At `s = ρt` with `0 < |t| ≤ 1` the integrand lies in `[log|t| - 3, 13/4]`
(`cin_sub_posLog_bounds`) and tends to `g_∞ + log|t|` as `ρ → ∞` when `τ(y) > 0`
(`tendsto_cin_sub_posLog`), where `g_∞ = lim (Cin X - log X)` is the shared library's
`ScaleSpace.cinConst` (`tendsto_cin_sub_log`). The proof of record splits the integrand into the
two terms `log⁺(ρ|t|τ) - log⁺(ρτ)` and `G(ρ|t|τ)`; here they are kept together, with the same
bounds and the same limits.

Lean core: Mathlib types, the shared library's `cin`, and this module's datum.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter ScaleSpace
open scoped Topology ENNReal

variable {d : ℕ}

/-! ## The radius of a superlevel set -/

/-- **`τ(y) = sup{r > 0 : k_d(r) > y}`**, the right end of the superlevel set of the profile; `0`
when the set is empty. -/
noncomputable def OriginDatum.levelRadius (D : OriginDatum d) (y : ℝ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ y < D.k r}

theorem OriginDatum.levelSet_bddAbove (D : OriginDatum d) {y : ℝ} (hy : 0 < y) :
    BddAbove {r : ℝ | 0 < r ∧ y < D.k r} := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 D.tendsto_k_atTop).2 y hy)
  refine ⟨R, fun r hr => ?_⟩
  by_contra hcon
  push Not at hcon
  exact absurd (hR r hcon.le) (not_lt.2 hr.2.le)

theorem OriginDatum.levelRadius_nonneg (D : OriginDatum d) (y : ℝ) : 0 ≤ D.levelRadius y :=
  Real.sSup_nonneg fun _ hr => hr.1.le

theorem OriginDatum.levelSet_subset (D : OriginDatum d) {y : ℝ} (hy : 0 < y) :
    {r : ℝ | 0 < r ∧ y < D.k r} ⊆ Ioc 0 (D.levelRadius y) :=
  fun _ hr => ⟨hr.1, le_csSup (D.levelSet_bddAbove hy) hr⟩

theorem OriginDatum.Ioo_subset_levelSet (D : OriginDatum d) (y : ℝ) :
    Ioo 0 (D.levelRadius y) ⊆ {r : ℝ | 0 < r ∧ y < D.k r} := by
  intro r hr
  have hne : {r : ℝ | 0 < r ∧ y < D.k r}.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have h0 : D.levelRadius y = 0 := by rw [OriginDatum.levelRadius, hcon, Real.sSup_empty]
    rw [h0] at hr
    exact absurd hr.2 (not_lt.2 hr.1.le)
  obtain ⟨r', hr', hlt⟩ := exists_lt_of_lt_csSup hne hr.2
  exact ⟨hr.1, lt_of_lt_of_le hr'.2 (D.k_antitone hr.1 hr'.1 hlt.le)⟩

/-- `τ(y) > 0` for `0 < y < c`. -/
theorem OriginDatum.levelRadius_pos (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {y : ℝ}
    (hy : 0 < y) (hyc : y < D.profileAtOrigin.toReal) : 0 < D.levelRadius y := by
  have hlt : ENNReal.ofReal y < D.profileAtOrigin :=
    (ENNReal.ofReal_lt_iff_lt_toReal hy.le hc).2 hyc
  obtain ⟨⟨r₀, hr₀⟩, hr⟩ := lt_iSup_iff.mp hlt
  have hk : y < D.k r₀ := by
    by_contra hcon
    push Not at hcon
    exact absurd hr (not_lt.2 (ENNReal.ofReal_le_ofReal hcon))
  exact lt_of_lt_of_le hr₀ (le_csSup (D.levelSet_bddAbove hy) ⟨hr₀, hk⟩)

/-- `τ(y) = 0` for `y ≥ c`. -/
theorem OriginDatum.levelRadius_eq_zero (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {y : ℝ}
    (hy : D.profileAtOrigin.toReal ≤ y) : D.levelRadius y = 0 := by
  have hempty : {r : ℝ | 0 < r ∧ y < D.k r} = ∅ := by
    refine eq_empty_of_forall_notMem fun r hr => ?_
    exact absurd (lt_of_lt_of_le hr.2 (D.k_le_toReal hc hr.1)) (not_lt.2 hy)
  rw [OriginDatum.levelRadius, hempty, Real.sSup_empty]

theorem OriginDatum.levelRadius_antitoneOn (D : OriginDatum d) :
    AntitoneOn D.levelRadius (Ioi 0) := by
  intro y hy y' _ hyy'
  change sSup {r : ℝ | 0 < r ∧ y' < D.k r} ≤ D.levelRadius y
  by_cases hne : {r : ℝ | 0 < r ∧ y' < D.k r}.Nonempty
  · exact csSup_le_csSup (D.levelSet_bddAbove hy) hne fun r hr => ⟨hr.1, lt_of_le_of_lt hyy' hr.2⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact D.levelRadius_nonneg y

theorem OriginDatum.aemeasurable_levelRadius (D : OriginDatum d) :
    AEMeasurable D.levelRadius (volume.restrict (Ioi (0 : ℝ))) :=
  (measurable_indicator_Ioi_of_antitoneOn D.levelRadius_antitoneOn).aemeasurable.congr
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => by
      rw [indicator_of_mem hy]))

theorem OriginDatum.aemeasurable_k (D : OriginDatum d) :
    AEMeasurable D.k (volume.restrict (Ioi (0 : ℝ))) :=
  (measurable_indicator_Ioi_of_antitoneOn D.k_antitone).aemeasurable.congr
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => by
      rw [indicator_of_mem hr]))

/-! ## The layer-cake identity -/

/-- **The layer-cake identity for a nonincreasing profile**: for measurable `w ≥ 0`,
`∫_0^∞ w(r) k_d(r) dr = ∫_0^∞ (∫_{(0, τ(y)]} w(r) dr) dy`. -/
theorem OriginDatum.lintegral_mul_k (D : OriginDatum d) {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ r in Ioi (0 : ℝ), w r * ENNReal.ofReal (D.k r)
      = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ r in Ioc 0 (D.levelRadius y), w r := by
  set μ := (volume.restrict (Ioi (0 : ℝ))).withDensity w with hμ
  have hac : μ ≪ volume.restrict (Ioi (0 : ℝ)) := withDensity_absolutelyContinuous _ _
  have hkm : AEMeasurable D.k μ := D.aemeasurable_k.mono_ac hac
  have hnn : 0 ≤ᵐ[μ] D.k :=
    Filter.Eventually.filter_mono hac.ae_le
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall D.k_nonneg))
  have h1 : ∫⁻ r in Ioi (0 : ℝ), w r * ENNReal.ofReal (D.k r)
      = ∫⁻ r, ENNReal.ofReal (D.k r) ∂μ := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul₀ hw.aemeasurable
      D.aemeasurable_k.ennreal_ofReal]
    rfl
  rw [h1, lintegral_eq_lintegral_meas_lt μ hnn hkm]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  rw [hμ, withDensity_apply', Measure.restrict_restrict' measurableSet_Ioi]
  have hsub1 : Ioo 0 (D.levelRadius y) ⊆ {a | y < D.k a} ∩ Ioi 0 := fun r hr =>
    ⟨(D.Ioo_subset_levelSet y hr).2, hr.1⟩
  have hsub2 : {a | y < D.k a} ∩ Ioi 0 ⊆ Ioc 0 (D.levelRadius y) := fun r hr =>
    D.levelSet_subset hy ⟨hr.2, hr.1⟩
  refine le_antisymm (lintegral_mono_set hsub2) ?_
  rw [← setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := D.levelRadius y))]
  exact lintegral_mono_set hsub1

/-- **The cosine profile through the level radii**: `φ(s) = ∫_0^∞ Cin(s τ(y)) dy`. -/
theorem OriginDatum.cosProfileL_eq_lintegral_cin (D : OriginDatum d) (s : ℝ) :
    cosProfileL D.k s = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (cin (s * D.levelRadius y)) := by
  have hw : Measurable fun r : ℝ => ENNReal.ofReal ((1 - Real.cos (r * s)) / r) :=
    ((by fun_prop : Measurable fun r : ℝ => 1 - Real.cos (r * s)).div measurable_id).ennreal_ofReal
  have h := D.lintegral_mul_k hw
  have h0 : cosProfileL D.k s = ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos (r * s)) / r) * ENNReal.ofReal (D.k r) := by
    rw [cosProfileL]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have h1 : 0 ≤ 1 - Real.cos (r * s) := by linarith [Real.cos_le_one (r * s)]
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (div_nonneg h1 hr.le)]
    congr 1
    ring
  rw [h0, h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  exact lintegral_cos_div_eq_cin s (D.levelRadius_nonneg y)

/-- `∫_{(1/ρ, τ]} dr/r = log⁺(ρτ)` for `ρ > 0` and `τ ≥ 0`. -/
theorem lintegral_inv_Ioc_eq_posLog {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 ≤ τ) :
    ∫⁻ r in Ioc ρ⁻¹ τ, ENNReal.ofReal r⁻¹ = ENNReal.ofReal (Real.posLog (ρ * τ)) := by
  have hx : 0 < ρ⁻¹ := inv_pos.2 hρ
  rcases le_or_gt τ ρ⁻¹ with h | h
  · rw [Ioc_eq_empty (not_lt.2 h), Measure.restrict_empty, lintegral_zero_measure]
    have h1 : ρ * τ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h hρ.le
      rwa [mul_inv_cancel₀ hρ.ne'] at this
    rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (by positivity)]; exact h1),
      ENNReal.ofReal_zero]
  · have hint : IntervalIntegrable (fun r : ℝ => r⁻¹) volume ρ⁻¹ τ := by
      refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
      rw [uIcc_of_le h.le] at hv
      exact ne_of_gt (lt_of_lt_of_le hx hv.1)
    have h1 : 1 ≤ ρ * τ := by
      have := mul_le_mul_of_nonneg_left h.le hρ.le
      rwa [mul_inv_cancel₀ hρ.ne'] at this
    rw [← ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le h.le).1 hint)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
          inv_nonneg.2 (lt_trans hx hr.1).le)),
      ← intervalIntegral.integral_of_le h.le, integral_inv_of_pos hx (lt_trans hx h),
      Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact h1)]
    congr 2
    field_simp

/-- **The tail of the profile through the level radii**: for `ρ > 0`,
`∫_{1/ρ}^∞ k_d(r) dr/r = ∫_0^∞ log⁺(ρ τ(y)) dy`. -/
theorem OriginDatum.lintegral_k_div_Ioi_eq_posLog (D : OriginDatum d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ⁻¹, ENNReal.ofReal (D.k r / r)
      = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.posLog (ρ * D.levelRadius y)) := by
  have hx : 0 < ρ⁻¹ := inv_pos.2 hρ
  set w : ℝ → ℝ≥0∞ := (Ioi ρ⁻¹).indicator fun r => ENNReal.ofReal r⁻¹ with hwdef
  have hw : Measurable w := (measurable_inv.ennreal_ofReal).indicator measurableSet_Ioi
  have h0 : ∫⁻ r in Ioi ρ⁻¹, ENNReal.ofReal (D.k r / r)
      = ∫⁻ r in Ioi (0 : ℝ), w r * ENNReal.ofReal (D.k r) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ Ioi ρ⁻¹
    · have hr0 : (0 : ℝ) < r := lt_trans hx hr
      rw [indicator_of_mem hr, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr0), hwdef,
        indicator_of_mem hr, ← ENNReal.ofReal_mul (inv_nonneg.2 hr0.le)]
      congr 1
      ring
    · rw [indicator_of_notMem hr]
      by_cases hr0 : r ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hr0, hwdef, indicator_of_notMem hr, zero_mul]
      · rw [indicator_of_notMem hr0]
  rw [h0, D.lintegral_mul_k hw]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [hwdef, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi ρ⁻¹ ∩ Ioc 0 (D.levelRadius y) = Ioc ρ⁻¹ (D.levelRadius y) := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, lt_trans hx h.1, h.2⟩⟩
  rw [hset]
  exact lintegral_inv_Ioc_eq_posLog hρ (D.levelRadius_nonneg y)

/-- **`eq:profile-layer-cake`, in one integrand**: for `ρ > 0` and a real `s`,
`φ(s) - ∫_{1/ρ}^∞ k_d(r) dr/r = ∫_0^c [Cin(s τ(y)) - log⁺(ρ τ(y))] dy`, the integrand being
integrable on `(0, c]`. -/
theorem OriginDatum.cosProfile_sub_tail (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) :
    IntegrableOn (fun y => cin (s * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y))
        (Ioc 0 D.profileAtOrigin.toReal) ∧
      (cosProfileL D.k s).toReal - ∫ r in Ioi ρ⁻¹, D.k r / r
        = ∫ y in Ioc (0 : ℝ) D.profileAtOrigin.toReal,
            (cin (s * D.levelRadius y) - Real.posLog (ρ * D.levelRadius y)) := by
  set c := D.profileAtOrigin.toReal with hcdef
  have hx : 0 < ρ⁻¹ := inv_pos.2 hρ
  set g1 : ℝ → ℝ := fun y => cin (s * D.levelRadius y) with hg1
  set g2 : ℝ → ℝ := fun y => Real.posLog (ρ * D.levelRadius y) with hg2
  have hτm := D.aemeasurable_levelRadius
  have hm1 : AEMeasurable g1 (volume.restrict (Ioi (0 : ℝ))) :=
    continuous_cin.measurable.comp_aemeasurable (hτm.const_mul s)
  have hm2 : AEMeasurable g2 (volume.restrict (Ioi (0 : ℝ))) := by
    have : Measurable Real.posLog := by
      unfold Real.posLog
      exact measurable_const.max Real.measurable_log
    exact this.comp_aemeasurable (hτm.const_mul ρ)
  have hnn1 : ∀ y, 0 ≤ g1 y := fun y => cin_nonneg' _
  have hnn2 : ∀ y, 0 ≤ g2 y := fun y => Real.posLog_nonneg
  have hfin1 : cosProfileL D.k s ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      D.integrable_near_zero, ENNReal.mul_ne_top (by norm_num) D.integrable_at_top⟩)
      (cosProfileL_le_sq D.k D.k_nonneg s)
  have hkint := D.integrableOn_k_div_Ioi hx
  have hknn : 0 ≤ᵐ[volume.restrict (Ioi ρ⁻¹)] fun r => D.k r / r :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : ρ⁻¹ < r) =>
      div_nonneg (D.k_nonneg r (lt_trans hx hr)) (lt_trans hx hr).le)
  have hL1 : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (g1 y) = cosProfileL D.k s :=
    (D.cosProfileL_eq_lintegral_cin s).symm
  have hL2 : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (g2 y)
      = ENNReal.ofReal (∫ r in Ioi ρ⁻¹, D.k r / r) := by
    rw [← D.lintegral_k_div_Ioi_eq_posLog hρ, ofReal_integral_eq_lintegral_ofReal hkint hknn]
  have hi1 : IntegrableOn g1 (Ioi 0) := by
    refine ⟨hm1.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 (hL1 ▸ hfin1))
    exact lintegral_congr fun y => Real.enorm_eq_ofReal (hnn1 y)
  have hi2 : IntegrableOn g2 (Ioi 0) := by
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 (hL2 ▸ ENNReal.ofReal_ne_top))
    exact lintegral_congr fun y => Real.enorm_eq_ofReal (hnn2 y)
  have hv1 : ∫ y in Ioi (0 : ℝ), g1 y = (cosProfileL D.k s).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn1)
      hm1.aestronglyMeasurable, hL1]
  have hv2 : ∫ y in Ioi (0 : ℝ), g2 y = ∫ r in Ioi ρ⁻¹, D.k r / r := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn2)
      hm2.aestronglyMeasurable, hL2, ENNReal.toReal_ofReal (integral_nonneg_of_ae hknn)]
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hzero : ∀ y ∈ Ioi (0 : ℝ) \ Ioc 0 c, g1 y - g2 y = 0 := by
    intro y hy
    have hyc : c ≤ y := by
      by_contra hcon
      push Not at hcon
      exact hy.2 ⟨hy.1, hcon.le⟩
    simp only [hg1, hg2]
    rw [D.levelRadius_eq_zero hc hyc, mul_zero, mul_zero, cin_zero]
    simp [Real.posLog]
  refine ⟨(hi1.sub hi2).mono_set Ioc_subset_Ioi_self, ?_⟩
  rw [← hv1, ← hv2, ← integral_sub hi1 hi2]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero

/-! ## The integrand: bounds and limit -/

/-- `Cin(X) ≤ log⁺ X + 13/4` for `X ≥ 0`. -/
theorem cin_le_posLog_add {X : ℝ} (hX : 0 ≤ X) : cin X ≤ Real.posLog X + 13 / 4 := by
  rcases le_total 1 X with h | h
  · rw [Real.posLog_eq_log (by rwa [abs_of_nonneg hX])]
    exact cin_le_log_add h
  · have h1 := cin_le_sq X
    rw [(Real.posLog_eq_zero_iff X).2 (by rwa [abs_of_nonneg hX])]
    nlinarith

/-- `log⁺ X - 3 ≤ Cin(X)` for `X ≥ 0`. -/
theorem posLog_sub_le_cin {X : ℝ} (hX : 0 ≤ X) : Real.posLog X - 3 ≤ cin X := by
  rcases le_total 1 X with h | h
  · rw [Real.posLog_eq_log (by rwa [abs_of_nonneg hX])]
    exact log_sub_le_cin (by linarith)
  · rw [(Real.posLog_eq_zero_iff X).2 (by rwa [abs_of_nonneg hX])]
    linarith [cin_nonneg hX]

/-- For `P ≥ 0` and `0 < |t| ≤ 1`: `log|t| - 3 ≤ Cin(tP) - log⁺ P ≤ 13/4`. -/
theorem cin_sub_posLog_bounds {P t : ℝ} (hP : 0 ≤ P) (ht : t ≠ 0) (ht1 : |t| ≤ 1) :
    Real.log |t| - 3 ≤ cin (t * P) - Real.posLog P ∧ cin (t * P) - Real.posLog P ≤ 13 / 4 := by
  have habs : 0 < |t| := abs_pos.2 ht
  have hcin : cin (t * P) = cin (|t| * P) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, cin_neg]
  set X := |t| * P with hXdef
  have hX : 0 ≤ X := by positivity
  have hXP : X ≤ P := by nlinarith
  have h1 := cin_le_posLog_add hX
  have h2 := posLog_sub_le_cin hX
  have h3 : Real.posLog X ≤ Real.posLog P := Real.posLog_le_posLog hX hXP
  have h4 : Real.posLog P ≤ Real.posLog X - Real.log |t| := by
    have hP' : P = X * |t|⁻¹ := by rw [hXdef]; field_simp
    have h5 := Real.posLog_mul (x := X) (y := |t|⁻¹)
    rw [← hP'] at h5
    have h6 : Real.posLog |t|⁻¹ = -Real.log |t| := by
      rw [Real.posLog_eq_log (by rw [abs_inv, abs_abs]; exact (one_le_inv₀ habs).2 ht1),
        Real.log_inv]
    linarith
  rw [hcin]
  constructor <;> linarith

/-- **`g_∞` exists**: `Cin(X) - log X → g_∞` as `X → ∞`, with `g_∞` the shared library's
`ScaleSpace.cinConst`. -/
theorem tendsto_cin_sub_log : Tendsto (fun X : ℝ => cin X - Real.log X) atTop (𝓝 cinConst) := by
  have h : Tendsto (fun X : ℝ => 2 * X⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 2
  refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ h)
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_eq_abs]
  exact cin_expansion_top_bound hX

/-- For `t ≠ 0` and `τ > 0`: `Cin(ρtτ) - log⁺(ρτ) → g_∞ + log|t|` as `ρ → ∞`. -/
theorem tendsto_cin_sub_posLog {t τ : ℝ} (ht : t ≠ 0) (hτ : 0 < τ) :
    Tendsto (fun ρ : ℝ => cin (ρ * t * τ) - Real.posLog (ρ * τ)) atTop
      (𝓝 (cinConst + Real.log |t|)) := by
  have habs : 0 < |t| := abs_pos.2 ht
  have hX : Tendsto (fun ρ : ℝ => ρ * (|t| * τ)) atTop atTop :=
    tendsto_id.atTop_mul_const (by positivity)
  have h1 := (tendsto_cin_sub_log.comp hX).add_const (Real.log |t|)
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (1 / (|t| * τ)), eventually_ge_atTop (1 / τ),
    eventually_gt_atTop 0] with ρ h1 h2 hρ
  simp only [Function.comp_apply]
  have hP1 : 1 ≤ ρ * τ := by rwa [div_le_iff₀ hτ] at h2
  have hcin : cin (ρ * t * τ) = cin (ρ * (|t| * τ)) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, mul_assoc]
    · rw [h, show ρ * (-t * τ) = -(ρ * t * τ) by ring, cin_neg]
  rw [hcin, Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact hP1),
    Real.log_mul hρ.ne' (by positivity), Real.log_mul hρ.ne' hτ.ne',
    Real.log_mul habs.ne' hτ.ne']
  ring

end AffineHemigroup
