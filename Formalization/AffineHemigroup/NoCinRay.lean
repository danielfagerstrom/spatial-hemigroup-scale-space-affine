/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarClassification
import AffineHemigroup.FiltrationStrict
import AffineHemigroup.OriginDecay
import ScaleSpaceCore.CinRays
import ScaleSpaceCore.SDProfileCone

/-!
# `thm:no-cin-ray-in-the-plane`: no `Cin` ray reaches the plane

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `thm:no-cin-ray-in-the-plane`. Wave 2, group A
(Q-0281).

The blueprint's route, with its two density estimates read at the level of measures. Suppose
`ξ ↦ b Cin(τ|ξ|)` is the exponent of a self-decomposable law on `ℝ^d`, `d ≥ 2`. The polar reading
gives an origin datum `(a, k_d)` with Lévy measure `ν_d`. Its shadow `ν̄` on the first axis
(the image under `x ↦ ⟨e₁,x⟩`, off the origin) is a symmetric Lévy measure on the line, and
`(aI, ν̄, 0)` has the exponent of the ray's datum `(0, b 1_{(0,τ)})` in dimension `1`; A3(iii) and
A3(ii) identify `ν̄` with that datum's Lévy measure. So the slab `{τ < |x₁|}` is `ν_d`-null, and
by rotation and a dense sequence of directions `k_d = 0` on `(τ,∞)`. Then the slab
`{τ(1-ε) < |x₁| < τ}` has `ν_d`-mass at most a constant times `ε σ(cap_ε)`, the cap
`{|⟨e₁,η⟩| > 1 - ε}` shrinking to the two poles, which are `σ`-null when `d ≥ 2`; while the ray's
measure gives the same slab mass at least `bε`. Letting `ε → 0` is a contradiction.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The ray and its datum on the line -/

/-- **`thm:no-cin-ray-in-the-plane`**, the ray: `F(ω) = b Cin(τ|ω|)` is the admissible exponent
with Gaussian coefficient `0` and profile `b 1_{(0,τ)}` ([B, Lem. 3.1], Paper V's `cin_ray`
scaled by `b`). -/
theorem cin_ray_scaled {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ∃ P : ScaleSpace.SDProfile, P.a = 0 ∧
      (∀ x ∈ Ioi (0 : ℝ), P.k x = b * ScaleSpace.cinProfile τ x) ∧
      ∀ ω : ℝ, P.exponent ω = b * ScaleSpace.cin (τ * |ω|) := by
  obtain ⟨Q, hQa, hQk, hQe⟩ := ScaleSpace.cin_ray hτ
  refine ⟨Q.smul hb.le, by simp [hQa], fun x _ => by simp [hQk], fun ω => ?_⟩
  rw [ScaleSpace.SDProfile.exponent_smul, hQe]
  congr 1
  rcases le_or_gt 0 ω with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, ScaleSpace.cin_neg]

/-- The ray's datum in dimension `1`: `(0, b 1_{(0,τ)})`. -/
noncomputable def cinDatum {τ b : ℝ} (_hτ : 0 < τ) (hb : 0 < b) : OriginDatum 1 where
  a := 0
  k := fun r => b * ScaleSpace.cinProfile τ r
  a_nonneg := le_rfl
  k_nonneg := fun r _ => mul_nonneg hb.le (ScaleSpace.cinProfile_nonneg τ r)
  k_antitone := by
    intro r (hr : 0 < r) s (hs : 0 < s) hrs
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    unfold ScaleSpace.cinProfile
    by_cases h : s ∈ Ioo (0 : ℝ) τ
    · rw [indicator_of_mem h, indicator_of_mem (show r ∈ Ioo (0 : ℝ) τ from ⟨hr, by linarith [h.2]⟩)]
      rfl
    · rw [indicator_of_notMem h]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  integrable_near_zero := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal b) ?_
      (setLIntegral_mono' measurableSet_Ioo fun r hr => ENNReal.ofReal_le_ofReal ?_)
    · rw [setLIntegral_const, Real.volume_Ioo]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top
    · have h1 := ScaleSpace.cinProfile_le_one τ r
      have h0 := ScaleSpace.cinProfile_nonneg τ r
      have : b * ScaleSpace.cinProfile τ r * r ≤ b * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hb.le) hr.2.le hr.1.le (by positivity)
      linarith
  integrable_at_top := by
    refine ne_top_of_le_ne_top (b := ∫⁻ r, (Ioo (0 : ℝ) τ).indicator (fun _ => ENNReal.ofReal b) r) ?_
      ((setLIntegral_le_lintegral _ _).trans' (setLIntegral_mono' measurableSet_Ioi fun r hr => ?_))
    · rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · have hr1 : (1 : ℝ) < r := hr
      unfold ScaleSpace.cinProfile
      by_cases h : r ∈ Ioo (0 : ℝ) τ
      · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, mul_one]
        exact ENNReal.ofReal_le_ofReal (div_le_self hb.le hr1.le)
      · rw [indicator_of_notMem h, indicator_of_notMem h]; simp

theorem cinDatum_exponent {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) (ω : Rd 1) :
    (cinDatum hτ hb).exponent ω = b * ScaleSpace.cin (τ * ‖ω‖) := by
  obtain ⟨P', hP'a, hP'k, hP'e⟩ := (cinDatum hτ hb).toSDProfile
  obtain ⟨P, hPa, hPk, hPe⟩ := cin_ray_scaled hτ hb
  have hu : ‖ebasis (0 : Fin 1)‖ = 1 := by simp [ebasis]
  rw [(cinDatum hτ hb).exponent_eq_of_norm_eq (ξ' := ‖ω‖ • ebasis (0 : Fin 1))
    (by rw [norm_smul, hu, mul_one, norm_norm]), ← hP'e]
  have hcongr : P'.exponent ‖ω‖ = P.exponent ‖ω‖ := by
    rw [ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponent,
      ScaleSpace.SDProfile.exponentL, ScaleSpace.SDProfile.exponentL, hP'a, hPa]
    congr 2
    · simp [cinDatum]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [hP'k x hx, hPk x hx]
      rfl
  rw [hcongr, hPe, abs_of_nonneg (norm_nonneg ω)]

theorem cinDatum_levyMeasure_gt {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (cinDatum hτ hb).levyMeasure {y | τ < ‖y‖} = 0 := by
  rw [OriginDatum.levyMeasure, withDensity_apply _ (measurableSet_lt measurable_const
    continuous_norm.measurable)]
  refine setLIntegral_eq_zero (measurableSet_lt measurable_const continuous_norm.measurable)
    fun y (hy : τ < ‖y‖) => ?_
  have hy0 : y ≠ 0 := by
    rintro rfl; simp at hy; linarith
  rw [indicator_of_mem (show y ∈ ({0}ᶜ : Set (Rd 1)) from hy0)]
  simp only [cinDatum, ScaleSpace.cinProfile]
  rw [indicator_of_notMem (fun h : ‖y‖ ∈ Ioo (0 : ℝ) τ => absurd h.2 (not_lt.2 hy.le))]
  simp

theorem cinDatum_levyMeasure_slab {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) :
    ENNReal.ofReal (b / τ) * ENNReal.ofReal (τ * ε) ≤
      (cinDatum hτ hb).levyMeasure {y | τ * (1 - ε) < ‖y‖ ∧ ‖y‖ < τ} := by
  have hset : {y : Rd 1 | τ * (1 - ε) < ‖y‖ ∧ ‖y‖ < τ}
      = (fun y : Rd 1 => ‖y‖) ⁻¹' Ioo (τ * (1 - ε)) τ := rfl
  have hlo : 0 ≤ τ * (1 - ε) := mul_nonneg hτ.le (by linarith)
  rw [hset, ← Measure.map_apply continuous_norm.measurable measurableSet_Ioo,
    (cinDatum hτ hb).map_norm_levyMeasure le_rfl, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (τ * (1 - ε)) τ ∩ Ioi (0 : ℝ) = Ioo (τ * (1 - ε)) τ from
      inter_eq_left.2 fun r hr => lt_of_le_of_lt hlo hr.1]
  calc ENNReal.ofReal (b / τ) * ENNReal.ofReal (τ * ε)
      = ∫⁻ _ in Ioo (τ * (1 - ε)) τ, ENNReal.ofReal (b / τ) := by
        rw [setLIntegral_const, Real.volume_Ioo]; congr 2; ring
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt hlo hr.1
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [cinDatum, ScaleSpace.cinProfile]
  rw [indicator_of_mem (show r ∈ Ioo (0 : ℝ) τ from ⟨hr0, hr.2⟩), Pi.one_apply, mul_one]
  exact div_le_div_of_nonneg_left hb.le hr0 hr.2.le

/-! ## The real form of a datum's exponent -/

/-- `F_d(z) = ½a|z|² + ∫ (1 - cos⟨z,x⟩) ν_d(dx)`, with a Bochner integral. -/
theorem OriginDatum.exponent_eq_levy (hd : 1 ≤ d) (D : OriginDatum d) (z : Rd d) :
    D.exponent z = D.a * ‖z‖ ^ 2 / 2 + ∫ x, (1 - Real.cos ⟪z, x⟫) ∂D.levyMeasure := by
  have h1 := D.lkExponent_triplet hd z
  rw [(D.triplet hd).lkExponent_of_symm (a := D.a) rfl rfl
    (D.levyMeasure_map_isometry (LinearIsometryEquiv.neg ℝ)) z] at h1
  exact (Complex.ofReal_injective (neg_injective h1)).symm

/-! ## Rotations, the support, and the edge -/

/-- The mass of a slab `{τ < |⟨u, x⟩|}` does not depend on the direction of `u`. -/
theorem OriginDatum.levyMeasure_slab_rotate (D : OriginDatum d) {u v : Rd d} (huv : ‖u‖ = ‖v‖)
    (τ : ℝ) : D.levyMeasure {x | τ < |⟪u, x⟫|} = D.levyMeasure {x | τ < |⟪v, x⟫|} := by
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (u - v))ᗮ with hQdef
  have hQ : Q u = v := Submodule.reflection_sub huv
  have hpre : Q ⁻¹' {x | τ < |⟪v, x⟫|} = {x | τ < |⟪u, x⟫|} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq]
    rw [← hQ, LinearIsometryEquiv.inner_map_map]
  rw [← hpre, ← Measure.map_apply Q.continuous.measurable
    (measurableSet_lt measurable_const (by fun_prop)), D.levyMeasure_map_isometry]

/-- **The support** (`thm:no-cin-ray-in-the-plane`, "the shadow determines the support"): if the
slab `{τ < |⟨e, x⟩|}` is `ν_d`-null for one unit `e`, then `k_d = 0` on `(τ, ∞)`. By rotation
every such slab is null; a dense sequence of directions covers `{|x| > τ}` by them; and the radial
image of `ν_d` is `k_d(r) dr/r`. -/
theorem OriginDatum.k_eq_zero_of_slab (hd : 1 ≤ d) (D : OriginDatum d) {e : Rd d} (he : ‖e‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (h : D.levyMeasure {x | τ < |⟪e, x⟫|} = 0) :
    ∀ r : ℝ, τ < r → D.k r = 0 := by
  haveI : Nonempty (sphere (0 : Rd d) 1) := ⟨⟨e, by simp [he]⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (sphere (0 : Rd d) 1)
  have hnull : D.levyMeasure {x | τ < ‖x‖} = 0 := by
    refine measure_mono_null (t := ⋃ n, {x | τ < |⟪(u n : Rd d), x⟫|}) ?_
      (measure_iUnion_null fun n => ?_)
    · intro x (hx : τ < ‖x‖)
      have hx0 : 0 < ‖x‖ := lt_trans hτ hx
      let v : sphere (0 : Rd d) 1 := ⟨‖x‖⁻¹ • x, by
        simp [norm_smul, hx0.ne']⟩
      set ε := (‖x‖ - τ) / ‖x‖ with hε_def
      have hε : 0 < ε := div_pos (by linarith) hx0
      obtain ⟨n, hn⟩ := hu.exists_dist_lt v hε
      refine mem_iUnion.2 ⟨n, ?_⟩
      show τ < |⟪(u n : Rd d), x⟫|
      have hvx : ⟪(v : Rd d), x⟫ = ‖x‖ := by
        show ⟪‖x‖⁻¹ • x, x⟫ = ‖x‖
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      have hdist : ‖(u n : Rd d) - v‖ < ε := by
        rw [← dist_eq_norm, dist_comm]; exact hn
      have h1 : ⟪(u n : Rd d), x⟫ = ⟪(v : Rd d), x⟫ + ⟪(u n : Rd d) - v, x⟫ := by
        rw [inner_sub_left]; ring
      have h2 : -(‖(u n : Rd d) - v‖ * ‖x‖) ≤ ⟪(u n : Rd d) - v, x⟫ := by
        have := abs_real_inner_le_norm ((u n : Rd d) - v) x
        linarith [neg_abs_le ⟪(u n : Rd d) - v, x⟫]
      have h3 : ‖(u n : Rd d) - v‖ * ‖x‖ < ε * ‖x‖ := mul_lt_mul_of_pos_right hdist hx0
      have h4 : ε * ‖x‖ = ‖x‖ - τ := by rw [hε_def]; field_simp
      calc τ < ⟪(u n : Rd d), x⟫ := by linarith
        _ ≤ |⟪(u n : Rd d), x⟫| := le_abs_self _
    · rw [D.levyMeasure_slab_rotate (u := (u n : Rd d)) (v := e)
        (by rw [norm_eq_of_mem_sphere (u n), he]) τ]
      exact h
  have hrad : ∫⁻ r in Ioi τ, ENNReal.ofReal (D.k r / r) = 0 := by
    have h1 := hnull
    rw [show {x : Rd d | τ < ‖x‖} = (fun x => ‖x‖) ⁻¹' Ioi τ from rfl,
      ← Measure.map_apply continuous_norm.measurable measurableSet_Ioi, D.map_norm_levyMeasure hd,
      withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      show Ioi τ ∩ Ioi (0 : ℝ) = Ioi τ from inter_eq_left.2 (Ioi_subset_Ioi hτ.le)] at h1
    exact h1
  have hm : AEMeasurable (fun r => ENNReal.ofReal (D.k r / r)) (volume.restrict (Ioi τ)) := by
    have hm0 : AEMeasurable (fun r => ENNReal.ofReal (D.k r / r)) (volume.restrict (Ioi 0)) :=
      (((measurable_indicator_Ioi_of_antitoneOn D.k_antitone).div measurable_id).ennreal_ofReal
        |>.aemeasurable).congr ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr => by
          simp only [indicator_of_mem hr, id]))
    exact hm0.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hτ.le) le_rfl)
  have hae := (lintegral_eq_zero_iff' hm).1 hrad
  intro r hr
  haveI : (ae (volume.restrict (Ioo τ r))).NeBot :=
    ae_restrict_neBot.2 (by simp [Real.volume_Ioo, hr])
  obtain ⟨s, hs1, hs2⟩ := ((ae_restrict_of_ae_restrict_of_subset (show Ioo τ r ⊆ Ioi τ from Ioo_subset_Ioi_self) hae).and
    (ae_restrict_mem measurableSet_Ioo)).exists
  have hs0 : 0 < s := lt_trans hτ hs2.1
  have hks : D.k s ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < D.k s / s := div_pos hpos hs0
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hs1
    linarith
  exact le_antisymm ((D.k_antitone hs0 (lt_trans hs0 hs2.2) hs2.2.le).trans hks)
    (D.k_nonneg r (lt_trans hτ hr))

/-- **The edge** (`thm:no-cin-ray-in-the-plane`): when `k_d = 0` on `(τ,∞)`, the slab
`{τ(1-ε) < |⟨e,x⟩| < τ}` has `ν_d`-mass at most
`|S^{d-1}|⁻¹ σ{η : |⟨e,η⟩| > 1-ε} · (2k_d(τ/2)/τ) · τε`: a point `rη` of the slab with `k_d(r) ≠ 0`
has `r ∈ (τ(1-ε), τ]` and `η` in the cap. -/
theorem OriginDatum.levyMeasure_slab_le (hd : 1 ≤ d) (D : OriginDatum d) {e : Rd d}
    (he : ‖e‖ = 1) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsupp : ∀ r : ℝ, τ < r → D.k r = 0) :
    D.levyMeasure {x | τ * (1 - ε) < |⟪e, x⟫| ∧ |⟪e, x⟫| < τ} ≤
      (ENNReal.ofReal (sphereArea d))⁻¹ *
        ((volume : Measure (Rd d)).toSphere {η : sphere (0 : Rd d) 1 | 1 - ε < |⟪e, (η : Rd d)⟫|} *
          (ENNReal.ofReal (2 * D.k (τ / 2) / τ) * ENNReal.ofReal (τ * ε))) := by
  set S : Set (Rd d) := {x | τ * (1 - ε) < |⟪e, x⟫| ∧ |⟪e, x⟫| < τ} with hSdef
  have hS : MeasurableSet S := by
    rw [hSdef, setOf_and]
    exact (measurableSet_lt measurable_const (by fun_prop : Measurable fun x : Rd d => |⟪e, x⟫|)).inter
      (measurableSet_lt (by fun_prop : Measurable fun x : Rd d => |⟪e, x⟫|) measurable_const)
  set cap : Set (sphere (0 : Rd d) 1) := {η | 1 - ε < |⟪e, (η : Rd d)⟫|} with hcapdef
  have hcap : MeasurableSet cap := measurableSet_lt measurable_const (by fun_prop)
  set M := 2 * D.k (τ / 2) / τ with hMdef
  have hk2 : 0 ≤ D.k (τ / 2) := D.k_nonneg _ (show (0 : ℝ) < τ / 2 by positivity)
  have hM : 0 ≤ M := by positivity
  set I : Set ℝ := Ioc (τ * (1 - ε)) τ with hIdef
  -- the pointwise bound
  have hpt : ∀ η : sphere (0 : Rd d) 1, ∀ r : ℝ, 0 < r →
      S.indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)
        ≤ cap.indicator 1 η * I.indicator (fun _ => ENNReal.ofReal M) r := by
    intro η r hr
    by_cases hSη : r • (η : Rd d) ∈ S
    · obtain ⟨h1, h2⟩ := hSη
      rw [real_inner_smul_right, abs_mul, abs_of_pos hr] at h1 h2
      have hη1 : |⟪e, (η : Rd d)⟫| ≤ 1 := by
        have := abs_real_inner_le_norm e (η : Rd d)
        rwa [he, norm_eq_of_mem_sphere η, one_mul] at this
      by_cases hrτ : τ < r
      · rw [hsupp r hrτ, zero_div, ENNReal.ofReal_zero, mul_zero]; exact zero_le
      · push Not at hrτ
        have hrlo : τ * (1 - ε) < r := by nlinarith
        have hηcap : η ∈ cap := by
          show 1 - ε < |⟪e, (η : Rd d)⟫|
          by_contra hle
          push Not at hle
          have : r * |⟪e, (η : Rd d)⟫| ≤ τ * (1 - ε) := by
            calc r * |⟪e, (η : Rd d)⟫| ≤ τ * |⟪e, (η : Rd d)⟫| :=
                  mul_le_mul_of_nonneg_right hrτ (abs_nonneg _)
              _ ≤ τ * (1 - ε) := mul_le_mul_of_nonneg_left hle hτ.le
          linarith
        rw [indicator_of_mem (show r • (η : Rd d) ∈ S from ⟨by
            rw [real_inner_smul_right, abs_mul, abs_of_pos hr]; exact h1, by
            rw [real_inner_smul_right, abs_mul, abs_of_pos hr]; exact h2⟩),
          indicator_of_mem hηcap, indicator_of_mem (show r ∈ I from ⟨hrlo, hrτ⟩),
          Pi.one_apply, Pi.one_apply, one_mul, one_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        have hr2 : τ / 2 ≤ r := by nlinarith
        have hkr : D.k r ≤ D.k (τ / 2) :=
          D.k_antitone (show (0 : ℝ) < τ / 2 by positivity) hr hr2
        rw [hMdef, div_le_div_iff₀ hr hτ]
        nlinarith [D.k_nonneg r hr]
    · rw [indicator_of_notMem hSη, zero_mul]; exact zero_le
  rw [← lintegral_indicator_one hS, D.polar_decomposition_any hd _ (measurable_one.indicator hS)]
  refine mul_le_mul_right ?_ _
  calc ∫⁻ η : sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
        S.indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r))
          ∂((volume : Measure (Rd d)).toSphere)
      ≤ ∫⁻ η : sphere (0 : Rd d) 1, cap.indicator
          (fun _ => ENNReal.ofReal M * ENNReal.ofReal (τ * ε)) η
          ∂((volume : Measure (Rd d)).toSphere) := lintegral_mono fun η => ?_
    _ = _ := by rw [lintegral_indicator_const hcap, mul_comm]
  calc ∫⁻ r in Ioi (0 : ℝ), S.indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)
      ≤ ∫⁻ r in Ioi (0 : ℝ), cap.indicator 1 η * I.indicator (fun _ => ENNReal.ofReal M) r :=
        setLIntegral_mono' measurableSet_Ioi fun r hr => hpt η r hr
    _ ≤ ∫⁻ r, cap.indicator 1 η * I.indicator (fun _ => ENNReal.ofReal M) r :=
        setLIntegral_le_lintegral _ _
    _ = cap.indicator 1 η * (ENNReal.ofReal M * ENNReal.ofReal (τ * ε)) := by
        rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Ioc),
          lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
        congr 3
        ring
    _ = cap.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal (τ * ε)) η := by
        by_cases hη : η ∈ cap
        · rw [indicator_of_mem hη, indicator_of_mem hη, Pi.one_apply, one_mul]
        · rw [indicator_of_notMem hη, indicator_of_notMem hη, zero_mul]

/-- In dimension `d ≥ 2` the two poles `{|⟨e₁,η⟩| ≥ 1}` of the sphere are `σ`-null. -/
theorem toSphere_pole_null (hd : 2 ≤ d) [NeZero d] :
    (volume : Measure (Rd d)).toSphere
      {η : sphere (0 : Rd d) 1 | 1 ≤ |⟪ebasis (0 : Fin d), (η : Rd d)⟫|} = 0 := by
  set j : Fin d := ⟨1, by omega⟩
  have hj : (0 : Fin d) ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have he₂ : ebasis j ≠ 0 := by
    intro h
    have := congrArg (fun x : Rd d => x j) h
    simp [ebasis] at this
  refine measure_mono_null (fun η hη => ?_) (toSphere_inner_eq_zero he₂)
  simp only [mem_setOf_eq] at hη ⊢
  have hi0 : ⟪ebasis (0 : Fin d), (η : Rd d)⟫ = (η : Rd d) 0 := by
    simp [ebasis, EuclideanSpace.inner_single_left]
  have hij : ⟪ebasis j, (η : Rd d)⟫ = (η : Rd d) j := by
    simp [ebasis, EuclideanSpace.inner_single_left]
  rw [hi0] at hη
  rw [hij]
  have hsum : (η : Rd d) 0 ^ 2 + (η : Rd d) j ^ 2 ≤ ‖(η : Rd d)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc (η : Rd d) 0 ^ 2 + (η : Rd d) j ^ 2 = ∑ i ∈ {0, j}, ‖(η : Rd d) i‖ ^ 2 := by
          rw [Finset.sum_pair hj]; simp [Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ i, ‖(η : Rd d) i‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
  rw [norm_eq_of_mem_sphere η, one_pow] at hsum
  have h1 : 1 ≤ (η : Rd d) 0 ^ 2 := by
    have := mul_le_mul hη hη zero_le_one (abs_nonneg _)
    rw [one_mul, ← sq, sq_abs] at this
    exact this
  have h2 : (η : Rd d) j ^ 2 ≤ 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h2 (sq_nonneg _))

/-- The caps `{|⟨e₁,η⟩| > 1 - 1/(n+2)}` shrink to the null poles. -/
theorem tendsto_toSphere_cap (hd : 2 ≤ d) [NeZero d] :
    Tendsto (fun n : ℕ => (volume : Measure (Rd d)).toSphere
      {η : sphere (0 : Rd d) 1 | 1 - 1 / ((n : ℝ) + 2) < |⟪ebasis (0 : Fin d), (η : Rd d)⟫|})
      atTop (𝓝 0) := by
  set s : ℕ → Set (sphere (0 : Rd d) 1) :=
    fun n => {η | 1 - 1 / ((n : ℝ) + 2) < |⟪ebasis (0 : Fin d), (η : Rd d)⟫|} with hs
  have hanti : Antitone s := by
    intro m n hmn η hη
    simp only [hs, mem_setOf_eq] at hη ⊢
    refine lt_of_le_of_lt ?_ hη
    have : ((m : ℝ) + 2) ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) this
    linarith
  have hinter : (⋂ n, s n) ⊆ {η : sphere (0 : Rd d) 1 | 1 ≤ |⟪ebasis (0 : Fin d), (η : Rd d)⟫|} := by
    intro η hη
    simp only [mem_iInter, hs, mem_setOf_eq] at hη
    show 1 ≤ |⟪ebasis (0 : Fin d), (η : Rd d)⟫|
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    have h1 := hη n
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have h := tendsto_measure_iInter_atTop (μ := (volume : Measure (Rd d)).toSphere)
    (s := s) (fun n => (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rwa [measure_mono_null hinter (toSphere_pole_null hd)] at h

/-! ## The shadow on a line -/

theorem norm_toLine [NeZero d] (x : Rd d) : ‖toLine d x‖ = |⟪ebasis (0 : Fin d), x⟫| := by
  rw [toLine, norm_smul, Real.norm_eq_abs]
  simp [ebasis]

theorem inner_toLine [NeZero d] (ω : Rd 1) (x : Rd d) :
    ⟪ω, toLine d x⟫ = ⟪⟪ebasis (0 : Fin 1), ω⟫ • ebasis (0 : Fin d), x⟫ := by
  rw [toLine, real_inner_smul_right, real_inner_smul_left, real_inner_comm ω]
  ring

theorem toLine_neg [NeZero d] (x : Rd d) : toLine d (-x) = -toLine d x := by
  simp [toLine, inner_neg_right, neg_smul]

/-- **`thm:no-cin-ray-in-the-plane`**, the law form: for every integer `d ≥ 2`,
`ξ ↦ b Cin(τ|ξ|)` is not the exponent of a self-decomposable law on `ℝ^d`. -/
theorem no_cin_ray_law (hd : 2 ≤ d) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ¬ ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
        ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-(b * ScaleSpace.cin (τ * ‖ξ‖))) : ℝ) : ℂ) := by
  rintro ⟨μ, hprob, hsd, hchar⟩
  have hd1 : 1 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  set F : ℝ → ℝ := fun r => b * ScaleSpace.cin (τ * r) with hF
  have hF0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := fun r _ =>
    mul_nonneg hb.le (ScaleSpace.cin_nonneg' _)
  obtain ⟨O, hO⟩ := (polar_reading hd1 F hF0).1 ⟨μ, hprob, hsd, hchar⟩
  have hA := (sphereArea_eq_toSphere hd1).2
  have he₁ : ‖ebasis (0 : Fin d)‖ = 1 := by simp [ebasis]
  set O₁ := cinDatum hτ hb with hO₁
  -- the shadow `ν̄` of `ν_d` on the first axis, as a triplet on the line
  set νbar : Measure (Rd 1) := (O.levyMeasure.map (toLine d)).restrict {0}ᶜ with hνbar
  have hmeas0 : MeasurableSet ({0}ᶜ : Set (Rd 1)) := (measurableSet_singleton 0).compl
  have hν0 : νbar {0} = 0 := by
    rw [hνbar, Measure.restrict_apply (measurableSet_singleton 0)]
    simp
  have hνint : ∫⁻ y, ENNReal.ofReal (min (‖y‖ ^ 2) 1) ∂νbar ≠ ⊤ := by
    refine ne_top_of_le_ne_top (O.lintegral_min_levyMeasure_ne_top hd1) ?_
    calc ∫⁻ y, ENNReal.ofReal (min (‖y‖ ^ 2) 1) ∂νbar
        ≤ ∫⁻ y, ENNReal.ofReal (min (‖y‖ ^ 2) 1) ∂(O.levyMeasure.map (toLine d)) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ x, ENNReal.ofReal (min (‖toLine d x‖ ^ 2) 1) ∂O.levyMeasure :=
          lintegral_map (by fun_prop) continuous_toLine.measurable
      _ ≤ _ := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_min_right _
          (pow_le_pow_left₀ (norm_nonneg _) (by
            rw [norm_toLine]
            have := abs_real_inner_le_norm (ebasis (0 : Fin d)) x
            rwa [he₁, one_mul] at this) 2))
  let T : LevyTriplet 1 := {
    A := O.a • (1 : Mat 1)
    ν := νbar
    γ := 0
    A_posSemidef := Matrix.PosSemidef.one.smul O.a_nonneg
    ν_zero := hν0
    ν_integrable := hνint }
  have hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd 1)) = T.ν := by
    show νbar.map (LinearIsometryEquiv.neg ℝ (E := Rd 1)) = νbar
    have hnegm := (LinearIsometryEquiv.neg ℝ (E := Rd 1)).continuous.measurable
    ext B hB
    rw [Measure.map_apply hnegm hB, hνbar, Measure.restrict_apply (hnegm hB),
      Measure.restrict_apply hB,
      Measure.map_apply continuous_toLine.measurable ((hnegm hB).inter hmeas0),
      Measure.map_apply continuous_toLine.measurable (hB.inter hmeas0)]
    conv_rhs => rw [← O.levyMeasure_map_isometry (LinearIsometryEquiv.neg ℝ)]
    rw [Measure.map_apply (LinearIsometryEquiv.neg ℝ (E := Rd d)).continuous.measurable
      (continuous_toLine.measurable (hB.inter hmeas0))]
    congr 1
    ext x
    simp [toLine_neg]
  have hTexp : ∀ ω : Rd 1, T.lkExponent ω = -((O₁.exponent ω : ℝ) : ℂ) := by
    intro ω
    rw [T.lkExponent_of_symm (a := O.a) rfl rfl hsym ω]
    congr 2
    set c := ⟪ebasis (0 : Fin 1), ω⟫ with hc
    have hnorm : ‖c • ebasis (0 : Fin d)‖ = ‖ω‖ := by
      rw [norm_smul, he₁, mul_one, Real.norm_eq_abs, hc, ← norm_eq_abs_inner_ebasis_one]
    have hint : ∫ y, (1 - Real.cos ⟪ω, y⟫) ∂νbar
        = ∫ x, (1 - Real.cos ⟪c • ebasis (0 : Fin d), x⟫) ∂O.levyMeasure := by
      rw [hνbar, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        simp only [mem_compl_iff, mem_singleton_iff, not_not] at hy
        subst hy
        simp)]
      rw [integral_map continuous_toLine.measurable.aemeasurable (by fun_prop)]
      simp_rw [inner_toLine]
      rfl
    show O.a * ‖ω‖ ^ 2 / 2 + ∫ y, (1 - Real.cos ⟪ω, y⟫) ∂νbar = O₁.exponent ω
    rw [hint, ← hnorm, ← O.exponent_eq_levy hd1, ← hO, hnorm, hO₁, cinDatum_exponent]
  -- A3: the shadow is the ray's Lévy measure
  obtain ⟨μb, hprobb, hIDb, hTb⟩ := levy_khintchine_converse T
  obtain ⟨μ₁, hprob₁, -, hT₁, hchar₁⟩ := polar_reading_converse le_rfl O₁
  haveI := hprobb; haveI := hprob₁
  have hμ : μb = μ₁ := by
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hTb ω, hTexp ω, hchar₁ ω, Complex.ofReal_exp, Complex.ofReal_neg]
  have hT₁' : HasTriplet μb (O₁.triplet le_rfl) := by rw [hμ]; exact hT₁
  obtain ⟨-, hνeq, -⟩ := levy_khintchine_unique μb hIDb T (O₁.triplet le_rfl) hTb hT₁'
  have hνO₁ : νbar = O₁.levyMeasure := hνeq
  -- the support
  have hshadow : ∀ B : Set (Rd 1), MeasurableSet B →
      νbar B ≤ O.levyMeasure (toLine d ⁻¹' B) := by
    intro B hB
    rw [hνbar, Measure.restrict_apply hB, ← Measure.map_apply continuous_toLine.measurable hB]
    exact measure_mono inter_subset_left
  have hsupp : ∀ r : ℝ, τ < r → O.k r = 0 := by
    refine O.k_eq_zero_of_slab hd1 he₁ hτ ?_
    have hBm : MeasurableSet {y : Rd 1 | τ < ‖y‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    have h1 : νbar {y | τ < ‖y‖} = 0 := by rw [hνO₁, hO₁]; exact cinDatum_levyMeasure_gt hτ hb
    rw [hνbar, Measure.restrict_apply hBm,
      Measure.map_apply continuous_toLine.measurable (hBm.inter hmeas0)] at h1
    refine measure_mono_null (fun x (hx : τ < |⟪ebasis (0 : Fin d), x⟫|) => ?_) h1
    refine ⟨show τ < ‖toLine d x‖ by rw [norm_toLine]; exact hx, ?_⟩
    show toLine d x ≠ 0
    intro h0
    have := norm_toLine x
    rw [h0, norm_zero] at this
    linarith
  -- the edge
  set C : ℝ≥0∞ := (ENNReal.ofReal (sphereArea d))⁻¹ * ENNReal.ofReal (2 * O.k (τ / 2) / τ)
    with hC
  have hbound : ∀ n : ℕ, ENNReal.ofReal (b / τ) ≤ C * (volume : Measure (Rd d)).toSphere
      {η : sphere (0 : Rd d) 1 | 1 - 1 / ((n : ℝ) + 2) < |⟪ebasis (0 : Fin d), (η : Rd d)⟫|} := by
    intro n
    set ε : ℝ := 1 / ((n : ℝ) + 2) with hε
    have hε0 : 0 < ε := by positivity
    have hε2 : ε ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    have hBm : MeasurableSet {y : Rd 1 | τ * (1 - ε) < ‖y‖ ∧ ‖y‖ < τ} :=
      (measurableSet_lt measurable_const continuous_norm.measurable).inter
        (measurableSet_lt continuous_norm.measurable measurable_const)
    have hlow := cinDatum_levyMeasure_slab hτ hb hε0 hε2
    rw [← hO₁, ← hνO₁] at hlow
    have hpre : toLine d ⁻¹' {y : Rd 1 | τ * (1 - ε) < ‖y‖ ∧ ‖y‖ < τ}
        = {x | τ * (1 - ε) < |⟪ebasis (0 : Fin d), x⟫| ∧ |⟪ebasis (0 : Fin d), x⟫| < τ} := by
      ext x; simp only [mem_preimage, mem_setOf_eq, norm_toLine]
    have hup := (hshadow _ hBm).trans (le_of_eq (congrArg O.levyMeasure hpre))
    have hedge := O.levyMeasure_slab_le hd1 he₁ hτ hε0 hε2 hsupp
    have hX0 : ENNReal.ofReal (τ * ε) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hall := hlow.trans (hup.trans hedge)
    have hall' : ENNReal.ofReal (b / τ) * ENNReal.ofReal (τ * ε)
        ≤ (C * (volume : Measure (Rd d)).toSphere
          {η : sphere (0 : Rd d) 1 | 1 - ε < |⟪ebasis (0 : Fin d), (η : Rd d)⟫|}) *
          ENNReal.ofReal (τ * ε) := by
      refine hall.trans (le_of_eq ?_)
      rw [hC]
      ring
    exact (ENNReal.mul_le_mul_iff_left hX0 ENNReal.ofReal_ne_top).1 hall'
  have hlim : Tendsto (fun n : ℕ => C * (volume : Measure (Rd d)).toSphere
      {η : sphere (0 : Rd d) 1 | 1 - 1 / ((n : ℝ) + 2) < |⟪ebasis (0 : Fin d), (η : Rd d)⟫|})
      atTop (𝓝 0) := by
    have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by simp [hA]))
      ENNReal.ofReal_ne_top
    simpa using ENNReal.Tendsto.const_mul (tendsto_toSphere_cap hd) (Or.inr hCtop)
  have h0 := ge_of_tendsto' hlim hbound
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h0
  have : 0 < b / τ := div_pos hb hτ
  linarith

/-- **`thm:no-cin-ray-in-the-plane`**: for every integer `d ≥ 2`, `ξ ↦ b Cin(τ|ξ|)` is not the
exponent of a self-decomposable law on `ℝ^d`; that is, `F ∉ 𝒜_d`. -/
theorem no_cin_ray_in_the_plane (hd : 2 ≤ d) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (¬ ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
        ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-(b * ScaleSpace.cin (τ * ‖ξ‖))) : ℝ) : ℂ)) ∧
      ¬ classA d (fun ω => b * ScaleSpace.cin (τ * |ω|)) := by
  have hmain := no_cin_ray_law hd hτ hb
  refine ⟨hmain, fun h => hmain ?_⟩
  obtain ⟨-, μ, hprob, hsd, hchar⟩ := h
  exact ⟨μ, hprob, hsd, fun ξ => by rw [hchar ξ]; simp only [abs_norm]⟩

end AffineHemigroup
