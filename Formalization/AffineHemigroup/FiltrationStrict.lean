/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarClassification
import AffineHemigroup.DelayPolar
import AffineHemigroup.ThresholdCriterion
import AffineHemigroup.Thresholds
import AffineHemigroup.WitnessDatum
import AffineHemigroup.OriginBoundedness

/-!
# `thm:filtration-strict`: the dimension filtration is strict at every step

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `thm:filtration-strict`, clauses (1)–(3). Wave 2,
group A (Q-0281). The node's fourth declaration, `filtration_top` (`lem:filtration-top`,
`𝒜_∞ = 𝒮`), is proved in `AffineHemigroup.FiltrationTop` (wave N), on Schoenberg's radial theorem,
ledger A10.

Clause (1). Membership: for `0 < w ≤ w_d` the polar profile `k^{(w)}_d` is nonincreasing
(`lem:threshold-criterion`), so `lem:delay-polar-profile` gives an origin datum `(0, k^{(w)}_d)`
with exponent `F^{(w)}(|·|)`, and `prop:isotropic-polar-classification`(2) puts `F^{(w)}` in `𝒜_d`.
Exclusion: if `F^{(w)} ∈ 𝒜_{d+1}`, the polar reading gives a datum `(a, k_{d+1})`; the
non-monotone `k^{(w)}_{d+1}` defines a symmetric Lévy measure `ν'` (`lem:delay-polar-profile`
supplies its integrability and its exponent), whose law (A3(iii)) has the same transform as the
datum's, so A3(ii) identifies `ν'` with the datum's Lévy measure; the densities, hence the
profiles, agree almost everywhere (polar coordinates), and a continuous profile equal a.e. to a
nonincreasing one is nonincreasing, which `lem:threshold-criterion` excludes for `w > w_{d+1}`.
Clause (2): `M_2 > h_2(1/2) > 1/15` and `Γ(3/2) < 1`, so `w_2 < 15/2 < 6 + 4√2`. Clause (3): the
nesting `𝒜_{d+1} ⊆ 𝒜_d` by the projection on the first `d` coordinates, and clause (1).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The nesting `𝒜_{d+1} ⊆ 𝒜_d` -/

/-- The first `d` coordinates of a point of `ℝ^{d+1}`. -/
noncomputable def dropLast (d : ℕ) (x : Rd (d + 1)) : Rd d :=
  WithLp.toLp 2 fun i : Fin d => x (Fin.castSucc i)

/-- `ℝ^d` inside `ℝ^{d+1}`, with last coordinate `0`. -/
noncomputable def padZero (d : ℕ) (ξ : Rd d) : Rd (d + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i : Fin d => ξ i) 0)

theorem inner_dropLast (ξ : Rd d) (x : Rd (d + 1)) : ⟪ξ, dropLast d x⟫ = ⟪padZero d ξ, x⟫ := by
  simp only [dropLast, padZero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]

theorem norm_padZero (ξ : Rd d) : ‖padZero d ξ‖ = ‖ξ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [padZero, Fin.sum_univ_castSucc]

theorem padZero_smul (c : ℝ) (ξ : Rd d) : padZero d (c • ξ) = c • padZero d ξ := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [padZero]
  · simp [padZero]

theorem continuous_dropLast : Continuous (dropLast d) := by
  unfold dropLast
  fun_prop

/-- `\widehat{P_*μ}(ξ) = μ̂(ξ, 0)`. -/
theorem charFun_map_dropLast (μ : Measure (Rd (d + 1))) (ξ : Rd d) :
    charFun (μ.map (dropLast d)) ξ = charFun μ (padZero d ξ) := by
  rw [charFun_apply, charFun_apply, integral_map continuous_dropLast.measurable.aemeasurable
    (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [real_inner_comm, inner_dropLast, real_inner_comm]

/-- **The nesting** `𝒜_{d+1} ⊆ 𝒜_d` ([B, Prop. 4.9(1)], restated): the image of the law under the
projection on the first `d` coordinates is self-decomposable with transform `e^{-F(|ξ|)}`. -/
theorem classA_of_succ {F : ℝ → ℝ} (h : classA (d + 1) F) : classA d F := by
  obtain ⟨hP, μ, hprob, hsd, hchar⟩ := h
  haveI := hprob
  refine ⟨hP, μ.map (dropLast d),
    Measure.isProbabilityMeasure_map continuous_dropLast.measurable.aemeasurable, ?_, fun ξ => ?_⟩
  · rw [ScaleSpace.isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    obtain ⟨ρ, hρ, hfac⟩ := (ScaleSpace.isSelfDecomposable_iff_charFun μ).1 hsd c hc0 hc1
    haveI := hρ
    refine ⟨ρ.map (dropLast d),
      Measure.isProbabilityMeasure_map continuous_dropLast.measurable.aemeasurable, fun ξ => ?_⟩
    rw [charFun_map_dropLast, charFun_map_dropLast, charFun_map_dropLast, hfac, padZero_smul]
  · rw [charFun_map_dropLast, hchar, norm_padZero]

/-! ## A continuous function equal a.e. to a nonincreasing one is nonincreasing -/

theorem exists_ae_eq_mem_Ioo {f g : ℝ → ℝ}
    (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), f r = g r) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ u ∈ Ioo a b, f u = g u := by
  have h1 : ∀ᵐ u ∂(volume.restrict (Ioo a b)), f u = g u :=
    ae_restrict_of_ae_restrict_of_subset (fun u hu => lt_of_le_of_lt ha hu.1) h
  haveI : (ae (volume.restrict (Ioo a b))).NeBot :=
    ae_restrict_neBot.2 (by simp [Real.volume_Ioo, hab])
  obtain ⟨u, hu1, hu2⟩ := (h1.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact ⟨u, hu2, hu1⟩

theorem antitoneOn_of_ae_eq {f g : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hg : AntitoneOn g (Ioi 0)) (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), f r = g r) :
    AntitoneOn f (Ioi 0) := by
  intro r (hr : 0 < r) s (hs : 0 < s) hrs
  rcases hrs.lt_or_eq with hlt | heq
  swap
  · rw [heq]
  by_contra hcon
  push Not at hcon
  set m := (f r + f s) / 2 with hm
  have h1 : ∀ᶠ u in 𝓝 r, f u < m :=
    (hf.continuousAt (Ioi_mem_nhds hr)).eventually_lt_const (by linarith)
  have h2 : ∀ᶠ u in 𝓝 s, m < f u :=
    (hf.continuousAt (Ioi_mem_nhds hs)).eventually_const_lt (by linarith)
  obtain ⟨ε₁, hε₁, hb1⟩ := Metric.eventually_nhds_iff.1 h1
  obtain ⟨ε₂, hε₂, hb2⟩ := Metric.eventually_nhds_iff.1 h2
  set δ := min (min ε₁ ε₂) ((s - r) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hε₁ hε₂) (by linarith)
  have hδ1 : δ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ (s - r) / 2 := min_le_right _ _
  obtain ⟨u, hu, hfu⟩ := exists_ae_eq_mem_Ioo h hr.le (by linarith : r < r + δ)
  obtain ⟨v, hv, hfv⟩ := exists_ae_eq_mem_Ioo h (by linarith : 0 ≤ s - δ) (by linarith : s - δ < s)
  have hu' : f u < m := hb1 (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
  have hv' : m < f v := hb2 (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2])
  have huv : u ≤ v := by linarith [hu.2, hv.1]
  have := hg (show (0 : ℝ) < u by linarith [hu.1]) (show (0 : ℝ) < v by linarith [hv.1]) huv
  linarith

/-! ## The witness profile -/

theorem polarProfileOf_congr {k k' : ℝ → ℝ} (h : ∀ u ∈ Ioi (0 : ℝ), k u = k' u) {r : ℝ}
    (hr : 0 < r) : polarProfileOf k d r = polarProfileOf k' d r := by
  unfold polarProfileOf
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  rw [h _ (show (0 : ℝ) < r ^ 2 / (2 * v) by positivity)]

theorem witnessF_nonneg (w r : ℝ) : 0 ≤ witnessF w r := ENNReal.toReal_nonneg

/-- **`thm:filtration-strict`(1), membership**: for `0 < w ≤ w_d`, `F^{(w)} ∈ 𝒜_d`. -/
theorem witness_classA (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) (hwd : w ≤ threshold d) :
    classA d (witnessF w) := by
  obtain ⟨D, -, hDk, hDexp⟩ := witness_isDelayDatum hw
  have hanti : AntitoneOn (polarProfileOf D.k d) (Ioi 0) := by
    have h := (witness_antitone_iff d hd hw).2 hwd
    intro r hr s hs hrs
    rw [polarProfileOf_congr hDk hr, polarProfileOf_congr hDk hs]
    exact h hr hs hrs
  obtain ⟨O, -, -, hO⟩ := delay_polar_profile_datum hd D hanti
  refine (classA_iff_originDatum hd _ fun r _ => witnessF_nonneg w r).2 ⟨O, fun ξ => ?_⟩
  rw [OriginDatum.exponent, hO ξ, ← DelayDatum.exponent, hDexp]
  rfl

/-! ## The exclusion -/

/-- A radial measure `φ(|x|) dx` is invariant under linear isometries. -/
theorem withDensity_radial_map_isometry (φ : ℝ → ℝ≥0∞) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (volume.withDensity fun x : Rd d => φ ‖x‖).map Q = volume.withDensity fun x : Rd d => φ ‖x‖ := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply Q.continuous.measurable hB,
    withDensity_apply _ (Q.continuous.measurable hB), withDensity_apply _ hB,
    ← lintegral_indicator (Q.continuous.measurable hB), ← lintegral_indicator hB]
  have h := (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding
    (B.indicator fun x => φ ‖x‖)
  rw [← h]
  refine lintegral_congr fun x => ?_
  by_cases hx : Q x ∈ B
  · rw [indicator_of_mem (show x ∈ Q ⁻¹' B from hx), indicator_of_mem hx,
      LinearIsometryEquiv.norm_map]
  · rw [indicator_of_notMem (show x ∉ Q ⁻¹' B from hx), indicator_of_notMem hx]

/-- **`thm:filtration-strict`(1), exclusion**: for an integer `n ≥ 1` and `w > w_n`,
`F^{(w)} ∉ 𝒜_n`. If it were, the polar reading would give an origin datum `(a, k_n)`; the
non-monotone polar profile `k^{(w)}_n` of `lem:delay-polar-profile` defines a symmetric Lévy
measure whose law (A3(iii)) has the same transform, so by A3(ii) the two Lévy measures agree, and
`k^{(w)}_n = k_n` almost everywhere; a continuous function equal a.e. to a nonincreasing one is
nonincreasing, which `lem:threshold-criterion` excludes for `w > w_n`. -/
theorem witness_not_classA {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw : 0 < w) (hwn : threshold n < w) :
    ¬ classA n (witnessF w) := by
  classical
  intro h
  have hn0 : n ≠ 0 := by omega
  obtain ⟨O, hO⟩ := (classA_iff_originDatum hn _ fun r _ => witnessF_nonneg w r).1 h
  obtain ⟨D, hD0, hDk, hDexp⟩ := witness_isDelayDatum hw
  obtain ⟨-, -, h0, h1, hid⟩ := delay_polar_profile hn D
  have hA := (sphereArea_eq_toSphere hn).2
  -- the profile `k^{(w)}_n`, in a measurable version
  set K : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise (witnessClosedForm n w) 0 with hKdef
  have hKm : Measurable K := ContinuousOn.measurable_piecewise
    (contDiffOn_witnessClosedForm n hn w).continuousOn continuousOn_const measurableSet_Ioi
  have hKc : ContinuousOn K (Ioi 0) := (contDiffOn_witnessClosedForm n hn w).continuousOn.congr
    fun r hr => by rw [hKdef]; exact Set.piecewise_eq_of_mem _ _ _ hr
  have hKw : ∀ r : ℝ, 0 < r → polarProfileOf (witnessProfile w) n r = K r := fun r hr => by
    rw [polarProfileOf_witness_eq_closedForm n hn w hr, hKdef]
    exact (Set.piecewise_eq_of_mem (Ioi (0 : ℝ)) _ _ (show r ∈ Ioi (0 : ℝ) from hr)).symm
  have hK : ∀ r : ℝ, 0 < r → polarProfileOf D.k n r = K r := fun r hr => by
    rw [polarProfileOf_congr hDk hr, hKw r hr]
  have hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r := fun r hr => by
    rw [← hK r hr]; exact polarProfileOf_nonneg D hr
  -- its Lévy measure
  set φ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (K r / (sphereArea n * r ^ n)) with hφ
  have hφm : Measurable φ := by
    rw [hφ]
    exact (hKm.div (measurable_const.mul (measurable_id.pow_const n))).ennreal_ofReal
  have hφnm : Measurable fun x : Rd n => φ ‖x‖ := hφm.comp continuous_norm.measurable
  set ν : Measure (Rd n) := volume.withDensity fun x => φ ‖x‖ with hν
  have hν0 : ν {0} = 0 := by
    rw [hν, withDensity_apply _ (measurableSet_singleton 0)]
    refine setLIntegral_eq_zero (measurableSet_singleton 0) fun x hx => ?_
    rw [mem_singleton_iff] at hx
    subst hx
    simp [hφ, hn0]
  have hνint : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤ := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ hφnm (by fun_prop)]
    simp only [Pi.mul_apply]
    rw [lintegral_radial hn (fun r => φ r * ENNReal.ofReal (min (r ^ 2) 1)) (by fun_prop),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (sphereArea n) *
        (φ r * ENNReal.ofReal (min (r ^ 2) 1) * ENNReal.ofReal (r ^ (n - 1)))
        = ENNReal.ofReal (min (r ^ 2) 1 * K r / r) := by
      intro r (hr : 0 < r)
      have hk := hK0 r hr
      rw [hφ]
      simp only
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hA.le]
      congr 1
      have hrn : r ^ n = r ^ (n - 1) * r := by
        rw [← pow_succ]; congr 1; omega
      rw [hrn]
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
      lintegral_union measurableSet_Ici
        (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
    refine ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top h0
      (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_)),
      ne_top_of_le_ne_top h1 (le_of_eq ?_)⟩
    · have hr0 : 0 < r := hr.1
      rw [min_eq_left (by nlinarith [hr.1, hr.2]), hK r hr0]
      congr 1
      field_simp
    · rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
      refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
      rw [min_eq_right (by nlinarith), one_mul, hK r (by linarith)]
  -- the triplet `(0, ν, 0)` and its exponent
  let T : LevyTriplet n := {
    A := 0
    ν := ν
    γ := 0
    A_posSemidef := Matrix.PosSemidef.zero
    ν_zero := hν0
    ν_integrable := hνint }
  have hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd n)) = T.ν :=
    withDensity_radial_map_isometry φ _
  have hcos : ∀ z : Rd n, ∫ x, (1 - Real.cos ⟪z, x⟫) ∂ν = witnessF w ‖z‖ := by
    intro z
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => show (0 : ℝ) ≤ 1 - Real.cos ⟪z, x⟫ by
        linarith [Real.cos_le_one ⟪z, x⟫]) (by fun_prop),
      hν, lintegral_withDensity_eq_lintegral_mul _ hφnm (by fun_prop)]
    simp only [Pi.mul_apply]
    have hpt : ∀ x : Rd n, φ ‖x‖ * ENNReal.ofReal (1 - Real.cos ⟪z, x⟫)
        = ENNReal.ofReal ((1 - Real.cos ⟪z, x⟫) *
          (polarProfileOf D.k n ‖x‖ / (sphereArea n * ‖x‖ ^ n))) := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp [hφ, hn0]
      · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
        rw [hφ, hK _ hx0, mul_comm, ENNReal.ofReal_mul (by linarith [Real.cos_le_one ⟪z, x⟫])]
    simp_rw [hpt]
    have h2 := hid z
    rw [hD0, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add] at h2
    rw [← h2, ← DelayDatum.exponent, hDexp]
    rfl
  have hTexp : ∀ z : Rd n, T.lkExponent z = -((witnessF w ‖z‖ : ℝ) : ℂ) := by
    intro z
    rw [T.lkExponent_of_symm (a := 0) (by simp [T]) rfl hsym z]
    congr 2
    show 0 * ‖z‖ ^ 2 / 2 + ∫ x, (1 - Real.cos ⟪z, x⟫) ∂ν = witnessF w ‖z‖
    rw [hcos z]
    ring
  -- the two laws, and A3(ii)
  obtain ⟨μ', hprob', hID', hT'⟩ := levy_khintchine_converse T
  obtain ⟨μ, hprob, -, hTO, hcharO⟩ := polar_reading_converse hn O
  haveI := hprob; haveI := hprob'
  have hμ : μ' = μ := by
    refine Measure.ext_of_charFun (funext fun z => ?_)
    rw [hT' z, hTexp z, hcharO z, ← hO z, Complex.ofReal_exp, Complex.ofReal_neg]
  have hTO' : HasTriplet μ' (O.triplet hn) := by rw [hμ]; exact hTO
  obtain ⟨-, hνeq, -⟩ := levy_khintchine_unique μ' hID' T (O.triplet hn) hT' hTO'
  have hνO : ν = O.levyMeasure := hνeq
  -- the densities agree almost everywhere, so the profiles do
  have hae := (withDensity_eq_iff_of_sigmaFinite hφnm.aemeasurable
    O.measurable_levyDensity.aemeasurable).mp hνO
  have hOm := measurable_indicator_Ioi_of_antitoneOn O.k_antitone
  set E : Set ℝ := Ioi 0 ∩ {r | K r = (Ioi (0 : ℝ)).indicator O.k r}ᶜ with hE
  have hEm : MeasurableSet E := measurableSet_Ioi.inter (measurableSet_eq_fun hKm hOm).compl
  have hnull : volume ((fun x : Rd n => ‖x‖) ⁻¹' E) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
    obtain ⟨hx0, hxne⟩ := hx
    have hx0' : (0 : ℝ) < ‖x‖ := hx0
    have hx : x ≠ 0 := norm_pos_iff.mp hx0'
    simp only [mem_setOf_eq]
    rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd n)) from hx), hφ]
    intro heq
    apply hxne
    simp only [mem_setOf_eq]
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi (0 : ℝ) from hx0')]
    have hden : 0 < sphereArea n * ‖x‖ ^ n := by positivity
    have h3 := (ENNReal.ofReal_eq_ofReal_iff (div_nonneg (hK0 _ hx0') hden.le)
      (div_nonneg (O.k_nonneg _ hx0') hden.le)).mp heq
    exact (div_left_inj' hden.ne').mp h3
  have hrad := lintegral_radial hn (E.indicator 1) (measurable_one.indicator hEm)
  have hL : ∫⁻ x : Rd n, E.indicator 1 ‖x‖ = 0 := by
    have : (fun x : Rd n => E.indicator (1 : ℝ → ℝ≥0∞) ‖x‖)
        = ((fun x : Rd n => ‖x‖) ⁻¹' E).indicator 1 := by
      ext x
      by_cases hx : ‖x‖ ∈ E
      · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x : Rd n => ‖x‖) ⁻¹' E from hx)]
        rfl
      · rw [indicator_of_notMem hx,
          indicator_of_notMem (show x ∉ (fun x : Rd n => ‖x‖) ⁻¹' E from hx)]
    rw [this, lintegral_indicator_one (continuous_norm.measurable hEm), hnull]
  rw [hL, eq_comm, mul_eq_zero] at hrad
  have hrad' : ∫⁻ r in Ioi (0 : ℝ), E.indicator 1 r * ENNReal.ofReal (r ^ (n - 1)) = 0 := by
    rcases hrad with h | h
    · exact absurd h (by simp [hA])
    · exact h
  rw [lintegral_eq_zero_iff (by fun_prop)] at hrad'
  have hae' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), K r = O.k r := by
    filter_upwards [hrad', ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    simp only [Pi.zero_apply, mul_eq_zero] at hr
    rcases hr with h | h
    · by_contra hne
      have hmem : r ∈ E := ⟨hr0, by
        simp only [mem_compl_iff, mem_setOf_eq]
        rw [indicator_of_mem hr0]; exact hne⟩
      rw [indicator_of_mem hmem] at h
      simp at h
    · exact absurd h (by simp; positivity)
  -- a continuous function equal a.e. to a nonincreasing one is nonincreasing
  have hanti : AntitoneOn K (Ioi 0) := antitoneOn_of_ae_eq hKc O.k_antitone hae'
  have hanti' : AntitoneOn (polarProfileOf (witnessProfile w) n) (Ioi 0) := by
    intro r hr s hs hrs
    rw [hKw r hr, hKw s hs]
    exact hanti hr hs hrs
  have := (witness_antitone_iff n hn hw).1 hanti'
  linarith

/-- **`thm:filtration-strict`(1)**: for an integer `d ≥ 1` and `w ∈ (w_{d+1}, w_d]`,
`F^{(w)} ∈ 𝒜_d ∖ 𝒜_{d+1}`. Spends A2, A3, A4 through `prop:isotropic-polar-reading`(1). Until
2026-10-05 it also assumed `w ≤ 6 + 4√2`, the bound of [B, Lem. 4.12(1)], which no step read
(admissibility comes from `prop:isotropic-polar-classification`(2)); the author dropped it, a
widening. -/
theorem filtration_witness (d : ℕ) (hd : 1 ≤ d) {w : ℝ} (hw1 : threshold ((d : ℝ) + 1) < w)
    (hw2 : w ≤ threshold d) :
    classA d (witnessF w) ∧ ¬ classA (d + 1) (witnessF w) := by
  have hw : 0 < w := lt_trans (threshold_pos _ (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)) hw1
  exact ⟨witness_classA hd hw hw2,
    witness_not_classA (n := d + 1) (by omega) hw (by push_cast; exact hw1)⟩

/-! ## Clause (2): `w_2 < 6 + 4√2` -/

theorem threshold_two_lt : threshold 2 < 6 + 4 * Real.sqrt 2 := by
  have hM := thresholdFun_le_thresholdSup (d := 2) (by norm_num) (z := 1 / 2) (by norm_num)
  -- `h_2(1/2) = (1/2)^{3/2} (e^{-1/2} - e^{-1/4}/2) > 1/15`
  have he1 : Real.exp (-(1 / 2 : ℝ)) > 3 / 5 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg]
    rw [gt_iff_lt, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  have he2 : Real.exp (-(1 / 4 : ℝ)) < 4 / 5 := by
    have h := Real.add_one_lt_exp (show (1 / 4 : ℝ) ≠ 0 by norm_num)
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hp : (1 / 3 : ℝ) < (1 / 2 : ℝ) ^ ((2 + 1 : ℝ) / 2) := by
    have h32 : (1 / 2 : ℝ) ^ ((2 + 1 : ℝ) / 2) = (1 / 2) * Real.sqrt (1 / 2) := by
      rw [show ((2 + 1 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
        Real.rpow_one, Real.sqrt_eq_rpow]
    rw [h32]
    have hs : (2 / 3 : ℝ) < Real.sqrt (1 / 2) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hh : (1 / 15 : ℝ) < thresholdFun 2 (1 / 2) := by
    unfold thresholdFun
    have h2 : (2 : ℝ) ^ (-(2 : ℝ) / 2) = 1 / 2 := by
      rw [show (-(2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]; norm_num
    rw [h2, show -(1 / 2 : ℝ) / 2 = -(1 / 4) by norm_num]
    have hb : (1 / 5 : ℝ) < Real.exp (-(1 / 2)) - 1 / 2 * Real.exp (-(1 / 4)) := by linarith
    have : (1 / 3 : ℝ) * (1 / 5) < (1 / 2 : ℝ) ^ ((2 + 1 : ℝ) / 2) *
        (Real.exp (-(1 / 2)) - 1 / 2 * Real.exp (-(1 / 4))) :=
      mul_lt_mul'' hp hb (by norm_num) (by norm_num)
    linarith
  have hG := Real.Gamma_three_div_two_lt_one
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  unfold threshold
  rw [show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num]
  have hMpos : (1 / 15 : ℝ) < thresholdSup 2 := lt_of_lt_of_le hh hM
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **`thm:filtration-strict`(2)**: `w_2 < 6 + 4√2`; so the set of `w ∈ (w_{d+1}, w_d]` with
`w ≤ 6 + 4√2` is `(w_{d+1}, w_d]` itself for every `d ≥ 2`, and it is nonempty for every `d ≥ 1`.
(Until 2026-10-05 this was "the parameters allowed in (1)"; clause (1) no longer names the bound.) -/
theorem filtration_witness_exists :
    threshold 2 < 6 + 4 * Real.sqrt 2 ∧
      (∀ d : ℕ, 2 ≤ d → {w : ℝ | threshold ((d : ℝ) + 1) < w ∧ w ≤ threshold d ∧
          w ≤ 6 + 4 * Real.sqrt 2} = Ioc (threshold ((d : ℝ) + 1)) (threshold d)) ∧
      ∀ d : ℕ, 1 ≤ d → {w : ℝ | threshold ((d : ℝ) + 1) < w ∧ w ≤ threshold d ∧
          w ≤ 6 + 4 * Real.sqrt 2}.Nonempty := by
  obtain ⟨hanti, -, hne⟩ := threshold_strictAnti
  have h2 := threshold_two_lt
  have hle : ∀ d : ℕ, 2 ≤ d → threshold d ≤ threshold 2 := by
    intro d hd
    have := hanti.antitoneOn (show (2 : ℕ) ∈ Ici 1 by simp) (show d ∈ Ici 1 by
      simp only [mem_Ici]; omega) hd
    simpa using this
  refine ⟨h2, fun d hd => ?_, fun d hd => ?_⟩
  · ext w
    simp only [mem_setOf_eq, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2'⟩; exact ⟨h1, h2', by linarith [hle d hd]⟩
  · rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · have hd1' : d = 1 := by omega
      subst hd1'
      have h12 : threshold 2 < threshold 1 := by
        have := hanti (show (1 : ℕ) ∈ Ici 1 by simp) (show (2 : ℕ) ∈ Ici 1 by simp)
          (by norm_num)
        simpa using this
      refine ⟨min (threshold 1) (6 + 4 * Real.sqrt 2), ?_, by push_cast; exact min_le_left _ _,
        min_le_right _ _⟩
      push_cast
      norm_num
      exact ⟨h12, h2⟩
    · obtain ⟨w, hw1, hw2⟩ := hne d hd
      exact ⟨w, hw1, hw2, by linarith [hle d hd2]⟩

/-! ## Clause (3): the chain -/

/-- **`thm:filtration-strict`(3)**, the strictness: `𝒜_1 ⊋ 𝒜_2 ⊋ ⋯`, every inclusion strict,
`𝒜_∞ ⊊ 𝒜_d` for every `d`, and no `𝒜_D` equals `𝒜_∞`. The clause's last identification
`𝒜_∞ = 𝒮` is `filtration_top`. -/
theorem filtration_strict :
    (∀ d : ℕ, 1 ≤ d → {F : ℝ → ℝ | classA (d + 1) F} ⊂ {F | classA d F}) ∧
      (∀ d : ℕ, 1 ≤ d → {F : ℝ → ℝ | classAInf F} ⊂ {F | classA d F}) ∧
      ∀ D : ℕ, 1 ≤ D → {F : ℝ → ℝ | classA D F} ≠ {F | classAInf F} := by
  have hsep : ∀ d : ℕ, 1 ≤ d → ∃ F : ℝ → ℝ, classA d F ∧ ¬ classA (d + 1) F := by
    intro d hd
    obtain ⟨w, hw1, hw2, -⟩ := filtration_witness_exists.2.2 d hd
    exact ⟨witnessF w, filtration_witness d hd hw1 hw2⟩
  have hinf : ∀ d : ℕ, 1 ≤ d → {F : ℝ → ℝ | classAInf F} ⊂ {F | classA d F} := by
    intro d hd
    refine ⟨fun F hF => hF d hd, fun hsub => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hsep d hd
    exact hF' ((hsub hF : classAInf F) (d + 1) (by omega))
  refine ⟨fun d hd => ⟨fun F hF => classA_of_succ hF, fun hsub => ?_⟩, hinf, fun D hD heq => ?_⟩
  · obtain ⟨F, hF, hF'⟩ := hsep d hd
    exact hF' (hsub hF)
  · exact (hinf D hD).ne heq.symm

end AffineHemigroup
