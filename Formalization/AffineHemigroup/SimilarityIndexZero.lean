/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityBounded
import AffineHemigroup.SimilarityOrbit
import AffineHemigroup.SimilarityStableOrder
import AffineHemigroup.ExponentLog
import AffineHemigroup.LogOrbitRays
import AffineHemigroup.TripletSum
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `prop:similarity-general-index-zero` — index `0` for a general part: shape-blind at the origin

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-general-index-zero`
(Q-0281 wave 2, group H). Spends A3(i)–(ii) through `prop:similarity-general-sandwich`, and A3(iii)
once in (3) under the first hypothesis.

## The route

The blueprint's. (1) reads the sandwich `L_{λ_-I} ≤ L_Σ ≤ L_{λ_+I}` and the polar form of
`L_{tI}(K_A(ε)) = σ̄(A) ∫_{ε/√t}^{1/√t} k_I(r) dr/r`. (2) reads the sandwich of the exponents and
`lem:isotropic-exponent-log`(2). (3) is the blow-up: for every complex Schwartz function `φ`,
`∫ φ(x/R) ρ(dx) = ∫ 𝓕φ(ξ) ρ̂(2πξ/R) dξ`; the left side tends to `φ(0)ρ{0}` (a Schwartz function
tends to `0` at infinity, so no compact support is needed and the density of `C_c^∞` in the Schwartz
space is not used), the right side to `∫ 𝓕φ H` (dominated convergence, `H` the almost-everywhere
blow-up limit). Taking `φ = 𝓕⁻¹g` for a real `g ∈ C_c^∞` gives `∫ g (H - ρ{0}) = 0`, and the
fundamental lemma of the calculus of variations (Mathlib's
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `H = ρ{0}` almost everywhere. The passage
between `σ̄`-almost every direction and Lebesgue-almost every point is the polar form of Lebesgue
measure (`lintegral_polar`).
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set Filter Real
open scoped MatrixOrder RealInnerProductSpace Topology ENNReal FourierTransform

variable {d : ℕ}

/-! ## The exponent of the datum, and cluster points -/

/-- `F_d = ψ_{ν_d}` for a datum without a Gaussian part. -/
theorem OriginDatum.exponent_eq_levyExp (D : OriginDatum d) (ha : D.a = 0) (ω : Rd d) :
    D.exponent ω = levyExp D.levyMeasure ω := by
  simp [OriginDatum.exponent, OriginDatum.exponentL, levyExp, levyExpL, ha]

/-- A cluster point of `f ≤ g` along `F`, with `g → b`, is at most `b`. -/
theorem mapClusterPt_le_of_le {α : Type*} {F : Filter α} {f g : α → ℝ} {b y : ℝ}
    (hfg : ∀ x, f x ≤ g x) (hg : Tendsto g F (𝓝 b)) (hy : MapClusterPt y F f) : y ≤ b := by
  by_contra h
  push Not at h
  have hev : ∀ᶠ x in F, g x < (b + y) / 2 := hg.eventually (gt_mem_nhds (by linarith))
  have hfr := (mapClusterPt_iff_frequently.1 hy) (Ioi ((b + y) / 2)) (Ioi_mem_nhds (by linarith))
  obtain ⟨x, hx1, hx2⟩ := (hfr.and_eventually hev).exists
  have := hfg x
  simp only [mem_Ioi] at hx1
  linarith

/-- A cluster point of `f ≥ g` along `F`, with `g → b`, is at least `b`. -/
theorem le_mapClusterPt_of_le {α : Type*} {F : Filter α} {f g : α → ℝ} {b y : ℝ}
    (hfg : ∀ x, g x ≤ f x) (hg : Tendsto g F (𝓝 b)) (hy : MapClusterPt y F f) : b ≤ y := by
  have h := mapClusterPt_le_of_le (f := fun x => -f x) (g := fun x => -g x) (b := -b) (y := -y)
    (fun x => neg_le_neg (hfg x)) hg.neg (by
      have := hy.map (continuous_neg.continuousAt) (tendsto_map)
      simpa [MapClusterPt, Function.comp_def] using this)
  linarith

/-! ## Clause (1): the profile near the origin -/

/-- **The logarithmic index of the profile**: `∫_{εs}^s k_d(r) dr/r / log(1/ε) → c` as `ε ↓ 0`. -/
theorem OriginDatum.tendsto_integral_k_log (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => (∫ r in (ε * s)..s, D.k r / r) / Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 D.profileAtOrigin.toReal) := by
  set c := D.profileAtOrigin.toReal with hcdef
  have hlogpos : ∀ ε : ℝ, 0 < ε → ε < 1 → 0 < Real.log (1 / ε) := fun ε h0 h1 =>
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ h0 |>.2 h1)
  have hev01 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 :=
    (eventually_nhdsWithin_of_forall fun ε (h : 0 < ε) => h).and
      (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos))
  /- The upper bound `∫ ≤ c log(1/ε)`. -/
  have hup : ∀ ε : ℝ, 0 < ε → ε < 1 → ∫ r in (ε * s)..s, D.k r / r ≤ c * Real.log (1 / ε) := by
    intro ε h0 h1
    have hb : (1 : ℝ) ≤ 1 / ε := by rw [one_div]; exact (one_le_inv₀ h0).2 h1.le
    have hbx : 1 / ε * (ε * s) = s := by field_simp
    have h := (D.integral_k_div_bounds (x := ε * s) (b := 1 / ε) (m := 0) (M := c)
      (by positivity) hb (fun v hv => D.k_nonneg v (lt_of_lt_of_le (by positivity) hv.1))
      (fun v hv => D.k_le_toReal hc (lt_of_lt_of_le (by positivity) hv.1))).2
    rwa [hbx] at h
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · /- From below: `k ≥ c'` near `0`, for `a < c' < c`. -/
    set c' := (a + c) / 2 with hc'
    have hc'c : c' < c := by linarith
    have hk : ∀ᶠ r in 𝓝[>] (0 : ℝ), c' < D.k r :=
      (D.tendsto_k_zero hc).eventually (lt_mem_nhds hc'c)
    obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hk
    have hr₀0 : 0 < r₀ := hr₀
    set s0 := min s (r₀ / 2) with hs0
    have hs00 : 0 < s0 := lt_min hs (by linarith)
    have hs0s : s0 ≤ s := min_le_left _ _
    have hs0r : s0 < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hlow : ∀ ε : ℝ, 0 < ε → ε < 1 → ε * s < s0 →
        c' * Real.log (s0 / s) + c' * Real.log (1 / ε) ≤ ∫ r in (ε * s)..s, D.k r / r := by
      intro ε h0 _ hεs
      have hx : 0 < ε * s := by positivity
      have hb : (1 : ℝ) ≤ s0 / (ε * s) := by rw [le_div_iff₀ hx, one_mul]; exact hεs.le
      have hbx : s0 / (ε * s) * (ε * s) = s0 := by field_simp
      have h := (D.integral_k_div_bounds (x := ε * s) (b := s0 / (ε * s)) (m := c') (M := c)
        hx hb (fun v hv => ?_)
        (fun v hv => D.k_le_toReal hc (lt_of_lt_of_le hx hv.1))).1
      · rw [hbx] at h
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (D.intervalIntegrable_k_div hx hεs.le) (D.intervalIntegrable_k_div hs00 hs0s)
        have hnn : 0 ≤ ∫ r in s0..s, D.k r / r :=
          intervalIntegral.integral_nonneg hs0s fun v hv =>
            div_nonneg (D.k_nonneg v (lt_of_lt_of_le hs00 hv.1)) (hs00.trans_le hv.1).le
        have hlog : Real.log (s0 / (ε * s)) = Real.log (s0 / s) + Real.log (1 / ε) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          congr 1
          field_simp
        rw [hlog, mul_add] at h
        linarith
      · rw [hbx] at hv
        exact (hsub ⟨lt_of_lt_of_le hx hv.1, lt_of_le_of_lt hv.2 hs0r⟩).le
    /- The lower bound tends to `c' > a`. -/
    have hlogtop : Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] 0) atTop := by
      have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
      simpa [one_div, Function.comp_def] using this
    have hg : Tendsto (fun ε : ℝ => c' + c' * Real.log (s0 / s) / Real.log (1 / ε)) (𝓝[>] 0)
        (𝓝 c') := by
      have := (tendsto_const_nhds (x := c' * Real.log (s0 / s))).div_atTop hlogtop
      simpa using (tendsto_const_nhds (x := c')).add this
    have hgev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < c' + c' * Real.log (s0 / s) / Real.log (1 / ε) :=
      hg.eventually (lt_mem_nhds (by linarith))
    have hεs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * s < s0 := by
      have : Tendsto (fun ε : ℝ => ε * s) (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun ε : ℝ => ε * s) (𝓝 0) (𝓝 (0 * s)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact this.eventually (gt_mem_nhds hs00)
    filter_upwards [hgev, hev01, hεs] with ε hε hε01 hεs'
    have hl := hlogpos ε hε01.1 hε01.2
    refine lt_of_lt_of_le hε ?_
    rw [le_div_iff₀ hl, add_mul, div_mul_cancel₀ _ hl.ne']
    have := hlow ε hε01.1 hε01.2 hεs'
    linarith
  · filter_upwards [hev01] with ε hε
    have hl := hlogpos ε hε.1 hε.2
    rw [div_lt_iff₀ hl]
    have := hup ε hε.1 hε.2
    nlinarith

/-- `σ̄` is a probability measure on the sphere; in particular `σ̄(A) < ∞`. -/
theorem normSphere_apply (hd : 1 ≤ d) {A : Set (Rd d)} (hA : MeasurableSet A) :
    normSphere d A = (ENNReal.ofReal (sphereArea d))⁻¹ *
      (volume : Measure (Rd d)).toSphere (Subtype.val ⁻¹' A) := by
  rw [normSphere, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hA, smul_eq_mul,
    (sphereArea_eq_toSphere hd).1]

theorem normSphere_ne_top (hd : 1 ≤ d) (A : Set (Rd d)) : normSphere d A ≠ ⊤ := by
  have hA := sphereArea_eq_toSphere hd
  refine ne_top_of_le_ne_top (b := normSphere d univ) ?_ (measure_mono (subset_univ A))
  rw [normSphere_apply hd MeasurableSet.univ, preimage_univ, ← hA.1,
    ENNReal.inv_mul_cancel (by simp [hA.2]) ENNReal.ofReal_ne_top]
  exact ENNReal.one_ne_top

/-- **The polar form of a sector**: `ν_d{x < |z| ≤ y, z/|z| ∈ A} = σ̄(A) ∫_x^y k_d(r) dr/r`. -/
theorem OriginDatum.levyMeasure_sector (hd : 1 ≤ d) (D : OriginDatum d) {A : Set (Rd d)}
    (hA : MeasurableSet A) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    D.levyMeasure {z | x < ‖z‖ ∧ ‖z‖ ≤ y ∧ ‖z‖⁻¹ • z ∈ A} =
      normSphere d A * ENNReal.ofReal (∫ r in x..y, D.k r / r) := by
  set K : Set (Rd d) := {z | x < ‖z‖ ∧ ‖z‖ ≤ y ∧ ‖z‖⁻¹ • z ∈ A} with hK
  have hnorm : Measurable fun z : Rd d => ‖z‖⁻¹ • z := (measurable_norm.inv).smul measurable_id
  have hKm : MeasurableSet K :=
    (measurableSet_lt measurable_const measurable_norm).inter
      ((measurableSet_le measurable_norm measurable_const).inter (hnorm hA))
  have hK0 : (0 : Rd d) ∉ K := fun h => by
    have := h.1; simp at this; linarith
  rw [← lintegral_indicator_one hKm, polar_decomposition hd D _ (measurable_one.indicator hKm)
    (indicator_of_notMem hK0 _)]
  /- The inner integral. -/
  set J : ℝ≥0∞ := ∫⁻ r in Ioc x y, ENNReal.ofReal (D.k r / r) with hJ
  have hinner : ∀ η : Metric.sphere (0 : Rd d) 1,
      ∫⁻ r in Ioi (0 : ℝ), K.indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r) =
        A.indicator 1 (η : Rd d) * J := by
    intro η
    have hη : ‖(η : Rd d)‖ = 1 := by simp
    have hpt : ∀ r : ℝ, 0 < r → K.indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r) =
        A.indicator 1 (η : Rd d) * (Ioc x y).indicator (fun r => ENNReal.ofReal (D.k r / r)) r := by
      intro r hr
      have hn : ‖r • (η : Rd d)‖ = r := by rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr.le]
      have hu : ‖r • (η : Rd d)‖⁻¹ • (r • (η : Rd d)) = η := by
        rw [hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      by_cases hrI : r ∈ Ioc x y
      · rw [indicator_of_mem hrI]
        by_cases hηA : (η : Rd d) ∈ A
        · rw [indicator_of_mem (show r • (η : Rd d) ∈ K from ⟨by rw [hn]; exact hrI.1,
            by rw [hn]; exact hrI.2, by rw [hu]; exact hηA⟩), indicator_of_mem hηA]
          rfl
        · rw [indicator_of_notMem (show r • (η : Rd d) ∉ K from fun h => hηA (by
            have := h.2.2; rwa [hu] at this)), indicator_of_notMem hηA]
      · rw [indicator_of_notMem hrI, mul_zero, indicator_of_notMem (show r • (η : Rd d) ∉ K from
          fun h => hrI ⟨by have := h.1; rwa [hn] at this, by have := h.2.1; rwa [hn] at this⟩),
          zero_mul]
    have hne : A.indicator (1 : Rd d → ℝ≥0∞) (η : Rd d) ≠ ⊤ := by
      by_cases h : (η : Rd d) ∈ A <;> simp [h]
    rw [setLIntegral_congr_fun measurableSet_Ioi fun r hr => hpt r hr, lintegral_const_mul' _ _ hne,
      lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Ioc_inter_Ioi, max_eq_left hx.le]
  simp_rw [hinner]
  have hfun : (fun η : Metric.sphere (0 : Rd d) 1 => A.indicator (1 : Rd d → ℝ≥0∞) (η : Rd d)) =
      (Subtype.val ⁻¹' A).indicator 1 := by
    funext η
    by_cases h : (η : Rd d) ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (show η ∈ Subtype.val ⁻¹' A from h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show η ∉ Subtype.val ⁻¹' A from h)]
  rw [lintegral_mul_const (r := J)
      (f := fun η : Metric.sphere (0 : Rd d) 1 => A.indicator (1 : Rd d → ℝ≥0∞) (η : Rd d))
      ((measurable_one.indicator hA).comp measurable_subtype_coe), hfun,
    lintegral_indicator_one (measurable_subtype_coe hA), ← mul_assoc, ← normSphere_apply hd hA]
  congr 1
  rw [hJ, intervalIntegral.integral_of_le hxy, ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).1 (D.intervalIntegrable_k_div hx hxy)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact div_nonneg (D.k_nonneg r (hx.trans hr.1)) (hx.trans hr.1).le

/-! ## The rays: the dilation limit of the exponent -/

section Family

variable {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d} {L : Mat d → Measure (Rd d)}

/-- `ψ_{tI}(ω) - ψ_I(ω) → (c/2) log t` as `|ω| → ∞`. -/
theorem tendsto_levyExp_ray (hd : 2 ≤ d) (hfam : IsSimGeneralFamily μ C L) (D : OriginDatum d)
    (hDa : D.a = 0) (hL1 : L 1 = D.levyMeasure) (hc : D.profileAtOrigin ≠ ⊤) {t : ℝ}
    (ht : 0 < t) :
    Tendsto (fun ω => levyExp (L (t • (1 : Mat d))) ω - levyExp (L 1) ω) (cocompact (Rd d))
      (𝓝 (D.profileAtOrigin.toReal / 2 * Real.log t)) := by
  have hd1 : 1 ≤ d := by omega
  have h := (isotropic_exponent_log_limit hd1 D hDa hc (Real.sqrt t) (Real.sqrt_pos.2 ht)).1
  have hlog : D.profileAtOrigin.toReal * Real.log (Real.sqrt t) =
      D.profileAtOrigin.toReal / 2 * Real.log t := by
    rw [Real.log_sqrt ht.le]; ring
  rw [hlog] at h
  refine h.congr fun ω => ?_
  rw [(sim_general_scale hd hfam PosDef.one ht).2 ω, hL1, D.exponent_eq_levyExp hDa,
    D.exponent_eq_levyExp hDa]

/-- **The sandwich along the rays** `λ_min(Σ) I ≤ Σ ≤ λ_max(Σ) I`. -/
theorem levyExp_sandwich_rays (hd : 2 ≤ d) (hfam : IsSimGeneralFamily μ C L)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ))
    {S : Mat d} (hS : S.PosDef) (ω : Rd d) :
    levyExp (L (lamMin S • (1 : Mat d))) ω ≤ levyExp (L S) ω ∧
      levyExp (L S) ω ≤ levyExp (L (lamMax S • (1 : Mat d))) ω := by
  haveI : NeZero d := ⟨by omega⟩
  have hlm : 0 < lamMin S := lamMin_pos hS
  have hlM : 0 < lamMax S := lt_of_lt_of_le hlm (lamMin_le_lamMax hS.isHermitian)
  exact ⟨sim_general_mono hd hfam hinc (PosDef.one.smul hlm) hS
      (loewnerLE_lamMin_smul_one hS.isHermitian) ω,
    sim_general_mono hd hfam hinc hS (PosDef.one.smul hlM)
      (loewnerLE_lamMax_smul_one hS.isHermitian) ω⟩

/-! ## Clause (1) -/

/-- `K_A(ε)` is a Borel set. -/
theorem measurableSet_polarSector {A : Set (Rd d)} (hA : MeasurableSet A) (ε : ℝ) :
    MeasurableSet (polarSector A ε) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    ((measurableSet_le measurable_norm measurable_const).inter
      (((measurable_norm.inv).smul measurable_id) hA))

/-- **`L_{tI}(K_A(ε)) = σ̄(A) ∫_{ε/√t}^{1/√t} k_I(r) dr/r`**. -/
theorem levy_ray_sector (hd : 2 ≤ d) (hfam : IsSimGeneralFamily μ C L) (D : OriginDatum d)
    (hL1 : L 1 = D.levyMeasure) {t : ℝ} (ht : 0 < t) {A : Set (Rd d)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    L (t • (1 : Mat d)) (polarSector A ε) = normSphere d A *
      ENNReal.ofReal (∫ r in (ε * (Real.sqrt t)⁻¹)..(Real.sqrt t)⁻¹, D.k r / r) := by
  have hd1 : 1 ≤ d := by omega
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [(sim_general_scale hd hfam PosDef.one ht).1, push, hL1,
    Measure.map_apply (lin _).continuous.measurable (measurableSet_polarSector hA ε)]
  have hset : lin (Real.sqrt t • (1 : Mat d)) ⁻¹' polarSector A ε =
      {z | ε * (Real.sqrt t)⁻¹ < ‖z‖ ∧ ‖z‖ ≤ (Real.sqrt t)⁻¹ ∧ ‖z‖⁻¹ • z ∈ A} := by
    ext z
    have hlz : lin (Real.sqrt t • (1 : Mat d)) z = Real.sqrt t • z := by
      rw [lin_smul, lin_one]; rfl
    have hn : ‖Real.sqrt t • z‖ = Real.sqrt t * ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg hst.le]
    have hu : ‖Real.sqrt t • z‖⁻¹ • (Real.sqrt t • z) = ‖z‖⁻¹ • z := by
      rw [hn, smul_smul, mul_inv, mul_comm (Real.sqrt t)⁻¹, mul_assoc, inv_mul_cancel₀ hst.ne',
        mul_one]
    simp only [mem_preimage, polarSector, mem_setOf_eq, hlz]
    have hiff : ‖z‖ ≤ (Real.sqrt t)⁻¹ ↔ ‖z‖ * Real.sqrt t ≤ 1 := by
      rw [show (Real.sqrt t)⁻¹ = 1 / Real.sqrt t from (one_div _).symm, le_div_iff₀ hst]
    rw [hu, hn, ← div_eq_mul_inv, div_lt_iff₀ hst, hiff]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨by linarith, by linarith, h3⟩
  rw [hset]
  exact D.levyMeasure_sector hd1 hA (by positivity)
    (mul_le_of_le_one_left (by positivity) hε1.le)

/-- `L_{tI}(K_A(ε))/log(1/ε) → c σ̄(A)`. -/
theorem tendsto_levy_ray_sector (hd : 2 ≤ d) (hfam : IsSimGeneralFamily μ C L)
    (D : OriginDatum d) (hL1 : L 1 = D.levyMeasure) (hc : D.profileAtOrigin ≠ ⊤) {t : ℝ}
    (ht : 0 < t) {A : Set (Rd d)} (hA : MeasurableSet A) :
    Tendsto (fun ε => (L (t • (1 : Mat d)) (polarSector A ε)).toReal / Real.log (1 / ε))
      (𝓝[>] 0) (𝓝 (D.profileAtOrigin.toReal * (normSphere d A).toReal)) := by
  have hd1 : 1 ≤ d := by omega
  have hst : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht)
  have h := (D.tendsto_integral_k_log hc hst).const_mul (normSphere d A).toReal
  rw [mul_comm] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds one_pos)] with ε (hε : 0 < ε) hε1
  rw [levy_ray_sector hd hfam D hL1 ht hA hε hε1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg
      (mul_le_of_le_one_left hst.le hε1.le) fun v hv =>
        div_nonneg (D.k_nonneg v (lt_of_lt_of_le (by positivity) hv.1))
          (lt_of_lt_of_le (by positivity) hv.1).le), mul_div_assoc]

/-- **`prop:similarity-general-index-zero`(1)**, the index at the origin: if `L_I` is the Lévy
measure of an origin datum `(0, k_I)` with `c := k_I(0+) < ∞` and every Loewner step has an
infinitely divisible increment, then `L_Σ(K_A(ε))/log(1/ε) → c σ̄(A)` as `ε ↓ 0`, for every
`Σ ∈ PD(d)` and Borel `A ⊆ S^{d-1}`. -/
theorem sim_index_zero_levy (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) (D : OriginDatum d)
    (_hDa : D.a = 0) (hL1 : L 1 = D.levyMeasure) (hc : D.profileAtOrigin ≠ ⊤)
    (hID : HasIDLoewnerIncrements μ) :
    ∀ S : Mat d, S.PosDef → ∀ A : Set (Rd d), A ⊆ Metric.sphere 0 1 → MeasurableSet A →
      Tendsto (fun ε => (L S (polarSector A ε)).toReal / Real.log (1 / ε)) (𝓝[>] 0)
        (𝓝 (D.profileAtOrigin.toReal * (normSphere d A).toReal)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  intro S hS A _ hA
  have hlm : 0 < lamMin S := lamMin_pos hS
  have hlM : 0 < lamMax S := lt_of_lt_of_le hlm (lamMin_le_lamMax hS.isHermitian)
  /- The sandwich of Lévy measures. -/
  have hlow : L (lamMin S • (1 : Mat d)) ≤ L S := by
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ S (PosDef.one.smul hlm) hS
      (loewnerLE_lamMin_smul_one hS.isHermitian)
    exact (sim_general_id_increment hd μ C L hfam _ S (PosDef.one.smul hlm) hS ρ hρ hρid heq).2.1
  have hup : L S ≤ L (lamMax S • (1 : Mat d)) := by
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID S _ hS (PosDef.one.smul hlM)
      (loewnerLE_lamMax_smul_one hS.isHermitian)
    exact (sim_general_id_increment hd μ C L hfam S _ hS (PosDef.one.smul hlM) ρ hρ hρid heq).2.1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_levy_ray_sector hd hfam D hL1 hc hlm hA)
    (tendsto_levy_ray_sector hd hfam D hL1 hc hlM hA) ?_ ?_ <;>
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds one_pos)] with ε (hε : 0 < ε) hε1 <;>
  have hl : 0 < Real.log (1 / ε) :=
    Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hε).2 hε1) <;>
  have hfin : L (lamMax S • (1 : Mat d)) (polarSector A ε) ≠ ⊤ := by
    rw [levy_ray_sector hd hfam D hL1 hlM hA hε hε1]
    exact ENNReal.mul_ne_top (normSphere_ne_top hd1 A) ENNReal.ofReal_ne_top
  · exact div_le_div_of_nonneg_right (ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (hup _))
      (hlow _)) hl.le
  · exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hfin (hup _)) hl.le

/-! ## Clause (2) -/

/-- **`prop:similarity-general-index-zero`(2)**, the exponent to within a bounded term: under
either hypothesis, every limit point of `ψ_Σ(ω) - ψ_I(ω)` as `|ω| → ∞` lies in
`[(c/2) log λ_min(Σ), (c/2) log λ_max(Σ)]`. -/
theorem sim_index_zero_exp (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) (D : OriginDatum d)
    (hDa : D.a = 0) (hL1 : L 1 = D.levyMeasure) (hc : D.profileAtOrigin ≠ ⊤)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ)) :
    ∀ S : Mat d, S.PosDef → ∀ y : ℝ,
      MapClusterPt y (cocompact (Rd d)) (fun ω => levyExp (L S) ω - levyExp (L 1) ω) →
      y ∈ Icc (D.profileAtOrigin.toReal / 2 * Real.log (lamMin S))
        (D.profileAtOrigin.toReal / 2 * Real.log (lamMax S)) := by
  haveI : NeZero d := ⟨by omega⟩
  intro S hS y hy
  have hlm : 0 < lamMin S := lamMin_pos hS
  have hlM : 0 < lamMax S := lt_of_lt_of_le hlm (lamMin_le_lamMax hS.isHermitian)
  have hsw := levyExp_sandwich_rays hd hfam hinc hS
  exact ⟨le_mapClusterPt_of_le (fun ω => sub_le_sub_right (hsw ω).1 _)
      (tendsto_levyExp_ray hd hfam D hDa hL1 hc hlm) hy,
    mapClusterPt_le_of_le (fun ω => sub_le_sub_right (hsw ω).2 _)
      (tendsto_levyExp_ray hd hfam D hDa hL1 hc hlM) hy⟩

end Family

/-! ## Clause (3): the blow-up of a positive increment -/

/-- **The Fourier side for a Schwartz function**: for `R > 0` and a finite measure `ρ`,
`∫ φ(x/R) ρ(dx) = ∫ 𝓕φ(ξ) ρ̂(2πξ/R) dξ`. -/
theorem integral_schwartz_dilate_eq_fourier (φ : SchwartzMap (Rd d) ℂ) (ρ : Measure (Rd d))
    [IsFiniteMeasure ρ] {R : ℝ} :
    ∫ x, φ (R⁻¹ • x) ∂ρ = ∫ ξ, (𝓕 φ) ξ * charFun ρ ((2 * π * R⁻¹) • ξ) := by
  set Φ : Rd d → ℂ := fun ξ => (𝓕 φ) ξ with hΦ
  have hΦi : Integrable Φ := (𝓕 φ).integrable
  have hinv : ∀ x : Rd d, ∫ ξ, Complex.exp (↑(2 * π * ⟪ξ, x⟫) * Complex.I) * Φ ξ = φ x := by
    intro x
    have h := φ.continuous.fourierInv_fourier_eq φ.integrable (𝓕 φ).integrable
    have hx := congrFun h x
    rw [fourierInv_eq'] at hx
    simp only [smul_eq_mul] at hx
    rw [hΦ]
    simp_rw [SchwartzMap.fourier_coe]
    exact hx
  set F : Rd d → Rd d → ℂ := fun x ξ =>
    Complex.exp (↑(2 * π * ⟪ξ, R⁻¹ • x⟫) * Complex.I) * Φ ξ with hF
  have hint : Integrable (Function.uncurry F) (ρ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF, Function.uncurry_def]
      exact (by fun_prop : Continuous fun p : Rd d × Rd d =>
        Complex.exp (↑(2 * π * ⟪p.2, R⁻¹ • p.1⟫) * Complex.I)).mul
          ((𝓕 φ).continuous.comp continuous_snd)
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, one_mul]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
  have h1 : ∀ x, φ (R⁻¹ • x) = ∫ ξ, F x ξ := fun x => (hinv (R⁻¹ • x)).symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1
  funext ξ
  simp only [hF]
  rw [integral_mul_const, mul_comm, charFun_apply]
  congr 2
  funext x
  congr 1
  rw [inner_smul_right, inner_smul_right, real_inner_comm]
  push_cast
  ring

/-- **The measure side**: `∫ φ(x/R) ρ(dx) → φ(0) ρ{0}` as `R ↓ 0`, for a Schwartz `φ` (which tends
to `0` at infinity) and a finite `ρ`. -/
theorem tendsto_integral_schwartz_dilate (φ : SchwartzMap (Rd d) ℂ) (ρ : Measure (Rd d))
    [IsFiniteMeasure ρ] :
    Tendsto (fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ) (𝓝[>] 0) (𝓝 (φ 0 * ((ρ {0}).toReal : ℂ))) := by
  have hlim : ∫ x, ({0} : Set (Rd d)).indicator (fun _ => φ 0) x ∂ρ =
      φ 0 * ((ρ {0}).toReal : ℂ) := by
    rw [integral_indicator (measurableSet_singleton 0), setIntegral_const, Complex.real_smul,
      mul_comm, measureReal_def]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => SchwartzMap.seminorm ℝ 0 0 φ)
    (Eventually.of_forall fun R =>
      (φ.continuous.comp (continuous_const_smul _)).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun x =>
      SchwartzMap.norm_le_seminorm ℝ φ _) (integrable_const _) (Eventually.of_forall fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [smul_zero, indicator_of_mem (mem_singleton (0 : Rd d))]
    exact tendsto_const_nhds
  · rw [indicator_of_notMem (by simpa using hx)]
    refine (SchwartzMap.tendsto_cocompact φ).comp ?_
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h := tendsto_inv_nhdsGT_zero.atTop_mul_const hn
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hR).le]

/-! ## Directions and points: `σ̄`-almost every direction is Lebesgue-almost every point -/

/-- `σ_{d-1}(N ∩ S^{d-1}) = 0` when `σ̄(N) = 0`. -/
theorem toSphere_preimage_eq_zero (hd : 1 ≤ d) {N : Set (Rd d)} (hN : MeasurableSet N)
    (h0 : normSphere d N = 0) :
    (volume : Measure (Rd d)).toSphere (Subtype.val ⁻¹' N) = 0 := by
  rw [normSphere_apply hd hN] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  · exact h

/-- `r eᵤ` has direction `u`, for `r > 0` and a unit `u`. -/
theorem dir_smul_unit {u : Rd d} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    r • u ≠ 0 ∧ ‖r • u‖⁻¹ • (r • u) = u := by
  have hn : ‖r • u‖ = r := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  refine ⟨fun h => ?_, by rw [hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]⟩
  have := congrArg norm h
  rw [hn, norm_zero] at this
  exact hr.ne' this

/-- **A property of `σ̄`-almost every direction holds at Lebesgue-almost every point.** -/
theorem ae_of_ae_normSphere (hd : 1 ≤ d) {P : Rd d → Prop} (h : ∀ᵐ u ∂normSphere d, P u) :
    ∀ᵐ x : Rd d, x ≠ 0 → P (‖x‖⁻¹ • x) := by
  rw [ae_iff] at h ⊢
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hσ := toSphere_preimage_eq_zero hd hN hN0
  set K : Set (Rd d) := {x | x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ N} with hK
  have hKm : MeasurableSet K :=
    (measurableSet_singleton (0 : Rd d)).compl.inter
      (((measurable_norm.inv).smul measurable_id) hN)
  refine measure_mono_null (t := K) (fun x hx => ?_) ?_
  · simp only [mem_setOf_eq, Classical.not_imp] at hx
    exact ⟨hx.1, hsub hx.2⟩
  rw [← lintegral_indicator_one hKm, lintegral_polar hd _ (measurable_one.indicator hKm)]
  have hnull : ∀ᵐ η ∂(volume : Measure (Rd d)).toSphere, η ∉ Subtype.val ⁻¹' N :=
    measure_eq_zero_iff_ae_notMem.1 hσ
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hnull] with η hη
  refine (setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_).trans
    lintegral_zero
  have hu : ‖(η : Rd d)‖ = 1 := by simp
  obtain ⟨-, hdir⟩ := dir_smul_unit hu hr
  rw [indicator_of_notMem (show r • (η : Rd d) ∉ K from fun hk => hη (by
    have := hk.2; rwa [hdir] at this)), zero_mul]

/-- **A property of Lebesgue-almost every point's direction holds at `σ̄`-almost every
direction.** -/
theorem ae_normSphere_of_ae (hd : 1 ≤ d) {P : Rd d → Prop}
    (h : ∀ᵐ x : Rd d, x ≠ 0 → P (‖x‖⁻¹ • x)) : ∀ᵐ u ∂normSphere d, P u := by
  rw [ae_iff] at h ⊢
  obtain ⟨M, hsub, hM, hM0⟩ := exists_measurable_superset_of_null h
  set radI : Rd d → ℝ≥0∞ := fun u => ∫⁻ r in Ioi (0 : ℝ),
    M.indicator 1 (r • u) * ENNReal.ofReal (r ^ (d - 1)) with hinner
  have hmeas : Measurable radI := by
    refine Measurable.lintegral_prod_right' (f := fun p : Rd d × ℝ =>
      M.indicator 1 (p.2 • p.1) * ENNReal.ofReal (p.2 ^ (d - 1))) ?_
    exact ((measurable_one.indicator hM).comp (measurable_snd.smul measurable_fst)).mul
      ((measurable_snd.pow_const _).ennreal_ofReal)
  /- `∫_sphere radI = |M| = 0`. -/
  have hzero : ∀ᵐ η : Metric.sphere (0 : Rd d) 1 ∂(volume : Measure (Rd d)).toSphere,
      radI (η : Rd d) = 0 := by
    have h1 := lintegral_polar hd _ (measurable_one.indicator hM)
    rw [lintegral_indicator_one hM, hM0] at h1
    exact (lintegral_eq_zero_iff (hmeas.comp measurable_subtype_coe)).1 h1.symm
  set T : Set (Rd d) := (Metric.sphere (0 : Rd d) 1)ᶜ ∪ {u | radI u ≠ 0} with hT
  have hTm : MeasurableSet T :=
    Metric.isClosed_sphere.measurableSet.compl.union (hmeas (measurableSet_singleton 0).compl)
  refine measure_mono_null (t := T) (fun u hu => ?_) ?_
  · by_cases hs : u ∈ Metric.sphere (0 : Rd d) 1
    · refine Or.inr ?_
      have hun : ‖u‖ = 1 := by simpa using hs
      have hall : ∀ r : ℝ, 0 < r → r • u ∈ M := by
        intro r hr
        obtain ⟨hne, hdir⟩ := dir_smul_unit hun hr
        refine hsub ?_
        simp only [mem_setOf_eq, Classical.not_imp]
        exact ⟨hne, by rw [hdir]; exact hu⟩
      simp only [mem_setOf_eq, hinner]
      have heq : ∫⁻ r in Ioi (0 : ℝ), M.indicator 1 (r • u) * ENNReal.ofReal (r ^ (d - 1)) =
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) :=
        setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => by
          rw [indicator_of_mem (hall r hr), Pi.one_apply, one_mul]
      rw [heq]
      refine ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) ?_)
      have htop : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ ((d - 1 : ℕ) : ℝ)) = ⊤ :=
        lintegral_Ioi_one_rpow_eq_top (by
          have : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)
      calc (1 : ℝ≥0∞) ≤ ⊤ := le_top
        _ = ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ (d - 1)) := by
            rw [← htop]
            refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
            rw [Real.rpow_natCast]
        _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) :=
            lintegral_mono_set (Ioi_subset_Ioi zero_le_one)
    · exact Or.inl hs
  · rw [normSphere_apply hd hTm]
    have hpre : Subtype.val ⁻¹' T = {η : Metric.sphere (0 : Rd d) 1 | radI (η : Rd d) ≠ 0} := by
      ext η
      simp [hT]
    rw [hpre, measure_eq_zero_iff_ae_notMem.2 (by
      filter_upwards [hzero] with η hη
      simpa using hη), mul_zero]

/-! ## Clause (3): the increment and the blow-up -/

section Blowup

variable {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d} {L : Mat d → Measure (Rd d)}

/-- **A probability measure with transform `e^{-(ψ_{Σ'} - ψ_Σ)}`** for a Loewner step `Σ ≤ Σ'`: the
positive increment itself without a Gaussian part, and under infinitely divisible increments the law
with triplet `(0, L_{Σ'} - L_Σ, 0)` (the difference symmetrized; A3(iii)). -/
theorem exists_increment_levyExp (hd : 2 ≤ d) (hfam : IsSimGeneralFamily μ C L)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hle : loewnerLE S S') :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      ∀ ω, charFun ρ ω = ((Real.exp (-(levyExp (L S') ω - levyExp (L S) ω)) : ℝ) : ℂ) := by
  rcases hinc with hID | ⟨hC, hfin⟩
  · obtain ⟨ρ0, hρ0, hρ0id, heq⟩ := hID S S' hS hS' hle
    haveI := hfam.isProbability S hS
    haveI := hfam.isProbability S' hS'
    haveI := hρ0
    obtain ⟨T, -, hTν, -, hT⟩ := hfam.triplet S hS
    obtain ⟨T', -, hTν', -, hT'⟩ := hfam.triplet S' hS'
    obtain ⟨Tρ, -, -, hν, -⟩ := triplet_increment hρ0id (hfam.infinitelyDivisible S' hS') hT heq hT'
    rw [hTν, hTν'] at hν
    set e : Rd d → Rd d := ⇑(LinearIsometryEquiv.neg ℝ (E := Rd d)) with he
    have hem : Measurable e := (LinearIsometryEquiv.neg ℝ (E := Rd d)).continuous.measurable
    have hee : ∀ x, e (e x) = x := fun x => by simp [he]
    have hne : ∀ x, ‖e x‖ = ‖x‖ := fun x => by simp [he]
    set ν := Tρ.ν with hνdef
    set ν' : Measure (Rd d) := (2⁻¹ : ℝ≥0∞) • (ν + ν.map e) with hν'
    have h2 : (2⁻¹ : ℝ≥0∞) * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    have hmap0 : ν.map e {0} = 0 := by
      rw [Measure.map_apply hem (measurableSet_singleton 0)]
      have : e ⁻¹' {0} = {0} := by ext x; simp [he]
      rw [this]; exact Tρ.ν_zero
    have hν'0 : ν' {0} = 0 := by
      have h0 : ν {0} = 0 := Tρ.ν_zero
      simp only [hν', Measure.smul_apply, Measure.add_apply, h0, hmap0, add_zero, smul_zero]
    have hint : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν' ≠ ⊤ := by
      rw [hν', lintegral_smul_measure, lintegral_add_measure,
        lintegral_map (by fun_prop) hem]
      simp only [hne]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨Tρ.ν_integrable, Tρ.ν_integrable⟩)
    have hsym : ν'.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = ν' := by
      change ν'.map e = ν'
      rw [hν', Measure.map_smul, Measure.map_add _ _ hem, Measure.map_map hem hem]
      have : e ∘ e = id := funext hee
      rw [this, Measure.map_id, add_comm]
    let T0 : LevyTriplet d := ⟨0, ν', 0, PosSemidef.zero, hν'0, hint⟩
    obtain ⟨ρ, hρ, -, hρT⟩ := levy_khintchine_converse T0
    refine ⟨ρ, hρ, fun ω => ?_⟩
    rw [hρT ω, T0.lkExponent_symm rfl hsym ω]
    /- `ψ_{ν'} = ψ_ν = ψ_{Σ'} - ψ_Σ`. -/
    have hcos : ∀ x,
        ENNReal.ofReal (1 - Real.cos ⟪ω, e x⟫) = ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) :=
      fun x => by simp [he, inner_neg_right, Real.cos_neg]
    have hν'exp : levyExpL ν' ω = levyExpL ν ω := by
      rw [levyExpL, hν', lintegral_smul_measure, lintegral_add_measure,
        lintegral_map (by fun_prop) hem]
      simp only [hcos]
      rw [← levyExpL, ← two_mul, smul_eq_mul, ← mul_assoc, h2, one_mul]
    have hLexp : levyExpL (L S') ω = levyExpL (L S) ω + levyExpL ν ω := by
      rw [hν, levyExpL, lintegral_add_measure]; rfl
    have hfinS := (hfam.isLevy hS).levyExpL_ne_top ω
    have hfinS' := (hfam.isLevy hS').levyExpL_ne_top ω
    have hfinν : levyExpL ν ω ≠ ⊤ := by
      refine ne_top_of_le_ne_top hfinS' ?_
      rw [hLexp]; exact le_add_self
    have hlev : levyExp (L S') ω = levyExp (L S) ω + levyExp ν ω := by
      rw [levyExp, levyExp, levyExp, hLexp, ENNReal.toReal_add hfinS hfinν]
    have hz : quad (0 : Mat d) ω = 0 := quad_zero ω
    simp only [T0, hz, zero_div, zero_add]
    rw [levyExp, hν'exp, ← levyExp, hlev, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · obtain ⟨ρ, hρ, heq⟩ := hfin S S' hS hS' hle
    obtain ⟨hρp, hcf, -⟩ := sim_general_finite_increment hd μ C L hfam hC S S' hS hS' ρ hρ heq
    exact ⟨ρ, hρp, hcf⟩

end Blowup

/-- **`prop:similarity-general-index-zero`(3)**, the blow-up: under either hypothesis, if (D) the
limit `Δ_Σ(u) = lim_{r→∞}(ψ_Σ(ru) - ψ_I(ru))` exists for `σ̄`-almost every `u`, then `Δ_Σ` is
`σ̄`-almost everywhere equal to a constant. Spends A3(iii) once under the first hypothesis. -/
theorem sim_index_zero_blowup (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) (D : OriginDatum d)
    (hDa : D.a = 0) (hL1 : L 1 = D.levyMeasure) (hc : D.profileAtOrigin ≠ ⊤)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ))
    (S : Mat d) (hS : S.PosDef) (Δ : Rd d → ℝ)
    (hD : ∀ᵐ u ∂(normSphere d), Tendsto (fun r : ℝ => levyExp (L S) (r • u) - levyExp (L 1) (r • u))
      atTop (𝓝 (Δ u))) :
    ∃ K : ℝ, Δ =ᵐ[normSphere d] fun _ => K := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  set t := lamMax S with htdef
  have ht : 0 < t := lt_of_lt_of_le (lamMin_pos hS) (lamMin_le_lamMax hS.isHermitian)
  obtain ⟨ρ, hρ, hρcf⟩ := exists_increment_levyExp hd hfam hinc hS (PosDef.one.smul ht)
    (loewnerLE_lamMax_smul_one hS.isHermitian)
  set c := D.profileAtOrigin.toReal with hcdef
  set H : Rd d → ℂ := fun ξ => ((Real.exp (-(c / 2 * Real.log t) + Δ (‖ξ‖⁻¹ • ξ)) : ℝ) : ℂ)
    with hH
  /- The blow-up limit at almost every point. -/
  have hray := tendsto_levyExp_ray hd hfam D hDa hL1 hc ht
  have hne0 : ∀ᵐ ξ : Rd d, ξ ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, setOf_eq_eq_singleton, measure_singleton]
  have hblow : ∀ᵐ ξ : Rd d, Tendsto (fun R : ℝ => charFun ρ ((2 * π * R⁻¹) • ξ)) (𝓝[>] 0)
      (𝓝 (H ξ)) := by
    filter_upwards [ae_of_ae_normSphere hd1 hD, hne0] with ξ hξD hξ0
    set u := ‖ξ‖⁻¹ • ξ with hu
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ0
    have hun : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hr : Tendsto (fun R : ℝ => 2 * π * R⁻¹ * ‖ξ‖) (𝓝[>] 0) atTop :=
      (tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)).atTop_mul_const hn
    have hω : ∀ R : ℝ, (2 * π * R⁻¹) • ξ = (2 * π * R⁻¹ * ‖ξ‖) • u := fun R => by
      rw [hu, smul_smul]
      congr 1
      field_simp
    have hcoc : Tendsto (fun R : ℝ => (2 * π * R⁻¹ * ‖ξ‖) • u) (𝓝[>] 0) (cocompact (Rd d)) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      refine hr.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
      rw [norm_smul, hun, mul_one, Real.norm_of_nonneg (by positivity)]
    have h1 := hray.comp hcoc
    have h2 := (hξD hξ0).comp hr
    have hexp : Tendsto (fun R : ℝ => -(levyExp (L (t • (1 : Mat d))) ((2 * π * R⁻¹) • ξ) -
        levyExp (L S) ((2 * π * R⁻¹) • ξ))) (𝓝[>] 0) (𝓝 (-(c / 2 * Real.log t) + Δ u)) := by
      have := (h1.sub h2).neg
      refine (this.congr fun R => ?_).trans (by rw [neg_sub', sub_neg_eq_add, add_comm])
      simp only [Function.comp_apply, hω]
      ring
    simp_rw [hρcf]
    exact (Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp hexp)
  /- Measurability and the bound of `H`, through the sequence `R = 1/(n+1)`. -/
  have hseqR : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity⟩
    exact tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by simp
  have hseq : ∀ᵐ ξ : Rd d, Tendsto (fun n : ℕ => charFun ρ ((2 * π * ((n : ℝ) + 1)⁻¹⁻¹) • ξ))
      atTop (𝓝 (H ξ)) := by
    filter_upwards [hblow] with ξ hξ
    exact hξ.comp hseqR
  have hHm : AEStronglyMeasurable H volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n =>
      (continuous_charFun.comp (continuous_const_smul _)).aestronglyMeasurable) hseq
  have hHb : ∀ᵐ ξ : Rd d, ‖H ξ‖ ≤ 1 := by
    filter_upwards [hseq] with ξ hξ
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hξ) fun n => norm_charFun_le_one _
  set p : ℂ := (((ρ {0}).toReal : ℝ) : ℂ) with hp
  /- `∫ g (H - ρ{0}) = 0` for every smooth compactly supported real `g`. -/
  have hzero : ∀ g : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      ∫ ξ, g ξ • (H ξ - p) = 0 := by
    intro g hg hgc
    set gS := testSchwartz g hg hgc with hgS
    set φ : SchwartzMap (Rd d) ℂ := 𝓕⁻ gS with hφ
    have hFφ : 𝓕 φ = gS := FourierTransform.fourier_fourierInv_eq gS
    have hgSi : Integrable (fun ξ => gS ξ) := gS.integrable
    have hgSH : Integrable (fun ξ => gS ξ * H ξ) := hgSi.mul_bdd hHm hHb
    /- `φ(0) = ∫ g`. -/
    have hφ0 : φ 0 = ∫ ξ, gS ξ := by
      rw [hφ, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      simp
    /- The two limits. -/
    have hL := tendsto_integral_schwartz_dilate φ ρ
    have hR : Tendsto (fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ) (𝓝[>] 0) (𝓝 (∫ ξ, gS ξ * H ξ)) := by
      have hdom := tendsto_integral_filter_of_dominated_convergence (μ := volume)
        (l := 𝓝[>] (0 : ℝ)) (F := fun (R : ℝ) ξ => gS ξ * charFun ρ ((2 * π * R⁻¹) • ξ))
        (f := fun ξ => gS ξ * H ξ) (fun ξ => ‖gS ξ‖)
        (Eventually.of_forall fun R => (gS.continuous.mul
          (continuous_charFun.comp (continuous_const_smul _))).aestronglyMeasurable)
        (Eventually.of_forall fun R => Eventually.of_forall fun ξ => by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (norm_charFun_le_one _))
        hgSi.norm (by
          filter_upwards [hblow] with ξ hξ
          exact hξ.const_mul _)
      refine hdom.congr fun R => ?_
      rw [integral_schwartz_dilate_eq_fourier, hFφ]
    have heq := tendsto_nhds_unique hL hR
    simp_rw [Complex.real_smul]
    have hgc : ∀ ξ, ((g ξ : ℝ) : ℂ) = gS ξ := fun ξ => rfl
    simp_rw [hgc, mul_sub]
    rw [integral_sub hgSH (hgSi.mul_const p), integral_mul_const, ← hφ0, heq]
    ring
  have hloc : LocallyIntegrable (fun ξ => H ξ - p) volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded (M := 1 + ‖p‖) hk.measure_lt_top.ne
      (hHm.sub aestronglyMeasurable_const) ?_
    filter_upwards [ae_restrict_of_ae hHb] with ξ hξ
    exact (norm_sub_le _ _).trans (by linarith)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  /- `ρ{0} > 0`, and `Δ = log ρ{0} + (c/2) log t` at almost every direction. -/
  have hval : ∀ᵐ ξ : Rd d, ξ ≠ 0 →
      Δ (‖ξ‖⁻¹ • ξ) = Real.log (ρ {0}).toReal + c / 2 * Real.log t := by
    filter_upwards [hae] with ξ hξ _
    have h1 : Real.exp (-(c / 2 * Real.log t) + Δ (‖ξ‖⁻¹ • ξ)) = (ρ {0}).toReal := by
      exact Complex.ofReal_injective (sub_eq_zero.1 hξ)
    rw [← h1, Real.log_exp]
    ring
  exact ⟨_, ae_normSphere_of_ae hd1 hval⟩

end AffineHemigroup
