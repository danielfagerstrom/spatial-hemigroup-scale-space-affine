/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.DelayPolar

/-!
# `prop:origin-boundedness-subordinated`: the subordinated slice, the density at the origin

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:origin-boundedness-subordinated`
(`thm:origin-boundedness-d`(3)). Wave 2, group A (Q-0281).

* `c = 2k_I(0+)` by monotone convergence in `eq:polar-profile-d`, read through the substitution of
  `lem:delay-polar-profile` (`delayRadialL_eq`) and `∫ v^{d/2-1}e^{-v} dv = Γ(d/2)`;
* the datum's exponent is `F_I(|ξ|²/2)`: [B, Prop. 4.9(2)] restated, which is
  `lem:delay-polar-profile` for the causally admissible `F_I` (`exponentL_eq_causal`);
* `μ = ρ.bind g^{(d)}` by the uniqueness of the Fourier transform (`charFun_bind_gaussVar`), and
  `ρ{0} = 0` because `e^{-F_I(σ)} = |μ̂(√(2σ)e)| → 0` by `lem:origin-decay-exponent`;
* the density `p` and its limit at the origin by Tonelli and the Gaussian and Gamma integrals.

**Route.** The finiteness dichotomy of the limit (`c > d`) and the unboundedness of every
representative for `c ≤ d` are read from clauses (4)–(5) of the parent, proved for every datum
(`lintegral_charFun_eq_top`, `lintegral_charFun_pow_ne_top`, `origin_unbounded`), where the
blueprint redoes them on the slice through upper bounds on `F_I`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-- A causally admissible exponent's data form a delay datum ([B, Def. 4.11] with the monotone
profile). -/
noncomputable def causalDelayDatum (FI : ScaleSpace.CausalAdmissible) : DelayDatum :=
  ⟨FI.b₀, FI.k, FI.b₀_nonneg, FI.k_nonneg,
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi FI.k_antitone, FI.k_zero,
    FI.integrable_near_zero, FI.integrable_at_top⟩

theorem causalDelayDatum_exponentL (FI : ScaleSpace.CausalAdmissible) (σ : ℝ) :
    (causalDelayDatum FI).exponentL σ = FI.exponentL σ := rfl

/-- **[B, Prop. 4.9(2)], restated**: a datum whose profile is the polar profile of a delay datum
with the same drift has exponent `F_I(|ξ|²/2)`. -/
theorem OriginDatum.exponentL_eq_delay (hd : 1 ≤ d) (D : OriginDatum d) (DI : DelayDatum)
    (ha : D.a = DI.b₀) (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf DI.k d r) (ξ : Rd d) :
    D.exponentL ξ = DI.exponentL (‖ξ‖ ^ 2 / 2) := by
  rw [(delay_polar_profile hd DI).2.2.2.2 ξ, OriginDatum.exponentL, ha]
  congr 1
  rw [OriginDatum.levyMeasure, lintegral_withDensity_eq_lintegral_mul _ D.measurable_levyDensity
    (by fun_prop)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  by_cases hx : x = 0
  · subst hx; simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), mul_comm,
      ← ENNReal.ofReal_mul (by linarith [Real.cos_le_one ⟪ξ, x⟫]), hsub _ hn]

/-! ## `c = 2k_I(0+)` -/

/-- **`prop:origin-boundedness-subordinated`** (`thm:origin-boundedness-d`(3)), the profile at the
origin: for a datum subordinated to a causally admissible `F_I` with drift `0`, `c = 2k_I(0+)`. -/
theorem subordinated_profileAtOrigin (hd : 1 ≤ d) (D : OriginDatum d) (_ha : D.a = 0)
    (_hc : 0 < D.profileAtOrigin) (FI : ScaleSpace.CausalAdmissible) (_hFI : FI.b₀ = 0)
    (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r) :
    D.profileAtOrigin = 2 * ⨆ u : Ioi (0 : ℝ), ENNReal.ofReal (FI.k u) := by
  set DI := causalDelayDatum FI with hDI
  set a := (d : ℝ) / 2 with ha
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha0 : 0 < a := by rw [ha]; positivity
  have hA := (sphereArea_eq_toSphere hd).2
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  set S := ⨆ u : Ioi (0 : ℝ), ENNReal.ofReal (FI.k u) with hS
  set J : ℝ → ℝ≥0∞ := fun r => ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v) *
    FI.k (r ^ 2 / (2 * v))) with hJ
  -- `ofReal (k_d r) = (2/Γ(a)) J(r)` for `r > 0`
  have hkd : ∀ r : ℝ, 0 < r → ENNReal.ofReal (D.k r) = ENNReal.ofReal (2 / Real.Gamma a) * J r := by
    intro r hr
    have h1 := delayRadialL_eq_polarProfile hd DI hr
    have h2 := delayRadialL_eq (d := d) DI.k DI.k_nonneg hr
    rw [h1] at h2
    have h2' : ENNReal.ofReal (polarProfileOf FI.k d r / (sphereArea d * r ^ d))
        = ENNReal.ofReal (Real.pi ^ (-a) * r ^ (-(d : ℝ))) * J r := h2
    have hpos : 0 < sphereArea d * r ^ d := by positivity
    rw [hsub r hr]
    have hk0 : 0 ≤ polarProfileOf FI.k d r := polarProfileOf_nonneg DI hr
    calc ENNReal.ofReal (polarProfileOf FI.k d r)
        = ENNReal.ofReal (sphereArea d * r ^ d) *
            ENNReal.ofReal (polarProfileOf FI.k d r / (sphereArea d * r ^ d)) := by
          rw [← ENNReal.ofReal_mul hpos.le]; congr 1; field_simp
      _ = ENNReal.ofReal (sphereArea d * r ^ d) *
            (ENNReal.ofReal (Real.pi ^ (-a) * r ^ (-(d : ℝ))) * J r) := by
          rw [h2']
      _ = ENNReal.ofReal (2 / Real.Gamma a) * J r := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le]
          congr 2
          rw [sphereArea, ← ha, Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hr.le, Real.rpow_natCast]
          field_simp
  -- `J` is bounded by `Γ(a) S` and attains it in the limit `r ↓ 0`
  have hkS : ∀ u : ℝ, 0 < u → ENNReal.ofReal (FI.k u) ≤ S := fun u hu =>
    le_iSup (fun u : Ioi (0 : ℝ) => ENNReal.ofReal (FI.k u)) ⟨u, hu⟩
  have hGint : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v))
      = ENNReal.ofReal (Real.Gamma a) := by
    rw [Real.Gamma_eq_integral ha0, ofReal_integral_eq_lintegral_ofReal]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun v _ => by ring_nf
    · exact (Real.GammaIntegral_convergent ha0)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v (hv : 0 < v) =>
        mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hv.le _))
  have hJle : ∀ r : ℝ, 0 < r → J r ≤ ENNReal.ofReal (Real.Gamma a) * S := by
    intro r hr
    rw [← hGint, ← lintegral_mul_const _ (by fun_prop)]
    refine setLIntegral_mono' measurableSet_Ioi fun v (hv : 0 < v) => ?_
    have hu : 0 < r ^ 2 / (2 * v) := by positivity
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl (hkS _ hu)
  -- the limit along `r = 1/(n+1)`
  have hlimk : Tendsto (fun u : ℝ => ENNReal.ofReal (FI.k u)) (𝓝[>] 0) (𝓝 S) := by
    have hA' : AntitoneOn (fun u : ℝ => ENNReal.ofReal (FI.k u)) (Ioi 0) := fun x hx y hy hxy =>
      ENNReal.ofReal_le_ofReal (FI.k_antitone hx hy hxy)
    have h := hA'.tendsto_nhdsGT (OrderTop.bddAbove _)
    rwa [show sSup ((fun u : ℝ => ENNReal.ofReal (FI.k u)) '' Ioi 0) = S by rw [hS, sSup_image']]
      at h
  have hge : ENNReal.ofReal (Real.Gamma a) * S ≤ ⨆ r : Ioi (0 : ℝ), J r := by
    set rn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hrn
    have hrn0 : ∀ n, 0 < rn n := fun n => by positivity
    have hkm : AEMeasurable FI.k (volume.restrict (Ioi 0)) :=
      aemeasurable_restrict_of_antitoneOn measurableSet_Ioi FI.k_antitone
    have hfm : ∀ n, AEMeasurable (fun v : ℝ => ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v) *
        FI.k (rn n ^ 2 / (2 * v)))) (volume.restrict (Ioi 0)) := by
      intro n
      have hc : 0 < rn n ^ 2 / 2 := by have := hrn0 n; positivity
      have hk' := hkm.comp_quasiMeasurePreserving (quasiMeasurePreserving_div_Ioi hc)
      refine (((by fun_prop : Measurable fun v : ℝ => v ^ (a - 1) * Real.exp (-v)).aemeasurable.mul
        hk').ennreal_ofReal).congr (ae_of_all _ fun v => ?_)
      simp only [Function.comp_apply, div_div]
    have hmono : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), Monotone fun n =>
        ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v) * FI.k (rn n ^ 2 / (2 * v))) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v (hv : 0 < v) => ?_)
      intro m n hmn
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      refine FI.k_antitone (show (0 : ℝ) < rn n ^ 2 / (2 * v) by have := hrn0 n; positivity)
        (show (0 : ℝ) < rn m ^ 2 / (2 * v) by have := hrn0 m; positivity) ?_
      have h1 : rn n ≤ rn m := by
        simp only [hrn]; gcongr
      have h2 : rn n ^ 2 ≤ rn m ^ 2 := pow_le_pow_left₀ (hrn0 n).le h1 2
      gcongr
    have htend : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun n =>
        ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v) * FI.k (rn n ^ 2 / (2 * v)))) atTop
        (𝓝 (ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v)) * S)) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v (hv : 0 < v) => ?_)
      have hu : Tendsto (fun n => rn n ^ 2 / (2 * v)) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
          (.of_forall fun n => show (0 : ℝ) < rn n ^ 2 / (2 * v) by have := hrn0 n; positivity)
        have h0 : Tendsto rn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
        have := (h0.pow 2).div_const (2 * v)
        simpa using this
      have hk := hlimk.comp hu
      have h := ENNReal.Tendsto.const_mul hk (Or.inr (ENNReal.ofReal_ne_top
        (r := v ^ (a - 1) * Real.exp (-v))))
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      exact (ENNReal.ofReal_mul (by positivity)).symm
    have hlim := lintegral_tendsto_of_tendsto_of_monotone hfm hmono htend
    have hval : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ (a - 1) * Real.exp (-v)) * S
        = ENNReal.ofReal (Real.Gamma a) * S := by
      rw [lintegral_mul_const _ (by fun_prop), hGint]
    rw [hval] at hlim
    refine le_of_tendsto' hlim fun n => ?_
    exact le_iSup (fun r : Ioi (0 : ℝ) => J r) ⟨rn n, hrn0 n⟩
  have hsup : ⨆ r : Ioi (0 : ℝ), J r = ENNReal.ofReal (Real.Gamma a) * S :=
    le_antisymm (iSup_le fun r => hJle r r.2) hge
  calc D.profileAtOrigin = ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (2 / Real.Gamma a) * J r := by
        rw [OriginDatum.profileAtOrigin]
        exact iSup_congr fun r => hkd r r.2
    _ = ENNReal.ofReal (2 / Real.Gamma a) * (ENNReal.ofReal (Real.Gamma a) * S) := by
        rw [← ENNReal.mul_iSup, hsup]
    _ = 2 * S := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hG.ne']
        simp

/-! ## The law as a Gaussian variance mixture -/

/-- The law's transform through the delay exponent: `μ̂(ξ) = e^{-F_I(|ξ|²/2)}`. -/
theorem IsLawOf.charFun_eq_causal (hd : 1 ≤ d) {D : OriginDatum d} {μ : Measure (Rd d)}
    (hμ : IsLawOf D μ) (FI : ScaleSpace.CausalAdmissible) (ha : D.a = FI.b₀)
    (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r) (ξ : Rd d) :
    charFun μ ξ = ((Real.exp (-FI.exponent (‖ξ‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [hμ.2 ξ, OriginDatum.exponent,
    D.exponentL_eq_delay hd (causalDelayDatum FI) ha hsub ξ, causalDelayDatum_exponentL]
  rfl

theorem ae_nonneg_of_Iio {ρ : Measure ℝ} (hρ0 : ρ (Iio 0) = 0) : ∀ᵐ u ∂ρ, 0 ≤ u := by
  rw [ae_iff]
  convert hρ0 using 2
  ext u; simp

/-- **The delay law has no atom at `0`**: `ρ{0} ≤ ∫ e^{-σu} ρ(du) = e^{-F_I(σ)} = |μ̂(√(2σ) e₁)|`,
which tends to `0` by `lem:origin-decay-exponent`. -/
theorem delayLaw_zero (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (FI : ScaleSpace.CausalAdmissible) (hFI : FI.b₀ = 0)
    (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ0 : ρ (Iio 0) = 0)
    (hlap : ∀ σ : ℝ, 0 ≤ σ → ∫ u, Real.exp (-(σ * u)) ∂ρ = Real.exp (-FI.exponent σ)) :
    ρ {0} = 0 := by
  obtain ⟨β, -, hβ0, hβc⟩ := ENNReal.lt_iff_exists_real_btwn.mp hc
  have hβ : 0 < β := ENNReal.ofReal_pos.mp hβ0
  obtain ⟨C, hC⟩ := origin_decay_exponent hd D ha hc μ hμ β hβc
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he
  have he1 : ‖e‖ = 1 := by simp [he, ebasis]
  have hae := ae_nonneg_of_Iio hρ0
  have hbound : ∀ σ : ℝ, 0 ≤ σ → ρ {0} ≤
      ENNReal.ofReal (C * (1 + Real.sqrt (2 * σ)) ^ (-β)) := by
    intro σ hσ
    have hint : Integrable (fun u : ℝ => Real.exp (-(σ * u))) ρ := by
      refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
      filter_upwards [hae] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    calc ρ {0} = ∫⁻ u, ({0} : Set ℝ).indicator 1 u ∂ρ := by
          rw [lintegral_indicator (measurableSet_singleton 0)]; simp
      _ ≤ ∫⁻ u, ENNReal.ofReal (Real.exp (-(σ * u))) ∂ρ := by
          refine lintegral_mono fun u => ?_
          by_cases hu : u = 0
          · subst hu; simp
          · rw [indicator_of_notMem (by simpa using hu)]; exact zero_le
      _ = ENNReal.ofReal (Real.exp (-FI.exponent σ)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => (Real.exp_pos _).le),
            hlap σ hσ]
      _ ≤ ENNReal.ofReal (C * (1 + Real.sqrt (2 * σ)) ^ (-β)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          set ξ := Real.sqrt (2 * σ) • e with hξ
          have hn : ‖ξ‖ = Real.sqrt (2 * σ) := by
            rw [hξ, norm_smul, he1, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
          have hsq : ‖ξ‖ ^ 2 / 2 = σ := by
            rw [hn, Real.sq_sqrt (by linarith)]; ring
          have h1 := hC ξ
          rw [hμ.charFun_eq_causal hd FI (by rw [ha, hFI]) hsub ξ, hsq, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, hn] at h1
          exact h1
  have htend : Tendsto (fun σ : ℝ => ENNReal.ofReal (C * (1 + Real.sqrt (2 * σ)) ^ (-β))) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rw [show (0 : ℝ) = C * 0 by ring]
    refine Tendsto.const_mul C ((tendsto_rpow_neg_atTop hβ).comp ?_)
    refine tendsto_atTop_add_const_left _ 1 ?_
    exact Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  exact le_antisymm (ge_of_tendsto htend (eventually_atTop.mpr ⟨0, hbound⟩)) (zero_le)

/-- `ρ` is carried by `(0,∞)`. -/
theorem restrict_Ioi_eq_self {ρ : Measure ℝ} (hρ0 : ρ (Iio 0) = 0) (hz : ρ {0} = 0) :
    ρ.restrict (Ioi 0) = ρ := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have : {a : ℝ | a ∉ Ioi 0} = Iio 0 ∪ {0} := by
    ext u; simp only [mem_setOf_eq, mem_Ioi, not_lt, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h | h; exacts [Or.inl h, Or.inr h]
    · rintro (h | h)
      · exact h.le
      · exact h.le
  rw [this]
  exact measure_union_null hρ0 hz

/-- **`prop:origin-boundedness-subordinated`** (`thm:origin-boundedness-d`(3)), the mixture: given a
probability measure `ρ` on `[0,∞)` with Laplace transform `e^{-F_I}` (the delay law; a hypothesis,
`% CHANGED Q-0281`), every law `μ` of the datum is the law of `√W Z`, `ρ.bind g^{(d)}`, and has the
radial density `p` of `eq:mixture-density`, nonincreasing in `|x|`. -/
theorem subordinated_law (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (FI : ScaleSpace.CausalAdmissible) (hFI : FI.b₀ = 0)
    (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ0 : ρ (Iio 0) = 0)
    (hlap : ∀ σ : ℝ, 0 ≤ σ → ∫ u, Real.exp (-(σ * u)) ∂ρ = Real.exp (-FI.exponent σ)) :
    μ = ρ.bind (gaussVar d) ∧ μ = volume.withDensity (mixtureDensity d ρ) ∧
      ∀ x y : Rd d, 0 < ‖x‖ → ‖x‖ ≤ ‖y‖ → mixtureDensity d ρ y ≤ mixtureDensity d ρ x := by
  haveI := hμ.1
  haveI := isProbabilityMeasure_bind_gaussVar (d := d) ρ
  have hz := delayLaw_zero hd D ha hc μ hμ FI hFI hsub ρ hρ0 hlap
  have hres := restrict_Ioi_eq_self hρ0 hz
  -- the transform
  have hbind : μ = ρ.bind (gaussVar d) := by
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [hμ.charFun_eq_causal hd FI (by rw [ha, hFI]) hsub ξ, charFun_bind_gaussVar ρ hρ0,
      ← hlap _ (by positivity)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    ring_nf
  -- the density
  have hdens : ρ.bind (gaussVar d) = volume.withDensity (mixtureDensity d ρ) := by
    refine Measure.ext fun B hB => ?_
    rw [Measure.bind_apply hB (measurable_gaussVar d).aemeasurable, withDensity_apply _ hB]
    have hjoint : Measurable (Function.uncurry fun (u : ℝ) (x : Rd d) =>
        ENNReal.ofReal (heatKernel d u x)) :=
      ((measurable_radialHeat_uncurry d).comp
        (measurable_fst.prodMk (continuous_norm.measurable.comp measurable_snd))).ennreal_ofReal
    calc ∫⁻ u, gaussVar d u B ∂ρ = ∫⁻ u in Ioi (0 : ℝ), gaussVar d u B ∂ρ := by rw [hres]
      _ = ∫⁻ u in Ioi (0 : ℝ), (∫⁻ x in B, ENNReal.ofReal (heatKernel d u x)) ∂ρ := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
          rw [gaussVar_eq_withDensity hu, withDensity_apply _ hB]
      _ = ∫⁻ x in B, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (heatKernel d u x) ∂ρ :=
          lintegral_lintegral_swap hjoint.aemeasurable
      _ = ∫⁻ x in B, mixtureDensity d ρ x := rfl
  refine ⟨hbind, hbind.trans hdens, fun x y hx hxy => ?_⟩
  refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 0 < u) => ENNReal.ofReal_le_ofReal ?_
  unfold heatKernel
  have : 0 < 2 * Real.pi * u := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h2 : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-! ## The density at the origin -/

/-- `p₀ = ∫ (2πu)^{-d/2} ρ(du)` written as the limit of `p` at the origin (monotone convergence). -/
theorem tendsto_mixtureDensity (ρ : Measure ℝ) :
    Tendsto (mixtureDensity d ρ) (𝓝[≠] 0)
      (𝓝 (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((2 * Real.pi * u) ^ (-(d : ℝ) / 2)) ∂ρ)) := by
  set P : ℝ → ℝ≥0∞ := fun r => ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (radialHeat d u r) ∂ρ with hP
  have hP0 : P 0 = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((2 * Real.pi * u) ^ (-(d : ℝ) / 2)) ∂ρ := by
    simp [hP, radialHeat]
  have hanti : AntitoneOn P (Ici 0) := by
    intro r hr s hs hrs
    refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 0 < u) => ENNReal.ofReal_le_ofReal ?_
    unfold radialHeat
    have : 0 < 2 * Real.pi * u := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr hrs 2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  -- `P(r) → P(0)` as `r ↓ 0`
  have hlim : Tendsto P (𝓝[>] 0) (𝓝 (P 0)) := by
    have h := (hanti.mono Ioi_subset_Ici_self).tendsto_nhdsGT (OrderTop.bddAbove _)
    have heq : sSup (P '' Ioi 0) = P 0 := by
      refine le_antisymm (sSup_le ?_) ?_
      · rintro _ ⟨r, hr, rfl⟩
        exact hanti self_mem_Ici (mem_Ici.mpr (le_of_lt hr)) (le_of_lt hr)
      · -- monotone convergence along `r = 1/(n+1)`
        set rn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hrn
        have hrn0 : ∀ n, 0 < rn n := fun n => by positivity
        have hm : ∀ n, AEMeasurable (fun u : ℝ => ENNReal.ofReal (radialHeat d u (rn n)))
            (ρ.restrict (Ioi 0)) := fun n =>
          ((measurable_radialHeat_uncurry d).comp
            (measurable_id.prodMk measurable_const)).ennreal_ofReal.aemeasurable
        have hmono : ∀ᵐ u ∂(ρ.restrict (Ioi 0)), Monotone fun n =>
            ENNReal.ofReal (radialHeat d u (rn n)) := by
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
          intro m n hmn
          refine ENNReal.ofReal_le_ofReal ?_
          unfold radialHeat
          have : 0 < 2 * Real.pi * u := by positivity
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have h1 : rn n ≤ rn m := by simp only [hrn]; gcongr
          have h2 : rn n ^ 2 ≤ rn m ^ 2 := pow_le_pow_left₀ (hrn0 n).le h1 2
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_right h2 (by positivity)
        have htend : ∀ᵐ u ∂(ρ.restrict (Ioi 0)), Tendsto (fun n =>
            ENNReal.ofReal (radialHeat d u (rn n))) atTop (𝓝 (ENNReal.ofReal (radialHeat d u 0))) := by
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
          refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
          have hc : Continuous fun r : ℝ => radialHeat d u r := by unfold radialHeat; fun_prop
          exact (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        have hl := lintegral_tendsto_of_tendsto_of_monotone hm hmono htend
        refine le_of_tendsto' hl fun n => le_sSup ⟨rn n, hrn0 n, rfl⟩
    rwa [heq] at h
  have hnorm : Tendsto (fun x : Rd d => ‖x‖) (𝓝[≠] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 := (continuous_norm (E := Rd d)).tendsto 0
      rw [norm_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact norm_pos_iff.mpr hx
  rw [← hP0]
  exact hlim.comp hnorm

/-- **`prop:origin-boundedness-subordinated`** (`thm:origin-boundedness-d`(3)), the value at the
origin: `p(x) → (2π)^{-d} ∫ μ̂ = (2π)^{-d/2} Γ(d/2)⁻¹ ∫₀^∞ σ^{d/2-1} e^{-F_I(σ)} dσ` as `x → 0`,
finite exactly when `c > d`. -/
theorem subordinated_density_limit (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (FI : ScaleSpace.CausalAdmissible) (hFI : FI.b₀ = 0)
    (hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ0 : ρ (Iio 0) = 0)
    (hlap : ∀ σ : ℝ, 0 ≤ σ → ∫ u, Real.exp (-(σ * u)) ∂ρ = Real.exp (-FI.exponent σ)) :
    Tendsto (mixtureDensity d ρ) (𝓝[≠] 0)
        (𝓝 (ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
          ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re)) ∧
      ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re
        = ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
          ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ ((d : ℝ) / 2 - 1) * Real.exp (-FI.exponent σ)) ∧
      (ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re ≠ ⊤ ↔
        (d : ℝ≥0∞) < D.profileAtOrigin) := by
  haveI := hμ.1
  have hz := delayLaw_zero hd D ha hc μ hμ FI hFI hsub ρ hρ0 hlap
  have hres := restrict_Ioi_eq_self hρ0 hz
  have hae := ae_nonneg_of_Iio hρ0
  set a := (d : ℝ) / 2 with ha2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha0 : 0 < a := by rw [ha2]; positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  set p₀ := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((2 * Real.pi * u) ^ (-(d : ℝ) / 2)) ∂ρ with hp₀
  -- the Laplace transform as a lower integral
  have hlapL : ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (Real.exp (-FI.exponent σ))
      = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(σ * u))) ∂ρ := by
    intro σ hσ
    have hint : Integrable (fun u : ℝ => Real.exp (-(σ * u))) ρ := by
      refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
      filter_upwards [hae] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    rw [← hlap σ hσ, ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun u => (Real.exp_pos _).le), hres]
  -- `(2π)^{-d} ∫ μ̂ = p₀`
  have hI : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re
      = p₀ := by
    have hre : ∀ ξ : Rd d, ENNReal.ofReal (charFun μ ξ).re
        = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(u / 2) * ‖ξ‖ ^ 2)) ∂ρ := by
      intro ξ
      rw [hμ.charFun_eq_causal hd FI (by rw [ha, hFI]) hsub ξ, Complex.ofReal_re,
        hlapL _ (by positivity)]
      refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => by ring_nf
    simp_rw [hre]
    have hjoint : Measurable (Function.uncurry fun (ξ : Rd d) (u : ℝ) =>
        ENNReal.ofReal (Real.exp (-(u / 2) * ‖ξ‖ ^ 2))) := by
      unfold Function.uncurry; fun_prop
    rw [lintegral_lintegral_swap hjoint.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_rexp_neg_mul_sq_norm_Rd d (half_pos hu))
      (ae_of_all _ fun ξ => (Real.exp_pos _).le),
      GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos hu), finrank_Rd,
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hpi _).le]
    congr 1
    rw [show Real.pi / (u / 2) = 2 * Real.pi / u by field_simp, Real.div_rpow hpi.le hu.le,
      Real.mul_rpow hpi.le hu.le, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
      Real.rpow_neg hpi.le, Real.rpow_neg hpi.le, Real.rpow_neg hu.le]
    have h2 : (2 * Real.pi) ^ (d : ℝ) = (2 * Real.pi) ^ ((d : ℝ) / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_add hpi]; ring_nf
    rw [h2]
    have : 0 < (2 * Real.pi) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hpi _
    have : 0 < u ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hu _
    field_simp
  -- `= (2π)^{-d/2} Γ(d/2)⁻¹ ∫ σ^{d/2-1} e^{-F_I(σ)} dσ`
  have hII : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.Gamma a) *
      ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (a - 1) * Real.exp (-FI.exponent σ)) = p₀ := by
    have hσ : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal (σ ^ (a - 1) * Real.exp (-FI.exponent σ))
        = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (a - 1) * Real.exp (-(σ * u))) ∂ρ := by
      intro σ hσ
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _), hlapL σ hσ.le,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun u => ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hσ]
    have hjoint : Measurable (Function.uncurry fun (σ : ℝ) (u : ℝ) =>
        ENNReal.ofReal (σ ^ (a - 1) * Real.exp (-(σ * u)))) := by
      unfold Function.uncurry; fun_prop
    rw [lintegral_lintegral_swap hjoint.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    have hq : (-1 : ℝ) < a - 1 := by linarith
    have hint := integrableOn_rpow_mul_exp_neg_mul_rpow hq le_rfl hu
    have hval := integral_rpow_mul_exp_neg_mul_rpow one_pos hq hu
    have hcongr : ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (a - 1) * Real.exp (-(σ * u)))
        = ENNReal.ofReal (∫ σ in Ioi (0 : ℝ), σ ^ (a - 1) * Real.exp (-u * σ ^ (1 : ℝ))) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun σ (hσ : 0 < σ) => by positivity))]
      refine setLIntegral_congr_fun measurableSet_Ioi fun σ _ => ?_
      rw [Real.rpow_one]; ring_nf
    rw [hcongr, hval, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show a - 1 + 1 = a by ring, Real.mul_rpow hpi.le hu.le,
      show -(d : ℝ) / 2 = -a by rw [ha2]; ring]
    simp only [div_one]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hI]; exact tendsto_mixtureDensity ρ
  · rw [hI, ← hII]
  · have hc0 : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hpi _
    have key : ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) * ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re
        ≠ ⊤ ↔ ∫⁻ ξ, ENNReal.ofReal (charFun μ ξ).re ≠ ⊤ :=
      ⟨fun h hI => h (by rw [hI, ENNReal.mul_top hc0]),
        fun h => ENNReal.mul_ne_top ENNReal.ofReal_ne_top h⟩
    rw [key]
    constructor
    · intro hfin
      by_contra hcd
      push Not at hcd
      exact hfin (lintegral_charFun_eq_top hd D ha μ hμ hcd)
    · intro hcd
      have h := lintegral_charFun_pow_ne_top hd D ha hc μ hμ 0 (by simpa using hcd)
      refine ne_top_of_le_ne_top h (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_)
      simpa using Complex.re_le_norm (charFun μ ξ)

/-- **`prop:origin-boundedness-subordinated`** (`thm:origin-boundedness-d`(3)), the last sentence:
if `c ≤ d`, no representative of `μ`'s density is bounded near the origin. -/
theorem subordinated_unbounded (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (_FI : ScaleSpace.CausalAdmissible) (_hFI : _FI.b₀ = 0)
    (_hsub : ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf _FI.k d r)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (_hρ0 : ρ (Iio 0) = 0)
    (_hlap : ∀ σ : ℝ, 0 ≤ σ → ∫ u, Real.exp (-(σ * u)) ∂ρ = Real.exp (-_FI.exponent σ))
    (hcd : D.profileAtOrigin ≤ d) :
    ∀ q : Rd d → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
      ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ x : Rd d, 0 < ‖x‖ ∧ ‖x‖ < δ ∧ M < q x :=
  (origin_unbounded hd D ha hc μ hμ hcd).2.2

end AffineHemigroup
