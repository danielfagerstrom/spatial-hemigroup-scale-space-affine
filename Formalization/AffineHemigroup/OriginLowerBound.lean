/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces
import AffineHemigroup.Polar
import AffineHemigroup.OriginExponent
import AffineHemigroup.OriginBoundedness
import AffineHemigroup.PolarReading
import AffineHemigroup.GaussMixture
import AffineHemigroup.DelayPolar
import AffineHemigroup.MaternLaw
import AffineHemigroup.RadialTransform

/-!
# `prop:origin-lower-bound-d`: a pointwise lower bound at the origin

Blueprint: `prop:origin-lower-bound-d` (`blueprint/src/parts/03-isotropic.tex`). Wave 2, group B
(Q-0281). Spends ledger A3(iii) (`levy_khintchine_converse`), for the law of the truncated datum,
and nothing else.

## The route

At one scale `ε ≤ ε₀` the law splits as `μ = μ₁ ∗ π` (`OriginDatum.law_eq_conv`, by the uniqueness
of the transform): `μ₁` is a law of the datum truncated at `τε` (A3(iii)), `π` the compound Poisson
law (`cpLaw`) of all the jumps of size `≥ τε` (`OriginDatum.bigJumps`). The blueprint splits these
into two compound Poisson laws, of the jumps in `[τε, ε)` and `≥ ε`; one law of their sum carries
the same two facts, `π ≥ (e^{-m}/2) L ∗ L` and `e^{-m} ≥ (τε)^c e^{-C_k}`, with a single mass `m`.

* **The twofold convolution fills a ball** (`OriginDatum.bigJumps_conv_ge`): on the shell
  `{ε/2 ≤ |x| < ε}` the big jumps dominate `a = c/(2|S^{d-1}|ε^d)` times Lebesgue measure, and by
  Tonelli and the shear `(x, y) ↦ (x + y, x)` the convolution of that with itself charges `G` with
  at least `a²|B(ε/8)| |G|`, through the ball `B(y₀, ε/8)` between the two shells
  (`exists_ball_in_shells`, which takes `d ≥ 2` for a unit vector orthogonal to `z`).
* **The small jumps move little** (`OriginDatum.truncate_law_tail`): the blueprint's coordinate
  truncation inequality is replaced by a Gaussian average, the identity
  `∫ (1 - e^{-|x|²/2ε²}) dμ₁ = ∫ (1 - μ̂₁) dg^{(d)}_{ε^{-2}}` (`integral_re_charFun_gaussVar`) and
  the Gaussian's second moment, which give `(1 - e^{-1/2}) μ₁(|x| ≥ ε) ≤ cτ²d/4 ≤ 3/32`, so
  `μ₁(|x| ≥ ε) ≤ 1/2` with the node's `τ`.
* **One scale and all scales** (`OriginDatum.one_scale`, `OriginDatum.all_scales`) follow the
  blueprint, with the shells `ε_n/4 < |x| ≤ ε_n/2` (closed at the top) located by
  `exists_nat_pow_near`.
* **The consequences**: clause (1) through the Lebesgue decomposition and
  `ae_le_of_forall_setLIntegral_le_of_sigmaFinite`; clause (2) by polar coordinates
  (`lintegral_radial`) and `∫_0^r t^{c-1} dt = r^c/c`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric Complex
open ScaleSpace (convPow isFiniteMeasure_convPow_Rd)
open scoped ENNReal Topology RealInnerProductSpace Nat

variable {d : ℕ}

/-! ## Compound Poisson laws on `ℝ^d` -/

/-- **The compound Poisson law** `π_L = e^{-L(ℝ^d)} ∑ₙ L^{*n}/n!` of a finite measure `L` on
`ℝ^d`. -/
noncomputable def cpLaw (L : Measure (Rd d)) : Measure (Rd d) :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-(L univ).toReal) / (n ! : ℝ)) • convPow L n

theorem convPow_univ (L : Measure (Rd d)) [IsFiniteMeasure L] (n : ℕ) :
    convPow L n univ = L univ ^ n := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    haveI := isFiniteMeasure_convPow_Rd L n
    rw [convPow, Measure.conv, Measure.map_apply measurable_add MeasurableSet.univ, preimage_univ,
      ← univ_prod_univ, Measure.prod_prod, ih, pow_succ]

theorem cpLaw_univ (L : Measure (Rd d)) [IsFiniteMeasure L] : cpLaw L univ = 1 := by
  set m := (L univ).toReal with hm
  have hL : L univ = ENNReal.ofReal m := (ENNReal.ofReal_toReal (measure_ne_top L univ)).symm
  rw [cpLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, convPow_univ, smul_eq_mul, hL]
  rw [tsum_poisson_mul_pow _ ENNReal.toReal_nonneg, ← Real.exp_add,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← hm, neg_add_cancel, Real.exp_zero,
    ENNReal.ofReal_one]

instance isProbabilityMeasure_cpLaw (L : Measure (Rd d)) [IsFiniteMeasure L] :
    IsProbabilityMeasure (cpLaw L) := ⟨cpLaw_univ L⟩

theorem charFun_convPow (L : Measure (Rd d)) [IsFiniteMeasure L] (n : ℕ) (ξ : Rd d) :
    charFun (convPow L n) ξ = charFun L ξ ^ n := by
  induction n with
  | zero => simp [convPow, charFun_dirac]
  | succ n ih =>
    haveI := isFiniteMeasure_convPow_Rd L n
    rw [convPow, charFun_conv, ih, pow_succ]

/-- **The transform of a compound Poisson law**: `π̂_L(ξ) = e^{-L(ℝ^d)} exp(L̂(ξ))`. -/
theorem charFun_cpLaw (L : Measure (Rd d)) [IsFiniteMeasure L] (ξ : Rd d) :
    charFun (cpLaw L) ξ = ((Real.exp (-(L univ).toReal) : ℝ) : ℂ) * Complex.exp (charFun L ξ) := by
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ξ⟫ * I)) (cpLaw L) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, cpLaw, integral_sum_measure hint]
  have hterm : ∀ n : ℕ, ∫ x, Complex.exp (⟪x, ξ⟫ * I) ∂(ENNReal.ofReal
      (Real.exp (-(L univ).toReal) / (n ! : ℝ)) • convPow L n)
      = ((Real.exp (-(L univ).toReal) : ℝ) : ℂ) * (charFun L ξ ^ n / (n ! : ℂ)) := by
    intro n
    rw [integral_smul_measure, ← charFun_apply, charFun_convPow,
      ENNReal.toReal_ofReal (by positivity)]
    rw [Complex.real_smul]
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-- A symmetric finite measure has a real transform: `L̂(ξ) = ∫ cos⟨x,ξ⟩ L(dx)`. -/
theorem charFun_of_symm (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hsym : L.map (fun x => -x) = L) (ξ : Rd d) :
    charFun L ξ = ((∫ x, Real.cos ⟪x, ξ⟫ ∂L : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (charFun L ξ) = charFun L ξ := by
    rw [← charFun_neg, charFun_apply, charFun_apply]
    conv_rhs => rw [← hsym]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [inner_neg_left, inner_neg_right]
  have him : (charFun L ξ).im = 0 := by
    have := congrArg Complex.im hconj
    simp at this
    linarith
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ξ⟫ * I)) L :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  apply Complex.ext
  · rw [Complex.ofReal_re, charFun_apply, ← RCLike.re_to_complex, ← integral_re hint]
    simp [Complex.exp_ofReal_mul_I_re]
  · rw [him, Complex.ofReal_im]

/-! ## The decomposition at one scale -/

/-- **The truncated datum** `(0, k_d 1_{(0,b)})`: the jumps of size below `b`. -/
noncomputable def OriginDatum.truncate (D : OriginDatum d) (b : ℝ) : OriginDatum d where
  a := 0
  k := fun r => if r < b then D.k r else 0
  a_nonneg := le_rfl
  k_nonneg := fun r hr => by
    by_cases h : r < b
    · simp only [h, if_true]; exact D.k_nonneg r hr
    · simp only [h, if_false, le_refl]
  k_antitone := by
    intro r hr s hs hrs
    by_cases hsb : s < b
    · have hrb : r < b := lt_of_le_of_lt hrs hsb
      simp only [hsb, hrb, if_true]
      exact D.k_antitone hr hs hrs
    · simp only [hsb, if_false]
      by_cases hrb : r < b
      · simp only [hrb, if_true]; exact D.k_nonneg r hr
      · simp only [hrb, if_false, le_refl]
  integrable_near_zero := by
    refine ne_top_of_le_ne_top D.integrable_near_zero (setLIntegral_mono' measurableSet_Ioo
      fun r hr => ENNReal.ofReal_le_ofReal ?_)
    by_cases h : r < b
    · simp only [h, if_true, le_refl]
    · simp only [h, if_false, zero_mul]; exact mul_nonneg (D.k_nonneg r hr.1) hr.1.le
  integrable_at_top := by
    refine ne_top_of_le_ne_top D.integrable_at_top (setLIntegral_mono' measurableSet_Ioi
      fun r (hr : 1 < r) => ENNReal.ofReal_le_ofReal ?_)
    by_cases h : r < b
    · simp only [h, if_true, le_refl]
    · simp only [h, if_false, zero_div]
      exact div_nonneg (D.k_nonneg r (lt_trans one_pos hr)) (by linarith)

/-- The truncated datum's Lévy measure is the restriction of `ν_d` to `{|x| < b}`. -/
theorem OriginDatum.levyMeasure_truncate (D : OriginDatum d) (b : ℝ) :
    (D.truncate b).levyMeasure = D.levyMeasure.restrict {x | ‖x‖ < b} := by
  have hS : MeasurableSet {x : Rd d | ‖x‖ < b} := measurableSet_lt continuous_norm.measurable
    measurable_const
  rw [OriginDatum.levyMeasure, OriginDatum.levyMeasure, restrict_withDensity hS,
    ← withDensity_indicator hS]
  congr 1
  funext x
  by_cases h0 : x = 0
  · subst h0; simp [Set.indicator_apply]
  · have h0' : x ∈ ({0}ᶜ : Set (Rd d)) := h0
    by_cases hx : ‖x‖ < b
    · rw [indicator_of_mem (show x ∈ {x : Rd d | ‖x‖ < b} from hx), indicator_of_mem h0',
        indicator_of_mem h0']
      simp only [OriginDatum.truncate, hx, if_true]
    · rw [indicator_of_notMem (show x ∉ {x : Rd d | ‖x‖ < b} from hx), indicator_of_mem h0']
      simp [OriginDatum.truncate, hx]

/-- **The big jumps** `ν_d` restricted to `{|x| ≥ b}`. -/
noncomputable def OriginDatum.bigJumps (D : OriginDatum d) (b : ℝ) : Measure (Rd d) :=
  D.levyMeasure.restrict {x | ‖x‖ < b}ᶜ

/-- **The mass of the big jumps** through `eq:polar-decomposition`:
`ν_d(|x| ≥ b) = ∫_b^∞ k_d(r) dr/r` for `b > 0`. -/
theorem OriginDatum.bigJumps_univ (hd : 1 ≤ d) (D : OriginDatum d) {b : ℝ} (hb : 0 < b) :
    D.bigJumps b univ = ∫⁻ r in Ici b, ENNReal.ofReal (D.k r / r) := by
  have hA := sphereArea_eq_toSphere hd
  have hS : MeasurableSet ({x : Rd d | ‖x‖ < b}ᶜ) :=
    (measurableSet_lt continuous_norm.measurable measurable_const).compl
  rw [OriginDatum.bigJumps, Measure.restrict_apply_univ, ← lintegral_indicator_one hS,
    D.polar_decomposition hd _ (measurable_one.indicator hS) (by simp [hb])]
  have hinner : ∀ η : sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      ({x : Rd d | ‖x‖ < b}ᶜ).indicator 1 (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)
      = ∫⁻ r in Ici b, ENNReal.ofReal (D.k r / r) := by
    intro η
    rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
      have hn : ‖r • (η : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr.le]
      by_cases hrb : b ≤ r
      · rw [indicator_of_mem (show r ∈ Ici b from hrb), indicator_of_mem
          (show r • (η : Rd d) ∈ ({x : Rd d | ‖x‖ < b}ᶜ) by simp [hn, hrb]), Pi.one_apply, one_mul]
      · rw [indicator_of_notMem (show r ∉ Ici b from hrb), indicator_of_notMem
          (show r • (η : Rd d) ∉ ({x : Rd d | ‖x‖ < b}ᶜ) by simp [hn]; linarith), zero_mul]
    · rw [indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
        indicator_of_notMem (show r ∉ Ici b from fun h => hr (lt_of_lt_of_le hb h))]
  simp_rw [hinner]
  rw [lintegral_const, ← hA.1, mul_left_comm, ENNReal.inv_mul_cancel (by simp [hA.2])
    ENNReal.ofReal_ne_top, mul_one]

/-- `k_d ≤ c` on `(0,∞)`, in `ℝ`, for a finite `c`. -/
theorem OriginDatum.k_le_profile (D : OriginDatum d) (hctop : D.profileAtOrigin ≠ ⊤) {r : ℝ}
    (hr : 0 < r) : D.k r ≤ D.profileAtOrigin.toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hctop).mp (D.ofReal_k_le hr)

/-- **The mass bound**: for `0 < b ≤ 1`, `ν_d(|x| ≥ b) ≤ c log(1/b) + C_k`. -/
theorem OriginDatum.bigJumps_univ_le (hd : 1 ≤ d) (D : OriginDatum d)
    (hctop : D.profileAtOrigin ≠ ⊤) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    D.bigJumps b univ ≤
      ENNReal.ofReal (D.profileAtOrigin.toReal * Real.log (1 / b) + D.tailConst) := by
  set c := D.profileAtOrigin.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hlog : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
  rw [D.bigJumps_univ hd hb]
  have hsplit : Ici b ⊆ Ioc b 1 ∪ Ici 1 ∪ {b} := by
    intro r hr
    rcases eq_or_lt_of_le (mem_Ici.mp hr) with h | h
    · exact Or.inr h.symm
    · by_cases h1 : r ≤ 1
      · exact Or.inl (Or.inl ⟨h, h1⟩)
      · exact Or.inl (Or.inr (le_of_lt (not_le.mp h1)))
  have h1 : ∫⁻ r in Ioc b 1, ENNReal.ofReal (D.k r / r)
      ≤ ENNReal.ofReal (c * Real.log (1 / b)) := by
    have hint : IntegrableOn (fun r : ℝ => c / r) (Ioc b 1) := by
      have : ContinuousOn (fun r : ℝ => c / r) (Icc b 1) :=
        continuousOn_const.div continuousOn_id fun r hr => (lt_of_lt_of_le hb hr.1).ne'
      exact (this.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    calc ∫⁻ r in Ioc b 1, ENNReal.ofReal (D.k r / r)
        ≤ ∫⁻ r in Ioc b 1, ENNReal.ofReal (c / r) := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ENNReal.ofReal_le_ofReal ?_
          have hr0 : 0 < r := lt_trans hb hr.1
          exact div_le_div_of_nonneg_right (D.k_le_profile hctop hr0) hr0.le
      _ = ENNReal.ofReal (∫ r in Ioc b 1, c / r) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun r hr => div_nonneg hc0 (lt_trans hb hr.1).le))]
      _ = ENNReal.ofReal (c * Real.log (1 / b)) := by
          rw [← intervalIntegral.integral_of_le hb1]
          simp_rw [div_eq_mul_inv]
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hb one_pos, one_div, one_mul]
  have h2 : ∫⁻ r in Ici 1, ENNReal.ofReal (D.k r / r) = ENNReal.ofReal D.tailConst := by
    rw [OriginDatum.tailConst, ENNReal.ofReal_toReal D.integrable_at_top]
    exact setLIntegral_congr Ioi_ae_eq_Ici.symm
  have h3 : ∫⁻ r in ({b} : Set ℝ), ENNReal.ofReal (D.k r / r) = 0 := by
    rw [Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]
  calc ∫⁻ r in Ici b, ENNReal.ofReal (D.k r / r)
      ≤ ∫⁻ r in Ioc b 1 ∪ Ici 1 ∪ {b}, ENNReal.ofReal (D.k r / r) := lintegral_mono_set hsplit
    _ ≤ (∫⁻ r in Ioc b 1, ENNReal.ofReal (D.k r / r)) + (∫⁻ r in Ici 1, ENNReal.ofReal (D.k r / r))
          + ∫⁻ r in ({b} : Set ℝ), ENNReal.ofReal (D.k r / r) :=
        (lintegral_union_le _ _ _).trans (add_le_add (lintegral_union_le _ _ _) le_rfl)
    _ ≤ ENNReal.ofReal (c * Real.log (1 / b)) + ENNReal.ofReal D.tailConst := by
        rw [h2, h3, add_zero]; exact add_le_add h1 le_rfl
    _ = ENNReal.ofReal (c * Real.log (1 / b) + D.tailConst) :=
        (ENNReal.ofReal_add (mul_nonneg hc0 hlog) ENNReal.toReal_nonneg).symm

theorem OriginDatum.isFiniteMeasure_bigJumps (hd : 1 ≤ d) (D : OriginDatum d)
    (hctop : D.profileAtOrigin ≠ ⊤) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    IsFiniteMeasure (D.bigJumps b) :=
  ⟨lt_of_le_of_lt (D.bigJumps_univ_le hd hctop hb hb1) ENNReal.ofReal_lt_top⟩

/-- The big jumps are symmetric. -/
theorem OriginDatum.bigJumps_symm (D : OriginDatum d) (b : ℝ) :
    (D.bigJumps b).map (fun x => -x) = D.bigJumps b := by
  have hS : MeasurableSet ({x : Rd d | ‖x‖ < b}ᶜ) :=
    (measurableSet_lt continuous_norm.measurable measurable_const).compl
  have hneg : (fun x : Rd d => -x) = (LinearIsometryEquiv.neg ℝ : Rd d ≃ₗᵢ[ℝ] Rd d) := by
    rw [LinearIsometryEquiv.coe_neg]
  have hpre : (fun x : Rd d => -x) ⁻¹' ({x : Rd d | ‖x‖ < b}ᶜ) = {x : Rd d | ‖x‖ < b}ᶜ := by
    ext x; simp
  rw [OriginDatum.bigJumps]
  conv_lhs => rw [← hpre]
  rw [← Measure.restrict_map (by fun_prop) hS, hneg, D.levyMeasure_map_isometry]

/-- **The exponent splits** at `b`: for `a = 0`, `F_d = F^{<b} + ∫ (1 - cos⟨ξ,x⟩) ν_d^{≥b}(dx)`. -/
theorem OriginDatum.exponentL_split (D : OriginDatum d) (ha : D.a = 0) (b : ℝ) (ξ : Rd d) :
    D.exponentL ξ = (D.truncate b).exponentL ξ +
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) ∂(D.bigJumps b) := by
  have hS : MeasurableSet {x : Rd d | ‖x‖ < b} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  rw [OriginDatum.exponentL, OriginDatum.exponentL, D.levyMeasure_truncate, ha,
    show (D.truncate b).a = 0 from rfl, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add,
    zero_add, OriginDatum.bigJumps, lintegral_add_compl _ hS]

/-- **The decomposition at one scale** (`prop:origin-lower-bound-d`): for `0 < b ≤ 1`, every law
`μ` of a datum with `a = 0` and `c < ∞` is `μ₁ ∗ π`, `μ₁` a law of the truncated datum (ledger
A3(iii)) and `π` the compound Poisson law of the big jumps. -/
theorem OriginDatum.law_eq_conv (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hctop : D.profileAtOrigin ≠ ⊤) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) :
    ∃ μ₁ : Measure (Rd d), IsLawOf (D.truncate b) μ₁ ∧
      haveI := D.isFiniteMeasure_bigJumps hd hctop hb hb1
      μ = μ₁ ∗ cpLaw (D.bigJumps b) := by
  haveI := D.isFiniteMeasure_bigJumps hd hctop hb hb1
  haveI := hμ.1
  set L := D.bigJumps b with hL
  obtain ⟨μ₁, hprob₁, -, hT₁⟩ := levy_khintchine_converse ((D.truncate b).triplet hd)
  haveI := hprob₁
  have hlaw₁ : IsLawOf (D.truncate b) μ₁ := ⟨hprob₁, fun ξ => by
    rw [hT₁ ξ, (D.truncate b).lkExponent_triplet hd, ← Complex.ofReal_neg, ← Complex.ofReal_exp]⟩
  refine ⟨μ₁, hlaw₁, Measure.ext_of_charFun (funext fun ξ => ?_)⟩
  have hint1 : Integrable (fun x : Rd d => 1 - Real.cos ⟪ξ, x⟫) L :=
    Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Real.cos_le_one ⟪ξ, x⟫, Real.neg_one_le_cos ⟪ξ, x⟫])
  have hpsi : (∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) ∂L).toReal
      = (L univ).toReal - ∫ x, Real.cos ⟪x, ξ⟫ ∂L := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun x => by
      show (0 : ℝ) ≤ 1 - Real.cos ⟪ξ, x⟫; linarith [Real.cos_le_one ⟪ξ, x⟫]),
      ENNReal.toReal_ofReal (integral_nonneg fun x => by
      show (0 : ℝ) ≤ 1 - Real.cos ⟪ξ, x⟫; linarith [Real.cos_le_one ⟪ξ, x⟫]),
      integral_sub (integrable_const 1)
      (Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [real_inner_comm]
  have hsplit : D.exponent ξ
      = (D.truncate b).exponent ξ + ((L univ).toReal - ∫ x, Real.cos ⟪x, ξ⟫ ∂L) := by
    rw [OriginDatum.exponent, D.exponentL_split ha b ξ, ENNReal.toReal_add
      ((D.truncate b).exponentL_ne_top hd ξ) ?_, ← hpsi]
    · rfl
    · have hfin := D.exponentL_ne_top hd ξ
      rw [D.exponentL_split ha b ξ] at hfin
      exact (ENNReal.add_ne_top.mp hfin).2
  rw [charFun_conv, hμ.2, hlaw₁.2, charFun_cpLaw, charFun_of_symm L (D.bigJumps_symm b), hsplit,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  ring

/-! ## The twofold convolution fills a ball -/

/-- For `d ≥ 2` every vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal (hd : 2 ≤ d) (z : Rd d) : ∃ w : Rd d, ‖w‖ = 1 ∧ ⟪z, w⟫ = 0 := by
  have hne : (ℝ ∙ z)ᗮ ≠ ⊥ := by
    intro h
    rw [Submodule.orthogonal_eq_bot_iff] at h
    have h1 : Module.finrank ℝ (ℝ ∙ z) ≤ 1 := by
      by_cases hz : z = 0
      · rw [hz, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; exact zero_le_one
      · rw [finrank_span_singleton hz]
    rw [h, finrank_top, finrank_euclideanSpace_fin] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  · rw [inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv, mul_zero]

/-- **The ball between two shells** (`prop:origin-lower-bound-d`, the twofold convolution): for
`d ≥ 2` and `|z| ≤ 3ε/2` there is `y₀` with `|y₀| = |z - y₀| = 3ε/4`, so every `y` within `ε/8`
of `y₀` has `|y|` and `|z - y|` in `[ε/2, ε)`. -/
theorem exists_ball_in_shells (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {z : Rd d}
    (hz : ‖z‖ ≤ 3 * ε / 2) :
    ∃ y₀ : Rd d, ∀ y ∈ ball y₀ (ε / 8),
      (ε / 2 ≤ ‖y‖ ∧ ‖y‖ < ε) ∧ (ε / 2 ≤ ‖z - y‖ ∧ ‖z - y‖ < ε) := by
  obtain ⟨w, hw1, hzw⟩ := exists_unit_orthogonal hd z
  set s := Real.sqrt (9 * ε ^ 2 / 16 - ‖z‖ ^ 2 / 4) with hs
  have hs2 : s ^ 2 = 9 * ε ^ 2 / 16 - ‖z‖ ^ 2 / 4 := by
    rw [hs, Real.sq_sqrt]
    nlinarith [norm_nonneg z]
  have hnorm : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ‖(1 / 2 : ℝ) • z + (σ * s) • w‖ = 3 * ε / 4 := by
    intro σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
    have hwz : ⟪w, z⟫ = 0 := by rw [real_inner_comm]; exact hzw
    have hsq : ‖(1 / 2 : ℝ) • z + (σ * s) • w‖ ^ 2 = (3 * ε / 4) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hw1, hzw, hwz, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      linear_combination hs2 + s ^ 2 * hσ2
    have h0 : 0 ≤ ‖(1 / 2 : ℝ) • z + (σ * s) • w‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖(1 / 2 : ℝ) • z + (σ * s) • w‖ - 3 * ε / 4),
      sq_nonneg (‖(1 / 2 : ℝ) • z + (σ * s) • w‖ + 3 * ε / 4)]
  set y₀ := (1 / 2 : ℝ) • z + (1 * s) • w with hy₀
  have hy₀n : ‖y₀‖ = 3 * ε / 4 := hnorm 1 (Or.inl rfl)
  have hzy₀ : z - y₀ = (1 / 2 : ℝ) • z + (-1 * s) • w := by
    rw [hy₀]; module
  have hzy₀n : ‖z - y₀‖ = 3 * ε / 4 := by rw [hzy₀]; exact hnorm (-1) (Or.inr rfl)
  refine ⟨y₀, fun y hy => ?_⟩
  rw [mem_ball, dist_eq_norm] at hy
  have h1 : ‖y₀‖ - ‖y - y₀‖ ≤ ‖y‖ := by
    have := norm_sub_norm_le y₀ (y₀ - y)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have h2 : ‖y‖ ≤ ‖y₀‖ + ‖y - y₀‖ := by
    have := norm_add_le y₀ (y - y₀)
    rwa [add_sub_cancel] at this
  have h3 : ‖z - y₀‖ - ‖y - y₀‖ ≤ ‖z - y‖ := by
    have := norm_sub_norm_le (z - y₀) (y - y₀)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have h4 : ‖z - y‖ ≤ ‖z - y₀‖ + ‖y - y₀‖ := by
    have := norm_sub_le (z - y₀) (y - y₀)
    rwa [sub_sub_sub_cancel_right] at this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- On the shell `{ε/2 ≤ |x| < ε}`, `ε ≤ ε₀`, the Lévy density of the datum is at least
`a = c/(2|S^{d-1}|ε^d)`, so the big jumps dominate `a` times Lebesgue measure on the shell. -/
theorem OriginDatum.bigJumps_ge_shell (hd : 1 ≤ d) (D : OriginDatum d) {ε₀ ε τ : ℝ}
    (hτ : τ ≤ 1 / 2) (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀)
    {A : Set (Rd d)} (hA : MeasurableSet A) :
    ENNReal.ofReal (D.profileAtOrigin.toReal / (2 * sphereArea d * ε ^ d)) *
        volume (A ∩ {x : Rd d | ε / 2 ≤ ‖x‖ ∧ ‖x‖ < ε}) ≤ D.bigJumps (τ * ε) A := by
  set S := {x : Rd d | ε / 2 ≤ ‖x‖ ∧ ‖x‖ < ε} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hA0 := (sphereArea_eq_toSphere hd).2
  have hsub : A ∩ S ⊆ A ∩ {x : Rd d | ‖x‖ < τ * ε}ᶜ := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    simp only [mem_compl_iff, mem_setOf_eq, not_lt]
    have : τ * ε ≤ ε / 2 := by nlinarith
    linarith [hx.2.1]
  rw [OriginDatum.bigJumps, Measure.restrict_apply hA]
  refine le_trans ?_ (measure_mono hsub)
  rw [OriginDatum.levyMeasure, withDensity_apply _ (hA.inter hSm), ← setLIntegral_const]
  refine setLIntegral_mono' (hA.inter hSm) fun x hx => ?_
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx.2.1
  have hxne : x ∈ ({0}ᶜ : Set (Rd d)) := fun h => by
    rw [mem_singleton_iff] at h; rw [h, norm_zero] at hx0; exact lt_irrefl 0 hx0
  rw [indicator_of_mem hxne]
  apply ENNReal.ofReal_le_ofReal
  have hk : D.profileAtOrigin.toReal / 2 ≤ D.k ‖x‖ :=
    hkε.trans (D.k_antitone hx0 (lt_of_lt_of_le hε hεε₀) (le_trans hx.2.2.le hεε₀))
  have hpow : ‖x‖ ^ d ≤ ε ^ d := pow_le_pow_left₀ (norm_nonneg x) hx.2.2.le d
  have hxd : 0 < ‖x‖ ^ d := pow_pos hx0 d
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : D.profileAtOrigin.toReal ≤ 2 * D.k ‖x‖ := by linarith
  have h2 : sphereArea d * ‖x‖ ^ d ≤ sphereArea d * ε ^ d := mul_le_mul_of_nonneg_left hpow hA0.le
  calc D.profileAtOrigin.toReal * (sphereArea d * ‖x‖ ^ d)
      ≤ (2 * D.k ‖x‖) * (sphereArea d * ε ^ d) :=
        mul_le_mul h1 h2 (by positivity) (by linarith [D.k_nonneg ‖x‖ hx0])
    _ = D.k ‖x‖ * (2 * sphereArea d * ε ^ d) := by ring

/-- **`prop:origin-lower-bound-d`, the twofold convolution fills a ball**: for `d ≥ 2`,
`ε ≤ ε₀` with `k_d(ε₀) ≥ c/2` and `τ ≤ 1/2`, the big jumps `L = ν_d(· ∩ {|x| ≥ τε})` satisfy
`(L ∗ L)(G) ≥ κ₀ ε^{-d} |G|` for every Borel `G ⊆ B̄(0, 3ε/2)`. -/
theorem OriginDatum.bigJumps_conv_ge (hd : 2 ≤ d) (D : OriginDatum d)
    (hctop : D.profileAtOrigin ≠ ⊤) {ε₀ ε τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (hε₀ : ε₀ ≤ 1) (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀)
    {G : Set (Rd d)} (hG : MeasurableSet G) (hGb : G ⊆ closedBall 0 (3 * ε / 2)) :
    haveI := D.isFiniteMeasure_bigJumps (by omega) hctop (mul_pos hτ0 hε)
      (by nlinarith)
    ENNReal.ofReal (lowerBoundKappa d D.profileAtOrigin.toReal / ε ^ d) * volume G ≤
      (D.bigJumps (τ * ε) ∗ D.bigJumps (τ * ε)) G := by
  have hd1 : 1 ≤ d := by omega
  haveI := D.isFiniteMeasure_bigJumps hd1 hctop (mul_pos hτ0 hε) (by nlinarith)
  set L := D.bigJumps (τ * ε) with hL
  set c := D.profileAtOrigin.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hA0 := (sphereArea_eq_toSphere hd1).2
  set a := c / (2 * sphereArea d * ε ^ d) with ha
  have ha0 : 0 ≤ a := by positivity
  set S := {x : Rd d | ε / 2 ≤ ‖x‖ ∧ ‖x‖ < ε} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  -- `L ≥ a · Lebesgue on S`
  have hLge : ENNReal.ofReal a • (volume : Measure (Rd d)).restrict S ≤ L := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
    exact D.bigJumps_ge_shell hd1 hτ hε hεε₀ hkε hA
  -- the convolution as an iterated integral
  have hGm : MeasurableSet ((fun p : Rd d × Rd d => p.1 + p.2) ⁻¹' G) := measurable_add hG
  have hconv : (L ∗ L) G = ∫⁻ x, L {y | x + y ∈ G} ∂L := by
    rw [Measure.conv, Measure.map_apply measurable_add hG, Measure.prod_apply hGm]
    rfl
  set T : Set (Rd d × Rd d) := {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 ∈ G} with hT
  have hTm : MeasurableSet T :=
    (measurable_fst hSm).inter ((measurable_snd hSm).inter hGm)
  have hstep1 : ENNReal.ofReal a * ENNReal.ofReal a * ((volume : Measure (Rd d)).prod volume) T
      ≤ (L ∗ L) G := by
    rw [hconv, Measure.prod_apply hTm]
    have hset : ∀ x : Rd d, volume (Prod.mk x ⁻¹' T)
        = S.indicator (fun x => volume ({y : Rd d | x + y ∈ G} ∩ S)) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]; congr 1; ext y; simp [hT, hx, and_comm]
      · rw [indicator_of_notMem hx]
        have : Prod.mk x ⁻¹' T = ∅ := by ext y; simp [hT, hx]
        rw [this, measure_empty]
    calc ENNReal.ofReal a * ENNReal.ofReal a * ∫⁻ x, volume (Prod.mk x ⁻¹' T)
        = ∫⁻ x, ENNReal.ofReal a * volume ({y : Rd d | x + y ∈ G} ∩ S)
            ∂(ENNReal.ofReal a • (volume : Measure (Rd d)).restrict S) := by
          rw [lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc,
            ← lintegral_indicator hSm]
          congr 2
          exact lintegral_congr fun x => hset x
      _ ≤ ∫⁻ x, L {y | x + y ∈ G} ∂L := by
          refine lintegral_mono' hLge fun x => ?_
          have hm : MeasurableSet {y : Rd d | x + y ∈ G} := (measurable_const_add x) hG
          exact D.bigJumps_ge_shell hd1 hτ hε hεε₀ hkε hm
  -- the shear `(x, y) ↦ (x + y, x)`
  set T' : Set (Rd d × Rd d) := {p | p.1 ∈ G ∧ p.2 ∈ S ∧ p.1 - p.2 ∈ S} with hT'
  have hT'm : MeasurableSet T' :=
    (measurable_fst hG).inter ((measurable_snd hSm).inter ((measurable_fst.sub measurable_snd) hSm))
  have hshear : MeasurePreserving (fun p : Rd d × Rd d => (p.1 + p.2, p.1))
      ((volume : Measure (Rd d)).prod volume) ((volume : Measure (Rd d)).prod volume) := by
    have h := (measurePreserving_prod_add (volume : Measure (Rd d)) (volume : Measure (Rd d)))
    exact Measure.measurePreserving_swap.comp h
  have hpre : (fun p : Rd d × Rd d => (p.1 + p.2, p.1)) ⁻¹' T' = T := by
    ext p; simp [hT, hT', and_comm, and_left_comm]
  have hTT' : ((volume : Measure (Rd d)).prod volume) T
      = ((volume : Measure (Rd d)).prod volume) T' := by
    rw [← hpre, hshear.measure_preimage hT'm.nullMeasurableSet]
  -- each `z ∈ G` sees a ball of radius `ε/8`
  have hball : ∀ z ∈ G, ENNReal.ofReal ((ε / 8) ^ d) * volume (ball (0 : Rd d) 1)
      ≤ volume (Prod.mk z ⁻¹' T') := by
    intro z hz
    have hzn : ‖z‖ ≤ 3 * ε / 2 := by simpa using hGb hz
    obtain ⟨y₀, hy₀⟩ := exists_ball_in_shells hd hε hzn
    haveI : Nontrivial (Rd d) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      infer_instance
    calc ENNReal.ofReal ((ε / 8) ^ d) * volume (ball (0 : Rd d) 1)
        = volume (ball y₀ (ε / 8)) := by
          rw [Measure.addHaar_ball volume y₀ (r := ε / 8) (by positivity),
            finrank_euclideanSpace_fin]
      _ ≤ volume (Prod.mk z ⁻¹' T') := measure_mono fun y hy => by
          obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hy₀ y hy
          exact ⟨hz, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hstep2 : ENNReal.ofReal ((ε / 8) ^ d) * volume (ball (0 : Rd d) 1) * volume G
      ≤ ((volume : Measure (Rd d)).prod volume) T' := by
    rw [Measure.prod_apply hT'm, ← setLIntegral_const]
    refine (setLIntegral_mono' hG hball).trans (setLIntegral_le_lintegral _ _)
  -- the constant
  have hV : volume (ball (0 : Rd d) 1) = ENNReal.ofReal (volume (ball (0 : Rd d) 1)).toReal :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hkey : lowerBoundKappa d c / ε ^ d
      = a * a * ((ε / 8) ^ d * (volume (ball (0 : Rd d) 1)).toReal) := by
    rw [lowerBoundKappa, ha, div_pow]
    have hεd : 0 < ε ^ d := pow_pos hε d
    have h8 : (0 : ℝ) < 8 ^ d := by positivity
    have h18 : ((1 : ℝ) / 8) ^ d * 8 ^ d = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (-(c ^ 2 * (volume (ball (0 : Rd d) 1)).toReal * ε ^ d)) * h18
  have hconst : ENNReal.ofReal (lowerBoundKappa d c / ε ^ d)
      = ENNReal.ofReal a * ENNReal.ofReal a *
          (ENNReal.ofReal ((ε / 8) ^ d) * volume (ball (0 : Rd d) 1)) := by
    rw [hkey, ENNReal.ofReal_mul (mul_nonneg ha0 ha0), ENNReal.ofReal_mul ha0,
      ENNReal.ofReal_mul (by positivity), ← hV]
  calc ENNReal.ofReal (lowerBoundKappa d c / ε ^ d) * volume G
      = ENNReal.ofReal a * ENNReal.ofReal a *
          (ENNReal.ofReal ((ε / 8) ^ d) * volume (ball (0 : Rd d) 1) * volume G) := by
        rw [hconst]; ring
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal a * ((volume : Measure (Rd d)).prod volume) T := by
        rw [hTT']; gcongr
    _ ≤ (L ∗ L) G := hstep1

/-! ## The small jumps move little -/

/-- **A Gaussian Parseval identity**: `∫ Re ρ̂ dg^{(d)}_s = ∫ e^{-s|x|²/2} ρ(dx)` for a probability
measure `ρ` on `ℝ^d` and `s ≥ 0`. -/
theorem integral_re_charFun_gaussVar (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] {s : ℝ}
    (hs : 0 ≤ s) :
    ∫ ξ, (charFun ρ ξ).re ∂(gaussVar d s) = ∫ x, Real.exp (-(s * ‖x‖ ^ 2) / 2) ∂ρ := by
  have hcont : Continuous (fun p : Rd d × Rd d => Real.cos ⟪p.2, p.1⟫) := by fun_prop
  have hint : Integrable (fun p : Rd d × Rd d => Real.cos ⟪p.2, p.1⟫) ((gaussVar d s).prod ρ) :=
    Integrable.of_bound hcont.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  calc ∫ ξ, (charFun ρ ξ).re ∂(gaussVar d s) = ∫ ξ, ∫ x, Real.cos ⟪x, ξ⟫ ∂ρ ∂(gaussVar d s) := by
        congr 1; funext ξ; exact ScaleSpace.re_charFun_eq_integral_cos ρ ξ
    _ = ∫ x, ∫ ξ, Real.cos ⟪x, ξ⟫ ∂(gaussVar d s) ∂ρ := integral_integral_swap hint
    _ = ∫ x, Real.exp (-(s * ‖x‖ ^ 2) / 2) ∂ρ := by
        congr 1; funext x
        have h := ScaleSpace.re_charFun_eq_integral_cos (gaussVar d s) x
        rw [charFun_gaussVar hs x, Complex.ofReal_re] at h
        rw [h]
        exact integral_congr_ae (ae_of_all _ fun ξ => by simp only [real_inner_comm])

/-- `|S^{d-1}| π^{-d/2} Γ(d/2 + 1) = d`. -/
theorem sphereArea_mul_gamma (hd : 1 ≤ d) :
    sphereArea d * Real.pi ^ (-((d : ℝ) / 2)) * Real.Gamma ((d : ℝ) / 2 + 1) = d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  rw [sphereArea, Real.Gamma_add_one (by positivity), Real.rpow_neg Real.pi_pos.le]
  field_simp

/-- **The second moment of `g^{(d)}_s`**: `∫ |ξ|² g^{(d)}_s(dξ) = d s` for `s > 0`. -/
theorem lintegral_norm_sq_gaussVar (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) ∂(gaussVar d s) = ENNReal.ofReal (d * s) := by
  rw [gaussVar_eq_withDensity hs, lintegral_withDensity_eq_lintegral_mul _
    (continuous_heatKernel.measurable.ennreal_ofReal) (by fun_prop)]
  simp_rw [Pi.mul_apply, mul_comm (ENNReal.ofReal (heatKernel d s _))]
  rw [lintegral_norm_sq_heatKernel hd hs, sphereArea_mul_gamma hd]

/-- **The exponent of the truncated datum is small**: `F^{<b}(ξ) ≤ c b² |ξ|²/4` for
`0 < b ≤ 1`. -/
theorem OriginDatum.truncate_exponent_le (hd : 1 ≤ d) (D : OriginDatum d)
    (hctop : D.profileAtOrigin ≠ ⊤) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ξ : Rd d) :
    (D.truncate b).exponent ξ ≤ D.profileAtOrigin.toReal * b ^ 2 * ‖ξ‖ ^ 2 / 4 := by
  set c := D.profileAtOrigin.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hA := sphereArea_eq_toSphere hd
  set D₁ := D.truncate b with hD₁
  have hnear : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (D₁.k r * r)
      ≤ ENNReal.ofReal (c * b ^ 2 / 2) := by
    have hint : IntegrableOn (fun r : ℝ => c * r) (Ioc 0 b) :=
      (by fun_prop : Continuous fun r : ℝ => c * r).integrableOn_Ioc
    calc ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (D₁.k r * r)
        ≤ ∫⁻ r in Ioc (0 : ℝ) b, ENNReal.ofReal (c * r) := by
          rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioc]
          refine lintegral_mono fun r => ?_
          by_cases hr : r ∈ Ioo (0 : ℝ) 1
          · rw [indicator_of_mem hr]
            by_cases hrb : r < b
            · rw [indicator_of_mem (show r ∈ Ioc (0 : ℝ) b from ⟨hr.1, hrb.le⟩)]
              refine ENNReal.ofReal_le_ofReal ?_
              simp only [hD₁, OriginDatum.truncate, hrb, if_true]
              exact mul_le_mul_of_nonneg_right (D.k_le_profile hctop hr.1) hr.1.le
            · simp only [hD₁, OriginDatum.truncate, hrb, if_false, zero_mul, ENNReal.ofReal_zero]
              exact zero_le
          · rw [indicator_of_notMem hr]; exact zero_le
      _ = ENNReal.ofReal (c * b ^ 2 / 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun r hr => mul_nonneg hc0 hr.1.le)),
            ← intervalIntegral.integral_of_le hb.le,
            intervalIntegral.integral_const_mul, integral_id]
          congr 1; ring
  have hfar : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D₁.k r / r) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun r (hr : 1 < r) => by
      have : ¬ r < b := not_lt.mpr (le_trans hb1 hr.le)
      simp only [hD₁, OriginDatum.truncate, this, if_false, zero_div, ENNReal.ofReal_zero]]
    exact lintegral_zero
  have hpt : ∀ η : sphere (0 : Rd d) 1, cosProfileL D₁.k ⟪ξ, (η : Rd d)⟫
      ≤ ENNReal.ofReal (‖ξ‖ ^ 2 / 2) * ENNReal.ofReal (c * b ^ 2 / 2) := by
    intro η
    refine (cosProfileL_le_sq D₁.k D₁.k_nonneg _).trans ?_
    rw [hfar, mul_zero, add_zero]
    have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
    have hle : ⟪ξ, (η : Rd d)⟫ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      have := abs_real_inner_le_norm ξ (η : Rd d)
      rw [hη, mul_one] at this
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hnear
  have hL : D₁.exponentL ξ ≤ ENNReal.ofReal (c * b ^ 2 * ‖ξ‖ ^ 2 / 4) := by
    rw [D₁.exponentL_eq_sphere hd, show D₁.a = 0 from rfl, zero_mul, zero_div, ENNReal.ofReal_zero,
      zero_add]
    calc (ENNReal.ofReal (sphereArea d))⁻¹ * ∫⁻ η : sphere (0 : Rd d) 1,
          cosProfileL D₁.k ⟪ξ, (η : Rd d)⟫ ∂((volume : Measure (Rd d)).toSphere)
        ≤ (ENNReal.ofReal (sphereArea d))⁻¹ * ∫⁻ _η : sphere (0 : Rd d) 1,
          ENNReal.ofReal (‖ξ‖ ^ 2 / 2) * ENNReal.ofReal (c * b ^ 2 / 2)
            ∂((volume : Measure (Rd d)).toSphere) := by
          gcongr with η; exact hpt η
      _ = ENNReal.ofReal (c * b ^ 2 * ‖ξ‖ ^ 2 / 4) := by
          rw [lintegral_const, ← hA.1, mul_left_comm, ENNReal.inv_mul_cancel (by simp [hA.2])
            ENNReal.ofReal_ne_top, mul_one, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL

/-- **The small jumps move little** (`prop:origin-lower-bound-d`): if `τ ≤ (3/(4d²c))^{1/2}`,
`d ≥ 2`, `0 < τε ≤ 1`, a law `μ₁` of the datum truncated at `τε` has `μ₁(|x| ≥ ε) ≤ 1/2`. Through
the Gaussian Parseval identity at variance `ε^{-2}`: `(1 - e^{-1/2}) μ₁(|x| ≥ ε) ≤
∫ (1 - e^{-|x|²/2ε²}) dμ₁ = ∫ (1 - μ̂₁) dg ≤ ∫ F^{<τε} dg ≤ cτ²d/4 ≤ 3/32`. -/
theorem OriginDatum.truncate_law_tail (hd : 2 ≤ d) (D : OriginDatum d)
    (hctop : D.profileAtOrigin ≠ ⊤) (hc0 : 0 < D.profileAtOrigin.toReal) {τ ε : ℝ} (hτ0 : 0 < τ)
    (hτ : τ ≤ Real.sqrt (3 / (4 * (d : ℝ) ^ 2 * D.profileAtOrigin.toReal))) (hε : 0 < ε)
    (hτε : τ * ε ≤ 1) (μ₁ : Measure (Rd d)) (hμ₁ : IsLawOf (D.truncate (τ * ε)) μ₁) :
    μ₁ {x | ε ≤ ‖x‖} ≤ ENNReal.ofReal (1 / 2) := by
  have hd1 : 1 ≤ d := by omega
  haveI := hμ₁.1
  set c := D.profileAtOrigin.toReal with hc
  set s : ℝ := (ε ^ 2)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  set γ := gaussVar d s with hγ
  set f : Rd d → ℝ := fun x => 1 - Real.exp (-(s * ‖x‖ ^ 2) / 2) with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [hf, sub_nonneg, Real.exp_le_one_iff]
    have : 0 ≤ s * ‖x‖ ^ 2 := by positivity
    rw [neg_div]; linarith
  have hfint : Integrable f μ₁ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (hf0 x)]
      simp only [hf]; linarith [Real.exp_pos (-(s * ‖x‖ ^ 2) / 2)])
  set g : Rd d → ℝ := fun ξ => 1 - (charFun μ₁ ξ).re with hg
  have hre : ∀ ξ, (charFun μ₁ ξ).re = Real.exp (-(D.truncate (τ * ε)).exponent ξ) :=
    hμ₁.charFun_re
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => by
    simp only [hg, hre, sub_nonneg, Real.exp_le_one_iff, neg_nonpos]
    exact OriginDatum.exponent_nonneg _ ξ
  have hgint : Integrable g γ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun ξ => by
      rw [Real.norm_of_nonneg (hg0 ξ)]
      simp only [hg, hre]; linarith [Real.exp_pos (-(D.truncate (τ * ε)).exponent ξ)])
  -- (A) the tail under `f`
  have hS : MeasurableSet {x : Rd d | ε ≤ ‖x‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hA : ENNReal.ofReal (1 - Real.exp (-(1 / 2))) * μ₁ {x | ε ≤ ‖x‖}
      ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ₁ := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono' hS fun x (hx : ε ≤ ‖x‖) => ENNReal.ofReal_le_ofReal ?_).trans
      (setLIntegral_le_lintegral _ _)
    simp only [hf]
    have h1 : 1 ≤ s * ‖x‖ ^ 2 := by
      rw [hs, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hε.le hx 2
    have : Real.exp (-(s * ‖x‖ ^ 2) / 2) ≤ Real.exp (-(1 / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  -- (B) Parseval
  have hB : ∫⁻ x, ENNReal.ofReal (f x) ∂μ₁ = ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂γ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ hf0),
      ← ofReal_integral_eq_lintegral_ofReal hgint (ae_of_all _ hg0)]
    congr 1
    simp only [hf, hg]
    rw [integral_sub (integrable_const 1) (Integrable.of_bound (by fun_prop) 1
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
          have : 0 ≤ s * ‖x‖ ^ 2 := by positivity
          rw [neg_div]; linarith)),
      integral_sub (integrable_const 1) (Integrable.of_bound (by fun_prop) 1
        (ae_of_all _ fun ξ => by
          rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (norm_charFun_le_one _))),
      integral_re_charFun_gaussVar μ₁ hs0.le]
    simp
  -- (C) the exponent bound and the second moment
  set K : ℝ := c * (τ * ε) ^ 2 / 4 with hK
  have hC : ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂γ ≤ ENNReal.ofReal (K * (d * s)) := by
    calc ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂γ ≤ ∫⁻ ξ, ENNReal.ofReal K * ENNReal.ofReal (‖ξ‖ ^ 2) ∂γ := by
          refine lintegral_mono fun ξ => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hg, hre]
          have h1 := Real.add_one_le_exp (-(D.truncate (τ * ε)).exponent ξ)
          have h2 := D.truncate_exponent_le hd1 hctop (mul_pos hτ0 hε) hτε ξ
          rw [hK]; linarith
      _ = ENNReal.ofReal (K * (d * s)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_norm_sq_gaussVar hd1 hs0,
            ← ENNReal.ofReal_mul (by positivity)]
  -- the numbers
  have hKds : K * (d * s) ≤ 3 / 32 := by
    have hτ2 : τ ^ 2 ≤ 3 / (4 * (d : ℝ) ^ 2 * c) := by
      have := pow_le_pow_left₀ hτ0.le hτ 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hKeq : K * (d * s) = c * τ ^ 2 * d / 4 := by
      rw [hK, hs, mul_pow]
      field_simp
    rw [hKeq]
    have h1 : c * τ ^ 2 ≤ 3 / (4 * (d : ℝ) ^ 2) := by
      calc c * τ ^ 2 ≤ c * (3 / (4 * (d : ℝ) ^ 2 * c)) := mul_le_mul_of_nonneg_left hτ2 hc0.le
        _ = 3 / (4 * (d : ℝ) ^ 2) := by field_simp
    calc c * τ ^ 2 * (d : ℝ) / 4 ≤ 3 / (4 * (d : ℝ) ^ 2) * (d : ℝ) / 4 := by gcongr
      _ = 3 / (16 * (d : ℝ)) := by field_simp; ring
      _ ≤ 3 / 32 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hexp : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (1 / 2)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  -- conclude in `ℝ`
  have hfin : μ₁ {x | ε ≤ ‖x‖} ≠ ⊤ := measure_ne_top _ _
  have hmain : ENNReal.ofReal (1 - Real.exp (-(1 / 2))) * μ₁ {x | ε ≤ ‖x‖}
      ≤ ENNReal.ofReal (K * (d * s)) := (hA.trans (le_of_eq hB)).trans hC
  have hreal : (1 - Real.exp (-(1 / 2))) * (μ₁ {x | ε ≤ ‖x‖}).toReal ≤ K * (d * s) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by positivity)] at this
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hX : 0 ≤ (μ₁ {x | ε ≤ ‖x‖}).toReal := ENNReal.toReal_nonneg
  nlinarith

/-! ## One scale -/

theorem lowerBoundTau_pos {c : ℝ} (hd : 1 ≤ d) (hc : 0 < c) : 0 < lowerBoundTau d c := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  exact lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))

theorem lowerBoundKappa_pos {c : ℝ} (hd : 1 ≤ d) (hc : 0 < c) : 0 < lowerBoundKappa d c := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hV : 0 < (volume (ball (0 : Rd d) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  unfold lowerBoundKappa
  positivity

/-- **One scale** (`prop:origin-lower-bound-d`): for `0 < ε ≤ ε₀` and a Borel
`E ⊆ B̄(0, ε/2)`, `μ(E) ≥ κ₁ ε^{c-d} |E|`, `κ₁ = (κ₀/4) τ^c e^{-C_k}`. -/
theorem OriginDatum.one_scale (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hctop : D.profileAtOrigin ≠ ⊤) (hc : 0 < D.profileAtOrigin.toReal) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {ε₀ ε : ℝ} (hε₀1 : ε₀ ≤ 1)
    (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    {E : Set (Rd d)} (hE : MeasurableSet E) (hEb : E ⊆ closedBall 0 (ε / 2)) :
    ENNReal.ofReal (lowerBoundKappa d D.profileAtOrigin.toReal / 4 *
        lowerBoundTau d D.profileAtOrigin.toReal ^ D.profileAtOrigin.toReal *
        Real.exp (-D.tailConst) * ε ^ (D.profileAtOrigin.toReal - d)) * volume E ≤ μ E := by
  have hd1 : 1 ≤ d := by omega
  set c := D.profileAtOrigin.toReal with hcdef
  set τ := lowerBoundTau d c with hτdef
  have hτ0 : 0 < τ := lowerBoundTau_pos hd1 hc
  have hτ12 : τ ≤ 1 / 2 := min_le_left _ _
  have hτs : τ ≤ Real.sqrt (3 / (4 * (d : ℝ) ^ 2 * c)) := min_le_right _ _
  set b := τ * ε with hb
  have hb0 : 0 < b := mul_pos hτ0 hε
  have hb1 : b ≤ 1 := by nlinarith
  haveI := hμ.1
  obtain ⟨μ₁, hlaw₁, hμeq⟩ := D.law_eq_conv hd1 ha hctop hb0 hb1 μ hμ
  haveI := D.isFiniteMeasure_bigJumps hd1 hctop hb0 hb1
  haveI := hlaw₁.1
  set L := D.bigJumps b with hL
  set m := (L univ).toReal with hm
  set κ₀ := lowerBoundKappa d c with hκ₀
  have hκ₀0 : 0 < κ₀ := lowerBoundKappa_pos hd1 hc
  -- the compound Poisson law dominates its second term
  have hπ : ∀ G : Set (Rd d), MeasurableSet G →
      ENNReal.ofReal (Real.exp (-m) / 2) * (L ∗ L) G ≤ cpLaw L G := by
    intro G hG
    rw [cpLaw, Measure.sum_apply _ hG]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 2)
    rw [Measure.smul_apply, smul_eq_mul, convPow, convPow, convPow, Measure.dirac_zero_conv]
    norm_num [hm]
  -- each translate of `E` by `|w| < ε` lies in `B̄(0, 3ε/2)`
  have htr : ∀ w : Rd d, ‖w‖ < ε →
      ENNReal.ofReal (Real.exp (-m) / 2) * (ENNReal.ofReal (κ₀ / ε ^ d) * volume E)
        ≤ cpLaw L {v | w + v ∈ E} := by
    intro w hw
    have hGm : MeasurableSet {v : Rd d | w + v ∈ E} := (measurable_const_add w) hE
    have hGb : {v : Rd d | w + v ∈ E} ⊆ closedBall 0 (3 * ε / 2) := by
      intro v hv
      have h1 := hEb hv
      rw [mem_closedBall, dist_zero_right] at h1 ⊢
      have : ‖v‖ ≤ ‖w + v‖ + ‖w‖ := by
        have := norm_sub_le (w + v) w
        rwa [add_sub_cancel_left] at this
      linarith
    have hvol : volume {v : Rd d | w + v ∈ E} = volume E := measure_preimage_add _ w E
    refine le_trans ?_ (hπ _ hGm)
    gcongr
    rw [← hvol]
    exact D.bigJumps_conv_ge hd hctop hτ0 hτ12 hε hεε₀ hε₀1 hkε hGm hGb
  -- the convolution with the small jumps
  have hsmall : ENNReal.ofReal (1 / 2) ≤ μ₁ {w | ‖w‖ < ε} := by
    have htail := D.truncate_law_tail hd hctop hc hτ0 hτs hε hb1 μ₁ hlaw₁
    have hcompl : {w : Rd d | ‖w‖ < ε} = {w | ε ≤ ‖w‖}ᶜ := by ext w; simp
    rw [hcompl,
      prob_compl_eq_one_sub (measurableSet_le measurable_const continuous_norm.measurable)]
    calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
      _ ≤ 1 - μ₁ {w | ε ≤ ‖w‖} := tsub_le_tsub_left htail 1
  have hconv : μ E = ∫⁻ w, cpLaw L {v | w + v ∈ E} ∂μ₁ := by
    rw [hμeq, Measure.conv, Measure.map_apply measurable_add hE,
      Measure.prod_apply (measurable_add hE)]
    rfl
  have hmain : ENNReal.ofReal (Real.exp (-m) / 2) * (ENNReal.ofReal (κ₀ / ε ^ d) * volume E) *
      ENNReal.ofReal (1 / 2) ≤ μ E := by
    rw [hconv]
    calc ENNReal.ofReal (Real.exp (-m) / 2) * (ENNReal.ofReal (κ₀ / ε ^ d) * volume E) *
          ENNReal.ofReal (1 / 2)
        ≤ ENNReal.ofReal (Real.exp (-m) / 2) * (ENNReal.ofReal (κ₀ / ε ^ d) * volume E) *
          μ₁ {w | ‖w‖ < ε} := by gcongr
      _ = ∫⁻ w in {w | ‖w‖ < ε}, ENNReal.ofReal (Real.exp (-m) / 2) *
          (ENNReal.ofReal (κ₀ / ε ^ d) * volume E) ∂μ₁ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ w in {w | ‖w‖ < ε}, cpLaw L {v | w + v ∈ E} ∂μ₁ :=
          setLIntegral_mono' (measurableSet_lt continuous_norm.measurable measurable_const)
            fun w hw => htr w hw
      _ ≤ ∫⁻ w, cpLaw L {v | w + v ∈ E} ∂μ₁ := setLIntegral_le_lintegral _ _
  -- the mass bound `e^{-m} ≥ (τε)^c e^{-C_k}`
  have hmle : m ≤ c * Real.log (1 / b) + D.tailConst := by
    have h := D.bigJumps_univ_le hd1 hctop hb0 hb1
    have hlog : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by rw [le_div_iff₀ hb0]; linarith)
    exact ENNReal.toReal_le_of_le_ofReal
      (add_nonneg (mul_nonneg hc.le hlog) ENNReal.toReal_nonneg) h
  have hexpm : b ^ c * Real.exp (-D.tailConst) ≤ Real.exp (-m) := by
    rw [Real.rpow_def_of_pos hb0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [one_div, Real.log_inv] at hmle
    linarith
  have hεpow : ε ^ (c - d) = ε ^ c / ε ^ d := by
    rw [Real.rpow_sub hε, Real.rpow_natCast]
  have hreal : κ₀ / 4 * τ ^ c * Real.exp (-D.tailConst) * ε ^ (c - d)
      ≤ Real.exp (-m) / 2 * (κ₀ / ε ^ d) * (1 / 2) := by
    rw [hεpow]
    have hbc : b ^ c = τ ^ c * ε ^ c := Real.mul_rpow hτ0.le hε.le
    have hεd : 0 < ε ^ d := pow_pos hε d
    have h1 : τ ^ c * ε ^ c * Real.exp (-D.tailConst) ≤ Real.exp (-m) := by rw [← hbc]; exact hexpm
    have h2 : 0 ≤ κ₀ / ε ^ d := by positivity
    calc κ₀ / 4 * τ ^ c * Real.exp (-D.tailConst) * (ε ^ c / ε ^ d)
        = (τ ^ c * ε ^ c * Real.exp (-D.tailConst)) / 2 * (κ₀ / ε ^ d) * (1 / 2) := by
          field_simp; ring
      _ ≤ Real.exp (-m) / 2 * (κ₀ / ε ^ d) * (1 / 2) := by gcongr
  calc ENNReal.ofReal (κ₀ / 4 * τ ^ c * Real.exp (-D.tailConst) * ε ^ (c - d)) * volume E
      ≤ ENNReal.ofReal (Real.exp (-m) / 2 * (κ₀ / ε ^ d) * (1 / 2)) * volume E := by gcongr
    _ = ENNReal.ofReal (Real.exp (-m) / 2) * (ENNReal.ofReal (κ₀ / ε ^ d) * volume E) *
          ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ μ E := hmain

/-! ## All scales -/

/-- `θ r^p ≤ ε^p` when `2r ≤ ε < 4r`, `θ = min{2^p, 4^p}`. -/
theorem theta_mul_rpow_le {p ε r : ℝ} (hr : 0 < r) (h1 : 2 * r ≤ ε) (h2 : ε < 4 * r) :
    min ((2 : ℝ) ^ p) ((4 : ℝ) ^ p) * r ^ p ≤ ε ^ p := by
  have hrp : 0 ≤ r ^ p := Real.rpow_nonneg hr.le p
  rcases le_or_gt 0 p with hp | hp
  · calc min ((2 : ℝ) ^ p) ((4 : ℝ) ^ p) * r ^ p ≤ 2 ^ p * r ^ p :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hrp
      _ = (2 * r) ^ p := (Real.mul_rpow (by norm_num) hr.le).symm
      _ ≤ ε ^ p := Real.rpow_le_rpow (by positivity) h1 hp
  · calc min ((2 : ℝ) ^ p) ((4 : ℝ) ^ p) * r ^ p ≤ 4 ^ p * r ^ p :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hrp
      _ = (4 * r) ^ p := (Real.mul_rpow (by norm_num) hr.le).symm
      _ ≤ ε ^ p := Real.rpow_le_rpow_of_nonpos (by linarith) h2.le hp.le

/-- **All scales** (`eq:origin-lower-bound`): for `ε₀ ∈ (0,1]` with `k_d(ε₀) ≥ c/2` and a Borel
`E ⊆ B(0, ε₀/2)`, `μ(E) ≥ c₁ ∫_E |x|^{c-d} dx`, summing `OriginDatum.one_scale` over the dyadic
shells `ε₀ 2^{-n}/4 < |x| ≤ ε₀ 2^{-n}/2`. -/
theorem OriginDatum.all_scales (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hctop : D.profileAtOrigin ≠ ⊤) (hc : 0 < D.profileAtOrigin.toReal) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioc (0 : ℝ) 1)
    (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) {E : Set (Rd d)} (hE : MeasurableSet E)
    (hEb : E ⊆ ball 0 (ε₀ / 2)) :
    ENNReal.ofReal (lowerBoundConst d D.profileAtOrigin.toReal D.tailConst) *
        ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ (D.profileAtOrigin.toReal - d)) ≤ μ E := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  haveI := hμ.1
  set c := D.profileAtOrigin.toReal with hcdef
  set p : ℝ := c - d with hp
  set κ₁ := lowerBoundKappa d c / 4 * lowerBoundTau d c ^ c * Real.exp (-D.tailConst) with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := by
    have := lowerBoundKappa_pos (d := d) (by omega) hc
    have := lowerBoundTau_pos (d := d) (by omega) hc
    positivity
  have hc₁ : lowerBoundConst d c D.tailConst = κ₁ * min ((2 : ℝ) ^ p) ((4 : ℝ) ^ p) := rfl
  set εn : ℕ → ℝ := fun n => ε₀ / 2 ^ n with hεn
  have hεn0 : ∀ n, 0 < εn n := fun n => by simp only [hεn]; exact div_pos hε₀.1 (by positivity)
  have hεnle : ∀ n, εn n ≤ ε₀ := fun n => div_le_self hε₀.1.le (one_le_pow₀ (by norm_num))
  set A : ℕ → Set (Rd d) := fun n => {x | εn n / 4 < ‖x‖ ∧ ‖x‖ ≤ εn n / 2} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  -- the shells are disjoint and cover `E ∖ {0}`
  have hdisj : Pairwise (Function.onFun Disjoint fun n => E ∩ A n) := by
    have key : ∀ m n : ℕ, m < n → Disjoint (E ∩ A m) (E ∩ A n) := by
      intro m n hmn
      refine Set.disjoint_left.mpr fun x hxm hxn => ?_
      have h1 := hxm.2.1
      have h2 := hxn.2.2
      have hpow : (2 : ℝ) ^ m * 2 ≤ 2 ^ n := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hmn
      have : εn n / 2 ≤ εn m / 4 := by
        simp only [hεn]
        rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hε₀.1]
      linarith
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm
  have hcover : E ⊆ (⋃ n, E ∩ A n) ∪ {0} := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    left
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxb : ‖x‖ < ε₀ / 2 := by simpa using hEb hx
    have ht : 1 ≤ ε₀ / (2 * ‖x‖) := by rw [le_div_iff₀ (by positivity)]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ht (by norm_num : (1 : ℝ) < 2)
    refine mem_iUnion.mpr ⟨n, hx, ?_, ?_⟩
    · simp only [hεn]
      have h2' : ε₀ < 2 ^ (n + 1) * (2 * ‖x‖) := (div_lt_iff₀ (by positivity)).mp hn2
      rw [pow_succ] at h2'
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    · simp only [hεn]
      have h1' : 2 ^ n * (2 * ‖x‖) ≤ ε₀ := (le_div_iff₀ (by positivity)).mp hn1
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith
  -- one scale on each shell
  have hshell : ∀ n, ENNReal.ofReal (lowerBoundConst d c D.tailConst) *
      ∫⁻ x in E ∩ A n, ENNReal.ofReal (‖x‖ ^ p) ≤ μ (E ∩ A n) := by
    intro n
    have hsub : E ∩ A n ⊆ closedBall 0 (εn n / 2) := fun x hx => by
      rw [mem_closedBall, dist_zero_right]; exact hx.2.2
    refine le_trans ?_ (D.one_scale hd ha hctop hc μ hμ hε₀.2 hkε (hεn0 n) (hεnle n)
      (hE.inter (hAm n)) hsub)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_const]
    refine setLIntegral_mono' (hE.inter (hAm n)) fun x hx => ?_
    rw [← ENNReal.ofReal_mul (by rw [hc₁]; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hxn : 0 < ‖x‖ := lt_trans (by linarith [hεn0 n]) hx.2.1
    have h1 : 2 * ‖x‖ ≤ εn n := by linarith [hx.2.2]
    have h2 : εn n < 4 * ‖x‖ := by linarith [hx.2.1]
    have := theta_mul_rpow_le (p := p) hxn h1 h2
    rw [hc₁, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hκ₁0
  -- sum over the shells
  have hnull : volume ({0} : Set (Rd d)) = 0 := measure_singleton 0
  calc ENNReal.ofReal (lowerBoundConst d c D.tailConst) * ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ p)
      ≤ ENNReal.ofReal (lowerBoundConst d c D.tailConst) *
          ∫⁻ x in ⋃ n, E ∩ A n, ENNReal.ofReal (‖x‖ ^ p) := by
        refine mul_le_mul' le_rfl ?_
        calc ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ p)
            ≤ ∫⁻ x in (⋃ n, E ∩ A n) ∪ {0}, ENNReal.ofReal (‖x‖ ^ p) := lintegral_mono_set hcover
          _ ≤ (∫⁻ x in ⋃ n, E ∩ A n, ENNReal.ofReal (‖x‖ ^ p)) +
              ∫⁻ x in ({0} : Set (Rd d)), ENNReal.ofReal (‖x‖ ^ p) := lintegral_union_le _ _ _
          _ = ∫⁻ x in ⋃ n, E ∩ A n, ENNReal.ofReal (‖x‖ ^ p) := by
              rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure, add_zero]
    _ = ∑' n, ENNReal.ofReal (lowerBoundConst d c D.tailConst) *
          ∫⁻ x in E ∩ A n, ENNReal.ofReal (‖x‖ ^ p) := by
        rw [lintegral_iUnion (fun n => hE.inter (hAm n)) hdisj, ENNReal.tsum_mul_left]
    _ ≤ ∑' n, μ (E ∩ A n) := ENNReal.tsum_le_tsum hshell
    _ = μ (⋃ n, E ∩ A n) := (measure_iUnion hdisj fun n => hE.inter (hAm n)).symm
    _ ≤ μ E := measure_mono (iUnion_subset fun n => inter_subset_left)

/-! ## The node -/

theorem lowerBoundConst_pos {c Ck : ℝ} (hd : 1 ≤ d) (hc : 0 < c) : 0 < lowerBoundConst d c Ck := by
  have h1 := lowerBoundKappa_pos (d := d) hd hc
  have h2 := lowerBoundTau_pos (d := d) hd hc
  have h3 : 0 < lowerBoundTau d c ^ c := Real.rpow_pos_of_pos h2 c
  have h4 : 0 < min ((2 : ℝ) ^ (c - d)) ((4 : ℝ) ^ (c - d)) :=
    lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  unfold lowerBoundConst
  positivity

/-- **`prop:origin-lower-bound-d`**, `eq:origin-lower-bound` with its constants: for `d ≥ 2`, a
datum with Gaussian coefficient `0` and `0 < c < ∞`, and every law `μ` of it, there is an
`ε₀ ∈ (0,1]` with `k_d(ε₀) ≥ c/2`; for every such `ε₀`, `c₁ > 0` and
`μ(E) ≥ c₁ ∫_E |x|^{c-d} dx` for every Borel `E ⊆ {|x| < ε₀/2}`. -/
theorem origin_lower_bound (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc0 : 0 < D.profileAtOrigin) (hctop : D.profileAtOrigin ≠ ⊤) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) :
    (∃ ε₀ ∈ Ioc (0 : ℝ) 1, D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) ∧
      ∀ ε₀ ∈ Ioc (0 : ℝ) 1, D.profileAtOrigin.toReal / 2 ≤ D.k ε₀ →
        0 < lowerBoundConst d D.profileAtOrigin.toReal D.tailConst ∧
        ∀ E : Set (Rd d), MeasurableSet E → E ⊆ Metric.ball 0 (ε₀ / 2) →
          ENNReal.ofReal (lowerBoundConst d D.profileAtOrigin.toReal D.tailConst) *
              ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ (D.profileAtOrigin.toReal - d)) ≤ μ E := by
  have hc : 0 < D.profileAtOrigin.toReal := ENNReal.toReal_pos hc0.ne' hctop
  refine ⟨?_, fun ε₀ hε₀ hkε => ⟨lowerBoundConst_pos (by omega) hc,
    fun E hE hEb => D.all_scales hd ha hctop hc μ hμ hε₀ hkε hE hEb⟩⟩
  have hβ : ENNReal.ofReal (D.profileAtOrigin.toReal / 2) < D.profileAtOrigin := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hctop]
    exact (ENNReal.ofReal_lt_ofReal_iff hc).mpr (by linarith)
  obtain ⟨rβ, ⟨hr0, hr1⟩, hk⟩ := D.exists_le_k hβ
  exact ⟨rβ / 2, ⟨by positivity, by linarith⟩, hk _ ⟨by positivity, by linarith⟩⟩

/-- From `μ(E) ≥ ∫_E f` on every Borel `E ⊆ B` to `f ≤ g` a.e. on `B`, where
`∫_E g = μ_{ac}(E)` or `μ(E)`. -/
theorem ae_le_of_setLIntegral_le {f g : Rd d → ℝ≥0∞} (hf : Measurable f) {B : Set (Rd d)}
    (hB : MeasurableSet B)
    (h : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ B → ∫⁻ x in E, f x ≤ ∫⁻ x in E, g x) :
    ∀ᵐ x ∂(volume : Measure (Rd d)), x ∈ B → f x ≤ g x := by
  have hae : f ≤ᵐ[volume.restrict B] g := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf fun s hs _ => ?_
    rw [Measure.restrict_restrict hs]
    exact h _ (hs.inter hB) inter_subset_right
  exact (ae_restrict_iff' hB).mp hae

/-- **`prop:origin-lower-bound-d`(1)**: with `ε₀` and `c₁` as in `origin_lower_bound`, the density
`q = dμ_ac/dx` of the absolutely continuous part satisfies `q(x) ≥ c₁|x|^{c-d}` for almost every
`x` with `|x| < ε₀/2`; so does every density of `μ` when it has one; and `|x|^{c-d} → ∞` as
`x → 0` when `c < d`. -/
theorem origin_lower_bound_density (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc0 : 0 < D.profileAtOrigin) (hctop : D.profileAtOrigin ≠ ⊤) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioc (0 : ℝ) 1)
    (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) :
    (∀ᵐ x ∂(volume : Measure (Rd d)), ‖x‖ < ε₀ / 2 →
        ENNReal.ofReal (lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
          ‖x‖ ^ (D.profileAtOrigin.toReal - d)) ≤ μ.rnDeriv volume x) ∧
      (∀ q : Rd d → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
        ∀ᵐ x ∂(volume : Measure (Rd d)), ‖x‖ < ε₀ / 2 →
          lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
            ‖x‖ ^ (D.profileAtOrigin.toReal - d) ≤ q x) ∧
      (D.profileAtOrigin.toReal < d →
        Tendsto (fun x : Rd d => ‖x‖ ^ (D.profileAtOrigin.toReal - d)) (𝓝[≠] 0) atTop) := by
  haveI := hμ.1
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hc : 0 < D.profileAtOrigin.toReal := ENNReal.toReal_pos hc0.ne' hctop
  set c := D.profileAtOrigin.toReal with hcdef
  set c₁ := lowerBoundConst d c D.tailConst with hc₁
  have hc₁0 : 0 < c₁ := lowerBoundConst_pos (by omega) hc
  set B := ball (0 : Rd d) (ε₀ / 2) with hB
  have hBm : MeasurableSet B := measurableSet_ball
  set f : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (c₁ * ‖x‖ ^ (c - d)) with hf
  have hfm : Measurable f := by
    simp only [hf]
    exact (measurable_const.mul (continuous_norm.measurable.pow_const _)).ennreal_ofReal
  -- the bound in integrated form
  have hbound : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ B → ∫⁻ x in E, f x ≤ μ E := by
    intro E hE hEB
    have h := D.all_scales hd ha hctop hc μ hμ hε₀ hkε hE hEB
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    refine le_trans (le_of_eq (setLIntegral_congr_fun hE fun x _ => ?_)) h
    simp only [hf]
    rw [ENNReal.ofReal_mul hc₁0.le]
  have hmemB : ∀ x : Rd d, ‖x‖ < ε₀ / 2 ↔ x ∈ B := fun x => by simp [hB]
  refine ⟨?_, ?_, ?_⟩
  · -- the absolutely continuous part, through the Lebesgue decomposition
    obtain ⟨N, hNm, hsN, hvN⟩ := Measure.mutuallySingular_singularPart μ volume
    have hdec := Measure.haveLebesgueDecomposition_add μ volume
    have h := ae_le_of_setLIntegral_le hfm hBm (g := μ.rnDeriv volume) fun E hE hEB => by
      calc ∫⁻ x in E, f x = ∫⁻ x in E ∩ N, f x := by
            refine setLIntegral_congr ?_
            refine (ae_eq_set.mpr ⟨?_, ?_⟩).symm
            · rw [sdiff_eq_empty.mpr inter_subset_left]; exact measure_empty
            · exact measure_mono_null (fun x hx hxN => hx.2 ⟨hx.1, hxN⟩) hvN
        _ ≤ μ (E ∩ N) := hbound _ (hE.inter hNm) (inter_subset_left.trans hEB)
        _ = μ.singularPart volume (E ∩ N) + volume.withDensity (μ.rnDeriv volume) (E ∩ N) := by
            conv_lhs => rw [hdec]
            rfl
        _ = ∫⁻ x in E ∩ N, μ.rnDeriv volume x := by
            rw [measure_mono_null inter_subset_right hsN, zero_add,
              withDensity_apply _ (hE.inter hNm)]
        _ ≤ ∫⁻ x in E, μ.rnDeriv volume x := lintegral_mono_set inter_subset_left
    filter_upwards [h] with x hx hxB
    exact hx ((hmemB x).mp hxB)
  · -- every density
    intro q hq
    have h := ae_le_of_setLIntegral_le hfm hBm (g := fun x => ENNReal.ofReal (q x))
      fun E hE hEB => by
        have := hbound E hE hEB
        rwa [hq, withDensity_apply _ hE] at this
    have hne : ∀ᵐ x ∂(volume : Measure (Rd d)), x ≠ 0 := by
      rw [ae_iff]; simp only [ne_eq, not_not, setOf_eq_eq_singleton]; exact measure_singleton 0
    filter_upwards [h, hne] with x hx hx0 hxB
    have hle := hx ((hmemB x).mp hxB)
    simp only [hf] at hle
    have hpos : 0 < c₁ * ‖x‖ ^ (c - d) :=
      mul_pos hc₁0 (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) _)
    rcases (ENNReal.ofReal_le_ofReal_iff' ).mp hle with h1 | h1
    · exact h1
    · linarith
  · -- the blow-up
    intro hcd
    exact (tendsto_rpow_neg_nhdsGT_zero (by linarith)).comp tendsto_norm_nhdsNE_zero

/-- **`prop:origin-lower-bound-d`(2)**: with `ε₀` and `c₁` as in `origin_lower_bound`,
`μ({|x| < r}) ≥ c₁ |S^{d-1}| c⁻¹ r^c` for `0 < r ≤ ε₀/2`. -/
theorem origin_lower_bound_ball (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc0 : 0 < D.profileAtOrigin) (hctop : D.profileAtOrigin ≠ ⊤) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioc (0 : ℝ) 1)
    (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) {r : ℝ} (hr : r ∈ Ioc 0 (ε₀ / 2)) :
    ENNReal.ofReal (lowerBoundConst d D.profileAtOrigin.toReal D.tailConst * sphereArea d /
        D.profileAtOrigin.toReal * r ^ D.profileAtOrigin.toReal) ≤ μ (Metric.ball 0 r) := by
  have hd1 : 1 ≤ d := by omega
  have hc : 0 < D.profileAtOrigin.toReal := ENNReal.toReal_pos hc0.ne' hctop
  set c := D.profileAtOrigin.toReal with hcdef
  set c₁ := lowerBoundConst d c D.tailConst with hc₁
  have hc₁0 : 0 < c₁ := lowerBoundConst_pos hd1 hc
  have hA := (sphereArea_eq_toSphere hd1).2
  have h := D.all_scales hd ha hctop hc μ hμ hε₀ hkε (measurableSet_ball (x := 0) (ε := r))
    (ball_subset_ball hr.2)
  refine le_trans (le_of_eq ?_) h
  -- `∫_{|x|<r} |x|^{c-d} dx = |S^{d-1}| r^c/c`
  have hmeas :
      Measurable fun t : ℝ => (Iio r).indicator (fun t => ENNReal.ofReal (t ^ (c - d))) t :=
    (measurable_id.pow_const _).ennreal_ofReal.indicator measurableSet_Iio
  have hint : ∫⁻ x in ball (0 : Rd d) r, ENNReal.ofReal (‖x‖ ^ (c - d))
      = ∫⁻ x : Rd d, (Iio r).indicator (fun t => ENNReal.ofReal (t ^ (c - d))) ‖x‖ := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun x => ?_
    by_cases hx : ‖x‖ < r
    · rw [indicator_of_mem (show x ∈ ball (0 : Rd d) r by simpa using hx),
        indicator_of_mem (show ‖x‖ ∈ Iio r from hx)]
    · rw [indicator_of_notMem (show x ∉ ball (0 : Rd d) r by simpa using hx),
        indicator_of_notMem (show ‖x‖ ∉ Iio r from hx)]
  have hrad : ∫⁻ t in Ioi (0 : ℝ), (Iio r).indicator (fun t => ENNReal.ofReal (t ^ (c - d))) t *
      ENNReal.ofReal (t ^ (d - 1)) = ENNReal.ofReal (r ^ c / c) := by
    have hpow : IntegrableOn (fun t : ℝ => t ^ (c - 1)) (Ioc 0 r) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (r := c - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1.le).mp this
    calc ∫⁻ t in Ioi (0 : ℝ), (Iio r).indicator (fun t => ENNReal.ofReal (t ^ (c - d))) t *
          ENNReal.ofReal (t ^ (d - 1))
        = ∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (t ^ (c - 1)) := by
          rw [← setLIntegral_congr Ioo_ae_eq_Ioc, ← lintegral_indicator measurableSet_Ioo,
            ← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun t => ?_
          by_cases ht : t ∈ Ioo (0 : ℝ) r
          · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1),
              indicator_of_mem (show t ∈ Iio r from ht.2), ← ENNReal.ofReal_mul
              (Real.rpow_nonneg ht.1.le _), pow_pred_eq_rpow hd1 ht.1, ← Real.rpow_add ht.1]
            congr 2; ring
          · rw [indicator_of_notMem ht]
            by_cases ht0 : t ∈ Ioi (0 : ℝ)
            · rw [indicator_of_mem ht0, indicator_of_notMem (show t ∉ Iio r from
                fun h => ht ⟨ht0, h⟩), zero_mul]
            · rw [indicator_of_notMem ht0]
      _ = ENNReal.ofReal (r ^ c / c) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hpow ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun t ht => Real.rpow_nonneg ht.1.le _)),
            ← intervalIntegral.integral_of_le hr.1.le, integral_rpow (Or.inl (by linarith)),
            sub_add_cancel, Real.zero_rpow hc.ne', sub_zero]
  rw [hint, lintegral_radial hd1 _ hmeas, hrad, ← ENNReal.ofReal_mul hA.le,
    ← ENNReal.ofReal_mul hc₁0.le]
  congr 1
  field_simp

end AffineHemigroup
