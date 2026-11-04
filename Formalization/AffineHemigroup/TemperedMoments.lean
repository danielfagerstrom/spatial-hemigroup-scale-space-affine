/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.TemperedStepCone
import AffineHemigroup.OriginLowerBound
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# `prop:tempered-moments`: exponential moments of the tempered orbits

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:tempered-moments`
(`prop:tempered-step-cone`(2); wave 2, group D, Q-0281). Spends nothing: the compound Poisson laws
`π_ε` of the Lévy measure restricted to `{|x| > ε}` are built by hand (`cpLaw`), their transforms
tend to `μ̂_I` as `ε ↓ 0`, so they tend to `μ_I` weakly (Mathlib's Lévy continuity theorem), and the
exponential moment `∫ e^{⟨θ,x⟩} dπ_ε = exp ∫_{|x|>ε} (cosh⟨θ,x⟩ - 1) m(|x|) dx` is bounded uniformly
in `ε`; a weak limit keeps the bound (truncate `e^{⟨θ,x⟩}` at `N`, then monotone convergence).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter ProbabilityTheory
open ScaleSpace (convPow isFiniteMeasure_convPow_Rd)
open scoped Topology ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

variable {d : ℕ}

/-! ## Exponential moments of a compound Poisson law on `ℝ^d` -/

/-- `∫ e^{⟨θ,x⟩} L^{*n}(dx) = (∫ e^{⟨θ,x⟩} L(dx))ⁿ`. -/
theorem lintegral_exp_inner_convPow (L : Measure (Rd d)) [IsFiniteMeasure L] (θ : Rd d)
    (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(convPow L n) =
      (∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L) ^ n := by
  have hmeas : Measurable fun x : Rd d => ENNReal.ofReal (Real.exp ⟪θ, x⟫) := by fun_prop
  induction n with
  | zero => simp [convPow, lintegral_dirac' _ hmeas]
  | succ n ih =>
    haveI := isFiniteMeasure_convPow_Rd L n
    rw [convPow, Measure.conv, lintegral_map hmeas measurable_add, pow_succ, ← ih,
      ← lintegral_prod_mul hmeas.aemeasurable hmeas.aemeasurable]
    congr 1
    ext p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, inner_add_right]

/-- **The exponential moment of a compound Poisson law**: if `∫ e^{⟨θ,x⟩} L(dx) = c`, then
`∫ e^{⟨θ,x⟩} π_L(dx) = e^{-L(ℝ^d)} e^{c}`. -/
theorem lintegral_exp_inner_cpLaw (L : Measure (Rd d)) [IsFiniteMeasure L] (θ : Rd d) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L = ENNReal.ofReal c) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(cpLaw L) =
      ENNReal.ofReal (Real.exp (-(L univ).toReal) * Real.exp c) := by
  rw [cpLaw, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_exp_inner_convPow, hc]
  exact tsum_poisson_mul_pow _ hc0

/-! ## A weak limit keeps an exponential moment bound -/

/-- **Lower semicontinuity of an exponential moment**: if probability measures `Pₙ → Q` weakly and
`∫ e^{⟨θ,x⟩} dPₙ ≤ B` for every `n`, then `∫ e^{⟨θ,x⟩} dQ ≤ B`. Mathlib types only. -/
theorem lintegral_exp_inner_le_of_tendsto {P : ℕ → ProbabilityMeasure (Rd d)}
    {Q : ProbabilityMeasure (Rd d)} (hlim : Tendsto P atTop (𝓝 Q)) (θ : Rd d) {B : ℝ≥0∞}
    (hB : ∀ n, ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(P n : Measure (Rd d)) ≤ B) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(Q : Measure (Rd d)) ≤ B := by
  set g : ℕ → Rd d → ℝ≥0 := fun N x => min (Real.toNNReal (Real.exp ⟪θ, x⟫)) (N : ℝ≥0) with hg
  have hgc : ∀ N, Continuous (g N) := fun N => by
    simp only [hg]; fun_prop
  have hgb : ∀ N (x y : Rd d), dist (g N x) (g N y) ≤ N := by
    intro N x y
    rw [NNReal.dist_eq]
    have h1 : ((g N x : ℝ≥0) : ℝ) ≤ N := by exact_mod_cast min_le_right _ _
    have h2 : ((g N y : ℝ≥0) : ℝ) ≤ N := by exact_mod_cast min_le_right _ _
    have h3 : (0 : ℝ) ≤ g N x := (g N x).2
    have h4 : (0 : ℝ) ≤ g N y := (g N y).2
    rw [abs_sub_le_iff]
    constructor <;> linarith
  set f : ℕ → Rd d →ᵇ ℝ≥0 := fun N =>
    BoundedContinuousFunction.mkOfBound ⟨g N, hgc N⟩ N (hgb N) with hf
  have hle : ∀ N x, ((f N x : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ⟪θ, x⟫) := by
    intro N x
    change ((min (Real.toNNReal (Real.exp ⟪θ, x⟫)) (N : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤ _
    rw [ENNReal.ofReal]
    exact_mod_cast min_le_left _ _
  have hfN : ∀ N, ∫⁻ x, (f N x : ℝ≥0∞) ∂(Q : Measure (Rd d)) ≤ B := fun N =>
    le_of_tendsto' ((ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hlim) (f N))
      fun n => (lintegral_mono fun x => hle N x).trans (hB n)
  have hmono : ∀ x, Monotone fun N => ((f N x : ℝ≥0) : ℝ≥0∞) := by
    intro x N M hNM
    change ((min (Real.toNNReal (Real.exp ⟪θ, x⟫)) (N : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
      ((min (Real.toNNReal (Real.exp ⟪θ, x⟫)) (M : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
    exact_mod_cast min_le_min_left _ (by exact_mod_cast hNM)
  have htend : ∀ x, Tendsto (fun N => ((f N x : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp ⟪θ, x⟫))) := by
    intro x
    obtain ⟨N0, hN0⟩ := exists_nat_ge (Real.toNNReal (Real.exp ⟪θ, x⟫))
    refine tendsto_atTop_of_eventually_const (i₀ := N0) fun N hN => ?_
    change ((min (Real.toNNReal (Real.exp ⟪θ, x⟫)) (N : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = _
    rw [min_eq_left (hN0.trans (by exact_mod_cast hN)), ENNReal.ofReal]
  have hlimN := lintegral_tendsto_of_tendsto_of_monotone (μ := (Q : Measure (Rd d)))
    (f := fun N x => ((f N x : ℝ≥0) : ℝ≥0∞))
    (fun N => ((f N).continuous.measurable.coe_nnreal_ennreal).aemeasurable)
    (Eventually.of_forall hmono) (Eventually.of_forall htend)
  exact le_of_tendsto' hlimN hfN

/-! ## The truncated Lévy measures of a radial profile -/

namespace RadialProfile

/-- The density of `m(|x|)dx` restricted to `{|x| > ε}`, in `ℝ≥0∞`. -/
noncomputable def truncDens (K : RadialProfile d) (ε : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioi ε).indicator fun r => ENNReal.ofReal (K.m r)

/-- **The Lévy measure `m(|x|)dx` restricted to `{|x| > ε}`**. -/
noncomputable def truncLevy (K : RadialProfile d) (ε : ℝ) : Measure (Rd d) :=
  volume.withDensity fun x => K.truncDens ε ‖x‖

theorem measurable_truncDens_norm (hd : 1 ≤ d) (K : RadialProfile d) (ε : ℝ) :
    Measurable fun x : Rd d => K.truncDens ε ‖x‖ := by
  have h : (fun x : Rd d => K.truncDens ε ‖x‖) =
      {x : Rd d | ε < ‖x‖}.indicator fun x => ENNReal.ofReal (K.m ‖x‖) := by
    funext x
    simp only [truncDens, indicator, mem_Ioi, mem_setOf_eq]
  rw [h]
  exact ((K.measurable_m_norm hd).ennreal_ofReal).indicator
    (measurableSet_lt measurable_const continuous_norm.measurable)

theorem truncLevy_univ_ne_top (hd : 1 ≤ d) (K : RadialProfile d) {ε : ℝ} (hε : 0 < ε) :
    K.truncLevy ε univ ≠ ⊤ := by
  rw [truncLevy, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  set c := min (ε ^ 2) 1 with hc
  have hc0 : 0 < c := lt_min (by positivity) one_pos
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := c⁻¹)) K.integrable)
    ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  simp only [truncDens, indicator, mem_Ioi]
  split_ifs with h
  · rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin : c ≤ min (‖x‖ ^ 2) 1 := min_le_min (by nlinarith) le_rfl
    have hm : 0 ≤ K.k ‖x‖ / ‖x‖ ^ d := K.m_nonneg hd (norm_nonneg _)
    rw [RadialProfile.m]
    calc K.k ‖x‖ / ‖x‖ ^ d = c⁻¹ * (c * (K.k ‖x‖ / ‖x‖ ^ d)) := by field_simp
      _ ≤ c⁻¹ * (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) := by gcongr
  · exact bot_le

theorem isFiniteMeasure_truncLevy (hd : 1 ≤ d) (K : RadialProfile d) {ε : ℝ} (hε : 0 < ε) :
    IsFiniteMeasure (K.truncLevy ε) :=
  ⟨lt_top_iff_ne_top.2 (K.truncLevy_univ_ne_top hd hε)⟩

theorem truncLevy_symm (K : RadialProfile d) (ε : ℝ) :
    (K.truncLevy ε).map (fun x => -x) = K.truncLevy ε := by
  have h := withDensity_radial_map_isometry (K.truncDens ε) (LinearIsometryEquiv.neg ℝ (E := Rd d))
  simpa [truncLevy] using h

/-- `∫ f dL_ε = ∫_{|x|>ε} f(x) m(|x|) dx` for measurable `f ≥ 0`. -/
theorem lintegral_truncLevy (hd : 1 ≤ d) (K : RadialProfile d) (ε : ℝ) {f : Rd d → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(K.truncLevy ε) = ∫⁻ x, K.truncDens ε ‖x‖ * f x := by
  rw [truncLevy, lintegral_withDensity_eq_lintegral_mul _ (K.measurable_truncDens_norm hd ε) hf]
  rfl

end RadialProfile

namespace RadialProfile

/-- **The transform of `π_ε`**: `π̂_ε(ω) = exp(-∫_{|x|>ε} (1 - cos⟨x,ω⟩) m(|x|) dx)`. -/
theorem charFun_cpLaw_truncLevy (hd : 1 ≤ d) (K : RadialProfile d) {ε : ℝ} (hε : 0 < ε)
    (ω : Rd d) :
    haveI := K.isFiniteMeasure_truncLevy hd hε
    charFun (cpLaw (K.truncLevy ε)) ω = ((Real.exp (-(∫⁻ x, K.truncDens ε ‖x‖ *
      ENNReal.ofReal (1 - Real.cos ⟪x, ω⟫)).toReal) : ℝ) : ℂ) := by
  haveI := K.isFiniteMeasure_truncLevy hd hε
  set L := K.truncLevy ε with hL
  have hc : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪x, ω⟫ := fun x => by linarith [Real.cos_le_one ⟪x, ω⟫]
  have hcos : Integrable (fun x : Rd d => Real.cos ⟪x, ω⟫) L :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪x, ω⟫) L :=
    (integrable_const _).sub hcos
  have h1 : (∫⁻ x, K.truncDens ε ‖x‖ * ENNReal.ofReal (1 - Real.cos ⟪x, ω⟫)).toReal =
      (L univ).toReal - ∫ x, Real.cos ⟪x, ω⟫ ∂L := by
    rw [← K.lintegral_truncLevy hd ε (by fun_prop), ← hL,
      ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hc) hint.aestronglyMeasurable,
      integral_sub (integrable_const _) hcos, integral_const, smul_eq_mul, mul_one,
      measureReal_def]
  rw [charFun_cpLaw, charFun_of_symm L (K.truncLevy_symm ε) ω, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, ← Real.exp_add, h1]
  congr 2
  ring

/-- **`π_ε → μ_I` in transform** as `ε = 1/(n+1) ↓ 0`, by monotone convergence. -/
theorem tendsto_charFun_cpLaw_truncLevy (hd : 1 ≤ d) (K : RadialProfile d) (ω : Rd d) :
    Tendsto (fun n : ℕ => ((Real.exp (-(∫⁻ x, K.truncDens (1 / ((n : ℝ) + 1)) ‖x‖ *
      ENNReal.ofReal (1 - Real.cos ⟪x, ω⟫)).toReal) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-K.exponent ω) : ℝ) : ℂ)) := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεanti : Antitone ε := fun n m hnm => by
    simp only [hε]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  set F : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.m ‖x‖) with hF
  have hlim : Tendsto (fun n => ∫⁻ x, K.truncDens (ε n) ‖x‖ *
      ENNReal.ofReal (1 - Real.cos ⟪x, ω⟫)) atTop (𝓝 (∫⁻ x, F x)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((K.measurable_truncDens_norm hd _).mul (by fun_prop)).aemeasurable)
      (Eventually.of_forall fun x n m hnm => ?_) (Eventually.of_forall fun x => ?_)
    · refine mul_le_mul_left ?_ _
      exact indicator_le_indicator_of_subset (Ioi_subset_Ioi (hεanti hnm)) (fun _ => bot_le) _
    · rcases eq_or_ne x 0 with rfl | hx
      · simp [hF]
      · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        have hlt : ε n < ‖x‖ := lt_of_le_of_lt (hεanti hn) hN
        have hc : 0 ≤ 1 - Real.cos ⟪x, ω⟫ := by linarith [Real.cos_le_one ⟪x, ω⟫]
        simp only [RadialProfile.truncDens, indicator_of_mem (show ‖x‖ ∈ Ioi (ε n) from hlt), hF]
        rw [← ENNReal.ofReal_mul (K.m_nonneg hd (norm_nonneg _)), real_inner_comm, mul_comm]
  have hne : ∫⁻ x, F x ≠ ⊤ := K.exponentL_ne_top hd ω
  have h2 := (ENNReal.tendsto_toReal hne).comp hlim
  have h3 := ((Complex.continuous_ofReal.comp Real.continuous_exp).tendsto _).comp h2.neg
  exact h3

/-- **The exponential moments of `π_ε` are bounded uniformly in `ε`**:
`∫ e^{⟨θ,x⟩} dπ_ε ≤ exp M`, `M = ∫ (cosh⟨θ,x⟩ - 1) m(|x|) dx`, when `M < ∞`. -/
theorem lintegral_exp_inner_cpLaw_truncLevy_le (hd : 1 ≤ d) (K : RadialProfile d) {ε : ℝ}
    (hε : 0 < ε) (θ : Rd d)
    (hM : ∫⁻ x, ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖) ≠ ⊤) :
    haveI := K.isFiniteMeasure_truncLevy hd hε
    ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(cpLaw (K.truncLevy ε)) ≤
      ENNReal.ofReal (Real.exp (∫⁻ x, ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) *
        K.m ‖x‖)).toReal) := by
  haveI := K.isFiniteMeasure_truncLevy hd hε
  set L := K.truncLevy ε with hL
  set M := ∫⁻ x, ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖) with hMdef
  have hexpm : Measurable fun x : Rd d => ENNReal.ofReal (Real.exp ⟪θ, x⟫) := by fun_prop
  -- the symmetry turns `e^{⟨θ,x⟩}` into `cosh⟨θ,x⟩`
  have hsym : ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-⟪θ, x⟫)) ∂L := by
    have hs := K.truncLevy_symm ε
    rw [← hL] at hs
    conv_lhs => rw [← hs]
    rw [lintegral_map hexpm (by fun_prop)]
    simp_rw [inner_neg_right]
  have hcosh : ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L =
      ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪θ, x⟫) ∂L := by
    have h2 : (2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L =
        2 * ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪θ, x⟫) ∂L := by
      rw [two_mul]
      conv_lhs => arg 2; rw [hsym]
      rw [← lintegral_add_left hexpm, ← lintegral_const_mul _ (by fun_prop)]
      have h2c : ∀ c : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal c = ENNReal.ofReal (2 * c) := fun c => by
        rw [ENNReal.ofReal_mul zero_le_two]; norm_num
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, h2c, Real.cosh_eq]
      congr 1
      ring
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h2
  -- `∫ cosh dL = L(ℝ^d) + ∫ (cosh - 1) dL ≤ L(ℝ^d) + M`
  have hsplit : ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪θ, x⟫) ∂L =
      L univ + ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪θ, x⟫ - 1) ∂L := by
    rw [← lintegral_one, ← lintegral_add_left measurable_const]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (by linarith [Real.one_le_cosh ⟪θ, x⟫])]
    congr 1
    ring
  have hle : ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪θ, x⟫ - 1) ∂L ≤ M := by
    rw [hL, K.lintegral_truncLevy hd ε (by fun_prop), hMdef]
    refine lintegral_mono fun x => ?_
    have h1 : K.truncDens ε ‖x‖ ≤ ENNReal.ofReal (K.m ‖x‖) := by
      unfold RadialProfile.truncDens
      exact indicator_le_self' (fun _ _ => bot_le) _
    calc K.truncDens ε ‖x‖ * ENNReal.ofReal (Real.cosh ⟪θ, x⟫ - 1)
        ≤ ENNReal.ofReal (K.m ‖x‖) * ENNReal.ofReal (Real.cosh ⟪θ, x⟫ - 1) := by gcongr
      _ = ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖) := by
          rw [← ENNReal.ofReal_mul (K.m_nonneg hd (norm_nonneg _)), mul_comm]
  set A := ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂L with hA
  have hLfin : L univ ≠ ⊤ := measure_ne_top L univ
  have hAle : A ≤ L univ + M := (hcosh.trans hsplit).trans_le (add_le_add le_rfl hle)
  have hAfin : A ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hLfin, hM⟩) hAle
  rw [lintegral_exp_inner_cpLaw L θ ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hAfin).symm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hAr : A.toReal ≤ (L univ).toReal + M.toReal := by
    rw [← ENNReal.toReal_add hLfin hM]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hLfin, hM⟩) hAle
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

end RadialProfile

/-- `cosh s - 1 ≤ (s²/2) e^{s²/2}`. -/
theorem cosh_sub_one_le (s : ℝ) : Real.cosh s - 1 ≤ s ^ 2 / 2 * Real.exp (s ^ 2 / 2) := by
  have h1 := Real.cosh_le_exp_half_sq s
  have h2 := Real.add_one_le_exp (-(s ^ 2 / 2))
  have h3 : Real.exp (-(s ^ 2 / 2)) * Real.exp (s ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 ≤ s ^ 2 / 2 := by positivity
  nlinarith [Real.exp_pos (s ^ 2 / 2)]

/-- `cosh s ≤ e^{|s|}`. -/
theorem cosh_le_exp_abs (s : ℝ) : Real.cosh s ≤ Real.exp |s| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp s ≤ Real.exp |s| := Real.exp_le_exp.2 (le_abs_self s)
  have h2 : Real.exp (-s) ≤ Real.exp |s| := Real.exp_le_exp.2 (neg_le_abs s)
  linarith

/-- **`M = ∫ (cosh⟨θ,x⟩ - 1) m(|x|) dx < ∞`** for `|θ| ≤ β` when
`∫₁^∞ e^{βr} r^{-1-α} j(r) dr < ∞`: near the origin `cosh s - 1 ≤ (s²/2)e^{s²/2}`, away from it
`cosh s ≤ e^{β|x|}` and polar coordinates. -/
theorem lintegral_cosh_sub_one_ne_top (hd : 1 ≤ d) (K : RadialProfile d) {α β : ℝ} (j : ℝ → ℝ)
    (hK : ∀ r : ℝ, 0 < r → K.k r = r ^ (-α) * j r)
    (hmom : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (β * r) * r ^ (-1 - α) * j r) ≠ ⊤)
    {θ : Rd d} (hθ : ‖θ‖ ≤ β) :
    ∫⁻ x, ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖) ≠ ⊤ := by
  have hβ : 0 ≤ β := (norm_nonneg θ).trans hθ
  set C₁ := β ^ 2 / 2 * Real.exp (β ^ 2 / 2) with hC₁
  set kI := (Ioi (0 : ℝ)).indicator K.k with hkI
  have hkIm : Measurable kI := measurable_indicator_Ioi_of_antitoneOn K.k_antitone
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((Ioi (1 : ℝ)).indicator
    (fun r => Real.exp (β * r) * (kI r / r ^ d)) r) with hg
  have hgm : Measurable g :=
    ((((by fun_prop : Measurable fun r : ℝ => Real.exp (β * r)).mul
      (hkIm.div (by fun_prop))).indicator measurableSet_Ioi)).ennreal_ofReal
  -- the pointwise bound
  have hpt : ∀ x : Rd d, ENNReal.ofReal ((Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖) ≤
      ENNReal.ofReal C₁ * ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) + g ‖x‖ := by
    intro x
    have hm := K.m_nonneg hd (norm_nonneg x)
    have hs : |⟪θ, x⟫| ≤ β * ‖x‖ :=
      (abs_real_inner_le_norm θ x).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
    have hc1 : 0 ≤ Real.cosh ⟪θ, x⟫ - 1 := by linarith [Real.one_le_cosh ⟪θ, x⟫]
    rcases le_or_gt ‖x‖ 1 with h1 | h1
    · refine le_add_right ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [min_eq_left (by nlinarith [norm_nonneg x]), ← RadialProfile.m]
      have hs2 : ⟪θ, x⟫ ^ 2 ≤ β ^ 2 * ‖x‖ ^ 2 := by
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hs 2
      have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
      have hs3 : ⟪θ, x⟫ ^ 2 ≤ β ^ 2 := hs2.trans (mul_le_of_le_one_right (sq_nonneg β) hx2)
      have hb : Real.cosh ⟪θ, x⟫ - 1 ≤ C₁ * ‖x‖ ^ 2 := by
        refine (cosh_sub_one_le _).trans ?_
        rw [hC₁]
        have he : Real.exp (⟪θ, x⟫ ^ 2 / 2) ≤ Real.exp (β ^ 2 / 2) :=
          Real.exp_le_exp.2 (by linarith)
        calc ⟪θ, x⟫ ^ 2 / 2 * Real.exp (⟪θ, x⟫ ^ 2 / 2)
            ≤ β ^ 2 * ‖x‖ ^ 2 / 2 * Real.exp (β ^ 2 / 2) := by
              gcongr
          _ = β ^ 2 / 2 * Real.exp (β ^ 2 / 2) * ‖x‖ ^ 2 := by ring
      calc (Real.cosh ⟪θ, x⟫ - 1) * K.m ‖x‖ ≤ C₁ * ‖x‖ ^ 2 * K.m ‖x‖ :=
            mul_le_mul_of_nonneg_right hb hm
        _ = C₁ * (‖x‖ ^ 2 * K.m ‖x‖) := by ring
    · refine le_add_left ?_
      have hx0 : 0 < ‖x‖ := by linarith
      simp only [hg, indicator_of_mem (show ‖x‖ ∈ Ioi (1 : ℝ) from h1), hkI,
        indicator_of_mem (show ‖x‖ ∈ Ioi (0 : ℝ) from hx0)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← RadialProfile.m]
      have hb : Real.cosh ⟪θ, x⟫ - 1 ≤ Real.exp (β * ‖x‖) :=
        (sub_le_self _ zero_le_one).trans ((cosh_le_exp_abs _).trans (Real.exp_le_exp.2 hs))
      exact mul_le_mul_of_nonneg_right hb hm
  have hmeas1 : Measurable fun x : Rd d =>
      ENNReal.ofReal C₁ * ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) :=
    measurable_const.mul (((by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).mul
      (K.measurable_m_norm hd)).ennreal_ofReal)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left hmeas1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top K.integrable, ?_⟩
  rw [lintegral_radial hd g hgm]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top hmom ?_)
  have h0 : ∫⁻ r in Ioc (0 : ℝ) 1, g r * ENNReal.ofReal (r ^ (d - 1)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) fun r hr => by
      simp only [hg, indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from not_lt.2 hr.2),
        ENNReal.ofReal_zero, zero_mul]]
    exact lintegral_zero
  have h1 : ∫⁻ r in Ioi (1 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1)) =
      ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (β * r) * r ^ (-1 - α) * j r) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr1 : (1 : ℝ) < r := hr
    have hr0 : (0 : ℝ) < r := by linarith
    simp only [hg, indicator_of_mem hr, hkI, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr0)]
    rw [← ENNReal.ofReal_mul (by
      have := K.k_nonneg r hr0
      positivity)]
    congr 1
    have hpow : r ^ d = r ^ (d - 1) * r := by rw [← pow_succ]; congr 1; omega
    have hrp : r ^ (-1 - α) = r ^ (-α) / r := by
      rw [show -1 - α = -α - 1 by ring, Real.rpow_sub_one hr0.ne']
    rw [hK r hr0, hrp, hpow]
    field_simp
  calc ∫⁻ r in Ioi (0 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1))
      ≤ ∫⁻ r in Ioc (0 : ℝ) 1 ∪ Ioi 1, g r * ENNReal.ofReal (r ^ (d - 1)) :=
        lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ r in Ioc (0 : ℝ) 1, g r * ENNReal.ofReal (r ^ (d - 1))) +
          ∫⁻ r in Ioi (1 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1)) := lintegral_union_le _ _ _
    _ = _ := by rw [h0, h1, zero_add]

/-! ## `prop:tempered-moments` -/

/-- **`prop:tempered-moments`** (`prop:tempered-step-cone`(2)): if `β > 0` and
`∫₁^∞ e^{βr} r^{-1-α} j(r) dr < ∞`, then `∫ e^{⟨θ,x⟩} μ_Σ(dx) < ∞` for every `Σ ∈ PD(d)` and every
`θ` with `|Σ^{1/2}θ| ≤ β`. -/
theorem tempered_exponential_moments (hd : 1 ≤ d) {α : ℝ} (_hα0 : 0 < α) (_hα2 : α < 2)
    (j : ℝ → ℝ) (_hj : IsTemperingProfile j) (β : ℝ) (_hβ : 0 < β)
    (hmom : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (β * r) * r ^ (-1 - α) * j r) ≠ ⊤)
    (K : RadialProfile d) (hK : ∀ r : ℝ, 0 < r → K.k r = r ^ (-α) * j r) (μI : Measure (Rd d))
    (hμI : IsProfileLaw K μI) :
    ∀ S : Mat d, S.PosDef → ∀ θ : Rd d, ‖lin (msqrt S) θ‖ ≤ β →
      ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(affineOrbit μI S) ≠ ⊤ := by
  intro S hS θ hθ
  haveI := hμI.1
  set θ' := lin (msqrt S) θ with hθ'
  -- the orbit's moment at `θ` is `μ_I`'s at `Σ^{1/2}θ`
  have hmap : ∫⁻ x, ENNReal.ofReal (Real.exp ⟪θ, x⟫) ∂(affineOrbit μI S) =
      ∫⁻ y, ENNReal.ofReal (Real.exp ⟪θ', y⟫) ∂μI := by
    rw [affineOrbit, push, lintegral_map (by fun_prop) (lin (msqrt S)).continuous.measurable]
    refine lintegral_congr fun y => ?_
    rw [real_inner_comm, inner_lin_left, msqrt_transpose, real_inner_comm]
  rw [hmap]
  -- the compound Poisson approximations `π_ε`, `ε = 1/(n+1)`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  haveI hfin : ∀ n, IsFiniteMeasure (K.truncLevy (ε n)) := fun n =>
    K.isFiniteMeasure_truncLevy hd (hεpos n)
  let P : ℕ → ProbabilityMeasure (Rd d) := fun n => ⟨cpLaw (K.truncLevy (ε n)), inferInstance⟩
  let Q : ProbabilityMeasure (Rd d) := ⟨μI, hμI.1⟩
  have hlim : Tendsto P atTop (𝓝 Q) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ω => ?_
    have h1 : (fun n => charFun (P n : Measure (Rd d)) ω) = fun n : ℕ =>
        ((Real.exp (-(∫⁻ x, K.truncDens (1 / ((n : ℝ) + 1)) ‖x‖ *
          ENNReal.ofReal (1 - Real.cos ⟪x, ω⟫)).toReal) : ℝ) : ℂ) := by
      funext n
      exact K.charFun_cpLaw_truncLevy hd (hεpos n) ω
    have h2 : charFun (Q : Measure (Rd d)) ω = ((Real.exp (-K.exponent ω) : ℝ) : ℂ) := hμI.2 ω
    rw [h1, h2]
    exact K.tendsto_charFun_cpLaw_truncLevy hd ω
  have hM := lintegral_cosh_sub_one_ne_top hd K j hK hmom (θ := θ') hθ
  have hB := lintegral_exp_inner_le_of_tendsto hlim θ' fun n =>
    K.lintegral_exp_inner_cpLaw_truncLevy_le hd (hεpos n) θ' hM
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB

end AffineHemigroup
