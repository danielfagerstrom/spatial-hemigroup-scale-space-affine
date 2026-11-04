/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StageAtom
import AffineHemigroup.LineLevyUnique
import AffineHemigroup.OriginBoundedness

/-!
# `prop:isotropic-stage-density`: a stage is infinitely divisible; the stages with a density

Blueprint: `blueprint/src/parts/03-isotropic.tex`. Q-0447 (the statements were typed in Q-0434).

A stage `μ_{s,t}`, `0 < s < t`, of a family with the display of a gauge `χ` and the exponent of a
datum `(a, k_d)`, `c = k_d(0+)`:

1. is infinitely divisible and has the generating triplet `(a(χ(t)² - χ(s)²) I, ν_{s,t}, 0)`
   (`isotropic_stage_triplet`; ledger A3(iii));
2. is absolutely continuous if `a = 0` and `c = ∞` (`isotropic_stage_absolutelyContinuous`;
   A3(iii)), and then gives no point a mass (`isotropic_stage_no_point_mass`);
3. has a nonnegative density of class `C^n` for every `n`, with a bounded derivative of every
   order, if `a > 0` (`isotropic_stage_smooth_density`; ledger A1 at every order).

So a stage has a point mass at the origin exactly when `a = 0` and `c < ∞`, and it is absolutely
continuous otherwise (`isotropic_stage_dichotomy`, with `prop:isotropic-stage-atom`).

## The route

* **A symmetric triplet** (`exists_law_of_symm_triplet`): A3(iii) and the library's
  `LevyTriplet.lkExponent_of_symm` give a law with the transform
  `exp[-½v|ξ|² - ∫ (1 - cos⟨ξ,x⟩) ν(dx)]`.
* **Removing the jumps larger than `ε`** (`null_le_exp_neg_mass`): a law with the transform
  `exp[-∫ (1 - cos) dν]`, `ν` a symmetric Lévy measure with a density, is the convolution of the
  compound Poisson law of `ν` restricted to `{|x| > ε}` and the law of the rest, so it gives a
  Lebesgue-null set at most `e^{-ν(|x| > ε)}`. When `ν` has infinite mass the bound tends to `0`.
* **The smooth density**: `|μ̂(ξ)| ≤ e^{-b|ξ|²}`, `b = ½a(χ(t)² - χ(s)²) > 0`, so every moment of
  the transform is finite (`r^n ≤ n! e^r` and `r ≤ 1/(2b) + (b/2)r²`); A1 at each order gives a
  density `g_n`, and the continuous densities of one measure are one function
  (`eq_of_withDensity_ofReal_eq`).

## Trust

`isotropic_stage_triplet`, `isotropic_stage_absolutelyContinuous`,
`isotropic_stage_no_point_mass`, `exists_law_of_symm_triplet` and `null_le_exp_neg_mass` print
A3(iii) (`levy_khintchine_converse`);
`isotropic_stage_smooth_density` prints A1 (`density_of_integrable_charFun`);
`isotropic_stage_dichotomy` prints both. `OriginDatum.stageTriplet` is Lean core.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open ScaleSpace (IsSelfDecomposable mconvL1E convPow)
open scoped Topology MatrixOrder ENNReal RealInnerProductSpace Nat

variable {d : ℕ}

/-! ## A symmetric triplet -/

/-- **The law of a symmetric triplet** `(vI, ν, 0)` (ledger A3(iii)): an infinitely divisible law
with that triplet, whose transform is `exp[-½v|ξ|² - ∫ (1 - cos⟨ξ,x⟩) ν(dx)]`
(`eq:symmetric-triplet`). -/
theorem exists_law_of_symm_triplet (T : LevyTriplet d) {v : ℝ} (hA : T.A = v • (1 : Mat d))
    (hγ : T.γ = 0) (hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧ HasTriplet μ T ∧
      ∀ ξ : Rd d, charFun μ ξ
        = ((Real.exp (-(v * ‖ξ‖ ^ 2 / 2 + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂T.ν)) : ℝ) : ℂ) := by
  obtain ⟨μ, hprob, hID, hT⟩ := levy_khintchine_converse T
  refine ⟨μ, hprob, hID, hT, fun ξ => ?_⟩
  rw [hT ξ, T.lkExponent_of_symm hA hγ hsym ξ, ← Complex.ofReal_neg, ← Complex.ofReal_exp]

namespace OriginDatum

/-- **The triplet of a stage**: `(a(L² - ℓ²) I, ν, 0)` with `ν` the measure of the dilation
difference. -/
noncomputable def stageTriplet (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ < L) : LevyTriplet d where
  A := (D.a * (L ^ 2 - ℓ ^ 2)) • (1 : Mat d)
  ν := D.stageMeasure ℓ L
  γ := 0
  A_posSemidef := Matrix.PosSemidef.one.smul (mul_nonneg D.a_nonneg (by nlinarith))
  ν_zero := D.stageMeasure_zero ℓ L
  ν_integrable := D.stageMeasure_integrable hd hℓ hL

end OriginDatum

/-! ## Clause (1) -/

/-- **`prop:isotropic-stage-density`(1)**: the stage is infinitely divisible and has the
generating triplet `(a(χ(t)² - χ(s)²) I, ν_{s,t}, 0)`. Ledger A3(iii). -/
theorem isotropic_stage_triplet (hd : 1 ≤ d) (D : OriginDatum d) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IsInfinitelyDivisible (μ s t) ∧
      ∃ T : LevyTriplet d, T.A = (D.a * (χ t ^ 2 - χ s ^ 2)) • (1 : Mat d) ∧
        T.ν = D.stageMeasure (χ s) (χ t) ∧ T.γ = 0 ∧ HasTriplet (μ s t) T := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  haveI := hprob s t hs.le hst.le
  have hTν : (D.stageTriplet hd hℓ hL).ν = D.stageMeasure (χ s) (χ t) := rfl
  obtain ⟨μ', hprob', hID, hT, hchar⟩ := exists_law_of_symm_triplet (D.stageTriplet hd hℓ hL)
    (v := D.a * (χ t ^ 2 - χ s ^ 2)) rfl rfl (D.stageMeasure_neg _ _)
  haveI := hprob'
  have heq : μ' = μ s t := eq_of_charFun_eq fun ξ => by
    rw [hchar ξ, hTν, isotropic_stage_transform hd D hχ hD μ hrep hs hst ξ]
    congr 3
    ring
  rw [← heq]
  exact ⟨hID, D.stageTriplet hd hℓ hL, rfl, rfl, rfl, hT⟩

/-! ## Clause (2): removing the large jumps -/

/-- **Removing the jumps larger than `ε`**: a probability measure with the transform
`exp[-∫ (1 - cos⟨ξ,x⟩) ν(dx)]`, `ν` a symmetric Lévy measure with a density, gives a Lebesgue-null
Borel set at most `e^{-ν(|x| > ε)}`. Ledger A3(iii), for the law of the jumps of size at most
`ε`. -/
theorem null_le_exp_neg_mass (T : LevyTriplet d)
    (hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν) (hac : T.ν ≪ volume)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂T.ν) : ℝ) : ℂ))
    {ε : ℝ} (hε : 0 < ε) {N : Set (Rd d)} (hN0 : volume N = 0) :
    μ N ≤ ENNReal.ofReal (Real.exp (-(T.ν {x | ε < ‖x‖}).toReal)) := by
  have hSm : MeasurableSet {x : Rd d | ε < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hnegS : (LinearIsometryEquiv.neg ℝ (E := Rd d)) ⁻¹' {x : Rd d | ε < ‖x‖}
      = {x : Rd d | ε < ‖x‖} := by
    ext x; simp
  have hnegSc : (LinearIsometryEquiv.neg ℝ (E := Rd d)) ⁻¹' {x : Rd d | ε < ‖x‖}ᶜ
      = {x : Rd d | ε < ‖x‖}ᶜ := by
    ext x; simp
  have hsymr : ∀ U : Set (Rd d), MeasurableSet U →
      (LinearIsometryEquiv.neg ℝ (E := Rd d)) ⁻¹' U = U →
      (T.ν.restrict U).map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν.restrict U := by
    intro U hU hpre
    conv_lhs => rw [← hpre]
    rw [← Measure.restrict_map (LinearIsometryEquiv.neg ℝ).continuous.measurable hU, hsym]
  haveI hfin : IsFiniteMeasure (T.ν.restrict {x : Rd d | ε < ‖x‖}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (T.measure_norm_gt_ne_top hε)⟩
  have hbigac : T.ν.restrict {x : Rd d | ε < ‖x‖} ≪ volume :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac
  -- the law of the jumps of size at most `ε`
  obtain ⟨T', hT'A, hT'ν, hT'γ⟩ : ∃ T' : LevyTriplet d, T'.A = (0 : ℝ) • (1 : Mat d) ∧
      T'.ν = T.ν.restrict {x : Rd d | ε < ‖x‖}ᶜ ∧ T'.γ = 0 :=
    ⟨{ A := (0 : ℝ) • (1 : Mat d)
       ν := T.ν.restrict {x : Rd d | ε < ‖x‖}ᶜ
       γ := 0
       A_posSemidef := Matrix.PosSemidef.one.smul le_rfl
       ν_zero := by
        rw [Measure.restrict_apply (measurableSet_singleton 0)]
        exact measure_mono_null inter_subset_left T.ν_zero
       ν_integrable := ne_top_of_le_ne_top T.ν_integrable
        (lintegral_mono' Measure.restrict_le_self le_rfl) }, rfl, rfl, rfl⟩
  obtain ⟨μ₁, hprob₁, -, -, hchar₁⟩ := exists_law_of_symm_triplet T' hT'A hT'γ
    (by rw [hT'ν]; exact hsymr _ hSm.compl hnegSc)
  haveI := hprob₁
  rw [hT'ν] at hchar₁
  -- the law is the convolution of the two
  have hconv : μ = cpLaw (T.ν.restrict {x : Rd d | ε < ‖x‖}) ∗ μ₁ := eq_of_charFun_eq fun ξ => by
    rw [charFun_conv, charFun_cpLaw_of_symm _ (hsymr _ hSm hnegS) ξ, hchar₁ ξ, hμ ξ,
      ← Complex.ofReal_mul, ← Real.exp_add, ← integral_add_compl hSm (T.integrable_one_sub_cos ξ)]
    congr 2
    ring
  haveI := isFiniteMeasure_cpSmooth (T.ν.restrict {x : Rd d | ε < ‖x‖})
  have h0 : (cpSmooth (T.ν.restrict {x : Rd d | ε < ‖x‖}) ∗ μ₁) N = 0 := by
    rw [Measure.conv_comm]
    exact Measure.conv_absolutelyContinuous (cpSmooth_absolutelyContinuous _ hbigac) hN0
  rw [hconv, cpLaw_eq_dirac_add, Measure.add_conv, Measure.conv_smul_left, Measure.dirac_zero_conv,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul, h0, add_zero, Measure.restrict_apply_univ]
  exact (mul_le_mul' le_rfl prob_le_one).trans_eq (mul_one _)

/-- **`prop:isotropic-stage-density`(2)**: no Gaussian part and an infinite profile at the
origin: the stage is absolutely continuous. Ledger A3(iii). -/
theorem isotropic_stage_absolutelyContinuous (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin = ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    μ s t ≪ volume := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  haveI := hprob s t hs.le hst.le
  have hTν : (D.stageTriplet hd hℓ hL).ν = D.stageMeasure (χ s) (χ t) := rfl
  have hμ : ∀ ξ : Rd d, charFun (μ s t) ξ = ((Real.exp
      (-∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂(D.stageTriplet hd hℓ hL).ν) : ℝ) : ℂ) := fun ξ => by
    rw [isotropic_stage_transform hd D hχ hD μ hrep hs hst ξ, ha, zero_div, zero_mul, zero_mul,
      zero_add, hTν]
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ N : Set (Rd d), volume N = 0 →
      μ s t N ≤ ENNReal.ofReal (Real.exp (-(D.stageMeasure (χ s) (χ t) {x | ε < ‖x‖}).toReal)) :=
    fun ε hε N hN0 => null_le_exp_neg_mass (D.stageTriplet hd hℓ hL) (D.stageMeasure_neg _ _)
      (D.stageMeasure_absolutelyContinuous _ _) (μ s t) hμ hε hN0
  have hfinn : ∀ ε : ℝ, 0 < ε → D.stageMeasure (χ s) (χ t) {x | ε < ‖x‖} ≠ ⊤ :=
    fun ε hε => (D.stageTriplet hd hℓ hL).measure_norm_gt_ne_top hε
  -- the mass off the ball of radius `1/(n+1)` tends to the total mass, which is infinite
  have htop : D.stageMeasure (χ s) (χ t) univ = ⊤ := by
    rw [D.stageMeasure_univ hd hℓ hL, hc, ENNReal.top_mul]
    simpa using Real.log_pos ((one_lt_div hℓ).mpr hL)
  have hmono : Monotone fun n : ℕ => {x : Rd d | 1 / ((n : ℝ) + 1) < ‖x‖} := by
    intro m n hmn x hx
    simp only [mem_setOf_eq] at hx ⊢
    refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hx
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hunion : (⋃ n : ℕ, {x : Rd d | 1 / ((n : ℝ) + 1) < ‖x‖}) = {0}ᶜ := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩ rfl
      rw [norm_zero] at hn
      exact absurd hn (not_lt.mpr (by positivity))
    · intro hx
      exact exists_nat_one_div_lt (norm_pos_iff.mpr hx)
  have hcompl : D.stageMeasure (χ s) (χ t) {0}ᶜ = ⊤ := by
    have h := measure_add_measure_compl (μ := D.stageMeasure (χ s) (χ t))
      (measurableSet_singleton (0 : Rd d))
    rwa [D.stageMeasure_zero, zero_add, htop] at h
  have hlim := tendsto_measure_iUnion_atTop (μ := D.stageMeasure (χ s) (χ t)) hmono
  rw [hunion, hcompl] at hlim
  intro N hN0
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' (x := atTop) (f := fun K : ℝ => ENNReal.ofReal (Real.exp (-K))) ?_
    fun K => ?_
  · have h : Tendsto (fun K : ℝ => ENNReal.ofReal (Real.exp (-K))) atTop
        (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
    rwa [ENNReal.ofReal_zero] at h
  · obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 (ENNReal.ofReal K) ENNReal.ofReal_lt_top).exists
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine (hbound _ hpos N hN0).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hK : K ≤ (D.stageMeasure (χ s) (χ t) {x | 1 / ((n : ℝ) + 1) < ‖x‖}).toReal := by
      rcases le_or_gt K 0 with h | h
      · exact h.trans ENNReal.toReal_nonneg
      · exact ((ENNReal.ofReal_lt_iff_lt_toReal h.le (hfinn _ hpos)).mp hn).le
    linarith

/-- **`prop:isotropic-stage-density`(2), "in particular it has no point mass"**: with no Gaussian
part and an infinite profile at the origin, the stage gives every point the mass `0`. -/
theorem isotropic_stage_no_point_mass (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin = ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∀ x : Rd d, μ s t {x} = 0 := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  exact fun x => isotropic_stage_absolutelyContinuous hd D ha hc hχ hD μ hprob hrep hs hst
    (measure_singleton x)

/-! ## Clause (3): a Gaussian part -/

/-- **`prop:isotropic-stage-density`(3)**: a Gaussian part: the stage has a nonnegative density of
class `C^n` for every `n`, with a bounded derivative of every order. Ledger A1, at every order. -/
theorem isotropic_stage_smooth_density (hd : 1 ≤ d) (D : OriginDatum d) (ha : 0 < D.a)
    {F χ : ℝ → ℝ} (hχ : IsGauge χ) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ p : Rd d → ℝ, (∀ x, 0 ≤ p x) ∧ (∀ n : ℕ, ContDiff ℝ n p) ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n p x‖ ≤ C) ∧
      μ s t = volume.withDensity fun x => ENNReal.ofReal (p x) := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  haveI := hprob s t hs.le hst.le
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = D.a / 2 * (χ t ^ 2 - χ s ^ 2) := ⟨_, rfl⟩
  have hb : 0 < b := by
    rw [hbdef]
    have : 0 < χ t ^ 2 - χ s ^ 2 := by nlinarith
    positivity
  -- the Gaussian bound on the transform, with a power
  have hbound : ∀ (n : ℕ) (z : Rd d), ‖charFun (μ s t) z‖ * ‖z‖ ^ n
      ≤ (n ! : ℝ) * Real.exp (1 / (2 * b)) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
    intro n z
    have hr : 0 ≤ ‖z‖ := norm_nonneg z
    have h1 : ‖charFun (μ s t) z‖ ≤ Real.exp (-b * ‖z‖ ^ 2) := by
      rw [isotropic_stage_transform hd D hχ hD μ hrep hs hst z, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, ← hbdef]
      refine Real.exp_le_exp.mpr ?_
      have hI : 0 ≤ ∫ x, (1 - Real.cos ⟪z, x⟫) ∂(D.stageMeasure (χ s) (χ t)) :=
        integral_nonneg fun x => one_sub_cos_nonneg_real _
      linarith
    have h2 : ‖z‖ ^ n ≤ (n ! : ℝ) * Real.exp ‖z‖ := by
      have h := Real.pow_div_factorial_le_exp ‖z‖ hr n
      rwa [div_le_iff₀ (by positivity : (0 : ℝ) < n !), mul_comm] at h
    have h3 : ‖z‖ ≤ 1 / (2 * b) + b / 2 * ‖z‖ ^ 2 := by
      have h : 0 ≤ (b * ‖z‖ - 1) ^ 2 / (2 * b) := by positivity
      have e : (b * ‖z‖ - 1) ^ 2 / (2 * b) = 1 / (2 * b) + b / 2 * ‖z‖ ^ 2 - ‖z‖ := by
        field_simp
        ring
      linarith
    have e2 : Real.exp (-b * ‖z‖ ^ 2) * Real.exp (b / 2 * ‖z‖ ^ 2)
        = Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖charFun (μ s t) z‖ * ‖z‖ ^ n
        ≤ Real.exp (-b * ‖z‖ ^ 2) * ((n ! : ℝ) * Real.exp ‖z‖) :=
          mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
      _ ≤ Real.exp (-b * ‖z‖ ^ 2) * ((n ! : ℝ) * Real.exp (1 / (2 * b) + b / 2 * ‖z‖ ^ 2)) := by
          gcongr
      _ = (n ! : ℝ) * Real.exp (1 / (2 * b)) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
          rw [Real.exp_add]
          linear_combination ((n ! : ℝ) * Real.exp (1 / (2 * b))) * e2
  have hfin : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal (‖charFun (μ s t) z‖ * ‖z‖ ^ n) ≠ ⊤ := by
    intro n
    have hint : Integrable fun z : Rd d =>
        (n ! : ℝ) * Real.exp (1 / (2 * b)) * Real.exp (-(b / 2) * ‖z‖ ^ 2) :=
      (integrable_rexp_neg_mul_sq_norm_Rd d (by positivity : 0 < b / 2)).const_mul _
    exact ne_top_of_le_ne_top hint.lintegral_lt_top.ne
      (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hbound n z))
  -- A1 at every order, and the densities are one function
  choose g hg0 hgC hgμ hgt using fun n : ℕ => density_of_integrable_charFun (μ s t) n (hfin n)
  have hgc : ∀ n : ℕ, Continuous (g n) := fun n => (hgC n).continuous
  have heq : ∀ n : ℕ, g n = g 0 := fun n =>
    eq_of_withDensity_ofReal_eq (hgc n) (hgc 0) (hg0 n) (hg0 0) ((hgμ n).symm.trans (hgμ 0))
  refine ⟨g 0, hg0 0, fun n => heq n ▸ hgC n, fun n => ?_, hgμ 0⟩
  have hcont : Continuous fun x => ‖iteratedFDeriv ℝ n (g 0) x‖ := by
    have h := (hgC n).continuous_iteratedFDeriv (m := n) le_rfl
    rw [heq n] at h
    exact h.norm
  have htend : Tendsto (fun x => ‖iteratedFDeriv ℝ n (g 0) x‖) (cocompact (Rd d)) (𝓝 0) := by
    have h := hgt n n le_rfl
    rw [heq n] at h
    exact tendsto_zero_iff_norm_tendsto_zero.mp h
  obtain ⟨C, hC⟩ := bddAbove_range_of_tendsto_cocompact hcont htend
  exact ⟨C, fun x => hC ⟨x, rfl⟩⟩

/-! ## The last sentence -/

/-- **`prop:isotropic-stage-density`, the last sentence**: a stage `μ_{s,t}`, `0 < s < t`, has a
point mass at the origin exactly when the datum has no Gaussian part and a finite profile at the
origin, and it is absolutely continuous in the two other cases. `F ≢ 0` is not asked: for
`F ≡ 0` the datum has `a = 0` and `c = 0`, the stage is `δ₀`, and both sides hold. -/
theorem isotropic_stage_dichotomy (hd : 1 ≤ d) (D : OriginDatum d) {F χ : ℝ → ℝ}
    (hχ : IsGauge χ) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (0 < μ s t {0} ↔ D.a = 0 ∧ D.profileAtOrigin ≠ ⊤) ∧
      (¬ (D.a = 0 ∧ D.profileAtOrigin ≠ ⊤) → μ s t ≪ volume) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hac : ¬ (D.a = 0 ∧ D.profileAtOrigin ≠ ⊤) → μ s t ≪ volume := by
    intro h
    by_cases ha : D.a = 0
    · have hc : D.profileAtOrigin = ⊤ := by
        by_contra hc
        exact h ⟨ha, hc⟩
      exact isotropic_stage_absolutelyContinuous hd D ha hc hχ hD μ hprob hrep hs hst
    · obtain ⟨p, -, -, -, hp⟩ := isotropic_stage_smooth_density hd D
        (lt_of_le_of_ne D.a_nonneg (Ne.symm ha)) hχ hD μ hprob hrep hs hst
      rw [hp]
      exact withDensity_absolutelyContinuous _ _
  refine ⟨⟨fun hpos => ?_, fun h => ?_⟩, hac⟩
  · by_contra h
    exact hpos.ne' (hac h (measure_singleton (0 : Rd d)))
  · obtain ⟨p, -, -, -, -, hμ, -⟩ :=
      isotropic_stage_operator hd D h.1 h.2 hχ hD μ hprob hrep hs hst
    have hℓ : 0 < χ s := hχ.pos hs
    have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
    have hpow : 0 < ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos hℓ (hℓ.trans hL)) _)
    rw [hμ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton 0),
      smul_eq_mul, mul_one]
    exact lt_of_lt_of_le hpow le_self_add

end AffineHemigroup
