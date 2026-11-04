/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StageLevyMeasure
import AffineHemigroup.OriginLowerBound
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# `prop:isotropic-stage-atom`: a stage with a point mass at the centre

Blueprint: `blueprint/src/parts/03-isotropic.tex`. Q-0447 (the statements were typed in Q-0434).

A stage `μ_{s,t}`, `0 < s < t`, of a family with the display of a gauge `χ` and the exponent of a
datum `(0, k_d)` with `c = k_d(0+) < ∞`: its Lévy measure `ν` is finite, the stage is the compound
Poisson law of `ν`, it is `λ^c δ₀ + η` with `λ = χ(s)/χ(t)` and `η` absolutely continuous of mass
`1 - λ^c`, as an operator on `L¹(ℝ^d)` it is `λ^c` times the identity plus convolution by `η`, and
it is not self-decomposable.

## The route

* **The compound Poisson law without its first term** (`cpSmooth`): `cpLaw L = e^{-m} δ₀ + η`
  with `η = e^{-m} ∑_{n ≥ 1} L^{*n}/n!` (`cpLaw_eq_dirac_add`), and `η` is absolutely continuous
  when `L` is (`cpSmooth_absolutelyContinuous`): `L^{*(n+1)} = L^{*n} ∗ L`, and a convolution with
  an absolutely continuous factor is absolutely continuous (Mathlib's
  `Measure.conv_absolutelyContinuous`).
* **The transform** of the compound Poisson law of a symmetric finite measure in real form
  (`charFun_cpLaw_of_symm`), from the library's `charFun_cpLaw` and `charFun_of_symm`.
* **The operator** (`mconvL1E_smul_dirac_add`): convolution by `p δ₀ + η` on `L¹(ℝ^d)` is
  `p · id + (η ∗ ·)`, from the additivity of the integral in the measure.
* **The density** (`isotropic_stage_operator`, after the blind check of Q-0447): the series `η`
  is finite and absolutely continuous, so it has a density `p ≥ 0` in `L¹`, its Radon–Nikodym
  derivative read in `ℝ` (`exists_density_of_absolutelyContinuous`), and convolution by a
  measure with the density `p` is convolution by `p` (`mconvE_withDensity`).
* **Not self-decomposable** (`not_selfDecomposable_of_atom`): the mass of the origin under
  `μ = (½·)_* μ ∗ ρ` forces `ρ{0} = 1`, so `ρ = δ₀`, `μ̂(ξ) = μ̂(ξ/2^n) → 1` and `μ = δ₀`. It asks
  `d ≥ 1`: on `ℝ⁰` every measure is absolutely continuous and `δ₀` is self-decomposable.

## Trust

Every declaration of this file prints Lean's three logical axioms and nothing else.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open ScaleSpace (IsSelfDecomposable mconvL1E convPow isFiniteMeasure_convPow_Rd)
open scoped Topology MatrixOrder ENNReal RealInnerProductSpace Nat

variable {d : ℕ}

/-! ## A compound Poisson law without its first term -/

/-- **The smoothing part of a compound Poisson law**, `e^{-L(ℝ^d)} ∑_{n ≥ 1} L^{*n}/n!`. -/
noncomputable def cpSmooth (L : Measure (Rd d)) : Measure (Rd d) :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-(L univ).toReal) / ((n + 1)! : ℝ)) • convPow L (n + 1)

/-- The term `n = 0` split off: `π_L = e^{-L(ℝ^d)} δ₀ + η`. -/
theorem cpLaw_eq_dirac_add (L : Measure (Rd d)) :
    cpLaw L = ENNReal.ofReal (Real.exp (-(L univ).toReal)) • Measure.dirac 0 + cpSmooth L := by
  refine Measure.ext fun s hs => ?_
  rw [cpLaw, Measure.add_apply, cpSmooth, Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  congr 1
  simp [convPow]

theorem cpSmooth_le (L : Measure (Rd d)) : cpSmooth L ≤ cpLaw L := by
  rw [cpLaw_eq_dirac_add]
  exact Measure.le_add_left le_rfl

theorem isFiniteMeasure_cpSmooth (L : Measure (Rd d)) [IsFiniteMeasure L] :
    IsFiniteMeasure (cpSmooth L) :=
  isFiniteMeasure_of_le (cpLaw L) (cpSmooth_le L)

/-- A convolution power of positive order of an absolutely continuous finite measure is absolutely
continuous. -/
theorem convPow_succ_absolutelyContinuous (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hL : L ≪ volume) (n : ℕ) : convPow L (n + 1) ≪ volume := by
  rw [convPow]
  exact Measure.conv_absolutelyContinuous hL

/-- The smoothing part of the compound Poisson law of an absolutely continuous finite measure is
absolutely continuous. -/
theorem cpSmooth_absolutelyContinuous (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hL : L ≪ volume) : cpSmooth L ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h => ?_
  rw [cpSmooth, Measure.sum_apply _ hs]
  refine ENNReal.tsum_eq_zero.mpr fun n => ?_
  rw [Measure.smul_apply, convPow_succ_absolutelyContinuous L hL n h, smul_zero]

/-- The mass of the smoothing part: `1 - e^{-L(ℝ^d)}`. -/
theorem cpSmooth_univ (L : Measure (Rd d)) [IsFiniteMeasure L] :
    cpSmooth L univ = ENNReal.ofReal (1 - Real.exp (-(L univ).toReal)) := by
  have h := cpLaw_univ L
  rw [cpLaw_eq_dirac_add, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (mem_univ _), smul_eq_mul, mul_one, add_comm] at h
  rw [ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h,
    ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]

/-- **The transform of the compound Poisson law of a symmetric finite measure**:
`π̂_L(ξ) = exp[-∫ (1 - cos⟨ξ,x⟩) L(dx)]`. -/
theorem charFun_cpLaw_of_symm (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hsym : L.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = L) (ξ : Rd d) :
    charFun (cpLaw L) ξ = ((Real.exp (-∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂L) : ℝ) : ℂ) := by
  have hsym' : L.map (fun x => -x) = L := by
    have hneg : (fun x : Rd d => -x) = (LinearIsometryEquiv.neg ℝ : Rd d ≃ₗᵢ[ℝ] Rd d) := by
      rw [LinearIsometryEquiv.coe_neg]
    rw [hneg]
    exact hsym
  have hint : Integrable (fun x : Rd d => Real.cos ⟪x, ξ⟫) L :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hcomm : ∀ x : Rd d, ⟪ξ, x⟫ = ⟪x, ξ⟫ := fun x => real_inner_comm x ξ
  have hI : ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂L = (L univ).toReal - ∫ x, Real.cos ⟪x, ξ⟫ ∂L := by
    simp_rw [hcomm]
    rw [integral_sub (integrable_const 1) hint]
    simp [integral_const, measureReal_def]
  rw [charFun_cpLaw, charFun_of_symm L hsym' ξ, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Real.exp_add, hI]
  congr 2
  ring

/-! ## The operator of a point mass plus a measure -/

/-- **Convolution by `p δ₀ + η` on `L¹(ℝ^d)`** is `p` times the identity plus convolution by
`η`. -/
theorem mconvL1E_smul_dirac_add {p : ℝ} (hp : 0 ≤ p) (μ η : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure η] (h : μ = ENNReal.ofReal p • Measure.dirac 0 + η) :
    mconvL1E μ = p • ContinuousLinearMap.id ℝ (L1 d) + mconvL1E η := by
  subst h
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have hadd : ((p • ContinuousLinearMap.id ℝ (L1 d) + mconvL1E η) f : Rd d → ℝ)
      =ᵐ[volume] fun x => p * (f : Rd d → ℝ) x + ScaleSpace.mconvE η (f : Rd d → ℝ) x := by
    have h1 : (p • ContinuousLinearMap.id ℝ (L1 d) + mconvL1E η) f = p • f + mconvL1E η f := rfl
    rw [h1]
    filter_upwards [Lp.coeFn_add (p • f) (mconvL1E η f), Lp.coeFn_smul p f,
      ScaleSpace.coeFn_mconvL1E η f] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
  refine (ScaleSpace.coeFn_mconvL1E _ f).trans (Filter.EventuallyEq.trans ?_ hadd.symm)
  filter_upwards [(ScaleSpace.integrable_uncurry_subE η (Lp.aestronglyMeasurable f)
    (L1.integrable_coeFn f)).prod_right_ae] with x hx
  simp only [Function.uncurry] at hx
  have hδ : Integrable (fun y : Rd d => (f : Rd d → ℝ) (x - y))
      (ENNReal.ofReal p • Measure.dirac (0 : Rd d)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [ScaleSpace.mconvE_apply, ScaleSpace.mconvE_apply, integral_add_measure hδ hx,
    integral_smul_measure, integral_dirac, sub_zero, ENNReal.toReal_ofReal hp, smul_eq_mul]

/-- A finite measure on `ℝ^d` that is absolutely continuous has a nonnegative, measurable,
integrable density, of integral its mass: its Radon–Nikodym derivative, read in `ℝ`. -/
theorem exists_density_of_absolutelyContinuous (η : Measure (Rd d)) [IsFiniteMeasure η]
    (hη : η ≪ volume) :
    ∃ p : Rd d → ℝ, (∀ x, 0 ≤ p x) ∧ Measurable p ∧ Integrable p ∧
      ∫ x, p x = (η univ).toReal ∧ η = volume.withDensity fun x => ENNReal.ofReal (p x) := by
  refine ⟨fun x => (η.rnDeriv volume x).toReal, fun x => ENNReal.toReal_nonneg,
    (Measure.measurable_rnDeriv η volume).ennreal_toReal, Measure.integrable_toReal_rnDeriv,
    ?_, ?_⟩
  · rw [Measure.integral_toReal_rnDeriv hη, measureReal_def]
  · conv_lhs => rw [← Measure.withDensity_rnDeriv_eq η volume hη]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top η volume] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]

/-- **Convolution by a measure with the density `p` is convolution by `p`**:
`∫ f(x - y) η(dy) = ∫ p(y) f(x - y) dy`. -/
theorem mconvE_withDensity {p : Rd d → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hpm : Measurable p)
    (f : Rd d → ℝ) (x : Rd d) :
    ScaleSpace.mconvE (volume.withDensity fun y => ENNReal.ofReal (p y)) f x
      = ∫ y, p y * f (x - y) := by
  rw [ScaleSpace.mconvE_apply, integral_withDensity_eq_integral_toReal_smul hpm.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]

/-! ## A point mass at the origin and self-decomposability -/

/-- A probability measure that gives the origin the mass `1` is `δ₀`. -/
theorem eq_dirac_of_singleton_eq_one (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (h : ρ {0} = 1) : ρ = Measure.dirac 0 := by
  have hc : ρ ({0}ᶜ) = 0 := (prob_compl_eq_zero_iff (measurableSet_singleton 0)).mpr h
  refine Measure.ext fun s hs => ?_
  by_cases h0 : (0 : Rd d) ∈ s
  · rw [Measure.dirac_apply_of_mem h0]
    refine le_antisymm prob_le_one ?_
    rw [← h]
    exact measure_mono (singleton_subset_iff.mpr h0)
  · rw [Measure.dirac_apply' _ hs, indicator_of_notMem h0]
    have hsub : s ⊆ ({0}ᶜ : Set (Rd d)) := fun x hx hx0 => h0 (by
      rw [mem_singleton_iff] at hx0
      rwa [hx0] at hx)
    exact measure_mono_null hsub hc

/-- **The fact behind `prop:isotropic-stage-atom`(4)**, which reads nothing of the cascade: on
`ℝ^d`, `d ≥ 1`, a probability measure with an atom of weight `p ∈ (0,1)` at the origin whose
remaining part is absolutely continuous is not self-decomposable. (`d ≥ 1` is needed: on `ℝ⁰`
every measure is absolutely continuous, and `δ₀ = p δ₀ + (1 - p) δ₀` is self-decomposable.) -/
theorem not_selfDecomposable_of_atom (hd : 1 ≤ d) (μ η : Measure (Rd d))
    [IsProbabilityMeasure μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hη : η ≪ volume)
    (hμ : μ = ENNReal.ofReal p • Measure.dirac 0 + η) :
    ¬ IsSelfDecomposable μ := by
  intro hsd
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hvol0 : (volume : Measure (Rd d)) {0} = 0 := measure_singleton 0
  haveI hηfin : IsFiniteMeasure η := by
    refine isFiniteMeasure_of_le μ ?_
    rw [hμ]
    exact Measure.le_add_left le_rfl
  have hμ0 : μ {0} = ENNReal.ofReal p := by
    rw [hμ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton 0),
      hη hvol0, add_zero, smul_eq_mul, mul_one]
  obtain ⟨ρ, hρ, hdec⟩ := hsd (1 / 2) (by norm_num) (by norm_num)
  haveI := hρ
  have hgm : Measurable fun x : Rd d => (1 / 2 : ℝ) • x := measurable_const_smul _
  -- the image of the absolutely continuous part is absolutely continuous
  have hη' : η.map (fun x : Rd d => (1 / 2 : ℝ) • x) ≪ volume := by
    refine (hη.map hgm).trans ?_
    rw [Measure.map_addHaar_smul volume (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact Measure.smul_absolutelyContinuous
  haveI : IsFiniteMeasure (η.map fun x : Rd d => (1 / 2 : ℝ) • x) := Measure.isFiniteMeasure_map η _
  have hmap : μ.map (fun x : Rd d => (1 / 2 : ℝ) • x)
      = ENNReal.ofReal p • Measure.dirac 0 + η.map (fun x : Rd d => (1 / 2 : ℝ) • x) := by
    conv_lhs => rw [hμ]
    rw [Measure.map_add _ _ hgm, Measure.map_smul, Measure.map_dirac' hgm, smul_zero]
  have hconv0 : (η.map (fun x : Rd d => (1 / 2 : ℝ) • x) ∗ ρ) {0} = 0 := by
    rw [Measure.conv_comm]
    exact Measure.conv_absolutelyContinuous hη' hvol0
  -- the residual gives the origin the mass 1
  have hρ0 : ρ {0} = 1 := by
    have h : μ {0} = (μ.map (fun x : Rd d => (1 / 2 : ℝ) • x) ∗ ρ) {0} := by rw [← hdec]
    rw [hmap, Measure.add_conv, Measure.conv_smul_left, Measure.dirac_zero_conv,
      Measure.add_apply, Measure.smul_apply, hconv0, add_zero, hμ0, smul_eq_mul] at h
    have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    exact (ENNReal.mul_eq_left hp' ENNReal.ofReal_ne_top).mp h.symm
  have hfix : μ = μ.map (fun x : Rd d => (1 / 2 : ℝ) • x) := by
    rw [eq_dirac_of_singleton_eq_one ρ hρ0, Measure.conv_dirac_zero] at hdec
    exact hdec
  -- the transform is constant along `ξ/2^n`, so it is `1`
  have hcf : ∀ ξ : Rd d, charFun μ ξ = charFun μ ((1 / 2 : ℝ) • ξ) := fun ξ => by
    conv_lhs => rw [hfix]
    exact charFun_map_smul _ _
  have hiter : ∀ (n : ℕ) (ξ : Rd d), charFun μ ξ = charFun μ ((1 / 2 : ℝ) ^ n • ξ) := by
    intro n
    induction n with
    | zero => intro ξ; simp
    | succ n ih =>
      intro ξ
      rw [ih ξ, hcf ((1 / 2 : ℝ) ^ n • ξ), smul_smul, ← pow_succ']
  have hone : ∀ ξ : Rd d, charFun μ ξ = 1 := by
    intro ξ
    have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n • ξ) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).smul_const ξ
      rwa [zero_smul] at h
    have h0 : charFun μ 0 = 1 := by simp [charFun_zero]
    have h2 := ((continuous_charFun (μ := μ)).tendsto 0).comp hlim
    rw [h0] at h2
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => hiter n ξ) h2
  have hμδ : μ = Measure.dirac 0 := eq_of_charFun_eq fun ξ => by
    rw [hone, charFun_dirac]
    simp
  rw [hμδ, Measure.dirac_apply_of_mem (mem_singleton 0)] at hμ0
  have hlt : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hp1
  exact absurd hμ0.symm hlt.ne

/-! ## `prop:isotropic-stage-atom` -/

/-- **`prop:isotropic-stage-atom`(1)**: the stage is the compound Poisson law of its Lévy
measure, which is finite. -/
theorem isotropic_stage_compoundPoisson (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IsFiniteMeasure (D.stageMeasure (χ s) (χ t)) ∧
      μ s t = cpLaw (D.stageMeasure (χ s) (χ t)) := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  have hfin : IsFiniteMeasure (D.stageMeasure (χ s) (χ t)) :=
    ⟨lt_top_iff_ne_top.mpr ((D.stageMeasure_univ_ne_top_iff hd hℓ hL).mpr hc)⟩
  refine ⟨hfin, ?_⟩
  haveI := hfin
  haveI := hprob s t hs.le hst.le
  refine eq_of_charFun_eq fun ξ => ?_
  rw [isotropic_stage_transform hd D hχ hD μ hrep hs hst ξ,
    charFun_cpLaw_of_symm _ (D.stageMeasure_neg _ _) ξ, ha, zero_div, zero_mul, zero_mul,
    zero_add]

/-- **`prop:isotropic-stage-atom`(1), `e^{-m} = λ^c`**: with `m = c log(χ(t)/χ(s))` the mass of
the Lévy measure of the stage and `c < ∞`, `e^{-m} = (χ(s)/χ(t))^c`. (The hypothesis `c < ∞` is
the print's and is not used: at `c = ∞` both sides are read with `∞.toReal = 0`.) -/
theorem isotropic_stage_exp_neg_mass (hd : 1 ≤ d) (D : OriginDatum d)
    (_hc : D.profileAtOrigin ≠ ⊤) {χ : ℝ → ℝ} (hχ : IsGauge χ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) :
    (D.stageMeasure (χ s) (χ t) univ).toReal
        = D.profileAtOrigin.toReal * Real.log (χ t / χ s) ∧
      Real.exp (-(D.stageMeasure (χ s) (χ t) univ).toReal)
        = (χ s / χ t) ^ D.profileAtOrigin.toReal := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  have hlog : 0 ≤ Real.log (χ t / χ s) := Real.log_nonneg ((one_lt_div hℓ).mpr hL).le
  have hm : (D.stageMeasure (χ s) (χ t) univ).toReal
      = D.profileAtOrigin.toReal * Real.log (χ t / χ s) := by
    rw [D.stageMeasure_univ hd hℓ hL, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog]
  refine ⟨hm, ?_⟩
  rw [hm, Real.rpow_def_of_pos (div_pos hℓ (hℓ.trans hL)), ← inv_div (χ t) (χ s), Real.log_inv]
  congr 1
  ring

/-- **`prop:isotropic-stage-atom`, "Then `c > 0`"**: a datum with no Gaussian part whose exponent
is not identically `0` has a positive profile at the origin. (Added after the blind check of
Q-0434, finding F-A7: the print states it and no type did.) -/
theorem profileAtOrigin_pos (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) {F : ℝ → ℝ}
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) :
    0 < D.profileAtOrigin := by
  by_contra h
  have hc : D.profileAtOrigin = 0 := le_antisymm (not_lt.mp h) bot_le
  obtain ⟨r, hr, hFr⟩ := hFne
  obtain ⟨ξ, hξ⟩ := exists_norm_eq hd hr
  apply hFr
  have hk : ∀ r : ℝ, 0 < r → D.k r ≤ 0 := fun r hr => by
    have h1 := D.ofReal_k_le hr
    rw [hc] at h1
    exact ENNReal.ofReal_eq_zero.mp (le_antisymm h1 bot_le)
  have hν : D.levyMeasure = 0 := by
    have h0 : (fun x : Rd d => ({0}ᶜ : Set (Rd d)).indicator
        (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x) = 0 := by
      funext x
      by_cases hx : x = 0
      · subst hx
        simp
      · have hA := (sphereArea_eq_toSphere hd).2
        rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), Pi.zero_apply,
          ENNReal.ofReal_eq_zero]
        exact div_nonpos_of_nonpos_of_nonneg (hk _ (norm_pos_iff.mpr hx)) (by positivity)
    rw [OriginDatum.levyMeasure, h0, withDensity_zero]
  rw [← hξ, hD ξ, OriginDatum.exponent, OriginDatum.exponentL, hν, ha]
  simp

/-- **`prop:isotropic-stage-atom`(2) and (3)**: the atom, the smoothing part and the operator.
`η` is the measure `λ^c ∑_{n ≥ 1} ν^{*n}/n!`; the statement names it by its properties. The weight
`λ^c` of the point mass is in `(0,1)`: the conjunct `0 < λ^c` holds because `χ s > 0`, and the
conjunct `λ^c < 1` is the print's upper bound, for which `F ≢ 0` is asked (without it the type was
true at `c = 0`, with `μ_{s,t} = δ₀` and `η = 0`). The instance that `mconvL1E (μ s t)` needs is
`hprob s t`. The series of `η` and the density `p` of clause (3) are `isotropic_stage_operator`. -/
theorem isotropic_stage_atom (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ (η : Measure (Rd d)) (_ : IsFiniteMeasure η),
      η ≪ volume ∧
      μ s t = ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal) • Measure.dirac 0 + η ∧
      η univ = ENNReal.ofReal (1 - (χ s / χ t) ^ D.profileAtOrigin.toReal) ∧
      μ s t {0} = ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal) ∧
      0 < (χ s / χ t) ^ D.profileAtOrigin.toReal ∧
      (χ s / χ t) ^ D.profileAtOrigin.toReal < 1 ∧
      ¬ μ s t ≪ volume ∧
      (haveI := hprob s t hs.le hst.le; mconvL1E (μ s t)) =
        ((χ s / χ t) ^ D.profileAtOrigin.toReal) •
          ContinuousLinearMap.id ℝ (L1 d) + mconvL1E η := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  have hLpos : 0 < χ t := hℓ.trans hL
  obtain ⟨hfin, hcp⟩ := isotropic_stage_compoundPoisson hd D ha hc hχ hD μ hprob hrep hs hst
  haveI := hfin
  haveI hμprob := hprob s t hs.le hst.le
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set ν := D.stageMeasure (χ s) (χ t) with hν
  set c := D.profileAtOrigin.toReal with hcdef
  have hlam0 : 0 < χ s / χ t := div_pos hℓ hLpos
  have hlam1 : χ s / χ t < 1 := (div_lt_one hLpos).mpr hL
  have hcpos : 0 < c := ENNReal.toReal_pos (profileAtOrigin_pos hd D ha hD hFne).ne' hc
  -- `e^{-m} = λ^c`
  have hexp : Real.exp (-(ν univ).toReal) = (χ s / χ t) ^ c :=
    (isotropic_stage_exp_neg_mass hd D hc hχ hs hst).2
  have hpow0 : 0 < (χ s / χ t) ^ c := Real.rpow_pos_of_pos hlam0 c
  have hpow1 : (χ s / χ t) ^ c < 1 := Real.rpow_lt_one hlam0.le hlam1 hcpos
  haveI hηfin : IsFiniteMeasure (cpSmooth ν) := isFiniteMeasure_cpSmooth ν
  have hηac : cpSmooth ν ≪ volume :=
    cpSmooth_absolutelyContinuous ν (D.stageMeasure_absolutelyContinuous _ _)
  have hμeq : μ s t = ENNReal.ofReal ((χ s / χ t) ^ c) • Measure.dirac 0 + cpSmooth ν := by
    rw [hcp, cpLaw_eq_dirac_add, hexp]
  have hμ0 : μ s t {0} = ENNReal.ofReal ((χ s / χ t) ^ c) := by
    rw [hμeq, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton 0),
      hηac (measure_singleton 0), add_zero, smul_eq_mul, mul_one]
  refine ⟨cpSmooth ν, hηfin, hηac, hμeq, ?_, hμ0, hpow0, hpow1, fun hac => ?_,
    mconvL1E_smul_dirac_add hpow0.le (μ s t) (cpSmooth ν) hμeq⟩
  · rw [cpSmooth_univ, hexp]
  · have h0 := hac (measure_singleton (0 : Rd d))
    rw [hμ0, ENNReal.ofReal_eq_zero] at h0
    exact absurd hpow0 (not_lt.mpr h0)

/-- **`prop:isotropic-stage-atom`(2) and (3), the smoothing part by its series and its density**:
the measure `η = λ^c ∑_{n ≥ 1} ν^{*n}/n!` (`cpSmooth`) has a density `p ≥ 0`, integrable, of
integral `1 - λ^c`; `μ_{s,t} = λ^c δ₀ + η`; and the operator of the stage is
`μ_{s,t} ∗ f = λ^c f + p ∗ f` for `f ∈ L¹(ℝ^d)`, with `(p ∗ f)(x) = ∫ p(y) f(x - y) dy`, as an
equality almost everywhere of the representative of `mconvL1E (μ s t) f`. `F ≢ 0` is not asked. -/
theorem isotropic_stage_operator (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ p : Rd d → ℝ, (∀ x, 0 ≤ p x) ∧ Integrable p ∧
      ∫ x, p x = 1 - (χ s / χ t) ^ D.profileAtOrigin.toReal ∧
      cpSmooth (D.stageMeasure (χ s) (χ t)) = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      μ s t = ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal) • Measure.dirac 0
        + cpSmooth (D.stageMeasure (χ s) (χ t)) ∧
      ∀ f : L1 d, (((haveI := hprob s t hs.le hst.le; mconvL1E (μ s t)) f : L1 d) : Rd d → ℝ)
        =ᵐ[volume] fun x => (χ s / χ t) ^ D.profileAtOrigin.toReal * (f : Rd d → ℝ) x
          + ∫ y, p y * (f : Rd d → ℝ) (x - y) := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  obtain ⟨hfin, hcp⟩ := isotropic_stage_compoundPoisson hd D ha hc hχ hD μ hprob hrep hs hst
  haveI := hfin
  haveI hμprob := hprob s t hs.le hst.le
  have hexp := (isotropic_stage_exp_neg_mass hd D hc hχ hs hst).2
  have hpow0 : 0 < (χ s / χ t) ^ D.profileAtOrigin.toReal :=
    Real.rpow_pos_of_pos (div_pos hℓ (hℓ.trans hL)) _
  haveI hηfin : IsFiniteMeasure (cpSmooth (D.stageMeasure (χ s) (χ t))) :=
    isFiniteMeasure_cpSmooth _
  have hηac : cpSmooth (D.stageMeasure (χ s) (χ t)) ≪ volume :=
    cpSmooth_absolutelyContinuous _ (D.stageMeasure_absolutelyContinuous _ _)
  have hμeq : μ s t = ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal) • Measure.dirac 0
      + cpSmooth (D.stageMeasure (χ s) (χ t)) := by
    rw [hcp, cpLaw_eq_dirac_add, hexp]
  obtain ⟨p, hp0, hpm, hpi, hpint, hpη⟩ := exists_density_of_absolutelyContinuous _ hηac
  refine ⟨p, hp0, hpi, ?_, hpη, hμeq, fun f => ?_⟩
  · rw [hpint, cpSmooth_univ, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg))), hexp]
  · have hop := mconvL1E_smul_dirac_add hpow0.le (μ s t) _ hμeq
    have hTf : mconvL1E (μ s t) f = (χ s / χ t) ^ D.profileAtOrigin.toReal • f
        + mconvL1E (cpSmooth (D.stageMeasure (χ s) (χ t))) f :=
      congrArg (fun T : L1 d →L[ℝ] L1 d => T f) hop
    refine (Filter.EventuallyEq.of_eq (congrArg (fun g : L1 d => (g : Rd d → ℝ)) hTf)).trans ?_
    filter_upwards [Lp.coeFn_add ((χ s / χ t) ^ D.profileAtOrigin.toReal • f)
      (mconvL1E (cpSmooth (D.stageMeasure (χ s) (χ t))) f),
      Lp.coeFn_smul ((χ s / χ t) ^ D.profileAtOrigin.toReal) f,
      ScaleSpace.coeFn_mconvL1E (cpSmooth (D.stageMeasure (χ s) (χ t))) f] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, ← mconvE_withDensity hp0 hpm, ← hpη]

/-- **`prop:isotropic-stage-atom`(4)**: the stage is not self-decomposable. -/
theorem isotropic_stage_not_selfDecomposable (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ¬ IsSelfDecomposable (μ s t) := by
  obtain ⟨η, -, hac, hμ, -, -, hpos, hlt, -, -⟩ :=
    isotropic_stage_atom hd D ha hc hχ hD hFne μ hprob hrep hs hst
  haveI := hprob s t hs.le hst.le
  exact not_selfDecomposable_of_atom hd (μ s t) η hpos hlt hac hμ

end AffineHemigroup
