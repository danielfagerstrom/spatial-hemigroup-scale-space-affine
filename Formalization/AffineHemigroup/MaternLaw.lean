/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.GammaGaussLaw
import ScaleSpaceCore.ExpIntegral
import ScaleSpaceCore.GammaMeasure

/-!
# The Matérn law as a Gamma mixture of Gaussian laws, Frullani's integral, a Poisson series

* **Frullani's integral**, `∫₀^∞ (e^{-ax} - e^{-bx}) x^{-1} dx = log(b/a)` for `0 < a < b`
  (`lintegral_frullani`), by Tonelli from `(e^{-ax} - e^{-bx})/x = ∫_a^b e^{-tx} dt`.
* **A Poisson series**, `∑ₙ e^{-m}/n! · cⁿ = e^{-m}e^{c}` in `ℝ≥0∞` (`tsum_poisson_mul_pow`).
* **The Gaussian mixtures.** For a probability measure `ν` on `[0,∞)`, the law of `√(2V) Z` with
  `V ∼ ν` and `Z` standard normal, independent, has transform `ω ↦ ∫ e^{-v|ω|²} ν(dv)`
  (`charFun_gaussMixture`): Fubini and Mathlib's `charFun_stdGaussian`.
* **The Gamma law.** `∫ e^{-uv} Γ(γ)^{-1}v^{γ-1}e^{-v} dv = (1+u)^{-γ}`
  (`lintegral_exp_gammaMeasure`), from the shared library.
* **The Matérn law**, `gammaGaussLaw_transform`: for `γ > 0` the law of `√(2V) Z`, `V` Gamma
  distributed of shape `γ`, is a probability measure with transform `(1 + |ω|²)^{-γ}`.

Lean core only. The declarations before the last stood in `AffineHemigroup.MaternOrbit`, which
imports this file and whose header gives the route; they are here unchanged (Q-0452). The last
is new: it states on their own the first two clauses of `matern_orbit`
(`prop:affine-orbits-matern`), with the lines by which that theorem proves them, for the formal
examples of the isotropic theory (`AffineHemigroup.Witnesses`, `AffineHemigroup.Probes`).
-/

namespace AffineHemigroup

section

open MeasureTheory Set Filter Matrix ProbabilityTheory Real
open scoped MatrixOrder RealInnerProductSpace Topology ENNReal Nat

variable {d : ℕ}

/-- `∫_a^b e^{-tx} dt = (e^{-ax} - e^{-bx})/x` for `x > 0`. -/
theorem integral_exp_neg_mul_param {a b x : ℝ} (hx : 0 < x) :
    ∫ t in a..b, exp (-(t * x)) = (exp (-(a * x)) - exp (-(b * x))) / x := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t => -exp (-(t * x)) / x) (exp (-(t * x))) t := by
    intro t _
    have h1 : HasDerivAt (fun t => -(t * x)) (-(1 * x)) t := ((hasDerivAt_id t).mul_const x).neg
    have h2 : HasDerivAt (fun t => -exp (-(t * x)) / x) (-(exp (-(t * x)) * -(1 * x)) / x) t :=
      (h1.exp.neg).div_const x
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- **Frullani's integral**: `∫₀^∞ (e^{-ax} - e^{-bx}) x^{-1} dx = log(b/a)` for `0 < a < b`. -/
theorem lintegral_frullani {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((exp (-(a * x)) - exp (-(b * x))) / x)
      = ENNReal.ofReal (log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  -- The integrand is an integral over `t ∈ (a, b]`.
  have hin : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal ((exp (-(a * x)) - exp (-(b * x))) / x)
      = ∫⁻ t in Ioc a b, ENNReal.ofReal (exp (-(t * x))) := by
    intro x hx
    rw [← integral_exp_neg_mul_param hx, intervalIntegral.integral_of_le hab.le,
      ofReal_integral_eq_lintegral_ofReal]
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    · exact Eventually.of_forall fun _ => (exp_pos _).le
  rw [setLIntegral_congr_fun measurableSet_Ioi hin]
  rw [lintegral_lintegral_swap]
  · -- The inner integral is `1/t`, and `∫_a^b dt/t = log(b/a)`.
    have hin2 : ∀ t ∈ Ioc a b, ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(t * x)))
        = ENNReal.ofReal (t⁻¹) := by
      intro t ht
      rw [ScaleSpace.lintegral_Ioi_exp_neg_mul (ha.trans ht.1)]
    rw [setLIntegral_congr_fun measurableSet_Ioc hin2, ← ofReal_integral_eq_lintegral_ofReal,
      ← intervalIntegral.integral_of_le hab.le, integral_inv_of_pos ha hb]
    · exact (continuousOn_inv₀.mono fun t ht => (ha.trans_le ht.1).ne').integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun t ht => (inv_pos.2 (ha.trans ht.1)).le)
  · exact (by fun_prop :
      Measurable fun p : ℝ × ℝ => ENNReal.ofReal (exp (-(p.2 * p.1)))).aemeasurable

/-- `∑ₙ e^{-m}/n! · cⁿ = e^{-m}e^{c}`, in `ℝ≥0∞`, for `c ≥ 0`. -/
theorem tsum_poisson_mul_pow (m : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∑' n : ℕ, ENNReal.ofReal (exp (-m) / (n ! : ℝ)) * ENNReal.ofReal c ^ n
      = ENNReal.ofReal (exp (-m) * exp c) := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal (exp (-m) / (n ! : ℝ)) * ENNReal.ofReal c ^ n
      = ENNReal.ofReal (exp (-m) * (c ^ n / (n ! : ℝ))) := by
    intro n
    rw [← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((Real.summable_pow_div_factorial c).mul_left _), tsum_mul_left, Real.exp_eq_exp_ℝ,
    NormedSpace.exp_eq_tsum_div]

/-- **The Laplace transform of the Gamma law** of shape `γ` and scale `1`: `(1+u)^{-γ}`. The shared
library's `ScaleSpace.lintegral_gammaMeasure_rpow_mul_exp` at `q = 0`, `r = 1` (Q-0362). -/
theorem lintegral_exp_gammaMeasure {γ : ℝ} (hγ : 0 < γ) {u : ℝ} (hu : 0 ≤ u) :
    ∫⁻ v, ENNReal.ofReal (exp (-(u * v))) ∂(gammaMeasure γ 1)
      = ENNReal.ofReal ((1 + u) ^ (-γ)) := by
  have h := ScaleSpace.lintegral_gammaMeasure_rpow_mul_exp hγ one_pos (q := 0)
    (by rwa [add_zero]) hu
  simp only [rpow_zero, one_mul, add_zero, one_rpow] at h
  rw [h, mul_div_assoc, div_self (Gamma_pos_of_pos hγ).ne', mul_one, one_div,
    inv_rpow (by linarith), ← rpow_neg (by linarith)]

/-- The map `(v, z) ↦ √(2v) z` is measurable. -/
theorem measurable_sqrtTwoSmul : Measurable fun p : ℝ × Rd d => Real.sqrt (2 * p.1) • p.2 := by
  fun_prop

/-- The law of `√(2V) Z` is a probability measure. -/
theorem isProbabilityMeasure_gaussMixture (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure
      ((ν.prod (stdGaussian (Rd d))).map fun p => Real.sqrt (2 * p.1) • p.2) :=
  Measure.isProbabilityMeasure_map measurable_sqrtTwoSmul.aemeasurable

/-- **The transform of a Gaussian mixture**: for a probability measure `ν` on `[0,∞)`, the law of
`√(2V) Z`, `V ∼ ν` and `Z` standard normal independent, has transform `∫ e^{-v|ω|²} ν(dv)`. -/
theorem charFun_gaussMixture (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ v ∂ν, 0 ≤ v)
    (ω : Rd d) :
    charFun ((ν.prod (stdGaussian (Rd d))).map fun p => Real.sqrt (2 * p.1) • p.2) ω
      = ((∫ v, exp (-(‖ω‖ ^ 2 * v)) ∂ν : ℝ) : ℂ) := by
  rw [charFun_apply, integral_map measurable_sqrtTwoSmul.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop)), integral_prod, ← integral_complex_ofReal]
  · refine integral_congr_ae ?_
    filter_upwards [hν] with v hv
    have hin : ∀ z : Rd d, ⟪Real.sqrt (2 * v) • z, ω⟫ = ⟪z, Real.sqrt (2 * v) • ω⟫ := by
      intro z
      rw [real_inner_smul_left, real_inner_smul_right]
    have h1 : ∫ y : Rd d, Complex.exp (↑⟪Real.sqrt (2 * v) • y, ω⟫ * Complex.I)
        ∂stdGaussian (Rd d) = charFun (stdGaussian (Rd d)) (Real.sqrt (2 * v) • ω) := by
      rw [charFun_apply]
      simp_rw [hin]
    simp only
    rw [h1, charFun_stdGaussian, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.ofReal_exp]
    congr 1
    have h2 : (Real.sqrt (2 * v) * ‖ω‖) ^ 2 = 2 * v * ‖ω‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h3 : ((Real.sqrt (2 * v) * ‖ω‖ : ℝ) : ℂ) ^ 2 = ((2 * v * ‖ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, h2]
    rw [h3]
    push_cast
    ring
  · refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]

/-- The transform of a Gaussian mixture as a Laplace transform: `∫ e^{-uv} ν(dv)` read as a lower
integral. -/
theorem charFun_gaussMixture_lintegral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ v ∂ν, 0 ≤ v) (ω : Rd d) :
    charFun ((ν.prod (stdGaussian (Rd d))).map fun p => Real.sqrt (2 * p.1) • p.2) ω
      = (((∫⁻ v, ENNReal.ofReal (exp (-(‖ω‖ ^ 2 * v))) ∂ν).toReal : ℝ) : ℂ) := by
  rw [charFun_gaussMixture ν hν, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ => (exp_pos _).le) (Continuous.aestronglyMeasurable (by fun_prop))]

/-- `e^{-γ log(1+u)} = (1+u)^{-γ}` for `u ≥ 0`. -/
theorem exp_neg_mul_log_one_add {γ u : ℝ} (hu : 0 ≤ u) :
    exp (-(γ * log (1 + u))) = (1 + u) ^ (-γ) := by
  rw [rpow_def_of_pos (by linarith)]
  congr 1
  ring

/-- **The Matérn law**: for `γ > 0` the law of `√(2V) Z`, `V` Gamma distributed of shape `γ` and
scale `1`, is a probability measure with transform `(1 + |ω|²)^{-γ}`. These are the first two
clauses of `matern_orbit` (`prop:affine-orbits-matern`), stated on their own, with the lines by
which that theorem proves them. -/
theorem gammaGaussLaw_transform (γ : ℝ) (hγ : 0 < γ) :
    IsProbabilityMeasure (gammaGaussLaw d γ) ∧
      ∀ ω : Rd d, charFun (gammaGaussLaw d γ) ω = (((1 + ‖ω‖ ^ 2) ^ (-γ) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_gammaMeasure hγ one_pos
  refine ⟨isProbabilityMeasure_gaussMixture _, fun ω => ?_⟩
  rw [gammaGaussLaw, charFun_gaussMixture_lintegral _
      ((ScaleSpace.ae_pos_gammaMeasure γ 1).mono fun _ hv => hv.le),
    lintegral_exp_gammaMeasure hγ (sq_nonneg _),
    ENNReal.toReal_ofReal (rpow_nonneg (by positivity) _)]

end

end AffineHemigroup
