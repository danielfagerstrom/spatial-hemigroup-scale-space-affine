/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Orbits
import AffineHemigroup.Defs.Orbits
import ScaleSpaceCore.ExpIntegral
import ScaleSpaceCore.GammaMeasure
import AffineHemigroup.MaternLaw

/-!
# `prop:affine-orbits-matern` — the Matérn orbits

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:affine-orbits-matern`
(`prop:affine-orbits`(4), split), whose proof is the part of `prop:affine-orbits`' proof headed
clause (4). Lean core only: the laws are the constructions `gammaGaussLaw` and `maternRayLaw` of
`AffineHemigroup.Defs.Orbits`, so no existence clause of the ledger (A3(iii)) is read.

## The route

The blueprint's, in the Laplace variable `u = |ω|²`.

* **The Gaussian mixtures.** For a probability measure `ν` on `[0,∞)`, the law of `√(2V) Z` with
  `V ∼ ν` and `Z` standard normal, independent, has transform `ω ↦ ∫ e^{-v|ω|²} ν(dv)`
  (`charFun_gaussMixture`): Fubini and Mathlib's `charFun_stdGaussian`.
* **The Gamma law.** `∫ e^{-uv} Γ(γ)^{-1}v^{γ-1}e^{-v} dv = (1+u)^{-γ}` is the shared library's
  `ScaleSpace.lintegral_gammaMeasure_rpow_mul_exp` at `q = 0`, `r = 1`
  (`lintegral_exp_gammaMeasure`), and the law is carried by `(0,∞)` by its `ae_pos_gammaMeasure`.
* **Frullani's integral**, `∫₀^∞ (e^{-ax} - e^{-bx}) x^{-1} dx = log(b/a)` for `0 < a < b`
  (`lintegral_frullani`), by Tonelli from `(e^{-ax} - e^{-bx})/x = ∫_a^b e^{-tx} dt` and
  `∫₀^∞ e^{-tx} dx = 1/t` (the shared library's `ScaleSpace.lintegral_Ioi_exp_neg_mul`), rather
  than by the blueprint's substitution and squeeze.
* **The compound Poisson law.** Its Laplace transform is `e^{-L(ℝ)} ∑ (L̂(u))ⁿ/n! =
  e^{-L(ℝ)}e^{L̂(u)}` (`lintegral_exp_compoundPoisson`), from the Laplace transform of a convolution
  power (`lintegral_exp_convPow`), the blueprint's "conditioning on `N`". With the Matérn Lévy
  measure, `L̂(u) = γ log((1+u)/(λ^{-2}+u))` is Frullani at `(u + λ^{-2}, u + 1)` and the total mass
  `L(ℝ) = 2γ log λ` is Frullani at `(λ^{-2}, 1)`; so the subtraction of the blueprint's display
  `∫(1 - e^{-ux}) n(x) dx` is never formed.

Since Q-0452 the Gaussian mixtures, the Laplace transform of the Gamma law, Frullani's integral and
the Poisson series are in `AffineHemigroup.MaternLaw`, which this file imports.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory Real
open ScaleSpace (convPow isFiniteMeasure_convPow)
open scoped MatrixOrder RealInnerProductSpace Topology ENNReal Nat

variable {d : ℕ}

/-! ## The compound Poisson law -/

/-- **The Laplace transform of a convolution power**:
`∫ e^{-sx} L^{n*}(dx) = (∫ e^{-sx} L(dx))ⁿ`. -/
theorem lintegral_exp_convPow (L : Measure ℝ) [IsFiniteMeasure L] (s : ℝ) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (exp (-(s * x))) ∂(convPow L n)
      = (∫⁻ x, ENNReal.ofReal (exp (-(s * x))) ∂L) ^ n := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (exp (-(s * x))) := by fun_prop
  induction n with
  | zero => simp [convPow, lintegral_dirac' _ hmeas]
  | succ n ih =>
    haveI := isFiniteMeasure_convPow L n
    rw [convPow, Measure.conv, lintegral_map hmeas measurable_add, pow_succ, ← ih,
      ← lintegral_prod_mul hmeas.aemeasurable hmeas.aemeasurable]
    congr 1
    ext p
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    ring_nf

/-- **The Laplace transform of a compound Poisson law**: if `∫ e^{-sx} L(dx) = c`, then
`∫ e^{-sx} (compoundPoisson L)(dx) = e^{-L(ℝ)} e^{c}`. -/
theorem lintegral_exp_compoundPoisson (L : Measure ℝ) [IsFiniteMeasure L] (s : ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∫⁻ x, ENNReal.ofReal (exp (-(s * x))) ∂L = ENNReal.ofReal c) :
    ∫⁻ x, ENNReal.ofReal (exp (-(s * x))) ∂(compoundPoisson L)
      = ENNReal.ofReal (exp (-(L univ).toReal) * exp c) := by
  rw [compoundPoisson, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_exp_convPow, hc]
  exact tsum_poisson_mul_pow _ hc0

/-- A compound Poisson law of a finite measure is a probability measure. -/
theorem isProbabilityMeasure_compoundPoisson (L : Measure ℝ) [IsFiniteMeasure L] :
    IsProbabilityMeasure (compoundPoisson L) := by
  constructor
  have h := lintegral_exp_compoundPoisson L 0 ENNReal.toReal_nonneg
    (c := (L univ).toReal) (by simp [ENNReal.ofReal_toReal (measure_ne_top L univ)])
  simp only [zero_mul, neg_zero, exp_zero, ENNReal.ofReal_one, lintegral_const, one_mul] at h
  rw [h, ← exp_add, neg_add_cancel, exp_zero, ENNReal.ofReal_one]

/-- A convolution of measures carried by `[0,∞)` is carried by `[0,∞)`. -/
theorem ae_nonneg_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) : ∀ᵐ x ∂(μ ∗ ν), 0 ≤ x := by
  rw [Measure.conv, ae_map_iff (p := fun x : ℝ => 0 ≤ x) measurable_add.aemeasurable
    measurableSet_Ici]
  have h1 : ∀ᵐ p ∂(μ.prod ν), 0 ≤ p.1 := Measure.quasiMeasurePreserving_fst.ae hμ
  have h2 : ∀ᵐ p ∂(μ.prod ν), 0 ≤ p.2 := Measure.quasiMeasurePreserving_snd.ae hν
  filter_upwards [h1, h2] with p hp1 hp2
  exact add_nonneg hp1 hp2

/-- A compound Poisson law of a finite measure carried by `[0,∞)` is carried by `[0,∞)`. -/
theorem ae_nonneg_compoundPoisson (L : Measure ℝ) [IsFiniteMeasure L] (hL : ∀ᵐ x ∂L, 0 ≤ x) :
    ∀ᵐ x ∂(compoundPoisson L), 0 ≤ x := by
  have hpow : ∀ n : ℕ, ∀ᵐ x ∂(convPow L n), 0 ≤ x := by
    intro n
    induction n with
    | zero =>
      rw [convPow, ae_dirac_iff (p := fun x : ℝ => 0 ≤ x) measurableSet_Ici]
    | succ n ih =>
      haveI := isFiniteMeasure_convPow L n
      rw [convPow]
      exact ae_nonneg_conv ih hL
  rw [compoundPoisson, Measure.ae_sum_iff' (p := fun x : ℝ => 0 ≤ x) measurableSet_Ici]
  exact fun n => Measure.ae_smul_measure (hpow n) _

/-! ## The Matérn Lévy measure -/

/-- `(e^{-x/λ²} - e^{-x})/x ≥ 0` for `x > 0`, `λ ≥ 1`. -/
theorem maternRay_density_nonneg {lam x : ℝ} (hlam : 1 ≤ lam) (hx : 0 < x) :
    0 ≤ (exp (-x / lam ^ 2) - exp (-x)) / x := by
  refine div_nonneg (sub_nonneg.2 (exp_le_exp.2 ?_)) hx.le
  rw [neg_div, neg_le_neg_iff]
  exact div_le_self hx.le (one_le_pow₀ hlam)

/-- **The Laplace transform of the Matérn Lévy measure**: for `u ≥ 0`,
`∫ e^{-ux} γ(e^{-x/λ²} - e^{-x})x^{-1} dx = γ log((1+u)/(λ^{-2}+u))`, Frullani's integral at
`(λ^{-2}+u, 1+u)`. -/
theorem lintegral_exp_maternRayLevy {γ lam : ℝ} (hγ : 0 ≤ γ) (hlam : 1 < lam) {u : ℝ}
    (hu : 0 ≤ u) :
    ∫⁻ x, ENNReal.ofReal (exp (-(u * x))) ∂(maternRayLevy γ lam)
      = ENNReal.ofReal (γ * log ((1 + u) / ((lam ^ 2)⁻¹ + u))) := by
  have hl2 : 1 < lam ^ 2 := one_lt_pow₀ hlam two_ne_zero
  have ha : 0 < (lam ^ 2)⁻¹ + u := add_pos_of_pos_of_nonneg (inv_pos.2 (by positivity)) hu
  have hab : (lam ^ 2)⁻¹ + u < 1 + u := by
    have := inv_lt_one_of_one_lt₀ hl2
    linarith
  rw [maternRayLevy, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      ((fun x => ENNReal.ofReal (γ * (exp (-x / lam ^ 2) - exp (-x)) / x)) *
        fun x => ENNReal.ofReal (exp (-(u * x)))) x
      = ENNReal.ofReal γ * ENNReal.ofReal
          ((exp (-(((lam ^ 2)⁻¹ + u) * x)) - exp (-((1 + u) * x))) / x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [Pi.mul_apply]
    rw [mul_div_assoc, ENNReal.ofReal_mul hγ, mul_assoc,
      ← ENNReal.ofReal_mul (maternRay_density_nonneg hlam.le hx0)]
    congr 2
    rw [div_mul_eq_mul_div, sub_mul, ← exp_add, ← exp_add]
    congr 3 <;> ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _ (by fun_prop),
    lintegral_frullani ha hab, ← ENNReal.ofReal_mul hγ]

/-- **The total mass of the Matérn Lévy measure** is `2γ log λ`. -/
theorem maternRayLevy_univ {γ lam : ℝ} (hγ : 0 ≤ γ) (hlam : 1 < lam) :
    maternRayLevy γ lam univ = ENNReal.ofReal (2 * γ * log lam) := by
  have h := lintegral_exp_maternRayLevy hγ hlam le_rfl
  simp only [zero_mul, neg_zero, exp_zero, ENNReal.ofReal_one, lintegral_const, one_mul,
    add_zero, div_inv_eq_mul] at h
  rw [h, Real.log_pow]
  congr 1
  push_cast
  ring

/-- The Matérn Lévy measure is finite. -/
theorem isFiniteMeasure_maternRayLevy {γ lam : ℝ} (hγ : 0 ≤ γ) (hlam : 1 < lam) :
    IsFiniteMeasure (maternRayLevy γ lam) :=
  ⟨by rw [maternRayLevy_univ hγ hlam]; exact ENNReal.ofReal_lt_top⟩

/-- The Matérn Lévy measure is carried by `(0,∞)`. -/
theorem ae_nonneg_maternRayLevy (γ lam : ℝ) : ∀ᵐ x ∂(maternRayLevy γ lam), 0 ≤ x := by
  rw [maternRayLevy]
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact le_of_lt hx

/-- **`prop:affine-orbits-matern`, "`W ≥ 0`"** (blind review W1E-4): for `γ > 0` and `λ > 1` the
compound Poisson law of `W`, with Lévy measure `γ (e^{-x/λ²} - e^{-x}) x⁻¹ dx` on `(0,∞)`, is a
probability measure carried by `[0,∞)`. -/
theorem maternRay_W_nonneg {γ lam : ℝ} (hγ : 0 < γ) (hlam : 1 < lam) :
    IsProbabilityMeasure (compoundPoisson (maternRayLevy γ lam)) ∧
      ∀ᵐ x ∂(compoundPoisson (maternRayLevy γ lam)), 0 ≤ x := by
  haveI := isFiniteMeasure_maternRayLevy hγ.le hlam
  exact ⟨isProbabilityMeasure_compoundPoisson _,
    ae_nonneg_compoundPoisson _ (ae_nonneg_maternRayLevy γ lam)⟩

/-! ## The node -/

/-- **`prop:affine-orbits-matern`** (`prop:affine-orbits`(4)): for `γ > 0`, `(1 + |ω|²)^{-γ}` is the
characteristic function of the law of `√(2V) Z`; `g_γ(u) = γ log(1+u)` satisfies the hypothesis of
`prop:affine-orbits` and is not linear; the orbit has `μ̂_Σ(ω) = (1 + ⟨ω,Σω⟩)^{-γ}`; and for every
`λ > 1` the hypothesis of clause (2) holds with `ν_λ` the law of `√(2W) Z`, `W` compound Poisson
with Lévy measure `γ(e^{-x/λ²} - e^{-x})x⁻¹dx` on `(0,∞)`, of total mass `2γ log λ`. -/
theorem matern_orbit (_hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) :
    let g : ℝ → ℝ := fun u => γ * Real.log (1 + u)
    IsProbabilityMeasure (gammaGaussLaw d γ) ∧
      (∀ ω : Rd d, charFun (gammaGaussLaw d γ) ω = (((1 + ‖ω‖ ^ 2) ^ (-γ) : ℝ) : ℂ)) ∧
      ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∀ ω : Rd d, charFun (gammaGaussLaw d γ) ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      (∀ S : Mat d, S.PosDef → ∀ ω : Rd d,
        charFun (affineOrbit (gammaGaussLaw d γ) S) ω = (((1 + quad S ω) ^ (-γ) : ℝ) : ℂ)) ∧
      (¬ ∃ b : ℝ, ∀ u : ℝ, 0 ≤ u → g u = b * u) ∧
      ∀ lam : ℝ, 1 < lam →
        maternRayLevy γ lam univ = ENNReal.ofReal (2 * γ * Real.log lam) ∧
        IsProbabilityMeasure (maternRayLaw d γ lam) ∧
        ∀ ω : Rd d, ((Real.exp (-g (lam ^ 2 * ‖ω‖ ^ 2)) : ℝ) : ℂ) =
          ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) * charFun (maternRayLaw d γ lam) ω := by
  intro g
  haveI := isProbabilityMeasure_gammaMeasure hγ one_pos
  -- The law of `√(2V) Z` and its transform.
  have hcf : ∀ ω : Rd d, charFun (gammaGaussLaw d γ) ω = (((1 + ‖ω‖ ^ 2) ^ (-γ) : ℝ) : ℂ) := by
    intro ω
    rw [gammaGaussLaw, charFun_gaussMixture_lintegral _
        ((ScaleSpace.ae_pos_gammaMeasure γ 1).mono fun _ hv => hv.le),
      lintegral_exp_gammaMeasure hγ (sq_nonneg _),
      ENNReal.toReal_ofReal (rpow_nonneg (by positivity) _)]
  have hcf' : ∀ ω : Rd d, charFun (gammaGaussLaw d γ) ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) := by
    intro ω
    rw [hcf, exp_neg_mul_log_one_add (sq_nonneg _)]
  refine ⟨isProbabilityMeasure_gaussMixture _, hcf, ?_, fun u hu => ?_, by simp [g], hcf',
    fun S hS ω => ?_, ?_, fun lam hlam => ?_⟩
  · -- `g` is continuous on `[0,∞)`.
    refine continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := hu
    linarith
  · exact mul_nonneg hγ.le (log_nonneg (by linarith))
  · -- The orbit.
    rw [charFun_affineOrbit_exp hcf' hS.posSemidef, exp_neg_mul_log_one_add
      (quad_nonneg hS.posSemidef ω)]
  · -- `g` is not linear: `g(3) = 2g(1)` would force `3b = 2b` with `b = g(1) > 0`.
    rintro ⟨b, hb⟩
    have h1 := hb 1 zero_le_one
    have h3 := hb 3 (by norm_num)
    simp only [g] at h1 h3
    have hlog4 : Real.log (1 + 3) = 2 * Real.log (1 + 1) := by
      rw [show (1 : ℝ) + 3 = (1 + 1) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4] at h3
    have hpos : 0 < γ * Real.log (1 + 1) := mul_pos hγ (log_pos (by norm_num))
    nlinarith
  · -- The ray increments.
    haveI := isFiniteMeasure_maternRayLevy hγ.le hlam
    haveI := isProbabilityMeasure_compoundPoisson (maternRayLevy γ lam)
    refine ⟨maternRayLevy_univ hγ.le hlam, isProbabilityMeasure_gaussMixture _, fun ω => ?_⟩
    set u : ℝ := ‖ω‖ ^ 2 with hu
    have hu0 : 0 ≤ u := sq_nonneg _
    have hl2 : 0 < lam ^ 2 := by positivity
    have ha : 0 < (lam ^ 2)⁻¹ + u := add_pos_of_pos_of_nonneg (inv_pos.2 hl2) hu0
    have hab : (lam ^ 2)⁻¹ + u ≤ 1 + u := by
      have := inv_le_one_of_one_le₀ (one_le_pow₀ hlam.le : (1 : ℝ) ≤ lam ^ 2)
      linarith
    have hc0 : 0 ≤ γ * log ((1 + u) / ((lam ^ 2)⁻¹ + u)) :=
      mul_nonneg hγ.le (log_nonneg ((one_le_div ha).2 hab))
    have hW := lintegral_exp_compoundPoisson (maternRayLevy γ lam) u hc0
      (lintegral_exp_maternRayLevy hγ.le hlam hu0)
    rw [maternRayLaw, charFun_gaussMixture_lintegral _
      (ae_nonneg_compoundPoisson _ (ae_nonneg_maternRayLevy γ lam)), ← hu, hW,
      ENNReal.toReal_ofReal (by positivity), maternRayLevy_univ hγ.le hlam,
      ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg zero_le_two hγ.le) (log_nonneg hlam.le)),
      ← Complex.ofReal_mul, ← exp_add, ← exp_add]
    congr 2
    -- `log(1 + λ²u) = 2 log λ + log(λ^{-2} + u)`.
    have he : 1 + lam ^ 2 * u = lam ^ 2 * ((lam ^ 2)⁻¹ + u) := by
      field_simp
    simp only [g]
    rw [he, Real.log_mul hl2.ne' ha.ne', Real.log_pow, Real.log_div (by linarith) ha.ne']
    push_cast
    ring

end AffineHemigroup
