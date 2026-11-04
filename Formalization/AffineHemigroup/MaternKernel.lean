/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MaternCrossShape
import AffineHemigroup.StableOrderGenerated
import AffineHemigroup.StableTail
import AffineHemigroup.SimilarityLine
import AffineHemigroup.FixedFrame
import ScaleSpaceCore.InverseGamma

/-!
# `lem:matern-kernel-hessian`: the kernel of the Matérn law of index `1` and its Hessian

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:matern-kernel-hessian`. Wave 2, group I,
Q-0281. The kernel `G(y) = ∫₀^∞ e^{-t} h_t(y) dt` is `F(|y|²)` with
`F(u) = (4π)^{-d/2} L_{-d/2}(u)` and `L_m(u) := ∫₀^∞ e^{-t} t^m e^{-u/4t} dt`; differentiating under
the integral gives `L_m' = -L_{m-1}/4` for `u > 0`, hence `G` is smooth off the origin, and the
second derivative of `F(|·|²)` is read off. The transform of `G` is Fubini with the Gaussian
transform; the density of the orbit is the transform again and the substitution `x = Σ^{1/2}y`. The
substitution `t = r²s` turns `r^d ∇·P∇G(rŷ)` into `⟨ŷ,Pŷ⟩𝓐(r) - (tr P)𝓑(r)`, and the limits of
`𝓐`, `𝓑` are dominated convergence and the Gamma integral after `s = 1/v`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The Laplace-type integrals `L_m(u) := ∫₀^∞ e^{-t} t^m e^{-u/4t} dt` -/

/-- **`L_m(u) := ∫₀^∞ e^{-t} t^m e^{-u/4t} dt`**, finite for `u > 0` and every real `m`. -/
noncomputable def maternLap (m u : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ m * Real.exp (-u / (4 * t))

/-- `e^{-x} ≤ n!/xⁿ` for `x > 0`. Mathlib types only. -/
theorem exp_neg_le_factorial_div {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
  have h := Real.pow_div_factorial_le_exp _ hx.le n
  have hp : 0 < x ^ n / (n.factorial : ℝ) := by positivity
  rw [Real.exp_neg, ← inv_div]
  exact inv_anti₀ hp h

/-- `t ↦ e^{-t} t^m e^{-c/4t}` is integrable on `(0,∞)` for `c > 0` and every real `m`. Mathlib
types only. -/
theorem integrableOn_maternLap (m : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ m * Real.exp (-c / (4 * t))) (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-m - 1)
  have hs : 0 < m + n + 1 := by linarith
  have hg := Integrable.const_mul (Real.GammaIntegral_convergent hs)
    ((n.factorial : ℝ) * 4 ^ n / c ^ n)
  refine Integrable.mono' hg (by fun_prop : Measurable fun t : ℝ =>
    Real.exp (-t) * t ^ m * Real.exp (-c / (4 * t))).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  have h1 := exp_neg_le_factorial_div (div_pos hc (by positivity : (0 : ℝ) < 4 * t)) n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_div]
  calc Real.exp (-t) * t ^ m * Real.exp (-(c / (4 * t)))
      ≤ Real.exp (-t) * t ^ m * ((n.factorial : ℝ) / (c / (4 * t)) ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (n.factorial : ℝ) * 4 ^ n / c ^ n * (Real.exp (-t) * t ^ (m + n + 1 - 1)) := by
        rw [show m + n + 1 - 1 = m + n by ring, Real.rpow_add_natCast ht.ne', div_pow, mul_pow]
        field_simp

/-- **`L_m' = -L_{m-1}/4`** on `(0,∞)`, by differentiation under the integral. -/
theorem hasDerivAt_maternLap (m : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (maternLap m) (-(1 / 4) * maternLap (m - 1) u) u := by
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x t => Real.exp (-t) * t ^ m * Real.exp (-x / (4 * t)))
    (F' := fun x t => -(1 / 4) * (Real.exp (-t) * t ^ (m - 1) * Real.exp (-x / (4 * t))))
    (bound := fun t => 1 / 4 * (Real.exp (-t) * t ^ (m - 1) * Real.exp (-(u / 2) / (4 * t))))
    (x₀ := u) (s := Ioi (u / 2)) (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun x => (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-t) * t ^ m * Real.exp (-x / (4 * t))).aestronglyMeasurable)
    (integrableOn_maternLap m hu)
    (by fun_prop : Measurable fun t : ℝ =>
      -(1 / 4) * (Real.exp (-t) * t ^ (m - 1) * Real.exp (-u / (4 * t)))).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) x hx => by
      have hx' : u / 2 < x := hx
      have he : Real.exp (-x / (4 * t)) ≤ Real.exp (-(u / 2) / (4 * t)) :=
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) (by positivity))
      have hX : 0 ≤ Real.exp (-t) * t ^ (m - 1) * Real.exp (-x / (4 * t)) := by positivity
      have hXY : Real.exp (-t) * t ^ (m - 1) * Real.exp (-x / (4 * t)) ≤
          Real.exp (-t) * t ^ (m - 1) * Real.exp (-(u / 2) / (4 * t)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith))
    ((integrableOn_maternLap (m - 1) (by linarith : 0 < u / 2)).const_mul (1 / 4))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) x _ => by
      have h := (((hasDerivAt_neg x).div_const (4 * t)).exp).const_mul
        (Real.exp (-t) * t ^ m)
      refine h.congr_deriv ?_
      rw [Real.rpow_sub_one ht.ne']
      field_simp))
  have h2 := hint.2
  rw [integral_const_mul] at h2
  exact h2

/-- `L_m` is `C^n` on `(0,∞)`, for every `n` and `m`. -/
theorem contDiffOn_maternLap (n : ℕ) : ∀ m : ℝ, ContDiffOn ℝ n (maternLap m) (Ioi 0) := by
  induction n with
  | zero =>
    intro m
    exact contDiffOn_zero.2 fun u hu =>
      (hasDerivAt_maternLap m hu).continuousAt.continuousWithinAt
  | succ n ih =>
    intro m
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun u hu => (hasDerivAt_maternLap m hu).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    refine ((contDiffOn_const (c := -(1 / 4 : ℝ))).mul (ih (m - 1))).congr fun u hu => ?_
    exact (hasDerivAt_maternLap m hu).deriv

/-! ## The profile `F` with `G = F(|·|²)`, and its two derivatives -/

/-- **`F(u) := (4π)^{-d/2} L_{-d/2}(u)`**, so that `G(y) = F(|y|²)`. -/
noncomputable def maternProfile (d : ℕ) (u : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLap (-(d : ℝ) / 2) u

/-- **`F'(u) = -(4π)^{-d/2} L_{-d/2-1}(u)/4`**. -/
noncomputable def maternProfile1 (d : ℕ) (u : ℝ) : ℝ :=
  -(1 / 4) * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLap (-(d : ℝ) / 2 - 1) u)

/-- **`F''(u) = (4π)^{-d/2} L_{-d/2-2}(u)/16`**. -/
noncomputable def maternProfile2 (d : ℕ) (u : ℝ) : ℝ :=
  1 / 16 * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLap (-(d : ℝ) / 2 - 1 - 1) u)

theorem maternGreen_eq_profile (y : Rd d) : maternGreen d y = maternProfile d (‖y‖ ^ 2) := by
  rw [maternGreen, maternProfile, maternLap, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  rw [Real.mul_rpow (by positivity) ht.le]
  ring

theorem hasDerivAt_maternProfile {u : ℝ} (hu : 0 < u) :
    HasDerivAt (maternProfile d) (maternProfile1 d u) u := by
  have h := (hasDerivAt_maternLap (-(d : ℝ) / 2) hu).const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2))
  unfold maternProfile
  refine h.congr_deriv ?_
  rw [maternProfile1]
  ring

theorem hasDerivAt_maternProfile1 {u : ℝ} (hu : 0 < u) :
    HasDerivAt (maternProfile1 d) (maternProfile2 d u) u := by
  have h := ((hasDerivAt_maternLap (-(d : ℝ) / 2 - 1) hu).const_mul
    ((4 * Real.pi) ^ (-(d : ℝ) / 2))).const_mul (-(1 / 4 : ℝ))
  unfold maternProfile1
  refine h.congr_deriv ?_
  rw [maternProfile2]
  ring

/-- **`G` is smooth on `ℝ^d ∖ {0}`** (`lem:matern-kernel-hessian`(1)). -/
theorem contDiffOn_maternGreen :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternGreen d) {0}ᶜ := by
  have hP : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternProfile d) (Ioi 0) :=
    contDiffOn_const.mul (contDiffOn_infty.2 fun n => contDiffOn_maternLap n _)
  have hG : maternGreen d = fun y : Rd d => maternProfile d (‖y‖ ^ 2) :=
    funext maternGreen_eq_profile
  rw [hG]
  exact hP.comp (contDiff_norm_sq ℝ).contDiffOn fun y hy =>
    show (0 : ℝ) < ‖y‖ ^ 2 from pow_pos (norm_pos_iff.2 hy) 2

/-! ## The heat kernel, the transform of `G`, `∫ G = 1` -/

/-! The integrand of `G` is `e^{-t} g_{2t}(y)`, with `g_u` the heat kernel of variance `u`
(`heatKernel`, `Defs.Origin`): `g_{2t}(y) = (4πt)^{-d/2} e^{-|y|²/4t}`. -/

/-- **The transform of the heat kernel**: `ĝ_{2t}(ζ) = e^{-t|ζ|²}`. -/
theorem integral_heatKernel_fourier {t : ℝ} (ht : 0 < t) (ζ : Rd d) :
    ∫ y : Rd d, Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) * ((heatKernel d (2 * t) y : ℝ) : ℂ) =
      ((Real.exp (-(t * ‖ζ‖ ^ 2)) : ℝ) : ℂ) := by
  have hb : 0 < (((1 / (2 * (2 * t)) : ℝ)) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I ζ
  have hfun : (fun y : Rd d => Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) *
      ((heatKernel d (2 * t) y : ℝ) : ℂ)) = fun y =>
        (((2 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-(((1 / (2 * (2 * t)) : ℝ)) : ℂ) * ‖y‖ ^ 2 + Complex.I * ⟪ζ, y⟫) := by
    funext y
    rw [heatKernel, Complex.ofReal_mul, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun, integral_const_mul, h, finrank_Rd]
  have h1 : ((Real.pi : ℂ) / (((1 / (2 * (2 * t)) : ℝ)) : ℂ)) ^ ((d : ℂ) / 2) =
      (((2 * Real.pi * (2 * t)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / (((1 / (2 * (2 * t)) : ℝ)) : ℂ)) =
        ((2 * Real.pi * (2 * t) : ℝ) : ℂ) by push_cast; field_simp,
      Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have h3 : Complex.I ^ 2 * (‖ζ‖ : ℂ) ^ 2 / (4 * (((1 / (2 * (2 * t)) : ℝ)) : ℂ)) =
      ((-(t * ‖ζ‖ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.I_sq]
    push_cast
    field_simp
    ring
  rw [h1, h3, ← Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (by positivity), show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero,
    Complex.ofReal_one, one_mul]

/-- The joint integrand `(y,t) ↦ e^{-t} g_{2t}(y)` on `ℝ^d × (0,∞)`. -/
theorem measurable_maternJoint :
    Measurable (fun p : Rd d × ℝ => Real.exp (-p.2) * heatKernel d (2 * p.2) p.1) := by
  unfold heatKernel
  fun_prop

theorem integrable_maternJoint :
    Integrable (fun p : Rd d × ℝ => Real.exp (-p.2) * heatKernel d (2 * p.2) p.1)
      ((volume : Measure (Rd d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff' measurable_maternJoint.aestronglyMeasurable]
  refine ⟨(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) =>
    show Integrable (fun x : Rd d => Real.exp (-t) * heatKernel d (2 * t) x) volume from
      (integrable_heatKernel (by positivity)).const_mul _), ?_⟩
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    have := Real.GammaIntegral_convergent (s := 1) one_pos
    simpa using this
  refine hexp.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  have hn : (fun x : Rd d => ‖Real.exp (-t) * heatKernel d (2 * t) x‖) =
      fun x => Real.exp (-t) * heatKernel d (2 * t) x := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (heatKernel_nonneg (by positivity) x))]
  show Real.exp (-t) = ∫ x, ‖Real.exp (-t) * heatKernel d (2 * t) x‖
  rw [hn, integral_const_mul, integral_heatKernel_volume (by positivity), mul_one]

theorem maternGreen_eq_heat (y : Rd d) :
    maternGreen d y = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * heatKernel d (2 * t) y := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [heatKernel, show 2 * Real.pi * (2 * t) = 4 * Real.pi * t by ring,
    show 2 * (2 * t) = 4 * t by ring]

theorem maternGreen_fun_eq_heat :
    maternGreen d = fun y => ∫ t in Ioi (0 : ℝ), Real.exp (-t) * heatKernel d (2 * t) y :=
  funext maternGreen_eq_heat

theorem maternGreen_nonneg (y : Rd d) : 0 ≤ maternGreen d y := by
  rw [maternGreen_eq_heat]
  exact setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) =>
    mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg (by positivity) y)

theorem integrable_maternGreen : Integrable (maternGreen d) := by
  rw [maternGreen_fun_eq_heat]
  exact (integrable_maternJoint (d := d)).integral_prod_left

theorem measurable_maternGreen : Measurable (maternGreen d) := by
  have h : StronglyMeasurable (Function.uncurry fun (y : Rd d) (t : ℝ) =>
      Real.exp (-t) * heatKernel d (2 * t) y) :=
    (measurable_maternJoint (d := d)).stronglyMeasurable
  rw [maternGreen_fun_eq_heat]
  exact (h.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

/-- **`Ĝ(ζ) = (1 + |ζ|²)^{-1}`** (`lem:matern-kernel-hessian`(1)). -/
theorem integral_maternGreen_fourier (ζ : Rd d) :
    fourierPlus (fun y => (maternGreen d y : ℂ)) ζ = (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hint := integrable_maternJoint (d := d)
  have hmeas : Measurable fun p : Rd d × ℝ => Complex.exp (((⟪ζ, p.1⟫ : ℝ) : ℂ) * Complex.I) *
      ((Real.exp (-p.2) * heatKernel d (2 * p.2) p.1 : ℝ) : ℂ) :=
    (by fun_prop : Continuous fun p : Rd d × ℝ =>
      Complex.exp (((⟪ζ, p.1⟫ : ℝ) : ℂ) * Complex.I)).measurable.mul
      (Complex.measurable_ofReal.comp measurable_maternJoint)
  have hint' : Integrable (Function.uncurry fun (y : Rd d) (t : ℝ) =>
      Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (-t) * heatKernel d (2 * t) y : ℝ) : ℂ))
      ((volume : Measure (Rd d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Integrable.mono' hint.norm hmeas.aestronglyMeasurable
      (Eventually.of_forall fun p => le_of_eq ?_)
    show ‖Complex.exp (((⟪ζ, p.1⟫ : ℝ) : ℂ) * Complex.I) *
      ((Real.exp (-p.2) * heatKernel d (2 * p.2) p.1 : ℝ) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hG : ∀ y : Rd d, ((maternGreen d y : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-t) * heatKernel d (2 * t) y : ℝ) : ℂ) := fun y => by
    rw [maternGreen_eq_heat, integral_complex_ofReal]
  unfold fourierPlus
  simp_rw [hG, ← integral_const_mul]
  rw [integral_integral_swap hint']
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ∫ y : Rd d, Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) *
      ((Real.exp (-t) * heatKernel d (2 * t) y : ℝ) : ℂ) =
      ((Real.exp (-t) * Real.exp (-(t * ‖ζ‖ ^ 2)) : ℝ) : ℂ) := by
    intro t ht
    have hf : (fun y : Rd d => Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (-t) * heatKernel d (2 * t) y : ℝ) : ℂ)) = fun y =>
        ((Real.exp (-t) : ℝ) : ℂ) * (Complex.exp (((⟪ζ, y⟫ : ℝ) : ℂ) * Complex.I) *
          ((heatKernel d (2 * t) y : ℝ) : ℂ)) := by
      funext y
      push_cast
      ring
    rw [hf, integral_const_mul, integral_heatKernel_fourier ht, Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal]
  congr 1
  have hr : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  have hΓ := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) one_pos hr
  rw [Real.rpow_one, Real.Gamma_one, mul_one, one_div] at hΓ
  rw [← hΓ]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  rw [sub_self, Real.rpow_zero, one_mul, ← Real.exp_add]
  congr 1
  ring

/-- **`∫ G = 1`** (`lem:matern-kernel-hessian`(1)). -/
theorem integral_maternGreen : ∫ y, maternGreen d y = 1 := by
  have h := integral_maternGreen_fourier (d := d) 0
  simp only [fourierPlus, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, norm_zero] at h
  rw [integral_complex_ofReal] at h
  have h' : ((∫ y, maternGreen d y : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [h]
    norm_num
  exact_mod_cast h'

/-! ## The density of the orbit -/

/-- The Matérn law of index `1` has the density `G`. -/
theorem maternLaw_eq_withDensity {μI : Measure (Rd d)} (hμI : IsMaternLaw 1 μI) :
    μI = volume.withDensity (fun y => ENNReal.ofReal (maternGreen d y)) := by
  haveI := hμI.1
  haveI : IsFiniteMeasure (volume.withDensity fun y : Rd d => ENNReal.ofReal (maternGreen d y)) :=
    isFiniteMeasure_withDensity_ofReal integrable_maternGreen.2
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [hμI.2, charFun_apply, integral_withDensity_eq_integral_toReal_smul
    measurable_maternGreen.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Real.rpow_neg_one, ← integral_maternGreen_fourier ω, fourierPlus]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (maternGreen_nonneg y), Complex.real_smul, real_inner_comm, mul_comm]

/-- **`K_Σ` is a density of the Matérn orbit of index `1` at `Σ`** (`lem:matern-kernel-hessian`(1)),
by `x = Σ^{1/2}y`. -/
theorem maternOrbit_eq_withDensity {μI : Measure (Rd d)} (hμI : IsMaternLaw 1 μI) {T : Mat d}
    (hT : T.PosDef) :
    affineOrbit μI T = volume.withDensity (fun x => ENNReal.ofReal (maternDensity T x)) := by
  set A := msqrt T with hA
  have hU : IsUnit A.det := msqrt_mem_glSet hT
  have hdA : A.det ≠ 0 := hU.ne_zero
  have hdT := hT.det_pos
  have hAm : Measurable (lin A) := (lin A).continuous.measurable
  rw [affineOrbit, push, maternLaw_eq_withDensity hμI, ← hA]
  ext s hs
  rw [Measure.map_apply hAm hs, withDensity_apply _ (hAm hs), withDensity_apply _ hs]
  have hK : Measurable fun x => s.indicator (fun x => ENNReal.ofReal (maternDensity T x)) x :=
    ((measurable_const.mul (measurable_maternGreen.comp (lin A⁻¹).continuous.measurable)).ennreal_ofReal
      : Measurable fun x => ENNReal.ofReal (maternDensity T x)).indicator hs
  have h := lintegral_comp_lin hdA hK
  rw [abs_det_msqrt hT, lintegral_indicator hs] at h
  have hpt : ∀ y, s.indicator (fun x => ENNReal.ofReal (maternDensity T x)) (lin A y) =
      ENNReal.ofReal (T.det ^ (-(1 : ℝ) / 2)) *
        ((lin A) ⁻¹' s).indicator (fun y => ENNReal.ofReal (maternGreen d y)) y := by
    intro y
    by_cases hy : lin A y ∈ s
    · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ (lin A) ⁻¹' s from hy), maternDensity,
        ← hA, lin_inv_mul_apply hU, ENNReal.ofReal_mul (by positivity)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉ (lin A) ⁻¹' s from hy), mul_zero]
  simp_rw [hpt] at h
  rw [lintegral_const_mul _ (measurable_maternGreen.ennreal_ofReal.indicator (hAm hs)),
    lintegral_indicator (hAm hs)] at h
  have hK2 : (T.det ^ ((1 : ℝ) / 2))⁻¹ = T.det ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg hdT.le]; ring_nf
  rw [hK2] at h
  have hne : ENNReal.ofReal (T.det ^ (-(1 : ℝ) / 2)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  exact (ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 h

/-! ## The second derivative of `G` -/

theorem hasFDerivAt_maternGreen {x : Rd d} (hx : x ≠ 0) :
    HasFDerivAt (maternGreen d) (maternProfile1 d (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x := by
  have hG : maternGreen d = fun y : Rd d => maternProfile d (‖y‖ ^ 2) :=
    funext maternGreen_eq_profile
  rw [hG]
  have h := (hasDerivAt_maternProfile (d := d) (pow_pos (norm_pos_iff.2 hx) 2)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  exact h

/-- **`∂_v∂_w G(x) = 2F'(|x|²)⟨w,v⟩ + 4F''(|x|²)⟨w,x⟩⟨x,v⟩`** for `x ≠ 0`. -/
theorem fderiv_fderiv_maternGreen {x : Rd d} (hx : x ≠ 0) (v w : Rd d) :
    fderiv ℝ (fderiv ℝ (maternGreen d)) x v w =
      maternProfile1 d (‖x‖ ^ 2) * (2 * ⟪w, v⟫) +
        2 * ⟪w, x⟫ * (maternProfile2 d (‖x‖ ^ 2) * (2 * ⟪x, v⟫)) := by
  have hopen : IsOpen ({0}ᶜ : Set (Rd d)) := isOpen_compl_singleton
  have hev : (fun y => fderiv ℝ (maternGreen d) y w) =ᶠ[𝓝 x]
      fun y => maternProfile1 d (‖y‖ ^ 2) * (2 * ⟪w, y⟫) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(hasFDerivAt_maternGreen hy).fderiv]
    simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    rw [real_inner_comm]
    push_cast
    ring
  have hg : HasFDerivAt (fun y => maternProfile1 d (‖y‖ ^ 2) * (2 * ⟪w, y⟫))
      (maternProfile1 d (‖x‖ ^ 2) • ((2 : ℝ) • innerSL ℝ w) +
        (2 * ⟪w, x⟫) • (maternProfile2 d (‖x‖ ^ 2) • (2 • innerSL ℝ x))) x := by
    have h1 := (hasDerivAt_maternProfile1 (d := d) (pow_pos (norm_pos_iff.2 hx) 2)).comp_hasFDerivAt
      x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have h2 := ((innerSL ℝ w).hasFDerivAt (x := x)).const_mul (2 : ℝ)
    exact h1.mul h2
  have hC : ContDiffAt ℝ 2 (maternGreen d) x :=
    (contDiffOn_maternGreen.contDiffAt (hopen.mem_nhds hx)).of_le (WithTop.coe_le_coe.2 le_top)
  have hD : DifferentiableAt ℝ (fderiv ℝ (maternGreen d)) x :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h3 := hD.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have h4 := h3.unique (hg.congr_of_eventuallyEq hev)
  have h5 := congrArg (fun L : Rd d →L[ℝ] ℝ => L v) h4
  simp only [_root_.add_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul] at h5
  rw [h5]
  push_cast
  ring

/-- **`∇·P∇G(x) = 4F''(|x|²)⟨x,Px⟩ + 2F'(|x|²) tr P`** for `x ≠ 0`. -/
theorem secondOrderOp_maternGreen (P : Mat d) {x : Rd d} (hx : x ≠ 0) :
    secondOrderOp P (maternGreen d) x =
      4 * maternProfile2 d (‖x‖ ^ 2) * quad P x + 2 * maternProfile1 d (‖x‖ ^ 2) * P.trace := by
  set F1 := maternProfile1 d (‖x‖ ^ 2)
  set F2 := maternProfile2 d (‖x‖ ^ 2)
  have hterm : ∀ j k : Fin d, P j k * iteratedFDeriv ℝ 2 (maternGreen d) x ![ebasis j, ebasis k] =
      2 * F1 * (if k = j then P j j else 0) + 4 * F2 * ((x j * x k) * P j k) := by
    intro j k
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [fderiv_fderiv_maternGreen hx, inner_ebasis_left, inner_ebasis_left, real_inner_comm,
      inner_ebasis_left, ebasis_apply]
    split_ifs with h
    · subst h; ring
    · ring
  rw [secondOrderOp]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [quad_eq_sum, Matrix.trace]
  simp only [Matrix.diag]
  ring

/-! ## The substitution `t = r²s` -/

/-- **`J_m(r) := ∫₀^∞ e^{-r²s} s^m e^{-1/4s} ds`**. -/
noncomputable def maternLapS (m r : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s))

/-- **`L_m(r²) = (r²)^{m+1} J_m(r)`**, the substitution `t = r²s`. -/
theorem maternLap_sq_eq {r : ℝ} (hr : 0 < r) (m : ℝ) :
    maternLap m (r ^ 2) = (r ^ 2) ^ (m + 1) * maternLapS m r := by
  have hr2 : 0 < r ^ 2 := by positivity
  have h := integral_comp_mul_left_Ioi
    (fun t => Real.exp (-t) * t ^ m * Real.exp (-(r ^ 2) / (4 * t))) 0 hr2
  simp only [mul_zero, smul_eq_mul] at h
  have hcongr : ∫ s in Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * (r ^ 2 * s) ^ m *
      Real.exp (-(r ^ 2) / (4 * (r ^ 2 * s))) =
      (r ^ 2) ^ m * ∫ s in Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * s ^ m *
        Real.exp (-1 / (4 * s)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
    rw [Real.mul_rpow hr2.le hs.le, show -(r ^ 2) / (4 * (r ^ 2 * s)) = -1 / (4 * s) by
      field_simp]
    ring
  rw [hcongr] at h
  unfold maternLap maternLapS
  rw [Real.rpow_add_one hr2.ne']
  calc ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ m * Real.exp (-(r ^ 2) / (4 * t))
      = r ^ 2 * ((r ^ 2)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ m *
          Real.exp (-(r ^ 2) / (4 * t))) := by rw [← mul_assoc, mul_inv_cancel₀ hr2.ne', one_mul]
    _ = _ := by rw [← h]; ring

theorem maternA_eq (r : ℝ) :
    maternA d r = 1 / 4 * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLapS (-(d : ℝ) / 2 - 1 - 1) r) := by
  unfold maternA maternLapS
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  simp only [maternKappa]
  rw [Real.mul_rpow (by positivity) hs.le, Real.rpow_sub_one hs.ne', Real.rpow_sub_one hs.ne']
  field_simp

theorem maternB_eq (r : ℝ) :
    maternB d r = 1 / 2 * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLapS (-(d : ℝ) / 2 - 1) r) := by
  unfold maternB maternLapS
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  simp only [maternKappa]
  rw [Real.mul_rpow (by positivity) hs.le, Real.rpow_sub_one hs.ne']
  field_simp

theorem sq_rpow_neg_half {r : ℝ} (hr : 0 < r) : (r ^ 2) ^ (-(d : ℝ) / 2) = (r ^ d)⁻¹ := by
  rw [neg_div, Real.rpow_neg (by positivity), ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem maternA_eq_profile2 {r : ℝ} (hr : 0 < r) :
    maternA d r = 4 * r ^ d * r ^ 2 * maternProfile2 d (r ^ 2) := by
  rw [maternA_eq, maternProfile2, maternLap_sq_eq hr,
    show -(d : ℝ) / 2 - 1 - 1 + 1 = -(d : ℝ) / 2 - 1 by ring,
    Real.rpow_sub_one (by positivity), sq_rpow_neg_half hr]
  field_simp
  ring

theorem maternB_eq_profile1 {r : ℝ} (hr : 0 < r) :
    maternB d r = -2 * r ^ d * maternProfile1 d (r ^ 2) := by
  rw [maternB_eq, maternProfile1, maternLap_sq_eq hr,
    show -(d : ℝ) / 2 - 1 + 1 = -(d : ℝ) / 2 by ring, sq_rpow_neg_half hr]
  field_simp
  ring

/-- **`r^d ∇·P∇G(rŷ) = ⟨ŷ,Pŷ⟩𝓐(r) - (tr P)𝓑(r)`** (`lem:matern-kernel-hessian`(2)). -/
theorem maternGreen_hessian_eq (P : Mat d) {r : ℝ} (hr : 0 < r) {y : Rd d} (hy : ‖y‖ = 1) :
    r ^ d * secondOrderOp P (maternGreen d) (r • y) =
      quad P y * maternA d r - P.trace * maternB d r := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hx : r • y ≠ 0 := smul_ne_zero hr.ne' hy0
  have hn : ‖r • y‖ ^ 2 = r ^ 2 := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hy, mul_one]
  have hq : quad P (r • y) = r ^ 2 * quad P y := by
    unfold quad
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [secondOrderOp_maternGreen P hx, hn, hq, maternA_eq_profile2 hr, maternB_eq_profile1 hr]
  ring

/-! ## The limits as `r ↓ 0` -/

/-- `s ↦ s^m e^{-1/4s}` is integrable on `(0,∞)` for `m < -1`: the shared library's
`ScaleSpace.inverse_gamma_integral` at `c = 1/4`, `b = -m - 1` (Q-0363). Mathlib types only. -/
theorem integrableOn_rpow_exp_inv {m : ℝ} (hm : m < -1) :
    IntegrableOn (fun s : ℝ => s ^ m * Real.exp (-1 / (4 * s))) (Ioi 0) := by
  refine (ScaleSpace.inverse_gamma_integral (b := -m - 1) (c := 1 / 4) (by linarith)
    (by norm_num)).1.congr_fun (fun s _ => ?_) measurableSet_Ioi
  dsimp only
  rw [show -1 - (-m - 1) = m by ring, show -(1 / 4 : ℝ) / s = -1 / (4 * s) by ring]

/-- **`∫₀^∞ s^m e^{-1/4s} ds = 4^{-m-1} Γ(-m-1)`** for `m < -1`: the shared library's
`ScaleSpace.inverse_gamma_integral` at `c = 1/4`, `b = -m - 1` (Q-0363). -/
theorem integral_rpow_exp_inv {m : ℝ} (hm : m < -1) :
    ∫ s in Ioi (0 : ℝ), s ^ m * Real.exp (-1 / (4 * s)) = 4 ^ (-m - 1) * Real.Gamma (-m - 1) := by
  have h := (ScaleSpace.inverse_gamma_integral (b := -m - 1) (c := 1 / 4) (by linarith)
    (by norm_num)).2
  rw [show (1 / (1 / 4 : ℝ)) = 4 by norm_num] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [show -1 - (-m - 1) = m by ring, show -(1 / 4 : ℝ) / s = -1 / (4 * s) by ring]

/-- `J_m(r) → ∫₀^∞ s^m e^{-1/4s} ds` as `r ↓ 0`, for `m < -1`, by dominated convergence. -/
theorem tendsto_maternLapS {m : ℝ} (hm : m < -1) :
    Tendsto (maternLapS m) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi (0 : ℝ), s ^ m * Real.exp (-1 / (4 * s)))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => s ^ m * Real.exp (-1 / (4 * s))) ?_ ?_ (integrableOn_rpow_exp_inv hm) ?_
  · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun s : ℝ =>
      Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s))).aestronglyMeasurable
  · refine Eventually.of_forall fun r =>
      (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 0 < s) => ?_)
    have he : Real.exp (-(r ^ 2 * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
    calc Real.exp (-(r ^ 2 * s)) * (s ^ m * Real.exp (-1 / (4 * s)))
        ≤ 1 * (s ^ m * Real.exp (-1 / (4 * s))) :=
          mul_le_mul_of_nonneg_right he (by positivity)
      _ = s ^ m * Real.exp (-1 / (4 * s)) := one_mul _
  · refine Eventually.of_forall fun s => ?_
    have hc : Continuous fun r : ℝ => Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s)) := by
      fun_prop
    have h := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, neg_zero,
      Real.exp_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds

theorem maternBd_pos (hd : 1 ≤ d) : 0 < maternBd d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := Real.Gamma_pos_of_pos (div_pos hd' two_pos)
  unfold maternBd
  positivity

/-- **`𝓑(r) → 𝓑_d`** as `r ↓ 0` (`lem:matern-kernel-hessian`(2)). -/
theorem tendsto_maternB (hd : 1 ≤ d) : Tendsto (maternB d) (𝓝[>] 0) (𝓝 (maternBd d)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : -(d : ℝ) / 2 - 1 < -1 := by linarith
  have h := ((tendsto_maternLapS hm).const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2))).const_mul
    (1 / 2 : ℝ)
  rw [integral_rpow_exp_inv hm, show -(-(d : ℝ) / 2 - 1) - 1 = (d : ℝ) / 2 by ring] at h
  have hfun : maternB d = fun r =>
      1 / 2 * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLapS (-(d : ℝ) / 2 - 1) r) :=
    funext maternB_eq
  rw [hfun]
  convert h using 2
  have h4 : (4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num), show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  rw [maternBd, Real.mul_rpow (by norm_num) Real.pi_pos.le]
  linear_combination (-(1 / 2) * Real.pi ^ (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)) * h4

/-- **`𝓐(r) → d𝓑_d`** as `r ↓ 0` (`lem:matern-kernel-hessian`(2)). -/
theorem tendsto_maternA (hd : 1 ≤ d) :
    Tendsto (maternA d) (𝓝[>] 0) (𝓝 (d * maternBd d)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : -(d : ℝ) / 2 - 1 - 1 < -1 := by linarith
  have h := ((tendsto_maternLapS hm).const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2))).const_mul
    (1 / 4 : ℝ)
  rw [integral_rpow_exp_inv hm, show -(-(d : ℝ) / 2 - 1 - 1) - 1 = (d : ℝ) / 2 + 1 by ring,
    Real.rpow_add_one (by norm_num), Real.Gamma_add_one (by positivity)] at h
  have hfun : maternA d = fun r =>
      1 / 4 * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * maternLapS (-(d : ℝ) / 2 - 1 - 1) r) :=
    funext maternA_eq
  rw [hfun]
  convert h using 2
  have h4 : (4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num), show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  rw [maternBd, Real.mul_rpow (by norm_num) Real.pi_pos.le]
  linear_combination
    (-(1 / 2) * (d : ℝ) * Real.pi ^ (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)) * h4

/-- **The uniform limit** `r^d ∇·P∇G(rŷ) → 𝓑_d(d⟨ŷ,Pŷ⟩ - tr P)` on the unit sphere
(`lem:matern-kernel-hessian`(2)). -/
theorem tendstoUniformlyOn_maternHessian (hd : 1 ≤ d) (P : Mat d) :
    TendstoUniformlyOn
      (fun (r : ℝ) (y : Rd d) => r ^ d * secondOrderOp P (maternGreen d) (r • y))
      (fun y => maternBd d * ((d : ℝ) * quad P y - P.trace)) (𝓝[>] 0) (Metric.sphere 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set C := ‖lin P‖ + |P.trace| + 1 with hC
  have hCpos : 0 < C := by positivity
  have hδ : 0 < ε / C := div_pos hε hCpos
  have hA := (tendsto_maternA hd).eventually (Metric.ball_mem_nhds _ hδ)
  have hB := (tendsto_maternB hd).eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hA, hB, self_mem_nhdsWithin] with r hAr hBr hr y hy
  have hr' : 0 < r := hr
  have hy1 : ‖y‖ = 1 := by simpa using hy
  rw [maternGreen_hessian_eq P hr' hy1]
  rw [Real.dist_eq] at hAr hBr
  rw [Real.dist_eq]
  have hq : |quad P y| ≤ ‖lin P‖ := by
    have := abs_quad_le P y
    rwa [hy1, one_pow, mul_one] at this
  have e : maternBd d * ((d : ℝ) * quad P y - P.trace) - (quad P y * maternA d r -
      P.trace * maternB d r) = -(quad P y * (maternA d r - d * maternBd d)) +
        P.trace * (maternB d r - maternBd d) := by ring
  rw [e]
  calc |-(quad P y * (maternA d r - d * maternBd d)) + P.trace * (maternB d r - maternBd d)|
      ≤ |-(quad P y * (maternA d r - d * maternBd d))| +
          |P.trace * (maternB d r - maternBd d)| := abs_add_le _ _
    _ = |quad P y| * |maternA d r - d * maternBd d| +
          |P.trace| * |maternB d r - maternBd d| := by rw [abs_neg, abs_mul, abs_mul]
    _ ≤ ‖lin P‖ * (ε / C) + |P.trace| * (ε / C) := by
        gcongr
    _ = (‖lin P‖ + |P.trace|) * (ε / C) := by ring
    _ < C * (ε / C) := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by field_simp

/-! ## The node -/

/-- **`lem:matern-kernel-hessian`(1)**, the kernel. -/
theorem matern_kernel (_hd : 1 ≤ d) :
    (∀ y : Rd d, 0 ≤ maternGreen d y) ∧ Integrable (maternGreen d) ∧ ∫ y, maternGreen d y = 1 ∧
      (∀ ζ : Rd d, fourierPlus (fun y => (maternGreen d y : ℂ)) ζ =
        (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternGreen d) {0}ᶜ ∧
      ∀ μI : Measure (Rd d), IsMaternLaw 1 μI → ∀ T : Mat d, T.PosDef →
        affineOrbit μI T = volume.withDensity (fun x => ENNReal.ofReal (maternDensity T x)) :=
  ⟨maternGreen_nonneg, integrable_maternGreen, integral_maternGreen, integral_maternGreen_fourier,
    contDiffOn_maternGreen, fun _ hμI _ hT => maternOrbit_eq_withDensity hμI hT⟩

/-- **`lem:matern-kernel-hessian`(2)**, the Hessian near the origin. -/
theorem matern_kernel_hessian (hd : 1 ≤ d) :
    (∀ P : Mat d, P.IsHermitian → ∀ r : ℝ, 0 < r → ∀ y : Rd d, ‖y‖ = 1 →
      r ^ d * secondOrderOp P (maternGreen d) (r • y) =
        quad P y * maternA d r - P.trace * maternB d r) ∧
      Tendsto (maternA d) (𝓝[>] 0) (𝓝 (d * maternBd d)) ∧
      Tendsto (maternB d) (𝓝[>] 0) (𝓝 (maternBd d)) ∧ 0 < maternBd d ∧
      ∀ P : Mat d, P.PosSemidef →
        TendstoUniformlyOn (fun (r : ℝ) (y : Rd d) => r ^ d * secondOrderOp P (maternGreen d) (r • y))
          (fun y => maternBd d * ((d : ℝ) * quad P y - P.trace)) (𝓝[>] 0) (Metric.sphere 0 1) :=
  ⟨fun P _ _ hr _ hy => maternGreen_hessian_eq P hr hy, tendsto_maternA hd, tendsto_maternB hd,
    maternBd_pos hd, fun P _ => tendstoUniformlyOn_maternHessian hd P⟩

end AffineHemigroup
