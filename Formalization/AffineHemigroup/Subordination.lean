/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.GaussMixture
import AffineHemigroup.RadialTransform
import AffineHemigroup.MaternLaw
import ScaleSpaceCore.InverseGamma
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The heat kernel subordinated by a Gamma-type Lévy measure

Blueprint: `blueprint/src/parts/05-orbits.tex`, the proof of `prop:tempered-step-cone`, clauses
(3)(b) and (4) (wave 2, group D, Q-0281). For `a ≥ 0` the profile

  `F_a(r) := ∫₀^∞ (4πt)^{-d/2} t^{-1-a} e^{-1/(4t) - r²t} dt`

is the radial part of the Lévy density `∫₀^∞ h_s(x) s^{-1-a} e^{-s} ds = |x|^{-d-2a} F_a(|x|)`,
`h_s` the heat kernel with transform `e^{-s|ω|²}`; its exponent is
`∫₀^∞ (1 - e^{-s|ω|²}) s^{-1-a} e^{-s} ds`, a Gamma integral for `0 < a < 1` and Frullani's for
`a = 0`. Everything here is Lean core.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The subordinated profile `F_a` -/

/-- The integrand of `F_a(r)`: `(4πt)^{-d/2} t^{-1-a} e^{-1/(4t) - r²t}`. -/
noncomputable def subIntegrand (d : ℕ) (a r t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) * Real.exp (-1 / (4 * t) - r ^ 2 * t)

/-- **`F_a(r) := ∫₀^∞ (4πt)^{-d/2} t^{-1-a} e^{-1/(4t) - r²t} dt`**, the profile of the heat
kernel subordinated by `s^{-1-a}e^{-s}ds` (`prop:tempered-step-cone`(3)(b), (4)). -/
noncomputable def subProfile (d : ℕ) (a r : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), subIntegrand d a r t

/-- `(4πt)^{-d/2} t^{-1-a} = (4π)^{-d/2} t^{-1-(a + d/2)}` for `t > 0`. -/
theorem heat_rpow_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-1 - (a + (d : ℝ) / 2)) := by
  rw [Real.mul_rpow (by positivity) ht.le, mul_assoc, ← Real.rpow_add ht]
  ring_nf

/-- **The bound of every `F_a` integrand**: `t ↦ (4πt)^{-d/2} t^{-1-a} e^{-η/(4t)}` is integrable on
`(0,∞)` for `η > 0` (`a ≥ 0`, `d ≥ 1`), and at `η = 1` its integral is
`(4π)^{-d/2} 4^{a + d/2} Γ(a + d/2)`. -/
theorem heat_bound_integral (hd : 1 ≤ d) {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) *
        Real.exp (-η / (4 * t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) *
        Real.exp (-η / (4 * t)) =
        (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((4 / η) ^ (a + (d : ℝ) / 2) *
          Real.Gamma (a + (d : ℝ) / 2)) := by
  have hb : 0 < a + (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hint, hval⟩ := ScaleSpace.inverse_gamma_integral hb (by positivity : 0 < η / 4)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) *
      Real.exp (-η / (4 * t)) = (4 * Real.pi) ^ (-(d : ℝ) / 2) *
        (t ^ (-1 - (a + (d : ℝ) / 2)) * Real.exp (-(η / 4) / t)) := by
    intro t ht
    rw [heat_rpow_eq ht, mul_assoc]
    congr 3
    field_simp
  refine ⟨IntegrableOn.congr_fun (hint.const_mul _) (fun t ht => (hpt t ht).symm) measurableSet_Ioi,
    ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hval]
  congr 2
  field_simp

theorem subIntegrand_nonneg {a r t : ℝ} (ht : 0 < t) : 0 ≤ subIntegrand d a r t := by
  unfold subIntegrand; positivity

/-- `F_a`'s integrand decreases in `r²`. -/
theorem subIntegrand_le {a r s t : ℝ} (ht : 0 < t) (hrs : r ^ 2 ≤ s ^ 2) :
    subIntegrand d a s t ≤ subIntegrand d a r t := by
  unfold subIntegrand
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith

theorem subIntegrand_zero {a t : ℝ} :
    subIntegrand d a 0 t = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) *
      Real.exp (-1 / (4 * t)) := by
  simp [subIntegrand]

theorem measurable_subIntegrand (a r : ℝ) : Measurable (subIntegrand d a r) := by
  unfold subIntegrand; fun_prop

theorem integrableOn_subIntegrand (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    IntegrableOn (subIntegrand d a r) (Ioi 0) := by
  refine Integrable.mono' (heat_bound_integral hd ha one_pos).1
    (measurable_subIntegrand a r).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_of_nonneg (subIntegrand_nonneg ht), ← subIntegrand_zero]
  exact subIntegrand_le ht (by nlinarith)

theorem subProfile_nonneg (a r : ℝ) : 0 ≤ subProfile d a r :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => subIntegrand_nonneg ht

/-- `F_a` is nonincreasing on `[0,∞)`. -/
theorem subProfile_antitone (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    AntitoneOn (subProfile d a) (Ici 0) := by
  intro r hr s hs hrs
  refine setIntegral_mono_on (integrableOn_subIntegrand hd ha s)
    (integrableOn_subIntegrand hd ha r) measurableSet_Ioi fun t ht => subIntegrand_le ht ?_
  have hr0 : (0 : ℝ) ≤ r := hr
  nlinarith

/-- `F_a` is continuous (dominated by its integrand at `r = 0`). -/
theorem continuous_subProfile (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) : Continuous (subProfile d a) := by
  refine continuous_of_dominated (bound := subIntegrand d a 0)
    (fun r => (measurable_subIntegrand a r).aestronglyMeasurable) (fun r => ?_)
    (integrableOn_subIntegrand hd ha 0) (Eventually.of_forall fun t => ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_of_nonneg (subIntegrand_nonneg ht)]
    exact subIntegrand_le ht (by nlinarith)
  · unfold subIntegrand; fun_prop

/-- **`F_a(0) = (4π)^{-d/2} 4^{a + d/2} Γ(a + d/2)`**, positive. -/
theorem subProfile_zero (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    subProfile d a 0 = (4 * Real.pi) ^ (-(d : ℝ) / 2) * (4 ^ (a + (d : ℝ) / 2) *
      Real.Gamma (a + (d : ℝ) / 2)) := by
  have h := (heat_bound_integral hd ha one_pos).2
  rw [div_one] at h
  rw [← h, subProfile]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => subIntegrand_zero

theorem subProfile_zero_pos (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) : 0 < subProfile d a 0 := by
  rw [subProfile_zero hd ha]
  have hb : 0 < a + (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := Real.Gamma_pos_of_pos hb
  positivity

/-- **The exponential bound**: for `0 < η < 1` and `r ≥ 0`,
`F_a(r) ≤ C_η e^{-(1-η)r}`, `C_η := ∫₀^∞ (4πt)^{-d/2} t^{-1-a} e^{-η/(4t)} dt`, from
`1/(4t) + r²t ≥ (1-η)r + η/(4t)`. -/
theorem subProfile_le_exp (hd : 1 ≤ d) {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) (hη1 : η < 1)
    {r : ℝ} (_hr : 0 ≤ r) :
    subProfile d a r ≤ (∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - a) *
        Real.exp (-η / (4 * t))) * Real.exp (-(1 - η) * r) := by
  rw [← integral_mul_const]
  refine setIntegral_mono_on (integrableOn_subIntegrand hd ha r)
    ((heat_bound_integral hd ha hη).1.mul_const _) measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  unfold subIntegrand
  rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have key : 1 / (4 * t) + r ^ 2 * t - r = (1 - 2 * r * t) ^ 2 / (4 * t) := by
    field_simp; ring
  have hsq : 0 ≤ (1 - 2 * r * t) ^ 2 / (4 * t) := by positivity
  have h1 : (1 - η) * r ≤ (1 - η) * (1 / (4 * t) + r ^ 2 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 0 ≤ η * (r ^ 2 * t) := by positivity
  have h3 : -1 / (4 * t) = -(1 / (4 * t)) := by ring
  have h4 : -η / (4 * t) = -(η * (1 / (4 * t))) := by ring
  rw [h3, h4]
  nlinarith

/-! ## The substitution `s = |x|²t` -/

/-- The integrand `h_s(x) s^{-1-a} e^{-s}` at `|x| = ρ`, `h_s` the heat kernel with transform
`e^{-s|ω|²}`. -/
noncomputable def heatSub (d : ℕ) (a ρ s : ℝ) : ℝ :=
  (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-ρ ^ 2 / (4 * s)) * (s ^ (-1 - a) * Real.exp (-s))

/-- `(ρ²)^x = ρ^{2x}` for `ρ ≥ 0`. -/
theorem sq_rpow_eq {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) : (ρ ^ 2) ^ x = ρ ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ]; norm_num

/-- `h_{ρ²t}(ρ) (ρ²t)^{-1-a} e^{-ρ²t} = ρ^{-d-2-2a} · (F_a's integrand at ρ)`. -/
theorem heatSub_comp {a ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    heatSub d a ρ (ρ ^ 2 * t) = ρ ^ (-(d : ℝ) - 2 - 2 * a) * subIntegrand d a ρ t := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  unfold heatSub subIntegrand
  have e1 : (4 * Real.pi * (ρ ^ 2 * t)) ^ (-(d : ℝ) / 2) =
      ρ ^ (-(d : ℝ)) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (ρ ^ 2 * t) = ρ ^ 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow hρ2.le (by positivity), sq_rpow_eq hρ.le]
    congr 2
    ring
  have e2 : (ρ ^ 2 * t) ^ (-1 - a) = ρ ^ (-2 - 2 * a) * t ^ (-1 - a) := by
    rw [Real.mul_rpow hρ2.le ht.le, sq_rpow_eq hρ.le]
    congr 2
    ring
  have e3 : -ρ ^ 2 / (4 * (ρ ^ 2 * t)) = -1 / (4 * t) := by field_simp
  have e4 : ρ ^ (-(d : ℝ) - 2 - 2 * a) = ρ ^ (-(d : ℝ)) * ρ ^ (-2 - 2 * a) := by
    rw [← Real.rpow_add hρ]; ring_nf
  rw [e1, e2, e3, e4, sub_eq_add_neg (-1 / (4 * t)), Real.exp_add]
  ring_nf

/-- **The substitution `s = |x|²t`**: for `ρ > 0`, `s ↦ h_s(ρ) s^{-1-a} e^{-s}` is integrable and
`∫₀^∞ h_s(ρ) s^{-1-a} e^{-s} ds = ρ^{-d-2a} F_a(ρ)`. -/
theorem heatSub_integral (hd : 1 ≤ d) {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) :
    IntegrableOn (heatSub d a ρ) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), heatSub d a ρ s = ρ ^ (-(d : ℝ) - 2 * a) * subProfile d a ρ := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hcomp : IntegrableOn (fun t => heatSub d a ρ (ρ ^ 2 * t)) (Ioi 0) :=
    IntegrableOn.congr_fun ((integrableOn_subIntegrand hd ha ρ).const_mul
      (ρ ^ (-(d : ℝ) - 2 - 2 * a))) (fun t ht => (heatSub_comp hρ ht).symm) measurableSet_Ioi
  have hint : IntegrableOn (heatSub d a ρ) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (heatSub d a ρ) 0 hρ2).1 hcomp
    rwa [mul_zero] at this
  refine ⟨hint, ?_⟩
  have h := integral_comp_mul_left_Ioi (heatSub d a ρ) 0 hρ2
  rw [mul_zero, smul_eq_mul, setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => heatSub_comp (d := d) (a := a) hρ ht), integral_const_mul] at h
  have h2 : ∫ s in Ioi (0 : ℝ), heatSub d a ρ s =
      ρ ^ 2 * (ρ ^ (-(d : ℝ) - 2 - 2 * a) * subProfile d a ρ) := by
    rw [subProfile, h]; field_simp
  rw [h2, ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add hρ]
  ring_nf

/-! ## The heat kernel's cosine integral -/

/-- **`∫ (1 - cos⟨ω,x⟩) h_s(x) dx = 1 - e^{-s|ω|²}`** for `s > 0`, `h_s(x) = (4πs)^{-d/2}
e^{-|x|²/(4s)}` the density of `N(0, 2sI)`. -/
theorem lintegral_one_sub_cos_heat {s : ℝ} (hs : 0 < s) (ω : Rd d) :
    ∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
        ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)))) =
      ENNReal.ofReal (1 - Real.exp (-(s * ‖ω‖ ^ 2))) := by
  have hs2 : 0 < 2 * s := by positivity
  have hk : ∀ x : Rd d, (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)) =
      heatKernel d (2 * s) x := fun x => by
    unfold heatKernel; ring_nf
  have hc : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪ω, x⟫ := fun x => by linarith [Real.cos_le_one ⟪ω, x⟫]
  have hpt : ∀ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
      ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)))) =
      ((fun x => ENNReal.ofReal (heatKernel d (2 * s) x)) *
        fun x => ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫)) x := fun x => by
    simp only [Pi.mul_apply]
    rw [hk, mul_comm, ENNReal.ofReal_mul (heatKernel_nonneg hs2 x)]
  simp_rw [hpt]
  rw [← lintegral_withDensity_eq_lintegral_mul _ (continuous_heatKernel.measurable.ennreal_ofReal)
    (by fun_prop), ← gaussVar_eq_withDensity hs2]
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪ω, x⟫) (gaussVar d (2 * s)) :=
    Integrable.of_bound (by fun_prop) 2 (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hc x)]; linarith [Real.neg_one_le_cos ⟪ω, x⟫])
  have hcos : Integrable (fun x : Rd d => Real.cos ⟪ω, x⟫) (gaussVar d (2 * s)) :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hc),
    integral_sub (integrable_const _) hcos]
  have hre := ScaleSpace.re_charFun_eq_integral_cos (gaussVar d (2 * s)) ω
  rw [charFun_gaussVar hs2.le, Complex.ofReal_re] at hre
  have hcomm : ∫ x, Real.cos ⟪ω, x⟫ ∂(gaussVar d (2 * s)) =
      ∫ x, Real.cos ⟪x, ω⟫ ∂(gaussVar d (2 * s)) := by
    simp_rw [real_inner_comm]
  rw [hcomm, ← hre]
  congr 1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  congr 2
  ring

theorem heatSub_nonneg {a ρ s : ℝ} (hs : 0 < s) : 0 ≤ heatSub d a ρ s := by
  unfold heatSub; positivity

/-! ## Tonelli, and the subordinator's exponent -/

/-- **Tonelli**: `∫ (1 - cos⟨ω,x⟩) |x|^{-d-2a} F_a(|x|) dx = ∫₀^∞ s^{-1-a} e^{-s}(1 - e^{-s|ω|²}) ds`,
through `|x|^{-d-2a} F_a(|x|) = ∫₀^∞ h_s(x) s^{-1-a} e^{-s} ds` and the heat kernel's cosine
integral. -/
theorem lintegral_one_sub_cos_subProfile (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (ω : Rd d) :
    ∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
        (‖x‖ ^ (-(d : ℝ) - 2 * a) * subProfile d a ‖x‖)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 - a) * Real.exp (-s)) *
        ENNReal.ofReal (1 - Real.exp (-(s * ‖ω‖ ^ 2))) := by
  have hc : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪ω, x⟫ := fun x => by
    linarith [Real.cos_le_one ⟪ω, x⟫]
  have hpt : ∀ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
      (‖x‖ ^ (-(d : ℝ) - 2 * a) * subProfile d a ‖x‖)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * heatSub d a ‖x‖ s) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
      obtain ⟨hint, hval⟩ := heatSub_integral hd ha hρ
      rw [← hval, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)]
      exact (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun s hs => mul_nonneg (hc x) (heatSub_nonneg hs))
  simp_rw [hpt]
  have hmeas : Measurable (Function.uncurry fun (x : Rd d) (s : ℝ) =>
      ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * heatSub d a ‖x‖ s)) := by
    unfold heatSub Function.uncurry; fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hfac : ∀ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * heatSub d a ‖x‖ s) =
      ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
        ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)))) *
        ENNReal.ofReal (s ^ (-1 - a) * Real.exp (-s)) := by
    intro x
    rw [← ENNReal.ofReal_mul (mul_nonneg (hc x) (by positivity))]
    unfold heatSub
    ring_nf
  simp_rw [hfac]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_one_sub_cos_heat hs0, mul_comm]

/-- **The Gamma subordinator's exponent**: for `0 < a < 1` and `u ≥ 0`,
`∫₀^∞ s^{-1-a} e^{-s}(1 - e^{-us}) ds = Γ(1-a)/a · ((1+u)^a - 1)`. -/
theorem lintegral_gamma_subordinator {a u : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hu : 0 ≤ u) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 - a) * Real.exp (-s)) *
        ENNReal.ofReal (1 - Real.exp (-(s * u))) =
      ENNReal.ofReal (Real.Gamma (1 - a) / a * ((1 + u) ^ a - 1)) := by
  -- the integrand is an integral over `σ ∈ (1, 1+u]`
  have hin : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 - a) * Real.exp (-s)) *
      ENNReal.ofReal (1 - Real.exp (-(s * u))) =
      ∫⁻ σ in Ioc 1 (1 + u), ENNReal.ofReal (s ^ (-a) * Real.exp (-(σ * s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hint : IntegrableOn (fun σ : ℝ => s ^ (-a) * Real.exp (-(σ * s))) (Ioc 1 (1 + u)) :=
      (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun σ => by positivity), integral_const_mul,
      ← intervalIntegral.integral_of_le (by linarith), integral_exp_neg_mul_param hs0,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : s ^ (-1 - a) = s ^ (-a) / s := by
      rw [show -1 - a = -a - 1 by ring, Real.rpow_sub_one hs0.ne']
    rw [h1, one_mul, add_mul, one_mul, neg_add, Real.exp_add]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hin]
  have hmeas : Measurable (Function.uncurry fun (s σ : ℝ) =>
      ENNReal.ofReal (s ^ (-a) * Real.exp (-(σ * s)))) := by
    unfold Function.uncurry; fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  -- the inner integral is a Gamma integral
  have hin2 : ∀ σ ∈ Ioc (1 : ℝ) (1 + u), ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-a) * Real.exp (-(σ * s))) =
      ENNReal.ofReal (σ ^ (a - 1) * Real.Gamma (1 - a)) := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have hint : IntegrableOn (fun s : ℝ => s ^ (-a) * Real.exp (-(σ * s))) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -a) (b := σ) (by linarith)
        le_rfl hσ0
      refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
      simp [Real.rpow_one, neg_mul]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
        have : (0 : ℝ) < s := hs
        positivity))]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - a) (r := σ) (by linarith) hσ0
    rw [show 1 - a - 1 = -a by ring] at h
    rw [h]
    congr 1
    rw [one_div, Real.inv_rpow hσ0.le, ← Real.rpow_neg hσ0.le]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioc hin2]
  have hint : IntegrableOn (fun σ : ℝ => σ ^ (a - 1) * Real.Gamma (1 - a)) (Ioc 1 (1 + u)) :=
    (ContinuousOn.integrableOn_Icc (ContinuousOn.mul (fun σ hσ => (Real.continuousAt_rpow_const
      _ _ (Or.inl (by linarith [hσ.1]))).continuousWithinAt) continuousOn_const)).mono_set
      Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ => by
      have : (0 : ℝ) < σ := by linarith [hσ.1]
      have := Real.Gamma_pos_of_pos (show 0 < 1 - a by linarith)
      positivity)),
    integral_mul_const, ← intervalIntegral.integral_of_le (by linarith),
    integral_rpow (Or.inl (by linarith))]
  congr 1
  rw [show a - 1 + 1 = a by ring, Real.one_rpow]
  field_simp

/-- **Frullani's subordinator** (`a = 0`): `∫₀^∞ s⁻¹ e^{-s}(1 - e^{-us}) ds = log(1 + u)` for
`u ≥ 0`. -/
theorem lintegral_frullani_subordinator {u : ℝ} (hu : 0 ≤ u) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 - (0 : ℝ)) * Real.exp (-s)) *
        ENNReal.ofReal (1 - Real.exp (-(s * u))) = ENNReal.ofReal (Real.log (1 + u)) := by
  rcases hu.lt_or_eq with hu | rfl
  · have h := lintegral_frullani (a := 1) (b := 1 + u) one_pos (by linarith)
    rw [div_one] at h
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [sub_zero, Real.rpow_neg_one, one_mul, add_mul, one_mul, neg_add, Real.exp_add]
    field_simp
  · simp

end AffineHemigroup
