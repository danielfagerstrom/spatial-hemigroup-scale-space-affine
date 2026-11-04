/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MaternKernel
import AffineHemigroup.Polar
import AffineHemigroup.DiagonalStable
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# `prop:matern-negative-mass`: how much a step across shapes fails

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:matern-negative-mass`. Wave 2, group J,
Q-0281.

The would-be increment `ρ` of a step `Σ ≤ Σ'` of the Matérn orbit of index `1` is the functional
`ρ(φ) = (2π)^{-d} ∫ φ̂(ω) (1 + ⟨ω,Σω⟩)/(1 + ⟨ω,Σ'ω⟩) dω`. Against a finite signed measure
it is the integral (Fubini with the inversion formula); away from the origin it is the function
`q = ∇·P∇K_{Σ'}` (the transform of a second derivative, and two integrations by parts against a
smooth cut-off of `K_{Σ'}`). Near the origin `q` is read through `lem:matern-kernel-hessian` after
the substitution `x = Σ'^{1/2}y`; polar coordinates turn the mass of `q₋` on a shell into
`∫_a^1 F(r) dr/r`, whose logarithmic growth is that of `F`'s limit; the limit is positive exactly
off the rays, and then no finite signed measure has `q` as its restriction off the origin. In the
plane the angular integral is computed in polar angle.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Topology Matrix Complex
open scoped RealInnerProductSpace ENNReal FourierTransform SchwartzMap

variable {d : ℕ}

/-! ## Fourier inversion against a finite measure -/

/-- `φ̂(ω) = 𝓕φ(-(2π)⁻¹ω)`: the blueprint's transform in Mathlib's normalisation. -/
theorem fourierPlus_eq_fourier (f : Rd d → ℂ) (ω : Rd d) :
    fourierPlus f ω = 𝓕 f ((-(2 * Real.pi)⁻¹) • ω) := by
  rw [Real.fourier_eq', fourierPlus]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  rw [inner_smul_right, real_inner_comm]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Fubini with the inversion formula**: for a Schwartz `f` and a finite measure `ν`,
`∫ 𝓕f(ξ) ν̂(2πξ) dξ = ∫ f dν`. -/
theorem integral_fourier_mul_charFun (f : 𝓢(Rd d, ℂ)) (ν : Measure (Rd d)) [IsFiniteMeasure ν] :
    ∫ ξ, 𝓕 (f : Rd d → ℂ) ξ * charFun ν ((2 * Real.pi) • ξ) = ∫ x, f x ∂ν := by
  set Φ : Rd d → ℂ := fun ξ => (𝓕 f) ξ with hΦ
  have hΦi : Integrable Φ := (𝓕 f).integrable
  have hinv : ∀ x, ∫ ξ, cexp (↑(2 * Real.pi * ⟪ξ, x⟫) * I) * Φ ξ = f x := by
    intro x
    have h := f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable
    have hx := congrFun h x
    rw [Real.fourierInv_eq'] at hx
    simp only [smul_eq_mul] at hx
    rw [hΦ]
    simp only [SchwartzMap.fourier_coe]
    exact hx
  set F : Rd d → Rd d → ℂ := fun x ξ => cexp (↑(2 * Real.pi * ⟪ξ, x⟫) * I) * Φ ξ with hF
  have hint : Integrable (Function.uncurry F) (ν.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF, Function.uncurry_def, hΦ]
      have := (𝓕 f).continuous
      fun_prop
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, one_mul]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
  have h1 : ∀ x, f x = ∫ ξ, F x ξ := fun x => (hinv x).symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1
  funext ξ
  simp only [hF]
  rw [integral_mul_const, mul_comm, charFun_apply]
  simp only [hΦ, SchwartzMap.fourier_coe]
  congr 2
  funext x
  congr 1
  rw [inner_smul_right, real_inner_comm]

theorem fourierPlus_schwartz (f : 𝓢(Rd d, ℂ)) :
    fourierPlus (f : Rd d → ℂ) =
      fun ω => ((𝓕 f : 𝓢(Rd d, ℂ)) : Rd d → ℂ) ((-(2 * Real.pi)⁻¹) • ω) := by
  funext ω
  rw [fourierPlus_eq_fourier, SchwartzMap.fourier_coe]

theorem integrable_fourierPlus (f : 𝓢(Rd d, ℂ)) : Integrable (fourierPlus (f : Rd d → ℂ)) := by
  have hc : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact neg_ne_zero.2 (inv_ne_zero this.ne')
  rw [fourierPlus_schwartz]
  exact (𝓕 f).integrable.comp_smul hc

theorem continuous_fourierPlus (f : 𝓢(Rd d, ℂ)) : Continuous (fourierPlus (f : Rd d → ℂ)) := by
  rw [fourierPlus_schwartz]
  have := (𝓕 f).continuous
  fun_prop

theorem integrable_fourierPlus_mul_charFun (f : 𝓢(Rd d, ℂ)) (ν : Measure (Rd d))
    [IsFiniteMeasure ν] : Integrable fun ω => fourierPlus (f : Rd d → ℂ) ω * charFun ν (-ω) := by
  refine (integrable_fourierPlus f).mul_bdd (c := ν.real univ) ?_
    (Eventually.of_forall fun ω => norm_charFun_le _)
  exact ((measurable_charFun (μ := ν)).comp measurable_neg).aestronglyMeasurable

/-- **`∫ φ̂(ω) ν̂(-ω) dω = (2π)^d ∫ φ dν`** for a Schwartz `φ` and a finite measure `ν`. -/
theorem integral_fourierPlus_mul_charFun (f : 𝓢(Rd d, ℂ)) (ν : Measure (Rd d))
    [IsFiniteMeasure ν] :
    ∫ ω, fourierPlus (f : Rd d → ℂ) ω * charFun ν (-ω) =
      (((2 * Real.pi) ^ d : ℝ) : ℂ) * ∫ x, f x ∂ν := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℝ := -(2 * Real.pi)⁻¹ with hc
  have hpt : ∀ ω : Rd d, fourierPlus (f : Rd d → ℂ) ω * charFun ν (-ω) =
      (fun ξ => 𝓕 (f : Rd d → ℂ) ξ * charFun ν ((2 * Real.pi) • ξ)) (c • ω) := by
    intro ω
    simp only
    rw [fourierPlus_eq_fourier, smul_smul, hc, mul_neg, mul_inv_cancel₀ hπ.ne', neg_one_smul]
  rw [integral_congr_ae (Eventually.of_forall hpt), Measure.integral_comp_smul volume
    (fun ξ => 𝓕 (f : Rd d → ℂ) ξ * charFun ν ((2 * Real.pi) • ξ)) c, integral_fourier_mul_charFun,
    finrank_euclideanSpace_fin]
  rw [hc, neg_pow, inv_pow, mul_inv, inv_inv, abs_mul, abs_of_pos (by positivity :
    (0 : ℝ) < (2 * Real.pi) ^ d)]
  rw [Complex.real_smul]
  congr 1
  push_cast
  have : |((-1 : ℝ) ^ d)⁻¹| = 1 := by rw [abs_inv, abs_pow, abs_neg, abs_one, one_pow, inv_one]
  rw [this, Complex.ofReal_one, one_mul]

/-! ## `maternIncrement_eq_integral` -/

theorem charFun_add_measure (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (t : Rd d) : charFun (μ + ν) t = charFun μ t + charFun ν t := by
  have hb : ∀ (m : Measure (Rd d)) [IsFiniteMeasure m],
      Integrable (fun x : Rd d => cexp (⟪x, t⟫ * I)) m := by
    intro m _
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply, integral_add_measure (hb μ) (hb ν), ← charFun_apply, ← charFun_apply]

instance isFiniteMeasure_affineOrbit (μI : Measure (Rd d)) [IsFiniteMeasure μI] (S : Mat d) :
    IsFiniteMeasure (affineOrbit μI S) := by
  unfold affineOrbit push
  infer_instance

/-- The increment's transform: if `μ_{Σ'} + μ_Σ * ρ₋ = μ_Σ * ρ₊`, then
`ρ̂₊(ω) - ρ̂₋(ω) = (1 + ⟨ω,Σω⟩)/(1 + ⟨ω,Σ'ω⟩)`. -/
theorem maternIncrement_charFun {μI : Measure (Rd d)} (hμI : IsMaternLaw 1 μI) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (ρp ρm : Measure (Rd d)) [IsFiniteMeasure ρp]
    [IsFiniteMeasure ρm] (h : affineOrbit μI S' + affineOrbit μI S ∗ ρm = affineOrbit μI S ∗ ρp)
    (ω : Rd d) :
    ((((1 + quad S ω) / (1 + quad S' ω)) : ℝ) : ℂ) = charFun ρp ω - charFun ρm ω := by
  haveI := hμI.1
  have hc := congrArg (fun m => charFun m ω) h
  rw [charFun_add_measure, charFun_conv, charFun_conv, charFun_maternOrbit_one hμI hS,
    charFun_maternOrbit_one hμI hS'] at hc
  have h1 : 0 < 1 + quad S ω := by linarith [quad_nonneg hS.posSemidef ω]
  have h1' : 0 < 1 + quad S' ω := by linarith [quad_nonneg hS'.posSemidef ω]
  have ha : ((1 + quad S ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have hb : ((1 + quad S' ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1'.ne'
  push_cast at hc ha hb ⊢
  field_simp at hc ⊢
  linear_combination hc

/-- **`prop:matern-negative-mass`**, the functional: whenever `μ_{Σ'} = μ_Σ * ρ` for a finite signed
measure `ρ = ρ₊ - ρ₋`, the functional `ρ(φ)` is `∫ φ dρ` on Schwartz functions. -/
theorem maternIncrement_eq_integral (_hd : 2 ≤ d) (μI : Measure (Rd d)) (hμI : IsMaternLaw 1 μI)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (_hP : loewnerLE S S') (_hP0 : S' - S ≠ 0)
    (ρp ρm : Measure (Rd d)) [IsFiniteMeasure ρp] [IsFiniteMeasure ρm]
    (h : affineOrbit μI S' + affineOrbit μI S ∗ ρm = affineOrbit μI S ∗ ρp)
    (φ : 𝓢(Rd d, ℂ)) :
    maternIncrement S S' φ = ∫ x, φ x ∂ρp - ∫ x, φ x ∂ρm := by
  have hR : ∀ ω : Rd d, ((((1 + quad S ω) / (1 + quad S' ω)) : ℝ) : ℂ) =
      charFun ρp (-ω) - charFun ρm (-ω) := by
    intro ω
    rw [← maternIncrement_charFun hμI hS hS' ρp ρm h (-ω), quad_neg_vec, quad_neg_vec]
  rw [maternIncrement]
  simp_rw [hR, mul_sub]
  rw [integral_sub (integrable_fourierPlus_mul_charFun φ ρp)
    (integrable_fourierPlus_mul_charFun φ ρm), integral_fourierPlus_mul_charFun,
    integral_fourierPlus_mul_charFun, ← mul_sub, ← mul_assoc]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have : (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * (((2 * Real.pi) ^ d : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg hπ.le, Real.rpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ hπ.ne'), Complex.ofReal_one]
  rw [this, one_mul]

/-! ## Clause (1): the increment off the origin -/

theorem lin_msqrt_inv_ne_zero {S : Mat d} (hS : S.PosDef) {x : Rd d} (hx : x ≠ 0) :
    lin (msqrt S)⁻¹ x ≠ 0 := by
  intro h
  apply hx
  have := lin_mul_inv_apply (msqrt_mem_glSet hS) x
  rw [h, map_zero] at this
  exact this.symm

theorem contDiffAt_maternDensity {S : Mat d} (hS : S.PosDef) {x : Rd d} (hx : x ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternDensity S) x := by
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternGreen d) (lin (msqrt S)⁻¹ x) :=
    contDiffOn_maternGreen.contDiffAt
      (isOpen_compl_singleton.mem_nhds (lin_msqrt_inv_ne_zero hS hx))
  exact contDiffAt_const.mul (hG.comp x (lin (msqrt S)⁻¹).contDiff.contDiffAt)

theorem maternDensity_nonneg {S : Mat d} (hS : S.PosDef) (x : Rd d) : 0 ≤ maternDensity S x :=
  mul_nonneg (Real.rpow_nonneg hS.det_pos.le _) (maternGreen_nonneg _)

theorem measurable_maternDensity (S : Mat d) : Measurable (maternDensity S) :=
  measurable_const.mul (measurable_maternGreen.comp (lin _).continuous.measurable)

/-- The cut-off `χ_δ(x) := s(|x|²/δ² - 1)`, `s` the smooth transition: `0` on the closed ball of
radius `δ`, `1` where `|x|² ≥ 2δ²`. -/
noncomputable def cutoff (δ : ℝ) (x : Rd d) : ℝ := Real.smoothTransition (‖x‖ ^ 2 / δ ^ 2 - 1)

theorem contDiff_cutoff (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff (d := d) δ) :=
  Real.smoothTransition.contDiff.comp (((contDiff_norm_sq ℝ).div_const _).sub contDiff_const)

theorem cutoff_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : Rd d} (hx : ‖x‖ ≤ δ) : cutoff δ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : ‖x‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  rw [sub_nonpos, div_le_one (by positivity)]
  exact this

theorem cutoff_eq_one {δ : ℝ} (hδ : 0 < δ) {x : Rd d} (hx : 2 * δ ^ 2 ≤ ‖x‖ ^ 2) :
    cutoff δ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith

/-- `K_Σ` cut off near the origin: smooth on all of `ℝ^d`. -/
noncomputable def cutKernel (δ : ℝ) (S : Mat d) (x : Rd d) : ℝ := cutoff δ x * maternDensity S x

theorem contDiff_cutKernel {δ : ℝ} (hδ : 0 < δ) {S : Mat d} (hS : S.PosDef) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutKernel δ S) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : cutKernel δ S =ᶠ[𝓝 (0 : Rd d)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Rd d) hδ] with y hy
      rw [mem_ball_zero_iff] at hy
      simp [cutKernel, cutoff_eq_zero hδ hy.le]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (contDiff_cutoff δ).contDiffAt.mul (contDiffAt_maternDensity hS hx)

theorem cutKernel_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (S : Mat d) {x : Rd d}
    (hx : 2 * δ ^ 2 < ‖x‖ ^ 2) : cutKernel δ S =ᶠ[𝓝 x] maternDensity S := by
  have ho : IsOpen {y : Rd d | 2 * δ ^ 2 < ‖y‖ ^ 2} :=
    isOpen_lt continuous_const (continuous_norm.pow 2)
  filter_upwards [ho.mem_nhds hx] with y hy
  simp [cutKernel, cutoff_eq_one hδ (le_of_lt hy)]

/-- **The transform of a derivative**: `(∂_vf)^(ω) = -i⟨ω,v⟩ f̂(ω)` for `f` of class `C¹` with
compact support, by an integration by parts. -/
theorem fourierPlus_fderiv {f : Rd d → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (v ω : Rd d) :
    fourierPlus (fun x => fderiv ℝ f x v) ω = -((⟪ω, v⟫ : ℂ) * I) * fourierPlus f ω := by
  set L : Rd d →L[ℝ] ℂ := (innerSL ℝ ω).smulRight I with hL
  have hLx : ∀ x, L x = (⟪ω, x⟫ : ℂ) * I := by
    intro x
    simp [hL, Complex.real_smul]
  set e : Rd d → ℂ := fun x => cexp ((⟪ω, x⟫ : ℂ) * I) with he
  have hed : ∀ x, HasFDerivAt e (e x • L) x := by
    intro x
    have h2 := (L.hasFDerivAt (x := x)).cexp
    simp only [hLx] at h2
    exact h2
  have hcont_e : Continuous e := by fun_prop
  have hfd : Continuous fun x => fderiv ℝ f x v :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hed' : ∀ x, fderiv ℝ e x v = e x * ((⟪ω, v⟫ : ℂ) * I) := by
    intro x
    rw [(hed x).fderiv, _root_.smul_apply, hLx, smul_eq_mul]
  have h1 : Integrable fun x => fderiv ℝ e x v * f x := by
    simp_rw [hed']
    exact ((hcont_e.mul continuous_const).mul hf.continuous).integrable_of_hasCompactSupport
      (hc.mul_left (f := fun x => e x * ((⟪ω, v⟫ : ℂ) * I)))
  have h2 : Integrable fun x => e x * fderiv ℝ f x v :=
    (hcont_e.mul hfd).integrable_of_hasCompactSupport ((hc.fderiv_apply (𝕜 := ℝ) v).mul_left)
  have h3 : Integrable fun x => e x * f x :=
    (hcont_e.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hed x).differentiableAt) (fun x _ => hdiff x)
  simp only [fourierPlus]
  change ∫ x, e x * fderiv ℝ f x v = -((⟪ω, v⟫ : ℂ) * I) * ∫ x, e x * f x
  rw [hIBP]
  simp_rw [hed']
  rw [← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  ring

/-- The first derivatives `φ_k := ∂_kφ`. -/
noncomputable def pd1 (g : Rd d → ℂ) (k : Fin d) (x : Rd d) : ℂ := fderiv ℝ g x (ebasis k)

/-- The second derivatives `φ_{jk} := ∂_j∂_kφ`. -/
noncomputable def pd2 (g : Rd d → ℂ) (j k : Fin d) (x : Rd d) : ℂ :=
  fderiv ℝ (pd1 g k) x (ebasis j)

/-- `ψ := ∇·P∇φ = ∑ P_{jk} ∂_j∂_kφ`. -/
noncomputable def secondOpC (P : Mat d) (g : Rd d → ℂ) (x : Rd d) : ℂ :=
  ∑ j, ∑ k, (P j k : ℂ) * pd2 g j k x

section Smooth

variable {g : Rd d → ℂ}

theorem tsupport_pd1_subset (k : Fin d) : tsupport (pd1 g k) ⊆ tsupport g :=
  tsupport_fderiv_apply_subset ℝ _

theorem tsupport_pd2_subset (j k : Fin d) : tsupport (pd2 g j k) ⊆ tsupport g :=
  (tsupport_fderiv_apply_subset ℝ _).trans (tsupport_pd1_subset k)

theorem pd2_eq_zero {x : Rd d} (hx : x ∉ tsupport g) (j k : Fin d) : pd2 g j k x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_pd2_subset j k h)

theorem secondOpC_eq_zero (P : Mat d) {x : Rd d} (hx : x ∉ tsupport g) :
    secondOpC P g x = 0 := by
  simp [secondOpC, pd2_eq_zero hx]

theorem support_secondOpC_subset (P : Mat d) : Function.support (secondOpC P g) ⊆ tsupport g :=
  fun x hx => by
    by_contra h
    exact hx (secondOpC_eq_zero P h)

variable (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
include hg

theorem contDiff_pd1 (k : Fin d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd1 g k) :=
  (hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

theorem contDiff_pd2 (j k : Fin d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd2 g j k) :=
  ((contDiff_pd1 hg k).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
    contDiff_const

theorem contDiff_secondOpC (P : Mat d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secondOpC P g) :=
  ContDiff.sum fun j _ => ContDiff.sum fun k _ => contDiff_const.mul (contDiff_pd2 hg j k)

variable (hc : HasCompactSupport g)
include hc

omit hg in
theorem hasCompactSupport_pd1 (k : Fin d) : HasCompactSupport (pd1 g k) :=
  hc.fderiv_apply (𝕜 := ℝ) _

omit hg in
theorem hasCompactSupport_pd2 (j k : Fin d) : HasCompactSupport (pd2 g j k) :=
  (hasCompactSupport_pd1 hc k).fderiv_apply (𝕜 := ℝ) _

omit hg in
theorem hasCompactSupport_secondOpC (P : Mat d) : HasCompactSupport (secondOpC P g) :=
  hc.mono' (support_secondOpC_subset P)

/-- `(∇·P∇φ)^(ω) = -⟨ω,Pω⟩ φ̂(ω)`. -/
theorem fourierPlus_secondOpC (P : Mat d) (ω : Rd d) :
    fourierPlus (secondOpC P g) ω = -((quad P ω : ℝ) : ℂ) * fourierPlus g ω := by
  have he : Continuous fun x : Rd d => cexp ((⟪ω, x⟫ : ℂ) * I) := by fun_prop
  have hint : ∀ j k, Integrable fun x => cexp ((⟪ω, x⟫ : ℂ) * I) * ((P j k : ℂ) * pd2 g j k x) :=
    fun j k => (he.mul (continuous_const.mul (contDiff_pd2 hg j k).continuous)
      ).integrable_of_hasCompactSupport
        ((hasCompactSupport_pd2 hc j k).mul_left.mul_left (f := fun x => cexp ((⟪ω, x⟫ : ℂ) * I)))
  have h2 : ∀ j k, fourierPlus (pd2 g j k) ω =
      -(((ω j * ω k : ℝ)) : ℂ) * fourierPlus g ω := by
    intro j k
    have hk := fourierPlus_fderiv ((contDiff_pd1 hg k).of_le (by simp))
      (hasCompactSupport_pd1 hc k) (ebasis j) ω
    have hk' := fourierPlus_fderiv (hg.of_le (by simp)) hc (ebasis k) ω
    rw [show pd2 g j k = fun x => fderiv ℝ (pd1 g k) x (ebasis j) from rfl, hk]
    rw [show (pd1 g k) = fun x => fderiv ℝ g x (ebasis k) from rfl, hk', real_inner_comm,
      inner_ebasis_left, real_inner_comm, inner_ebasis_left]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [fourierPlus, secondOpC]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [fun j => integral_finsetSum (Finset.univ : Finset (Fin d))
    (f := fun k x => cexp ((⟪ω, x⟫ : ℂ) * I) * ((P j k : ℂ) * pd2 g j k x))
    (fun k _ => hint j k)]
  have h3 : ∀ j k, ∫ x, cexp ((⟪ω, x⟫ : ℂ) * I) * ((P j k : ℂ) * pd2 g j k x) =
      (P j k : ℂ) * fourierPlus (pd2 g j k) ω := by
    intro j k
    rw [fourierPlus, ← integral_const_mul]
    congr 1
    funext x
    ring
  simp_rw [h3, h2]
  rw [quad_eq_sum]
  push_cast
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [fourierPlus]
  ring

end Smooth

/-- The second partial derivatives of a real function, `∂_a∂_bK := ∂_a(∂_bK)`. -/
noncomputable def pr2 (K : Rd d → ℝ) (a b : Fin d) (x : Rd d) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ K y (ebasis b)) x (ebasis a)

section RealKernel

variable {K : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
include hK

theorem contDiff_fderiv_apply' (v : Rd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => fderiv ℝ K y v :=
  (hK.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

theorem continuous_pr2 (a b : Fin d) : Continuous (pr2 K a b) :=
  ((contDiff_fderiv_apply' hK _).continuous_fderiv (by simp)).clm_apply continuous_const

theorem iteratedFDeriv_two_eq_pr2 (x : Rd d) (a b : Fin d) :
    iteratedFDeriv ℝ 2 K x ![ebasis a, ebasis b] = pr2 K a b x := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hK2 : ContDiff ℝ 2 K := hK.of_le (WithTop.coe_le_coe.2 le_top)
  have hD : DifferentiableAt ℝ (fderiv ℝ K) x :=
    ((hK2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  rw [pr2, fderiv_clm_apply hD (differentiableAt_const _)]
  simp

theorem secondOrderOp_eq_pr2 (P : Mat d) (x : Rd d) :
    secondOrderOp P K x = ∑ j, ∑ k, P j k * pr2 K j k x := by
  simp only [secondOrderOp, iteratedFDeriv_two_eq_pr2 hK]

/-- **Two integrations by parts**: `∫ K ∂_j∂_kφ = ∫ (∂_k∂_jK) φ` for smooth `K` and a smooth `φ` with
compact support. -/
theorem integral_mul_pd2 {g : Rd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hc : HasCompactSupport g) (j k : Fin d) :
    ∫ x, (K x : ℂ) * pd2 g j k x = ∫ x, (pr2 K k j x : ℂ) * g x := by
  have h1t : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hK1 : ContDiff ℝ 1 K := hK.of_le h1t
  have hKd : Differentiable ℝ K := hK1.differentiable one_ne_zero
  have hKf : Continuous fun x => fderiv ℝ K x (ebasis j) :=
    (hK1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJ := contDiff_fderiv_apply' hK (ebasis j)
  have hJd : Differentiable ℝ fun y => fderiv ℝ K y (ebasis j) :=
    (hJ.of_le h1t).differentiable one_ne_zero
  have hp1 := contDiff_pd1 hg k
  have hp1d : Differentiable ℝ (pd1 g k) := (hp1.of_le h1t).differentiable one_ne_zero
  have hgd : Differentiable ℝ g := (hg.of_le h1t).differentiable one_ne_zero
  have hc1 := hasCompactSupport_pd1 hc k
  have hc2 := hasCompactSupport_pd2 hc j k
  have s1 : HasCompactSupport (fun x => fderiv ℝ K x (ebasis j) • pd1 g k x) :=
    HasCompactSupport.smul_left (f := fun x => fderiv ℝ K x (ebasis j)) hc1
  have c1 : Continuous (fun x => fderiv ℝ K x (ebasis j) • pd1 g k x) := hKf.smul hp1.continuous
  have t1 : Integrable (fun x => fderiv ℝ K x (ebasis j) • pd1 g k x) :=
    c1.integrable_of_hasCompactSupport s1
  have t2 : Integrable (fun x => K x • fderiv ℝ (pd1 g k) x (ebasis j)) :=
    (Continuous.smul hK.continuous (contDiff_pd2 hg j k).continuous :
      Continuous (fun x => K x • pd2 g j k x)).integrable_of_hasCompactSupport
      (HasCompactSupport.smul_left (f := K) hc2)
  have t3 : Integrable (fun x => K x • pd1 g k x) :=
    (Continuous.smul hK.continuous hp1.continuous :
      Continuous (fun x => K x • pd1 g k x)).integrable_of_hasCompactSupport
      (HasCompactSupport.smul_left (f := K) hc1)
  have I1 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (f := K)
    (g := pd1 g k) (v := ebasis j) t1 t2 t3 (fun x _ => hKd x) (fun x _ => hp1d x)
  have u1 : Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ K y (ebasis j)) x (ebasis k) • g x) :=
    (Continuous.smul (continuous_pr2 hK k j) hg.continuous :
      Continuous (fun x => pr2 K k j x • g x)).integrable_of_hasCompactSupport
      (HasCompactSupport.smul_left (f := pr2 K k j) hc)
  have u3 : Integrable (fun x => fderiv ℝ K x (ebasis j) • g x) :=
    (Continuous.smul hKf hg.continuous :
      Continuous (fun x => fderiv ℝ K x (ebasis j) • g x)).integrable_of_hasCompactSupport
      (HasCompactSupport.smul_left (f := fun x => fderiv ℝ K x (ebasis j)) hc)
  have I2 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun y => fderiv ℝ K y (ebasis j)) (g := g) (v := ebasis k) u1 t1 u3
    (fun x _ => hJd x) (fun x _ => hgd x)
  have e1 : (fun x => (K x : ℂ) * pd2 g j k x) =
      fun x => K x • fderiv ℝ (pd1 g k) x (ebasis j) := by
    funext x
    rw [Complex.real_smul]
    rfl
  have e2 : (fun x => (pr2 K k j x : ℂ) * g x) =
      fun x => fderiv ℝ (fun y => fderiv ℝ K y (ebasis j)) x (ebasis k) • g x := by
    funext x
    rw [Complex.real_smul]
    rfl
  have e3 : (fun x => fderiv ℝ K x (ebasis j) • pd1 g k x) =
      fun x => fderiv ℝ K x (ebasis j) • fderiv ℝ g x (ebasis k) := rfl
  rw [e1, e2, I1, e3, I2, neg_neg]

end RealKernel

/-- **`prop:matern-negative-mass`(1)**, the identity: `ρ(φ) = ∫ φ q dx` for a Schwartz `φ` with
compact support away from the origin, `q = ∇·P∇K_{Σ'}`. -/
theorem maternIncrement_off_origin (μI : Measure (Rd d)) (hμI : IsMaternLaw 1 μI) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (φ : 𝓢(Rd d, ℂ)) (hc : HasCompactSupport φ)
    (h0 : (0 : Rd d) ∉ tsupport φ) :
    maternIncrement S S' φ =
      ∫ x, φ x * ((secondOrderOp (S' - S) (maternDensity S') x : ℝ) : ℂ) := by
  haveI := hμI.1
  set g : Rd d → ℂ := ⇑φ with hgdef
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := φ.smooth ⊤
  set P := S' - S with hPdef
  have hPh : P.IsHermitian := hS'.isHermitian.sub hS.isHermitian
  set ψS : 𝓢(Rd d, ℂ) := (hasCompactSupport_secondOpC hc P).toSchwartzMap
    (contDiff_secondOpC hg P) with hψS
  have hψ : (ψS : Rd d → ℂ) = secondOpC P g := rfl
  -- the transform side
  have hA : maternIncrement S S' φ = ∫ x, ψS x ∂(affineOrbit μI S') := by
    have hpt : ∀ ω, fourierPlus g ω * ((((1 + quad S ω) / (1 + quad S' ω)) : ℝ) : ℂ) =
        fourierPlus g ω * charFun (Measure.dirac (0 : Rd d)) (-ω) +
          fourierPlus (ψS : Rd d → ℂ) ω * charFun (affineOrbit μI S') (-ω) := by
      intro ω
      rw [hψ, fourierPlus_secondOpC hg hc, charFun_dirac, charFun_maternOrbit_one hμI hS',
        quad_neg_vec, hPdef, quad_sub]
      simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
      have h1' : 0 < 1 + quad S' ω := by linarith [quad_nonneg hS'.posSemidef ω]
      have hb : ((1 + quad S' ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1'.ne'
      push_cast at hb ⊢
      field_simp
      ring
    rw [maternIncrement, ← hgdef]
    simp_rw [hpt]
    rw [integral_add (integrable_fourierPlus_mul_charFun φ _)
      (integrable_fourierPlus_mul_charFun ψS _), integral_fourierPlus_mul_charFun,
      integral_fourierPlus_mul_charFun, integral_dirac, ← hgdef, image_eq_zero_of_notMem_tsupport h0,
      mul_zero, zero_add, ← mul_assoc]
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have : (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * (((2 * Real.pi) ^ d : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, Real.rpow_neg hπ.le, Real.rpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hπ.ne'), Complex.ofReal_one]
    rw [this, one_mul]
  -- the density
  have hB : ∫ x, ψS x ∂(affineOrbit μI S') =
      ∫ x, (maternDensity S' x : ℂ) * secondOpC P g x := by
    rw [maternOrbit_eq_withDensity hμI hS', integral_withDensity_eq_integral_toReal_smul
      (measurable_maternDensity S').ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (maternDensity_nonneg hS' x), Complex.real_smul]
    rfl
  -- the cut-off
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl 0 h0
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hfar : ∀ x ∈ tsupport g, 2 * δ ^ 2 < ‖x‖ ^ 2 := by
    intro x hx
    have : ε ≤ ‖x‖ := by
      by_contra h
      push Not at h
      exact hball (mem_ball_zero_iff.2 h) hx
    nlinarith
  have hC : ∫ x, (maternDensity S' x : ℂ) * secondOpC P g x =
      ∫ x, (cutKernel δ S' x : ℂ) * secondOpC P g x := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [(cutKernel_eventuallyEq hδ S' (hfar x hx)).eq_of_nhds]
    · rw [secondOpC_eq_zero P hx, mul_zero, mul_zero]
  -- two integrations by parts
  have hK := contDiff_cutKernel hδ hS'
  have hint1 : ∀ j k, Integrable fun x =>
      (cutKernel δ S' x : ℂ) * ((P j k : ℂ) * pd2 g j k x) :=
    fun j k => ((continuous_ofReal.comp hK.continuous).mul
      (continuous_const.mul (contDiff_pd2 hg j k).continuous)).integrable_of_hasCompactSupport
      ((hasCompactSupport_pd2 hc j k).mul_left.mul_left)
  have hint2 : ∀ j k, Integrable fun x =>
      g x * ((P j k : ℂ) * (pr2 (cutKernel δ S') j k x : ℂ)) :=
    fun j k => (hg.continuous.mul (continuous_const.mul
      (continuous_ofReal.comp (continuous_pr2 hK j k)))).integrable_of_hasCompactSupport
      hc.mul_right
  have hD : ∫ x, (cutKernel δ S' x : ℂ) * secondOpC P g x =
      ∫ x, g x * ((secondOrderOp P (cutKernel δ S') x : ℝ) : ℂ) := by
    simp_rw [secondOrderOp_eq_pr2 hK, secondOpC, Finset.mul_sum]
    push_cast
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint1 j k,
      integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint2 j k]
    simp_rw [fun j => integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin d))
      (f := fun k x => (cutKernel δ S' x : ℂ) * ((P j k : ℂ) * pd2 g j k x))
      (fun k _ => hint1 j k),
      fun j => integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin d))
      (f := fun k x => g x * ((P j k : ℂ) * (pr2 (cutKernel δ S') j k x : ℂ)))
      (fun k _ => hint2 j k)]
    have l1 : ∀ j k, ∫ x, (cutKernel δ S' x : ℂ) * ((P j k : ℂ) * pd2 g j k x) =
        (P j k : ℂ) * ∫ x, (pr2 (cutKernel δ S') k j x : ℂ) * g x := by
      intro j k
      rw [← integral_mul_pd2 hK hg hc j k, ← integral_const_mul]
      congr 1
      funext x
      ring
    have l2 : ∀ j k, ∫ x, g x * ((P j k : ℂ) * (pr2 (cutKernel δ S') j k x : ℂ)) =
        (P j k : ℂ) * ∫ x, (pr2 (cutKernel δ S') j k x : ℂ) * g x := by
      intro j k
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [l1, l2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have := hPh.apply j k
    simp only [star_trivial] at this
    rw [this]
  -- back to `K_{Σ'}` on the support
  have hE : ∫ x, g x * ((secondOrderOp P (cutKernel δ S') x : ℝ) : ℂ) =
      ∫ x, g x * ((secondOrderOp P (maternDensity S') x : ℝ) : ℂ) := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · have := ((cutKernel_eventuallyEq hδ S' (hfar x hx)).iteratedFDeriv ℝ 2).eq_of_nhds
      simp only [secondOrderOp, this]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  rw [hA, hB, hC, hD, hE]

theorem contDiff_pr2 {K : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (a b : Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pr2 K a b) :=
  ((contDiff_fderiv_apply' hK _).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
    contDiff_const

/-- `q = ∇·P∇K_{Σ'}` is smooth on `ℝ^d ∖ {0}`. -/
theorem contDiffOn_secondOrderOp_maternDensity {S' : Mat d} (hS' : S'.PosDef) (P : Mat d) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secondOrderOp P (maternDensity S')) {0}ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  set δ := ‖x‖ / 2 with hδdef
  have hδ : 0 < δ := by have := norm_pos_iff.2 hx0; positivity
  have hfar : 2 * δ ^ 2 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx0
    rw [hδdef]
    nlinarith
  have hK := contDiff_cutKernel hδ hS'
  have hglob : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secondOrderOp P (cutKernel δ S')) := by
    have : secondOrderOp P (cutKernel δ S') = fun y => ∑ j, ∑ k, P j k * pr2 (cutKernel δ S') j k y :=
      funext (secondOrderOp_eq_pr2 hK P)
    rw [this]
    exact ContDiff.sum fun j _ => ContDiff.sum fun k _ => contDiff_const.mul (contDiff_pr2 hK j k)
  have hev : secondOrderOp P (cutKernel δ S') =ᶠ[𝓝 x] secondOrderOp P (maternDensity S') := by
    have h1 := (cutKernel_eventuallyEq hδ S' hfar).iteratedFDeriv ℝ 2
    have h2 := h1.eventually_nhds
    filter_upwards [h2] with y hy
    simp only [secondOrderOp, hy.self_of_nhds]
  exact (hglob.contDiffAt.congr_of_eventuallyEq hev.symm).contDiffWithinAt

/-- **`prop:matern-negative-mass`(1)**, off the origin: `K_Σ` is a density of `μ_Σ`;
`q = ∇·P∇K_{Σ'}` is smooth on `ℝ^d ∖ {0}`; and `ρ(φ) = ∫ φ q dx` for every smooth `φ` with compact
support in `ℝ^d ∖ {0}`. -/
theorem matern_negative_mass_off_origin (_hd : 2 ≤ d) (μI : Measure (Rd d))
    (hμI : IsMaternLaw 1 μI) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef)
    (_hP : loewnerLE S S') (_hP0 : S' - S ≠ 0) :
    (∀ T : Mat d, T.PosDef →
        affineOrbit μI T = volume.withDensity (fun x => ENNReal.ofReal (maternDensity T x))) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secondOrderOp (S' - S) (maternDensity S')) {0}ᶜ ∧
      ∀ φ : 𝓢(Rd d, ℂ), HasCompactSupport φ → (0 : Rd d) ∉ tsupport φ →
        maternIncrement S S' φ =
          ∫ x, φ x * ((secondOrderOp (S' - S) (maternDensity S') x : ℝ) : ℂ) :=
  ⟨fun _ hT => maternOrbit_eq_withDensity hμI hT,
    contDiffOn_secondOrderOp_maternDensity hS' _,
    fun φ hc h0 => maternIncrement_off_origin μI hμI hS hS' φ hc h0⟩

/-! ## Clause (2): the density near the origin -/

/-- `x ↦ Σ^{-1/2}x` as a continuous linear equivalence. -/
noncomputable def linInvEquiv {S : Mat d} (hS : S.PosDef) : Rd d ≃L[ℝ] Rd d :=
  ContinuousLinearEquiv.equivOfInverse (lin (msqrt S)⁻¹) (lin (msqrt S))
    (fun y => lin_mul_inv_apply (msqrt_mem_glSet hS) y)
    (fun y => lin_inv_mul_apply (msqrt_mem_glSet hS) y)

theorem linInvEquiv_apply {S : Mat d} (hS : S.PosDef) (x : Rd d) :
    linInvEquiv hS x = lin (msqrt S)⁻¹ x := rfl

theorem lin_ebasis (A : Mat d) (j : Fin d) : lin A (ebasis j) = ∑ a, A a j • ebasis a := by
  ext i
  rw [lin_apply_coord]
  simp [ebasis_apply, WithLp.ofLp_sum, Finset.sum_apply]

/-- A bilinear form at `A e_j, A e_k`: `B(Ae_j, Ae_k) = ∑_{a,b} A_{aj}A_{bk} B(e_a, e_b)`. -/
theorem bilin_lin_ebasis (B : Rd d →L[ℝ] Rd d →L[ℝ] ℝ) (A : Mat d) (j k : Fin d) :
    B (lin A (ebasis j)) (lin A (ebasis k)) =
      ∑ a, ∑ b, A a j * A b k * B (ebasis a) (ebasis b) := by
  rw [lin_ebasis A j, lin_ebasis A k]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Four finite sums reordered, `(a, b, j, k) ↦ (j, k, a, b)`. Mathlib types only. -/
theorem sum_four_comm {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ j, ∑ k, f a b j k = ∑ j, ∑ k, ∑ a, ∑ b, f a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, f a b j k = ∑ a, ∑ j, ∑ b, ∑ k, f a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ b, ∑ k, f a b j k := Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ k, ∑ b, f a b j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, f a b j k := Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- **The substitution `x = Σ'^{1/2}y`**: `∇_x·P∇_xK_{Σ'}(x) = (det Σ')^{-1/2} ∇_y·P'∇_yG(y)` at
`y = Σ'^{-1/2}x ≠ 0`, with `P' = Σ'^{-1/2}PΣ'^{-1/2}`. -/
theorem secondOrderOp_maternDensity {S' : Mat d} (hS' : S'.PosDef) (P : Mat d) {x : Rd d}
    (hx : x ≠ 0) :
    secondOrderOp P (maternDensity S') x =
      S'.det ^ (-(1 : ℝ) / 2) * secondOrderOp (relStep S' P) (maternGreen d) (lin (msqrt S')⁻¹ x) := by
  set A := (msqrt S')⁻¹ with hAdef
  set c := S'.det ^ (-(1 : ℝ) / 2) with hc
  set E := linInvEquiv hS' with hE
  set L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ with hL
  have hAx : lin A x ≠ 0 := lin_msqrt_inv_ne_zero hS' hx
  have hf : maternDensity S' = L ∘ (maternGreen d ∘ E) := by
    funext y
    simp [maternDensity, hL, hE, linInvEquiv_apply, hc]
  have hGE : ContDiffAt ℝ 2 (maternGreen d ∘ E) x := by
    have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (maternGreen d) (E x) :=
      contDiffOn_maternGreen.contDiffAt (isOpen_compl_singleton.mem_nhds hAx)
    exact (hG.comp x E.contDiff.contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)
  have hcomp : ∀ u v : Rd d, iteratedFDeriv ℝ 2 (maternDensity S') x ![u, v] =
      c * fderiv ℝ (fderiv ℝ (maternGreen d)) (lin A x) (lin A u) (lin A v) := by
    intro u v
    rw [hf, L.iteratedFDeriv_comp_left hGE le_rfl]
    have hr : iteratedFDeriv ℝ 2 (maternGreen d ∘ E) x =
        (iteratedFDeriv ℝ 2 (maternGreen d) (E x)).compContinuousLinearMap
          fun _ => (E : Rd d →L[ℝ] Rd d) := by
      simp only [← iteratedFDerivWithin_univ]
      have := E.iteratedFDerivWithin_comp_right (maternGreen d) uniqueDiffOn_univ
        (mem_univ (E x)) 2
      rwa [preimage_univ] at this
    rw [hr]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hL]
    rw [iteratedFDeriv_two_apply]
    simp [linInvEquiv_apply, hE, hAdef]
  have hAt : Aᵀ = A := msqrt_inv_transpose S'
  have hsym : ∀ k b, A k b = A b k := fun k b => by
    have := congrFun (congrFun hAt b) k
    rw [Matrix.transpose_apply] at this
    exact this
  have key : ∀ a b, (A * P * A) a b = ∑ j, ∑ k, A a j * P j k * A b k := by
    intro a b
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsym k b]
  set F : Fin d → Fin d → ℝ := fun a b =>
    fderiv ℝ (fderiv ℝ (maternGreen d)) (lin A x) (ebasis a) (ebasis b) with hF
  rw [secondOrderOp, secondOrderOp]
  simp_rw [hcomp, iteratedFDeriv_two_apply, bilin_lin_ebasis]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show relStep S' P = A * P * A from rfl]
  simp_rw [key, Finset.sum_mul]
  rw [sum_four_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lin_msqrt_ne_zero {S : Mat d} (hS : S.PosDef) {y : Rd d} (hy : y ≠ 0) :
    lin (msqrt S) y ≠ 0 := by
  intro h
  apply hy
  have := lin_inv_mul_apply (msqrt_mem_glSet hS) y
  rw [h, map_zero] at this
  exact this.symm

/-- `q(Σ'^{1/2}y) = (det Σ')^{-1/2} Q(y)` for `y ≠ 0`, `Q := ∇·P'∇G`. -/
theorem secondOrderOp_maternDensity_lin {S' : Mat d} (hS' : S'.PosDef) (P : Mat d) {y : Rd d}
    (hy : y ≠ 0) :
    secondOrderOp P (maternDensity S') (lin (msqrt S') y) =
      S'.det ^ (-(1 : ℝ) / 2) * secondOrderOp (relStep S' P) (maternGreen d) y := by
  rw [secondOrderOp_maternDensity hS' P (lin_msqrt_ne_zero hS' hy),
    lin_inv_mul_apply (msqrt_mem_glSet hS')]

theorem det_rpow_half_mul {S : Mat d} (hS : S.PosDef) :
    S.det ^ ((1 : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add hS.det_pos]
  norm_num

/-- **`prop:matern-negative-mass`(2)**, the density near the origin: with `x = Σ'^{1/2}r ŷ`,
`(det Σ')^{1/2} r^d q(Σ'^{1/2}rŷ) → 𝓑_d(d⟨ŷ,P'ŷ⟩ - tr P')` uniformly in `ŷ` as `r ↓ 0`. -/
theorem matern_negative_mass_near_origin (hd : 2 ≤ d) {S S' : Mat d} (_hS : S.PosDef)
    (hS' : S'.PosDef) (_hP : loewnerLE S S') (_hP0 : S' - S ≠ 0) :
    TendstoUniformlyOn
      (fun (r : ℝ) (y : Rd d) => S'.det ^ ((1 : ℝ) / 2) * r ^ d *
        secondOrderOp (S' - S) (maternDensity S') (lin (msqrt S') (r • y)))
      (fun y => maternBd d * maternAngular S S' y) (𝓝[>] 0) (Metric.sphere 0 1) := by
  have h := tendstoUniformlyOn_maternHessian (by omega : 1 ≤ d) (relStep S' (S' - S))
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r) y hy
  have hy1 : ‖y‖ = 1 := by simpa using hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  have hry : r • y ≠ 0 := smul_ne_zero hr.ne' hy0
  simp only
  rw [secondOrderOp_maternDensity_lin hS' _ hry]
  calc r ^ d * secondOrderOp (relStep S' (S' - S)) (maternGreen d) (r • y)
      = (S'.det ^ ((1 : ℝ) / 2) * S'.det ^ (-(1 : ℝ) / 2)) *
          (r ^ d * secondOrderOp (relStep S' (S' - S)) (maternGreen d) (r • y)) := by
        rw [det_rpow_half_mul hS', one_mul]
    _ = _ := by ring

/-! ## Clause (3): the negative mass on a shell -/

/-- `∇·P∇f` is measurable for every `f` (the derivative of any function is measurable). -/
theorem measurable_secondOrderOp (P : Mat d) (f : Rd d → ℝ) : Measurable (secondOrderOp P f) := by
  unfold secondOrderOp
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine measurable_const.mul ?_
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ((measurable_fderiv ℝ (fderiv ℝ f)).apply_continuousLinearMap _).apply_continuousLinearMap _

/-- `0 ≤ J_m(r) ≤ J_m(0)` for `m < -1`. -/
theorem maternLapS_nonneg_le {m : ℝ} (hm : m < -1) (r : ℝ) :
    0 ≤ maternLapS m r ∧ maternLapS m r ≤ ∫ s in Ioi (0 : ℝ), s ^ m * Real.exp (-1 / (4 * s)) := by
  have hI := integrableOn_rpow_exp_inv hm
  have hle : ∀ s ∈ Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s)) ≤
      s ^ m * Real.exp (-1 / (4 * s)) := by
    intro s hs
    have hs0 : 0 < s := hs
    have he : Real.exp (-(r ^ 2 * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
    rw [mul_assoc]
    calc Real.exp (-(r ^ 2 * s)) * (s ^ m * Real.exp (-1 / (4 * s)))
        ≤ 1 * (s ^ m * Real.exp (-1 / (4 * s))) := mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := one_mul _
  have hI' : IntegrableOn (fun s : ℝ => Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s)))
      (Ioi 0) := by
    refine hI.mono' (by fun_prop : Measurable fun s : ℝ =>
      Real.exp (-(r ^ 2 * s)) * s ^ m * Real.exp (-1 / (4 * s))).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle s hs
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun s hs => ?_, setIntegral_mono_on hI' hI
    measurableSet_Ioi hle⟩
  have hs0 : 0 < s := hs
  positivity

theorem maternA_nonneg_le (hd : 1 ≤ d) (r : ℝ) : 0 ≤ maternA d r ∧ maternA d r ≤ maternA d 0 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : -(d : ℝ) / 2 - 1 - 1 < -1 := by linarith
  obtain ⟨h0, h1⟩ := maternLapS_nonneg_le hm r
  have hz : maternLapS (-(d : ℝ) / 2 - 1 - 1) 0 =
      ∫ s in Ioi (0 : ℝ), s ^ (-(d : ℝ) / 2 - 1 - 1) * Real.exp (-1 / (4 * s)) := by
    unfold maternLapS
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp
  rw [maternA_eq, maternA_eq, hz]
  have hc : 0 ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) := by positivity
  constructor
  · positivity
  · gcongr

theorem maternB_nonneg_le (hd : 1 ≤ d) (r : ℝ) : 0 ≤ maternB d r ∧ maternB d r ≤ maternB d 0 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : -(d : ℝ) / 2 - 1 < -1 := by linarith
  obtain ⟨h0, h1⟩ := maternLapS_nonneg_le hm r
  have hz : maternLapS (-(d : ℝ) / 2 - 1) 0 =
      ∫ s in Ioi (0 : ℝ), s ^ (-(d : ℝ) / 2 - 1) * Real.exp (-1 / (4 * s)) := by
    unfold maternLapS
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp
  rw [maternB_eq, maternB_eq, hz]
  have hc : 0 ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) := by positivity
  constructor
  · positivity
  · gcongr

/-- The uniform bound `|r^d ∇·P∇G(rŷ)| ≤ ‖P‖𝓐(0) + |tr P|𝓑(0)` for `r > 0`, `|ŷ| = 1`. -/
theorem abs_maternHessian_le (hd : 1 ≤ d) (P : Mat d) {r : ℝ} (hr : 0 < r) {y : Rd d}
    (hy : ‖y‖ = 1) :
    |r ^ d * secondOrderOp P (maternGreen d) (r • y)| ≤
      ‖lin P‖ * maternA d 0 + |P.trace| * maternB d 0 := by
  rw [maternGreen_hessian_eq P hr hy]
  have hq : |quad P y| ≤ ‖lin P‖ := by
    have := abs_quad_le P y
    rwa [hy, one_pow, mul_one] at this
  obtain ⟨hA0, hA1⟩ := maternA_nonneg_le hd r
  obtain ⟨hB0, hB1⟩ := maternB_nonneg_le hd r
  calc |quad P y * maternA d r - P.trace * maternB d r|
      ≤ |quad P y * maternA d r| + |P.trace * maternB d r| := abs_sub _ _
    _ = |quad P y| * maternA d r + |P.trace| * maternB d r := by
        rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hB0]
    _ ≤ ‖lin P‖ * maternA d 0 + |P.trace| * maternB d 0 := by gcongr

/-- `∫_a^1 dr/r = log(1/a)` over the open interval. Mathlib types only. -/
theorem integral_Ioo_inv {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫ r in Ioo a 1, r⁻¹ = Real.log (1 / a) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1,
    integral_inv_of_pos ha one_pos]

theorem integrableOn_Ioo_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hf : Measurable f)
    (hb : ∀ r ∈ Ioo a b, |f r| ≤ C) : IntegrableOn f (Ioo a b) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr => by
    rw [Real.norm_eq_abs]; exact hb r hr)

/-- **The logarithmic growth of `∫_a^1 F(r) dr/r`**: if `0 ≤ F ≤ M` on `(0,1)` and `F → L` at
`0+`, then `∫_a^1 F(r) dr/r = L log(1/a) + o(log(1/a))` as `a ↓ 0`. Mathlib types only. -/
theorem isLittleO_lintegral_div {F : ℝ → ℝ} {L M : ℝ} (hFm : Measurable F)
    (hF0 : ∀ r, 0 < r → r < 1 → 0 ≤ F r) (hFM : ∀ r, 0 < r → r < 1 → F r ≤ M)
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 L)) :
    (fun a => (∫⁻ r in Ioo a 1, ENNReal.ofReal (F r / r)).toReal - L * Real.log (1 / a))
      =o[𝓝[>] 0] fun a => Real.log (1 / a) := by
  have hM0 : 0 ≤ M := (hF0 (1 / 2) (by norm_num) (by norm_num)).trans
    (hFM (1 / 2) (by norm_num) (by norm_num))
  set C := M + |L| with hC
  have hC0 : 0 ≤ C := by positivity
  -- the lintegral as an integral, and the difference as `∫ (F - L)/r`
  have hD : ∀ a, 0 < a → a < 1 →
      (∫⁻ r in Ioo a 1, ENNReal.ofReal (F r / r)).toReal - L * Real.log (1 / a) =
        ∫ r in Ioo a 1, (F r - L) * r⁻¹ := by
    intro a ha ha1
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo a 1)] fun r => F r / r :=
      (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr =>
        div_nonneg (hF0 r (ha.trans hr.1) hr.2) (ha.trans hr.1).le)
    rw [← integral_eq_lintegral_of_nonneg_ae hnn (hFm.div measurable_id).aestronglyMeasurable,
      ← integral_Ioo_inv ha ha1.le, ← integral_const_mul]
    have h1 : IntegrableOn (fun r => F r / r) (Ioo a 1) := by
      refine integrableOn_Ioo_of_bound (C := M / a) (hFm.div measurable_id) fun r hr => ?_
      have hr0 : 0 < r := ha.trans hr.1
      rw [abs_of_nonneg (div_nonneg (hF0 r hr0 hr.2) hr0.le)]
      calc F r / r ≤ M / r := div_le_div_of_nonneg_right (hFM r hr0 hr.2) hr0.le
        _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha hr.1.le
    have h2 : IntegrableOn (fun r => L * r⁻¹) (Ioo a 1) := by
      refine integrableOn_Ioo_of_bound (C := |L| / a) (measurable_const.mul measurable_inv)
        fun r hr => ?_
      have hr0 : 0 < r := ha.trans hr.1
      rw [abs_mul, abs_inv, abs_of_pos hr0, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (abs_nonneg _) ha hr.1.le
    rw [← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    ring
  have hlog : Tendsto (fun a : ℝ => Real.log (1 / a)) (𝓝[>] 0) atTop := by
    have : (fun a : ℝ => Real.log (1 / a)) = fun a => -Real.log a := by
      funext a
      rw [one_div, Real.log_inv]
    rw [this]
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hη : 0 < c / 2 := by positivity
  obtain ⟨u, hu, hFu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hlim.eventually (Metric.closedBall_mem_nhds L hη))
  set ρ := min u (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hu (by norm_num)
  have hρu : ρ ≤ u := min_le_left _ _
  have hρ1 : ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hev1 : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioo 0 ρ := Ioo_mem_nhdsGT hρ0
  have hev2 : ∀ᶠ a in 𝓝[>] (0 : ℝ), 2 * C / (c * ρ) ≤ Real.log (1 / a) :=
    hlog.eventually (eventually_ge_atTop _)
  filter_upwards [hev1, hev2] with a ha hlg
  have ha0 : 0 < a := ha.1
  have ha1 : a < 1 := ha.2.trans hρ1
  have hlog0 : 0 < Real.log (1 / a) := Real.log_pos (by rw [lt_div_iff₀ ha0]; linarith)
  rw [hD a ha0 ha1, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog0]
  have hbound : ∀ r ∈ Ioo a 1, ‖(F r - L) * r⁻¹‖ ≤ c / 2 * r⁻¹ + C / ρ := by
    intro r hr
    have hr0 : 0 < r := ha0.trans hr.1
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr0]
    rcases lt_or_ge r ρ with hrρ | hrρ
    · have h1 : F r ∈ Metric.closedBall L (c / 2) := hFu ⟨hr0, hrρ.trans_le hρu⟩
      rw [Metric.mem_closedBall, Real.dist_eq] at h1
      have : |F r - L| * r⁻¹ ≤ c / 2 * r⁻¹ := by gcongr
      have : 0 ≤ C / ρ := by positivity
      linarith
    · have h1 : |F r - L| ≤ C := by
        calc |F r - L| ≤ |F r| + |L| := abs_sub _ _
          _ ≤ M + |L| := by
            rw [abs_of_nonneg (hF0 r hr0 hr.2)]
            linarith [hFM r hr0 hr.2]
      have h2 : |F r - L| * r⁻¹ ≤ C * ρ⁻¹ := by
        gcongr
      have : 0 ≤ c / 2 * r⁻¹ := by positivity
      have : C / ρ = C * ρ⁻¹ := div_eq_mul_inv _ _
      linarith
  have hint : IntegrableOn (fun r => c / 2 * r⁻¹ + C / ρ) (Ioo a 1) := by
    refine integrableOn_Ioo_of_bound (C := c / 2 / a + C / ρ)
      ((measurable_const.mul measurable_inv).add measurable_const) fun r hr => ?_
    have hr0 : 0 < r := ha0.trans hr.1
    rw [abs_of_nonneg (by positivity)]
    gcongr
    · rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hη.le ha0 hr.1.le
  calc |∫ r in Ioo a 1, (F r - L) * r⁻¹|
      = ‖∫ r in Ioo a 1, (F r - L) * r⁻¹‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ r in Ioo a 1, (c / 2 * r⁻¹ + C / ρ) :=
        norm_integral_le_of_norm_le hint
          ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound))
    _ = c / 2 * Real.log (1 / a) + C / ρ * (1 - a) := by
        have hi1 : IntegrableOn (fun r => c / 2 * r⁻¹) (Ioo a 1) := by
          refine integrableOn_Ioo_of_bound (C := c / 2 / a) (measurable_const.mul measurable_inv)
            fun r hr => ?_
          have hr0 : 0 < r := ha0.trans hr.1
          rw [abs_of_nonneg (by positivity), ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left hη.le ha0 hr.1.le
        have hi2 : IntegrableOn (fun _ => C / ρ) (Ioo a 1) :=
          integrableOn_Ioo_of_bound (C := |C / ρ|) measurable_const fun r _ => le_rfl
        rw [integral_add hi1 hi2, integral_const_mul, integral_Ioo_inv ha0 ha1.le,
          setIntegral_const, Real.volume_real_Ioo_of_le ha1.le, smul_eq_mul]
        ring
    _ ≤ c / 2 * Real.log (1 / a) + C / ρ := by
        have : 0 ≤ C / ρ := by positivity
        nlinarith
    _ ≤ c * Real.log (1 / a) := by
        have h3 : C / ρ ≤ c / 2 * Real.log (1 / a) := by
          rw [div_le_iff₀ hρ0]
          rw [div_le_iff₀ (by positivity)] at hlg
          nlinarith
        linarith

/-- The shell `{a < |y| < 1}`. -/
def shellY (d : ℕ) (a : ℝ) : Set (Rd d) := {y | a < ‖y‖ ∧ ‖y‖ < 1}

theorem measurableSet_shellY (a : ℝ) : MeasurableSet (shellY d a) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The angular mass at radius `r`: `F_σ(r) := ∫_{S^{d-1}} (σ r^dQ(rη))₊ σ(dη)`, `Q := ∇·P∇G`. -/
noncomputable def angMass (P : Mat d) (σ r : ℝ) : ℝ :=
  (∫⁻ η : Metric.sphere (0 : Rd d) 1, ENNReal.ofReal (σ * (r ^ d *
    secondOrderOp P (maternGreen d) (r • (η : Rd d)))) ∂(volume.toSphere)).toReal

/-- The mass of the unit sphere, `|S^{d-1}|`. -/
noncomputable def sphereMass (d : ℕ) : ℝ := ((volume : Measure (Rd d)).toSphere univ).toReal

theorem measurable_angMass (P : Mat d) (σ : ℝ) : Measurable (angMass P σ) := by
  have hm : Measurable fun p : ℝ × Metric.sphere (0 : Rd d) 1 =>
      ENNReal.ofReal (σ * (p.1 ^ d * secondOrderOp P (maternGreen d) (p.1 • (p.2 : Rd d)))) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ((measurable_fst.pow_const _).mul
      ((measurable_secondOrderOp P _).comp (measurable_fst.smul
        (measurable_subtype_coe.comp measurable_snd)))))
  exact (hm.lintegral_prod_right').ennreal_toReal

theorem lintegral_ofReal_le_of_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {h : X → ℝ} {C : ℝ} (hC : ∀ x, h x ≤ C) :
    ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≤ ENNReal.ofReal C * μ univ := by
  calc ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hC x)
    _ = ENNReal.ofReal C * μ univ := lintegral_const _

theorem ofReal_max_zero (t : ℝ) : ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
  simp

section Shell

variable {P : Mat d} {Mb : ℝ} (σ : ℝ) (hMb0 : 0 ≤ Mb)
  (hMb : ∀ r : ℝ, 0 < r → ∀ η : Rd d, ‖η‖ = 1 →
    |r ^ d * secondOrderOp P (maternGreen d) (r • η)| ≤ Mb)
include hMb

omit hMb in
theorem le_bound_of_hMb (hMb : ∀ r : ℝ, 0 < r → ∀ η : Rd d, ‖η‖ = 1 →
      |r ^ d * secondOrderOp P (maternGreen d) (r • η)| ≤ Mb) {r : ℝ} (hr : 0 < r)
    (η : Metric.sphere (0 : Rd d) 1) :
    σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d))) ≤ |σ| * Mb := by
  calc σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))
      ≤ |σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))| := le_abs_self _
    _ = |σ| * |r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d))| := abs_mul _ _
    _ ≤ |σ| * Mb := by gcongr; exact hMb r hr η (norm_eq_of_mem_sphere η)

theorem angMass_lintegral_ne_top {r : ℝ} (hr : 0 < r) :
    ∫⁻ η : Metric.sphere (0 : Rd d) 1, ENNReal.ofReal (σ * (r ^ d *
      secondOrderOp P (maternGreen d) (r • (η : Rd d)))) ∂(volume.toSphere) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ univ))
    (lintegral_ofReal_le_of_bound _ (C := |σ| * Mb) (le_bound_of_hMb σ hMb hr))

include hMb0 in
theorem angMass_le {r : ℝ} (hr : 0 < r) : angMass P σ r ≤ |σ| * Mb * sphereMass d := by
  have h := lintegral_ofReal_le_of_bound (volume.toSphere : Measure (Metric.sphere (0 : Rd d) 1))
    (C := |σ| * Mb) (le_bound_of_hMb σ hMb hr)
  unfold angMass sphereMass
  calc _ ≤ (ENNReal.ofReal (|σ| * Mb) * (volume : Measure (Rd d)).toSphere univ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **Polar coordinates on the shell**: `∫_{a<|y|<1} (σQ)₊ dy = ∫_a^1 F_σ(r) dr/r`. -/
theorem lintegral_shellY (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in shellY d a, ENNReal.ofReal (σ * secondOrderOp P (maternGreen d) y) =
      ∫⁻ r in Ioo a 1, ENNReal.ofReal (angMass P σ r / r) := by
  set Q := secondOrderOp P (maternGreen d) with hQ
  have hQm : Measurable Q := measurable_secondOrderOp P _
  set f : Rd d → ℝ≥0∞ := (shellY d a).indicator fun y => ENNReal.ofReal (σ * Q y) with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hQm)).indicator (measurableSet_shellY a)
  rw [← lintegral_indicator (measurableSet_shellY a), lintegral_polar hd f hfm]
  have hj : Measurable (Function.uncurry fun (η : Metric.sphere (0 : Rd d) 1) (r : ℝ) =>
      f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))) := by
    refine (hfm.comp (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst))).mul ?_
    exact ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)
  rw [lintegral_lintegral_swap hj.aemeasurable]
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ η : Metric.sphere (0 : Rd d) 1,
      f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1)) ∂(volume.toSphere) =
      (Ioo a 1).indicator (fun r => ENNReal.ofReal (angMass P σ r / r)) r := by
    intro r hr
    have hr0 : 0 < r := hr
    have hnorm : ∀ η : Metric.sphere (0 : Rd d) 1, ‖r • (η : Rd d)‖ = r := fun η => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, norm_eq_of_mem_sphere η, mul_one]
    by_cases hra : r ∈ Ioo a 1
    · rw [indicator_of_mem hra]
      have hin : ∀ η : Metric.sphere (0 : Rd d) 1, f (r • (η : Rd d)) =
          ENNReal.ofReal ((r ^ d)⁻¹) * ENNReal.ofReal (σ * (r ^ d * Q (r • (η : Rd d)))) := by
        intro η
        have hmem : r • (η : Rd d) ∈ shellY d a := by
          simp only [shellY, mem_setOf_eq, hnorm]
          exact hra
        rw [hf, indicator_of_mem hmem, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      simp_rw [hin]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _
        ENNReal.ofReal_ne_top, ← ENNReal.ofReal_toReal (angMass_lintegral_ne_top σ hMb hr0)]
      have hA0 : 0 ≤ angMass P σ r := ENNReal.toReal_nonneg
      rw [← angMass, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (r ^ d)⁻¹),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hA0)]
      congr 1
      have hd1 : r ^ d = r ^ (d - 1) * r := by
        rw [← pow_succ]; congr 1; omega
      rw [hd1]
      field_simp
    · rw [indicator_of_notMem hra]
      have hz : ∀ η : Metric.sphere (0 : Rd d) 1, f (r • (η : Rd d)) = 0 := by
        intro η
        refine indicator_of_notMem ?_ _
        simp only [shellY, mem_setOf_eq, hnorm]
        exact hra
      simp [hz]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Ioo,
    inter_eq_left.2 (show Ioo a 1 ⊆ Ioi (0 : ℝ) from fun r hr => ha.trans hr.1)]

omit hMb in
theorem angMass_eq_integral (r : ℝ) :
    angMass P σ r = ∫ η : Metric.sphere (0 : Rd d) 1,
      max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 ∂(volume.toSphere) := by
  have hm : Measurable fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 :=
    (measurable_const.mul (measurable_const.mul ((measurable_secondOrderOp P _).comp
      (measurable_const.smul measurable_subtype_coe)))).max measurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0)
    (Eventually.of_forall fun η => le_max_right _ _) hm.aestronglyMeasurable, angMass]
  simp_rw [ofReal_max_zero]

omit hMb in
/-- **The limit of the angular mass**: `F_σ(r) → ∫ (σ𝓑_d(d⟨η,Pη⟩ - tr P))₊ dσ` as `r ↓ 0`, from the
uniform limit of `lem:matern-kernel-hessian`(2). -/
theorem tendsto_angMass (hd : 1 ≤ d) (hMb : ∀ r : ℝ, 0 < r → ∀ η : Rd d, ‖η‖ = 1 →
      |r ^ d * secondOrderOp P (maternGreen d) (r • η)| ≤ Mb) :
    Tendsto (angMass P σ) (𝓝[>] 0) (𝓝 (∫ η : Metric.sphere (0 : Rd d) 1,
      max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0 ∂(volume.toSphere))) := by
  set μ : Measure (Metric.sphere (0 : Rd d) 1) := volume.toSphere with hμ
  have hU := tendstoUniformlyOn_maternHessian hd P
  rw [Metric.tendstoUniformlyOn_iff] at hU
  rw [Metric.tendsto_nhds]
  intro ε hε
  set m := sphereMass d with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set ε' := ε / ((|σ| + 1) * (m + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  filter_upwards [hU ε' hε'0, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [angMass_eq_integral σ r, Real.dist_eq]
  have hf : Continuous fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0 := by
    have := continuous_quad_vec P
    fun_prop
  have hgm : Measurable fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 :=
    (measurable_const.mul (measurable_const.mul ((measurable_secondOrderOp P _).comp
      (measurable_const.smul measurable_subtype_coe)))).max measurable_const
  have hgi : Integrable (fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0) μ := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (|σ| * Mb) (Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_bound_of_hMb σ hMb hr0 η) (by
      have := (abs_nonneg _).trans (hMb r hr0 η (norm_eq_of_mem_sphere η))
      positivity)
  have hfi : Integrable (fun η : Metric.sphere (0 : Rd d) 1 =>
      max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0) μ := by
    haveI : CompactSpace (Metric.sphere (0 : Rd d) 1) := isCompact_iff_compactSpace.1
      (isCompact_sphere _ _)
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hgi hfi]
  calc |∫ η, (max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 -
        max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0) ∂μ|
      = ‖∫ η, (max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 -
        max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ _η, |σ| * ε' ∂μ := by
        refine norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs]
        have h1 := hr η (mem_sphere_zero_iff_norm.2 (norm_eq_of_mem_sphere η))
        rw [Real.dist_eq] at h1
        calc |max (σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d)))) 0 -
              max (σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))) 0|
            ≤ |σ * (r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d))) -
              σ * (maternBd d * ((d : ℝ) * quad P η - P.trace))| := abs_max_sub_max_le_abs _ _ _
          _ = |σ| * |maternBd d * ((d : ℝ) * quad P η - P.trace) -
              r ^ d * secondOrderOp P (maternGreen d) (r • (η : Rd d))| := by
              rw [← mul_sub, abs_mul, abs_sub_comm]
          _ ≤ |σ| * ε' := by gcongr
    _ = |σ| * ε' * m := by
        rw [integral_const, smul_eq_mul, mul_comm]
        rfl
    _ < ε := by
        rw [hε']
        have hpos : 0 < (|σ| + 1) * (m + 1) := by positivity
        rw [show |σ| * (ε / ((|σ| + 1) * (m + 1))) * m =
          ε * (|σ| * m / ((|σ| + 1) * (m + 1))) by field_simp]
        have : |σ| * m / ((|σ| + 1) * (m + 1)) < 1 := by
          rw [div_lt_one hpos]
          nlinarith [abs_nonneg σ]
        nlinarith

end Shell

/-- **The substitution `x = Σ'^{1/2}y` on the shells**:
`∫_{E_a} (σq)₊ dx = ∫_{a<|y|<1} (σQ)₊ dy`, `Q = ∇·P'∇G`. -/
theorem lintegral_E_eq {S' : Mat d} (hS' : S'.PosDef) (P : Mat d) (σ : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x in {x | a < ‖lin (msqrt S')⁻¹ x‖ ∧ ‖lin (msqrt S')⁻¹ x‖ < 1},
        ENNReal.ofReal (σ * secondOrderOp P (maternDensity S') x) =
      ∫⁻ y in shellY d a, ENNReal.ofReal (σ * secondOrderOp (relStep S' P) (maternGreen d) y) := by
  set B := msqrt S' with hBdef
  set E : Set (Rd d) := {x | a < ‖lin B⁻¹ x‖ ∧ ‖lin B⁻¹ x‖ < 1} with hE
  have hU : IsUnit B.det := msqrt_mem_glSet hS'
  have hB : B.det ≠ 0 := hU.ne_zero
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const (measurable_norm.comp (lin _).continuous.measurable)).inter
      (measurableSet_lt (measurable_norm.comp (lin _).continuous.measurable) measurable_const)
  set G' : Rd d → ℝ≥0∞ := E.indicator fun x => ENNReal.ofReal (σ * secondOrderOp P
    (maternDensity S') x) with hG'
  have hG'm : Measurable G' := (ENNReal.measurable_ofReal.comp (measurable_const.mul
    (measurable_secondOrderOp P _))).indicator hEm
  have h1 := lintegral_comp_lin hB hG'm
  set c := S'.det ^ (-(1 : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hS'.det_pos.le _
  have hpt : ∀ y, G' (lin B y) = ENNReal.ofReal c * (shellY d a).indicator
      (fun y => ENNReal.ofReal (σ * secondOrderOp (relStep S' P) (maternGreen d) y)) y := by
    intro y
    have hmem : lin B y ∈ E ↔ y ∈ shellY d a := by
      simp only [hE, shellY, mem_setOf_eq, lin_inv_mul_apply hU]
    by_cases hy : y ∈ shellY d a
    · have hy0 : y ≠ 0 := by
        rintro rfl
        simp only [shellY, mem_setOf_eq, norm_zero] at hy
        linarith [hy.1]
      rw [hG', indicator_of_mem (hmem.2 hy), indicator_of_mem hy,
        secondOrderOp_maternDensity_lin hS' P hy0, ← hc, ← ENNReal.ofReal_mul hc0]
      congr 1
      ring
    · rw [hG', indicator_of_notMem (fun h => hy (hmem.1 h)), indicator_of_notMem hy, mul_zero]
  simp_rw [hpt] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator (measurableSet_shellY a), abs_det_msqrt hS'] at h1
  rw [← lintegral_indicator hEm]
  change ∫⁻ x, G' x = _
  have hdet : 0 < S'.det := hS'.det_pos
  have hk : ENNReal.ofReal (S'.det ^ ((1 : ℝ) / 2)) * ENNReal.ofReal (S'.det ^ ((1 : ℝ) / 2))⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc ∫⁻ x, G' x
      = ENNReal.ofReal (S'.det ^ ((1 : ℝ) / 2)) *
          (ENNReal.ofReal (S'.det ^ ((1 : ℝ) / 2))⁻¹ * ∫⁻ x, G' x) := by
        rw [← mul_assoc, hk, one_mul]
    _ = ENNReal.ofReal (S'.det ^ ((1 : ℝ) / 2)) * (ENNReal.ofReal c *
          ∫⁻ y in shellY d a, ENNReal.ofReal (σ * secondOrderOp (relStep S' P) (maternGreen d) y)) := by
        rw [h1]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hc, det_rpow_half_mul hS',
          ENNReal.ofReal_one, one_mul]

/-! ## The angular factor on the sphere -/

theorem sphereMass_eq (hd : 1 ≤ d) : sphereMass d = sphereArea d := by
  rw [sphereMass, ← (sphereArea_eq_toSphere hd).1, ENNReal.toReal_ofReal (sphereArea_eq_toSphere hd).2.le]

/-- `∫_{S^{d-1}} f dσ = |S^{d-1}| ∫ f dσ̄`. -/
theorem integral_toSphere_eq (hd : 1 ≤ d) (f : Rd d → ℝ) :
    ∫ η : Metric.sphere (0 : Rd d) 1, f η ∂(volume.toSphere) =
      sphereMass d * ∫ u, f u ∂normSphere d := by
  have hA := sphereArea_eq_toSphere hd
  have hemb : MeasurableEmbedding (Subtype.val : Metric.sphere (0 : Rd d) 1 → Rd d) :=
    MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
  rw [normSphere, integral_smul_measure, hemb.integral_map, smul_eq_mul, ← mul_assoc,
    ENNReal.toReal_inv, sphereMass, mul_inv_cancel₀, one_mul]
  rw [← hA.1, ENNReal.toReal_ofReal hA.2.le]
  exact hA.2.ne'

theorem integral_coord_mul_coord (hd : 1 ≤ d) (a b : Fin d) :
    ∫ u, u a * u b ∂normSphere d = if a = b then 1 / (d : ℝ) else 0 := by
  split_ifs with h
  · subst h
    rw [← integral_coord_sq hd a]
    congr 1
    funext u
    ring
  · refine integral_normSphere_eq_zero_of_odd a fun u => ?_
    rw [flipIso_apply, flipIso_apply, if_pos rfl, if_neg (Ne.symm h)]
    ring

/-- `∫ ⟨u,Pu⟩ σ̄(du) = tr P/d`. -/
theorem integral_quad_normSphere (hd : 1 ≤ d) (P : Mat d) :
    ∫ u, quad P u ∂normSphere d = P.trace / d := by
  simp_rw [quad_eq_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_normSphere hd (by fun_prop)]
  simp_rw [fun a => integral_finsetSum (μ := normSphere d) (Finset.univ : Finset (Fin d))
    (f := fun b u => u a * u b * P a b) (fun b _ => integrable_normSphere hd (by fun_prop)),
    integral_mul_const, integral_coord_mul_coord hd]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.trace, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diag]
  ring

/-- **The angular factor has mean zero**: `∫_{S^{d-1}} (d⟨η,P'η⟩ - tr P') σ(dη) = 0`. -/
theorem integral_maternAngular (hd : 1 ≤ d) (S S' : Mat d) :
    ∫ η : Metric.sphere (0 : Rd d) 1, maternAngular S S' η ∂(volume.toSphere) = 0 := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  rw [integral_toSphere_eq hd]
  unfold maternAngular
  rw [integral_sub ((integrable_normSphere hd (continuous_quad_vec _)).const_mul _)
    (integrable_const _), integral_const_mul, integral_quad_normSphere hd, integral_const,
    probReal_univ, one_smul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  ring

theorem continuous_maternAngular (S S' : Mat d) : Continuous (maternAngular S S') := by
  unfold maternAngular
  have := continuous_quad_vec (relStep S' (S' - S))
  fun_prop

theorem integrable_sphere_of_continuous {f : Rd d → ℝ} (hf : Continuous f) :
    Integrable (fun η : Metric.sphere (0 : Rd d) 1 => f η) (volume.toSphere) := by
  haveI : CompactSpace (Metric.sphere (0 : Rd d) 1) := isCompact_iff_compactSpace.1
    (isCompact_sphere _ _)
  exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- `𝓑_dΘ` is the limit of both angular masses: `∫ (∓𝓑_d(d⟨η,P'η⟩ - tr P'))₊ dσ = 𝓑_dΘ`. -/
theorem limit_eq_theta (hd : 1 ≤ d) (S S' : Mat d) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∫ η : Metric.sphere (0 : Rd d) 1, max (σ * (maternBd d *
      ((d : ℝ) * quad (relStep S' (S' - S)) η - (relStep S' (S' - S)).trace))) 0
        ∂(volume.toSphere) = maternBd d * maternTheta S S' := by
  have hB := maternBd_pos hd
  have hpt : ∀ η : Rd d, max (σ * (maternBd d *
      ((d : ℝ) * quad (relStep S' (S' - S)) η - (relStep S' (S' - S)).trace))) 0 =
      maternBd d * max (σ * maternAngular S S' η) 0 := by
    intro η
    rw [maternAngular, mul_max_of_nonneg _ _ hB.le, mul_zero, mul_left_comm]
  simp_rw [hpt]
  rw [integral_const_mul, maternTheta]
  congr 1
  rcases hσ with rfl | rfl
  · -- `max(f, 0) = max(-f, 0) + f` and `∫ f = 0`
    have h1 : ∀ η : Rd d, max (1 * maternAngular S S' η) 0 =
        max (-maternAngular S S' η) 0 + maternAngular S S' η := by
      intro η
      rcases le_total (maternAngular S S' η) 0 with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
    simp_rw [h1]
    rw [integral_add (integrable_sphere_of_continuous
      ((continuous_maternAngular S S').neg.max continuous_const))
      (integrable_sphere_of_continuous (continuous_maternAngular S S')),
      integral_maternAngular hd, add_zero]
  · simp_rw [neg_one_mul]

theorem sphereMass_pos (hd : 1 ≤ d) : 0 < sphereMass d := by
  rw [sphereMass_eq hd]; exact (sphereArea_eq_toSphere hd).2

/-- A continuous function, nonnegative on the sphere and positive at a point of it, has positive
`σ̄`-integral. -/
theorem integral_normSphere_pos (hd : 1 ≤ d) {f : Rd d → ℝ} (hf : Continuous f)
    (hnn : ∀ u : Rd d, ‖u‖ = 1 → 0 ≤ f u) {u₀ : Rd d} (hu₀ : ‖u₀‖ = 1) (hpos : 0 < f u₀) :
    0 < ∫ u, f u ∂normSphere d := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  have hae : 0 ≤ᵐ[normSphere d] f := by
    filter_upwards [ae_normSphere_norm] with u hu
    exact hnn u hu
  rw [integral_pos_iff_support_of_nonneg_ae hae (integrable_normSphere hd hf)]
  refine lt_of_lt_of_le (normSphere_pos_of_isOpen hd (isOpen_lt continuous_const hf) hu₀ hpos)
    (measure_mono fun u hu => ?_)
  exact ne_of_gt hu

theorem relStep_sub_eq {S S' : Mat d} (hS' : S'.PosDef) :
    relStep S' (S' - S) = 1 - relStep S' S := by
  rw [relStep_sub, relStep_self hS']

/-- **`Θ > 0` if and only if `Σ'` is not a multiple of `Σ`** (`prop:matern-negative-mass`(3)). -/
theorem maternTheta_pos_iff (hd : 2 ≤ d) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) :
    0 < maternTheta S S' ↔ ¬ ∃ c : ℝ, S' = c • S := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  set P' := relStep S' (S' - S) with hP'
  have hP'h : P'.IsHermitian := relStep_isHermitian S' (hS'.isHermitian.sub hS.isHermitian)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  constructor
  · rintro hpos ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have := hS'.det_pos
      rw [hc, Matrix.det_zero (Fin.pos_iff_nonempty.1 (by omega))] at this
      exact lt_irrefl _ this
    have hSeq : S = c⁻¹ • S' := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hP'eq : P' = (1 - c⁻¹) • (1 : Mat d) := by
      rw [hP', relStep_sub_eq hS', hSeq, relStep_smul, relStep_self hS', sub_smul, one_smul]
    have hzero : ∀ η : Metric.sphere (0 : Rd d) 1, max (-maternAngular S S' η) 0 = 0 := by
      intro η
      have hη := norm_eq_of_mem_sphere η
      rw [maternAngular, ← hP', hP'eq, quad_smul, quad_one, hη, Matrix.trace_smul,
        Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      simp only [one_pow, mul_one]
      rw [show (d : ℝ) * (1 - c⁻¹) - (1 - c⁻¹) * d = 0 by ring, neg_zero, max_self]
    rw [maternTheta] at hpos
    simp_rw [hzero, integral_zero] at hpos
    exact lt_irrefl _ hpos
  · intro hns
    -- `P'` is not a multiple of `I`
    have hnsP : ¬ ∃ κ : ℝ, P' = κ • (1 : Mat d) := by
      rintro ⟨κ, hκ⟩
      rw [hP', relStep_sub_eq hS'] at hκ
      have h1 : relStep S' S = (1 - κ) • (1 : Mat d) := by
        rw [sub_smul, one_smul, ← hκ]; abel
      have h2 : S = (1 - κ) • S' := by
        rw [← msqrt_mul_relStep hS' S, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          msqrt_mul_self hS'.posSemidef]
      by_cases hk : 1 - κ = 0
      · rw [hk, zero_smul] at h2
        have := hS.det_pos
        rw [h2, Matrix.det_zero (Fin.pos_iff_nonempty.1 (by omega))] at this
        exact lt_irrefl _ this
      · exact hns ⟨(1 - κ)⁻¹, by rw [h2, smul_smul, inv_mul_cancel₀ hk, one_smul]⟩
    obtain ⟨u, v, hu, hv, huv⟩ := exists_quad_lt_of_not_scalar hP'h hnsP
    -- the angular factor is negative somewhere on the sphere
    have hneg : ∃ η₀ : Rd d, ‖η₀‖ = 1 ∧ maternAngular S S' η₀ < 0 := by
      by_contra hcon
      push Not at hcon
      have hposu : 0 < maternAngular S S' u := by
        have h1 := hcon v hv
        unfold maternAngular at h1 ⊢
        rw [← hP'] at h1 ⊢
        have : (d : ℝ) * quad P' v < d * quad P' u :=
          mul_lt_mul_of_pos_left huv (by positivity)
        linarith
      have h0 := integral_maternAngular hd1 S S'
      rw [integral_toSphere_eq hd1] at h0
      have h3 := integral_normSphere_pos hd1 (continuous_maternAngular S S') hcon hu hposu
      have h4 := sphereMass_pos (d := d) hd1
      have : 0 < sphereMass d * ∫ u, maternAngular S S' u ∂normSphere d := mul_pos h4 h3
      linarith
    obtain ⟨η₀, hη₀, hη₀neg⟩ := hneg
    rw [maternTheta, integral_toSphere_eq hd1 (fun y => max (-maternAngular S S' y) 0)]
    refine mul_pos (sphereMass_pos hd1) (integral_normSphere_pos hd1
      ((continuous_maternAngular S S').neg.max continuous_const)
      (fun u _ => le_max_right _ _) hη₀ ?_)
    exact lt_max_of_lt_left (by linarith)

/-! ## The total variation of a would-be signed increment -/

/-- **The negative mass is bounded by `ρ₋`**: if `μ_{Σ'} + μ_Σ * ρ₋ = μ_Σ * ρ₊`, then
`∫_{E_a} q₋ dx ≤ ρ₋(ℝ^d)` for every `a ∈ (0,1)`: the smooth functions `s((n+1)g)`, `g` smooth with
support `E_a ∩ {q < 0}`, increase to the indicator of that set, and each has `∫ φ q = ρ(φ) ≥ -ρ₋(ℝ^d)`. -/
theorem lintegral_neg_le_mass (hd : 2 ≤ d) (μI : Measure (Rd d)) (hμI : IsMaternLaw 1 μI)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hP : loewnerLE S S') (hP0 : S' - S ≠ 0)
    (ρp ρm : Measure (Rd d)) [IsFiniteMeasure ρp] [IsFiniteMeasure ρm]
    (h : affineOrbit μI S' + affineOrbit μI S ∗ ρm = affineOrbit μI S ∗ ρp) {a : ℝ}
    (ha : 0 < a) :
    ∫⁻ x in {x | a < ‖lin (msqrt S')⁻¹ x‖ ∧ ‖lin (msqrt S')⁻¹ x‖ < 1},
      ENNReal.ofReal (-secondOrderOp (S' - S) (maternDensity S') x) ≤
        ENNReal.ofReal (ρm.real univ) := by
  set q := secondOrderOp (S' - S) (maternDensity S') with hq
  set A := (msqrt S')⁻¹ with hA
  set E : Set (Rd d) := {x | a < ‖lin A x‖ ∧ ‖lin A x‖ < 1} with hE
  have hqc : ContinuousOn q {0}ᶜ := (contDiffOn_secondOrderOp_maternDensity hS' _).continuousOn
  have hqm : Measurable q := measurable_secondOrderOp _ _
  have hlinA : Continuous fun x => ‖lin A x‖ := continuous_norm.comp (lin A).continuous
  have hEo : IsOpen E := (isOpen_lt continuous_const hlinA).inter (isOpen_lt hlinA continuous_const)
  have hE0 : E ⊆ {0}ᶜ := by
    intro x hx h0
    rw [mem_singleton_iff] at h0
    rw [hE, mem_setOf_eq, h0, map_zero, norm_zero] at hx
    linarith [hx.1]
  set U := E ∩ q ⁻¹' Iio 0 with hU
  have hUo : IsOpen U := by
    have h1 := hqc.isOpen_inter_preimage isOpen_compl_singleton (isOpen_Iio (a := (0 : ℝ)))
    have : U = E ∩ ({0}ᶜ ∩ q ⁻¹' Iio 0) := by
      ext x
      simp only [hU, mem_inter_iff]
      exact ⟨fun h => ⟨h.1, hE0 h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hEo.inter h1
  obtain ⟨g, hgs, hgc, hgr⟩ := hUo.exists_contDiff_support_eq (n := ⊤)
  have hg0 : ∀ x, 0 ≤ g x := fun x => (hgr ⟨x, rfl⟩).1
  -- the compact set `K ⊇ E`, away from the origin
  set K : Set (Rd d) := {x | a ≤ ‖lin A x‖ ∧ ‖lin A x‖ ≤ 1} with hK
  have hKc : IsClosed K := (isClosed_le continuous_const hlinA).inter
    (isClosed_le hlinA continuous_const)
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨‖lin (msqrt S')‖, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    have hx' : x = lin (msqrt S') (lin A x) := (lin_mul_inv_apply (msqrt_mem_glSet hS') x).symm
    calc ‖x‖ = ‖lin (msqrt S') (lin A x)‖ := by rw [← hx']
      _ ≤ ‖lin (msqrt S')‖ * ‖lin A x‖ := (lin _).le_opNorm _
      _ ≤ ‖lin (msqrt S')‖ * 1 := by gcongr; exact hx.2
      _ = _ := mul_one _
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have h0K : (0 : Rd d) ∉ K := by
    intro h0
    rw [hK, mem_setOf_eq, map_zero, norm_zero] at h0
    linarith [h0.1]
  have hEK : E ⊆ K := fun x hx => ⟨hx.1.le, hx.2.le⟩
  -- the test functions
  set φ : ℕ → Rd d → ℝ := fun n x => Real.smoothTransition ((n + 1) * g x) with hφ
  have hφs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hgc)
  have hφ0 : ∀ n x, x ∉ U → φ n x = 0 := by
    intro n x hx
    have : g x = 0 := by
      by_contra hne
      exact hx (hgs ▸ hne)
    simp [hφ, this]
  have hφsupp : ∀ n, tsupport (φ n) ⊆ K := fun n =>
    closure_minimal (fun x hx => hEK (by_contra fun hU' => hx (hφ0 n x (fun h => hU' h.1))))
      hKc
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    hKcpt.of_isClosed_subset (isClosed_tsupport _) (hφsupp n)
  have hφ01 : ∀ n x, 0 ≤ φ n x ∧ φ n x ≤ 1 := fun n x =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- each test function: `∫ φ (-q) ≤ ρ₋(ℝ^d)`
  have hprod_cont : ∀ n, Continuous fun x => φ n x * q x := by
    intro n
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hev : (fun x => φ n x * q x) =ᶠ[𝓝 (0 : Rd d)] fun _ => 0 := by
        filter_upwards [hKc.isOpen_compl.mem_nhds h0K] with y hy
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφsupp n h)), zero_mul]
      exact (continuousAt_const.congr hev.symm)
    · exact (hφs n).continuous.continuousAt.mul
        (hqc.continuousAt (isOpen_compl_singleton.mem_nhds hx))
  have hprod_int : ∀ n, Integrable fun x => φ n x * (-q x) := by
    intro n
    have := ((hprod_cont n).neg).integrable_of_hasCompactSupport (μ := volume)
      (hφc n).mul_right.neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    ring
  have hnn : ∀ n x, 0 ≤ φ n x * (-q x) := by
    intro n x
    by_cases hx : x ∈ U
    · exact mul_nonneg (hφ01 n x).1 (by linarith [show q x < 0 from hx.2])
    · rw [hφ0 n x hx, zero_mul]
  have hbound : ∀ n, ∫ x, φ n x * (-q x) ≤ ρm.real univ := by
    intro n
    set T := testSchwartz (φ n) (hφs n) (hφc n) with hT
    have hTe : (T : Rd d → ℂ) = Complex.ofReal ∘ φ n := rfl
    have hT0 : (0 : Rd d) ∉ tsupport T := fun h0 => h0K (hφsupp n
      (tsupport_comp_subset Complex.ofReal_zero (φ n) (hTe ▸ h0)))
    have hTc : HasCompactSupport T := hTe ▸ (hφc n).comp_left Complex.ofReal_zero
    have h1 := maternIncrement_off_origin μI hμI hS hS' T hTc hT0
    have h2 := maternIncrement_eq_integral hd μI hμI hS hS' hP hP0 ρp ρm h T
    rw [h1, hTe] at h2
    simp only [Function.comp_apply] at h2
    simp_rw [← Complex.ofReal_mul] at h2
    rw [integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub] at h2
    have e := Complex.ofReal_injective h2
    have hp : 0 ≤ ∫ x, φ n x ∂ρp := integral_nonneg fun x => (hφ01 n x).1
    have hm : ∫ x, φ n x ∂ρm ≤ ρm.real univ := by
      have hi : Integrable (φ n) ρm := Integrable.of_bound (hφs n).continuous.aestronglyMeasurable
        1 (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 n x).1]; exact (hφ01 n x).2)
      calc ∫ x, φ n x ∂ρm ≤ ∫ _x, (1 : ℝ) ∂ρm :=
            integral_mono hi (integrable_const _) fun x => (hφ01 n x).2
        _ = ρm.real univ := by rw [integral_const, smul_eq_mul, mul_one]
    have hneg : ∫ x, φ n x * (-q x) = -∫ x, φ n x * q x := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    rw [hneg, e]
    linarith
  -- monotone convergence
  set F : ℕ → Rd d → ℝ≥0∞ := fun n x => ENNReal.ofReal (φ n x * (-q x)) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp ((hφs n).continuous.measurable.mul hqm.neg)
  have hFle : ∀ n, ∫⁻ x, F n x ≤ ENNReal.ofReal (ρm.real univ) := by
    intro n
    rw [hF, ← ofReal_integral_eq_lintegral_ofReal (hprod_int n)
      (Eventually.of_forall (hnn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hmono : Monotone F := by
    intro n m hnm x
    simp only [hF]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hx : x ∈ U
    · have hqx : 0 ≤ -q x := by linarith [show q x < 0 from hx.2]
      refine mul_le_mul_of_nonneg_right (Real.smoothTransition.monotone ?_) hqx
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      nlinarith [hg0 x]
    · rw [hφ0 n x hx, hφ0 m x hx]
  have hsup : ∀ x, ⨆ n, F n x = U.indicator (fun x => ENNReal.ofReal (-q x)) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      have hgx : 0 < g x := lt_of_le_of_ne (hg0 x) (Ne.symm (by
        have : x ∈ Function.support g := hgs ▸ hx
        exact this))
      refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal ?_) ?_
      · have hqx : 0 ≤ -q x := by linarith [show q x < 0 from hx.2]
        calc φ n x * (-q x) ≤ 1 * (-q x) := mul_le_mul_of_nonneg_right (hφ01 n x).2 hqx
          _ = -q x := one_mul _
      · obtain ⟨n, hn⟩ := exists_nat_gt (1 / g x)
        refine le_iSup_of_le n (le_of_eq ?_)
        simp only [hF, hφ]
        rw [Real.smoothTransition.one_of_one_le, one_mul]
        rw [div_lt_iff₀ hgx] at hn
        nlinarith
    · rw [indicator_of_notMem hx]
      simp [hF, hφ0 _ x hx]
  have hEm : MeasurableSet E := hEo.measurableSet
  have hEU : ∫⁻ x in E, ENNReal.ofReal (-q x) =
      ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (-q x)) x := by
    rw [← lintegral_indicator hEm]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, indicator_of_mem hx.1]
    · rw [indicator_of_notMem hx]
      by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]
        have : 0 ≤ q x := by
          by_contra hc
          exact hx ⟨hxE, show q x < 0 from lt_of_not_ge hc⟩
        exact ENNReal.ofReal_of_nonpos (by linarith)
      · rw [indicator_of_notMem hxE]
  change ∫⁻ x in E, ENNReal.ofReal (-q x) ≤ _
  rw [hEU]
  simp_rw [← hsup]
  rw [lintegral_iSup hFm hmono]
  exact iSup_le hFle

/-! ## Clause (3) -/

/-- **`prop:matern-negative-mass`(3)**, the negative mass diverges logarithmically: on
`E_a = {a < |Σ'^{-1/2}x| < 1}`, `∫_{E_a} q₋ = 𝓑_dΘ log(1/a) + o(log(1/a))` as `a ↓ 0`, and the same
for `q₊`; `Θ > 0` if and only if `Σ'` is not a multiple of `Σ`, and then no finite signed measure
`ρ` has `μ_{Σ'} = μ_Σ * ρ`. -/
theorem matern_negative_mass_log (hd : 2 ≤ d) (μI : Measure (Rd d)) (hμI : IsMaternLaw 1 μI)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hP : loewnerLE S S') (hP0 : S' - S ≠ 0) :
    let q := secondOrderOp (S' - S) (maternDensity S')
    let E : ℝ → Set (Rd d) := fun a =>
      {x | a < ‖lin (msqrt S')⁻¹ x‖ ∧ ‖lin (msqrt S')⁻¹ x‖ < 1}
    (∀ a ∈ Ioo (0 : ℝ) 1, ∫⁻ x in E a, ENNReal.ofReal (-q x) ≠ ⊤ ∧
        ∫⁻ x in E a, ENNReal.ofReal (q x) ≠ ⊤) ∧
      (fun a => (∫⁻ x in E a, ENNReal.ofReal (-q x)).toReal -
          maternBd d * maternTheta S S' * Real.log (1 / a)) =o[𝓝[>] 0]
        (fun a => Real.log (1 / a)) ∧
      (fun a => (∫⁻ x in E a, ENNReal.ofReal (q x)).toReal -
          maternBd d * maternTheta S S' * Real.log (1 / a)) =o[𝓝[>] 0]
        (fun a => Real.log (1 / a)) ∧
      (0 < maternTheta S S' ↔ ¬ ∃ c : ℝ, S' = c • S) ∧
      (0 < maternTheta S S' → ¬ ∃ ρp ρm : Measure (Rd d), IsFiniteMeasure ρp ∧ IsFiniteMeasure ρm ∧
        affineOrbit μI S' + affineOrbit μI S ∗ ρm = affineOrbit μI S ∗ ρp) := by
  intro q E
  have hd1 : 1 ≤ d := by omega
  set P' := relStep S' (S' - S) with hP'
  set Mb := ‖lin P'‖ * maternA d 0 + |P'.trace| * maternB d 0 with hMbdef
  have hMb0 : 0 ≤ Mb := by
    have := (maternA_nonneg_le (d := d) hd1 0).1
    have := (maternB_nonneg_le (d := d) hd1 0).1
    positivity
  have hMb := fun r hr η hη => abs_maternHessian_le (d := d) hd1 P' (r := r) hr (y := η) hη
  set m := sphereMass d with hm
  -- the masses as integrals in `r`
  have key : ∀ σ : ℝ, ∀ a : ℝ, 0 < a → ∫⁻ x in E a, ENNReal.ofReal (σ * q x) =
      ∫⁻ r in Ioo a 1, ENNReal.ofReal (angMass P' σ r / r) := fun σ a ha =>
    (lintegral_E_eq hS' (S' - S) σ ha).trans (lintegral_shellY σ hMb hd1 ha)
  have hnegq : ∀ a, ∫⁻ x in E a, ENNReal.ofReal (-q x) =
      ∫⁻ x in E a, ENNReal.ofReal ((-1) * q x) := fun a => by simp_rw [neg_one_mul]
  have hposq : ∀ a, ∫⁻ x in E a, ENNReal.ofReal (q x) =
      ∫⁻ x in E a, ENNReal.ofReal (1 * q x) := fun a => by simp_rw [one_mul]
  have hfin : ∀ σ : ℝ, ∀ a ∈ Ioo (0 : ℝ) 1,
      ∫⁻ r in Ioo a 1, ENNReal.ofReal (angMass P' σ r / r) ≠ ⊤ := by
    intro σ a ha
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (|σ| * Mb * m / a) * volume (Ioo a 1))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Ioo_lt_top.ne) ?_
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ENNReal.ofReal_le_ofReal ?_
    have hr0 : 0 < r := ha.1.trans hr.1
    have h1 := angMass_le σ hMb0 hMb hr0
    have h0 : 0 ≤ angMass P' σ r := ENNReal.toReal_nonneg
    calc angMass P' σ r / r ≤ |σ| * Mb * m / r := div_le_div_of_nonneg_right h1 hr0.le
      _ ≤ |σ| * Mb * m / a := div_le_div_of_nonneg_left (by
          have := ENNReal.toReal_nonneg (a := (volume : Measure (Rd d)).toSphere univ)
          positivity) ha.1 hr.1.le
  have hasym : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (fun a => (∫⁻ x in E a, ENNReal.ofReal (σ * q x)).toReal -
        maternBd d * maternTheta S S' * Real.log (1 / a)) =o[𝓝[>] 0]
          (fun a => Real.log (1 / a)) := by
    intro σ hσ
    have hlim := tendsto_angMass σ hd1 hMb
    rw [limit_eq_theta hd1 S S' σ hσ] at hlim
    have h := isLittleO_lintegral_div (measurable_angMass P' σ)
      (fun r _ _ => ENNReal.toReal_nonneg) (fun r hr _ => angMass_le σ hMb0 hMb hr) hlim
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha
    rw [key σ a ha.1]
  refine ⟨fun a ha => ⟨?_, ?_⟩, ?_, ?_, maternTheta_pos_iff hd hS hS', ?_⟩
  · rw [hnegq, key _ a ha.1]; exact hfin _ a ha
  · rw [hposq, key _ a ha.1]; exact hfin _ a ha
  · have := hasym (-1) (Or.inr rfl)
    simp_rw [neg_one_mul] at this
    exact this
  · have := hasym 1 (Or.inl rfl)
    simp_rw [one_mul] at this
    exact this
  · rintro hpos ⟨ρp, ρm, hp, hm', hid⟩
    have hL : 0 < maternBd d * maternTheta S S' := mul_pos (maternBd_pos hd1) hpos
    have hX : ∀ a ∈ Ioo (0 : ℝ) 1,
        (∫⁻ x in E a, ENNReal.ofReal (-q x)).toReal ≤ ρm.real univ := by
      intro a ha
      have h := lintegral_neg_le_mass hd μI hμI hS hS' hP hP0 ρp ρm hid ha.1
      calc (∫⁻ x in E a, ENNReal.ofReal (-q x)).toReal
          ≤ (ENNReal.ofReal (ρm.real univ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        _ = ρm.real univ := ENNReal.toReal_ofReal measureReal_nonneg
    have hasy := (hasym (-1) (Or.inr rfl))
    simp_rw [neg_one_mul] at hasy
    have hb := hasy.bound (half_pos hL)
    have hlog : Tendsto (fun a : ℝ => Real.log (1 / a)) (𝓝[>] 0) atTop := by
      have : (fun a : ℝ => Real.log (1 / a)) = fun a => -Real.log a := by
        funext a
        rw [one_div, Real.log_inv]
      rw [this]
      exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have hI : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨a, hab, ha, hla⟩ := (hb.and (hI.and
      (hlog.eventually (eventually_gt_atTop
        (2 * (ρm.real univ + 1) / (maternBd d * maternTheta S S')))))).exists
    have hl0 : 0 < Real.log (1 / a) := by
      have := div_pos (show (0 : ℝ) < 2 * (ρm.real univ + 1) by
        have := measureReal_nonneg (μ := ρm) (s := univ); linarith) hL
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl0] at hab
    have hXa := hX a ha
    rw [div_lt_iff₀ hL] at hla
    have := neg_abs_le ((∫⁻ x in E a, ENNReal.ofReal (-q x)).toReal -
      maternBd d * maternTheta S S' * Real.log (1 / a))
    nlinarith

/-! ## Clause (4): the plane -/

/-- `∫_{-π}^{π} (cos(2θ - φ₀))₋ dθ = 2`. Mathlib types only. -/
theorem integral_max_neg_cos_shift (φ₀ : ℝ) :
    ∫ θ in (-Real.pi)..Real.pi, max (-Real.cos (2 * θ - φ₀)) 0 = 2 := by
  set g : ℝ → ℝ := fun t => max (-Real.cos t) 0 with hg
  have hgc : Continuous g := by fun_prop
  have hgp : Function.Periodic g (2 * Real.pi) := fun t => by
    simp only [hg, Real.cos_add_two_pi]
  have h1 : ∫ θ in (-Real.pi)..Real.pi, g (2 * θ - φ₀) =
      (2 : ℝ)⁻¹ • ∫ t in (2 * -Real.pi - φ₀)..(2 * Real.pi - φ₀), g t :=
    intervalIntegral.integral_comp_mul_sub (f := g) two_ne_zero φ₀
  have hper : ∀ s : ℝ, ∫ t in s..s + 2 * Real.pi, g t = 2 := by
    intro s
    rw [hgp.intervalIntegral_add_eq s (-(Real.pi / 2))]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (μ := volume) (-(Real.pi / 2)) (Real.pi / 2))
      (hgc.intervalIntegrable (μ := volume) (Real.pi / 2) (-(Real.pi / 2) + 2 * Real.pi))
    rw [← hsplit]
    have hA : ∫ t in (-(Real.pi / 2))..(Real.pi / 2), g t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
      intro t ht
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at ht
      simp only [hg]
      have := Real.cos_nonneg_of_mem_Icc ht
      exact max_eq_right (by linarith)
    have hB : ∫ t in (Real.pi / 2)..(-(Real.pi / 2) + 2 * Real.pi), g t = 2 := by
      rw [intervalIntegral.integral_congr (g := fun t => -Real.cos t), intervalIntegral.integral_neg,
        integral_cos]
      · have e1 : -(Real.pi / 2) + 2 * Real.pi = Real.pi / 2 + Real.pi := by ring
        rw [e1, Real.sin_add_pi, Real.sin_pi_div_two]
        ring
      · intro t ht
        rw [uIcc_of_le (by linarith [Real.pi_pos])] at ht
        simp only [hg]
        have := Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2])
        exact max_eq_left (by linarith)
    rw [hA, hB, zero_add]
  rw [show (fun θ => max (-Real.cos (2 * θ - φ₀)) 0) = fun θ => g (2 * θ - φ₀) from rfl, h1]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (μ := volume) (2 * -Real.pi - φ₀) (2 * -Real.pi - φ₀ + 2 * Real.pi))
    (hgc.intervalIntegrable (μ := volume) (2 * -Real.pi - φ₀ + 2 * Real.pi) (2 * Real.pi - φ₀))
  rw [← hsplit, hper, show 2 * Real.pi - φ₀ = (2 * -Real.pi - φ₀ + 2 * Real.pi) + 2 * Real.pi by ring,
    hper, smul_eq_mul]
  norm_num

/-- The unit vector `(cos θ, sin θ)` of the plane. -/
noncomputable def unitVec (θ : ℝ) : Rd 2 := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

theorem norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unitVec, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

theorem continuous_unitVec : Continuous unitVec := by
  unfold unitVec
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

theorem measurable_unitVec : Measurable unitVec := continuous_unitVec.measurable

/-- **Polar angle on the circle**: `∫_{S¹} h dσ = ∫_{-π}^{π} h(cos θ, sin θ) dθ`. -/
theorem lintegral_sphere_two {h : Rd 2 → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ η : Metric.sphere (0 : Rd 2) 1, h η ∂(volume.toSphere) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, h (unitVec θ) := by
  set F : Rd 2 → ℝ≥0∞ := (Metric.ball (0 : Rd 2) 1).indicator fun x => h (‖x‖⁻¹ • x) with hF
  have hFm : Measurable F :=
    (hh.comp ((measurable_norm.inv).smul measurable_id)).indicator measurableSet_ball
  have hhalf : ∫⁻ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal r) r =
      ENNReal.ofReal (1 / 2) := by
    rw [setLIntegral_indicator measurableSet_Iio, show Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 by
      ext; simp [and_comm], ← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
        integral_id]
      norm_num
    · exact (continuous_id.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr => hr.1.le)
  -- polar coordinates on `ℝ^2` through the sphere
  have hA : ∫⁻ x, F x = ENNReal.ofReal (1 / 2) *
      ∫⁻ η : Metric.sphere (0 : Rd 2) 1, h η ∂(volume.toSphere) := by
    rw [lintegral_polar (by norm_num) F hFm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun η => ?_
    have hη := norm_eq_of_mem_sphere η
    have hpt : ∀ r ∈ Ioi (0 : ℝ), F (r • (η : Rd 2)) * ENNReal.ofReal (r ^ (2 - 1)) =
        h η * (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal r) r := by
      intro r hr
      have hr0 : 0 < r := hr
      have hn : ‖r • (η : Rd 2)‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hη, mul_one]
      by_cases hr1 : r < 1
      · rw [hF, indicator_of_mem (by rw [mem_ball_zero_iff, hn]; exact hr1),
          indicator_of_mem (show r ∈ Iio (1 : ℝ) from hr1), hn, smul_smul,
          inv_mul_cancel₀ hr0.ne', one_smul]
        norm_num
      · rw [hF, indicator_of_notMem (by rw [mem_ball_zero_iff, hn]; exact hr1),
          indicator_of_notMem (show r ∉ Iio (1 : ℝ) from hr1), zero_mul, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _
      (ENNReal.measurable_ofReal.indicator measurableSet_Iio), hhalf, mul_comm]
  -- the same integral through `ℝ × ℝ` and `polarCoord`
  set g : ℝ × ℝ → Rd 2 := fun p => WithLp.toLp 2 ![p.1, p.2] with hg
  have hmp : MeasurePreserving g volume volume := by
    exact (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm
  have hB : ∫⁻ x, F x = ENNReal.ofReal (1 / 2) * ∫⁻ θ in Ioo (-Real.pi) Real.pi, h (unitVec θ) := by
    have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 • F (g (polarCoord.symm p)) =
          (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal r) p.1 * h (unitVec p.2) := by
      rintro ⟨r, θ⟩ ⟨hr, _⟩
      have hr0 : 0 < r := hr
      have hgv : g (polarCoord.symm (r, θ)) = r • unitVec θ := by
        simp only [hg, polarCoord_symm_apply, unitVec]
        ext i
        fin_cases i <;> simp
      have hn : ‖r • unitVec θ‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, norm_unitVec, mul_one]
      simp only
      rw [hgv]
      by_cases hr1 : r < 1
      · rw [hF, indicator_of_mem (by rw [mem_ball_zero_iff, hn]; exact hr1),
          indicator_of_mem (show r ∈ Iio (1 : ℝ) from hr1), hn, smul_smul,
          inv_mul_cancel₀ hr0.ne', one_smul, smul_eq_mul]
      · rw [hF, indicator_of_notMem (by rw [mem_ball_zero_iff, hn]; exact hr1),
          indicator_of_notMem (show r ∉ Iio (1 : ℝ) from hr1), zero_mul, smul_zero]
    rw [← hmp.lintegral_comp hFm, ← lintegral_comp_polarCoord_symm, polarCoord_target,
      setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt,
      Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_mul (f := (Iio (1 : ℝ)).indicator fun r => ENNReal.ofReal r)
        (g := fun θ => h (unitVec θ))
        (ENNReal.measurable_ofReal.indicator measurableSet_Iio).aemeasurable
        (hh.comp measurable_unitVec).aemeasurable, hhalf]
  rw [hA] at hB
  exact (ENNReal.mul_right_inj (by norm_num) ENNReal.ofReal_ne_top).1 hB

/-- The angular factor in the plane, in polar angle:
`2⟨u,Pu⟩ - tr P = (P₁₁ - P₂₂) cos 2θ + 2P₁₂ sin 2θ` at `u = (cos θ, sin θ)`, `P` symmetric. -/
theorem angular_plane {P : Mat 2} (hP : P.IsHermitian) (θ : ℝ) :
    (2 : ℝ) * quad P (unitVec θ) - P.trace =
      (P 0 0 - P 1 1) * Real.cos (2 * θ) + 2 * P 0 1 * Real.sin (2 * θ) := by
  have h10 : P 1 0 = P 0 1 := by
    have := hP.apply 1 0
    simpa using this.symm
  rw [quad_eq_sum, Matrix.trace_fin_two]
  simp only [Fin.sum_univ_two]
  have hu0 : (unitVec θ) 0 = Real.cos θ := rfl
  have hu1 : (unitVec θ) 1 = Real.sin θ := rfl
  rw [hu0, hu1, h10, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (2 * P 1 1) * Real.cos_sq_add_sin_sq θ

/-- `R := √((P₁₁ - P₂₂)² + 4P₁₂²)`, the gap between the two eigenvalues of a symmetric `2 × 2`
matrix. -/
noncomputable def gap2 (P : Mat 2) : ℝ := Real.sqrt ((P 0 0 - P 1 1) ^ 2 + 4 * P 0 1 ^ 2)

/-- **`Θ` in the plane**: `Θ = 2R`. -/
theorem maternTheta_plane_eq (S S' : Mat 2) (hP : (relStep S' (S' - S)).IsHermitian) :
    maternTheta S S' = 2 * gap2 (relStep S' (S' - S)) := by
  set P := relStep S' (S' - S) with hPdef
  set R := gap2 P with hR
  set z : ℂ := ⟨P 0 0 - P 1 1, 2 * P 0 1⟩ with hz
  have hzn : ‖z‖ = R := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hR, gap2]
    congr 1
    simp only [hz]
    ring
  have hR0 : 0 ≤ R := hzn ▸ norm_nonneg _
  have hang : ∀ θ, maternAngular S S' (unitVec θ) = R * Real.cos (2 * θ - Complex.arg z) := by
    intro θ
    rw [maternAngular, ← hPdef, show ((2 : ℕ) : ℝ) = 2 by norm_num, angular_plane hP θ,
      Real.cos_sub]
    have hc := Complex.norm_mul_cos_arg z
    have hs := Complex.norm_mul_sin_arg z
    rw [hzn] at hc hs
    have hre : z.re = P 0 0 - P 1 1 := rfl
    have him : z.im = 2 * P 0 1 := rfl
    rw [hre] at hc
    rw [him] at hs
    linear_combination (-Real.cos (2 * θ)) * hc + (-Real.sin (2 * θ)) * hs
  have hcont : Continuous fun y : Rd 2 => max (-maternAngular S S' y) 0 :=
    (continuous_maternAngular S S').neg.max continuous_const
  rw [maternTheta, integral_eq_lintegral_of_nonneg_ae (f := fun η : Metric.sphere (0 : Rd 2) 1 =>
      max (-maternAngular S S' η) 0) (Eventually.of_forall fun η => le_max_right _ _)
    (hcont.comp continuous_subtype_val).aestronglyMeasurable,
    lintegral_sphere_two (h := fun y => ENNReal.ofReal (max (-maternAngular S S' y) 0))
      (ENNReal.measurable_ofReal.comp hcont.measurable),
    ← integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
      (f := fun θ => max (-maternAngular S S' (unitVec θ)) 0)
      (Eventually.of_forall fun θ => le_max_right _ _)
      (hcont.comp continuous_unitVec).aestronglyMeasurable,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp_rw [hang]
  have hpt : ∀ θ, max (-(R * Real.cos (2 * θ - Complex.arg z))) 0 =
      R * max (-Real.cos (2 * θ - Complex.arg z)) 0 := by
    intro θ
    rw [mul_max_of_nonneg _ _ hR0, mul_zero, mul_neg]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_max_neg_cos_shift]
  ring

/-- The eigenvalues of a symmetric `2 × 2` matrix: `λ↑ = ((tr - R)/2, (tr + R)/2)`. -/
theorem eigUp_two {P : Mat 2} (hP : P.IsHermitian) :
    eigUp P = ![(P.trace - gap2 P) / 2, (P.trace + gap2 P) / 2] := by
  have h10 : P 1 0 = P 0 1 := by
    have := hP.apply 1 0
    simpa using this.symm
  set R := gap2 P with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (P 0 0 - P 1 1) ^ 2 + 4 * P 0 1 ^ 2 := Real.sq_sqrt (by positivity)
  refine eigUp_eq_of_roots ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  · set a := (P.trace - R) / 2
    set b := (P.trace + R) / 2
    have hfac : P.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) := by
      rw [Matrix.charpoly_fin_two]
      have hsum : a + b = P.trace := by simp only [a, b]; ring
      have hprod : a * b = P.det := by
        simp only [a, b]
        rw [Matrix.det_fin_two, Matrix.trace_fin_two, h10]
        nlinarith [hR2]
      rw [← hsum, ← hprod]
      simp only [map_add, map_mul]
      ring
    rw [hfac, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero a)
      (Polynomial.X_sub_C_ne_zero b)), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    simp [Fin.univ_val_map, List.ofFn_succ]
    rfl

/-- **`prop:matern-negative-mass`(4)**, the plane: for `d = 2` and `p₁ ≥ p₂` the eigenvalues of
`P'`, `𝓑₂Θ = (p₁ - p₂)/π`. -/
theorem matern_negative_mass_plane {S S' : Mat 2} (hS : S.PosDef) (hS' : S'.PosDef)
    (_hP : loewnerLE S S') (_hP0 : S' - S ≠ 0) :
    maternBd 2 * maternTheta S S' =
      (eigUp (relStep S' (S' - S)) 1 - eigUp (relStep S' (S' - S)) 0) / Real.pi := by
  have hP := relStep_isHermitian S' (hS'.isHermitian.sub hS.isHermitian)
  have hB : maternBd 2 = 1 / (2 * Real.pi) := by
    rw [maternBd]
    norm_num [Real.Gamma_one, Real.rpow_neg_one]
    ring
  rw [maternTheta_plane_eq S S' hP, eigUp_two hP, hB]
  simp
  field_simp
  ring

/-- **`prop:matern-negative-mass`(4)**, the step from `t²I` to `t² diag(1+ε, 1)`:
`𝓑₂Θ = ε/(π(1+ε))`. -/
theorem matern_negative_mass_plane_example (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    maternBd 2 * maternTheta (t ^ 2 • (1 : Mat 2)) (t ^ 2 • diagonal ![1 + ε, 1]) =
      ε / (Real.pi * (1 + ε)) := by
  set s : Fin 2 → ℝ := ![t * Real.sqrt (1 + ε), t] with hs
  set s' : Fin 2 → ℝ := ![t * Real.sqrt ε, 0] with hs'
  have hspos : ∀ i, 0 < s i := by
    intro i
    fin_cases i <;> simp [hs] <;> positivity
  have hS'eq : t ^ 2 • diagonal ![1 + ε, 1] = diagonal fun i => s i ^ 2 := by
    rw [← diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp [hs, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + ε)]
  have hdiff : t ^ 2 • diagonal ![1 + ε, 1] - t ^ 2 • (1 : Mat 2) =
      diagonal fun i => s' i ^ 2 := by
    rw [← diagonal_one, ← diagonal_smul, ← diagonal_smul, diagonal_sub]
    congr 1
    funext i
    fin_cases i <;> simp [hs', mul_pow, Real.sq_sqrt hε.le] <;> ring
  have hrel : relStep (t ^ 2 • diagonal ![1 + ε, 1])
      (t ^ 2 • diagonal ![1 + ε, 1] - t ^ 2 • (1 : Mat 2)) =
      diagonal ![ε / (1 + ε), 0] := by
    rw [hdiff, hS'eq, relStep_diagonal_sq hspos]
    congr 1
    funext i
    fin_cases i
    · simp [hs, hs', div_pow, mul_pow, Real.sq_sqrt hε.le,
        Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + ε)]
      field_simp
    · simp [hs, hs']
  have hP : (relStep (t ^ 2 • diagonal ![1 + ε, 1])
      (t ^ 2 • diagonal ![1 + ε, 1] - t ^ 2 • (1 : Mat 2))).IsHermitian := by
    rw [hrel]
    exact isHermitian_diagonal _
  have hB : maternBd 2 = 1 / (2 * Real.pi) := by
    rw [maternBd]
    norm_num [Real.Gamma_one, Real.rpow_neg_one]
    ring
  rw [maternTheta_plane_eq _ _ hP, hrel, hB, gap2]
  simp only [diagonal_apply_eq, diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide)]
  simp
  rw [Real.sqrt_sq (by positivity)]
  field_simp

end AffineHemigroup
