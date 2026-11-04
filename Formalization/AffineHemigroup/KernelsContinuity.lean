/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OperatorsKernels
import ScaleSpaceCore.L1ContinuitySpace
import AffineHemigroup.PositiveTransform

/-!
# `lem:kernels-to-operators`(1): continuity in `L¹` from the transforms, by Gaussian smoothing

Blueprint: `blueprint/src/parts/04-classical.tex`. Q-0281, wave M, phase 2.

The proof of record, step by step, without \Levy's continuity theorem:

* **the smoothing kernel** `γ_σ(x) = σ^{-d} γ(σ⁻¹ x)` (`gaussSigma`), a probability density;
* **its Fourier integral**: `e^{-b|z|²}` is a constant times `∫ e^{-|ω|²/(4b)} e^{-i⟨z,ω⟩} dω`
  (`exists_gauss_fourier`, from Mathlib's `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`),
  so by Fubini `(ν ∗ γ_σ)(x)` is a constant times `∫ e^{-σ²|ω|²/2} e^{-i⟨x,ω⟩} ν̂(ω) dω`
  (`exists_mconvE_gaussSigma_eq`), and dominated convergence gives `μ_n ∗ γ_σ → μ ∗ γ_σ`
  pointwise (`tendsto_mconvE_gaussSigma`);
* **Scheffé's argument** (`tendsto_integral_abs_sub_of_tendsto`) turns that into convergence in
  `L¹`, the densities being nonnegative with equal integrals;
* **the approximation** `‖γ_σ ∗ f - f‖₁ ≤ ∫ γ_σ(y) ‖T_y f - f‖₁ dy → 0` (`norm_bconvE_sub_le`,
  `tendsto_integral_gaussSigma_mul`), by the substitution `y = σ z` and dominated convergence;
* **the split** `μ_n ∗ f - μ ∗ f`, with `μ ∗ (γ_σ ∗ f) = (μ ∗ γ_σ) ∗ f` read through the
  commutativity of convolution and the interchange identity (`mconvL1E_bconvE`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology RealInnerProductSpace
open ScaleSpace (transL1E bconvE mconvL1E mconvE transDiffE)

variable {d : ℕ}

/-! ## Scheffé's argument -/

/-- **Scheffé.** Nonnegative integrable functions `h_n` with the integral of an integrable `h`,
converging to `h` almost everywhere, converge to it in `L¹`. -/
theorem tendsto_integral_abs_sub_of_tendsto {α : Type*} [MeasurableSpace α] {m : Measure α}
    {h : ℕ → α → ℝ} {h₀ : α → ℝ} (hint : ∀ n, Integrable (h n) m) (hint0 : Integrable h₀ m)
    (hnn : ∀ n x, 0 ≤ h n x) (hmass : ∀ n, ∫ x, h n x ∂m = ∫ x, h₀ x ∂m)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => h n x) atTop (𝓝 (h₀ x))) :
    Tendsto (fun n => ∫ x, |h n x - h₀ x| ∂m) atTop (𝓝 0) := by
  have hsplit : ∀ n, ∫ x, |h n x - h₀ x| ∂m = 2 * ∫ x, max (h₀ x - h n x) 0 ∂m := by
    intro n
    have hpt : ∀ x, |h n x - h₀ x| = (h n x - h₀ x) + 2 * max (h₀ x - h n x) 0 := by
      intro x
      rcases le_total (h n x) (h₀ x) with hle | hle
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
    simp_rw [hpt]
    rw [integral_add (f := fun x => h n x - h₀ x) (g := fun x => 2 * max (h₀ x - h n x) 0)
      ((hint n).sub hint0) (((hint0.sub (hint n)).pos_part).const_mul 2),
      integral_sub (hint n) hint0, hmass n, sub_self, zero_add, integral_const_mul]
  simp_rw [hsplit]
  have hlim0 : Tendsto (fun n => ∫ x, max (h₀ x - h n x) 0 ∂m) atTop
      (𝓝 (∫ x, max (h₀ x - h₀ x) 0 ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |h₀ x|)
      (fun n => (hint0.sub (hint n)).pos_part.aestronglyMeasurable) hint0.abs
      (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hnn n x, le_abs_self (h₀ x)]) (abs_nonneg _)
    · filter_upwards [hlim] with x hx
      exact ((tendsto_const_nhds.sub hx).max tendsto_const_nhds)
  simpa using hlim0.const_mul 2

/-! ## The smoothing kernel -/

/-- The standard Gaussian density has integral `1`. -/
theorem integral_gaussDensity : ∫ x, gaussDensity d x = 1 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd d) (b := 1 / 2) (by norm_num)
  rw [finrank_euclideanSpace_fin] at h
  simp only [gaussDensity]
  rw [integral_const_mul]
  have he : ∫ x : Rd d, Real.exp (-(‖x‖ ^ 2) / 2) = (2 * Real.pi) ^ ((d : ℝ) / 2) := by
    have h2 : Real.pi / (1 / 2) = 2 * Real.pi := by ring
    rw [← h2, ← h]
    congr 1; ext x; congr 1; ring
  rw [he, ← Real.rpow_add (by positivity), show -(d : ℝ) / 2 + d / 2 = 0 by ring, Real.rpow_zero]

/-- The standard Gaussian density is nonnegative. -/
theorem gaussDensity_nonneg (x : Rd d) : 0 ≤ gaussDensity d x := by
  unfold gaussDensity
  positivity

/-- `γ_σ(x) = σ^{-d} γ(σ⁻¹ x)`, the centred Gaussian density of covariance `σ² I`. -/
noncomputable def gaussSigma (d : ℕ) (σ : ℝ) (x : Rd d) : ℝ :=
  (σ ^ d)⁻¹ * gaussDensity d (σ⁻¹ • x)

/-- `γ_σ ≥ 0`. -/
theorem gaussSigma_nonneg {σ : ℝ} (hσ : 0 < σ) (x : Rd d) : 0 ≤ gaussSigma d σ x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hσ.le _)) (gaussDensity_nonneg _)

/-- `γ_σ` is integrable. -/
theorem integrable_gaussSigma {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussSigma d σ) :=
  ((integrable_gaussDensity d).comp_smul (inv_ne_zero hσ.ne')).const_mul _

/-- `∫ γ_σ = 1`, by the substitution `x = σ y`. -/
theorem integral_gaussSigma {σ : ℝ} (hσ : 0 < σ) : ∫ x, gaussSigma d σ x = 1 := by
  simp only [gaussSigma]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (gaussDensity d) hσ.le,
    finrank_euclideanSpace_fin, integral_gaussDensity, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_ne_zero _ hσ.ne')]

/-- The standard Gaussian density is continuous. -/
theorem continuous_gaussDensity : Continuous (gaussDensity d) := by
  unfold gaussDensity
  fun_prop

/-- `γ_σ` in the form its Fourier integral reads: `(σ^d)⁻¹ (2π)^{-d/2} e^{-|x|²/(2σ²)}`. -/
theorem gaussSigma_eq {σ : ℝ} (hσ : 0 < σ) (x : Rd d) :
    gaussSigma d σ x =
      (σ ^ d)⁻¹ * (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2) := by
  simp only [gaussSigma, gaussDensity, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hσ]
  rw [mul_assoc]
  congr 3
  field_simp

/-! ## The Fourier integral of a Gaussian, and of `ν ∗ γ_σ` -/

/-- **`e^{-b|z|²}` as a Fourier integral**: for `b > 0` there is a constant `K` with
`e^{-b|z|²} = K ∫ e^{-|ω|²/(4b)} e^{-i⟨z,ω⟩} dω` for every `z`. -/
theorem exists_gauss_fourier {b : ℝ} (hb : 0 < b) :
    ∃ K : ℂ, ∀ z : Rd d, ((Real.exp (-b * ‖z‖ ^ 2) : ℝ) : ℂ) =
      K * ∫ ω : Rd d, cexp (-((1 / (4 * b) : ℝ) : ℂ) * (‖ω‖ : ℂ) ^ 2 + (-I) * (⟪z, ω⟫ : ℂ)) := by
  have hb' : 0 < (((1 / (4 * b) : ℝ) : ℂ)).re := by
    rw [ofReal_re]; positivity
  set A : ℂ := (Real.pi / ((1 / (4 * b) : ℝ) : ℂ)) ^ (Module.finrank ℝ (Rd d) / 2 : ℂ) with hA
  have hA0 : A ≠ 0 := by
    intro h
    have h0 := ((Complex.cpow_eq_zero_iff _ _).mp h).1
    refine div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) ?_ h0
    exact ofReal_ne_zero.mpr (by positivity)
  refine ⟨A⁻¹, fun z => ?_⟩
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb' (-I) z, ← hA, ← mul_assoc,
    inv_mul_cancel₀ hA0, one_mul, ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **The Fourier integral of `ν ∗ γ_σ`**: there is a constant `C` with
`(ν ∗ γ_σ)(x) = C ∫ e^{-σ²|ω|²/2} e^{-i⟨x,ω⟩} ν̂(ω) dω` for every probability measure `ν` and
every `x`. -/
theorem exists_mconvE_gaussSigma_eq {σ : ℝ} (hσ : 0 < σ) :
    ∃ (C : ℂ) (F : Rd d → Rd d → ℂ), (∀ x ω, ‖F x ω‖ = Real.exp (-(σ ^ 2 / 2) * ‖ω‖ ^ 2)) ∧
      (∀ x, Continuous (F x)) ∧
      ∀ (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (x : Rd d),
        ((mconvE ν (gaussSigma d σ) x : ℝ) : ℂ) = C * ∫ ω, F x ω * charFun ν ω := by
  set b : ℝ := 1 / (2 * σ ^ 2) with hbdef
  have hb : 0 < b := by positivity
  obtain ⟨K, hK⟩ := exists_gauss_fourier (d := d) hb
  have hb4 : (1 / (4 * b) : ℝ) = σ ^ 2 / 2 := by rw [hbdef]; field_simp; ring
  set F : Rd d → Rd d → ℂ := fun x ω =>
    cexp (-((σ ^ 2 / 2 : ℝ) : ℂ) * (‖ω‖ : ℂ) ^ 2 + (-I) * (⟪x, ω⟫ : ℂ)) with hF
  set c : ℝ := (σ ^ d)⁻¹ * (2 * Real.pi) ^ (-(d : ℝ) / 2) with hc
  have hnormF : ∀ x ω, ‖F x ω‖ = Real.exp (-(σ ^ 2 / 2) * ‖ω‖ ^ 2) := by
    intro x ω
    have he : (-((σ ^ 2 / 2 : ℝ) : ℂ) * (‖ω‖ : ℂ) ^ 2 + (-I) * (⟪x, ω⟫ : ℂ))
        = ((-(σ ^ 2 / 2) * ‖ω‖ ^ 2 : ℝ) : ℂ) + ((-⟪x, ω⟫ : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hF]
    dsimp only
    rw [he, Complex.norm_exp, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hcontF : ∀ x, Continuous (F x) := fun x => by rw [hF]; fun_prop
  refine ⟨(c : ℂ) * K, F, hnormF, hcontF, fun ν _ x => ?_⟩
  -- the kernel at `x - y`, as the Fourier integral, and the factorization of the integrand
  have hpt : ∀ y : Rd d, ((gaussSigma d σ (x - y) : ℝ) : ℂ) =
      (c : ℂ) * K * ∫ ω, F x ω * cexp (⟪y, ω⟫ * I) := by
    intro y
    rw [gaussSigma_eq hσ, ofReal_mul, hK (x - y), hb4, ← mul_assoc]
    congr 2
    ext ω
    simp only [hF]
    rw [← Complex.exp_add, inner_sub_left]
    congr 1
    push_cast
    ring
  have hint : Integrable (Function.uncurry fun (y ω : Rd d) => F x ω * cexp (⟪y, ω⟫ * I))
      (ν.prod volume) := by
    have hbound : Integrable (fun p : Rd d × Rd d => (1 : ℝ) * Real.exp (-(σ ^ 2 / 2) * ‖p.2‖ ^ 2))
        (ν.prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod (integrable_rexp_neg_mul_sq_norm_Rd d (by positivity))
    refine hbound.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by
        change Continuous fun p : Rd d × Rd d => F x p.2 * cexp (⟪p.1, p.2⟫ * I)
        rw [hF]; fun_prop))
    · change ‖F x p.2 * cexp (⟪p.1, p.2⟫ * I)‖ ≤ 1 * Real.exp (-(σ ^ 2 / 2) * ‖p.2‖ ^ 2)
      rw [norm_mul, hnormF, Complex.norm_exp_ofReal_mul_I, mul_one, one_mul]
  rw [ScaleSpace.mconvE_apply, ← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  change ∫ y, F x ω * cexp (⟪y, ω⟫ * I) ∂ν = F x ω * charFun ν ω
  rw [integral_const_mul, charFun_apply]

/-- **`ν_n ∗ γ_σ → ν ∗ γ_σ` pointwise** when the transforms converge pointwise. -/
theorem tendsto_mconvE_gaussSigma {σ : ℝ} (hσ : 0 < σ) (μn : ℕ → Measure (Rd d))
    [∀ n, IsProbabilityMeasure (μn n)] (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (h : ∀ ω : Rd d, Tendsto (fun n => charFun (μn n) ω) atTop (𝓝 (charFun μ ω)))
    (x : Rd d) :
    Tendsto (fun n => mconvE (μn n) (gaussSigma d σ) x) atTop
      (𝓝 (mconvE μ (gaussSigma d σ) x)) := by
  obtain ⟨C, F, hnormF, hcontF, hrepr⟩ := exists_mconvE_gaussSigma_eq (d := d) hσ
  have hc : Tendsto (fun n => ((mconvE (μn n) (gaussSigma d σ) x : ℝ) : ℂ)) atTop
      (𝓝 ((mconvE μ (gaussSigma d σ) x : ℝ) : ℂ)) := by
    simp only [hrepr]
    refine Tendsto.const_mul C ?_
    refine tendsto_integral_of_dominated_convergence
      (fun ω => Real.exp (-(σ ^ 2 / 2) * ‖ω‖ ^ 2)) (fun n => ?_) ?_
      (fun n => Filter.Eventually.of_forall fun ω => ?_) ?_
    · exact ((hcontF x).aestronglyMeasurable.mul
        (continuous_charFun (μ := μn n)).aestronglyMeasurable)
    · exact integrable_rexp_neg_mul_sq_norm_Rd d (by positivity)
    · rw [norm_mul, hnormF]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_charFun_le_one _)
    · exact Filter.Eventually.of_forall fun ω => (h ω).const_mul (F x ω)
  have := (Complex.continuous_re.tendsto _).comp hc
  simpa [Function.comp_def] using this

/-! ## The approximation `γ_σ ∗ f → f` -/

/-- **`‖g ∗ f - f‖₁ ≤ ∫ g(y) ‖T_y f - f‖₁ dy`** for a probability density `g`. -/
theorem norm_bconvE_sub_le {g : Rd d → ℝ} (hg : Integrable g) (hgnn : ∀ y, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (f : L1 d) :
    ‖bconvE g f - f‖ ≤ ∫ y, g y * transDiffE f y := by
  have hsub : bconvE g f - f = ∫ y, g y • (transL1E y f - f) := by
    simp only [smul_sub]
    rw [integral_sub (ScaleSpace.integrable_smul_transL1E hg f) (hg.smul_const f),
      integral_smul_const, hg1, one_smul, bconvE]
  rw [hsub]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ‖g y • (transL1E y f - f)‖ = g y * transDiffE f y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgnn y)]
  rfl

/-- **`∫ γ_σ(y) D(y) dy → 0` as `σ → 0`** for a bounded continuous `D` vanishing at `0`: the
substitution `y = σ z` and dominated convergence. -/
theorem tendsto_integral_gaussSigma_mul {D : Rd d → ℝ} (hD : Continuous D) {M : ℝ}
    (hM : ∀ y, |D y| ≤ M) (hD0 : D 0 = 0) :
    Tendsto (fun σ => ∫ y, gaussSigma d σ y * D y) (𝓝[>] 0) (𝓝 0) := by
  have hsub : ∀ σ : ℝ, 0 < σ →
      ∫ y, gaussSigma d σ y * D y = ∫ z, gaussDensity d z * D (σ • z) := by
    intro σ hσ
    have := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z : Rd d => gaussDensity d z * D (σ • z)) hσ.le
    rw [finrank_euclideanSpace_fin] at this
    simp only [gaussSigma, mul_assoc]
    rw [integral_const_mul]
    have hcongr : ∫ y : Rd d, gaussDensity d (σ⁻¹ • y) * D y
        = ∫ y : Rd d, gaussDensity d (σ⁻¹ • y) * D (σ • σ⁻¹ • y) := by
      congr 1; ext y; rw [smul_inv_smul₀ hσ.ne']
    rw [hcongr, this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hσ.ne'), one_mul]
  have hlim : Tendsto (fun σ : ℝ => ∫ z, gaussDensity d z * D (σ • z)) (𝓝[>] 0)
      (𝓝 (∫ z, gaussDensity d z * D ((0 : ℝ) • z))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => gaussDensity d z * M)
      (Filter.Eventually.of_forall fun σ => ?_) (Filter.Eventually.of_forall fun σ =>
        Filter.Eventually.of_forall fun z => ?_) ((integrable_gaussDensity d).mul_const M) ?_
    · exact (continuous_gaussDensity.mul (hD.comp (continuous_const.smul continuous_id)))
        |>.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussDensity_nonneg z), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM _) (gaussDensity_nonneg z)
    · refine Filter.Eventually.of_forall fun z => Tendsto.const_mul _ ?_
      exact ((hD.comp (continuous_id.smul continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
  simp only [zero_smul, hD0, mul_zero, integral_zero] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun σ hσ => (hsub σ hσ).symm)

/-! ## The assembly -/

/-- **`μ ∗ (f ⋆ u) = f ⋆ (μ ∗ u)`**: convolution by a measure passes through `bconvE`. -/
theorem mconvL1E_bconvE (μ : Measure (Rd d)) [IsFiniteMeasure μ] {f : Rd d → ℝ}
    (hf : Integrable f) (u : L1 d) :
    mconvL1E μ (bconvE f u) = bconvE f (mconvL1E μ u) :=
  ScaleSpace.map_bconvE (mconvL1E μ) (fun a g => ScaleSpace.mconvL1E_transL1E μ a g) hf u

/-- The `L¹` distance of `μ_n ∗ γ_σ` from `μ ∗ γ_σ` tends to `0`. -/
theorem tendsto_norm_mconvL1E_gaussSigma {σ : ℝ} (hσ : 0 < σ) (μn : ℕ → Measure (Rd d))
    [∀ n, IsProbabilityMeasure (μn n)] (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (h : ∀ ω : Rd d, Tendsto (fun n => charFun (μn n) ω) atTop (𝓝 (charFun μ ω))) :
    Tendsto (fun n => ‖mconvL1E (μn n) ((integrable_gaussSigma hσ).toL1 (gaussSigma d σ)) -
      mconvL1E μ ((integrable_gaussSigma hσ).toL1 (gaussSigma d σ))‖) atTop (𝓝 0) := by
  set g := gaussSigma d σ with hgdef
  have hg := integrable_gaussSigma (d := d) hσ
  have hgm : AEStronglyMeasurable g := hg.aestronglyMeasurable
  have hnorm : ∀ ν : Measure (Rd d), ∀ _ : IsProbabilityMeasure ν,
      ((mconvL1E ν (hg.toL1 g) : L1 d) : Rd d → ℝ) =ᵐ[volume] mconvE ν g := fun ν _ =>
    (ScaleSpace.coeFn_mconvL1E ν _).trans (ScaleSpace.mconvE_congr_ae ν (Integrable.coeFn_toL1 hg))
  have heq : ∀ n, ‖mconvL1E (μn n) (hg.toL1 g) - mconvL1E μ (hg.toL1 g)‖
      = ∫ x, |mconvE (μn n) g x - mconvE μ g x| := by
    intro n
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (mconvL1E (μn n) (hg.toL1 g)) (mconvL1E μ (hg.toL1 g)),
      hnorm (μn n) inferInstance, hnorm μ inferInstance] with x hx h1 h2
    rw [hx, Pi.sub_apply, h1, h2, Real.norm_eq_abs]
  refine Tendsto.congr (fun n => (heq n).symm) ?_
  refine tendsto_integral_abs_sub_of_tendsto (fun n => ScaleSpace.integrable_mconvE _ hgm hg)
    (ScaleSpace.integrable_mconvE _ hgm hg) (fun n x => ?_) (fun n => ?_)
    (Filter.Eventually.of_forall (tendsto_mconvE_gaussSigma hσ μn μ h))
  · exact integral_nonneg fun y => gaussSigma_nonneg hσ _
  · rw [ScaleSpace.integral_mconvE _ hgm hg, ScaleSpace.integral_mconvE _ hgm hg, measure_univ,
      measure_univ]

/-- **`lem:kernels-to-operators`(1)**, continuity: `μ̂_n(ω) → μ̂(ω)` for every `ω` gives
`μ_n ∗ f → μ ∗ f` in `L¹(ℝ^d)` for every `f ∈ L¹(ℝ^d)`. -/
theorem kernels_to_operators_continuity (_hd : 1 ≤ d) (μn : ℕ → Measure (Rd d))
    [∀ n, IsProbabilityMeasure (μn n)] (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (h : ∀ ω : Rd d, Tendsto (fun n => charFun (μn n) ω) atTop (𝓝 (charFun μ ω)))
    (f : L1 d) :
    Tendsto (fun n => mconvL1E (μn n) f) atTop (𝓝 (mconvL1E μ f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `σ` with `‖γ_σ ∗ f - f‖₁ < ε / 4`
  have hD := ScaleSpace.continuous_transDiffE f
  have happ := tendsto_integral_gaussSigma_mul (d := d) hD
    (fun y => by rw [abs_of_nonneg (ScaleSpace.transDiffE_nonneg f y)];
                 exact ScaleSpace.transDiffE_le f y)
    (ScaleSpace.transDiffE_zero f)
  have hev := (happ.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
  obtain ⟨σ, hσε, hσ'⟩ := hev.exists
  have hσ : 0 < σ := hσ'
  have hg := integrable_gaussSigma (d := d) hσ
  set A : L1 d := bconvE (gaussSigma d σ) f with hA
  have hAf : ‖A - f‖ < ε / 4 :=
    (norm_bconvE_sub_le hg (gaussSigma_nonneg hσ) (integral_gaussSigma hσ) f).trans_lt hσε
  -- `μ ∗ A = f ⋆ (μ ∗ γ_σ)`
  have hfi : Integrable ((f : Rd d → ℝ)) := L1.integrable_coeFn f
  have hAc : A = bconvE (f : Rd d → ℝ) (hg.toL1 (gaussSigma d σ)) := by
    rw [hA, bconvE_comm hg f]
  set C : ℝ := ∫ y, ‖(f : Rd d → ℝ) y‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hconv := tendsto_norm_mconvL1E_gaussSigma hσ μn μ h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / (4 * (C + 1))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hNn
  have hmid : ‖mconvL1E (μn n) A - mconvL1E μ A‖ < ε / 4 := by
    rw [hAc, mconvL1E_bconvE _ hfi, mconvL1E_bconvE _ hfi, ← bconvE_sub hfi]
    refine (norm_bconvE_le hfi _).trans_lt ?_
    calc C * ‖mconvL1E (μn n) (hg.toL1 (gaussSigma d σ)) - mconvL1E μ (hg.toL1 (gaussSigma d σ))‖
        ≤ (C + 1) * ‖mconvL1E (μn n) (hg.toL1 (gaussSigma d σ)) -
            mconvL1E μ (hg.toL1 (gaussSigma d σ))‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C + 1) * (ε / (4 * (C + 1))) := mul_lt_mul_of_pos_left hNn (by linarith)
      _ = ε / 4 := by field_simp
  have h1 : ‖mconvL1E (μn n) f - mconvL1E (μn n) A‖ < ε / 4 := by
    rw [← map_sub]
    exact (ScaleSpace.norm_mconvL1E_le _ _).trans_lt (by rw [norm_sub_rev]; exact hAf)
  have h3 : ‖mconvL1E μ A - mconvL1E μ f‖ < ε / 4 := by
    rw [← map_sub]
    exact (ScaleSpace.norm_mconvL1E_le _ _).trans_lt hAf
  rw [dist_eq_norm]
  calc ‖mconvL1E (μn n) f - mconvL1E μ f‖
      = ‖(mconvL1E (μn n) f - mconvL1E (μn n) A) + (mconvL1E (μn n) A - mconvL1E μ A)
          + (mconvL1E μ A - mconvL1E μ f)‖ := by congr 1; abel
    _ ≤ ‖mconvL1E (μn n) f - mconvL1E (μn n) A‖ + ‖mconvL1E (μn n) A - mconvL1E μ A‖
          + ‖mconvL1E μ A - mconvL1E μ f‖ := norm_add₃_le
    _ < ε / 4 + ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith

end AffineHemigroup
