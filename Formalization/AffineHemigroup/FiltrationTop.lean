/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces
import AffineHemigroup.LevyKhintchineNegDef
import AffineHemigroup.BernsteinUnique
import AffineHemigroup.PolarClassification
import AffineHemigroup.Subordinated
import AffineHemigroup.DelayPolar
import AffineHemigroup.OriginExponent
import ScaleSpaceCore.AnalysisDirection
import ScaleSpaceCore.SDExponents
import ScaleSpaceCore.SDProfile
import ScaleSpaceCore.BridgeExponents

/-!
# `lem:filtration-top`: the top of the filtration is the subordinated slice, `𝒜_∞ = 𝒮`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:filtration-top` ([B, Prop. 4.9(4)],
restated), Q-0281 wave N; its tag also closes `thm:filtration-strict`, whose fourth declaration is
`filtration_top`. Ledger: A10 (`schoenberg_radial_bernstein`), admitted by the author on 2026-10-07,
and A2–A4 through the polar reading.

## `𝒮 ⊆ 𝒜_∞` (`classAInf_of_classS`)

For `F = F_I(·²/2)` with `F_I = (b₀, k_I)` causally admissible and `d ≥ 1`: `F` is admissible by
[B, Lem. 4.2] (the shared library's `ScaleSpace.bridge_exponents`; Lean core); the
polar profile `k_d` is nonincreasing (`polarProfileOf_antitone`), so `lem:delay-polar-profile`
makes `(b₀, k_d)` an origin datum with exponent `F(|·|)`, and the converse direction of `prop:isotropic-polar-reading`(1) gives the
self-decomposable law (A2, A3(iii)).

## `𝒜_∞ ⊆ 𝒮` (`classS_of_classAInf`)

Put `f(σ) = F(√(2σ))` and `g_c(σ) = f(σ) - f(c²σ)`, `0 < c ≤ 1`.

1. In each `d ≥ 1` the forward polar reading (A2–A4) writes `F(|η|) = F_d(η)` for an origin datum
   `(a_d, k_d)`; the image of its Lévy measure under `x ↦ cx` is below it
   (`OriginDatum.map_smul_levyMeasure_le`), so `lem:lk-negative-definite` makes `ξ ↦ f(|ξ|²)` and
   `ξ ↦ g_c(|ξ|²)` negative definite (`radial_negDef_of_lk`); at `d = 0` both vanish.
2. A10 gives `f(σ) = a + bσ + ∫ (1 - e^{-σt}) m(dt)` and the same for each `g_c`.
3. `a = 0`, since `a ≤ f(σ) → F(0) = 0`.
4. `f(σ) = f(c²σ) + g_c(σ)` and `lem:bernstein-triplet-unique` give `m = D_{c²} m + m_c`, so
   `D_λ m ≤ m` for every `λ ∈ (0,1]`.
5. `lem:dilation-decreasing-profile` (`ScaleSpace.exists_profile_of_dilate_le`) gives
   `m(dt) = k(t) dt/t`, `k ≥ 0` nonincreasing; the windows of `(b, k)` are bounded by
   `∫ (1 ∧ t) m(dt)`, so `(b, k)` is causally admissible, and its exponent is `f` on `(0,∞)`.

[B]'s own proof of Prop. 4.9(4) spends six cited facts; this one spends A10 and the polar reading.
The infinite divisibility of the residual (Sato Prop. 15.5, second clause), the complete
monotonicity of `e^{-f}` with Bernstein's theorem, and the half-line characterization of
self-decomposable laws are not used.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-! ## Radial functions -/

/-- `ℝ⁰` is a point. -/
theorem norm_eq_zero_rd0 (x : Rd 0) : ‖x‖ = 0 := by
  simp [EuclideanSpace.norm_eq]

/-- **The hypothesis of ledger A10, from Lévy–Khintchine data in every positive dimension**: if
`h(0) = 0`, `ξ ↦ h(|ξ|²)` is continuous on every `ℝ^d`, and for `d ≥ 1`
`h(|ξ|²) = (ψ - ψ')(√2 ξ)` for two Lévy–Khintchine forms as in `lkForm_sub_negDef`, then
`ξ ↦ h(|ξ|²)` is continuous and negative definite on `ℝ^d` for every `d : ℕ` (at `d = 0` every
term vanishes). -/
theorem radial_negDef_of_lk (h : ℝ → ℝ) (h0 : h 0 = 0)
    (hcont : ∀ d : ℕ, Continuous fun ξ : Rd d => h (‖ξ‖ ^ 2))
    (hlk : ∀ d : ℕ, 1 ≤ d → ∃ (α α' : ℝ) (L L' : Measure (Rd d)), L' ≤ L ∧ α' ≤ α ∧
      (∀ η, levyExpL L η ≠ ⊤) ∧
        ∀ ξ : Rd d, h (‖ξ‖ ^ 2) = lkForm α L (Real.sqrt 2 • ξ) - lkForm α' L' (Real.sqrt 2 • ξ)) :
    ∀ d : ℕ, Continuous (fun ξ : Rd d => h (‖ξ‖ ^ 2)) ∧
      ∀ (n : ℕ) (ξ : Fin n → Rd d) (c : Fin n → ℂ),
        0 ≤ ∑ j, ∑ k, (((h (‖ξ j‖ ^ 2) + h (‖ξ k‖ ^ 2) - h (‖ξ j - ξ k‖ ^ 2) : ℝ) : ℂ) *
          c j * starRingEnd ℂ (c k)) := by
  intro d
  refine ⟨hcont d, fun n ξ c => ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [norm_eq_zero_rd0, h0]
  · obtain ⟨α, α', L, L', hL, hα, hfin, hh⟩ := hlk d hd
    have e : ∀ j k, h (‖ξ j‖ ^ 2) + h (‖ξ k‖ ^ 2) - h (‖ξ j - ξ k‖ ^ 2) =
        (lkForm α L (Real.sqrt 2 • ξ j) - lkForm α' L' (Real.sqrt 2 • ξ j)) +
          (lkForm α L (Real.sqrt 2 • ξ k) - lkForm α' L' (Real.sqrt 2 • ξ k)) -
            (lkForm α L (Real.sqrt 2 • ξ j - Real.sqrt 2 • ξ k) -
              lkForm α' L' (Real.sqrt 2 • ξ j - Real.sqrt 2 • ξ k)) := by
      intro j k
      rw [hh, hh, hh, smul_sub]
    simp_rw [e]
    exact lkForm_sub_negDef hL hα hfin (fun j => Real.sqrt 2 • ξ j) c

/-- A radial negative definite function vanishing at `0` is nonnegative: the case `n = 1` reads
`2h(σ) - h(0) ≥ 0`. -/
theorem nonneg_of_radial_negDef (h : ℝ → ℝ) (h0 : h 0 = 0)
    (hnd : ∀ (n : ℕ) (ξ : Fin n → Rd 1) (c : Fin n → ℂ),
      0 ≤ ∑ j, ∑ k, (((h (‖ξ j‖ ^ 2) + h (‖ξ k‖ ^ 2) - h (‖ξ j - ξ k‖ ^ 2) : ℝ) : ℂ) *
        c j * starRingEnd ℂ (c k))) {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ h σ := by
  set ξ : Rd 1 := EuclideanSpace.single 0 (Real.sqrt σ) with hξ
  have hn : ‖ξ‖ ^ 2 = σ := by
    rw [hξ, PiLp.norm_single, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hσ]
  have := hnd 1 ![ξ] ![1]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
    Finset.sum_singleton, sub_self, norm_zero, hn, map_one, mul_one] at this
  have h2 := Complex.zero_le_real.mp this
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, h0] at h2
  linarith

/-! ## The Lévy measure of an origin datum decreases under dilation -/

/-- **The Lévy measure of an origin datum decreases under dilation**: for `0 < c ≤ 1`, the image
of `ν_d` under `x ↦ cx` has density `k_d(|x|/c)/(|S^{d-1}||x|^d) ≤ k_d(|x|)/(|S^{d-1}||x|^d)`, the
profile being nonincreasing. -/
theorem OriginDatum.map_smul_levyMeasure_le (hd : 1 ≤ d) (D : OriginDatum d) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Measure.map (fun x : Rd d => c • x) D.levyMeasure ≤ D.levyMeasure := by
  have hA := (sphereArea_eq_toSphere hd).2
  set ρ : Rd d → ℝ≥0∞ := fun x => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x with hρ
  have hρm : Measurable ρ := D.measurable_levyDensity
  have hsm : Measurable fun x : Rd d => c • x := measurable_const_smul c
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.map_apply hsm hs, OriginDatum.levyMeasure, withDensity_apply _ (hsm hs),
    withDensity_apply _ hs]
  have hcd : (0 : ℝ) < c ^ d := pow_pos hc0 d
  have hpt : ∀ y : Rd d, ENNReal.ofReal |(c ^ Module.finrank ℝ (Rd d))⁻¹| * ρ (c⁻¹ • y) ≤ ρ y := by
    intro y
    rw [finrank_Rd, abs_of_pos (inv_pos.mpr hcd)]
    by_cases hy : y = 0
    · subst hy
      simp [hρ]
    · have hy' : c⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hc0.ne') hy
      have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      rw [hρ]
      simp only
      rw [indicator_of_mem (show c⁻¹ • y ∈ ({0}ᶜ : Set (Rd d)) from hy'),
        indicator_of_mem (show y ∈ ({0}ᶜ : Set (Rd d)) from hy),
        ← ENNReal.ofReal_mul (by positivity),
        norm_smul, Real.norm_of_nonneg (inv_pos.mpr hc0).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : ‖y‖ ≤ c⁻¹ * ‖y‖ := le_mul_of_one_le_left hn.le (one_le_inv_iff₀.mpr ⟨hc0, hc1⟩)
      have hk := D.k_antitone (show ‖y‖ ∈ Ioi (0 : ℝ) from hn)
        (show c⁻¹ * ‖y‖ ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.mpr hc0) hn) hle
      calc (c ^ d)⁻¹ * (D.k (c⁻¹ * ‖y‖) / (sphereArea d * (c⁻¹ * ‖y‖) ^ d))
          = D.k (c⁻¹ * ‖y‖) / (sphereArea d * ‖y‖ ^ d) := by
            rw [mul_pow, inv_pow]
            field_simp
        _ ≤ D.k ‖y‖ / (sphereArea d * ‖y‖ ^ d) :=
            div_le_div_of_nonneg_right hk (by positivity)
  calc ∫⁻ x in (fun x : Rd d => c • x) ⁻¹' s, ρ x
      = ∫⁻ x, s.indicator (fun y => ρ (c⁻¹ • y)) (c • x) := by
        rw [← lintegral_indicator (hsm hs)]
        refine lintegral_congr fun x => ?_
        by_cases hx : c • x ∈ s
        · rw [indicator_of_mem (show x ∈ (fun x : Rd d => c • x) ⁻¹' s from hx),
            indicator_of_mem hx, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
        · rw [indicator_of_notMem (show x ∉ (fun x : Rd d => c • x) ⁻¹' s from hx),
            indicator_of_notMem hx]
    _ = ∫⁻ y, s.indicator (fun y => ρ (c⁻¹ • y)) y
          ∂(Measure.map (fun x : Rd d => c • x) volume) := by
        exact (lintegral_map (f := s.indicator fun y => ρ (c⁻¹ • y))
          ((hρm.comp (measurable_const_smul _)).indicator hs) hsm).symm
    _ = ∫⁻ y in s, ENNReal.ofReal |(c ^ Module.finrank ℝ (Rd d))⁻¹| * ρ (c⁻¹ • y) := by
        rw [Measure.map_addHaar_smul _ hc0.ne', lintegral_smul_measure,
          lintegral_indicator hs, smul_eq_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y in s, ρ y := lintegral_mono fun y => hpt y

/-- `∫ (1 - cos⟨η,y⟩) ((c·)_* L)(dy) = ∫ (1 - cos⟨cη,x⟩) L(dx)`. -/
theorem levyExpL_map_smul (L : Measure (Rd d)) (c : ℝ) (η : Rd d) :
    levyExpL (Measure.map (fun x : Rd d => c • x) L) η = levyExpL L (c • η) := by
  unfold levyExpL
  rw [lintegral_map (by fun_prop) (measurable_const_smul c)]
  simp only [real_inner_smul_left, real_inner_smul_right]

/-- The exponent of an origin datum is the Lévy–Khintchine form `lkForm (a/2) ν_d`. -/
theorem OriginDatum.exponent_eq_lkForm (hd : 1 ≤ d) (D : OriginDatum d) (η : Rd d) :
    D.exponent η = lkForm (D.a / 2) D.levyMeasure η := by
  have hfin := ENNReal.add_ne_top.mp (D.exponentL_ne_top hd η)
  rw [OriginDatum.exponent, OriginDatum.exponentL, ENNReal.toReal_add hfin.1 hfin.2,
    ENNReal.toReal_ofReal (by have := D.a_nonneg; positivity), lkForm]
  unfold levyExpL
  ring

/-- `F_d(cη)` is the Lévy–Khintchine form with `α = ac²/2` and the image of `ν_d` under
`x ↦ cx`. -/
theorem OriginDatum.exponent_smul_eq_lkForm (hd : 1 ≤ d) (D : OriginDatum d) (c : ℝ) (η : Rd d) :
    D.exponent (c • η) =
      lkForm (D.a * c ^ 2 / 2) (Measure.map (fun x : Rd d => c • x) D.levyMeasure) η := by
  rw [D.exponent_eq_lkForm hd, lkForm, lkForm, levyExpL_map_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

/-- The jump part of `F_d` is finite. -/
theorem OriginDatum.levyExpL_ne_top (hd : 1 ≤ d) (D : OriginDatum d) (η : Rd d) :
    levyExpL D.levyMeasure η ≠ ⊤ :=
  (ENNReal.add_ne_top.mp (D.exponentL_ne_top hd η)).2

/-! ## The inclusion `𝒮 ⊆ 𝒜_∞` -/

/-- **[B, Prop. 4.9(2)]'s monotonicity**: the polar profile of a causally admissible delay datum
is nonincreasing on `(0,∞)`, `k_I(r²/2v) ≥ k_I(s²/2v)` for `r ≤ s` under the integral of
`eq:polar-profile-d`. -/
theorem polarProfileOf_antitone (hd : 1 ≤ d) (FI : ScaleSpace.CausalAdmissible) :
    AntitoneOn (polarProfileOf FI.k d) (Ioi 0) := by
  intro r hr s hs hrs
  have hr0 : (0 : ℝ) < r := hr
  have hs0 : (0 : ℝ) < s := hs
  have hint := (delay_polar_profile (d := d) hd (causalDelayDatum FI)).1
  have hG : 0 < 2 / Real.Gamma ((d : ℝ) / 2) :=
    div_pos two_pos (Real.Gamma_pos_of_pos (by positivity))
  refine mul_le_mul_of_nonneg_left ?_ hG.le
  refine setIntegral_mono_on (hint s hs) (hint r hr) measurableSet_Ioi fun v (hv : 0 < v) => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact FI.k_antitone (show r ^ 2 / (2 * v) ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; positivity)
    (show s ^ 2 / (2 * v) ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; positivity)
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hr0.le hrs 2) (by positivity))

/-- **`lem:filtration-top`, `𝒮 ⊆ 𝒜_∞`**: admissibility by [B, Lem. 4.2] (the shared library's
`bridge_exponents`, Lean core), the law by `lem:delay-polar-profile` and the converse direction
of `prop:isotropic-polar-reading`(1) (A2, A3(iii)). -/
theorem classAInf_of_classS (F : ℝ → ℝ) (hF : classS F) : classAInf F := by
  obtain ⟨FI, hFI⟩ := hF
  intro d hd
  obtain ⟨Q, -, -, hQ⟩ := ScaleSpace.bridge_exponents FI
  obtain ⟨O, -, -, hO⟩ := delay_polar_profile_datum hd (causalDelayDatum FI)
    (polarProfileOf_antitone hd FI)
  obtain ⟨μ, hprob, hsd, -, hchar⟩ := polar_reading_converse hd O
  refine ⟨⟨Q, fun r hr => by rw [hFI r hr, hQ]⟩, μ, hprob, hsd, fun ξ => ?_⟩
  rw [hchar ξ, hFI _ (norm_nonneg ξ)]
  congr 3
  rw [OriginDatum.exponent, hO ξ, causalDelayDatum_exponentL]
  rfl

/-! ## The inclusion `𝒜_∞ ⊆ 𝒮` -/

/-- A dilation by `c > 0` keeps a measure carried by `(0,∞)` there. -/
theorem map_mul_Iic_eq_zero {m : Measure ℝ} (hm : m (Iic 0) = 0) {c : ℝ} (hc : 0 < c) :
    (Measure.map (fun t : ℝ => c * t) m) (Iic 0) = 0 := by
  rw [Measure.map_apply (measurable_const_mul c) measurableSet_Iic]
  refine measure_mono_null (fun t ht => ?_) hm
  simp only [mem_preimage, mem_Iic] at ht ⊢
  nlinarith

/-- `∫ (1 - e^{-σt}) (D_c m)(dt) = ∫ (1 - e^{-cσt}) m(dt)`. -/
theorem lintegral_one_sub_exp_map (m : Measure ℝ) (c σ : ℝ) :
    ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂(Measure.map (fun t : ℝ => c * t) m) =
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-((c * σ) * t))) ∂m := by
  rw [lintegral_map (by fun_prop) (measurable_const_mul c)]
  refine lintegral_congr fun t => ?_
  ring_nf

/-- **`lem:filtration-top`, `𝒜_∞ ⊆ 𝒮`**: the radial theorem (A10) twice, for `f = F(√(2·))`
and for `f - f(c²·)`, whose hypotheses are `lem:lk-negative-definite` applied to the polar reading
(A2–A4); then `lem:bernstein-triplet-unique` makes the Lévy measure `m` of `f` decrease under
dilation, and `lem:dilation-decreasing-profile` (`ScaleSpace.exists_profile_of_dilate_le`) gives
it the profile of a causally admissible exponent. -/
theorem classS_of_classAInf (F : ℝ → ℝ) (hF : classAInf F) : classS F := by
  obtain ⟨⟨P, hP⟩, -⟩ := hF 1 le_rfl
  have hFnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := fun r hr => by
    rw [hP r hr]; exact ENNReal.toReal_nonneg
  have hF0 : F 0 = 0 := by
    rw [hP 0 le_rfl]
    simp [ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponentL]
  have hdat : ∀ d : ℕ, 1 ≤ d → ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ := by
    intro d hd
    obtain ⟨-, μ, hprob, hsd, hchar⟩ := hF d hd
    haveI := hprob
    exact polar_reading_forward hd F hFnn μ hsd hchar
  set f : ℝ → ℝ := fun σ => F (Real.sqrt (2 * σ)) with hf
  have hf0 : f 0 = 0 := by simp [hf, hF0]
  have hfnn : ∀ σ : ℝ, 0 ≤ f σ := fun σ => hFnn _ (Real.sqrt_nonneg _)
  have hfP : ∀ σ : ℝ, f σ = P.exponent (Real.sqrt (2 * σ)) := fun σ => hP _ (Real.sqrt_nonneg _)
  have hfc : Continuous f := by
    rw [show f = fun σ => P.exponent (Real.sqrt (2 * σ)) from funext hfP]
    exact P.continuous_exponent.comp (by fun_prop)
  -- the radial values through a datum
  have hrad : ∀ (d : ℕ) (D : OriginDatum d), (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) →
      ∀ c : ℝ, 0 ≤ c → ∀ ξ : Rd d, f (c ^ 2 * ‖ξ‖ ^ 2) = D.exponent (c • (Real.sqrt 2 • ξ)) := by
    intro d D hD c hc ξ
    rw [← hD, norm_smul, norm_smul, Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
    change F (Real.sqrt (2 * (c ^ 2 * ‖ξ‖ ^ 2))) = F (c * (Real.sqrt 2 * ‖ξ‖))
    congr 1
    rw [show 2 * (c ^ 2 * ‖ξ‖ ^ 2) = (c * (Real.sqrt 2 * ‖ξ‖)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring]
    exact Real.sqrt_sq (by positivity)
  have hcont : ∀ (c : ℝ) (d : ℕ), Continuous fun ξ : Rd d => f (c ^ 2 * ‖ξ‖ ^ 2) :=
    fun c d => hfc.comp (by fun_prop)
  have hcont1 : ∀ d : ℕ, Continuous fun ξ : Rd d => f (‖ξ‖ ^ 2) := fun d => by
    simpa using hcont 1 d
  -- Step 1: `f` and `g_c` are continuous and negative definite in every dimension
  have hfnd := radial_negDef_of_lk f hf0 hcont1 fun d hd => by
    obtain ⟨D, hD⟩ := hdat d hd
    refine ⟨D.a / 2, 0, D.levyMeasure, 0, Measure.zero_le _, by linarith [D.a_nonneg],
      D.levyExpL_ne_top hd, fun ξ => ?_⟩
    rw [lkForm_zero_measure, sub_zero, ← D.exponent_eq_lkForm hd]
    simpa using hrad d D hD 1 zero_le_one ξ
  set g : ℝ → ℝ → ℝ := fun c σ => f σ - f (c ^ 2 * σ) with hg
  have hgnd : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ d : ℕ, Continuous (fun ξ : Rd d => g c (‖ξ‖ ^ 2)) ∧
      ∀ (n : ℕ) (ξ : Fin n → Rd d) (z : Fin n → ℂ),
        0 ≤ ∑ j, ∑ k, (((g c (‖ξ j‖ ^ 2) + g c (‖ξ k‖ ^ 2) - g c (‖ξ j - ξ k‖ ^ 2) : ℝ) : ℂ) *
          z j * starRingEnd ℂ (z k)) := by
    intro c hc0 hc1
    refine radial_negDef_of_lk (g c) (by simp [hg, hf0]) (fun d => (hcont1 d).sub (hcont c d))
      fun d hd => ?_
    obtain ⟨D, hD⟩ := hdat d hd
    refine ⟨D.a / 2, D.a * c ^ 2 / 2, D.levyMeasure,
      Measure.map (fun x : Rd d => c • x) D.levyMeasure, D.map_smul_levyMeasure_le hd hc0 hc1,
      ?_, D.levyExpL_ne_top hd, fun ξ => ?_⟩
    · have : c ^ 2 ≤ 1 := by nlinarith
      nlinarith [D.a_nonneg]
    · change f (‖ξ‖ ^ 2) - f (c ^ 2 * ‖ξ‖ ^ 2) = _
      rw [← D.exponent_eq_lkForm hd, ← D.exponent_smul_eq_lkForm hd, ← hrad d D hD c hc0.le]
      congr 1
      simpa using hrad d D hD 1 zero_le_one ξ
  have hgnn : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ σ : ℝ, 0 ≤ σ → 0 ≤ g c σ := fun c hc0 hc1 σ hσ =>
    nonneg_of_radial_negDef (g c) (by simp [hg, hf0]) (hgnd c hc0 hc1 1).2 hσ
  -- Step 2: the radial theorem (A10) for `f`
  obtain ⟨a, b, m, ha, hb, hm, hint, hrep⟩ :=
    schoenberg_radial_bernstein f (fun σ _ => hfnn σ) hfnd
  -- Step 3: `a = 0`
  have ha0 : a = 0 := by
    have hle : ∀ σ : ℝ, 0 < σ → a ≤ f σ := fun σ hσ => by
      have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (f σ) := by
        rw [hrep σ hσ, add_assoc]; exact le_self_add
      exact (ENNReal.ofReal_le_ofReal_iff (hfnn σ)).mp h1
    have htend : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      have h := (hfc.continuousAt (x := 0)).tendsto
      rw [hf0] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    have : a ≤ 0 := ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun σ hσ => hle σ hσ)
    linarith
  subst ha0
  -- Steps 2 and 4: the radial theorem for each `g_c`, and the uniqueness of the triplet
  have hdil : ∀ c : ℝ, 0 < c → c ≤ 1 → Measure.map (fun t : ℝ => c ^ 2 * t) m ≤ m := by
    intro c hc0 hc1
    obtain ⟨ac, bc, mc, hac, hbc, hmc, -, hrepc⟩ :=
      schoenberg_radial_bernstein (g c) (fun σ hσ => hgnn c hc0 hc1 σ hσ.le) (hgnd c hc0 hc1)
    have hc2 : 0 < c ^ 2 := by positivity
    have heq : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal 0 + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m =
        ENNReal.ofReal ac + ENNReal.ofReal ((b * c ^ 2 + bc) * σ) +
          ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t)))
            ∂(Measure.map (fun t : ℝ => c ^ 2 * t) m + mc) := by
      intro σ hσ
      have hsplit : ENNReal.ofReal (f σ) =
          ENNReal.ofReal (f (c ^ 2 * σ)) + ENNReal.ofReal (g c σ) := by
        rw [← ENNReal.ofReal_add (hfnn _) (hgnn c hc0 hc1 σ hσ.le), hg]
        simp
      rw [← hrep σ hσ, hsplit, hrep (c ^ 2 * σ) (by positivity), hrepc σ hσ,
        lintegral_add_measure, lintegral_one_sub_exp_map,
        show (b * c ^ 2 + bc) * σ = b * (c ^ 2 * σ) + bc * σ by ring,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_zero]
      ring
    have hfin : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal 0 + ENNReal.ofReal (b * σ) +
        ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m ≠ ⊤ := fun σ hσ => by
      rw [← hrep σ hσ]; exact ENNReal.ofReal_ne_top
    have hfold : (Measure.map (fun t : ℝ => c ^ 2 * t) m + mc) (Iic 0) = 0 := by
      rw [Measure.add_apply, map_mul_Iic_eq_zero hm hc2, hmc, add_zero]
    obtain ⟨-, -, hmm⟩ := bernstein_triplet_unique le_rfl hb hac (by positivity) hm hfold heq hfin
    calc Measure.map (fun t : ℝ => c ^ 2 * t) m
        ≤ Measure.map (fun t : ℝ => c ^ 2 * t) m + mc := Measure.le_add_right le_rfl
      _ = m := hmm.symm
  -- Step 5: the nonincreasing profile
  have hint2 : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top hint (lintegral_mono_ae ?_)
    filter_upwards [ae_pos_of_Iic_eq_zero hm] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt x 1 with h1 | h1
    · rw [min_eq_right h1]; exact (min_le_right _ _).trans (by nlinarith)
    · rw [min_eq_left h1.le]; exact min_le_left _ _
  let PL : ScaleSpace.SymLevyPair := ⟨0, m, le_rfl, hm, hint2⟩
  obtain ⟨Q, -, hQ⟩ := ScaleSpace.exists_profile_of_dilate_le PL fun lam hl0 hl1 => by
    have h := hdil (Real.sqrt lam) (Real.sqrt_pos.mpr hl0) (Real.sqrt_le_one.mpr hl1)
    rwa [Real.sq_sqrt hl0.le] at h
  change m = ScaleSpace.profileMeasure Q.k at hQ
  have hkm : AEMeasurable Q.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi Q.k_antitone
  -- Step 6: the causally admissible exponent
  have hwin : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Q.k x / x) * ENNReal.ofReal (min 1 x) ≠ ⊤ := by
    rw [← ScaleSpace.lintegral_profileMeasure hkm (by fun_prop), ← hQ]; exact hint
  have hw0 : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (Q.k u) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hwin (le_trans (le_of_eq ?_)
      (lintegral_mono_set (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)))
    refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [min_eq_right hu.2.le, ← ENNReal.ofReal_mul (div_nonneg (Q.k_nonneg u hu.1) hu.1.le),
      div_mul_cancel₀ _ hu.1.ne']
  have hw1 : ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (Q.k u / u) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hwin (le_trans (le_of_eq ?_)
      (lintegral_mono_set (Ioi_subset_Ioi zero_le_one)))
    refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 1 < u) => ?_
    rw [min_eq_left hu.le, ENNReal.ofReal_one, mul_one]
  let FI : ScaleSpace.CausalAdmissible :=
    ⟨b, Q.k, hb, Q.k_nonneg, Q.k_antitone, Q.k_zero, hw0, hw1⟩
  have hFI : ∀ σ : ℝ, 0 < σ → FI.exponent σ = f σ := by
    intro σ hσ
    have h : FI.exponentL σ = ENNReal.ofReal (f σ) := by
      rw [hrep σ hσ, ENNReal.ofReal_zero, zero_add, hQ,
        ScaleSpace.lintegral_profileMeasure hkm (by fun_prop)]
      change ENNReal.ofReal (b * σ) + _ = _
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
      rw [← ENNReal.ofReal_mul (div_nonneg (Q.k_nonneg u hu) hu.le)]
      congr 1
      exact (by ring : (1 - Real.exp (-(σ * u))) * Q.k u / u =
        Q.k u / u * (1 - Real.exp (-(σ * u))))
    rw [ScaleSpace.CausalAdmissible.exponent, h, ENNReal.toReal_ofReal (hfnn σ)]
  refine ⟨FI, fun r hr => ?_⟩
  rcases hr.eq_or_lt with rfl | hr0
  · rw [hF0, show (0 : ℝ) ^ 2 / 2 = 0 by norm_num, FI.exponent_zero]
  · rw [hFI _ (by positivity)]
    change F r = F (Real.sqrt (2 * (r ^ 2 / 2)))
    rw [show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hr]

/-- **`lem:filtration-top`** ([B, Prop. 4.9(4)], restated): `𝒜_∞ = 𝒮`. -/
theorem filtration_top (F : ℝ → ℝ) : classAInf F ↔ classS F :=
  ⟨classS_of_classAInf F, classAInf_of_classS F⟩
end AffineHemigroup
