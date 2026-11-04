/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# `prop:origin-rate-d`, Steps 1, 3 and 3′: Gaussian averages of a regularly varying function

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:origin-rate-d` (Q-0416). Mathlib types
only: nothing here names a datum, a law or a ledger entry, and every declaration is Lean core.

A **ray profile** (`IsRayProfile`) is a measurable function `φ : ℝ → ℝ` with `0 < φ ≤ 1`,
nonincreasing on `(0,∞)`. The transform of an isotropic origin datum along a ray,
`ρ ↦ μ̂(ρe)`, is one (`IsLawOf.isRayProfile`, in `AffineHemigroup.OriginRate`). The file proves,
for a ray profile with `φ(aR)/φ(R) → a^{-c}` as `R → ∞`, what the proof of the rate needs of the
theory of regular variation, without the uniform convergence theorem:

* **Step 1** (`antitoneOn_dyadic_bound`, `IsRayProfile.ratio_le`): the ratio limit at `a = 2`
  alone gives `φ(y) ≤ 2^γ (x/y)^γ φ(x)` for `X ≤ y ≤ x` and any `γ > c`, by dyadic iteration, and
  from it `φ(Ru)/φ(R) ≤ 1 + C u^{-γ}` for `R ≥ X` and every `u > 0`. This stands for Potter's
  bound (Bingham–Goldie–Teugels, Thm. 1.5.6);
* **Step 3** (`IsRayProfile.tendsto_gaussian_average`), for `0 < c < n`:
  `∫_0^∞ φ(Ru) u^{n-1} e^{-u²/4} du / φ(R) → ∫_0^∞ u^{n-1-c} e^{-u²/4} du`, by dominated
  convergence with Step 1;
* **Step 3′**, for `c = n`: with `P(y) = ∫_0^y φ(ρ) ρ^{n-1} dρ` (`truncMoment`) and
  `T(R) = ∫_0^∞ φ(ρ) ρ^{n-1} e^{-ρ²/4R²} dρ` (`gaussMoment`): `R^n φ(R)/P(R) → 0`
  (`tendsto_mul_div_truncMoment`), `P(aR)/P(R) → 1` (`tendsto_truncMoment_dilate`; this stands
  for Prop. 1.5.9a of the same book) and `T(R)/P(R) → 1`
  (`tendsto_gaussMoment_div_truncMoment`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped Topology

/-! ## The dyadic bound -/

/-- Iterating a dyadic bound: `φ(y) ≤ Λ φ(2y)` for `y ≥ X` gives `φ(y) ≤ Λ^n φ(2^n y)`. -/
theorem iterate_dyadic_bound {φ : ℝ → ℝ} {X Λ : ℝ} (hX : 0 < X) (hΛ : 0 ≤ Λ)
    (hdyad : ∀ y, X ≤ y → φ y ≤ Λ * φ (2 * y)) (n : ℕ) :
    ∀ y, X ≤ y → φ y ≤ Λ ^ n * φ (2 ^ n * y) := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h2 := hdyad (2 ^ n * y) (by nlinarith)
    calc φ y ≤ Λ ^ n * φ (2 ^ n * y) := ih y hy
      _ ≤ Λ ^ n * (Λ * φ (2 * (2 ^ n * y))) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hΛ n)
      _ = Λ ^ (n + 1) * φ (2 ^ (n + 1) * y) := by
          rw [show (2 : ℝ) * (2 ^ n * y) = 2 ^ (n + 1) * y by ring]; ring

/-- **A dyadic bound for a nonincreasing function** (Step 1 of `prop:origin-rate-d`): if `φ ≥ 0`
is nonincreasing on `[X,∞)` and `φ(y) ≤ 2^γ φ(2y)` there, then `φ(y) ≤ 2^γ (x/y)^γ φ(x)` for
`X ≤ y ≤ x`. With `n` the least integer with `2^n y ≥ x`: `φ(y) ≤ 2^{γn} φ(2^n y) ≤ 2^{γn} φ(x)`
and `n < log₂(x/y) + 1`. -/
theorem antitoneOn_dyadic_bound {φ : ℝ → ℝ} {X γ : ℝ} (hX : 0 < X) (hγ : 0 ≤ γ)
    (hnn : ∀ x, X ≤ x → 0 ≤ φ x) (hanti : AntitoneOn φ (Ici X))
    (hdyad : ∀ y, X ≤ y → φ y ≤ 2 ^ γ * φ (2 * y)) {x y : ℝ} (hy : X ≤ y) (hyx : y ≤ x) :
    φ y ≤ 2 ^ γ * (x / y) ^ γ * φ x := by
  have hy0 : 0 < y := hX.trans_le hy
  have hx0 : 0 < x := hy0.trans_le hyx
  have hxy : 1 ≤ x / y := (one_le_div hy0).mpr hyx
  have hxy0 : 0 < x / y := by positivity
  set n := ⌈Real.logb 2 (x / y)⌉₊ with hn
  have hlog0 : 0 ≤ Real.logb 2 (x / y) := Real.logb_nonneg (by norm_num) hxy
  have h1 : Real.logb 2 (x / y) ≤ n := Nat.le_ceil _
  have h2 : (n : ℝ) < Real.logb 2 (x / y) + 1 := Nat.ceil_lt_add_one hlog0
  have hpow : x / y ≤ 2 ^ n := by
    have := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hxy0).mp h1
    rwa [Real.rpow_natCast] at this
  have hx2 : x ≤ 2 ^ n * y := by rwa [div_le_iff₀ hy0] at hpow
  have h3 := iterate_dyadic_bound hX (by positivity : (0 : ℝ) ≤ 2 ^ γ) hdyad n y hy
  have h4 : φ (2 ^ n * y) ≤ φ x :=
    hanti (mem_Ici.mpr (hy.trans hyx)) (mem_Ici.mpr (hy.trans (hyx.trans hx2))) hx2
  have h5 : ((2 : ℝ) ^ γ) ^ n ≤ 2 ^ γ * (x / y) ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ (γ * n) ≤ 2 ^ (γ * (Real.logb 2 (x / y) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left h2.le hγ)
      _ = 2 ^ γ * (x / y) ^ γ := by
          rw [mul_add, mul_one, Real.rpow_add (by norm_num), mul_comm γ,
            Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hxy0]
          ring
  calc φ y ≤ (2 ^ γ) ^ n * φ (2 ^ n * y) := h3
    _ ≤ (2 ^ γ) ^ n * φ x := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ 2 ^ γ * (x / y) ^ γ * φ x := mul_le_mul_of_nonneg_right h5 (hnn x (hy.trans hyx))

/-- **A ray profile**: a measurable `φ : ℝ → ℝ` with `0 < φ ≤ 1`, nonincreasing on `(0,∞)`. The
transform of an isotropic origin datum along a ray is one. -/
structure IsRayProfile (φ : ℝ → ℝ) : Prop where
  measurable : Measurable φ
  pos : ∀ x : ℝ, 0 < φ x
  le_one : ∀ x : ℝ, φ x ≤ 1
  antitone : AntitoneOn φ (Ioi 0)

/-- **The truncated moment** `P(y) = ∫_0^y φ(ρ) ρ^{n-1} dρ` of a ray profile. -/
noncomputable def truncMoment (φ : ℝ → ℝ) (n y : ℝ) : ℝ := ∫ ρ in (0 : ℝ)..y, φ ρ * ρ ^ (n - 1)

/-- **The Gaussian moment** `T(R) = ∫_0^∞ φ(ρ) ρ^{n-1} e^{-ρ²/4R²} dρ` of a ray profile. -/
noncomputable def gaussMoment (φ : ℝ → ℝ) (n R : ℝ) : ℝ :=
  ∫ ρ in Ioi (0 : ℝ), φ ρ * ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)

/-- **The bound on the ratios of a ray profile** (Step 1 of `prop:origin-rate-d`): if
`φ(2R)/φ(R) → 2^{-c}` and `γ > c`, there are `X, C > 0` with `φ(Ru)/φ(R) ≤ 1 + C u^{-γ}` for every
`R ≥ X` and every `u > 0`. For `u ≥ 1` the ratio is at most `1`; for `u < 1` and `Ru ≥ X` it is the
dyadic bound; for `Ru < X` the numerator is at most `1` and the dyadic bound between `X` and `R`
bounds `1/φ(R)`. -/
theorem IsRayProfile.ratio_le {φ : ℝ → ℝ} (h : IsRayProfile φ) {c γ : ℝ} (hcγ : c < γ)
    (hγ0 : 0 < γ)
    (hrv : Tendsto (fun R => φ (2 * R) / φ R) atTop (𝓝 ((2 : ℝ) ^ (-c)))) :
    ∃ X C : ℝ, 0 < X ∧ 0 < C ∧ ∀ R, X ≤ R → ∀ u, 0 < u → φ (R * u) / φ R ≤ 1 + C * u ^ (-γ) := by
  have h2 : ∀ᶠ R in atTop, (2 : ℝ) ^ (-γ) < φ (2 * R) / φ R :=
    hrv.eventually (lt_mem_nhds (Real.rpow_lt_rpow_of_exponent_lt one_lt_two (neg_lt_neg hcγ)))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp h2
  set X := max X₀ 1 with hXdef
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : 0 < X := by linarith
  have hdyad : ∀ y, X ≤ y → φ y ≤ 2 ^ γ * φ (2 * y) := by
    intro y hy
    have hy0 : 0 < y := hX0.trans_le hy
    have h' := (hX₀ y ((le_max_left _ _).trans hy)).le
    rw [le_div_iff₀ (h.pos y), Real.rpow_neg (by norm_num),
      inv_mul_le_iff₀ (by positivity)] at h'
    exact h'
  have hantiX : AntitoneOn φ (Ici X) := h.antitone.mono fun x hx => hX0.trans_le hx
  have hbound : ∀ x y, X ≤ y → y ≤ x → φ y ≤ 2 ^ γ * (x / y) ^ γ * φ x := fun x y hy hyx =>
    antitoneOn_dyadic_bound hX0 hγ0.le (fun x hx => (h.pos x).le) hantiX hdyad
      hy hyx
  have hφX := h.pos X
  refine ⟨X, 2 ^ γ / φ X, hX0, by positivity, fun R hR u hu => ?_⟩
  have hR0 : 0 < R := hX0.trans_le hR
  have hφR := h.pos R
  have huγ : 0 < u ^ (-γ) := Real.rpow_pos_of_pos hu _
  have hCge : (2 : ℝ) ^ γ ≤ 2 ^ γ / φ X := by
    rw [le_div_iff₀ hφX]
    exact mul_le_of_le_one_right (by positivity) (h.le_one X)
  rw [div_le_iff₀ hφR]
  have hterm : 0 ≤ 2 ^ γ / φ X * u ^ (-γ) * φ R := by positivity
  rcases le_or_gt 1 u with hu1 | hu1
  · have : φ (R * u) ≤ φ R :=
      h.antitone hR0 (mul_pos hR0 hu) (le_mul_of_one_le_right hR0.le hu1)
    nlinarith
  · rcases le_or_gt X (R * u) with hRu | hRu
    · have h' := hbound R (R * u) hRu (mul_le_of_le_one_right hR0.le hu1.le)
      have e1 : R / (R * u) = u⁻¹ := by field_simp
      rw [e1, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at h'
      calc φ (R * u) ≤ 2 ^ γ * u ^ (-γ) * φ R := h'
        _ ≤ 2 ^ γ / φ X * u ^ (-γ) * φ R := by gcongr
        _ ≤ (1 + 2 ^ γ / φ X * u ^ (-γ)) * φ R := by nlinarith
    · have h' := hbound R X le_rfl hR
      have hRX : R / X ≤ u⁻¹ := by
        rw [div_le_iff₀ hX0, inv_mul_eq_div, le_div_iff₀ hu]
        exact hRu.le
      have hpw : (R / X) ^ γ ≤ u ^ (-γ) := by
        rw [Real.rpow_neg hu.le, ← Real.inv_rpow hu.le]
        exact Real.rpow_le_rpow (by positivity) hRX hγ0.le
      have h1 : φ (R * u) ≤ 1 := h.le_one _
      have h2' : φ X ≤ 2 ^ γ * u ^ (-γ) * φ R := h'.trans (by gcongr)
      have h3 : 1 ≤ 2 ^ γ / φ X * u ^ (-γ) * φ R := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hφX, one_mul]
        exact h2'
      nlinarith

/-- **The Abelian step below the threshold** (Step 3 of `prop:origin-rate-d`): for a ray profile
with `φ(aR)/φ(R) → a^{-c}` for every `a > 0` and `0 < c < n`,
`∫_0^∞ φ(Ru) u^{n-1} e^{-u²/4} du / φ(R) → ∫_0^∞ u^{n-1-c} e^{-u²/4} du` as `R → ∞`. Dominated
convergence: the integrand is at most `(1 + C u^{-γ}) u^{n-1} e^{-u²/4}` for `R ≥ X`, with
`γ = (c+n)/2 < n`. -/
theorem IsRayProfile.tendsto_gaussian_average {φ : ℝ → ℝ} (h : IsRayProfile φ) {c n : ℝ}
    (hc : 0 < c) (hcn : c < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-c)))) :
    Tendsto (fun R : ℝ =>
        (∫ u in Ioi (0 : ℝ), φ (R * u) * (u ^ (n - 1) * Real.exp (-(1 / 4) * u ^ 2))) / φ R)
      atTop (𝓝 (∫ u in Ioi (0 : ℝ), u ^ (n - 1 - c) * Real.exp (-(1 / 4) * u ^ 2))) := by
  set γ := (c + n) / 2 with hγ
  have hcγ : c < γ := by rw [hγ]; linarith
  have hγn : γ < n := by rw [hγ]; linarith
  have hγ0 : 0 < γ := hc.trans hcγ
  obtain ⟨X, C, hX0, hC0, hratio⟩ := h.ratio_le hcγ hγ0 (hrv 2 two_pos)
  set w : ℝ → ℝ := fun u => u ^ (n - 1) * Real.exp (-(1 / 4) * u ^ 2) with hw
  have hwm : Measurable w := (measurable_id.pow_const _).mul (by fun_prop)
  have hwint : IntegrableOn w (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)
  have hw2int : IntegrableOn (fun u : ℝ => u ^ (n - 1 - γ) * Real.exp (-(1 / 4) * u ^ 2))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)
  have hmain : Tendsto (fun R : ℝ => ∫ u in Ioi (0 : ℝ), φ (R * u) / φ R * w u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), u ^ (n - 1 - c) * Real.exp (-(1 / 4) * u ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => w u + C * (u ^ (n - 1 - γ) * Real.exp (-(1 / 4) * u ^ 2))) ?_ ?_
      (hwint.add (hw2int.const_mul C)) ?_
    · exact .of_forall fun R =>
        (((h.measurable.comp (measurable_const.mul measurable_id)).div_const _).mul
          hwm).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop X] with R hR
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
      have hR0 : 0 < R := hX0.trans_le hR
      have hw0 : 0 ≤ w u := by positivity
      rw [Real.norm_of_nonneg (mul_nonneg
        (div_nonneg (h.pos _).le (h.pos _).le) hw0)]
      calc φ (R * u) / φ R * w u ≤ (1 + C * u ^ (-γ)) * w u :=
            mul_le_mul_of_nonneg_right (hratio R hR u hu) hw0
        _ = w u + C * (u ^ (n - 1 - γ) * Real.exp (-(1 / 4) * u ^ 2)) := by
            simp only [hw]
            rw [show n - 1 - γ = -γ + (n - 1) by ring, Real.rpow_add hu]
            ring
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
      have h1 := (hrv u hu).mul_const (w u)
      have e : u ^ (-c) * w u = u ^ (n - 1 - c) * Real.exp (-(1 / 4) * u ^ 2) := by
        simp only [hw]
        rw [show n - 1 - c = -c + (n - 1) by ring, Real.rpow_add hu]
        ring
      rw [e] at h1
      refine h1.congr fun R => ?_
      rw [mul_comm u R]
  refine hmain.congr fun R => ?_
  rw [← integral_div]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [hw]
  ring

namespace IsRayProfile

variable {φ : ℝ → ℝ} {n : ℝ}

/-- `ρ ↦ φ(ρ) ρ^{n-1}` is interval integrable, `n > 0`. -/
theorem intervalIntegrable_mul_rpow (h : IsRayProfile φ) (hn : 0 < n) (a b : ℝ) :
    IntervalIntegrable (fun ρ => φ ρ * ρ ^ (n - 1)) volume a b := by
  have h1 : IntervalIntegrable (fun ρ : ℝ => ρ ^ (n - 1)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine h1.norm.mono_fun' ((h.measurable.mul (measurable_id.pow_const _)).aestronglyMeasurable)
    (.of_forall fun ρ => ?_)
  change ‖φ ρ * ρ ^ (n - 1)‖ ≤ ‖ρ ^ (n - 1)‖
  rw [norm_mul, Real.norm_of_nonneg (h.pos ρ).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (h.le_one ρ)

/-- `P(y) ≥ 0` for `y ≥ 0`. -/
theorem truncMoment_nonneg (h : IsRayProfile φ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ truncMoment φ n y :=
  intervalIntegral.integral_nonneg hy fun ρ hρ =>
    mul_nonneg (h.pos ρ).le (Real.rpow_nonneg hρ.1 _)

/-- `P(y) - P(x) = ∫_x^y φ(ρ) ρ^{n-1} dρ`. -/
theorem truncMoment_sub (h : IsRayProfile φ) (hn : 0 < n) (x y : ℝ) :
    truncMoment φ n y - truncMoment φ n x = ∫ ρ in x..y, φ ρ * ρ ^ (n - 1) :=
  intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_mul_rpow hn 0 y)
    (h.intervalIntegrable_mul_rpow hn 0 x)

/-- `∫_x^y ρ^{n-1} dρ = (y^n - x^n)/n`, `n > 0`. -/
theorem integral_rpow_pred (hn : 0 < n) (x y : ℝ) :
    ∫ ρ in x..y, ρ ^ (n - 1) = (y ^ n - x ^ n) / n := by
  rw [integral_rpow (Or.inl (by linarith)), sub_add_cancel]

/-- `P(y) - P(x) ≤ φ(x) (y^n - x^n)/n` for `0 < x ≤ y`. -/
theorem truncMoment_sub_le (h : IsRayProfile φ) (hn : 0 < n) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    truncMoment φ n y - truncMoment φ n x ≤ φ x * ((y ^ n - x ^ n) / n) := by
  rw [h.truncMoment_sub hn, ← integral_rpow_pred hn, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hxy (h.intervalIntegrable_mul_rpow hn x y)
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _) fun ρ hρ => ?_
  exact mul_le_mul_of_nonneg_right (h.antitone hx (hx.trans_le hρ.1) hρ.1)
    (Real.rpow_nonneg (hx.le.trans hρ.1) _)

/-- `φ(y) (y^n - x^n)/n ≤ P(y) - P(x)` for `0 < x ≤ y`. -/
theorem le_truncMoment_sub (h : IsRayProfile φ) (hn : 0 < n) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    φ y * ((y ^ n - x ^ n) / n) ≤ truncMoment φ n y - truncMoment φ n x := by
  rw [h.truncMoment_sub hn, ← integral_rpow_pred hn, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hxy
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (h.intervalIntegrable_mul_rpow hn x y) fun ρ hρ => ?_
  exact mul_le_mul_of_nonneg_right (h.antitone (hx.trans_le hρ.1) (hx.trans_le hxy) hρ.2)
    (Real.rpow_nonneg (hx.le.trans hρ.1) _)

/-- `P(y) > 0` for `y > 0`. -/
theorem truncMoment_pos (h : IsRayProfile φ) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    0 < truncMoment φ n y := by
  have h1 := h.le_truncMoment_sub hn (half_pos hy) (half_le_self hy.le)
  have h2 : 0 ≤ truncMoment φ n (y / 2) := h.truncMoment_nonneg (half_pos hy).le
  have h3 : (y / 2) ^ n < y ^ n := Real.rpow_lt_rpow (half_pos hy).le (half_lt_self hy) hn
  have h4 : 0 < φ y * ((y ^ n - (y / 2) ^ n) / n) :=
    mul_pos (h.pos y) (div_pos (sub_pos.mpr h3) hn)
  linarith

/-- `P` is nondecreasing on `(0,∞)`. -/
theorem truncMoment_mono (h : IsRayProfile φ) (hn : 0 < n) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : truncMoment φ n x ≤ truncMoment φ n y := by
  have h1 := h.le_truncMoment_sub hn hx hxy
  have h3 : x ^ n ≤ y ^ n := Real.rpow_le_rpow hx.le hxy hn.le
  have h4 : 0 ≤ φ y * ((y ^ n - x ^ n) / n) :=
    mul_nonneg (h.pos y).le (div_nonneg (sub_nonneg.mpr h3) hn.le)
  linarith

/-- The dyadic increments: for every `k`, eventually
`k (κ/2) R^n φ(R) ≤ P(R) - P(R/2^k)`, `κ = (1 - 2^{-n})/n`. -/
theorem eventually_mul_le_truncMoment_sub (h : IsRayProfile φ) (hn : 0 < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-n)))) (k : ℕ) :
    ∀ᶠ R in atTop, (k : ℝ) * ((1 - (1 / 2 : ℝ) ^ n) / n / 2) * (R ^ n * φ R)
      ≤ truncMoment φ n R - truncMoment φ n (R / 2 ^ k) := by
  induction k with
  | zero => exact .of_forall fun R => by simp
  | succ k ih =>
    set a : ℝ := (2 ^ k)⁻¹ with ha
    have ha0 : 0 < a := by positivity
    have hlim : Tendsto (fun R => a ^ n * (φ (a * R) / φ R)) atTop (𝓝 1) := by
      have := (hrv a ha0).const_mul (a ^ n)
      rwa [← Real.rpow_add ha0, add_neg_cancel, Real.rpow_zero] at this
    have hev : ∀ᶠ R in atTop, (1 / 2 : ℝ) < a ^ n * (φ (a * R) / φ R) :=
      hlim.eventually (lt_mem_nhds (by norm_num))
    filter_upwards [ih, hev, eventually_gt_atTop 0] with R hR hR2 hR0
    have haR : 0 < a * R := mul_pos ha0 hR0
    have e1 : R / 2 ^ k = a * R := by rw [ha]; field_simp
    have e2 : R / 2 ^ (k + 1) = a * R / 2 := by rw [ha, pow_succ]; field_simp
    have hstep := h.le_truncMoment_sub hn (half_pos haR) (half_le_self haR.le)
    have hpow : (a * R / 2) ^ n = (a * R) ^ n * (1 / 2 : ℝ) ^ n := by
      rw [div_eq_mul_one_div, Real.mul_rpow haR.le (by norm_num)]
    have hL : R ^ n * φ R / 2 ≤ (a * R) ^ n * φ (a * R) := by
      rw [Real.mul_rpow ha0.le hR0.le]
      have hφR := h.pos R
      have := (lt_div_iff₀ hφR).mp (by
        rw [mul_div_assoc']  at hR2
        exact hR2 : (1 / 2 : ℝ) < a ^ n * φ (a * R) / φ R)
      have hRn : 0 ≤ R ^ n := Real.rpow_nonneg hR0.le _
      nlinarith
    have hκ : 0 ≤ (1 - (1 / 2 : ℝ) ^ n) / n := by
      refine div_nonneg (sub_nonneg.mpr ?_) hn.le
      exact Real.rpow_le_one (by norm_num) (by norm_num) hn.le
    have hstep' : (1 - (1 / 2 : ℝ) ^ n) / n * ((a * R) ^ n * φ (a * R))
        ≤ truncMoment φ n (a * R) - truncMoment φ n (a * R / 2) := by
      refine le_trans (le_of_eq ?_) hstep
      rw [hpow]; ring
    rw [e1] at hR
    rw [e2]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hL hκ]

/-- `R^n φ(R) / P(R) → 0`. -/
theorem tendsto_mul_div_truncMoment (h : IsRayProfile φ) (hn : 0 < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-n)))) :
    Tendsto (fun R => R ^ n * φ R / truncMoment φ n R) atTop (𝓝 0) := by
  set κ := (1 - (1 / 2 : ℝ) ^ n) / n / 2 with hκdef
  have hκ : 0 < κ := by
    refine div_pos (div_pos (sub_pos.mpr ?_) hn) two_pos
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hn
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact ha'.trans_le (div_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _) (h.pos R).le)
      (h.truncMoment_nonneg hR.le))
  · obtain ⟨k, hk⟩ := exists_nat_gt (1 / (κ * b))
    have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
    filter_upwards [h.eventually_mul_le_truncMoment_sub hn hrv k, eventually_gt_atTop 0]
      with R hR hR0
    have hP := h.truncMoment_pos hn hR0
    have hP2 : 0 ≤ truncMoment φ n (R / 2 ^ k) := h.truncMoment_nonneg (by positivity)
    rw [← hκdef] at hR
    rw [div_lt_iff₀ hP]
    have h1 : (k : ℝ) * κ * (R ^ n * φ R) ≤ truncMoment φ n R := by linarith
    have h2 : 1 < (k : ℝ) * κ * b := by
      have := (div_lt_iff₀ (mul_pos hκ hb)).mp hk
      linarith
    have hL : 0 < R ^ n * φ R := mul_pos (Real.rpow_pos_of_pos hR0 _) (h.pos R)
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le, mul_pos hL (sub_pos.mpr h2)]

/-- `P(aR)/P(R) → 1`, `a ≥ 1`. -/
theorem tendsto_truncMoment_dilate_of_one_le (h : IsRayProfile φ) (hn : 0 < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-n))))
    {a : ℝ} (ha : 1 ≤ a) :
    Tendsto (fun R => truncMoment φ n (a * R) / truncMoment φ n R) atTop (𝓝 1) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hup : Tendsto (fun R => 1 + (a ^ n - 1) / n * (R ^ n * φ R / truncMoment φ n R)) atTop
      (𝓝 1) := by
    have := ((h.tendsto_mul_div_truncMoment hn hrv).const_mul ((a ^ n - 1) / n)).const_add 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hP := h.truncMoment_pos hn hR
    rw [le_div_iff₀ hP, one_mul]
    exact h.truncMoment_mono hn hR (le_mul_of_one_le_left hR.le ha)
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hP := h.truncMoment_pos hn hR
    have h1 := h.truncMoment_sub_le hn hR (le_mul_of_one_le_left hR.le ha)
    rw [Real.mul_rpow ha0.le hR.le] at h1
    rw [div_le_iff₀ hP, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hP.ne']
    have e : φ R * ((a ^ n * R ^ n - R ^ n) / n) = (a ^ n - 1) / n * (R ^ n * φ R) := by ring
    linarith

/-- `P(aR)/P(R) → 1` for every `a > 0`. -/
theorem tendsto_truncMoment_dilate (h : IsRayProfile φ) (hn : 0 < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-n))))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R => truncMoment φ n (a * R) / truncMoment φ n R) atTop (𝓝 1) := by
  rcases le_or_gt 1 a with h1 | h1
  · exact h.tendsto_truncMoment_dilate_of_one_le hn hrv h1
  · have h' := (h.tendsto_truncMoment_dilate_of_one_le hn hrv
      (one_le_inv_iff₀.mpr ⟨ha, h1.le⟩)).comp (tendsto_id.const_mul_atTop ha)
    have h'' := h'.inv₀ one_ne_zero
    rw [inv_one] at h''
    refine h''.congr fun R => ?_
    simp only [Function.comp_apply, id]
    rw [inv_div, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

/-- The integrand of `T(R)` is integrable on `(0,∞)`. -/
theorem integrableOn_gaussMoment (h : IsRayProfile φ) (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ρ => φ ρ * ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)) (Ioi 0) := by
  have hb : (0 : ℝ) < 1 / (4 * R ^ 2) := by positivity
  have h1 : IntegrableOn (fun ρ : ℝ => ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)
  refine Integrable.mono' h1 (((h.measurable.mul (measurable_id.pow_const _)).mul
    (by fun_prop)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun ρ (hρ : 0 < ρ) => ?_))
  have hp : 0 ≤ ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2) := by positivity
  rw [mul_assoc, norm_mul, Real.norm_of_nonneg (h.pos ρ).le, Real.norm_of_nonneg hp]
  exact mul_le_of_le_one_left hp (h.le_one ρ)

/-- `e^{-ε²/4} P(εR) ≤ T(R)`. -/
theorem exp_mul_truncMoment_le_gaussMoment (h : IsRayProfile φ) (hn : 0 < n) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) :
    Real.exp (-(ε ^ 2 / 4)) * truncMoment φ n (ε * R) ≤ gaussMoment φ n R := by
  have hεR : 0 < ε * R := mul_pos hε hR
  have hint := h.integrableOn_gaussMoment hn hR
  have hsub : Ioc 0 (ε * R) ⊆ Ioi (0 : ℝ) := Ioc_subset_Ioi_self
  have h1 : ∫ ρ in Ioc 0 (ε * R), φ ρ * ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)
      ≤ gaussMoment φ n R := by
    refine setIntegral_mono_set hint ?_ hsub.eventuallyLE
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun ρ (hρ : 0 < ρ) => by
      have := h.pos ρ
      positivity)
  refine le_trans ?_ h1
  rw [truncMoment, intervalIntegral.integral_of_le hεR.le, ← integral_const_mul]
  refine setIntegral_mono_on ?_ (hint.mono_set hsub) measurableSet_Ioc fun ρ hρ => ?_
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hεR.le).mp
      (h.intervalIntegrable_mul_rpow hn 0 (ε * R))).const_mul _
  · have hg : 0 ≤ φ ρ * ρ ^ (n - 1) := mul_nonneg (h.pos ρ).le (Real.rpow_nonneg hρ.1.le _)
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hg
    have h2 : ρ ^ 2 ≤ (ε * R) ^ 2 := pow_le_pow_left₀ hρ.1.le hρ.2 2
    rw [neg_mul, neg_le_neg_iff, one_div, inv_mul_le_iff₀ (by positivity)]
    nlinarith

/-- `T(R) ≤ P(R) + 2^{n-1} Γ(n/2) R^n φ(R)`. -/
theorem gaussMoment_le (h : IsRayProfile φ) (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    gaussMoment φ n R ≤ truncMoment φ n R
      + 2 ^ (n - 1) * Real.Gamma (n / 2) * (R ^ n * φ R) := by
  have hint := h.integrableOn_gaussMoment hn hR
  have hb : (0 : ℝ) < 1 / (4 * R ^ 2) := by positivity
  have hw : IntegrableOn (fun ρ : ℝ => ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)
  have hval : ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)
      = 2 ^ (n - 1) * Real.Gamma (n / 2) * R ^ n := by
    have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := n - 1) two_pos (by linarith) hb
    simp only [Real.rpow_two] at this
    rw [this, sub_add_cancel]
    have e : (1 / (4 * R ^ 2)) ^ (-n / 2) = 2 ^ n * R ^ n := by
      rw [show (1 / (4 * R ^ 2) : ℝ) = ((2 * R) ^ (2 : ℝ))⁻¹ by
        rw [Real.rpow_two]; ring_nf, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hR.le]
      congr 1 <;> ring_nf
    rw [e, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [gaussMoment, ← Ioc_union_Ioi_eq_Ioi hR.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hR.le))]
  refine add_le_add ?_ ?_
  · rw [truncMoment, intervalIntegral.integral_of_le hR.le]
    refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp
        (h.intervalIntegrable_mul_rpow hn 0 R)) measurableSet_Ioc fun ρ hρ => ?_
    have hg : 0 ≤ φ ρ * ρ ^ (n - 1) := mul_nonneg (h.pos ρ).le (Real.rpow_nonneg hρ.1.le _)
    refine mul_le_of_le_one_right hg (Real.exp_le_one_iff.mpr ?_)
    have : 0 ≤ 1 / (4 * R ^ 2) * ρ ^ 2 := by positivity
    linarith
  · calc ∫ ρ in Ioi R, φ ρ * ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)
        ≤ ∫ ρ in Ioi R, φ R * (ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)) := by
          refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hR.le))
            ((hw.mono_set (Ioi_subset_Ioi hR.le)).const_mul _) measurableSet_Ioi
            fun ρ (hρ : R < ρ) => ?_
          have hρ0 : 0 < ρ := hR.trans hρ
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (h.antitone hR hρ0 hρ.le) (by positivity)
      _ ≤ ∫ ρ in Ioi (0 : ℝ), φ R * (ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)) := by
          refine setIntegral_mono_set (hw.const_mul _) ?_
            (Ioi_subset_Ioi hR.le).eventuallyLE
          exact (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun ρ (hρ : 0 < ρ) => by
            have := h.pos R
            positivity)
      _ = 2 ^ (n - 1) * Real.Gamma (n / 2) * (R ^ n * φ R) := by
          rw [integral_const_mul, hval]; ring

/-- **The Abelian step at the threshold** (Step 3′(iii) of `prop:origin-rate-d`): for a ray
profile with `φ(aR)/φ(R) → a^{-n}`, `T(R)/P(R) → 1` as `R → ∞`. From below,
`T(R) ≥ e^{-ε²/4} P(εR)` and `P(εR)/P(R) → 1`; from above, `T(R) ≤ P(R) + 2^{n-1} Γ(n/2) R^n φ(R)`
and `R^n φ(R)/P(R) → 0`. -/
theorem tendsto_gaussMoment_div_truncMoment (h : IsRayProfile φ) (hn : 0 < n)
    (hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-n)))) :
    Tendsto (fun R => gaussMoment φ n R / truncMoment φ n R) atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun b hb => ?_⟩
  · have hcont : Tendsto (fun ε : ℝ => Real.exp (-(ε ^ 2 / 4))) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun ε : ℝ => Real.exp (-(ε ^ 2 / 4))) (𝓝 0) (𝓝 (Real.exp (-(0 ^ 2 / 4)))) :=
        (Continuous.tendsto (by fun_prop) 0)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
        Real.exp_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hε, hε0⟩ := ((hcont.eventually (lt_mem_nhds ha')).and self_mem_nhdsWithin).exists
    have hε0' : 0 < ε := hε0
    have hlim := (h.tendsto_truncMoment_dilate hn hrv hε0').const_mul (Real.exp (-(ε ^ 2 / 4)))
    rw [mul_one] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hε), eventually_gt_atTop 0] with R hR hR0
    have hP := h.truncMoment_pos hn hR0
    refine hR.trans_le ?_
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hP]
    exact h.exp_mul_truncMoment_le_gaussMoment hn hR0 hε0'
  · have hup : Tendsto (fun R => 1 + 2 ^ (n - 1) * Real.Gamma (n / 2) *
        (R ^ n * φ R / truncMoment φ n R)) atTop (𝓝 1) := by
      have := ((h.tendsto_mul_div_truncMoment hn hrv).const_mul
        (2 ^ (n - 1) * Real.Gamma (n / 2))).const_add 1
      simpa using this
    filter_upwards [hup.eventually (gt_mem_nhds hb), eventually_gt_atTop 0] with R hR hR0
    have hP := h.truncMoment_pos hn hR0
    refine lt_of_le_of_lt ?_ hR
    rw [div_le_iff₀ hP, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hP.ne']
    exact h.gaussMoment_le hn hR0

end IsRayProfile

end AffineHemigroup
