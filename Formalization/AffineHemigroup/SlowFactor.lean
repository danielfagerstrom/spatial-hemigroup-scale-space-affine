/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ExponentLog

/-!
# `prop:isotropic-exponent-profile`(1): the slowly varying factor of the polar profile

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-exponent-profile`, clause (1),
and the tail identity `eq:profile-tail` of its proof (Q-0427).

For an isotropic origin datum with a finite profile at the origin `c = k_d(0+)`,
`K(x) = exp ∫_x^1 (c - k_d(u)) du/u` is `OriginDatum.slowFactor`, a **total** function of a real
`x`: for `0 < x ≤ 1` it is the blueprint's `K`; for `x > 1` the interval integral is oriented and
the value is below `1`; for `x ≤ 0` the value is not read. `K(0+)` in the convergent case is
`OriginDatum.slowFactorZero`, `exp ∫_{(0,1]} (c - k_d(u)) du/u`, read only under the hypothesis
that the integrand is integrable on `(0,1]`.

* `slowFactor_basic`: `K(1) = 1`, `K` is continuous and nonincreasing on `(0,1]`, and
  `1 ≤ K(x) ≤ x^{-c}` there;
* `slowFactor_ratio`: `K(ax)/K(x) → 1` as `x ↓ 0`, for every `a > 0`;
* `slowFactor_tendsto_of_integrable`: if `(c - k_d(u))/u` is integrable on `(0,1]`, `K(x) → K(0+)`
  as `x ↓ 0`, with `1 ≤ K(0+)` and `K ≤ K(0+)` on `(0,1]`;
* `slowFactor_tendsto_atTop`: if it is not, `K(x) → ∞`;
* `integral_k_div_Ioi_eq`: for `ρ ≥ 1`, `∫_{1/ρ}^∞ k_d(r) dr/r = c log ρ - log K(1/ρ) + C_k`.

Lean core: Mathlib types and this module's datum only.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {d : ℕ}

namespace OriginDatum

/-- **`K(x) = exp ∫_x^1 (c - k_d(u)) du/u`** (`prop:isotropic-exponent-profile`), `c` the profile
at the origin as a real number; a total function, read on `(0,1]`. -/
noncomputable def slowFactor (D : OriginDatum d) (x : ℝ) : ℝ :=
  Real.exp (∫ u in x..1, (D.profileAtOrigin.toReal - D.k u) / u)

/-- **`K(0+) = exp ∫_0^1 (c - k_d(u)) du/u`** (`prop:isotropic-exponent-profile`(1)), the limit of
`K` at `0` when the integral converges. When it does not, the Bochner integral is `0` and the
value is `1`, which no statement reads: every statement naming it assumes the integrability. -/
noncomputable def slowFactorZero (D : OriginDatum d) : ℝ :=
  Real.exp (∫ u in Ioc (0 : ℝ) 1, (D.profileAtOrigin.toReal - D.k u) / u)

end OriginDatum

/-! ## The integrand `(c - k_d(u))/u` -/

/-- `(c - k_d(u))/u ≥ 0` for `u > 0`, when `c` is finite. -/
theorem OriginDatum.slowIntegrand_nonneg (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {u : ℝ}
    (hu : 0 < u) : 0 ≤ (D.profileAtOrigin.toReal - D.k u) / u :=
  div_nonneg (sub_nonneg.2 (D.k_le_toReal hc hu)) hu.le

/-- `(c - k_d(u))/u` is interval integrable between two positive points. -/
theorem OriginDatum.intervalIntegrable_slowIntegrand (D : OriginDatum d) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    IntervalIntegrable (fun u => (D.profileAtOrigin.toReal - D.k u) / u) volume x y := by
  have key : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable (fun u => (D.profileAtOrigin.toReal - D.k u) / u) volume a b := by
    intro a b ha hab
    have h1 : IntervalIntegrable (fun u : ℝ => D.profileAtOrigin.toReal * u⁻¹) volume a b := by
      refine ContinuousOn.intervalIntegrable (continuousOn_const.mul
        (continuousOn_inv₀.mono fun v hv => ?_))
      rw [uIcc_of_le hab] at hv
      exact ne_of_gt (lt_of_lt_of_le ha hv.1)
    refine (h1.sub (D.intervalIntegrable_k_div ha hab)).congr fun u _ => ?_
    change D.profileAtOrigin.toReal * u⁻¹ - D.k u / u = (D.profileAtOrigin.toReal - D.k u) / u
    ring
  rcases le_total x y with h | h
  · exact key x y hx h
  · exact (key y x hy h).symm

/-- `∫_x^1 - ∫_y^1 = ∫_x^y` of the integrand, for `x, y > 0`. -/
theorem OriginDatum.slowIntegral_sub (D : OriginDatum d) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ u in x..1, (D.profileAtOrigin.toReal - D.k u) / u) -
        ∫ u in y..1, (D.profileAtOrigin.toReal - D.k u) / u
      = ∫ u in x..y, (D.profileAtOrigin.toReal - D.k u) / u := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (D.intervalIntegrable_slowIntegrand hx hy) (D.intervalIntegrable_slowIntegrand hy one_pos)]
  ring

/-- For `b ≥ 1` and `x > 0`: `0 ≤ ∫_x^{bx} (c - k_d(u)) du/u ≤ (c - k_d(bx)) log b`. -/
theorem OriginDatum.slowIntegral_dilate_bounds (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    {x b : ℝ} (hx : 0 < x) (hb : 1 ≤ b) :
    0 ≤ ∫ u in x..(b * x), (D.profileAtOrigin.toReal - D.k u) / u ∧
      ∫ u in x..(b * x), (D.profileAtOrigin.toReal - D.k u) / u
        ≤ (D.profileAtOrigin.toReal - D.k (b * x)) * Real.log b := by
  have hxb : x ≤ b * x := le_mul_of_one_le_left hx.le hb
  have hbx : 0 < b * x := by positivity
  refine ⟨intervalIntegral.integral_nonneg hxb fun u hu =>
    D.slowIntegrand_nonneg hc (lt_of_lt_of_le hx hu.1), ?_⟩
  have hlog : ∫ v in x..(b * x), v⁻¹ = Real.log b := by
    rw [integral_inv_of_pos hx hbx, mul_div_assoc, div_self hx.ne', mul_one]
  have hiinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume x (b * x) := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
    rw [uIcc_of_le hxb] at hv
    exact ne_of_gt (lt_of_lt_of_le hx hv.1)
  rw [← hlog, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hxb (D.intervalIntegrable_slowIntegrand hx hbx)
    (hiinv.const_mul _) fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le hx hu.1
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hu0.le)
  have := D.k_antitone hu0 hbx hu.2
  linarith

/-! ## Clause (1) -/

/-- **`prop:isotropic-exponent-profile`(1), the factor**: for a datum with a finite profile at
the origin `c`, `K(1) = 1`, `K` is continuous and nonincreasing on `(0,1]`, and
`1 ≤ K(x) ≤ x^{-c}` for `0 < x ≤ 1`. -/
theorem slowFactor_basic (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) :
    D.slowFactor 1 = 1 ∧ ContinuousOn D.slowFactor (Ioc 0 1) ∧ AntitoneOn D.slowFactor (Ioc 0 1) ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, 1 ≤ D.slowFactor x ∧
        D.slowFactor x ≤ x ^ (-D.profileAtOrigin.toReal) := by
  set c := D.profileAtOrigin.toReal with hcdef
  set f : ℝ → ℝ := fun u => (c - D.k u) / u with hf
  have hnn : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ ∫ u in x..1, f u := fun x hx =>
    intervalIntegral.integral_nonneg hx.2 fun u hu =>
      D.slowIntegrand_nonneg hc (lt_of_lt_of_le hx.1 hu.1)
  refine ⟨by simp [OriginDatum.slowFactor], ?_, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · -- continuity: on `[x₀/2, 1]` the primitive from `1` is continuous
    intro x₀ hx₀
    have hx₀2 : 0 < x₀ / 2 := by linarith [hx₀.1]
    have hle : x₀ / 2 ≤ 1 := by linarith [hx₀.2]
    have hcont := intervalIntegral.continuousOn_primitive_interval' (a := 1)
      (D.intervalIntegrable_slowIntegrand hx₀2 one_pos) (right_mem_uIcc)
    rw [uIcc_of_le hle] at hcont
    have hmem : Icc (x₀ / 2) 1 ∈ 𝓝[Ioc 0 1] x₀ :=
      mem_nhdsWithin.2 ⟨Ioi (x₀ / 2), isOpen_Ioi, by simp only [mem_Ioi]; linarith [hx₀.1],
        fun y hy => ⟨hy.1.le, hy.2.2⟩⟩
    have h1 : ContinuousWithinAt (fun b => ∫ u in (1 : ℝ)..b, f u) (Ioc 0 1) x₀ :=
      (hcont x₀ ⟨by linarith [hx₀.1], hx₀.2⟩).mono_of_mem_nhdsWithin hmem
    have h2 : ContinuousWithinAt (fun b => Real.exp (-∫ u in (1 : ℝ)..b, f u)) (Ioc 0 1) x₀ :=
      Real.continuous_exp.continuousAt.comp_continuousWithinAt h1.neg
    refine h2.congr (fun y _ => ?_) ?_
    · simp only [OriginDatum.slowFactor]; rw [intervalIntegral.integral_symm]
    · simp only [OriginDatum.slowFactor]; rw [intervalIntegral.integral_symm]
  · -- monotonicity
    intro x hx y hy hxy
    simp only [OriginDatum.slowFactor]
    refine Real.exp_le_exp.2 ?_
    have h := D.slowIntegral_sub hx.1 hy.1
    have h0 : 0 ≤ ∫ u in x..y, f u := intervalIntegral.integral_nonneg hxy fun u hu =>
      D.slowIntegrand_nonneg hc (lt_of_lt_of_le hx.1 hu.1)
    linarith
  · simp only [OriginDatum.slowFactor]
    exact Real.one_le_exp (hnn x hx)
  · -- `K(x) ≤ x^{-c}`
    simp only [OriginDatum.slowFactor]
    rw [Real.rpow_def_of_pos hx.1]
    refine Real.exp_le_exp.2 ?_
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    have hlog : ∫ v in x..1, v⁻¹ = -Real.log x := by
      rw [integral_inv_of_pos hx.1 one_pos, one_div, Real.log_inv]
    have hiinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume x 1 := by
      refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
      rw [uIcc_of_le hx.2] at hv
      exact ne_of_gt (lt_of_lt_of_le hx.1 hv.1)
    have : ∫ u in x..1, f u ≤ ∫ u in x..1, c * u⁻¹ := by
      refine intervalIntegral.integral_mono_on hx.2
        (D.intervalIntegrable_slowIntegrand hx.1 one_pos) (hiinv.const_mul c) fun u hu => ?_
      have hu0 : 0 < u := lt_of_lt_of_le hx.1 hu.1
      simp only [hf]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith [D.k_nonneg u hu0]) (inv_nonneg.2 hu0.le)
    rw [intervalIntegral.integral_const_mul, hlog] at this
    linarith

/-- `x ↦ bx` maps the right neighbourhoods of `0` to themselves, `b > 0`. -/
theorem tendsto_mul_nhdsGT_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => b * x) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun x : ℝ => b * x) (𝓝 0) (𝓝 (b * 0)) := (continuous_const_mul b).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact mul_pos hb hx

/-- **`prop:isotropic-exponent-profile`(1), slow variation**: for every `a > 0`,
`K(ax)/K(x) → 1` as `x ↓ 0`. For small `x` both `x` and `ax` lie in `(0,1]`, where `K` is the
blueprint's function. -/
theorem slowFactor_ratio (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => D.slowFactor (a * x) / D.slowFactor x) (𝓝[>] 0) (𝓝 1) := by
  set c := D.profileAtOrigin.toReal with hcdef
  set f : ℝ → ℝ := fun u => (c - D.k u) / u with hf
  have hratio : ∀ x : ℝ, 0 < x →
      D.slowFactor (a * x) / D.slowFactor x = Real.exp (∫ u in (a * x)..x, f u) := by
    intro x hx
    simp only [OriginDatum.slowFactor]
    rw [← Real.exp_sub, D.slowIntegral_sub (mul_pos ha hx) hx]
  -- `c - k(bx) → 0`
  have hk0 : ∀ b : ℝ, 0 < b → Tendsto (fun x : ℝ => (c - D.k (b * x)) * |Real.log a|) (𝓝[>] 0)
      (𝓝 0) := by
    intro b hb
    have h1 : Tendsto (fun x : ℝ => D.k (b * x)) (𝓝[>] 0) (𝓝 c) :=
      (D.tendsto_k_zero hc).comp (tendsto_mul_nhdsGT_zero hb)
    have h2 := ((tendsto_const_nhds (x := c)).sub h1).mul_const |Real.log a|
    rwa [sub_self, zero_mul] at h2
  have hlim : Tendsto (fun x : ℝ => ∫ u in (a * x)..x, f u) (𝓝[>] 0) (𝓝 0) := by
    rcases le_total a 1 with ha1 | ha1
    · -- `ax ≤ x`: the integral lies in `[0, (c - k(x)) log(1/a)]`
      have hb : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 ha1
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hk0 1 one_pos) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
        have h := (D.slowIntegral_dilate_bounds hc (mul_pos ha hx) hb).1
        rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h
      · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
        have h := (D.slowIntegral_dilate_bounds hc (mul_pos ha hx) hb).2
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul, Real.log_inv] at h
        rw [one_mul, abs_of_nonpos (Real.log_nonpos ha.le ha1)]
        exact h
    · -- `x ≤ ax`: the integral lies in `[-(c - k(ax)) log a, 0]`
      have hneg : Tendsto (fun x : ℝ => -((c - D.k (a * x)) * |Real.log a|)) (𝓝[>] 0) (𝓝 0) := by
        simpa using (hk0 a ha).neg
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg tendsto_const_nhds ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
        have h := (D.slowIntegral_dilate_bounds hc hx ha1).2
        rw [intervalIntegral.integral_symm, abs_of_nonneg (Real.log_nonneg ha1)]
        linarith
      · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
        have h := (D.slowIntegral_dilate_bounds hc hx ha1).1
        rw [intervalIntegral.integral_symm]
        linarith
  have := (Real.continuous_exp.tendsto 0).comp hlim
  rw [Real.exp_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  exact (hratio x hx).symm

/-- **`prop:isotropic-exponent-profile`(1), the convergent case**: if `(c - k_d(u))/u` is
integrable on `(0,1]`, then `K(x) → K(0+) = exp ∫_0^1 (c - k_d(u)) du/u` as `x ↓ 0`,
`K(0+) ≥ 1`, and `K(x) ≤ K(0+)` for `0 < x ≤ 1` (with the monotonicity of `slowFactor_basic`:
`K(x)` increases to `K(0+)`). -/
theorem slowFactor_tendsto_of_integrable (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    (hI : IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto D.slowFactor (𝓝[>] 0) (𝓝 D.slowFactorZero) ∧ 1 ≤ D.slowFactorZero ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, D.slowFactor x ≤ D.slowFactorZero := by
  set c := D.profileAtOrigin.toReal with hcdef
  set f : ℝ → ℝ := fun u => (c - D.k u) / u with hf
  have hnn : ∀ u ∈ Ioc (0 : ℝ) 1, 0 ≤ f u := fun u hu => D.slowIntegrand_nonneg hc hu.1
  have hII : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hI
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · have hcont := intervalIntegral.continuousOn_primitive_interval' (a := 1) hII right_mem_uIcc
    rw [uIcc_of_le zero_le_one] at hcont
    have h0 : ContinuousWithinAt (fun b => ∫ u in (1 : ℝ)..b, f u) (Icc 0 1) 0 :=
      hcont 0 ⟨le_rfl, zero_le_one⟩
    have h1 : Tendsto (fun b => ∫ u in (1 : ℝ)..b, f u) (𝓝[>] 0) (𝓝 (∫ u in (1 : ℝ)..0, f u)) := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT (zero_lt_one' ℝ)]
      exact h0.tendsto.mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
    have h2 := (Real.continuous_exp.tendsto _).comp h1.neg
    have e : -(∫ u in (1 : ℝ)..0, f u) = ∫ u in Ioc (0 : ℝ) 1, f u := by
      rw [← intervalIntegral.integral_symm, intervalIntegral.integral_of_le zero_le_one]
    rw [e] at h2
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply, OriginDatum.slowFactor]
    rw [intervalIntegral.integral_symm, neg_neg]
  · simp only [OriginDatum.slowFactorZero]
    exact Real.one_le_exp (setIntegral_nonneg measurableSet_Ioc hnn)
  · simp only [OriginDatum.slowFactor, OriginDatum.slowFactorZero]
    refine Real.exp_le_exp.2 ?_
    rw [intervalIntegral.integral_of_le hx.2]
    exact setIntegral_mono_set hI
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hnn))
      (Filter.Eventually.of_forall (Ioc_subset_Ioc_left hx.1.le))

/-- **`prop:isotropic-exponent-profile`(1), the divergent case**: if `(c - k_d(u))/u` is not
integrable on `(0,1]`, then `K(x) → ∞` as `x ↓ 0`. -/
theorem slowFactor_tendsto_atTop (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    (hI : ¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto D.slowFactor (𝓝[>] 0) atTop := by
  set c := D.profileAtOrigin.toReal with hcdef
  set f : ℝ → ℝ := fun u => (c - D.k u) / u with hf
  have hanti := (slowFactor_basic D hc).2.2.1
  -- the integrals `∫_x^1 f` are unbounded
  have hunb : ∀ M : ℝ, ∃ x ∈ Ioc (0 : ℝ) 1, M < ∫ u in x..1, f u := by
    intro M
    by_contra hcon
    push Not at hcon
    refine hI (integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := M)
      (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (l := atTop) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat (Filter.Eventually.of_forall fun n => ?_))
    · have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn1).1
        (D.intervalIntegrable_slowIntegrand hn one_pos)
    · have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h := hcon _ ⟨hn, hn1⟩
      rw [intervalIntegral.integral_of_le hn1] at h
      refine le_trans (le_of_eq ?_) h
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      exact Real.norm_of_nonneg (D.slowIntegrand_nonneg hc (lt_trans hn hu.1))
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨x₀, hx₀, hM⟩ := hunb (Real.log (max M 1))
  have hmem : Ioo (0 : ℝ) x₀ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hx₀.1
  filter_upwards [hmem] with x hx
  have hx1 : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2.le hx₀.2⟩
  have h1 : D.slowFactor x₀ ≤ D.slowFactor x := hanti hx1 hx₀ hx.2.le
  have h2 : max M 1 < D.slowFactor x₀ := by
    simp only [OriginDatum.slowFactor]
    rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right M 1))]
    exact Real.exp_lt_exp.2 hM
  exact le_trans (le_max_left M 1) (le_trans h2.le h1)

/-! ## The tail integral of the profile through `K` -/

/-- `r ↦ k_d(r)/r` is integrable on `(x, ∞)` for `x > 0`. -/
theorem OriginDatum.integrableOn_k_div_Ioi (D : OriginDatum d) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r => D.k r / r) (Ioi x) := by
  have hmeas : AEMeasurable (fun r => D.k r / r) (volume.restrict (Ioi (0 : ℝ))) := by
    have hKm : Measurable ((Ioi (0 : ℝ)).indicator D.k) :=
      measurable_indicator_Ioi_of_antitoneOn D.k_antitone
    refine (hKm.div measurable_id).aemeasurable.congr ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun r (hr : 0 < r) => ?_))
    simp only [id, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
  have h1 : IntegrableOn (fun r => D.k r / r) (Ioi 1) := by
    refine ⟨(hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one)
      le_rfl)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 D.integrable_at_top)
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
    rw [Real.enorm_eq_ofReal (div_nonneg (D.k_nonneg r (lt_trans one_pos hr))
      (lt_trans one_pos hr).le)]
  rcases le_total 1 x with h | h
  · exact h1.mono_set (Ioi_subset_Ioi h)
  · rw [← Ioc_union_Ioi_eq_Ioi h]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1
      (D.intervalIntegrable_k_div hx h)).union h1

/-- `C_k = ∫_1^∞ k_d(r) dr/r` as a Bochner integral. -/
theorem OriginDatum.tailConst_eq_integral (D : OriginDatum d) :
    D.tailConst = ∫ r in Ioi (1 : ℝ), D.k r / r := by
  have hint := D.integrableOn_k_div_Ioi one_pos
  rw [OriginDatum.tailConst, integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : 1 < r) =>
      div_nonneg (D.k_nonneg r (lt_trans one_pos hr)) (lt_trans one_pos hr).le))
    hint.aestronglyMeasurable]

/-- **`eq:profile-tail`**: for `ρ ≥ 1`,
`∫_{1/ρ}^∞ k_d(r) dr/r = c log ρ - log K(1/ρ) + C_k`. -/
theorem integral_k_div_Ioi_eq (D : OriginDatum d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∫ r in Ioi ρ⁻¹, D.k r / r =
      D.profileAtOrigin.toReal * Real.log ρ - Real.log (D.slowFactor ρ⁻¹) + D.tailConst := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hx : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hx1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  set c := D.profileAtOrigin.toReal with hcdef
  have hsplit : ∫ r in Ioi ρ⁻¹, D.k r / r
      = (∫ r in ρ⁻¹..1, D.k r / r) + ∫ r in Ioi (1 : ℝ), D.k r / r := by
    rw [← Ioc_union_Ioi_eq_Ioi hx1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx1).1 (D.intervalIntegrable_k_div hx hx1))
      (D.integrableOn_k_div_Ioi one_pos), intervalIntegral.integral_of_le hx1]
  have hiinv : IntervalIntegrable (fun v : ℝ => c * v⁻¹) volume ρ⁻¹ 1 := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul
      (continuousOn_inv₀.mono fun v hv => ?_))
    rw [uIcc_of_le hx1] at hv
    exact ne_of_gt (lt_of_lt_of_le hx hv.1)
  have hk : ∫ r in ρ⁻¹..1, D.k r / r
      = c * Real.log ρ - ∫ u in ρ⁻¹..1, (c - D.k u) / u := by
    have hlog : ∫ v in ρ⁻¹..1, c * v⁻¹ = c * Real.log ρ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx one_pos, one_div, inv_inv]
    rw [← hlog, ← intervalIntegral.integral_sub hiinv
      (D.intervalIntegrable_slowIntegrand hx one_pos)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    change D.k u / u = c * u⁻¹ - (c - D.k u) / u
    ring
  rw [hsplit, hk, ← D.tailConst_eq_integral]
  simp only [OriginDatum.slowFactor, Real.log_exp]
  rfl

end AffineHemigroup
