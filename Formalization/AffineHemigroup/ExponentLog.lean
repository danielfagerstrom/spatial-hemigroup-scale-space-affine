/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginDecay
import AffineHemigroup.OriginBoundedness
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `lem:isotropic-exponent-log`(2): the exponent is logarithmic

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:isotropic-exponent-log`(2). Wave 2,
group A (Q-0281).

The blueprint's route. **One variable**: for `b ≥ 1`, `φ(bs) - φ(s) = ∫_0^∞ (1 - cos(us)) h_b(u) du`
with `h_b(u) = (k_d(u/b) - k_d(u))/u ≥ 0` (`cosProfileL_dilate`, the substitution `u = br`);
`∫ h_b = c log b` by truncation, `∫_ε^N h_b = ∫_{ε/b}^ε k_d(v) dv/v - ∫_{N/b}^N k_d(v) dv/v`
(`integral_hb`); the Riemann–Lebesgue lemma (Mathlib's `Real.tendsto_integral_exp_smul_cocompact`)
kills `∫ cos(us) h_b(u) du`. **The sphere**: `F_d(bρe₁) - F_d(ρe₁)` is the sphere average of the
one-variable difference at `s = ρ|⟨e₁,η⟩|`, which tends to `c log b` off the null great subsphere and
is bounded by `2c|log b|`; dominated convergence, and the radiality of `F_d`, give the limit along
the cocompact filter.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace FourierTransform

variable {d : ℕ}

/-! ## The profile at the two ends -/

/-- `k_d ≤ c` on `(0,∞)`, as reals, when `c` is finite. -/
theorem OriginDatum.k_le_toReal (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {r : ℝ}
    (hr : 0 < r) : D.k r ≤ D.profileAtOrigin.toReal := by
  have h := D.ofReal_k_le hr
  rw [← ENNReal.ofReal_toReal hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

/-- `k_d(0+) = c`, as reals, when `c` is finite. -/
theorem OriginDatum.tendsto_k_zero (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) :
    Tendsto D.k (𝓝[>] 0) (𝓝 D.profileAtOrigin.toReal) := by
  have h := (ENNReal.tendsto_toReal hc).comp D.tendsto_profileAtOrigin
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp [ENNReal.toReal_ofReal (D.k_nonneg r hr)]

/-- `k_d(r) → 0` as `r → ∞`: a nonincreasing `k_d ≥ ℓ > 0` would make `∫₁^∞ k_d(r) dr/r` diverge. -/
theorem OriginDatum.tendsto_k_atTop (D : OriginDatum d) : Tendsto D.k atTop (𝓝 0) := by
  have hanti : Antitone fun r : ℝ => D.k (max r 1) := fun x y hxy =>
    D.k_antitone (show max x 1 ∈ Ioi (0 : ℝ) from lt_of_lt_of_le one_pos (le_max_right x 1))
      (show max y 1 ∈ Ioi (0 : ℝ) from lt_of_lt_of_le one_pos (le_max_right y 1))
      (max_le_max hxy le_rfl)
  have hbdd : BddBelow (range fun r : ℝ => D.k (max r 1)) :=
    ⟨0, by
      rintro _ ⟨r, rfl⟩
      exact D.k_nonneg _ (show max r 1 ∈ Ioi (0 : ℝ) from lt_of_lt_of_le one_pos (le_max_right r 1))⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set ℓ := ⨅ r : ℝ, D.k (max r 1) with hℓ
  have hℓ0 : 0 ≤ ℓ := le_ciInf fun r =>
    D.k_nonneg _ (show max r 1 ∈ Ioi (0 : ℝ) from lt_of_lt_of_le one_pos (le_max_right r 1))
  have hℓeq : ℓ = 0 := by
    by_contra hne
    have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ0 (Ne.symm hne)
    have hge : ∀ r : ℝ, 1 < r → ℓ ≤ D.k r := fun r hr => by
      have := ciInf_le hbdd r
      rwa [max_eq_left hr.le] at this
    have htop : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (ℓ / r) = ⊤ := by
      have h := lintegral_Ioi_one_rpow_eq_top (a := -1) le_rfl
      have hcongr : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (ℓ / r)
          = ENNReal.ofReal ℓ * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ (-1 : ℝ)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
        rw [← ENNReal.ofReal_mul hℓ0, Real.rpow_neg_one, div_eq_mul_inv]
      rw [hcongr, h, ENNReal.mul_top (by simp [hℓpos])]
    refine D.integrable_at_top (eq_top_iff.mpr (htop ▸ ?_))
    refine setLIntegral_mono' measurableSet_Ioi fun r (hr : 1 < r) => ENNReal.ofReal_le_ofReal ?_
    exact div_le_div_of_nonneg_right (hge r hr) (by linarith)
  rw [hℓeq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [max_eq_left hr]

/-! ## The Frullani integral of a nonincreasing profile -/

/-- On a compact subinterval of `(0,∞)` the function `v ↦ k_d(v)/v` is integrable. -/
theorem OriginDatum.intervalIntegrable_k_div (D : OriginDatum d) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : IntervalIntegrable (fun v => D.k v / v) volume x y := by
  have hk : IntervalIntegrable D.k volume x y := by
    refine AntitoneOn.intervalIntegrable (D.k_antitone.mono ?_)
    intro v hv
    rw [uIcc_of_le hxy] at hv
    exact lt_of_lt_of_le hx hv.1
  have hinv : ContinuousOn (fun v : ℝ => v⁻¹) (uIcc x y) := by
    refine continuousOn_inv₀.mono fun v hv => ?_
    rw [uIcc_of_le hxy] at hv
    exact ne_of_gt (lt_of_lt_of_le hx hv.1)
  simpa [div_eq_mul_inv] using hk.mul_continuousOn hinv

/-- On a compact subinterval of `(0,∞)` the function `u ↦ k_d(u/b)/u` is integrable, `b > 0`. -/
theorem OriginDatum.intervalIntegrable_k_div_scaled (D : OriginDatum d) {x y b : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hb : 0 < b) : IntervalIntegrable (fun u => D.k (u / b) / u) volume x y := by
  have hk : IntervalIntegrable (fun u => D.k (u / b)) volume x y := by
    refine AntitoneOn.intervalIntegrable fun u hu v hv huv => ?_
    rw [uIcc_of_le hxy] at hu hv
    exact D.k_antitone (div_pos (lt_of_lt_of_le hx hu.1) hb) (div_pos (lt_of_lt_of_le hx hv.1) hb)
      (div_le_div_of_nonneg_right huv hb.le)
  have hinv : ContinuousOn (fun v : ℝ => v⁻¹) (uIcc x y) := by
    refine continuousOn_inv₀.mono fun v hv => ?_
    rw [uIcc_of_le hxy] at hv
    exact ne_of_gt (lt_of_lt_of_le hx hv.1)
  simpa [div_eq_mul_inv] using hk.mul_continuousOn hinv

/-- Bounds on `∫_x^{bx} k_d(v) dv/v` for a profile between `m` and `M` there:
`m log b ≤ ∫ ≤ M log b`. -/
theorem OriginDatum.integral_k_div_bounds (D : OriginDatum d) {x b m M : ℝ} (hx : 0 < x)
    (hb : 1 ≤ b) (hm : ∀ v ∈ Icc x (b * x), m ≤ D.k v) (hM : ∀ v ∈ Icc x (b * x), D.k v ≤ M) :
    m * Real.log b ≤ ∫ v in x..(b * x), D.k v / v ∧ ∫ v in x..(b * x), D.k v / v ≤ M * Real.log b := by
  have hxb : x ≤ b * x := le_mul_of_one_le_left hx.le hb
  have hlog : ∫ v in x..(b * x), v⁻¹ = Real.log b := by
    rw [integral_inv_of_pos hx (by positivity), mul_div_assoc, div_self hx.ne', mul_one]
  have hiinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume x (b * x) := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
    rw [uIcc_of_le hxb] at hv
    exact ne_of_gt (lt_of_lt_of_le hx hv.1)
  have hik := D.intervalIntegrable_k_div hx hxb
  constructor
  · rw [← hlog, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxb (hiinv.const_mul m) hik fun v hv => ?_
    have hv0 : 0 < v := lt_of_lt_of_le hx hv.1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hm v hv) (inv_nonneg.mpr hv0.le)
  · rw [← hlog, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxb hik (hiinv.const_mul M) fun v hv => ?_
    have hv0 : 0 < v := lt_of_lt_of_le hx hv.1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM v hv) (inv_nonneg.mpr hv0.le)

/-- The Frullani-type identity behind `lem:isotropic-exponent-log`(2): for `b ≥ 1`,
`∫_0^∞ (k_d(u/b) - k_d(u)) du/u = c log b`, as a lower integral. -/
theorem OriginDatum.lintegral_hb (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {b : ℝ}
    (hb : 1 ≤ b) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((D.k (u / b) - D.k u) / u)
      = ENNReal.ofReal (D.profileAtOrigin.toReal * Real.log b) := by
  set c := D.profileAtOrigin.toReal with hcdef
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  set h : ℝ → ℝ := fun u => (D.k (u / b) - D.k u) / u with hh
  have hhnn : ∀ u : ℝ, 0 < u → 0 ≤ h u := by
    intro u hu
    refine div_nonneg (sub_nonneg.mpr (D.k_antitone (div_pos hu hb0) hu ?_)) hu.le
    exact div_le_self hu.le hb
  -- the truncated integrals
  have htrunc : ∀ x N : ℝ, 0 < x → b * x ≤ N →
      ∫ u in x..N, h u = (∫ v in (x / b)..x, D.k v / v) - ∫ v in (N / b)..N, D.k v / v := by
    intro x N hx hxN
    have hxN' : x ≤ N := le_trans (le_mul_of_one_le_left hx.le hb) hxN
    have hxb : x / b ≤ x := div_le_self hx.le hb
    have hxb0 : 0 < x / b := div_pos hx hb0
    have hNb : x ≤ N / b := by rw [le_div_iff₀ hb0]; linarith
    have hNb' : N / b ≤ N := div_le_self (le_trans hx.le hxN') hb
    have hcomp : ∫ u in x..N, D.k (u / b) / u = ∫ v in (x / b)..(N / b), D.k v / v := by
      have h1 : ∫ u in x..N, D.k (u / b) / u = ∫ u in x..N, b⁻¹ * (D.k (u / b) / (u / b)) := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [uIcc_of_le hxN'] at hu
        have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hx hu.1)
        field_simp
      rw [h1, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_div (fun v => D.k v / v) hb0.ne', smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hb0.ne', one_mul]
    have hi1 := D.intervalIntegrable_k_div hxb0 hxb
    have hi2 := D.intervalIntegrable_k_div hx hNb
    have hi3 := D.intervalIntegrable_k_div (lt_of_lt_of_le hx hNb) hNb'
    have hik2 : IntervalIntegrable (fun u => D.k (u / b) / u) volume x N :=
      D.intervalIntegrable_k_div_scaled hx hxN' hb0
    have hik1 : IntervalIntegrable (fun u => D.k u / u) volume x N :=
      D.intervalIntegrable_k_div hx hxN'
    rw [show (fun u => h u) = fun u => D.k (u / b) / u - D.k u / u by
        funext u; rw [hh]; ring,
      intervalIntegral.integral_sub hik2 hik1, hcomp,
      ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      ← intervalIntegral.integral_add_adjacent_intervals hi2 hi3]
    ring
  -- the bounds
  have hbounds : ∀ x N : ℝ, 0 < x → b * x ≤ N →
      D.k x * Real.log b - D.k (N / b) * Real.log b ≤ ∫ u in x..N, h u ∧
        ∫ u in x..N, h u ≤ c * Real.log b := by
    intro x N hx hxN
    have hxb0 : 0 < x / b := div_pos hx hb0
    have hN0 : 0 < N / b := by
      have : 0 < N := lt_of_lt_of_le (by positivity) hxN
      positivity
    rw [htrunc x N hx hxN]
    have e1 : b * (x / b) = x := by field_simp
    have e2 : b * (N / b) = N := by field_simp
    have hA := D.integral_k_div_bounds hxb0 hb (m := D.k x) (M := c)
      (fun v hv => D.k_antitone (lt_of_lt_of_le hxb0 hv.1) hx (by rw [e1] at hv; exact hv.2))
      (fun v hv => D.k_le_toReal hc (lt_of_lt_of_le hxb0 hv.1))
    have hB := D.integral_k_div_bounds hN0 hb (m := 0) (M := D.k (N / b))
      (fun v hv => D.k_nonneg v (lt_of_lt_of_le hN0 hv.1))
      (fun v hv => D.k_antitone hN0 (lt_of_lt_of_le hN0 hv.1) hv.1)
    rw [e1] at hA
    rw [e2] at hB
    constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]
  -- the sequence
  set xn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hxn
  set Nn : ℕ → ℝ := fun n => b * ((n : ℝ) + 1) with hNn
  have hxn0 : ∀ n, 0 < xn n := fun n => by positivity
  have hxN : ∀ n, b * xn n ≤ Nn n := by
    intro n
    have h1 : xn n ≤ 1 := by
      simp only [hxn]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hNn]
    nlinarith
  set S : ℕ → Set ℝ := fun n => Ioo (xn n) (Nn n) with hS
  have hSmono : Monotone S := by
    intro m n hmn
    refine Ioo_subset_Ioo ?_ ?_
    · simp only [hxn]; gcongr
    · simp only [hNn]; gcongr
  have hSunion : (⋃ n, S n) = Ioi 0 := by
    ext u
    simp only [mem_iUnion, mem_Ioo, mem_Ioi, hS]
    constructor
    · rintro ⟨n, hn, -⟩; exact lt_trans (hxn0 n) hn
    · intro hu
      obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt hu
      obtain ⟨n2, hn2⟩ := exists_nat_gt (u / b)
      refine ⟨max n1 n2, lt_of_le_of_lt ?_ hn1, ?_⟩
      · simp only [hxn]; gcongr; exact_mod_cast le_max_left n1 n2
      · simp only [hNn]
        have : u / b < (max n1 n2 : ℕ) + 1 := by
          have : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
          linarith
        rw [div_lt_iff₀ hb0] at this
        linarith
  -- the lower integrals on the truncations
  have hSval : ∀ n, ∫⁻ u in S n, ENNReal.ofReal (h u) = ENNReal.ofReal (∫ u in (xn n)..(Nn n), h u) := by
    intro n
    have hle : xn n ≤ Nn n := le_trans (le_mul_of_one_le_left (hxn0 n).le hb) (hxN n)
    have hint : IntervalIntegrable h volume (xn n) (Nn n) := by
      refine ((D.intervalIntegrable_k_div_scaled (hxn0 n) hle hb0).sub
        (D.intervalIntegrable_k_div (hxn0 n) hle)).congr fun u _ => ?_
      show D.k (u / b) / u - D.k u / u = (D.k (u / b) - D.k u) / u
      ring
    have hint' : IntegrableOn h (Ioo (xn n) (Nn n)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint).mono_set Ioo_subset_Ioc_self
    have hnn' : 0 ≤ᵐ[volume.restrict (Ioo (xn n) (Nn n))] h :=
      (ae_restrict_iff' measurableSet_Ioo).mpr (.of_forall fun u hu =>
        hhnn u (lt_trans (hxn0 n) hu.1))
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint' hnn']
  -- the two limits
  have hlimL : Tendsto (fun n => ∫⁻ u in S n, ENNReal.ofReal (h u)) atTop
      (𝓝 (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (h u))) := by
    have hmeasS : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Ioo
    have hm := tendsto_measure_iUnion_atTop (μ := volume.withDensity fun u => ENNReal.ofReal (h u))
      hSmono
    rw [hSunion, withDensity_apply _ measurableSet_Ioi] at hm
    refine hm.congr fun n => ?_
    rw [Function.comp_apply, withDensity_apply _ (hmeasS n)]
  have hlimR : Tendsto (fun n => ∫ u in (xn n)..(Nn n), h u) atTop (𝓝 (c * Real.log b)) := by
    have hx : Tendsto xn atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        tendsto_one_div_add_atTop_nhds_zero_nat (.of_forall hxn0)
    have hk1 : Tendsto (fun n => D.k (xn n)) atTop (𝓝 c) := (D.tendsto_k_zero hc).comp hx
    have hN : Tendsto (fun n => Nn n / b) atTop atTop := by
      have : (fun n => Nn n / b) = fun n : ℕ => (n : ℝ) + 1 := by
        funext n; simp only [hNn]; field_simp
      rw [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hk2 : Tendsto (fun n => D.k (Nn n / b)) atTop (𝓝 0) := D.tendsto_k_atTop.comp hN
    have hlow : Tendsto (fun n => D.k (xn n) * Real.log b - D.k (Nn n / b) * Real.log b) atTop
        (𝓝 (c * Real.log b - 0 * Real.log b)) :=
      (hk1.mul_const _).sub (hk2.mul_const _)
    rw [zero_mul, sub_zero] at hlow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hbounds _ _ (hxn0 n) (hxN n)).1) (fun n => (hbounds _ _ (hxn0 n) (hxN n)).2)
  have hlimR' := (ENNReal.continuous_ofReal.tendsto _).comp hlimR
  refine tendsto_nhds_unique hlimL (hlimR'.congr fun n => ?_)
  simp only [Function.comp_apply]
  exact (hSval n).symm

/-! ## One variable: `φ(bs) - φ(s) → c log b` -/

/-- `h_b(u) = (k_d(u/b) - k_d(u))/u` agrees on `(0,∞)` with a measurable function. -/
theorem OriginDatum.aemeasurable_hb (D : OriginDatum d) {b : ℝ} (hb : 0 < b) :
    AEMeasurable (fun u => (D.k (u / b) - D.k u) / u) (volume.restrict (Ioi 0)) := by
  set K := (Ioi (0 : ℝ)).indicator D.k with hK
  have hKm : Measurable K := measurable_indicator_Ioi_of_antitoneOn D.k_antitone
  have hm : Measurable fun u : ℝ => (K (u / b) - K u) / u :=
    ((hKm.comp (measurable_id.div_const b)).sub hKm).div measurable_id
  refine hm.aemeasurable.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
    (.of_forall fun u (hu : 0 < u) => ?_))
  simp only [hK, indicator_of_mem (show u / b ∈ Ioi (0 : ℝ) from div_pos hu hb),
    indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]

/-- `h_b` is integrable on `(0,∞)` with integral `c log b`, for `b ≥ 1`. -/
theorem OriginDatum.integrable_hb (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {b : ℝ}
    (hb : 1 ≤ b) :
    IntegrableOn (fun u => (D.k (u / b) - D.k u) / u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (D.k (u / b) - D.k u) / u = D.profileAtOrigin.toReal * Real.log b := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hmeas := D.aemeasurable_hb hb0
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun u => (D.k (u / b) - D.k u) / u := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
    exact div_nonneg (sub_nonneg.mpr (D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb)))
      hu.le
  have hL := D.lintegral_hb hc hb
  have hint : IntegrableOn (fun u => (D.k (u / b) - D.k u) / u) (Ioi 0) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr (hL ▸ ENNReal.ofReal_ne_top))
    refine lintegral_congr_ae ?_
    filter_upwards [hnn] with u hu
    rw [Real.enorm_eq_ofReal hu]
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (Real.log_nonneg hb))]

/-- **The dilation** `u = br`: `φ(bs) = ∫_0^∞ (1 - cos(us)) k_d(u/b) du/u`. -/
theorem OriginDatum.cosProfileL_dilate (D : OriginDatum d) {b : ℝ} (hb : 0 < b) (s : ℝ) :
    cosProfileL D.k (b * s) = ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (1 - Real.cos (u * s)) * ENNReal.ofReal (D.k (u / b) / u) := by
  have himg : (fun u : ℝ => u / b) '' Ioi 0 = Ioi 0 := by
    ext r; constructor
    · rintro ⟨u, hu, rfl⟩; exact div_pos hu hb
    · intro hr; exact ⟨r * b, mul_pos hr hb, by field_simp⟩
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => u / b) (1 / b) (Ioi 0) u :=
    fun u _ => ((hasDerivAt_id u).div_const b).hasDerivWithinAt.congr_deriv (by simp)
  have hinj : InjOn (fun u : ℝ => u / b) (Ioi 0) := fun u _ v _ h => by
    simp only at h; field_simp at h; exact h
  have hsub : cosProfileL D.k (b * s) = ∫⁻ r in (fun u : ℝ => u / b) '' Ioi 0,
      ENNReal.ofReal (1 - Real.cos (r * (b * s))) * ENNReal.ofReal (D.k r / r) := by
    rw [himg]; rfl
  rw [hsub, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  have hk := D.k_nonneg (u / b) (div_pos hu hb)
  rw [mul_left_comm, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
  congr 2
  · field_simp
  · field_simp

/-- **The difference formula**: for `b ≥ 1`, `φ(bs) - φ(s) = ∫_0^∞ (1 - cos(us)) h_b(u) du`. -/
theorem OriginDatum.cosProfile_sub (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    {b : ℝ} (hb : 1 ≤ b) (s : ℝ) :
    (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal
      = ∫ u in Ioi (0 : ℝ), (1 - Real.cos (u * s)) * ((D.k (u / b) - D.k u) / u) := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  obtain ⟨hint, -⟩ := D.integrable_hb hc hb
  have hfin : ∀ t, cosProfileL D.k t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      D.integrable_near_zero, ENNReal.mul_ne_top (by norm_num) D.integrable_at_top⟩)
      (cosProfileL_le_sq D.k D.k_nonneg t)
  have hsplit : cosProfileL D.k (b * s) = cosProfileL D.k s + ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos (u * s)) * ((D.k (u / b) - D.k u) / u)) := by
    rw [D.cosProfileL_dilate hb0 s, cosProfileL, ← lintegral_add_right']
    · refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
      have h1 : 0 ≤ 1 - Real.cos (u * s) := by linarith [Real.cos_le_one (u * s)]
      have hk := D.k_nonneg u hu
      have hkb : D.k u ≤ D.k (u / b) := D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb)
      rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add
        (mul_nonneg h1 (div_nonneg hk hu.le))
        (mul_nonneg h1 (div_nonneg (by linarith) hu.le))]
      congr 1
      field_simp
      ring
    · exact ((by fun_prop : Measurable fun u : ℝ => 1 - Real.cos (u * s)).aemeasurable.mul
        (D.aemeasurable_hb hb0)).ennreal_ofReal
  have hY : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (u * s)) *
      ((D.k (u / b) - D.k u) / u)) ≠ ⊤ := by
    have := hfin (b * s)
    rw [hsplit] at this
    exact (ENNReal.add_ne_top.mp this).2
  rw [hsplit, ENNReal.toReal_add (hfin s) hY, add_sub_cancel_left,
    integral_eq_lintegral_of_nonneg_ae]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u (hu : 0 < u) => ?_)
    exact mul_nonneg (by linarith [Real.cos_le_one (u * s)])
      (div_nonneg (sub_nonneg.mpr (D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb))) hu.le)
  · exact ((by fun_prop : Measurable fun u : ℝ => 1 - Real.cos (u * s)).aemeasurable.mul
      (D.aemeasurable_hb hb0)).aestronglyMeasurable

/-- **The Riemann–Lebesgue lemma on `(0,∞)`**, cosine form: for `h` integrable on `(0,∞)`,
`∫_0^∞ cos(us) h(u) du → 0` as `s → ∞`. Mathlib types only. -/
theorem tendsto_integral_cos_mul_Ioi {h : ℝ → ℝ} (hh : IntegrableOn h (Ioi 0)) :
    Tendsto (fun s : ℝ => ∫ u in Ioi (0 : ℝ), Real.cos (u * s) * h u) atTop (𝓝 0) := by
  set H : ℝ → ℂ := fun u => (((Ioi (0 : ℝ)).indicator h u : ℝ) : ℂ) with hH
  have hRL := Real.tendsto_integral_exp_smul_cocompact H
  have hw : Tendsto (fun s : ℝ => s / (2 * Real.pi)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h1 := (Complex.continuous_re.tendsto 0).comp (hRL.comp hw)
  rw [Complex.zero_re] at h1
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply]
  have hInd : Integrable ((Ioi (0 : ℝ)).indicator h) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hh
  have hHint : Integrable H := hInd.ofReal
  have key : ∀ v : ℝ, (𝐞 (-(v * (s / (2 * Real.pi)))) • H v).re
      = Real.cos (v * s) * (Ioi (0 : ℝ)).indicator h v := by
    intro v
    simp only [hH, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    congr 1
    rw [show 2 * Real.pi * -(v * (s / (2 * Real.pi))) = -(v * s) by field_simp, Real.cos_neg]
  have hint : Integrable fun v : ℝ => 𝐞 (-(v * (s / (2 * Real.pi)))) • H v := by
    refine Integrable.mono' hHint.norm ?_ (ae_of_all _ fun v => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul hHint.aestronglyMeasurable
    · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [← RCLike.re_to_complex, ← integral_re hint, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [RCLike.re_to_complex, key v]
  by_cases hv : v ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hv, indicator_of_mem hv]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]

/-- **One variable, `b ≥ 1`**: `φ(bs) - φ(s) → c log b` as `s → ∞`, and
`0 ≤ φ(bs) - φ(s) ≤ 2c log b` for every `s`. -/
theorem OriginDatum.cosProfile_limit_one_le (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    {b : ℝ} (hb : 1 ≤ b) :
    Tendsto (fun s => (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal) atTop
        (𝓝 (D.profileAtOrigin.toReal * Real.log b)) ∧
      ∀ s, 0 ≤ (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal ∧
        (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal
          ≤ 2 * (D.profileAtOrigin.toReal * Real.log b) := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  obtain ⟨hint, hval⟩ := D.integrable_hb hc hb
  set h := fun u => (D.k (u / b) - D.k u) / u with hh
  have hnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ h u := fun u (hu : 0 < u) =>
    div_nonneg (sub_nonneg.mpr (D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb))) hu.le
  have hcosint : ∀ s : ℝ, IntegrableOn (fun u => Real.cos (u * s) * h u) (Ioi 0) := by
    intro s
    refine Integrable.mono' hint.norm (((by fun_prop : Measurable fun u : ℝ =>
      Real.cos (u * s)).aemeasurable.mul (D.aemeasurable_hb hb0)).aestronglyMeasurable)
      (ae_of_all _ fun u => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using Real.abs_cos_le_one (u * s))
  have hsplit : ∀ s, (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal
      = D.profileAtOrigin.toReal * Real.log b - ∫ u in Ioi (0 : ℝ), Real.cos (u * s) * h u := by
    intro s
    rw [D.cosProfile_sub hc hb s, ← hval, ← integral_sub hint (hcosint s)]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hh]; ring
  refine ⟨?_, fun s => ⟨?_, ?_⟩⟩
  · have h1 := (tendsto_integral_cos_mul_Ioi hint)
    have h2 := (tendsto_const_nhds (x := D.profileAtOrigin.toReal * Real.log b)).sub h1
    rw [sub_zero] at h2
    exact h2.congr fun s => (hsplit s).symm
  · rw [D.cosProfile_sub hc hb s]
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    exact mul_nonneg (by linarith [Real.cos_le_one (u * s)]) (hnn u hu)
  · rw [D.cosProfile_sub hc hb s, ← hval, ← integral_const_mul]
    refine setIntegral_mono_on ?_ (hint.const_mul 2) measurableSet_Ioi fun u hu => ?_
    · refine Integrable.mono' (hint.const_mul 2) (((by fun_prop : Measurable fun u : ℝ =>
        1 - Real.cos (u * s)).aemeasurable.mul (D.aemeasurable_hb hb0)).aestronglyMeasurable)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => ?_))
      rw [norm_mul, Real.norm_of_nonneg (hnn u hu), Real.norm_of_nonneg
        (by linarith [Real.cos_le_one (u * s)])]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.neg_one_le_cos (u * s)]) (hnn u hu)
    · exact mul_le_mul_of_nonneg_right (by linarith [Real.neg_one_le_cos (u * s)]) (hnn u hu)

/-- **One variable, every `b > 0`**: `φ(bs) - φ(s) → c log b` as `s → ∞`, and
`|φ(bs) - φ(s)| ≤ 2c|log b|` for every `s`. -/
theorem OriginDatum.cosProfile_limit (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun s => (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal) atTop
        (𝓝 (D.profileAtOrigin.toReal * Real.log b)) ∧
      ∀ s, |(cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal|
        ≤ 2 * (D.profileAtOrigin.toReal * |Real.log b|) := by
  have hc0 : 0 ≤ D.profileAtOrigin.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt 1 b with hb1 | hb1
  · obtain ⟨hl, hbd⟩ := D.cosProfile_limit_one_le hc hb1
    refine ⟨hl, fun s => ?_⟩
    rw [abs_of_nonneg (hbd s).1, abs_of_nonneg (Real.log_nonneg hb1)]
    exact (hbd s).2
  · have hb' : 1 ≤ b⁻¹ := one_le_inv_iff₀.mpr ⟨hb, hb1.le⟩
    obtain ⟨hl, hbd⟩ := D.cosProfile_limit_one_le hc hb'
    have heq : ∀ s, (cosProfileL D.k (b * s)).toReal - (cosProfileL D.k s).toReal
        = -((cosProfileL D.k (b⁻¹ * (b * s))).toReal - (cosProfileL D.k (b * s)).toReal) := by
      intro s
      rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]; ring
    have hlog : Real.log b⁻¹ = -Real.log b := Real.log_inv b
    refine ⟨?_, fun s => ?_⟩
    · have h1 := (hl.comp (tendsto_id.const_mul_atTop hb)).neg
      rw [hlog] at h1
      simp only [mul_neg, neg_neg] at h1
      exact h1.congr fun s => (heq s).symm
    · rw [heq s, abs_neg, abs_of_nonneg (hbd (b * s)).1,
        abs_of_nonpos (Real.log_nonpos hb.le hb1.le)]
      have := (hbd (b * s)).2
      rw [hlog] at this
      linarith

/-! ## The sphere average -/

/-- The cosine profile is a measurable function of `s` (through a measurable modification of
`k_d` on `(0,∞)`, which changes no value of `φ`). -/
theorem OriginDatum.measurable_cosProfileL (D : OriginDatum d) : Measurable (cosProfileL D.k) := by
  set K := (Ioi (0 : ℝ)).indicator D.k with hK
  have hKm : Measurable K := measurable_indicator_Ioi_of_antitoneOn D.k_antitone
  have heq : cosProfileL D.k = cosProfileL K := by
    funext s
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hK, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
  rw [heq]
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 - Real.cos (p.2 * p.1)) * ENNReal.ofReal (K p.2 / p.2) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 - Real.cos (p.2 * p.1))).mul
      ((hKm.comp measurable_snd).div measurable_snd).ennreal_ofReal
  exact hm.lintegral_prod_right'

/-- The real exponent as a sphere average, `a = 0`:
`F_d(ξ) = |S^{d-1}|⁻¹ ∫_{S^{d-1}} φ(⟨ξ,η⟩) σ_{d-1}(dη)`. -/
theorem OriginDatum.exponent_eq_integral_sphere (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (ξ : Rd d) :
    D.exponent ξ = (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
      (cosProfileL D.k ⟪ξ, (η : Rd d)⟫).toReal ∂((volume : Measure (Rd d)).toSphere) := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hfin : ∀ t, cosProfileL D.k t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      D.integrable_near_zero, ENNReal.mul_ne_top (by norm_num) D.integrable_at_top⟩)
      (cosProfileL_le_sq D.k D.k_nonneg t)
  rw [OriginDatum.exponent, D.exponentL_eq_sphere hd, ha, zero_mul, zero_div, ENNReal.ofReal_zero,
    zero_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hA.le,
    integral_toReal]
  · exact (D.measurable_cosProfileL.comp (by fun_prop)).aemeasurable
  · exact ae_of_all _ fun η => lt_top_iff_ne_top.mpr (hfin _)

/-- **The sphere average of the one-variable limit**: along a unit vector `e`,
`F_d(bρe) - F_d(ρe) → c log b` as `ρ → ∞`. -/
theorem OriginDatum.tendsto_exponent_dilate (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {b : ℝ} (hb : 0 < b) {e : Rd d} (he : ‖e‖ = 1) :
    Tendsto (fun ρ : ℝ => D.exponent ((b * ρ) • e) - D.exponent (ρ • e)) atTop
      (𝓝 (D.profileAtOrigin.toReal * Real.log b)) := by
  set σ := (volume : Measure (Rd d)).toSphere with hσ
  set c := D.profileAtOrigin.toReal with hcdef
  have hA := (sphereArea_eq_toSphere hd).2
  have he0 : e ≠ 0 := by rw [← norm_ne_zero_iff, he]; exact one_ne_zero
  set φR : ℝ → ℝ := fun s => (cosProfileL D.k s).toReal with hφR
  have hφm : Measurable φR := D.measurable_cosProfileL.ennreal_toReal
  obtain ⟨hlim, hbd⟩ := D.cosProfile_limit hc hb
  -- a uniform bound for `φ` on bounded arguments
  set I0 := ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (D.k r * r) with hI0
  set I1 := ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r) with hI1
  have hφbd : ∀ R s : ℝ, |s| ≤ R → φR s ≤ (ENNReal.ofReal (R ^ 2 / 2) * I0 + 2 * I1).toReal := by
    intro R s hs
    have hfin : ENNReal.ofReal (R ^ 2 / 2) * I0 + 2 * I1 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top D.integrable_near_zero,
        ENNReal.mul_ne_top (by norm_num) D.integrable_at_top⟩
    refine ENNReal.toReal_mono hfin ((cosProfileL_le_sq D.k D.k_nonneg s).trans ?_)
    have : s ^ 2 ≤ R ^ 2 := by
      have := sq_abs s
      nlinarith [abs_nonneg s]
    exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl) le_rfl
  have hφnn : ∀ s, 0 ≤ φR s := fun s => ENNReal.toReal_nonneg
  have hint : ∀ ρ : ℝ, Integrable (fun η : sphere (0 : Rd d) 1 => φR ⟪ρ • e, (η : Rd d)⟫) σ := by
    intro ρ
    refine Integrable.mono' (integrable_const ((ENNReal.ofReal (|ρ| ^ 2 / 2) * I0 + 2 * I1).toReal))
      ((hφm.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun η => ?_)
    rw [Real.norm_of_nonneg (hφnn _)]
    refine hφbd _ _ ?_
    have h1 := abs_real_inner_le_norm (ρ • e) (η : Rd d)
    rw [norm_smul, he, norm_eq_of_mem_sphere η, Real.norm_eq_abs] at h1
    simpa using h1
  -- the difference as one sphere integral
  have hdiff : ∀ ρ : ℝ, D.exponent ((b * ρ) • e) - D.exponent (ρ • e)
      = (sphereArea d)⁻¹ * ∫ η : sphere (0 : Rd d) 1,
          (φR (b * (ρ * ⟪e, (η : Rd d)⟫)) - φR (ρ * ⟪e, (η : Rd d)⟫)) ∂σ := by
    intro ρ
    rw [D.exponent_eq_integral_sphere hd ha, D.exponent_eq_integral_sphere hd ha, ← mul_sub,
      ← integral_sub (by simpa [mul_assoc] using hint (b * ρ)) (hint ρ)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    simp only [hφR, inner_smul_left, RCLike.conj_to_real]
    ring_nf
  -- dominated convergence
  have hdom : Tendsto (fun ρ : ℝ => ∫ η : sphere (0 : Rd d) 1,
      (φR (b * (ρ * ⟪e, (η : Rd d)⟫)) - φR (ρ * ⟪e, (η : Rd d)⟫)) ∂σ) atTop
      (𝓝 (∫ _η : sphere (0 : Rd d) 1, c * Real.log b ∂σ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * (c * |Real.log b|))
      (.of_forall fun ρ => ((hφm.comp (by fun_prop)).sub (hφm.comp (by fun_prop))).aestronglyMeasurable)
      (.of_forall fun ρ => ae_of_all _ fun η => ?_) (integrable_const _) ?_
    · rw [Real.norm_eq_abs]; exact hbd _
    · have hnull := toSphere_inner_eq_zero he0
      have hae : ∀ᵐ η : sphere (0 : Rd d) 1 ∂σ, ⟪e, (η : Rd d)⟫ ≠ 0 := by
        rw [ae_iff]
        exact measure_mono_null (fun η hη => not_not.mp hη) hnull
      filter_upwards [hae] with η hη
      rcases lt_or_gt_of_ne hη with hneg | hpos
      · have ht : Tendsto (fun ρ : ℝ => ρ * -⟪e, (η : Rd d)⟫) atTop atTop :=
          tendsto_id.atTop_mul_const (by linarith)
        refine (hlim.comp ht).congr fun ρ => ?_
        simp only [Function.comp_apply, hφR]
        rw [show b * (ρ * -⟪e, (η : Rd d)⟫) = -(b * (ρ * ⟪e, (η : Rd d)⟫)) by ring,
          show ρ * -⟪e, (η : Rd d)⟫ = -(ρ * ⟪e, (η : Rd d)⟫) by ring, cosProfileL_neg,
          cosProfileL_neg]
      · have ht : Tendsto (fun ρ : ℝ => ρ * ⟪e, (η : Rd d)⟫) atTop atTop :=
          tendsto_id.atTop_mul_const hpos
        exact hlim.comp ht
  have hval : (sphereArea d)⁻¹ * ∫ _η : sphere (0 : Rd d) 1, c * Real.log b ∂σ = c * Real.log b := by
    rw [integral_const, smul_eq_mul, measureReal_def, hσ, ← (sphereArea_eq_toSphere hd).1,
      ENNReal.toReal_ofReal hA.le, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
  rw [← hval]
  refine ((hdom.const_mul _)).congr fun ρ => (hdiff ρ).symm

/-- **`lem:isotropic-exponent-log`(2)**: `F_d(aξ) - F_d(ξ) → c log a` as `|ξ| → ∞`, for every
`a > 0`; equivalently, along a unit vector `e`, `g(u) := F_d(√u e)` has
`g(au) - g(u) → (c/2) log a` as `u → ∞`. -/
theorem isotropic_exponent_log_limit (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) (a : ℝ) (ha' : 0 < a) :
    Tendsto (fun ξ : Rd d => D.exponent (a • ξ) - D.exponent ξ) (cocompact (Rd d))
        (𝓝 (D.profileAtOrigin.toReal * Real.log a)) ∧
      ∀ e : Rd d, ‖e‖ = 1 →
        Tendsto (fun u : ℝ => D.exponent (Real.sqrt (a * u) • e) - D.exponent (Real.sqrt u • e))
          atTop (𝓝 (D.profileAtOrigin.toReal / 2 * Real.log a)) := by
  haveI : NeZero d := ⟨by omega⟩
  set e₁ : Rd d := ebasis (0 : Fin d) with he₁
  have he₁1 : ‖e₁‖ = 1 := by simp [he₁, ebasis]
  refine ⟨?_, fun e he => ?_⟩
  · have h := (D.tendsto_exponent_dilate hd ha hc ha' he₁1).comp
      (tendsto_norm_cocompact_atTop (E := Rd d))
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply]
    rw [D.exponent_eq_of_norm_eq (ξ := a • ξ) (ξ' := (a * ‖ξ‖) • e₁)
        (by rw [norm_smul, norm_smul, he₁1, mul_one, Real.norm_of_nonneg ha'.le,
          Real.norm_of_nonneg (by positivity)]),
      D.exponent_eq_of_norm_eq (ξ := ξ) (ξ' := ‖ξ‖ • e₁)
        (by rw [norm_smul, he₁1, mul_one, Real.norm_of_nonneg (norm_nonneg _)])]
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha'
    have h := (D.tendsto_exponent_dilate hd ha hc hsa he).comp Real.tendsto_sqrt_atTop
    have hlog : D.profileAtOrigin.toReal * Real.log (Real.sqrt a)
        = D.profileAtOrigin.toReal / 2 * Real.log a := by
      rw [Real.log_sqrt ha'.le]; ring
    rw [hlog] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul ha'.le]

end AffineHemigroup
