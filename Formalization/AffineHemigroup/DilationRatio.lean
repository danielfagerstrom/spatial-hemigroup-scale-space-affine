/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OrbitRays
import AffineHemigroup.OriginBoundedness
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# `lem:dilation-ratio`: monotonicity and two exponents of the dilation ratio

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:dilation-ratio` (wave 2, group D, Q-0281).
Cites nothing: the definition of `R`, the integrability of the Lévy density in polar coordinates, and
Fekete's argument for a supermultiplicative function, written out. Clause (4) reads the equivalence
`orbit_density_order_iff` of `prop:orbit-step-cone`(2), which is Lean core.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder ENNReal

variable {d : ℕ}

/-! ## Reading the infimum -/

/-- `R(λ)` is at most each of its quotients. -/
theorem dilRatio_le (hd : 1 ≤ d) (K : RadialProfile d) {lam : ℝ} (hlam : 1 ≤ lam) {r : ℝ}
    (hr : 0 < r) (hk : 0 < K.k r) : dilRatio K.k lam * K.k r ≤ K.k (r / lam) :=
  (le_div_iff₀ hk).1 (ciInf_le (dilRatio_mem hd K lam hlam).1 ⟨r, hr, hk⟩)

/-- A lower bound for every quotient bounds `R(λ)` below. -/
theorem le_dilRatio (K : RadialProfile d) {lam c : ℝ}
    (h : ∀ r : ℝ, 0 < r → 0 < K.k r → c * K.k r ≤ K.k (r / lam)) : c ≤ dilRatio K.k lam := by
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨r0, hr0, hk0⟩⟩
  exact le_ciInf fun r => (le_div_iff₀ r.2.2).2 (h r.1 r.2.1 r.2.2)

/-! ## Clause (1) -/

/-- **`lem:dilation-ratio`(1)**: `R(1) = 1`, `R` is nondecreasing on `[1,∞)`, and
`R(λν) ≥ R(λ)R(ν)` for `λ, ν ≥ 1`. -/
theorem dilRatio_monotone (hd : 1 ≤ d) (K : RadialProfile d) :
    dilRatio K.k 1 = 1 ∧ MonotoneOn (dilRatio K.k) (Ici 1) ∧
      ∀ lam ν : ℝ, 1 ≤ lam → 1 ≤ ν → dilRatio K.k lam * dilRatio K.k ν ≤ dilRatio K.k (lam * ν) := by
  refine ⟨dilRatio_one K, fun lam hlam ν hν hle => ?_, fun lam ν hlam hν => ?_⟩
  · have hlam' : (1 : ℝ) ≤ lam := hlam
    refine le_dilRatio K fun r hr hk => (dilRatio_le hd K hlam' hr hk).trans ?_
    exact K.k_antitone (div_pos hr (by linarith [show (1 : ℝ) ≤ ν from hν]))
      (div_pos hr (by linarith)) (div_le_div_of_nonneg_left hr.le (by linarith) hle)
  · refine le_dilRatio K fun r hr hk => ?_
    have hν0 : 0 < ν := by linarith
    have hrν : 0 < r / ν := div_pos hr hν0
    have hkν : K.k r ≤ K.k (r / ν) := K.k_antitone hrν hr (div_le_self hr.le hν)
    have hkν0 : 0 < K.k (r / ν) := lt_of_lt_of_le hk hkν
    have h1 := dilRatio_le hd K hν hr hk
    have h2 := dilRatio_le hd K hlam hrν hkν0
    have hR1 := (dilRatio_mem hd K lam hlam).2
    have heq : r / (lam * ν) = r / ν / lam := by rw [div_div, mul_comm]
    rw [heq]
    calc dilRatio K.k lam * dilRatio K.k ν * K.k r
        = dilRatio K.k lam * (dilRatio K.k ν * K.k r) := by ring
      _ ≤ dilRatio K.k lam * K.k (r / ν) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ K.k (r / ν / lam) := h2

/-- `R(λⁿ) ≥ R(λ)ⁿ`. -/
theorem pow_dilRatio_le (hd : 1 ≤ d) (K : RadialProfile d) {lam : ℝ} (hlam : 1 ≤ lam) (n : ℕ) :
    dilRatio K.k lam ^ n ≤ dilRatio K.k (lam ^ n) := by
  induction n with
  | zero => simp [dilRatio_one K]
  | succ n ih =>
    have hR := (dilRatio_mem hd K lam hlam).2
    calc dilRatio K.k lam ^ (n + 1) = dilRatio K.k lam ^ n * dilRatio K.k lam := pow_succ _ _
      _ ≤ dilRatio K.k (lam ^ n) * dilRatio K.k lam :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ dilRatio K.k (lam ^ n * lam) :=
          (dilRatio_monotone hd K).2.2 _ _ (one_le_pow₀ hlam) hlam
      _ = dilRatio K.k (lam ^ (n + 1)) := by rw [pow_succ]

/-! ## Clause (2) -/

/-- **A profile at least `c/r²` near the origin is not integrable**: `∫₀^a r k(r) dr = ∞`, against
`∫ (|x|² ∧ 1) m(|x|) dx < ∞` in polar coordinates. -/
theorem RadialProfile.not_ge_at_zero (hd : 1 ≤ d) (K : RadialProfile d) {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hk : ∀ r : ℝ, 0 < r → r ≤ a → c / r ^ 2 ≤ K.k r) : False := by
  apply K.integrable
  rw [K.lintegral_radial hd]
  have hA := (sphereArea_eq_toSphere (d := d) hd).2
  set b := min a 1 with hb
  have hb0 : 0 < b := lt_min ha one_pos
  -- `∫_0^b c/r dr = ∞`
  have hinv : ∫⁻ r in Ioo 0 b, ENNReal.ofReal (c / r) = ⊤ := by
    by_contra hfin
    have hnot := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -1) hb0).not.2 (lt_irrefl _)
    apply hnot
    refine ⟨(measurable_id.pow_const _).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hle : ∫⁻ r in Ioo 0 b, ‖r ^ (-1 : ℝ)‖ₑ ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ r in Ioo 0 b, ENNReal.ofReal (c / r) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
      have hr0 : 0 < r := hr.1
      rw [← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal (by positivity),
        Real.rpow_neg_one]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      field_simp
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin))
  have htop : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (min (r ^ 2) 1 * K.k r / r) = ⊤ := by
    refine eq_top_iff.2 (hinv ▸ ?_)
    refine (setLIntegral_mono' measurableSet_Ioo fun r hr => ?_).trans
      (lintegral_mono_set Ioo_subset_Ioi_self)
    have hr0 : 0 < r := hr.1
    have hra : r ≤ a := hr.2.le.trans (min_le_left _ _)
    have hr1 : r ≤ 1 := hr.2.le.trans (min_le_right _ _)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [min_eq_left (by nlinarith)]
    have h1 := hk r hr0 hra
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ hr0, div_mul_eq_mul_div, div_le_iff₀ hr0]
    nlinarith
  rw [htop, ENNReal.mul_top (by simp [hA])]

/-- **`lem:dilation-ratio`(2)**: `R(λ) < λ²` for every `λ > 1`. -/
theorem dilRatio_lt_sq (hd : 1 ≤ d) (K : RadialProfile d) :
    ∀ lam : ℝ, 1 < lam → dilRatio K.k lam < lam ^ 2 := by
  intro l0 hl0
  by_contra hge
  push Not at hge
  have hl00 : 0 < l0 := by linarith
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  -- `k(r/λ₀) ≥ λ₀² k(r)` wherever `k(r) > 0`
  have hstep : ∀ r : ℝ, 0 < r → 0 < K.k r → l0 ^ 2 * K.k r ≤ K.k (r / l0) := fun r hr hk =>
    (mul_le_mul_of_nonneg_right hge hk.le).trans (dilRatio_le hd K hl0.le hr hk)
  have hiter : ∀ n : ℕ, (l0 ^ 2) ^ n * K.k r0 ≤ K.k (r0 / l0 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 < K.k (r0 / l0 ^ n) := lt_of_lt_of_le (by positivity) ih
      calc (l0 ^ 2) ^ (n + 1) * K.k r0 = l0 ^ 2 * ((l0 ^ 2) ^ n * K.k r0) := by ring
        _ ≤ l0 ^ 2 * K.k (r0 / l0 ^ n) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ K.k (r0 / l0 ^ n / l0) := hstep _ (by positivity) hpos
        _ = K.k (r0 / l0 ^ (n + 1)) := by rw [div_div, ← pow_succ]
  -- so `k(r) ≥ k(r₀) r₀² / (λ₀² r²)` on `(0, r₀]`
  refine K.not_ge_at_zero hd hr0 (c := K.k r0 * r0 ^ 2 / l0 ^ 2) (by positivity) fun r hr hrr => ?_
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := r0 / r) ((one_le_div hr).2 hrr) hl0
  have hrle : r ≤ r0 / l0 ^ n := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hr] at hn1
    linarith
  have hk1 : K.k (r0 / l0 ^ n) ≤ K.k r := K.k_antitone hr (show (0 : ℝ) < r0 / l0 ^ n by positivity) hrle
  have hlt : r0 < l0 ^ (n + 1) * r := by rwa [div_lt_iff₀ hr] at hn2
  have hsq : r0 ^ 2 < (l0 ^ (n + 1) * r) ^ 2 := pow_lt_pow_left₀ hlt hr0.le two_ne_zero
  rw [div_le_iff₀ (by positivity)]
  have hpow : (l0 ^ (n + 1) * r) ^ 2 = (l0 ^ 2) ^ n * (l0 ^ 2 * r ^ 2) := by ring
  rw [hpow] at hsq
  have hkn := hiter n
  calc K.k r0 * r0 ^ 2 / l0 ^ 2 = K.k r0 * r0 ^ 2 / l0 ^ 2 := rfl
    _ ≤ K.k r0 * ((l0 ^ 2) ^ n * (l0 ^ 2 * r ^ 2)) / l0 ^ 2 := by
        gcongr
    _ = (l0 ^ 2) ^ n * K.k r0 * r ^ 2 := by field_simp
    _ ≤ K.k r * r ^ 2 := mul_le_mul_of_nonneg_right (hkn.trans hk1) (by positivity)

/-! ## Clause (3): Fekete's argument -/

/-- **`lem:dilation-ratio`(3)**, two exponents: the quotients `log R(λ)/log λ`, `λ > 1`, lie in
`[0,2)`; their limit as `λ → ∞` exists and is their supremum `β(k)`; `0 ≤ β₋(k) ≤ β(k) ≤ 2`,
`β₋(k) < 2`, `λ^{β₋(k)} ≤ R(λ) ≤ λ^{β(k)}` for `λ ≥ 1`; and for `α ≥ 0`, `R(λ) ≥ λ^α` for every
`λ ≥ 1` if and only if `α ≤ β₋(k)`. -/
theorem dilRatio_exponents (hd : 1 ≤ d) (K : RadialProfile d) :
    (∀ lam : ℝ, 1 < lam →
        0 ≤ Real.log (dilRatio K.k lam) / Real.log lam ∧
          Real.log (dilRatio K.k lam) / Real.log lam < 2) ∧
      Tendsto (fun lam => Real.log (dilRatio K.k lam) / Real.log lam) atTop
        (𝓝 (growthExp K.k)) ∧
      0 ≤ lowerExp K.k ∧ lowerExp K.k ≤ growthExp K.k ∧ growthExp K.k ≤ 2 ∧ lowerExp K.k < 2 ∧
      (∀ lam : ℝ, 1 ≤ lam →
        lam ^ lowerExp K.k ≤ dilRatio K.k lam ∧ dilRatio K.k lam ≤ lam ^ growthExp K.k) ∧
      ∀ α : ℝ, 0 ≤ α → ((∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam) ↔ α ≤ lowerExp K.k) := by
  set R := dilRatio K.k with hRdef
  set q : ℝ → ℝ := fun lam => Real.log (R lam) / Real.log lam with hqdef
  have hR1 : ∀ lam : ℝ, 1 ≤ lam → 1 ≤ R lam := fun lam h => (dilRatio_mem hd K lam h).2
  have hq : ∀ lam : ℝ, 1 < lam → 0 ≤ q lam ∧ q lam < 2 := by
    intro lam hlam
    have hl := Real.log_pos hlam
    have hR := hR1 lam hlam.le
    refine ⟨div_nonneg (Real.log_nonneg hR) hl.le, (div_lt_iff₀ hl).2 ?_⟩
    have h2 := dilRatio_lt_sq hd K lam hlam
    have : Real.log (R lam) < Real.log (lam ^ 2) :=
      Real.log_lt_log (by linarith) h2
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  haveI : Nonempty (Ioi (1 : ℝ)) := ⟨⟨2, by norm_num⟩⟩
  have hbddA : BddAbove (range fun lam : Ioi (1 : ℝ) => q lam) :=
    ⟨2, by rintro _ ⟨lam, rfl⟩; exact (hq lam lam.2).2.le⟩
  have hbddB : BddBelow (range fun lam : Ioi (1 : ℝ) => q lam) :=
    ⟨0, by rintro _ ⟨lam, rfl⟩; exact (hq lam lam.2).1⟩
  have hG : growthExp K.k = ⨆ lam : Ioi (1 : ℝ), q lam := rfl
  have hL : lowerExp K.k = ⨅ lam : Ioi (1 : ℝ), q lam := rfl
  have hqG : ∀ lam : ℝ, 1 < lam → q lam ≤ growthExp K.k := fun lam h => by
    rw [hG]; exact le_ciSup hbddA (⟨lam, h⟩ : Ioi (1 : ℝ))
  have hLq : ∀ lam : ℝ, 1 < lam → lowerExp K.k ≤ q lam := fun lam h => by
    rw [hL]; exact ciInf_le hbddB (⟨lam, h⟩ : Ioi (1 : ℝ))
  have hG2 : growthExp K.k ≤ 2 := by
    rw [hG]; exact ciSup_le fun lam => (hq lam lam.2).2.le
  have hL0 : 0 ≤ lowerExp K.k := by
    rw [hL]; exact le_ciInf fun lam => (hq lam lam.2).1
  have h2 : (1 : ℝ) < 2 := by norm_num
  -- `λ^b ≤ R(λ) ↔ b ≤ q(λ)` and the reverse, for `λ > 1`
  have hpow_le : ∀ lam : ℝ, 1 < lam → ∀ b : ℝ, lam ^ b ≤ R lam ↔ b ≤ q lam := by
    intro lam hlam b
    have hl := Real.log_pos hlam
    have hR := hR1 lam hlam.le
    rw [le_div_iff₀ hl, ← Real.log_le_log_iff (by positivity) (by linarith),
      Real.log_rpow (by linarith), mul_comm]
  have hle_pow : ∀ lam : ℝ, 1 < lam → ∀ b : ℝ, R lam ≤ lam ^ b ↔ q lam ≤ b := by
    intro lam hlam b
    have hl := Real.log_pos hlam
    have hR := hR1 lam hlam.le
    rw [div_le_iff₀ hl, ← Real.log_le_log_iff (by linarith) (by positivity),
      Real.log_rpow (by linarith), mul_comm]
  refine ⟨hq, ?_, hL0, (hLq 2 h2).trans (hqG 2 h2), hG2, lt_of_le_of_lt (hLq 2 h2) (hq 2 h2).2,
    fun lam hlam => ?_, fun α _ => ⟨fun h => ?_, fun h lam hlam => ?_⟩⟩
  · -- the limit, by Fekete's argument
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rw [hG] at ha
      obtain ⟨⟨l0, hl0⟩, hlt⟩ := exists_lt_of_lt_ciSup ha
      have hl0' : (1 : ℝ) < l0 := hl0
      change a < q l0 at hlt
      rcases lt_or_ge a 0 with ha0 | ha0
      · filter_upwards [eventually_gt_atTop 1] with lam hlam
        exact lt_of_lt_of_le ha0 (hq lam hlam).1
      obtain ⟨N, hN⟩ := exists_nat_gt (a / (q l0 - a))
      have hqa : 0 < q l0 - a := by linarith
      filter_upwards [eventually_ge_atTop (l0 ^ N), eventually_gt_atTop 1] with lam hlamN hlam
      obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hlam.le hl0'
      have hnN : N ≤ n := by
        have : l0 ^ N < l0 ^ (n + 1) := lt_of_le_of_lt hlamN hn2
        have := (pow_lt_pow_iff_right₀ hl0').1 this
        omega
      have hlog0 := Real.log_pos hl0'
      have hlog := Real.log_pos hlam
      have hRl0 := hR1 l0 hl0'.le
      -- `log R(λ) ≥ n log R(λ₀) = n q(λ₀) log λ₀`
      have hRn : R l0 ^ n ≤ R lam :=
        (pow_dilRatio_le hd K hl0'.le n).trans
          ((dilRatio_monotone hd K).2.1 (one_le_pow₀ hl0'.le) (show (1 : ℝ) ≤ lam from hlam.le)
            hn1)
      have hlogR : (n : ℝ) * (q l0 * Real.log l0) ≤ Real.log (R lam) := by
        have h1 : q l0 * Real.log l0 = Real.log (R l0) := by
          simp only [hqdef]; field_simp
        rw [h1, ← Real.log_pow]
        exact Real.log_le_log (by positivity) hRn
      -- `log λ < (n + 1) log λ₀`
      have hloglam : Real.log lam < ((n : ℝ) + 1) * Real.log l0 := by
        have := Real.log_lt_log (by linarith) hn2
        rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
      have hNn : a / (q l0 - a) < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
      rw [div_lt_iff₀ hqa] at hNn
      change a < Real.log (R lam) / Real.log lam
      rw [lt_div_iff₀ hlog]
      calc a * Real.log lam ≤ a * (((n : ℝ) + 1) * Real.log l0) :=
            mul_le_mul_of_nonneg_left hloglam.le ha0
        _ < (n : ℝ) * (q l0 * Real.log l0) := by nlinarith
        _ ≤ Real.log (R lam) := hlogR
    · filter_upwards [eventually_gt_atTop 1] with lam hlam
      exact lt_of_le_of_lt (hqG lam hlam) hb
  · -- the two displayed bounds
    rcases hlam.lt_or_eq with hlam | rfl
    · exact ⟨(hpow_le lam hlam _).2 (hLq lam hlam), (hle_pow lam hlam _).2 (hqG lam hlam)⟩
    · have h1 : R 1 = 1 := dilRatio_one K
      rw [Real.one_rpow, Real.one_rpow, h1]
      exact ⟨le_rfl, le_rfl⟩
  · rw [hL]
    exact le_ciInf fun lam => (hpow_le lam lam.2 α).1 (h lam lam.2.le)
  · rcases hlam.lt_or_eq with hlam | rfl
    · exact (hpow_le lam hlam α).2 (h.trans (hLq lam hlam))
    · have h1 : R 1 = 1 := dilRatio_one K
      rw [Real.one_rpow, h1]

/-! ## Clause (4): the rung -/

/-- **`lem:dilation-ratio`(4)**, the rung: for `d ≥ 2` and `0 < α < 2`, every pair `Σ ≼_α Σ'` has
`n_Σ ≤ n_{Σ'}` if and only if `α ≤ β₋(k)`. -/
theorem dilRatio_rung (hd : 2 ≤ d) (K : RadialProfile d) {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) :
    (∀ S S' : Mat d, stableLE α S S' → ∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔
      α ≤ lowerExp K.k := by
  have hd1 : 1 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  have hexp := (dilRatio_exponents hd1 K).2.2.2.2.2.2.2 α hα0.le
  constructor
  · intro H
    refine hexp.1 fun lam hlam => ?_
    rcases hlam.lt_or_eq with hlam | rfl
    swap
    · rw [Real.one_rpow, dilRatio_one K]
    have hl0 : 0 < lam := by linarith
    -- the step `I → diag(λ², …, λ², λ^{2(1+α)})`
    set w : Fin d → ℝ := fun i => lam ^ 2 * (if i = 0 then (lam ^ α) ^ 2 else 1) with hw
    have hU : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
    set M := udiag 1 w with hMdef
    have hwpos : ∀ i, 0 < w i := fun i => by
      simp only [hw]; split_ifs <;> positivity
    have hMpd : M.PosDef := (udiag_posDef_iff hU w).2 hwpos
    have hwge : ∀ i, lam ^ 2 ≤ w i := fun i => by
      simp only [hw]
      split_ifs
      · have : 1 ≤ (lam ^ α) ^ 2 := one_le_pow₀ (Real.one_le_rpow hlam.le hα0.le)
        nlinarith
      · rw [mul_one]
    have hl : lamMin M = lam ^ 2 := by
      refine le_antisymm ?_ (le_lamMin_udiag hU hwge)
      have h1 := lamMin_udiag_le hU w ⟨1, by omega⟩
      have hne : (⟨1, by omega⟩ : Fin d) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      have hw1 : w ⟨1, by omega⟩ = lam ^ 2 := by simp [hw, hne]
      rwa [hw1] at h1
    have hdet : M.det = (lam ^ 2) ^ d * (lam ^ α) ^ 2 := by
      rw [hMdef, det_udiag hU, hw, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_ite_eq' Finset.univ (0 : Fin d)]
      simp
    have hsq : Real.sqrt (lam ^ 2) = lam := Real.sqrt_sq hl0.le
    have hkey : (lam ^ 2) ^ d * (lam ^ α) ^ 2 = (lam ^ 2) ^ ((d : ℝ) + α) := by
      rw [← pow_mul_sqrt_rpow_sq (by positivity : (0 : ℝ) < lam ^ 2) α, hsq]
    have hstab : stableLE α 1 M := by
      refine ⟨Matrix.PosDef.one, hMpd, ?_⟩
      rw [relStep_one_left]
      exact ⟨hMpd, by rw [hdet, hl, hkey]⟩
    have hord := H 1 M hstab
    have h := ((orbit_density_order_iff hd1 K Matrix.PosDef.one hMpd).1.1 hord).2
    rw [relStep_one_left, hl, hdet, hsq] at h
    have h' : (lam ^ α) ^ 2 ≤ dilRatio K.k lam ^ 2 :=
      le_of_mul_le_mul_left h (by positivity)
    exact (pow_le_pow_iff_left₀ (by positivity) (by linarith [(dilRatio_mem hd1 K lam hlam.le).2])
      two_ne_zero).1 h'
  · intro h S S' hSS'
    obtain ⟨hS, hS', hMpd, hdet⟩ := hSS'
    refine (orbit_density_order_iff hd1 K hS hS').1.2 ⟨?_, ?_⟩
    · exact one_le_lamMin_of_stable hα0 hMpd hdet
    · have hl1 := one_le_lamMin_of_stable hα0 hMpd hdet
      have hl := lamMin_pos hMpd
      have hR := hexp.2 h (Real.sqrt (lamMin (relStep S S'))) (Real.one_le_sqrt.2 hl1)
      calc (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α) := hdet
        _ = lamMin (relStep S S') ^ d * (Real.sqrt (lamMin (relStep S S')) ^ α) ^ 2 :=
            (pow_mul_sqrt_rpow_sq hl α).symm
        _ ≤ lamMin (relStep S S') ^ d *
              dilRatio K.k (Real.sqrt (lamMin (relStep S S'))) ^ 2 := by
            gcongr

/-! ## Clause (5): values -/

/-- The quotients of a ratio `R(λ) = λ^a` are `a`, so both exponents are `a`. -/
theorem exponents_of_dilRatio_eq (K : RadialProfile d) (a : ℝ)
    (hR : ∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ a) :
    lowerExp K.k = a ∧ growthExp K.k = a := by
  have hq : ∀ lam : Ioi (1 : ℝ), Real.log (dilRatio K.k lam) / Real.log lam = a := by
    rintro ⟨lam, hlam⟩
    have hlam' : (1 : ℝ) < lam := hlam
    rw [hR lam hlam'.le, Real.log_rpow (by linarith), mul_div_assoc,
      div_self (Real.log_pos hlam').ne', mul_one]
  haveI : Nonempty (Ioi (1 : ℝ)) := ⟨⟨2, by norm_num⟩⟩
  exact ⟨(iInf_congr hq).trans ciInf_const, (iSup_congr hq).trans ciSup_const⟩

/-- **`lem:dilation-ratio`(5)**, values: for `k(r) = c r^{-α}`, `c > 0`, `0 < α < 2`,
`β₋(k) = β(k) = α`. -/
theorem dilRatio_exponents_stable (hd : 1 ≤ d) (K : RadialProfile d) (c α : ℝ) (_hc : 0 < c)
    (hα0 : 0 < α) (hα2 : α < 2) (hk : ∀ r : ℝ, 0 < r → K.k r = c * r ^ (-α)) :
    lowerExp K.k = α ∧ growthExp K.k = α :=
  exponents_of_dilRatio_eq K α (orbit_density_order_stable hd K c α hα0 hα2 hk).1

/-- **`lem:dilation-ratio`(5)**, values: if `k(0+)` is finite, `β₋(k) = β(k) = 0`. -/
theorem dilRatio_exponents_bounded (hd : 1 ≤ d) (K : RadialProfile d) (L : ℝ)
    (hL : Tendsto K.k (𝓝[>] 0) (𝓝 L)) :
    lowerExp K.k = 0 ∧ growthExp K.k = 0 :=
  exponents_of_dilRatio_eq K 0 fun lam hlam => by
    rw [Real.rpow_zero]; exact (orbit_density_order_bounded hd K L hL).1 lam hlam

/-- The dyadic profile `2^{⌊-log₂ r⌋}`. -/
noncomputable def dyadicK (r : ℝ) : ℝ := (2 : ℝ) ^ ⌊-Real.logb 2 r⌋

theorem dyadicK_pos (r : ℝ) : 0 < dyadicK r := zpow_pos two_pos _

/-- `2^{⌊x⌋} ≤ 2^x`. -/
theorem two_zpow_floor_le (x : ℝ) : (2 : ℝ) ^ ⌊x⌋ ≤ (2 : ℝ) ^ x := by
  rw [← Real.rpow_intCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (Int.floor_le x)

/-- `k(r) ≤ 1/r`. -/
theorem dyadicK_le_inv {r : ℝ} (hr : 0 < r) : dyadicK r ≤ r⁻¹ := by
  refine (two_zpow_floor_le _).trans (le_of_eq ?_)
  rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by norm_num) hr]

theorem dyadicK_antitone : AntitoneOn dyadicK (Ioi (0 : ℝ)) := by
  intro r hr s hs hrs
  refine zpow_le_zpow_right₀ one_le_two (Int.floor_mono ?_)
  exact neg_le_neg (Real.logb_le_logb_of_le one_lt_two hr hrs)

/-- `k(r/2) = 2 k(r)`. -/
theorem dyadicK_div_two {r : ℝ} (hr : 0 < r) : dyadicK (r / 2) = 2 * dyadicK r := by
  unfold dyadicK
  rw [Real.logb_div hr.ne' two_ne_zero, Real.logb_self_eq_one one_lt_two, neg_sub,
    sub_eq_add_neg, add_comm, Int.floor_add_one, zpow_add_one₀ two_ne_zero, mul_comm]

/-- `k(1) = 1`. -/
theorem dyadicK_one : dyadicK 1 = 1 := by simp [dyadicK]

/-- `k(1/λ) ≤ λ` for `λ ≥ 1`, and `k(1/λ) = 1` for `1 ≤ λ < 2`. -/
theorem dyadicK_inv {lam : ℝ} (hlam : 1 ≤ lam) :
    dyadicK (1 / lam) ≤ lam ∧ (lam < 2 → dyadicK (1 / lam) = 1) := by
  have hl0 : 0 < lam := by linarith
  have hlog : -Real.logb 2 (1 / lam) = Real.logb 2 lam := by
    rw [one_div, Real.logb_inv, neg_neg]
  refine ⟨?_, fun h2 => ?_⟩
  · unfold dyadicK
    rw [hlog]
    exact (two_zpow_floor_le _).trans (le_of_eq (Real.rpow_logb two_pos (by norm_num) hl0))
  · unfold dyadicK
    rw [hlog]
    have h0 : 0 ≤ Real.logb 2 lam := Real.logb_nonneg one_lt_two hlam
    have h1 : Real.logb 2 lam < 1 := by
      rw [Real.logb_lt_iff_lt_rpow one_lt_two hl0, Real.rpow_one]; exact h2
    have : ⌊Real.logb 2 lam⌋ = 0 := Int.floor_eq_iff.2 ⟨by simpa using h0, by simpa using h1⟩
    rw [this, zpow_zero]

/-- **The dyadic profile is a radial profile**: `k ≤ 1/r` gives
`∫₀^∞ (r² ∧ 1) k(r) dr/r ≤ ∫₀^∞ (r² ∧ 1) r^{-2} dr = 2`. -/
noncomputable def dyadicProfile (hd : 1 ≤ d) : RadialProfile d where
  k := dyadicK
  k_nonneg := fun r _ => (dyadicK_pos r).le
  k_antitone := dyadicK_antitone
  k_ne_zero := ⟨1, mem_Ioi.2 one_pos, (dyadicK_pos 1).ne'⟩
  integrable := by
    set f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (min (r ^ 2) 1 * (r⁻¹ / r ^ d)) with hf
    have hfm : Measurable f := by fun_prop
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => ?_ : _ ≤ ∫⁻ x : Rd d, f ‖x‖)
    · rw [lintegral_radial hd f hfm]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      -- the radial integral
      have hpt : ∀ r ∈ Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1)) =
          ENNReal.ofReal (min (r ^ 2) 1 / r ^ 2) := by
        intro r hr
        have hr0 : (0 : ℝ) < r := hr
        rw [hf, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hpow : r ^ d = r ^ (d - 1) * r := by rw [← pow_succ]; congr 1; omega
        rw [hpow]
        field_simp
      rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
      refine ne_top_of_le_ne_top ?_ ((lintegral_mono_set (Ioi_subset_Ioc_union_Ioi
        (b := 1))).trans (lintegral_union_le _ _ _))
      refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
      · refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioc (0 : ℝ) 1, 1) ?_
          (setLIntegral_mono' measurableSet_Ioc fun r hr => ?_)
        · rw [setLIntegral_const, Real.volume_Ioc, one_mul]; exact ENNReal.ofReal_ne_top
        · rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_one (by have := hr.1; positivity)]
          exact min_le_left _ _
      · have hint : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi 1) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
        refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne
          (setLIntegral_mono' measurableSet_Ioi fun r hr => ENNReal.ofReal_le_ofReal ?_)
        have hr1 : (1 : ℝ) < r := hr
        rw [min_eq_right (by nlinarith), Real.rpow_neg (by linarith), Real.rpow_two, one_div]
    · by_cases hx : x = 0
      · subst hx; simp [hf, zero_pow (by omega : d ≠ 0)]
      have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact div_le_div_of_nonneg_right (dyadicK_le_inv hn) (by positivity)

/-- **`lem:dilation-ratio`(5)**, the dyadic profile: `k(r) := 2ⁿ` for `2^{-n-1} < r ≤ 2^{-n}`,
`n ∈ ℤ` (that is `2^{⌊-log₂ r⌋}`), satisfies the hypotheses of `prop:orbit-step-cone` and has
`β₋(k) = 0` and `β(k) = 1`. -/
theorem dilRatio_dyadic (hd : 1 ≤ d) :
    ∃ K : RadialProfile d, (∀ r : ℝ, 0 < r → K.k r = (2 : ℝ) ^ ⌊-Real.logb 2 r⌋) ∧
      lowerExp K.k = 0 ∧ growthExp K.k = 1 := by
  obtain ⟨K, hk⟩ : ∃ K : RadialProfile d, K.k = dyadicK := ⟨dyadicProfile hd, rfl⟩
  have hk1 : K.k 1 = 1 := by rw [hk]; exact dyadicK_one
  have hkpos : ∀ r, 0 < K.k r := fun r => by rw [hk]; exact dyadicK_pos r
  have hkinv : ∀ lam : ℝ, K.k (1 / lam) = dyadicK (1 / lam) := fun lam => by rw [hk]
  have hk2 : ∀ r : ℝ, 0 < r → K.k (r / 2) = 2 * K.k r := fun r hr => by
    rw [hk]; exact dyadicK_div_two hr
  refine ⟨K, fun r _ => by rw [hk]; rfl, ?_, ?_⟩
  · -- `R(3/2) = 1`
    have h := dilRatio_exponents hd K
    have hR : dilRatio K.k (3 / 2) = 1 := by
      refine le_antisymm ?_ (dilRatio_mem hd K _ (by norm_num)).2
      have := dilRatio_le hd K (lam := 3 / 2) (by norm_num) one_pos (hkpos 1)
      rw [hk1, mul_one, hkinv, (dyadicK_inv (by norm_num)).2 (by norm_num)] at this
      exact this
    have hq : Real.log (dilRatio K.k (3 / 2)) / Real.log (3 / 2) = 0 := by
      rw [hR, Real.log_one, zero_div]
    have hle : lowerExp K.k ≤ 0 := by
      have : lowerExp K.k ≤ Real.log (dilRatio K.k (3 / 2)) / Real.log (3 / 2) := by
        haveI : Nonempty (Ioi (1 : ℝ)) := ⟨⟨2, by norm_num⟩⟩
        exact ciInf_le ⟨0, by rintro _ ⟨lam, rfl⟩; exact (h.1 lam lam.2).1⟩
          (⟨3 / 2, by norm_num⟩ : Ioi (1 : ℝ))
      rwa [hq] at this
    exact le_antisymm hle h.2.2.1
  · -- `R(λ) ≤ λ` everywhere and `R(2) = 2`
    have hR2 : dilRatio K.k 2 = 2 := by
      haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨1, one_pos, hkpos 1⟩⟩
      have hq : ∀ r : {r : ℝ // 0 < r ∧ 0 < K.k r}, K.k (r.1 / 2) / K.k r.1 = 2 := by
        rintro ⟨r, hr, hkr⟩
        rw [hk2 r hr, mul_div_assoc, div_self hkr.ne', mul_one]
      unfold dilRatio
      simp_rw [hq]
      exact ciInf_const
    have hqle : ∀ lam : Ioi (1 : ℝ), Real.log (dilRatio K.k lam) / Real.log lam ≤ 1 := by
      rintro ⟨lam, hlam⟩
      have hlam' : (1 : ℝ) < lam := hlam
      have hRl : dilRatio K.k lam ≤ lam := by
        have := dilRatio_le hd K (lam := lam) hlam'.le one_pos (hkpos 1)
        rw [hk1, mul_one, hkinv] at this
        exact this.trans (dyadicK_inv hlam'.le).1
      have hR1 := (dilRatio_mem hd K lam hlam'.le).2
      rw [div_le_one (Real.log_pos hlam')]
      exact Real.log_le_log (by linarith) hRl
    haveI : Nonempty (Ioi (1 : ℝ)) := ⟨⟨2, by norm_num⟩⟩
    refine le_antisymm (ciSup_le hqle) ?_
    have h2 : Real.log (dilRatio K.k 2) / Real.log 2 = 1 := by
      rw [hR2, div_self (Real.log_pos one_lt_two).ne']
    have hb : BddAbove (range fun lam : Ioi (1 : ℝ) =>
        Real.log (dilRatio K.k lam) / Real.log lam) :=
      ⟨1, by rintro _ ⟨lam, rfl⟩; exact hqle lam⟩
    calc (1 : ℝ) = Real.log (dilRatio K.k ((⟨2, mem_Ioi.2 one_lt_two⟩ : Ioi (1 : ℝ)) : ℝ)) /
          Real.log ((⟨2, mem_Ioi.2 one_lt_two⟩ : Ioi (1 : ℝ)) : ℝ) := h2.symm
      _ ≤ _ := le_ciSup hb _

end AffineHemigroup
