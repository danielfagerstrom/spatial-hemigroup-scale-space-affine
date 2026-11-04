/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginDecay
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# `cor:origin-profile-exponent`: the exponent determines `a` and the profile at the origin

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `cor:origin-profile-exponent` (Q-0409).

For an isotropic origin datum `(a, k_d)` in dimension `d ≥ 1` with exponent `F_d` and profile at
the origin `c = k_d(0+) ∈ [0,∞]`:

* `exponent_gaussian_limit` (clause (1)): `F_d(ξ)/|ξ|² → a/2` as `|ξ| → ∞`;
* `exponent_profile_limit` (clause (2)): `(F_d(ξ) - a|ξ|²/2)/log|ξ| → c` as `|ξ| → ∞`, in the
  extended reals, with `transform_profile_limit` for the last sentence of the clause, on a law of a
  datum with `a = 0`: `-log|μ̂(ξ)|/log|ξ| → c`;
* `origin_profile_dimension_free` (clause (3)): two data, in dimensions `d` and `d'`, whose
  exponents are one function `F` of the radius have the same Gaussian coefficient and the same
  profile at the origin.

No law is named except in `transform_profile_limit`, where it is a hypothesis (`IsLawOf`), and no
cited fact is spent.

**The route.** The jump part `F_d(ξ) - a|ξ|²/2` is the exponent of the datum `(0, k_d)`
(`OriginDatum.jumpPart`, `OriginDatum.exponent_eq_add`). Clause (1) is the quadratic bound behind
the finiteness of `F_d` (`cosProfileL_le_sq`), split at a radius `τ ∈ (0,1]` instead of at `1`
(`cosProfileL_le_sq_at`): `G(ξ) ≤ ½|ξ|² ∫₀^τ k_d r dr + 2 ∫_τ^∞ k_d dr/r`, and the first integral
tends to `0` with `τ`. Clause (2) joins the two bounds the chapter has: from below
`OriginDatum.exponent_decay` (the exponent form of `lem:origin-decay-exponent`), for every finite
`β < c`, and from above `isotropic_exponent_log_bound` (`lem:isotropic-exponent-log`(1)), for a
finite `c`. It is proved in `ℝ≥0∞` first, for `ENNReal.ofReal` of the quotient
(`OriginDatum.tendsto_ofReal_exponent_div_log`), and moved to `EReal`, where the quotient itself
is read: it is nonnegative for `|ξ| ≥ 1`. Clause (3) reads the two limits along a ray, where the
exponent is `F(r)`, and uses the uniqueness of a limit.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ScaleSpace
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The jump part of a datum -/

/-- **The datum `(0, k_d)`**: the same polar profile, Gaussian coefficient `0`. Its exponent is the
jump part `F_d(ξ) - ½a|ξ|²` of the datum's (`OriginDatum.exponent_eq_add`). -/
noncomputable def OriginDatum.jumpPart (D : OriginDatum d) : OriginDatum d :=
  { D with a := 0, a_nonneg := le_rfl }

theorem OriginDatum.exponentL_jumpPart (D : OriginDatum d) (ξ : Rd d) :
    D.exponentL ξ = ENNReal.ofReal (D.a * ‖ξ‖ ^ 2 / 2) + D.jumpPart.exponentL ξ := by
  have h : D.jumpPart.exponentL ξ =
      ENNReal.ofReal ((0 : ℝ) * ‖ξ‖ ^ 2 / 2)
        + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (inner ℝ ξ x)) ∂D.levyMeasure := rfl
  rw [h, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  rfl

/-- `F_d(ξ) = ½a|ξ|² + G(ξ)`, `G` the exponent of `(0, k_d)`. -/
theorem OriginDatum.exponent_eq_add (hd : 1 ≤ d) (D : OriginDatum d) (ξ : Rd d) :
    D.exponent ξ = D.a * ‖ξ‖ ^ 2 / 2 + D.jumpPart.exponent ξ := by
  rw [OriginDatum.exponent, D.exponentL_jumpPart ξ,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (D.jumpPart.exponentL_ne_top hd ξ),
    ENNReal.toReal_ofReal (div_nonneg (mul_nonneg D.a_nonneg (sq_nonneg _)) (by norm_num))]
  rfl

/-! ## Clause (1): the quadratic bound, split at `τ` -/

/-- **The quadratic bound, split at `τ`**: `1 - cos(rs) ≤ r²s²/2` on `(0,τ)`, `≤ 2` on `[τ,∞)`, so
`φ(s) ≤ (s²/2) ∫₀^τ k(r) r dr + 2 ∫_τ^∞ k(r) dr/r`. At `τ = 1` it is `cosProfileL_le_sq`. -/
theorem cosProfileL_le_sq_at (k : ℝ → ℝ) (hk : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r) {τ : ℝ} (hτ : 0 < τ)
    (s : ℝ) :
    cosProfileL k s ≤
      ENNReal.ofReal (s ^ 2 / 2) * (∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (k r * r)) +
      2 * ∫⁻ r in Ioi τ, ENNReal.ofReal (k r / r) := by
  rw [cosProfileL, ← Ioo_union_Ici_eq_Ioi hτ,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
  gcongr ?_ + ?_
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
    have hkr := hk r hr.1
    have h1 : 0 ≤ 1 - Real.cos (r * s) := by linarith [Real.cos_le_one (r * s)]
    have h2 : 1 - Real.cos (r * s) ≤ (r * s) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := r * s)]
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr0 : 0 < r := hr.1
    calc (1 - Real.cos (r * s)) * (k r / r) ≤ (r * s) ^ 2 / 2 * (k r / r) := by
          gcongr
      _ = s ^ 2 / 2 * (k r * r) := by field_simp
  · rw [← lintegral_const_mul' _ _ (by simp), Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    refine setLIntegral_mono' measurableSet_Ioi fun r _ => ?_
    gcongr
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.neg_one_le_cos (r * s)])

/-- `∫_τ^∞ k_d(r) dr/r < ∞` for `0 < τ ≤ 1`: on `(τ, 1]` the nonincreasing `k_d` is at most
`k_d(τ)`, and beyond `1` it is the datum's second integrability condition. -/
theorem OriginDatum.lintegral_Ioi_ne_top (D : OriginDatum d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫⁻ r in Ioi τ, ENNReal.ofReal (D.k r / r) ≠ ⊤ := by
  rw [← Ioc_union_Ioi_eq_Ioi hτ1, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  refine ENNReal.add_ne_top.mpr ⟨?_, D.integrable_at_top⟩
  have hvol : (volume : Measure ℝ) (Ioc τ 1) ≠ ⊤ := measure_Ioc_lt_top.ne
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := D.k τ / τ)) hvol) ?_
  calc ∫⁻ r in Ioc τ 1, ENNReal.ofReal (D.k r / r)
      ≤ ∫⁻ _r in Ioc τ 1, ENNReal.ofReal (D.k τ / τ) := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ENNReal.ofReal_le_ofReal ?_
        have hr0 : 0 < r := hτ.trans hr.1
        have hk : D.k r ≤ D.k τ := D.k_antitone hτ hr0 hr.1.le
        have hkτ : 0 ≤ D.k τ := D.k_nonneg τ hτ
        exact div_le_div₀ hkτ hk hτ hr.1.le
    _ = ENNReal.ofReal (D.k τ / τ) * volume (Ioc τ 1) := by
        rw [setLIntegral_const]

/-- **The exponent of a datum with no Gaussian part is at most quadratic, with a small
coefficient**: `F_d(ξ) ≤ ½|ξ|² ∫₀^τ k_d(r) r dr + 2 ∫_τ^∞ k_d(r) dr/r`, in `ℝ≥0∞`. -/
theorem OriginDatum.exponentL_le_sq_at (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) {τ : ℝ}
    (hτ : 0 < τ) (ξ : Rd d) :
    D.exponentL ξ ≤
      ENNReal.ofReal (‖ξ‖ ^ 2 / 2) * (∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (D.k r * r)) +
      2 * ∫⁻ r in Ioi τ, ENNReal.ofReal (D.k r / r) := by
  rw [D.exponentL_eq_sphere hd, ha, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  set B : ℝ≥0∞ :=
    ENNReal.ofReal (‖ξ‖ ^ 2 / 2) * (∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (D.k r * r)) +
      2 * ∫⁻ r in Ioi τ, ENNReal.ofReal (D.k r / r) with hB
  calc (ENNReal.ofReal (sphereArea d))⁻¹ *
        ∫⁻ η : sphere (0 : Rd d) 1, cosProfileL D.k ⟪ξ, (η : Rd d)⟫
          ∂((volume : Measure (Rd d)).toSphere)
      ≤ (ENNReal.ofReal (sphereArea d))⁻¹ *
        ∫⁻ _η : sphere (0 : Rd d) 1, B ∂((volume : Measure (Rd d)).toSphere) := by
        gcongr with η
        refine (cosProfileL_le_sq_at D.k D.k_nonneg hτ _).trans ?_
        have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
        have hle : ⟪ξ, (η : Rd d)⟫ ^ 2 ≤ ‖ξ‖ ^ 2 := by
          have := abs_real_inner_le_norm ξ (η : Rd d)
          rw [hη, mul_one] at this
          exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
        rw [hB]
        gcongr
    _ = B := by
        rw [lintegral_const, mul_comm, mul_assoc, mul_comm _ (ENNReal.ofReal (sphereArea d))⁻¹,
          inv_sphereArea_mul_toSphere_univ hd, mul_one]

/-- The same bound for the real exponent, `0 < τ ≤ 1`. -/
theorem OriginDatum.exponent_le_sq_at (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (ξ : Rd d) :
    D.exponent ξ ≤ ‖ξ‖ ^ 2 / 2 * (∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (D.k r * r)).toReal +
      2 * (∫⁻ r in Ioi τ, ENNReal.ofReal (D.k r / r)).toReal := by
  have hI : ∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (D.k r * r) ≠ ⊤ :=
    ne_top_of_le_ne_top D.integrable_near_zero (lintegral_mono_set (Ioo_subset_Ioo_right hτ1))
  have hT := D.lintegral_Ioi_ne_top hτ hτ1
  have hI' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := ‖ξ‖ ^ 2 / 2)) hI
  have hT' := ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hT
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hI', hT'⟩)
    (D.exponentL_le_sq_at hd ha hτ ξ)
  rwa [ENNReal.toReal_add hI' hT', ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h

/-- `∫₀^τ k_d(r) r dr → 0` as `τ ↓ 0`, in the form used: for every `ε > 0` there is `τ ∈ (0,1]`
with the integral at most `ε`. The integrand is integrable on `(0,1)`, the datum's first
integrability condition. -/
theorem OriginDatum.exists_lintegral_near_zero_le (D : OriginDatum d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      (∫⁻ r in Ioo (0 : ℝ) τ, ENNReal.ofReal (D.k r * r)).toReal ≤ ε := by
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun r => ENNReal.ofReal (D.k r * r))
    D.integrable_near_zero (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨r, -, hrpos, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
  refine ⟨min r 1, lt_min hr one_pos, min_le_right _ _, ?_⟩
  have hsub : Ioo (0 : ℝ) (min r 1) ⊆ Ioo 0 1 := Ioo_subset_Ioo_right (min_le_right _ _)
  have hmeas : (volume.restrict (Ioo (0 : ℝ) 1)) (Ioo 0 (min r 1)) < δ := by
    refine lt_of_le_of_lt (Measure.restrict_apply_le _ _) ?_
    rw [Real.volume_Ioo, sub_zero]
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hrδ
  have h := hδs _ hmeas
  rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub] at h
  exact ENNReal.toReal_le_of_le_ofReal hε.le h.le

/-- **`cor:origin-profile-exponent`(1)**: `F_d(ξ)/|ξ|² → a/2` as `|ξ| → ∞`. The exponent
determines the Gaussian coefficient. -/
theorem exponent_gaussian_limit (hd : 1 ≤ d) (D : OriginDatum d) :
    Tendsto (fun ξ : Rd d => D.exponent ξ / ‖ξ‖ ^ 2) (cocompact (Rd d)) (𝓝 (D.a / 2)) := by
  have hnorm := tendsto_norm_cocompact_atTop (E := Rd d)
  have hJ : Tendsto (fun ξ : Rd d => D.jumpPart.exponent ξ / ‖ξ‖ ^ 2) (cocompact (Rd d)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨τ, hτ, hτ1, hI⟩ := D.jumpPart.exists_lintegral_near_zero_le hε
    set T := (∫⁻ r in Ioi τ, ENNReal.ofReal (D.jumpPart.k r / r)).toReal with hT
    have hbig : ∀ᶠ ξ in cocompact (Rd d), 4 * T / ε < ‖ξ‖ ^ 2 :=
      ((tendsto_pow_atTop two_ne_zero).comp hnorm).eventually_gt_atTop _
    filter_upwards [hbig, hnorm.eventually_ge_atTop 1] with ξ hξ hξ1
    have hsq : 0 < ‖ξ‖ ^ 2 := pow_pos (lt_of_lt_of_le one_pos hξ1) 2
    have hup := D.jumpPart.exponent_le_sq_at hd rfl hτ hτ1 ξ
    have h0 := D.jumpPart.exponent_nonneg ξ
    have h4 : 4 * T < ‖ξ‖ ^ 2 * ε := (div_lt_iff₀ hε).mp hξ
    have h5 := mul_le_mul_of_nonneg_left hI (show 0 ≤ ‖ξ‖ ^ 2 / 2 by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg h0 hsq.le), div_lt_iff₀ hsq]
    linarith
  have hsum : Tendsto (fun ξ : Rd d => D.a / 2 + D.jumpPart.exponent ξ / ‖ξ‖ ^ 2)
      (cocompact (Rd d)) (𝓝 (D.a / 2 + 0)) := tendsto_const_nhds.add hJ
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hnorm.eventually_ge_atTop 1] with ξ hξ1
  have hsq : ‖ξ‖ ^ 2 ≠ 0 := (pow_pos (lt_of_lt_of_le one_pos hξ1) 2).ne'
  rw [D.exponent_eq_add hd ξ]
  field_simp

/-! ## Clause (2): the two logarithmic bounds -/

/-- **The lower logarithmic bound**, from `OriginDatum.exponent_decay`: for a datum with Gaussian
coefficient `0` and a finite `0 ≤ β < c` there is `K` with `F_d(ξ) ≥ β log|ξ| - K` for
`|ξ| ≥ 1`. -/
theorem OriginDatum.exponent_ge_log (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ K : ℝ, ∀ ξ : Rd d, 1 ≤ ‖ξ‖ → β * Real.log ‖ξ‖ - K ≤ D.exponent ξ := by
  obtain ⟨C, hC⟩ := D.exponent_decay hd ha β hβ
  have hCpos : 0 < C := by
    have h := hC 0
    rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact lt_of_lt_of_le (Real.exp_pos _) h
  refine ⟨Real.log C, fun ξ hξ => ?_⟩
  have hpos : 0 < (1 + ‖ξ‖) ^ (-β) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : -D.exponent ξ ≤ Real.log (C * (1 + ‖ξ‖) ^ (-β)) := by
    have := Real.log_le_log (Real.exp_pos _) (hC ξ)
    rwa [Real.log_exp] at this
  rw [Real.log_mul hCpos.ne' hpos.ne', Real.log_rpow (by linarith)] at h1
  have h2 : Real.log ‖ξ‖ ≤ Real.log (1 + ‖ξ‖) := Real.log_le_log (by linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hβ0
  linarith

/-- **The quotient `F_d/log|ξ|` tends to the profile at the origin**, for a datum with Gaussian
coefficient `0`, along any family `x` with `|x| → ∞`; in `ℝ≥0∞`, for `ENNReal.ofReal` of the
quotient, which is the quotient where `|x| ≥ 1`. -/
theorem OriginDatum.tendsto_ofReal_exponent_div_log (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    {ι : Type*} {l : Filter ι} {x : ι → Rd d} (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => ENNReal.ofReal (D.exponent (x i) / Real.log ‖x i‖)) l
      (𝓝 D.profileAtOrigin) := by
  have hlog : Tendsto (fun i => Real.log ‖x i‖) l atTop := Real.tendsto_log_atTop.comp hx
  have h1 : ∀ᶠ i in l, 1 ≤ ‖x i‖ := hx.eventually_ge_atTop 1
  have h3 : ∀ᶠ i in l, 0 < Real.log ‖x i‖ := hlog.eventually_gt_atTop 0
  rw [tendsto_order]
  constructor
  · -- below: every `b < c` is eventually exceeded
    intro b hb
    obtain ⟨β₀, hβ₀0, hbβ₀, hβ₀c⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    obtain ⟨β, -, hβ₀β, hβc⟩ := ENNReal.lt_iff_exists_real_btwn.mp hβ₀c
    have hββ : β₀ < β := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hβ₀0).mp hβ₀β
    obtain ⟨K, hK⟩ := D.exponent_ge_log hd ha (hβ₀0.trans hββ.le) hβc
    have h2 : ∀ᶠ i in l, K / (β - β₀) < Real.log ‖x i‖ := hlog.eventually_gt_atTop _
    filter_upwards [h1, h2, h3] with i hi1 hi2 hi3
    refine lt_of_lt_of_le hbβ₀ (ENNReal.ofReal_le_ofReal ?_)
    rw [le_div_iff₀ hi3]
    have hKi := hK (x i) hi1
    have h4 : K < Real.log ‖x i‖ * (β - β₀) := (div_lt_iff₀ (sub_pos.mpr hββ)).mp hi2
    linarith
  · -- above: every `b > c` is eventually an upper bound, by `lem:isotropic-exponent-log`(1)
    intro b hb
    have hc : D.profileAtOrigin ≠ ⊤ := ne_top_of_lt hb
    obtain ⟨γ, -, hcγ, hγb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    have hcγ' : D.profileAtOrigin.toReal < γ := ENNReal.toReal_lt_of_lt_ofReal hcγ
    set c := D.profileAtOrigin.toReal with hcdef
    set K := 13 / 4 * c + 2 * D.tailConst with hKdef
    have h2 : ∀ᶠ i in l, K / (γ - c) < Real.log ‖x i‖ := hlog.eventually_gt_atTop _
    filter_upwards [h1, h2, h3] with i hi1 hi2 hi3
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hγb
    rw [div_le_iff₀ hi3]
    have hup := (isotropic_exponent_log_bound hd D ha hc (x i) hi1).1
    have h4 : K < Real.log ‖x i‖ * (γ - c) := (div_lt_iff₀ (sub_pos.mpr hcγ')).mp hi2
    linarith

/-- From `ℝ≥0∞` to `EReal`: if `ENNReal.ofReal (f i) → c` and `f` is eventually nonnegative, then
`f i → c` in the extended reals. -/
theorem tendsto_coe_ereal_of_tendsto_ofReal {ι : Type*} {l : Filter ι} {f : ι → ℝ} {c : ℝ≥0∞}
    (h0 : ∀ᶠ i in l, 0 ≤ f i) (h : Tendsto (fun i => ENNReal.ofReal (f i)) l (𝓝 c)) :
    Tendsto (fun i => ((f i : ℝ) : EReal)) l (𝓝 (c : EReal)) := by
  have hc : Tendsto (fun i => ((ENNReal.ofReal (f i) : ℝ≥0∞) : EReal)) l (𝓝 (c : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto c).comp h
  refine hc.congr' ?_
  filter_upwards [h0] with i hi
  rw [EReal.coe_ennreal_ofReal, max_eq_left hi]

/-- **`cor:origin-profile-exponent`(2)**: `(F_d(ξ) - ½a|ξ|²)/log|ξ| → c = k_d(0+)` as `|ξ| → ∞`,
in the extended reals (`c = ∞` allowed: the quotient then tends to `+∞`). The exponent determines
the profile at the origin. -/
theorem exponent_profile_limit (hd : 1 ≤ d) (D : OriginDatum d) :
    Tendsto (fun ξ : Rd d => (((D.exponent ξ - D.a * ‖ξ‖ ^ 2 / 2) / Real.log ‖ξ‖ : ℝ) : EReal))
      (cocompact (Rd d)) (𝓝 (D.profileAtOrigin : EReal)) := by
  have hnorm := tendsto_norm_cocompact_atTop (E := Rd d)
  have h : Tendsto (fun ξ : Rd d => ENNReal.ofReal (D.jumpPart.exponent ξ / Real.log ‖ξ‖))
      (cocompact (Rd d)) (𝓝 D.profileAtOrigin) :=
    D.jumpPart.tendsto_ofReal_exponent_div_log hd rfl hnorm
  have h0 : ∀ᶠ ξ in cocompact (Rd d), 0 ≤ D.jumpPart.exponent ξ / Real.log ‖ξ‖ := by
    filter_upwards [hnorm.eventually_ge_atTop 1] with ξ hξ
    exact div_nonneg (D.jumpPart.exponent_nonneg ξ) (Real.log_nonneg hξ)
  refine (tendsto_coe_ereal_of_tendsto_ofReal h0 h).congr fun ξ => ?_
  rw [D.exponent_eq_add hd ξ, add_sub_cancel_left]

/-- **`cor:origin-profile-exponent`(2)**, the last sentence: for a datum with Gaussian coefficient
`0` and a law `μ` of it, `-log|μ̂(ξ)|/log|ξ| → c` as `|ξ| → ∞`. The profile at the origin is the
power at which the transform falls off. -/
theorem transform_profile_limit (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    Tendsto (fun ξ : Rd d => ((-Real.log ‖charFun μ ξ‖ / Real.log ‖ξ‖ : ℝ) : EReal))
      (cocompact (Rd d)) (𝓝 (D.profileAtOrigin : EReal)) := by
  refine (exponent_profile_limit hd D).congr fun ξ => ?_
  rw [hμ.norm_charFun, Real.log_exp, neg_neg, ha, zero_mul, zero_div, sub_zero]

/-! ## Clause (3): the same numbers in every dimension -/

/-- Clause (1) along a ray, for a datum whose exponent is `F(|ξ|)`: `F(r)/r² → a/2`. -/
theorem OriginDatum.tendsto_radial_gaussian (hd : 1 ≤ d) (D : OriginDatum d) (F : ℝ → ℝ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) :
    Tendsto (fun r : ℝ => F r / r ^ 2) atTop (𝓝 (D.a / 2)) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he
  have he1 : ‖e‖ = 1 := by simp [he, ebasis]
  have hray : Tendsto (fun r : ℝ => r • e) atTop (cocompact (Rd d)) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_abs_atTop_atTop.congr fun r => ?_
    rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
  refine ((exponent_gaussian_limit hd D).comp hray).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hn : ‖r • e‖ = r := by rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr]
  simp only [Function.comp_apply]
  rw [← hD (r • e), hn]

/-- Clause (2) along a ray, for a datum whose exponent is `F(|ξ|)`:
`(F(r) - ½ a r²)/log r → c`. -/
theorem OriginDatum.tendsto_radial_profile (hd : 1 ≤ d) (D : OriginDatum d) (F : ℝ → ℝ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) :
    Tendsto (fun r : ℝ => (((F r - D.a * r ^ 2 / 2) / Real.log r : ℝ) : EReal)) atTop
      (𝓝 (D.profileAtOrigin : EReal)) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he
  have he1 : ‖e‖ = 1 := by simp [he, ebasis]
  have hray : Tendsto (fun r : ℝ => r • e) atTop (cocompact (Rd d)) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_abs_atTop_atTop.congr fun r => ?_
    rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
  refine ((exponent_profile_limit hd D).comp hray).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hn : ‖r • e‖ = r := by rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr]
  simp only [Function.comp_apply]
  rw [← hD (r • e), hn]

/-- **`cor:origin-profile-exponent`(3)**: two isotropic origin data, in dimensions `d` and `d'`,
whose exponents are one function `F` of the radius have the same Gaussian coefficient and the same
profile at the origin. Both numbers are limits of `F` at infinity. -/
theorem origin_profile_dimension_free {d d' : ℕ} (hd : 1 ≤ d) (hd' : 1 ≤ d') (D : OriginDatum d)
    (D' : OriginDatum d') (F : ℝ → ℝ) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ)
    (hD' : ∀ ξ : Rd d', F ‖ξ‖ = D'.exponent ξ) :
    D'.a = D.a ∧ D'.profileAtOrigin = D.profileAtOrigin := by
  have ha : D'.a = D.a := by
    have := tendsto_nhds_unique (D'.tendsto_radial_gaussian hd' F hD')
      (D.tendsto_radial_gaussian hd F hD)
    linarith
  refine ⟨ha, ?_⟩
  have h2 := D.tendsto_radial_profile hd F hD
  have h2' := D'.tendsto_radial_profile hd' F hD'
  rw [ha] at h2'
  exact EReal.coe_ennreal_injective (tendsto_nhds_unique h2' h2)

end AffineHemigroup
