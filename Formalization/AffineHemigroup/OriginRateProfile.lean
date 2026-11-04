/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginRate
import AffineHemigroup.ExponentProfile

/-!
# `prop:origin-rate-profile-d`: the rate at the origin through the polar profile

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:origin-rate-profile-d` (Q-0427).

For an isotropic origin datum `(0, k_d)` in dimension `d ≥ 1` with profile at the origin
`0 < c ≤ d`, a law `μ` of it, and every `q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx`, with
`A = e^{-C_k - cϰ_d}` (`OriginDatum.profileConst`), `K` the factor `OriginDatum.slowFactor` and
`𝓛(s) = ∫_s^1 K(y) dy/y` (`OriginDatum.slowLog`), as `s ↓ 0`:

* clause (1), `c < d`, `Q = R(d,c) A`: `origin_density_rate_profile`
  (`q(s)/(Q s^{c-d} K(s)) → 1`) and `origin_ball_rate_profile`
  (`μ{|x| ≤ s}/(Q |S^{d-1}| c⁻¹ s^c K(s)) → 1`);
* clause (2), `c < d`: `origin_density_power_of_integrable` (`q(s) s^{d-c} → Q K(0+) > 0` and a
  bound `q(s) ≤ C s^{c-d}` at every `s > 0`, when `(c - k_d(u))/u` is integrable on `(0,1]`),
  `origin_density_power_of_not_integrable` (`q(s) s^{d-c} → ∞` and no such `C`, when it is not);
* clause (3), `c = d`, `B = (2π)^{-d} |S^{d-1}| A`: `origin_density_rate_profile_critical`,
  `origin_ball_rate_profile_critical`, `slowLog_bounds`
  (`log(1/s) ≤ 𝓛(s) ≤ K(s) log(1/s)` on `(0,1]`), `slowLog_div_log` (the limit of
  `𝓛(s)/log(1/s)`, `K(0+)` or `∞`), `origin_density_log_of_integrable`,
  `origin_density_log_of_not_integrable`;
* `origin_rate_profile`, `origin_rate_profile_critical`: the bundles, with the existence of `q`
  (`radial_monotone_law`).

**What is spent.** Nothing of its own. The limits for a given law and density print ledger A11,
through `origin_density_rate`, `origin_ball_rate` and their critical forms; `slowLog_bounds` and
`slowLog_div_log` are Lean core; the two bundles add A8, A2 and A3(iii).

**The route** is the proof of record's: `prop:isotropic-exponent-profile`(3) at `ρ = 1/s`
(`IsLawOf.tendsto_transform_div_profile`) multiplied into the two limits of `prop:origin-rate-d`;
at the threshold, the comparison of the two divergent integrals `∫_0^R μ̂(ρe) ρ^{d-1} dρ` and
`A ∫_1^R K(1/ρ) dρ/ρ` (`tendsto_integral_div_integral`), with the substitution `y = 1/ρ`
(`integral_slowFactor_inv`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Real RealInnerProductSpace

variable {d : ℕ}

namespace OriginDatum

/-- **`A := e^{-C_k - cϰ_d}`** (`prop:origin-rate-profile-d`), the constant of the transform at
infinity. -/
noncomputable def profileConst (D : OriginDatum d) : ℝ :=
  Real.exp (-D.tailConst - D.profileAtOrigin.toReal * exponentConst d)

/-- **`𝓛(s) := ∫_s^1 K(y) dy/y`** (`prop:origin-rate-profile-d`(3)); a total function, read on
`(0,1]`. -/
noncomputable def slowLog (D : OriginDatum d) (s : ℝ) : ℝ := ∫ y in s..1, D.slowFactor y / y

end OriginDatum

theorem OriginDatum.profileConst_pos (D : OriginDatum d) : 0 < D.profileConst := Real.exp_pos _

theorem OriginDatum.slowFactor_pos (D : OriginDatum d) (x : ℝ) : 0 < D.slowFactor x :=
  Real.exp_pos _

/-! ## The transform at the frequency `1/s` -/

/-- **`eq:profile-transform-at-s`**: `μ̂(e/s) / (A s^c K(s)) → 1` as `s ↓ 0`. -/
theorem IsLawOf.tendsto_transform_div_profile (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {μ : Measure (Rd d)} (hμ : IsLawOf D μ) {e : Rd d}
    (he : ‖e‖ = 1) :
    Tendsto (fun s : ℝ => (charFun μ (s⁻¹ • e)).re /
      (D.profileConst * s ^ D.profileAtOrigin.toReal * D.slowFactor s)) (𝓝[>] 0) (𝓝 1) := by
  have h := ((exponent_profile_asymptotic hd D ha hc he).2).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  simp only [Function.comp_apply]
  rw [hμ.charFun_re, inv_inv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, neg_neg]
  rfl

/-! ## Clause (1): below the threshold -/

/-- **`prop:origin-rate-profile-d`(1), the density**: for a datum with Gaussian coefficient `0`
and `0 < c < d`, every law `μ` of it and every `q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx`:
`q(s) / (Q s^{c-d} K(s)) → 1` as `s ↓ 0`, `Q = R(d,c) A`. Spends A11. -/
theorem origin_density_rate_profile (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s / (rateConst d D.profileAtOrigin.toReal * D.profileConst *
      s ^ (D.profileAtOrigin.toReal - d) * D.slowFactor s)) (𝓝[>] 0) (𝓝 1) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  obtain ⟨hctop, -, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  set c := D.profileAtOrigin.toReal with hcdef
  have h1 := origin_density_rate hd D ha hc hcd μ hμ he hq hμq
  have h2 := hμ.tendsto_transform_div_profile hd ha hctop he
  have h := h1.mul h2
  rw [mul_one] at h
  simp only [← hcdef] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hχ : 0 < (charFun μ (s⁻¹ • e)).re := by rw [hμ.charFun_re]; exact Real.exp_pos _
  set χ := (charFun μ (s⁻¹ • e)).re with hχdef
  have hK := D.slowFactor_pos s
  have hA := D.profileConst_pos
  have hpow : s ^ (c - d) = s ^ (-(d : ℝ)) * s ^ c := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h1' : 0 < s ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hs _
  have h2' : 0 < s ^ c := Real.rpow_pos_of_pos hs _
  rw [hpow]
  field_simp

/-- **`prop:origin-rate-profile-d`(1), the mass of a ball**: for a datum with Gaussian
coefficient `0` and `0 < c < d`, and every law `μ` of it:
`μ{|x| ≤ s} / (Q |S^{d-1}| c⁻¹ s^c K(s)) → 1` as `s ↓ 0`, `Q = R(d,c) A`. Spends A11. -/
theorem origin_ball_rate_profile (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) :
    Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
      (rateConst d D.profileAtOrigin.toReal * D.profileConst * sphereArea d /
        D.profileAtOrigin.toReal * s ^ D.profileAtOrigin.toReal * D.slowFactor s))
      (𝓝[>] 0) (𝓝 1) := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  set c := D.profileAtOrigin.toReal with hcdef
  have h1 := origin_ball_rate hd D ha hc hcd μ hμ he
  have h2 := hμ.tendsto_transform_div_profile hd ha hctop he
  have h := h1.mul h2
  rw [mul_one] at h
  simp only [← hcdef] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hχ : 0 < (charFun μ (s⁻¹ • e)).re := by rw [hμ.charFun_re]; exact Real.exp_pos _
  set χ := (charFun μ (s⁻¹ • e)).re with hχdef
  have hK := D.slowFactor_pos s
  have hA := D.profileConst_pos
  have h2' : 0 < s ^ c := Real.rpow_pos_of_pos hs _
  field_simp

/-! ## Clause (2): when a pure power holds -/

/-- `q(s) s^{d-c} / (Q K(s)) → 1`: clause (1) with the power moved to the numerator. -/
theorem tendsto_density_mul_rpow_div (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - D.profileAtOrigin.toReal) /
      (rateConst d D.profileAtOrigin.toReal * D.profileConst * D.slowFactor s))
      (𝓝[>] 0) (𝓝 1) := by
  refine (origin_density_rate_profile hd D ha hc hcd μ hμ hq hμq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hpow : s ^ (D.profileAtOrigin.toReal - d)
      = (s ^ ((d : ℝ) - D.profileAtOrigin.toReal))⁻¹ := by
    rw [← Real.rpow_neg hs.le]; congr 1; ring
  have h1 : 0 < s ^ ((d : ℝ) - D.profileAtOrigin.toReal) := Real.rpow_pos_of_pos hs _
  rw [hpow]
  field_simp

/-- **`prop:origin-rate-profile-d`(2), the convergent case**: for `0 < c < d`, if
`(c - k_d(u))/u` is integrable on `(0,1]`, then `q(s) s^{d-c} → Q K(0+)`, a positive number, and
there is `C` with `q(s) ≤ C s^{c-d}` for every `s > 0`. Spends A11. -/
theorem origin_density_power_of_integrable (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    (hI : IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - D.profileAtOrigin.toReal)) (𝓝[>] 0)
        (𝓝 (rateConst d D.profileAtOrigin.toReal * D.profileConst * D.slowFactorZero)) ∧
      0 < rateConst d D.profileAtOrigin.toReal * D.profileConst * D.slowFactorZero ∧
      ∃ C : ℝ, ∀ s : ℝ, 0 < s → q s ≤ C * s ^ (D.profileAtOrigin.toReal - d) := by
  haveI := hμ.1
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  have hcd' : D.profileAtOrigin.toReal < d := by
    have := (ENNReal.toReal_lt_toReal hctop (ENNReal.natCast_ne_top d)).mpr hcd
    simpa using this
  set c := D.profileAtOrigin.toReal with hcdef
  set Q := rateConst d c * D.profileConst with hQ
  have hQpos : 0 < Q := mul_pos (rateConst_pos hc0 hcd') D.profileConst_pos
  obtain ⟨hKlim, hK1, -⟩ := slowFactor_tendsto_of_integrable D hctop hI
  have hlim : Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - c)) (𝓝[>] 0)
      (𝓝 (Q * D.slowFactorZero)) := by
    have h1 := tendsto_density_mul_rpow_div hd D ha hc hcd μ hμ hq hμq
    have h2 := h1.mul (hKlim.const_mul Q)
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (_ : 0 < s)
    exact div_mul_cancel₀ _ (mul_pos hQpos (D.slowFactor_pos s)).ne'
  have hpos : 0 < Q * D.slowFactorZero := mul_pos hQpos (lt_of_lt_of_le one_pos hK1)
  refine ⟨hlim, hpos, ?_⟩
  -- near `0` the limit bounds `q(s) s^{d-c}`; away from `0`, `q(s) V_d s^d ≤ 1`
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), q s * s ^ ((d : ℝ) - c) < Q * D.slowFactorZero + 1 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hs₀' : (0 : ℝ) < s₀ := hs₀
  set V := (volume (ball (0 : Rd d) 1)).toReal with hV
  have hVpos : 0 < V := volume_unitBall_toReal_pos
  refine ⟨max (Q * D.slowFactorZero + 1) (s₀ ^ (-c) / V), fun s hs => ?_⟩
  have hp1 : 0 < s ^ (c - d) := Real.rpow_pos_of_pos hs _
  have hp2 : 0 < s ^ ((d : ℝ) - c) := Real.rpow_pos_of_pos hs _
  have hinv : s ^ ((d : ℝ) - c) * s ^ (c - d) = 1 := by
    rw [← Real.rpow_add hs]; simp
  have hbound : q s * s ^ ((d : ℝ) - c) ≤ max (Q * D.slowFactorZero + 1) (s₀ ^ (-c) / V) := by
    rcases lt_or_ge s s₀ with hlt | hge
    · exact le_trans (le_of_lt (hsub ⟨hs, hlt⟩)) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have h1 := radial_density_le_ball hd hq hμq hs
      have h2 : (μ (ball 0 s)).toReal ≤ 1 := by
        have := prob_le_one (μ := μ) (s := ball (0 : Rd d) s)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      have hsd : 0 < s ^ d := pow_pos hs d
      have h3 : q s ≤ 1 / (V * s ^ d) := by
        rw [le_div_iff₀ (mul_pos hVpos hsd)]; linarith
      have h4 : s ^ ((d : ℝ) - c) / s ^ d = s ^ (-c) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hs]; congr 1; ring
      have h5 : s ^ (-c) ≤ s₀ ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hs₀' hge (by linarith)
      calc q s * s ^ ((d : ℝ) - c) ≤ 1 / (V * s ^ d) * s ^ ((d : ℝ) - c) :=
            mul_le_mul_of_nonneg_right h3 hp2.le
        _ = s ^ (-c) / V := by rw [← h4]; field_simp
        _ ≤ s₀ ^ (-c) / V := div_le_div_of_nonneg_right h5 hVpos.le
  calc q s = q s * s ^ ((d : ℝ) - c) * s ^ (c - d) := by rw [mul_assoc, hinv, mul_one]
    _ ≤ max (Q * D.slowFactorZero + 1) (s₀ ^ (-c) / V) * s ^ (c - d) :=
        mul_le_mul_of_nonneg_right hbound hp1.le

/-- **`prop:origin-rate-profile-d`(2), the divergent case**: for `0 < c < d`, if `(c - k_d(u))/u`
is not integrable on `(0,1]`, then `q(s) s^{d-c} → ∞`, and there is no `C` with
`q(s) ≤ C s^{c-d}` for every `s > 0`. Spends A11. -/
theorem origin_density_power_of_not_integrable (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    (hI : ¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - D.profileAtOrigin.toReal)) (𝓝[>] 0) atTop ∧
      ¬ ∃ C : ℝ, ∀ s : ℝ, 0 < s → q s ≤ C * s ^ (D.profileAtOrigin.toReal - d) := by
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  have hcd' : D.profileAtOrigin.toReal < d := by
    have := (ENNReal.toReal_lt_toReal hctop (ENNReal.natCast_ne_top d)).mpr hcd
    simpa using this
  set c := D.profileAtOrigin.toReal with hcdef
  set Q := rateConst d c * D.profileConst with hQ
  have hQpos : 0 < Q := mul_pos (rateConst_pos hc0 hcd') D.profileConst_pos
  have hKtop := slowFactor_tendsto_atTop D hctop hI
  have hlim : Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - c)) (𝓝[>] 0) atTop := by
    have h1 := tendsto_density_mul_rpow_div hd D ha hc hcd μ hμ hq hμq
    have h2 := h1.pos_mul_atTop one_pos (hKtop.const_mul_atTop hQpos)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (_ : 0 < s)
    exact div_mul_cancel₀ _ (mul_pos hQpos (D.slowFactor_pos s)).ne'
  refine ⟨hlim, ?_⟩
  rintro ⟨C, hC⟩
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), C + 1 ≤ q s * s ^ ((d : ℝ) - c) := tendsto_atTop.1 hlim (C + 1)
  obtain ⟨s, h1, hs⟩ := (hev.and self_mem_nhdsWithin).exists
  have hs' : (0 : ℝ) < s := hs
  have hp2 : 0 < s ^ ((d : ℝ) - c) := Real.rpow_pos_of_pos hs' _
  have hinv : s ^ (c - d) * s ^ ((d : ℝ) - c) = 1 := by
    rw [← Real.rpow_add hs']; simp
  have h2 := mul_le_mul_of_nonneg_right (hC s hs') hp2.le
  rw [mul_assoc, hinv, mul_one] at h2
  linarith

/-! ## Clause (3): at the threshold -/

/-- `y ↦ K(y)/y` is interval integrable between two points of `(0,1]`. -/
theorem OriginDatum.intervalIntegrable_slowFactor_div (D : OriginDatum d)
    (hc : D.profileAtOrigin ≠ ⊤) {x y : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hy : y ∈ Ioc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => D.slowFactor u / u) volume x y := by
  have hcont := (slowFactor_basic D hc).2.1
  refine ContinuousOn.intervalIntegrable ?_
  have hsub : uIcc x y ⊆ Ioc (0 : ℝ) 1 := fun u hu =>
    ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) hu.1, le_trans hu.2 (max_le hx.2 hy.2)⟩
  exact (hcont.mono hsub).div continuousOn_id fun u hu => (hsub hu).1.ne'

/-- **`prop:origin-rate-profile-d`(3), the bounds on `𝓛`**: for `0 < s ≤ 1`,
`log(1/s) ≤ 𝓛(s) ≤ K(s) log(1/s)`. Lean core. -/
theorem slowLog_bounds (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Real.log (1 / s) ≤ D.slowLog s ∧ D.slowLog s ≤ D.slowFactor s * Real.log (1 / s) := by
  obtain ⟨-, -, hanti, hK⟩ := slowFactor_basic D hc
  have hlog : ∫ v in s..1, v⁻¹ = Real.log (1 / s) := integral_inv_of_pos hs.1 one_pos
  have hiinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume s 1 := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
    rw [uIcc_of_le hs.2] at hv
    exact ne_of_gt (lt_of_lt_of_le hs.1 hv.1)
  have hint := D.intervalIntegrable_slowFactor_div hc hs ⟨one_pos, le_rfl⟩
  constructor
  · rw [← hlog]
    refine intervalIntegral.integral_mono_on hs.2 hiinv hint fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le hs.1 hu.1
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (inv_nonneg.2 hu0.le) (hK u ⟨hu0, hu.2⟩).1
  · rw [← hlog, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hs.2 hint (hiinv.const_mul _) fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le hs.1 hu.1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hanti hs ⟨hu0, hu.2⟩ hu.1) (inv_nonneg.2 hu0.le)

/-- `log(1/s) → ∞` as `s ↓ 0`. -/
theorem tendsto_log_one_div_nhdsGT_zero :
    Tendsto (fun s : ℝ => Real.log (1 / s)) (𝓝[>] 0) atTop := by
  have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine h.congr fun s => ?_
  simp only [Function.comp_apply, one_div]

/-- For `0 < y₀ < 1` and every `a < K(y₀)`: `𝓛(s)/log(1/s) > a` for all small `s`. -/
theorem eventually_lt_slowLog_div_log (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {y₀ a : ℝ}
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (ha : a < D.slowFactor y₀) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), a < D.slowLog s / Real.log (1 / s) := by
  obtain ⟨-, -, hanti, hK⟩ := slowFactor_basic D hc
  have hy₀' : y₀ ∈ Ioc (0 : ℝ) 1 := ⟨hy₀.1, hy₀.2.le⟩
  -- `K(y₀)(1 + log y₀/log(1/s)) → K(y₀)`
  have hg : Tendsto (fun s : ℝ => D.slowFactor y₀ * (1 + Real.log y₀ / Real.log (1 / s)))
      (𝓝[>] 0) (𝓝 (D.slowFactor y₀)) := by
    have h1 : Tendsto (fun s : ℝ => Real.log y₀ / Real.log (1 / s)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_log_one_div_nhdsGT_zero
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).add h1).const_mul (D.slowFactor y₀)
    simpa using h2
  have hev := (tendsto_order.1 hg).1 a ha
  have hlogpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / s) :=
    tendsto_log_one_div_nhdsGT_zero.eventually (eventually_gt_atTop 0)
  filter_upwards [hev, hlogpos, Ioo_mem_nhdsGT hy₀.1] with s hs hlog hsy
  have hs1 : s ∈ Ioc (0 : ℝ) 1 := ⟨hsy.1, (lt_trans hsy.2 hy₀.2).le⟩
  refine lt_of_lt_of_le hs ?_
  rw [le_div_iff₀ hlog]
  -- `𝓛(s) ≥ ∫_s^{y₀} K(y) dy/y ≥ K(y₀) log(y₀/s)`
  have hint1 := D.intervalIntegrable_slowFactor_div hc hs1 hy₀'
  have hint2 := D.intervalIntegrable_slowFactor_div hc hy₀' ⟨one_pos, le_rfl⟩
  have hsplit : D.slowLog s = (∫ u in s..y₀, D.slowFactor u / u) +
      ∫ u in y₀..1, D.slowFactor u / u :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hnn : 0 ≤ ∫ u in y₀..1, D.slowFactor u / u :=
    intervalIntegral.integral_nonneg hy₀.2.le fun u hu =>
      div_nonneg (D.slowFactor_pos u).le (lt_of_lt_of_le hy₀.1 hu.1).le
  have hlog' : ∫ v in s..y₀, v⁻¹ = Real.log (y₀ / s) := integral_inv_of_pos hsy.1 hy₀.1
  have hiinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume s y₀ := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun v hv => ?_)
    rw [uIcc_of_le hsy.2.le] at hv
    exact ne_of_gt (lt_of_lt_of_le hsy.1 hv.1)
  have hlow : D.slowFactor y₀ * Real.log (y₀ / s) ≤ ∫ u in s..y₀, D.slowFactor u / u := by
    rw [← hlog', ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hsy.2.le (hiinv.const_mul _) hint1 fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le hsy.1 hu.1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (hanti ⟨hu0, le_trans hu.2 hy₀.2.le⟩ hy₀' hu.2) (inv_nonneg.2 hu0.le)
  have e : D.slowFactor y₀ * (1 + Real.log y₀ / Real.log (1 / s)) * Real.log (1 / s)
      = D.slowFactor y₀ * Real.log (y₀ / s) := by
    rw [Real.log_div hy₀.1.ne' hsy.1.ne', one_div, Real.log_inv]
    have hne : Real.log s ≠ 0 := by
      have : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
      rw [this] at hlog
      linarith
    field_simp
    ring
  rw [e, hsplit]
  linarith

/-- **`prop:origin-rate-profile-d`(3), the limit of `𝓛(s)/log(1/s)`**: `K(0+)` if
`(c - k_d(u))/u` is integrable on `(0,1]`, and `∞` if it is not. Lean core. -/
theorem slowLog_div_log (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) :
    (IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => D.slowLog s / Real.log (1 / s)) (𝓝[>] 0) (𝓝 D.slowFactorZero)) ∧
      (¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => D.slowLog s / Real.log (1 / s)) (𝓝[>] 0) atTop) := by
  have hmem : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hlogpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / s) :=
    tendsto_log_one_div_nhdsGT_zero.eventually (eventually_gt_atTop 0)
  constructor
  · intro hI
    obtain ⟨hKlim, -, hKle⟩ := slowFactor_tendsto_of_integrable D hc hI
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨y₀, hy₁, hy₂⟩ := (((tendsto_order.1 hKlim).1 a ha).and hmem).exists
      exact eventually_lt_slowLog_div_log D hc hy₂ hy₁
    · filter_upwards [hlogpos, hmem] with s hlog hs
      have hs1 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      refine lt_of_le_of_lt ?_ hb
      rw [div_le_iff₀ hlog]
      exact le_trans (slowLog_bounds D hc hs1).2
        (mul_le_mul_of_nonneg_right (hKle s hs1) hlog.le)
  · intro hI
    have hKtop := slowFactor_tendsto_atTop D hc hI
    refine tendsto_atTop.2 fun M => ?_
    obtain ⟨y₀, hy₁, hy₂⟩ := ((tendsto_atTop.1 hKtop (M + 1)).and hmem).exists
    filter_upwards [eventually_lt_slowLog_div_log D hc hy₂ (show M < D.slowFactor y₀ by linarith)]
      with s hs
    exact hs.le

/-- **The substitution `y = 1/ρ`**: `∫_1^R K(1/ρ) dρ/ρ = 𝓛(1/R)` for `R ≥ 1`. -/
theorem integral_slowFactor_inv (D : OriginDatum d) (hc : D.profileAtOrigin ≠ ⊤) {R : ℝ}
    (hR : 1 ≤ R) : ∫ ρ in (1 : ℝ)..R, D.slowFactor ρ⁻¹ / ρ = D.slowLog R⁻¹ := by
  have hcont := (slowFactor_basic D hc).2.1
  have hpos : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := fun x hx => by
    rw [uIcc_of_le hR] at hx; exact lt_of_lt_of_le one_pos hx.1
  have hf : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc 1 R) :=
    continuousOn_inv₀.mono fun x hx => (hpos x hx).ne'
  have hff' : ∀ x ∈ Ioo (min 1 R) (max 1 R),
      HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(x ^ 2)⁻¹) (Ioi x) x := by
    intro x hx
    rw [min_eq_left hR] at hx
    exact (hasDerivAt_inv (lt_trans one_pos hx.1).ne').hasDerivWithinAt
  have hf' : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (uIcc 1 R) :=
    ((continuous_pow 2).continuousOn.inv₀ fun x hx => (pow_pos (hpos x hx) 2).ne').neg
  have himg : (fun x : ℝ => x⁻¹) '' uIcc 1 R ⊆ Ioc (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h0 := hpos x hx
    rw [uIcc_of_le hR] at hx
    exact ⟨inv_pos.2 h0, inv_le_one_of_one_le₀ hx.1⟩
  have hg : ContinuousOn (fun u : ℝ => D.slowFactor u / u) ((fun x : ℝ => x⁻¹) '' uIcc 1 R) :=
    ((hcont.mono himg).div continuousOn_id fun u hu => (himg hu).1.ne')
  have h := intervalIntegral.integral_comp_mul_deriv'' hf hff' hf' hg
  rw [inv_one] at h
  have hL : ∫ ρ in (1 : ℝ)..R, D.slowFactor ρ⁻¹ / ρ
      = -∫ x in (1 : ℝ)..R, ((fun u : ℝ => D.slowFactor u / u) ∘ fun x : ℝ => x⁻¹) x *
          -(x ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := (hpos x hx).ne'
    simp only [Function.comp_apply]
    field_simp
  rw [hL, h, OriginDatum.slowLog, intervalIntegral.integral_symm, neg_neg]

/-- **The comparison of two divergent integrals**: if `h > 0` on `[a,∞)`, `f/h → 1` at infinity
and `∫_a^R h → ∞`, then `∫_a^R f / ∫_a^R h → 1`. Mathlib types only. -/
theorem tendsto_integral_div_integral {f h : ℝ → ℝ} {a : ℝ}
    (hf : ∀ R, a ≤ R → IntervalIntegrable f volume a R)
    (hh : ∀ R, a ≤ R → IntervalIntegrable h volume a R) (hpos : ∀ ρ, a ≤ ρ → 0 < h ρ)
    (hlim : Tendsto (fun ρ => f ρ / h ρ) atTop (𝓝 1))
    (hH : Tendsto (fun R => ∫ ρ in a..R, h ρ) atTop atTop) :
    Tendsto (fun R => (∫ ρ in a..R, f ρ) / ∫ ρ in a..R, h ρ) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) (ε / 2) hδ)
  set R₀ := max R₁ a with hR₀
  have haR₀ : a ≤ R₀ := le_max_right _ _
  have hclose : ∀ ρ, R₀ ≤ ρ → |f ρ - h ρ| ≤ ε / 2 * h ρ := by
    intro ρ hρ
    have h1 := hR₁ ρ (le_trans (le_max_left _ _) hρ)
    have hp := hpos ρ (le_trans haR₀ hρ)
    rw [Real.dist_eq] at h1
    have e : f ρ - h ρ = (f ρ / h ρ - 1) * h ρ := by field_simp
    rw [e, abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_right h1.le hp.le
  set C₀ := |∫ ρ in a..R₀, (f ρ - h ρ)| with hC₀
  filter_upwards [eventually_ge_atTop R₀, hH.eventually (eventually_gt_atTop (C₀ / (ε / 2))),
    hH.eventually (eventually_gt_atTop 0)] with R hR hHR hHpos
  have haR : a ≤ R := le_trans haR₀ hR
  have hf0 := hf R₀ haR₀
  have hh0 := hh R₀ haR₀
  have hf1 : IntervalIntegrable f volume R₀ R := hf0.symm.trans (hf R haR)
  have hh1 : IntervalIntegrable h volume R₀ R := hh0.symm.trans (hh R haR)
  have hsplit : (∫ ρ in a..R, f ρ) - ∫ ρ in a..R, h ρ
      = (∫ ρ in a..R₀, (f ρ - h ρ)) + ∫ ρ in R₀..R, (f ρ - h ρ) := by
    rw [intervalIntegral.integral_sub hf0 hh0, intervalIntegral.integral_sub hf1 hh1,
      ← intervalIntegral.integral_add_adjacent_intervals hf0 hf1,
      ← intervalIntegral.integral_add_adjacent_intervals hh0 hh1]
    ring
  have hH0 : 0 ≤ ∫ ρ in a..R₀, h ρ :=
    intervalIntegral.integral_nonneg haR₀ fun ρ hρ => (hpos ρ hρ.1).le
  have htail : |∫ ρ in R₀..R, (f ρ - h ρ)| ≤ ε / 2 * ∫ ρ in a..R, h ρ := by
    calc |∫ ρ in R₀..R, (f ρ - h ρ)| ≤ ∫ ρ in R₀..R, |f ρ - h ρ| :=
          intervalIntegral.abs_integral_le_integral_abs hR
      _ ≤ ∫ ρ in R₀..R, ε / 2 * h ρ :=
          intervalIntegral.integral_mono_on hR (hf1.sub hh1).abs (hh1.const_mul _)
            fun ρ hρ => hclose ρ hρ.1
      _ = ε / 2 * ∫ ρ in R₀..R, h ρ := intervalIntegral.integral_const_mul _ _
      _ ≤ ε / 2 * ∫ ρ in a..R, h ρ := by
          refine mul_le_mul_of_nonneg_left ?_ hδ.le
          rw [← intervalIntegral.integral_add_adjacent_intervals hh0 hh1]
          linarith
  have hC : C₀ < ε / 2 * ∫ ρ in a..R, h ρ := by
    have := (div_lt_iff₀ hδ).1 hHR
    linarith
  have hne := hHpos.ne'
  rw [Real.dist_eq]
  have e : (∫ ρ in a..R, f ρ) / (∫ ρ in a..R, h ρ) - 1
      = ((∫ ρ in a..R, f ρ) - ∫ ρ in a..R, h ρ) / ∫ ρ in a..R, h ρ := by
    field_simp
  rw [e, abs_div, abs_of_pos hHpos, div_lt_iff₀ hHpos, hsplit]
  calc |(∫ ρ in a..R₀, (f ρ - h ρ)) + ∫ ρ in R₀..R, (f ρ - h ρ)|
      ≤ C₀ + |∫ ρ in R₀..R, (f ρ - h ρ)| := abs_add_le _ _
    _ < ε * ∫ ρ in a..R, h ρ := by linarith

/-- **The truncated integral of the transform at the threshold**: for `c = d`,
`∫_{|ξ| ≤ 1/s} μ̂(ξ) dξ / (|S^{d-1}| A 𝓛(s)) → 1` as `s ↓ 0`. Lean core. -/
theorem IsLawOf.tendsto_integral_charFun_div_slowLog (hd : 1 ≤ d) {D : OriginDatum d}
    (ha : D.a = 0) (hcd : D.profileAtOrigin = d) {μ : Measure (Rd d)} (hμ : IsLawOf D μ) :
    Tendsto (fun s : ℝ => (∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re) /
      (sphereArea d * D.profileConst * D.slowLog s)) (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with hedef
  have he : ‖e‖ = 1 := by simp [hedef, ebasis]
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hcd' : D.profileAtOrigin.toReal = d := by rw [hcd]; simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hSA := (sphereArea_eq_toSphere hd).2
  have hA := D.profileConst_pos
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  set f : ℝ → ℝ := fun ρ => φ ρ * ρ ^ ((d : ℝ) - 1) with hf
  set h : ℝ → ℝ := fun ρ => D.profileConst * (D.slowFactor ρ⁻¹ / ρ) with hh
  have hcont := (slowFactor_basic D hctop).2.1
  have hhint : ∀ R, (1 : ℝ) ≤ R → IntervalIntegrable h volume 1 R := by
    intro R hR
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul ?_)
    have hpos : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := fun x hx => by
      rw [uIcc_of_le hR] at hx; exact lt_of_lt_of_le one_pos hx.1
    refine ContinuousOn.div ?_ continuousOn_id fun x hx => (hpos x hx).ne'
    refine hcont.comp (continuousOn_inv₀.mono fun x hx => (hpos x hx).ne') fun x hx => ?_
    have h0 := hpos x hx
    rw [uIcc_of_le hR] at hx
    exact ⟨inv_pos.2 h0, inv_le_one_of_one_le₀ hx.1⟩
  have hHeq : ∀ R, (1 : ℝ) ≤ R → ∫ ρ in (1 : ℝ)..R, h ρ = D.profileConst * D.slowLog R⁻¹ := by
    intro R hR
    simp only [hh]
    rw [intervalIntegral.integral_const_mul, integral_slowFactor_inv D hctop hR]
  have hHtop : Tendsto (fun R => ∫ ρ in (1 : ℝ)..R, h ρ) atTop atTop := by
    have h1 : Tendsto (fun R : ℝ => D.profileConst * Real.log R) atTop atTop :=
      Real.tendsto_log_atTop.const_mul_atTop hA
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop 1] with R hR
    rw [hHeq R hR]
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have hb := (slowLog_bounds D hctop (s := R⁻¹) ⟨inv_pos.2 hR0, inv_le_one_of_one_le₀ hR⟩).1
    rw [one_div, inv_inv] at hb
    exact mul_le_mul_of_nonneg_left hb hA.le
  have hratio : Tendsto (fun ρ => f ρ / h ρ) atTop (𝓝 1) := by
    have h1 := (exponent_profile_asymptotic hd D ha hctop he).2
    have hfold : Real.exp (-D.tailConst - D.profileAtOrigin.toReal * exponentConst d)
        = D.profileConst := rfl
    rw [hfold, hcd'] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    simp only [hf, hh, hφ]
    rw [hμ.charFun_re, Real.rpow_sub_one hρ.ne', Real.rpow_neg hρ.le]
    have hK := D.slowFactor_pos ρ⁻¹
    have hp : 0 < ρ ^ (d : ℝ) := Real.rpow_pos_of_pos hρ _
    field_simp
  have hmain := tendsto_integral_div_integral
    (fun R _ => hray.intervalIntegrable_mul_rpow hd0 1 R) hhint
    (fun ρ hρ => mul_pos hA (div_pos (D.slowFactor_pos _) (lt_of_lt_of_le one_pos hρ)))
    hratio hHtop
  -- add the piece on `[0,1]`, which is bounded
  have hP : Tendsto (fun R => truncMoment φ d R / ∫ ρ in (1 : ℝ)..R, h ρ) atTop (𝓝 1) := by
    have h0 : Tendsto (fun R => truncMoment φ d 1 / ∫ ρ in (1 : ℝ)..R, h ρ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hHtop
    have h2 := h0.add hmain
    rw [zero_add] at h2
    refine h2.congr fun R => ?_
    rw [← add_div]
    congr 1
    rw [truncMoment, truncMoment]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hray.intervalIntegrable_mul_rpow hd0 0 1) (hray.intervalIntegrable_mul_rpow hd0 1 R)
  have hcomp := hP.comp tendsto_inv_nhdsGT_zero
  refine hcomp.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
  simp only [Function.comp_apply]
  have hR : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs.1).2 hs.2
  rw [hHeq s⁻¹ hR, inv_inv, one_div,
    hμ.integral_charFun_closedBall hd ha he (inv_nonneg.2 hs.1.le)]
  rw [mul_assoc, mul_div_mul_left _ _ hSA.ne']

/-- **`prop:origin-rate-profile-d`(3), the density**: for a datum with Gaussian coefficient `0`
and `c = d`, every law `μ` of it and every `q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx`:
`q(s) / (B 𝓛(s)) → 1` as `s ↓ 0`, `B = (2π)^{-d} |S^{d-1}| A`. Spends A11. -/
theorem origin_density_rate_profile_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioi 0)) (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s /
      ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowLog s)) (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hSA := (sphereArea_eq_toSphere hd).2
  have hray : IsRayProfile (fun ρ : ℝ => (charFun μ (ρ • (ebasis (0 : Fin d) : Rd d))).re) :=
    hμ.isRayProfile hd ha _
  have h := (origin_density_rate_critical hd D ha hcd μ hμ hq hμq).mul
    (hμ.tendsto_integral_charFun_div_slowLog hd ha hcd)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hI : 0 < ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re := by
    rw [hμ.integral_charFun_closedBall hd ha he (by positivity)]
    exact mul_pos hSA (hray.truncMoment_pos hd0 (by positivity))
  set I := ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re with hIdef
  set p := (2 * π) ^ (-(d : ℝ)) with hp
  rw [div_mul_div_comm]
  have e1 : q s * I = I * q s := mul_comm _ _
  have e2 : p * I * (sphereArea d * D.profileConst * D.slowLog s)
      = I * (p * sphereArea d * D.profileConst * D.slowLog s) := by ring
  rw [e1, e2, mul_div_mul_left _ _ hI.ne']

/-- **`prop:origin-rate-profile-d`(3), the mass of a ball**: for a datum with Gaussian
coefficient `0` and `c = d`, and every law `μ` of it:
`μ{|x| ≤ s} / (B V_d s^d 𝓛(s)) → 1` as `s ↓ 0`, `B = (2π)^{-d} |S^{d-1}| A`. Spends A11. -/
theorem origin_ball_rate_profile_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
      ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst *
        (volume (ball (0 : Rd d) 1)).toReal * s ^ d * D.slowLog s)) (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hSA := (sphereArea_eq_toSphere hd).2
  have hray : IsRayProfile (fun ρ : ℝ => (charFun μ (ρ • (ebasis (0 : Fin d) : Rd d))).re) :=
    hμ.isRayProfile hd ha _
  have h := (origin_ball_rate_critical hd D ha hcd μ hμ).mul
    (hμ.tendsto_integral_charFun_div_slowLog hd ha hcd)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hI : 0 < ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re := by
    rw [hμ.integral_charFun_closedBall hd ha he (by positivity)]
    exact mul_pos hSA (hray.truncMoment_pos hd0 (by positivity))
  set I := ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re with hIdef
  set m := (μ (closedBall 0 s)).toReal with hm
  set V := (volume (ball (0 : Rd d) 1)).toReal with hV
  set p := (2 * π) ^ (-(d : ℝ)) with hp
  rw [div_mul_div_comm]
  have e1 : m * I = I * m := mul_comm _ _
  have e2 : p * V * s ^ d * I * (sphereArea d * D.profileConst * D.slowLog s)
      = I * (p * sphereArea d * D.profileConst * V * s ^ d * D.slowLog s) := by ring
  rw [e1, e2, mul_div_mul_left _ _ hI.ne']

/-- **`prop:origin-rate-profile-d`(3), the convergent case**: for `c = d`, if `(d - k_d(u))/u`
is integrable on `(0,1]`, then `q(s)/log(1/s) → B K(0+)`, a positive number. Spends A11. -/
theorem origin_density_log_of_integrable (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioi 0)) (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    (hI : IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0)
        (𝓝 ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowFactorZero)) ∧
      0 < (2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowFactorZero := by
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hSA := (sphereArea_eq_toSphere hd).2
  have hp : 0 < (2 * π) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  set B := (2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst with hB
  have hBpos : 0 < B := mul_pos (mul_pos hp hSA) D.profileConst_pos
  have hK1 := (slowFactor_tendsto_of_integrable D hctop hI).2.1
  refine ⟨?_, mul_pos hBpos (lt_of_lt_of_le one_pos hK1)⟩
  have h1 := origin_density_rate_profile_critical hd D ha hcd μ hμ hq hμq
  simp only [← hB] at h1
  have h2 := ((slowLog_div_log D hctop).1 hI).const_mul B
  have h := h1.mul h2
  rw [one_mul] at h
  refine h.congr' ?_
  have hlogpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / s) :=
    tendsto_log_one_div_nhdsGT_zero.eventually (eventually_gt_atTop 0)
  filter_upwards [hlogpos, Ioo_mem_nhdsGT one_pos] with s hlog hs
  have hL : 0 < D.slowLog s :=
    lt_of_lt_of_le hlog (slowLog_bounds D hctop ⟨hs.1, hs.2.le⟩).1
  field_simp

/-- **`prop:origin-rate-profile-d`(3), the divergent case**: for `c = d`, if `(d - k_d(u))/u` is
not integrable on `(0,1]`, then `q(s)/log(1/s) → ∞`. Spends A11. -/
theorem origin_density_log_of_not_integrable (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioi 0)) (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    (hI : ¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1)) :
    Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0) atTop := by
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hSA := (sphereArea_eq_toSphere hd).2
  have hp : 0 < (2 * π) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  set B := (2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst with hB
  have hBpos : 0 < B := mul_pos (mul_pos hp hSA) D.profileConst_pos
  have h1 := origin_density_rate_profile_critical hd D ha hcd μ hμ hq hμq
  simp only [← hB] at h1
  have h2 := ((slowLog_div_log D hctop).2 hI).const_mul_atTop hBpos
  have h := h1.pos_mul_atTop one_pos h2
  refine h.congr' ?_
  have hlogpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / s) :=
    tendsto_log_one_div_nhdsGT_zero.eventually (eventually_gt_atTop 0)
  filter_upwards [hlogpos, Ioo_mem_nhdsGT one_pos] with s hlog hs
  have hL : 0 < D.slowLog s :=
    lt_of_lt_of_le hlog (slowLog_bounds D hctop ⟨hs.1, hs.2.le⟩).1
  field_simp

/-! ## The bundles -/

/-- **`prop:origin-rate-profile-d`(1)–(2)**, in one statement: the law of a datum with Gaussian
coefficient `0` and `0 < c < d` has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`
(`radial_monotone_law`), and for it, as `s ↓ 0`: `q(s) ∼ Q s^{c-d} K(s)` and
`μ{|x| ≤ s} ∼ Q |S^{d-1}| c⁻¹ s^c K(s)`, `Q = R(d,c) A`; if `(c - k_d(u))/u` is integrable on
`(0,1]`, `q(s) s^{d-c} → Q K(0+) > 0` and `q(s) ≤ C s^{c-d}` at every `s > 0` for some `C`; if it
is not, `q(s) s^{d-c} → ∞` and there is no such `C`. Spends A11, and A8, A2 and A3(iii) for the
existence of `q`. -/
theorem origin_rate_profile (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s / (rateConst d D.profileAtOrigin.toReal * D.profileConst *
        s ^ (D.profileAtOrigin.toReal - d) * D.slowFactor s)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        (rateConst d D.profileAtOrigin.toReal * D.profileConst * sphereArea d /
          D.profileAtOrigin.toReal * s ^ D.profileAtOrigin.toReal * D.slowFactor s))
        (𝓝[>] 0) (𝓝 1) ∧
      (IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - D.profileAtOrigin.toReal)) (𝓝[>] 0)
            (𝓝 (rateConst d D.profileAtOrigin.toReal * D.profileConst * D.slowFactorZero)) ∧
          0 < rateConst d D.profileAtOrigin.toReal * D.profileConst * D.slowFactorZero ∧
          ∃ C : ℝ, ∀ s : ℝ, 0 < s → q s ≤ C * s ^ (D.profileAtOrigin.toReal - d)) ∧
      (¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - D.profileAtOrigin.toReal)) (𝓝[>] 0) atTop ∧
          ¬ ∃ C : ℝ, ∀ s : ℝ, 0 < s → q s ≤ C * s ^ (D.profileAtOrigin.toReal - d)) := by
  obtain ⟨q, hq0, hq, hμq⟩ :=
    radial_monotone_law hd D (Or.inr (D.not_ae_zero_of_profileAtOrigin_pos hc)) μ hμ
  exact ⟨q, hq0, hq, hμq, origin_density_rate_profile hd D ha hc hcd μ hμ hq hμq,
    origin_ball_rate_profile hd D ha hc hcd μ hμ,
    fun hI => origin_density_power_of_integrable hd D ha hc hcd μ hμ hq hμq hI,
    fun hI => origin_density_power_of_not_integrable hd D ha hc hcd μ hμ hq hμq hI⟩

/-- **`prop:origin-rate-profile-d`(3)**, in one statement: the law of a datum with Gaussian
coefficient `0` and `c = d` has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`, and
for it, as `s ↓ 0`: `q(s) ∼ B 𝓛(s)` and `μ{|x| ≤ s} ∼ B V_d s^d 𝓛(s)`,
`B = (2π)^{-d} |S^{d-1}| A`; `log(1/s) ≤ 𝓛(s) ≤ K(s) log(1/s)` on `(0,1]`; if `(d - k_d(u))/u` is
integrable on `(0,1]`, `𝓛(s)/log(1/s) → K(0+)` and `q(s)/log(1/s) → B K(0+) > 0`; if it is not,
both quotients tend to `∞`. Spends A11, and A8, A2 and A3(iii) for the existence of `q`. -/
theorem origin_rate_profile_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s /
        ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowLog s)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst *
          (volume (ball (0 : Rd d) 1)).toReal * s ^ d * D.slowLog s)) (𝓝[>] 0) (𝓝 1) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, Real.log (1 / s) ≤ D.slowLog s ∧
        D.slowLog s ≤ D.slowFactor s * Real.log (1 / s)) ∧
      (IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => D.slowLog s / Real.log (1 / s)) (𝓝[>] 0) (𝓝 D.slowFactorZero) ∧
          Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0)
            (𝓝 ((2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowFactorZero)) ∧
          0 < (2 * π) ^ (-(d : ℝ)) * sphereArea d * D.profileConst * D.slowFactorZero) ∧
      (¬ IntegrableOn (fun u => (D.profileAtOrigin.toReal - D.k u) / u) (Ioc 0 1) →
        Tendsto (fun s : ℝ => D.slowLog s / Real.log (1 / s)) (𝓝[>] 0) atTop ∧
          Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0) atTop) := by
  have hc : 0 < D.profileAtOrigin := by
    rw [hcd]
    exact_mod_cast hd
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  obtain ⟨q, hq0, hq, hμq⟩ :=
    radial_monotone_law hd D (Or.inr (D.not_ae_zero_of_profileAtOrigin_pos hc)) μ hμ
  refine ⟨q, hq0, hq, hμq, origin_density_rate_profile_critical hd D ha hcd μ hμ hq hμq,
    origin_ball_rate_profile_critical hd D ha hcd μ hμ, fun s hs => slowLog_bounds D hctop hs,
    fun hI => ?_, fun hI => ?_⟩
  · obtain ⟨h1, h2⟩ := origin_density_log_of_integrable hd D ha hcd μ hμ hq hμq hI
    exact ⟨(slowLog_div_log D hctop).1 hI, h1, h2⟩
  · exact ⟨(slowLog_div_log D hctop).2 hI,
      origin_density_log_of_not_integrable hd D ha hcd μ hμ hq hμq hI⟩

end AffineHemigroup
