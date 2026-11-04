/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginUpperBound
import AffineHemigroup.ExponentLog
import AffineHemigroup.RegularVariation
import AffineHemigroup.Interfaces

/-!
# `prop:origin-rate-d`: the rate of the mass of a small ball and of the density at the origin

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:origin-rate-d` (Q-0416).

For an isotropic origin datum `(0, k_d)` in dimension `d ≥ 1` with profile at the origin
`0 < c ≤ d`, a law `μ` of it, a unit vector `e` and every `q` nonincreasing on `(0,∞)` with
`μ = q(|x|) dx`, as `s ↓ 0`:

* `origin_ball_rate`, `origin_density_rate` (clause (1), `c < d`):
  `μ{|x| ≤ s} / (R(d,c) |S^{d-1}| c⁻¹ μ̂(e/s)) → 1` and `q(s) / (R(d,c) s^{-d} μ̂(e/s)) → 1`, with
  `R(d,c) = Γ((d-c)/2)/(2^c π^{d/2} Γ(c/2))` (`rateConst`);
* `origin_ball_rate_critical`, `origin_density_rate_critical` (clause (2), `c = d`):
  `μ{|x| ≤ s} / ((2π)^{-d} V_d s^d I(s)) → 1` and `q(s) / ((2π)^{-d} I(s)) → 1`, with
  `I(s) = ∫_{|ξ| ≤ 1/s} μ̂(ξ) dξ`;
* `origin_transform_ball_log`, `origin_density_log_lower` (clause (2)):
  `I(s) ≥ |S^{d-1}| e^{-13d/4 - 2C_k} log(1/s)` for `0 < s ≤ 1`, and `q(s) ≥ C log(1/s)` for small
  `s`, for every `C < (2π)^{-d} |S^{d-1}| e^{-13d/4 - 2C_k}`;
* `origin_rate`, `origin_rate_critical`: the bundles, with the existence of `q`
  (`radial_monotone_law`).

**What is spent.** One cited fact of its own, ledger A11 (`karamata_tauberian_zero`, Karamata's
Tauberian theorem at the origin), through `tendsto_ball_of_gauss`: the limits print A11 and no
other entry, the law and the density being hypotheses. `origin_transform_ball_log` and every
helper before `tendsto_ball_of_gauss` are Lean core. The two bundles add A8, A2 and A3(iii),
through `radial_monotone_law`.

**The route** (the blueprint's proof, step by step). Write `φ(ρ) = μ̂(ρe)`.

* The transform along a ray is a ray profile (`IsLawOf.isRayProfile`): positive, at most `1`,
  and nonincreasing, because `F_d(ξ) ≤ F_d(bξ)` for `b ≥ 1` (`OriginDatum.exponent_le_smul`, from
  the dilation formula of `lem:isotropic-exponent-log`'s proof). It varies regularly:
  `φ(aR)/φ(R) → a^{-c}` (`IsLawOf.tendsto_ray_ratio`, which is `lem:isotropic-exponent-log`(2)).
* **Step 2** (`IsLawOf.integral_gauss_eq`):
  `∫ e^{-R²|x|²} μ(dx) = (4π)^{-d/2} |S^{d-1}| R^{-d} T(R)`, from
  `lem:positive-transform-origin`(1) at `t = 1/(2R²)` and polar coordinates, `T` the Gaussian
  moment of `AffineHemigroup.RegularVariation`.
* **Steps 1, 3, 3′** are that module's: the Abelian limits `T(R)/(R^d φ(R)) → ∫ u^{d-1-c} e^{-u²/4}`
  for `c < d` and `T(R)/P(R) → 1` for `c = d`, `P` the truncated moment.
* **Step 4** (`tendsto_ball_of_gauss`, ledger A11): Karamata's theorem for the image of `μ` under
  `x ↦ |x|²`, whose Laplace transform is the Gaussian average, gives the mass of small balls.
* **Step 5** (`tendsto_radial_density_of_ball`): if `μ{|x| ≤ s}/W(s) → B` with `W` regularly
  varying at `0` of index `κ > 0`, then `q(s) s^d/W(s) → Bκ/|S^{d-1}|`. It is the argument of the
  monotone density theorem on the shells `{as < |x| ≤ bs}` (`radial_density_shell`), with the
  slopes of `t ↦ t^κ` and `t ↦ t^d` at `1` (`tendsto_rpow_sub_one_div_pow_sub_one`).
* The constants: `rateConst_div` and `critConst_eq`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Real RealInnerProductSpace

variable {d : ℕ}

/-- `|S^{d-1}| = d V_d`, `V_d` the volume of the unit ball. -/
theorem sphereArea_eq_mul_volume_unitBall (hd : 1 ≤ d) :
    sphereArea d = d * (volume (ball (0 : Rd d) 1)).toReal := by
  have h := (sphereArea_eq_toSphere hd).1
  have hpos := (sphereArea_eq_toSphere hd).2
  rw [Measure.toSphere_apply_univ, finrank_Rd] at h
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_mul, ENNReal.toReal_natCast] at h'

/-- **The mass of a spherical shell against a nonincreasing radial density** (the inequality
(1.7.5) of the monotone density theorem, on shells): for `μ = q(|x|) dx`, `q` nonincreasing on
`(0,∞)`, and `0 < r₁ ≤ r₂`, the mass of `{r₁ < |x| ≤ r₂}` lies between `max(q(r₂),0)` and
`max(q(r₁),0)` times its volume `V_d (r₂^d - r₁^d)`. -/
theorem radial_density_shell {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hr : r₁ ≤ r₂) :
    max (q r₂) 0 * ((volume (ball (0 : Rd d) 1)).toReal * (r₂ ^ d - r₁ ^ d))
        ≤ (μ (closedBall 0 r₂)).toReal - (μ (closedBall 0 r₁)).toReal ∧
      (μ (closedBall 0 r₂)).toReal - (μ (closedBall 0 r₁)).toReal
        ≤ max (q r₁) 0 * ((volume (ball (0 : Rd d) 1)).toReal * (r₂ ^ d - r₁ ^ d)) := by
  set S := closedBall (0 : Rd d) r₂ \ closedBall 0 r₁ with hS
  have hSm : MeasurableSet S := measurableSet_closedBall.diff measurableSet_closedBall
  have hsub : closedBall (0 : Rd d) r₁ ⊆ closedBall 0 r₂ := closedBall_subset_closedBall hr
  have hμS : (μ S).toReal = (μ (closedBall 0 r₂)).toReal - (μ (closedBall 0 r₁)).toReal := by
    rw [hS, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet (measure_ne_top μ _),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top μ _)]
  have hvfin : ∀ r : ℝ, volume (closedBall (0 : Rd d) r) ≠ ⊤ := fun r =>
    measure_closedBall_lt_top.ne
  have hvS : (volume S).toReal = (volume (ball (0 : Rd d) 1)).toReal * (r₂ ^ d - r₁ ^ d) := by
    rw [hS, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet (hvfin _),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (hvfin _),
      Measure.addHaar_closedBall volume (0 : Rd d) (hr₁.le.trans hr),
      Measure.addHaar_closedBall volume (0 : Rd d) hr₁.le, finrank_Rd,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (hr₁.le.trans hr) d),
      ENNReal.toReal_ofReal (pow_nonneg hr₁.le d)]
    ring
  have hmem : ∀ x ∈ S, r₁ < ‖x‖ ∧ ‖x‖ ≤ r₂ := fun x hx => by
    simp only [hS, Set.mem_sdiff, mem_closedBall_zero_iff, not_le] at hx
    exact ⟨hx.2, hx.1⟩
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top (hvfin r₂) (measure_mono sdiff_subset)
  have hμSeq : μ S = ∫⁻ x in S, ENNReal.ofReal (q ‖x‖) := by
    conv_lhs => rw [hμ]
    rw [withDensity_apply _ hSm]
  constructor
  · rw [← hμS, ← hvS]
    have h1 : ENNReal.ofReal (q r₂) * volume S ≤ μ S := by
      rw [hμSeq, ← setLIntegral_const]
      exact setLIntegral_mono' hSm fun x hx => ENNReal.ofReal_le_ofReal
        (hq (mem_Ioi.mpr (hr₁.trans (hmem x hx).1)) (mem_Ioi.mpr (hr₁.trans_le hr)) (hmem x hx).2)
    have h2 := ENNReal.toReal_mono (measure_ne_top μ S) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at h2
  · rw [← hμS, ← hvS]
    have h1 : μ S ≤ ENNReal.ofReal (q r₁) * volume S := by
      rw [hμSeq, ← setLIntegral_const]
      exact setLIntegral_mono' hSm fun x hx => ENNReal.ofReal_le_ofReal
        (hq (mem_Ioi.mpr hr₁) (mem_Ioi.mpr (hr₁.trans (hmem x hx).1)) (hmem x hx).1.le)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at h2

/-- `(t^κ - 1)/(t^d - 1) → κ/d` as `t → 1`. -/
theorem tendsto_rpow_sub_one_div_pow_sub_one (hd : 1 ≤ d) (κ : ℝ) :
    Tendsto (fun t : ℝ => (t ^ κ - 1) / (t ^ d - 1)) (𝓝[≠] 1) (𝓝 (κ / d)) := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ κ) (κ * (1 : ℝ) ^ (κ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun t : ℝ => t ^ d) ((d : ℝ) * (1 : ℝ) ^ (d - 1)) 1 := hasDerivAt_pow d 1
  have s1 := h1.tendsto_slope
  have s2 := h2.tendsto_slope
  simp only [Real.one_rpow, mul_one, one_pow] at s1 s2
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  refine (s1.div s2 hd0).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  simp only [Pi.div_apply, slope_def_field, Real.one_rpow, one_pow]
  field_simp

/-- Multiplication by `a > 0` maps the positive reals near `0` into themselves. -/
theorem tendsto_const_mul_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ => a * s) (𝓝[>] 0) (𝓝[>] 0) := by
  have h1 : Tendsto (fun s : ℝ => a * s) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_const_mul a).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
    (eventually_mem_nhdsWithin.mono fun s hs => mul_pos ha hs)

/-- **From the mass of balls to a nonincreasing radial density** (Step 5 of `prop:origin-rate-d`;
the argument of the monotone density theorem, Bingham–Goldie–Teugels Thm. 1.7.2b, on spherical
shells): let `μ = q(|x|) dx` be a finite measure on `ℝ^d` with `q` nonincreasing on `(0,∞)`, let
`W > 0` on `(0,∞)` with `W(as)/W(s) → a^κ` as `s ↓ 0` for every `a > 0`, `κ > 0`, and suppose
`μ{|x| ≤ s}/W(s) → B > 0`. Then `q(s) s^d/W(s) → Bκ/|S^{d-1}|`. Mathlib types and `sphereArea`. -/
theorem tendsto_radial_density_of_ball (hd : 1 ≤ d) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    {W : ℝ → ℝ} {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hWpos : ∀ s : ℝ, 0 < s → 0 < W s)
    (hW : ∀ a : ℝ, 0 < a → Tendsto (fun s => W (a * s) / W s) (𝓝[>] 0) (𝓝 (a ^ κ)))
    (hm : Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal / W s) (𝓝[>] 0) (𝓝 B)) :
    Tendsto (fun s : ℝ => q s * s ^ d / W s) (𝓝[>] 0) (𝓝 (B * κ / sphereArea d)) := by
  set V := (volume (ball (0 : Rd d) 1)).toReal with hV
  have hVpos : 0 < V := volume_unitBall_toReal_pos
  have hSV : sphereArea d = d * V := sphereArea_eq_mul_volume_unitBall hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ → ℝ := fun s => (μ (closedBall 0 s)).toReal with hmdef
  have hma : ∀ a : ℝ, 0 < a → Tendsto (fun s => m (a * s) / W s) (𝓝[>] 0) (𝓝 (B * a ^ κ)) := by
    intro a ha
    have := (hm.comp (tendsto_const_mul_nhdsGT_zero ha)).mul (hW a ha)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs
    simp only [Function.comp_apply]
    rw [div_mul_div_cancel₀ (hWpos _ (mul_pos ha hs0)).ne']
  set K := B * κ / (d * V) with hK
  have hKpos : 0 < K := by positivity
  have hG : Tendsto (fun t : ℝ => B * ((t ^ κ - 1) / (t ^ d - 1)) / V) (𝓝[≠] 1) (𝓝 K) := by
    have := ((tendsto_rpow_sub_one_div_pow_sub_one hd κ).const_mul B).div_const V
    have e : B * (κ / d) / V = K := by rw [hK]; field_simp
    rwa [e] at this
  set f : ℝ → ℝ := fun s => max (q s) 0 * s ^ d / W s with hf
  have hf_lim : Tendsto f (𝓝[>] 0) (𝓝 K) := by
    rw [tendsto_order]
    constructor
    · intro K' hK'
      obtain ⟨b, hbK, hb1⟩ := (((hG.mono_left (nhdsGT_le_nhdsNE 1)).eventually
        (lt_mem_nhds hK')).and self_mem_nhdsWithin).exists
      have hb1' : 1 < b := hb1
      have hb0 : 0 < b := by linarith
      have hbd : 0 < b ^ d - 1 := sub_pos.mpr (one_lt_pow₀ hb1' (by omega))
      have hlim : Tendsto (fun s => (m (b * s) / W s - m s / W s) / (V * (b ^ d - 1))) (𝓝[>] 0)
          (𝓝 ((B * b ^ κ - B) / (V * (b ^ d - 1)))) := ((hma b hb0).sub hm).div_const _
      have hval : (B * b ^ κ - B) / (V * (b ^ d - 1)) = B * ((b ^ κ - 1) / (b ^ d - 1)) / V := by
        have := hbd.ne'
        field_simp
      rw [hval] at hlim
      filter_upwards [hlim.eventually (lt_mem_nhds hbK), self_mem_nhdsWithin] with s hs hs0'
      have hs0 : 0 < s := hs0'
      refine hs.trans_le ?_
      have hsh := (radial_density_shell hq hμ hs0 (le_mul_of_one_le_left hs0.le hb1'.le)).2
      have hW0 := hWpos s hs0
      have key : m (b * s) - m s ≤ max (q s) 0 * s ^ d * (V * (b ^ d - 1)) := by
        calc m (b * s) - m s ≤ max (q s) 0 * (V * ((b * s) ^ d - s ^ d)) := hsh
          _ = max (q s) 0 * s ^ d * (V * (b ^ d - 1)) := by rw [mul_pow]; ring
      have hden : 0 < W s * (V * (b ^ d - 1)) := mul_pos hW0 (mul_pos hVpos hbd)
      rw [← sub_div, div_div]
      calc (m (b * s) - m s) / (W s * (V * (b ^ d - 1)))
          ≤ max (q s) 0 * s ^ d * (V * (b ^ d - 1)) / (W s * (V * (b ^ d - 1))) :=
            div_le_div_of_nonneg_right key hden.le
        _ = f s := by
            have h1 := hW0.ne'
            have h2 := hVpos.ne'
            have h3 := hbd.ne'
            simp only [hf]
            field_simp
    · intro K'' hK''
      obtain ⟨a, ⟨haK, ha1⟩, ha2⟩ := ((((hG.mono_left (nhdsLT_le_nhdsNE 1)).eventually
        (gt_mem_nhds hK'')).and self_mem_nhdsWithin).and
          (Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1))).exists
      have ha1' : a < 1 := ha1
      have ha0 : 0 < a := by linarith [ha2.1]
      have had : 0 < 1 - a ^ d := sub_pos.mpr (pow_lt_one₀ ha0.le ha1' (by omega))
      have hlim : Tendsto (fun s => (m s / W s - m (a * s) / W s) / (V * (1 - a ^ d))) (𝓝[>] 0)
          (𝓝 ((B - B * a ^ κ) / (V * (1 - a ^ d)))) := (hm.sub (hma a ha0)).div_const _
      have hval : (B - B * a ^ κ) / (V * (1 - a ^ d)) = B * ((a ^ κ - 1) / (a ^ d - 1)) / V := by
        rw [show a ^ κ - 1 = -(1 - a ^ κ) by ring, show a ^ d - 1 = -(1 - a ^ d) by ring,
          neg_div_neg_eq]
        have := had.ne'
        field_simp
      rw [hval] at hlim
      filter_upwards [hlim.eventually (gt_mem_nhds haK), self_mem_nhdsWithin] with s hs hs0'
      have hs0 : 0 < s := hs0'
      refine lt_of_le_of_lt ?_ hs
      have hsh := (radial_density_shell hq hμ (mul_pos ha0 hs0)
        (mul_le_of_le_one_left hs0.le ha1'.le)).1
      have hW0 := hWpos s hs0
      have key : max (q s) 0 * s ^ d * (V * (1 - a ^ d)) ≤ m s - m (a * s) := by
        calc max (q s) 0 * s ^ d * (V * (1 - a ^ d))
            = max (q s) 0 * (V * (s ^ d - (a * s) ^ d)) := by rw [mul_pow]; ring
          _ ≤ m s - m (a * s) := hsh
      have hden : 0 < W s * (V * (1 - a ^ d)) := mul_pos hW0 (mul_pos hVpos had)
      rw [← sub_div, div_div]
      calc f s = max (q s) 0 * s ^ d * (V * (1 - a ^ d)) / (W s * (V * (1 - a ^ d))) := by
            have h1 := hW0.ne'
            have h2 := hVpos.ne'
            have h3 := had.ne'
            simp only [hf]
            field_simp
        _ ≤ (m s - m (a * s)) / (W s * (V * (1 - a ^ d))) :=
            div_le_div_of_nonneg_right key hden.le
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < f s := hf_lim.eventually (lt_mem_nhds hKpos)
  have hK' : B * κ / sphereArea d = K := by rw [hK, hSV]
  rw [hK']
  refine hf_lim.congr' ?_
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs hs0'
  have hs0 : 0 < s := hs0'
  have hW0 := hWpos s hs0
  have hq0 : 0 < q s := by
    by_contra hneg
    rw [not_lt] at hneg
    simp only [hf, max_eq_right hneg, zero_mul, zero_div, lt_self_iff_false] at hs
  simp only [hf, max_eq_left hq0.le]


/-! ## The rate constant -/

/-- **`R(d,c) = Γ((d-c)/2) / (2^c π^{d/2} Γ(c/2))`** (`prop:origin-rate-d`), the constant of the
Riesz kernel. -/
noncomputable def rateConst (d : ℕ) (c : ℝ) : ℝ :=
  Real.Gamma (((d : ℝ) - c) / 2) / (2 ^ c * π ^ ((d : ℝ) / 2) * Real.Gamma (c / 2))

/-- `R(d,c) > 0` for `0 < c < d`. -/
theorem rateConst_pos {c : ℝ} (hc : 0 < c) (hcd : c < d) : 0 < rateConst d c := by
  unfold rateConst
  have h1 : 0 < Real.Gamma (((d : ℝ) - c) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (c / 2) := Real.Gamma_pos_of_pos (by linarith)
  positivity

/-- `(4π)^{-x/2} = 2^{-x} π^{-x/2}`. -/
theorem four_pi_rpow (x : ℝ) : (4 * π) ^ (-x / 2) = 2 ^ (-x) * π ^ (-x / 2) := by
  rw [Real.mul_rpow (by norm_num) Real.pi_pos.le,
    show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

/-- The Gaussian moment `∫_0^∞ u^{d-1-c} e^{-u²/4} du = 2^{d-c-1} Γ((d-c)/2)`. -/
theorem integral_rpow_mul_exp_quarter {c : ℝ} (hcd : c < d) :
    ∫ u in Ioi (0 : ℝ), u ^ ((d : ℝ) - 1 - c) * Real.exp (-(1 / 4) * u ^ 2)
      = 2 ^ ((d : ℝ) - c) * (1 / 2) * Real.Gamma (((d : ℝ) - c) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (d : ℝ) - 1 - c) (b := 1 / 4)
    two_pos (by linarith) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h, show ((d : ℝ) - 1 - c + 1) = (d : ℝ) - c by ring]
  have e : (1 / 4 : ℝ) ^ (-((d : ℝ) - c) / 2) = 2 ^ ((d : ℝ) - c) := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℝ))⁻¹ by rw [Real.rpow_two]; norm_num,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [e]

/-- The constant of the mass of a ball: `(4π)^{-d/2} J / Γ(1 + c/2) = R(d,c)/c`. -/
theorem rateConst_div {c : ℝ} (hc : 0 < c) (hcd : c < d) :
    (4 * π) ^ (-(d : ℝ) / 2) *
        (∫ u in Ioi (0 : ℝ), u ^ ((d : ℝ) - 1 - c) * Real.exp (-(1 / 4) * u ^ 2)) /
      Real.Gamma (1 + c / 2) = rateConst d c / c := by
  have hΓ : Real.Gamma (1 + c / 2) = c / 2 * Real.Gamma (c / 2) := by
    rw [add_comm]; exact Real.Gamma_add_one (by positivity)
  have hΓc : 0 < Real.Gamma (c / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (2 : ℝ) ^ (-(d : ℝ)) * 2 ^ ((d : ℝ) - c) = (2 ^ c)⁻¹ := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  have hπ : π ^ (-(d : ℝ) / 2) = (π ^ ((d : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg Real.pi_pos.le]
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have hπd : (0 : ℝ) < π ^ ((d : ℝ) / 2) := by positivity
  rw [integral_rpow_mul_exp_quarter hcd, four_pi_rpow, hΓ, rateConst, hπ]
  calc (2 : ℝ) ^ (-(d : ℝ)) * (π ^ ((d : ℝ) / 2))⁻¹ *
        (2 ^ ((d : ℝ) - c) * (1 / 2) * Real.Gamma (((d : ℝ) - c) / 2)) /
        (c / 2 * Real.Gamma (c / 2))
      = (2 : ℝ) ^ (-(d : ℝ)) * 2 ^ ((d : ℝ) - c) * ((π ^ ((d : ℝ) / 2))⁻¹ *
          ((1 / 2) * Real.Gamma (((d : ℝ) - c) / 2)) / (c / 2 * Real.Gamma (c / 2))) := by ring
    _ = Real.Gamma (((d : ℝ) - c) / 2) / (2 ^ c * π ^ ((d : ℝ) / 2) * Real.Gamma (c / 2)) / c := by
        rw [h2]
        field_simp

/-- `(4π)^{-d/2} / Γ(1 + d/2) = (2π)^{-d} |S^{d-1}| / d`. -/
theorem critConst_eq (hd : 1 ≤ d) :
    (4 * π) ^ (-(d : ℝ) / 2) / Real.Gamma (1 + (d : ℝ) / 2)
      = (2 * π) ^ (-(d : ℝ)) * (sphereArea d / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hΓ : Real.Gamma (1 + (d : ℝ) / 2) = (d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2) := by
    rw [add_comm]; exact Real.Gamma_add_one (by positivity)
  have hΓd : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h1 : (2 * π) ^ (-(d : ℝ)) = 2 ^ (-(d : ℝ)) * π ^ (-(d : ℝ)) :=
    Real.mul_rpow (by norm_num) Real.pi_pos.le
  have h2 : π ^ (-(d : ℝ)) * π ^ ((d : ℝ) / 2) = π ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  rw [four_pi_rpow, hΓ, h1, sphereArea, ← h2]
  field_simp

/-! ## The transform along a ray -/

/-- The cosine profile is nondecreasing under dilation: `φ(s) ≤ φ(bs)` for `b ≥ 1`, because
`φ(bs) = ∫ (1 - cos(us)) k_d(u/b) du/u` and `k_d(u/b) ≥ k_d(u)`. -/
theorem OriginDatum.cosProfileL_le_dilate (D : OriginDatum d) {b : ℝ} (hb : 1 ≤ b) (s : ℝ) :
    cosProfileL D.k s ≤ cosProfileL D.k (b * s) := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  rw [D.cosProfileL_dilate hb0 s, cosProfileL]
  refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  gcongr
  exact D.k_antitone (div_pos hu0 hb0) hu0 (div_le_self hu0.le hb)

/-- **The exponent is nondecreasing along rays**: `F_d(ξ) ≤ F_d(bξ)` for `b ≥ 1`. -/
theorem OriginDatum.exponent_le_smul (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) (ξ : Rd d)
    {b : ℝ} (hb : 1 ≤ b) : D.exponent ξ ≤ D.exponent (b • ξ) := by
  refine ENNReal.toReal_mono (D.exponentL_ne_top hd _) ?_
  rw [D.exponentL_eq_sphere hd, D.exponentL_eq_sphere hd, ha]
  simp only [zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  gcongr with η
  rw [real_inner_smul_left]
  exact D.cosProfileL_le_dilate hb _

/-- **The transform of a law of the datum along a ray is a ray profile.** -/
theorem IsLawOf.isRayProfile (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0) {μ : Measure (Rd d)}
    (hμ : IsLawOf D μ) (e : Rd d) : IsRayProfile (fun ρ : ℝ => (charFun μ (ρ • e)).re) := by
  haveI := hμ.1
  refine ⟨?_, fun x => ?_, fun x => ?_, fun x hx y _ hxy => ?_⟩
  · exact (Complex.continuous_re.comp (continuous_charFun.comp (by fun_prop))).measurable
  · rw [hμ.charFun_re]; exact Real.exp_pos _
  · rw [hμ.charFun_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (D.exponent_nonneg _))
  · have hx0 : (0 : ℝ) < x := hx
    change (charFun μ (y • e)).re ≤ (charFun μ (x • e)).re
    rw [hμ.charFun_re, hμ.charFun_re]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have := D.exponent_le_smul hd ha (x • e) ((one_le_div hx0).mpr hxy)
    rwa [smul_smul, div_mul_cancel₀ _ hx0.ne'] at this

/-- **The transform varies regularly along a ray**: `μ̂(aRe)/μ̂(Re) → a^{-c}`. -/
theorem IsLawOf.tendsto_ray_ratio (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {μ : Measure (Rd d)} (hμ : IsLawOf D μ) {e : Rd d}
    (he : ‖e‖ = 1) {a : ℝ} (ha' : 0 < a) :
    Tendsto (fun R : ℝ => (charFun μ ((a * R) • e)).re / (charFun μ (R • e)).re) atTop
      (𝓝 (a ^ (-D.profileAtOrigin.toReal))) := by
  have h := (D.tendsto_exponent_dilate hd ha hc ha' he).neg
  have h2 := (Real.continuous_exp.tendsto _).comp h
  have e1 : Real.exp (-(D.profileAtOrigin.toReal * Real.log a))
      = a ^ (-D.profileAtOrigin.toReal) := by
    rw [Real.rpow_def_of_pos ha']
    congr 1
    ring
  rw [e1] at h2
  refine h2.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [hμ.charFun_re, hμ.charFun_re, ← Real.exp_sub]
  congr 1
  ring

/-! ## The Gaussian average of the law (Step 2) -/

/-- The substitution `ρ = Ru` in the Gaussian moment. -/
theorem gaussMoment_eq (φ : ℝ → ℝ) (n : ℝ) {R : ℝ} (hR : 0 < R) :
    gaussMoment φ n R
      = R ^ n * ∫ u in Ioi (0 : ℝ), φ (R * u) * (u ^ (n - 1) * Real.exp (-(1 / 4) * u ^ 2)) := by
  have h := integral_comp_mul_left_Ioi
    (fun ρ : ℝ => φ ρ * ρ ^ (n - 1) * Real.exp (-(1 / (4 * R ^ 2)) * ρ ^ 2)) 0 hR
  rw [mul_zero, smul_eq_mul] at h
  have h' : gaussMoment φ n R
      = R * ∫ u in Ioi (0 : ℝ), φ (R * u) * (R * u) ^ (n - 1) *
          Real.exp (-(1 / (4 * R ^ 2)) * (R * u) ^ 2) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, gaussMoment]
  rw [h', ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  have e1 : (R * u) ^ (n - 1) = R ^ (n - 1) * u ^ (n - 1) := Real.mul_rpow hR.le hu0.le
  have e2 : -(1 / (4 * R ^ 2)) * (R * u) ^ 2 = -(1 / 4) * u ^ 2 := by
    field_simp
  have e3 : R ^ n = R * R ^ (n - 1) := by
    rw [Real.rpow_sub_one hR.ne']
    field_simp
  rw [e1, e2, e3]
  ring

/-- **Step 2**: `∫ e^{-R²|x|²} μ(dx) = (4π)^{-d/2} |S^{d-1}| R^{-d} T(R)`. -/
theorem IsLawOf.integral_gauss_eq (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0)
    {μ : Measure (Rd d)} (hμ : IsLawOf D μ) {e : Rd d} (he : ‖e‖ = 1) {R : ℝ} (hR : 0 < R) :
    ∫ x, Real.exp (-(R ^ 2 * ‖x‖ ^ 2)) ∂μ =
      (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * R ^ (-(d : ℝ)) *
        gaussMoment (fun ρ : ℝ => (charFun μ (ρ • e)).re) d R := by
  haveI := hμ.1
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hA := (sphereArea_eq_toSphere hd).2
  have ht : (0 : ℝ) < 1 / (2 * R ^ 2) := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hheat : ∀ x : Rd d, Real.exp (-(R ^ 2 * ‖x‖ ^ 2))
      = (π / R ^ 2) ^ ((d : ℝ) / 2) * heatKernel d (1 / (2 * R ^ 2)) x := by
    intro x
    unfold heatKernel
    have e1 : 2 * π * (1 / (2 * R ^ 2)) = π / R ^ 2 := by field_simp
    have e2 : -‖x‖ ^ 2 / (2 * (1 / (2 * R ^ 2))) = -(R ^ 2 * ‖x‖ ^ 2) := by field_simp
    rw [e1, e2, ← mul_assoc, ← Real.rpow_add (by positivity),
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  have hpt : ∀ ξ : Rd d, (charFun μ ξ).re * Real.exp (-(1 / (2 * R ^ 2) * ‖ξ‖ ^ 2) / 2)
      = φ ‖ξ‖ * Real.exp (-(1 / (4 * R ^ 2)) * ‖ξ‖ ^ 2) := by
    intro ξ
    have h1 : (charFun μ ξ).re = φ ‖ξ‖ := by
      simp only [hφ]
      rw [hμ.charFun_re, hμ.charFun_re, D.exponent_eq_of_norm_eq (ξ := ξ) (ξ' := ‖ξ‖ • e)
        (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg _)])]
    rw [h1]
    congr 2
    field_simp
    ring
  have hnn : ∀ r : ℝ, 0 ≤ φ r * Real.exp (-(1 / (4 * R ^ 2)) * r ^ 2) := fun r =>
    mul_nonneg (hray.pos r).le (Real.exp_pos _).le
  have hrad : ∫ ξ : Rd d, (charFun μ ξ).re * Real.exp (-(1 / (2 * R ^ 2) * ‖ξ‖ ^ 2) / 2)
      = sphereArea d * gaussMoment φ d R := by
    simp_rw [hpt]
    set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (φ r * Real.exp (-(1 / (4 * R ^ 2)) * r ^ 2))
      with hg
    have hgm : Measurable g := (hray.measurable.mul (by fun_prop)).ennreal_ofReal
    have hint := hray.integrableOn_gaussMoment hd0 hR
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun ξ => hnn ‖ξ‖)
      (((hray.measurable.comp measurable_norm).mul (by fun_prop)).aestronglyMeasurable)]
    have h1 : ∫⁻ ξ : Rd d, ENNReal.ofReal (φ ‖ξ‖ * Real.exp (-(1 / (4 * R ^ 2)) * ‖ξ‖ ^ 2))
        = ENNReal.ofReal (sphereArea d) * ENNReal.ofReal (gaussMoment φ d R) := by
      rw [show (∫⁻ ξ : Rd d, ENNReal.ofReal (φ ‖ξ‖ * Real.exp (-(1 / (4 * R ^ 2)) * ‖ξ‖ ^ 2)))
          = ∫⁻ ξ : Rd d, g ‖ξ‖ from rfl, lintegral_radial hd g hgm, gaussMoment,
        ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr => by
            have hr0 : (0 : ℝ) < r := hr
            have := hray.pos r
            positivity))]
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      simp only [hg]
      rw [← ENNReal.ofReal_mul (hnn r), pow_pred_eq_rpow hd hr0]
      congr 1
      ring
    rw [h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le, ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioi fun r hr => by
      have hr0 : (0 : ℝ) < r := hr
      have := hray.pos r
      positivity
  have hconst : (π / R ^ 2) ^ ((d : ℝ) / 2) * (2 * π) ^ (-(d : ℝ))
      = (4 * π) ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ)) := by
    have h1 : (π / R ^ 2) ^ ((d : ℝ) / 2) = π ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ)) := by
      rw [Real.div_rpow Real.pi_pos.le (sq_nonneg R), ← Real.rpow_two, ← Real.rpow_mul hR.le,
        Real.rpow_neg hR.le, div_eq_mul_inv]
      congr 3
      ring
    have h2 : (2 * π) ^ (-(d : ℝ)) = 2 ^ (-(d : ℝ)) * π ^ (-(d : ℝ)) :=
      Real.mul_rpow (by norm_num) Real.pi_pos.le
    have h4 : π ^ ((d : ℝ) / 2) * π ^ (-(d : ℝ)) = π ^ (-(d : ℝ) / 2) := by
      rw [← Real.rpow_add Real.pi_pos]
      congr 1
      ring
    rw [h1, h2, four_pi_rpow, ← h4]
    ring
  calc ∫ x, Real.exp (-(R ^ 2 * ‖x‖ ^ 2)) ∂μ
      = (π / R ^ 2) ^ ((d : ℝ) / 2) * ∫ x, heatKernel d (1 / (2 * R ^ 2)) x ∂μ := by
        simp_rw [hheat]
        rw [integral_const_mul]
    _ = (π / R ^ 2) ^ ((d : ℝ) / 2) * ((2 * π) ^ (-(d : ℝ)) *
          (sphereArea d * gaussMoment φ d R)) := by
        rw [integral_heatKernel_eq μ hμ.charFun_im ht, hrad]
    _ = (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * R ^ (-(d : ℝ)) * gaussMoment φ d R := by
        linear_combination (sphereArea d * gaussMoment φ d R) * hconst

/-! ## Step 4: Karamata's theorem for the image of the law under `x ↦ |x|²` -/

/-- **Step 4** (ledger A11): if the Gaussian average `∫ e^{-s|x|²} μ(dx)` of a finite measure on
`ℝ^d` is asymptotic to `c s^{-ρ} ℓ(s)` as `s → ∞`, `ℓ` slowly varying, `c, ρ > 0`, then
`μ{|x| ≤ s} ∼ c s^{2ρ} ℓ(1/s²)/Γ(1+ρ)` as `s ↓ 0`. Karamata's Tauberian theorem for the image of
`μ` under `x ↦ |x|²`. -/
theorem tendsto_ball_of_gauss (μ : Measure (Rd d)) [IsFiniteMeasure μ] (ℓ : ℝ → ℝ)
    (hℓm : Measurable ℓ) (hℓpos : ∀ x : ℝ, 0 < x → 0 < ℓ x)
    (hℓ : ∀ a : ℝ, 0 < a → Tendsto (fun x => ℓ (a * x) / ℓ x) atTop (𝓝 1))
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (h : Tendsto (fun s : ℝ => (∫ x, Real.exp (-(s * ‖x‖ ^ 2)) ∂μ) / (c * s ^ (-ρ) * ℓ s)) atTop
      (𝓝 1)) :
    Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        (c * (s ^ 2) ^ ρ * ℓ (1 / s ^ 2) / Real.Gamma (1 + ρ))) (𝓝[>] 0) (𝓝 1) := by
  have hm : Measurable (fun x : Rd d => ‖x‖ ^ 2) := measurable_norm.pow_const 2
  set ν := μ.map (fun x : Rd d => ‖x‖ ^ 2) with hν
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have h0 : ν (Iio 0) = 0 := by
    rw [hν, Measure.map_apply hm measurableSet_Iio]
    have : (fun x : Rd d => ‖x‖ ^ 2) ⁻¹' Iio 0 = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      positivity
    rw [this, measure_empty]
  have hL : ∀ s : ℝ, ∫ r, Real.exp (-(s * r)) ∂ν = ∫ x, Real.exp (-(s * ‖x‖ ^ 2)) ∂μ := fun s => by
    rw [hν, integral_map hm.aemeasurable
      (by fun_prop : Continuous fun r : ℝ => Real.exp (-(s * r))).aestronglyMeasurable]
  have hK := karamata_tauberian_zero ν h0 ℓ hℓm hℓpos hℓ c ρ hc hρ (by simpa only [hL] using h)
  have hsq : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    have h1 : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
      (eventually_mem_nhdsWithin.mono fun s (hs : 0 < s) => (pow_pos hs 2 : (0 : ℝ) < s ^ 2))
  refine (hK.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  simp only [Function.comp_apply]
  congr 2
  rw [hν, Measure.map_apply hm measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, mem_closedBall_zero_iff]
  exact pow_le_pow_iff_left₀ (norm_nonneg x) hs0.le two_ne_zero

/-! ## Clause (1): below the threshold -/

/-- **Step 3**: `∫ e^{-R²|x|²} μ(dx) / μ̂(Re) → (4π)^{-d/2} |S^{d-1}| ∫_0^∞ u^{d-1-c} e^{-u²/4} du`
as `R → ∞`, for `0 < c < d`. -/
theorem IsLawOf.tendsto_gauss_div_ray (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0)
    (hctop : D.profileAtOrigin ≠ ⊤) (hc0 : 0 < D.profileAtOrigin.toReal)
    (hcd : D.profileAtOrigin.toReal < d) {μ : Measure (Rd d)} (hμ : IsLawOf D μ) {e : Rd d}
    (he : ‖e‖ = 1) :
    Tendsto (fun R : ℝ => (∫ x, Real.exp (-(R ^ 2 * ‖x‖ ^ 2)) ∂μ) / (charFun μ (R • e)).re) atTop
      (𝓝 ((4 * π) ^ (-(d : ℝ) / 2) * sphereArea d *
        ∫ u in Ioi (0 : ℝ), u ^ ((d : ℝ) - 1 - D.profileAtOrigin.toReal) *
          Real.exp (-(1 / 4) * u ^ 2))) := by
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop
      (𝓝 (a ^ (-D.profileAtOrigin.toReal))) := fun a ha' =>
    hμ.tendsto_ray_ratio hd ha hctop he ha'
  have h := (hray.tendsto_gaussian_average hc0 hcd hrv).const_mul
    ((4 * π) ^ (-(d : ℝ) / 2) * sphereArea d)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [hμ.integral_gauss_eq hd ha he hR, gaussMoment_eq φ d hR]
  have e1 : R ^ (-(d : ℝ)) * R ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  set I := ∫ u in Ioi (0 : ℝ), φ (R * u) * (u ^ ((d : ℝ) - 1) * Real.exp (-(1 / 4) * u ^ 2))
    with hI
  have e2 : (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * R ^ (-(d : ℝ)) * (R ^ (d : ℝ) * I)
      = (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * I := by
    linear_combination ((4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * I) * e1
  rw [e2, mul_div_assoc]

/-- **`prop:origin-rate-d`(1), the mass of a ball**: for a datum with Gaussian coefficient `0`
and `0 < c < d`, every law `μ` of it and every unit vector `e`,
`μ{|x| ≤ s} / (R(d,c) |S^{d-1}| c⁻¹ μ̂(e/s)) → 1` as `s ↓ 0`. The law is a hypothesis; spends
A11. -/
theorem origin_ball_rate (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {e : Rd d} (he : ‖e‖ = 1) :
    Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        (rateConst d D.profileAtOrigin.toReal * sphereArea d / D.profileAtOrigin.toReal *
          (charFun μ (s⁻¹ • e)).re)) (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  have hcd' : D.profileAtOrigin.toReal < d := by
    have := (ENNReal.toReal_lt_toReal hctop (ENNReal.natCast_ne_top d)).mpr hcd
    simpa using this
  set c := D.profileAtOrigin.toReal with hcdef
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-c))) :=
    fun a ha' => hμ.tendsto_ray_ratio hd ha hctop he ha'
  have hA := (sphereArea_eq_toSphere hd).2
  set J := ∫ u in Ioi (0 : ℝ), u ^ ((d : ℝ) - 1 - c) * Real.exp (-(1 / 4) * u ^ 2) with hJ
  have hJpos : 0 < J := by
    rw [hJ, integral_rpow_mul_exp_quarter hcd']
    have : 0 < Real.Gamma (((d : ℝ) - c) / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  set Ic := (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d * J with hIc
  have hIcpos : 0 < Ic := by positivity
  have hAbel : Tendsto (fun R : ℝ => (∫ x, Real.exp (-(R ^ 2 * ‖x‖ ^ 2)) ∂μ) / φ R) atTop (𝓝 Ic) :=
    hμ.tendsto_gauss_div_ray hd ha hctop hc0 hcd' he
  -- the slowly varying function
  set ℓ : ℝ → ℝ := fun s => s ^ (c / 2) * φ (Real.sqrt s) with hℓdef
  have hℓm : Measurable ℓ :=
    (measurable_id.pow_const _).mul (hray.measurable.comp Real.continuous_sqrt.measurable)
  have hℓpos : ∀ x : ℝ, 0 < x → 0 < ℓ x := fun x hx =>
    mul_pos (Real.rpow_pos_of_pos hx _) (hray.pos _)
  have hℓ : ∀ a : ℝ, 0 < a → Tendsto (fun x => ℓ (a * x) / ℓ x) atTop (𝓝 1) := by
    intro a ha'
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha'
    have h1 := ((hrv (Real.sqrt a) hsa).comp Real.tendsto_sqrt_atTop).const_mul (a ^ (c / 2))
    have e1 : a ^ (c / 2) * Real.sqrt a ^ (-c) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha'.le, ← Real.rpow_add ha']
      have : c / 2 + 1 / 2 * -c = 0 := by ring
      rw [this, Real.rpow_zero]
    rw [e1] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, hℓdef]
    rw [Real.mul_rpow ha'.le hx.le, Real.sqrt_mul ha'.le]
    have h2 := (Real.rpow_pos_of_pos hx (c / 2)).ne'
    have h3 := (hray.pos (Real.sqrt x)).ne'
    field_simp
  have hgauss : Tendsto (fun s : ℝ => (∫ x, Real.exp (-(s * ‖x‖ ^ 2)) ∂μ) /
      (Ic * s ^ (-(c / 2)) * ℓ s)) atTop (𝓝 1) := by
    have h1 := (hAbel.comp Real.tendsto_sqrt_atTop).div_const Ic
    rw [div_self hIcpos.ne'] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [Function.comp_apply, hℓdef]
    rw [Real.sq_sqrt hs.le, div_div]
    congr 1
    have e2 : s ^ (-(c / 2)) * s ^ (c / 2) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    linear_combination (-(Ic * φ (Real.sqrt s))) * e2
  have hK := tendsto_ball_of_gauss μ ℓ hℓm hℓpos hℓ Ic (c / 2) hIcpos (by positivity) hgauss
  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  congr 1
  have e3 : (s ^ 2) ^ (c / 2) * (1 / s ^ 2) ^ (c / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), mul_one_div_cancel (by positivity),
      Real.one_rpow]
  have e4 : Real.sqrt (1 / s ^ 2) = s⁻¹ := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hs0.le]
  have e5 : Ic / Real.Gamma (1 + c / 2) = sphereArea d * (rateConst d c / c) := by
    rw [← rateConst_div hc0 hcd', hIc, hJ]
    ring
  simp only [hℓdef]
  rw [e4]
  have hG : Real.Gamma (1 + c / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  calc Ic * (s ^ 2) ^ (c / 2) * ((1 / s ^ 2) ^ (c / 2) * φ s⁻¹) / Real.Gamma (1 + c / 2)
      = Ic / Real.Gamma (1 + c / 2) * ((s ^ 2) ^ (c / 2) * (1 / s ^ 2) ^ (c / 2)) * φ s⁻¹ := by
        ring
    _ = rateConst d c * sphereArea d / c * φ s⁻¹ := by rw [e3, e5]; ring

/-- **`prop:origin-rate-d`(1), the density**: for a datum with Gaussian coefficient `0` and
`0 < c < d`, every law `μ` of it, every unit vector `e` and every `q` nonincreasing on `(0,∞)`
with `μ = q(|x|) dx`: `q(s) / (R(d,c) s^{-d} μ̂(e/s)) → 1` as `s ↓ 0`. The law and the density are
hypotheses; spends A11, through `origin_ball_rate`. -/
theorem origin_density_rate (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {e : Rd d} (he : ‖e‖ = 1) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s /
        (rateConst d D.profileAtOrigin.toReal * s ^ (-(d : ℝ)) * (charFun μ (s⁻¹ • e)).re))
      (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd.le
  have hcd' : D.profileAtOrigin.toReal < d := by
    have := (ENNReal.toReal_lt_toReal hctop (ENNReal.natCast_ne_top d)).mpr hcd
    simpa using this
  set c := D.profileAtOrigin.toReal with hcdef
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hA := (sphereArea_eq_toSphere hd).2
  have hR := rateConst_pos hc0 hcd'
  set B := rateConst d c * sphereArea d / c with hB
  have hBpos : 0 < B := by positivity
  have hW : ∀ a : ℝ, 0 < a → Tendsto (fun s : ℝ => φ (a * s)⁻¹ / φ s⁻¹) (𝓝[>] 0) (𝓝 (a ^ c)) := by
    intro a ha'
    have h1 := (hμ.tendsto_ray_ratio hd ha hctop he (inv_pos.mpr ha')).comp
      tendsto_inv_nhdsGT_zero
    have e1 : a⁻¹ ^ (-c) = a ^ c := by
      rw [Real.inv_rpow ha'.le, Real.rpow_neg ha'.le, inv_inv]
    rw [e1] at h1
    refine h1.congr fun s => ?_
    simp only [Function.comp_apply, hφ, mul_inv]
  have hm : Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal / φ s⁻¹) (𝓝[>] 0) (𝓝 B) := by
    have h1 := (origin_ball_rate hd D ha hc hcd μ hμ he).const_mul B
    rw [mul_one] at h1
    refine h1.congr fun s => ?_
    have h2 := (hray.pos s⁻¹).ne'
    simp only [hφ] at h2 ⊢
    rw [← hB]
    field_simp
  have h5 := tendsto_radial_density_of_ball hd hq hμq hc0 hBpos (fun s _ => hray.pos s⁻¹) hW hm
  have e2 : B * c / sphereArea d = rateConst d c := by
    rw [hB]
    field_simp
  rw [e2] at h5
  have h6 := h5.div_const (rateConst d c)
  rw [div_self hR.ne'] at h6
  refine h6.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  have h2 := (hray.pos s⁻¹).ne'
  have e3 : s ^ (-(d : ℝ)) = (s ^ d)⁻¹ := by
    rw [Real.rpow_neg hs0.le, Real.rpow_natCast]
  simp only [hφ] at h2 ⊢
  rw [e3]
  have h3 := (pow_pos hs0 d).ne'
  field_simp

/-! ## Clause (2): at the threshold -/

/-- Polar coordinates on a ball: `∫_{|ξ| ≤ y} μ̂ = |S^{d-1}| ∫_0^y μ̂(ρe) ρ^{d-1} dρ`. -/
theorem IsLawOf.integral_charFun_closedBall (hd : 1 ≤ d) {D : OriginDatum d} (ha : D.a = 0)
    {μ : Measure (Rd d)} (hμ : IsLawOf D μ) {e : Rd d} (he : ‖e‖ = 1) {y : ℝ} (hy : 0 ≤ y) :
    ∫ ξ in closedBall (0 : Rd d) y, (charFun μ ξ).re
      = sphereArea d * truncMoment (fun ρ : ℝ => (charFun μ (ρ • e)).re) d y := by
  haveI := hμ.1
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hA := (sphereArea_eq_toSphere hd).2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : ∀ ξ : Rd d, (charFun μ ξ).re = φ ‖ξ‖ := by
    intro ξ
    simp only [hφ]
    rw [hμ.charFun_re, hμ.charFun_re, D.exponent_eq_of_norm_eq (ξ := ξ) (ξ' := ‖ξ‖ • e)
      (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg _)])]
  set g : ℝ → ℝ≥0∞ := (Iic y).indicator (fun r => ENNReal.ofReal (φ r)) with hg
  have hgm : Measurable g := hray.measurable.ennreal_ofReal.indicator measurableSet_Iic
  have hint : IntegrableOn (fun ρ => φ ρ * ρ ^ ((d : ℝ) - 1)) (Ioc 0 y) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp
      (hray.intervalIntegrable_mul_rpow hd0 0 y)
  have h1 : ∫⁻ ξ in closedBall (0 : Rd d) y, ENNReal.ofReal (charFun μ ξ).re
      = ENNReal.ofReal (sphereArea d) * ENNReal.ofReal (truncMoment φ d y) := by
    have h2 : ∫⁻ ξ in closedBall (0 : Rd d) y, ENNReal.ofReal (charFun μ ξ).re
        = ∫⁻ ξ : Rd d, g ‖ξ‖ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      refine lintegral_congr fun ξ => ?_
      simp only [hg, indicator, mem_closedBall_zero_iff, mem_Iic, hre ξ]
    rw [h2, lintegral_radial hd g hgm, truncMoment, intervalIntegral.integral_of_le hy,
      ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun r hr =>
          mul_nonneg (hray.pos r).le (Real.rpow_nonneg hr.1.le _)))]
    congr 1
    have h3 : ∫⁻ r in Ioi (0 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1))
        = ∫⁻ r in Ioi (0 : ℝ), (Iic y).indicator
            (fun r => ENNReal.ofReal (φ r * r ^ ((d : ℝ) - 1))) r := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      simp only [hg, indicator]
      split_ifs
      · rw [← ENNReal.ofReal_mul (hray.pos r).le, pow_pred_eq_rpow hd hr0]
      · rw [zero_mul]
    rw [h3, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi]
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_closedBall).mpr (.of_forall fun ξ _ =>
      hμ.charFun_re_nonneg ξ))
    ((Complex.continuous_re.comp continuous_charFun).aestronglyMeasurable), h1,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le,
    ENNReal.toReal_ofReal (hray.truncMoment_nonneg hy)]

/-- The unit ball: `V_d = |S^{d-1}|/d`. -/
theorem volume_unitBall_eq_sphereArea_div (hd : 1 ≤ d) :
    (volume (ball (0 : Rd d) 1)).toReal = sphereArea d / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sphereArea_eq_mul_volume_unitBall hd]
  field_simp

/-- **`prop:origin-rate-d`(2), the mass of a ball**: for a datum with Gaussian coefficient `0`
and `c = d`, and every law `μ` of it,
`μ{|x| ≤ s} / ((2π)^{-d} V_d s^d ∫_{|ξ| ≤ 1/s} μ̂) → 1` as `s ↓ 0`. The law is a hypothesis;
spends A11. -/
theorem origin_ball_rate_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        ((2 * π) ^ (-(d : ℝ)) * (volume (ball (0 : Rd d) 1)).toReal * s ^ d *
          ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re)) (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he₁
  have he : ‖e‖ = 1 := by simp [he₁, ebasis]
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hcd' : D.profileAtOrigin.toReal = d := by rw [hcd]; simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-(d : ℝ)))) := by
    intro a ha'
    have := hμ.tendsto_ray_ratio hd ha hctop he ha'
    rwa [hcd'] at this
  have hA := (sphereArea_eq_toSphere hd).2
  set Kd := (4 * π) ^ (-(d : ℝ) / 2) * sphereArea d with hKd
  have hKdpos : 0 < Kd := by positivity
  have hT := hray.tendsto_gaussMoment_div_truncMoment hd0 hrv
  set ℓ : ℝ → ℝ := fun s => truncMoment φ d (Real.sqrt s) with hℓdef
  have hℓm : Measurable ℓ := by
    have hc : Continuous fun y : ℝ => truncMoment φ d y :=
      intervalIntegral.continuous_primitive (fun a b => hray.intervalIntegrable_mul_rpow hd0 a b) 0
    exact (hc.comp Real.continuous_sqrt).measurable
  have hℓpos : ∀ x : ℝ, 0 < x → 0 < ℓ x := fun x hx =>
    hray.truncMoment_pos hd0 (Real.sqrt_pos.mpr hx)
  have hℓ : ∀ a : ℝ, 0 < a → Tendsto (fun x => ℓ (a * x) / ℓ x) atTop (𝓝 1) := by
    intro a ha'
    have h1 := (hray.tendsto_truncMoment_dilate hd0 hrv (Real.sqrt_pos.mpr ha')).comp
      Real.tendsto_sqrt_atTop
    refine h1.congr fun x => ?_
    simp only [Function.comp_apply, hℓdef]
    rw [Real.sqrt_mul ha'.le]
  have hgauss : Tendsto (fun s : ℝ => (∫ x, Real.exp (-(s * ‖x‖ ^ 2)) ∂μ) /
      (Kd * s ^ (-((d : ℝ) / 2)) * ℓ s)) atTop (𝓝 1) := by
    refine (hT.comp Real.tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    simp only [Function.comp_apply, hℓdef]
    have e1 : ∫ x, Real.exp (-(s * ‖x‖ ^ 2)) ∂μ
        = Kd * Real.sqrt s ^ (-(d : ℝ)) * gaussMoment φ d (Real.sqrt s) := by
      have := hμ.integral_gauss_eq hd ha he hss
      rwa [Real.sq_sqrt hs.le] at this
    have e2 : Real.sqrt s ^ (-(d : ℝ)) = s ^ (-((d : ℝ) / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [e1, e2]
    have h1 := (Real.rpow_pos_of_pos hs (-((d : ℝ) / 2))).ne'
    have h2 := (hray.truncMoment_pos hd0 hss).ne'
    field_simp
  have hK := tendsto_ball_of_gauss μ ℓ hℓm hℓpos hℓ Kd ((d : ℝ) / 2) hKdpos (by positivity) hgauss
  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  congr 1
  have e3 : (s ^ 2) ^ ((d : ℝ) / 2) = s ^ d := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs0.le, ← Real.rpow_natCast]
    congr 1
    ring
  have e4 : Real.sqrt (1 / s ^ 2) = 1 / s := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hs0.le, one_div]
  simp only [hℓdef]
  rw [e3, e4, hμ.integral_charFun_closedBall hd ha he (by positivity : (0 : ℝ) ≤ 1 / s),
    volume_unitBall_eq_sphereArea_div hd]
  have e5 := critConst_eq hd
  have hG : Real.Gamma (1 + (d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  calc Kd * s ^ d * truncMoment φ d (1 / s) / Real.Gamma (1 + (d : ℝ) / 2)
      = (4 * π) ^ (-(d : ℝ) / 2) / Real.Gamma (1 + (d : ℝ) / 2) *
          (sphereArea d * s ^ d * truncMoment φ d (1 / s)) := by rw [hKd]; ring
    _ = (2 * π) ^ (-(d : ℝ)) * (sphereArea d / d) * s ^ d *
          (sphereArea d * truncMoment φ d (1 / s)) := by rw [e5]; ring

/-- **`prop:origin-rate-d`(2), the density**: for a datum with Gaussian coefficient `0` and
`c = d`, every law `μ` of it and every `q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx`:
`q(s) / ((2π)^{-d} ∫_{|ξ| ≤ 1/s} μ̂) → 1` as `s ↓ 0`. Spends A11, through
`origin_ball_rate_critical`. -/
theorem origin_density_rate_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioi 0)) (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s /
        ((2 * π) ^ (-(d : ℝ)) * ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re))
      (𝓝[>] 0) (𝓝 1) := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he₁
  have he : ‖e‖ = 1 := by simp [he₁, ebasis]
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hcd' : D.profileAtOrigin.toReal = d := by rw [hcd]; simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hrv : ∀ a : ℝ, 0 < a → Tendsto (fun R => φ (a * R) / φ R) atTop (𝓝 (a ^ (-(d : ℝ)))) := by
    intro a ha'
    have := hμ.tendsto_ray_ratio hd ha hctop he ha'
    rwa [hcd'] at this
  have hA := (sphereArea_eq_toSphere hd).2
  have hI : ∀ s : ℝ, 0 < s → ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re
      = sphereArea d * truncMoment φ d (1 / s) := fun s hs =>
    hμ.integral_charFun_closedBall hd ha he (by positivity)
  have hPpos : ∀ s : ℝ, 0 < s → 0 < truncMoment φ d (1 / s) := fun s hs =>
    hray.truncMoment_pos hd0 (by positivity)
  set B := (2 * π) ^ (-(d : ℝ)) * (sphereArea d / d) * sphereArea d with hB
  have hBpos : 0 < B := by positivity
  set W : ℝ → ℝ := fun s => s ^ d * truncMoment φ d (1 / s) with hWdef
  have hWpos : ∀ s : ℝ, 0 < s → 0 < W s := fun s hs => mul_pos (pow_pos hs d) (hPpos s hs)
  have hW : ∀ a : ℝ, 0 < a → Tendsto (fun s => W (a * s) / W s) (𝓝[>] 0) (𝓝 (a ^ (d : ℝ))) := by
    intro a ha'
    have h1 := ((hray.tendsto_truncMoment_dilate hd0 hrv (inv_pos.mpr ha')).comp
      tendsto_inv_nhdsGT_zero).const_mul (a ^ d)
    rw [mul_one, ← Real.rpow_natCast] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0 : ℝ) < s := hs
    simp only [Function.comp_apply, hWdef]
    rw [Real.rpow_natCast, mul_pow, one_div, one_div, mul_inv]
    have h2 := (pow_pos hs0 d).ne'
    have h3 : truncMoment φ d s⁻¹ ≠ 0 := by
      have := hPpos s hs0
      rw [one_div] at this
      exact this.ne'
    field_simp
  have hm : Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal / W s) (𝓝[>] 0) (𝓝 B) := by
    have h1 := (origin_ball_rate_critical hd D ha hcd μ hμ).const_mul B
    rw [mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0 : ℝ) < s := hs
    simp only [hWdef]
    rw [hI s hs0, volume_unitBall_eq_sphereArea_div hd, hB]
    have h2 := (pow_pos hs0 d).ne'
    have h3 := (hPpos s hs0).ne'
    have h4 : (2 * π) ^ (-(d : ℝ)) ≠ 0 := by positivity
    field_simp
  have h5 := tendsto_radial_density_of_ball hd hq hμq hd0 hBpos hWpos hW hm
  have hlim : B * d / sphereArea d = (2 * π) ^ (-(d : ℝ)) * sphereArea d := by
    rw [hB]
    field_simp
  rw [hlim] at h5
  have hne : (2 * π) ^ (-(d : ℝ)) * sphereArea d ≠ 0 := by positivity
  have h6 := h5.div_const ((2 * π) ^ (-(d : ℝ)) * sphereArea d)
  rw [div_self hne] at h6
  refine h6.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  simp only [hWdef]
  rw [hI s hs0]
  have h2 := (pow_pos hs0 d).ne'
  have h3 := (hPpos s hs0).ne'
  have h4 : (2 * π) ^ (-(d : ℝ)) ≠ 0 := by positivity
  field_simp

/-- **`prop:origin-rate-d`(2), the logarithmic bound on the truncated transform**: for a datum
with Gaussian coefficient `0` and `c = d`, and every law `μ` of it,
`∫_{|ξ| ≤ 1/s} μ̂ ≥ |S^{d-1}| e^{-13d/4 - 2C_k} log(1/s)` for `0 < s ≤ 1`. Lean core. -/
theorem origin_transform_ball_log (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    sphereArea d * Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) * Real.log (1 / s)
      ≤ ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re := by
  haveI := hμ.1
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he₁
  have he : ‖e‖ = 1 := by simp [he₁, ebasis]
  have hctop : D.profileAtOrigin ≠ ⊤ := by rw [hcd]; exact ENNReal.natCast_ne_top d
  have hcd' : D.profileAtOrigin.toReal = d := by rw [hcd]; simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set φ : ℝ → ℝ := fun ρ => (charFun μ (ρ • e)).re with hφ
  have hray : IsRayProfile φ := hμ.isRayProfile hd ha e
  have hA := (sphereArea_eq_toSphere hd).2
  set C₀ := Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) with hC₀
  have hy : (1 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs.1]; simpa using hs.2
  rw [hμ.integral_charFun_closedBall hd ha he (by positivity : (0 : ℝ) ≤ 1 / s), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hA.le
  have h1 : C₀ * Real.log (1 / s) ≤ truncMoment φ d (1 / s) - truncMoment φ d 1 := by
    rw [hray.truncMoment_sub hd0, ← div_one (1 / s), ← integral_inv_of_pos one_pos (by positivity),
      div_one, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hy
      ((intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le hy] at hx
        exact (lt_of_lt_of_le one_pos hx.1).ne') continuousOn_id).const_mul _)
      (hray.intervalIntegrable_mul_rpow hd0 1 (1 / s)) fun ρ hρ => ?_
    have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ.1
    have hb := (isotropic_exponent_log_bound hd D ha hctop (ρ • e)
      (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hρ0.le]; exact hρ.1)).2
    rw [hcd', norm_smul, he, mul_one, Real.norm_of_nonneg hρ0.le, ← hμ.charFun_re] at hb
    calc C₀ * ρ⁻¹ = C₀ * ρ ^ (-(d : ℝ)) * ρ ^ ((d : ℝ) - 1) := by
          rw [mul_assoc, ← Real.rpow_add hρ0, show -(d : ℝ) + ((d : ℝ) - 1) = -1 by ring,
            Real.rpow_neg_one]
      _ ≤ φ ρ * ρ ^ ((d : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hρ0.le _)
  have h2 : 0 ≤ truncMoment φ d 1 := hray.truncMoment_nonneg zero_le_one
  linarith

/-- **`prop:origin-rate-d`(2), the logarithmic growth of the density**: for a datum with Gaussian
coefficient `0` and `c = d`, every law `μ` of it, every `q` nonincreasing on `(0,∞)` with
`μ = q(|x|) dx` and every `C < (2π)^{-d} |S^{d-1}| e^{-13d/4 - 2C_k}`:
`q(s) ≥ C log(1/s)` for all small `s > 0`. Spends A11. -/
theorem origin_density_log_lower (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioi 0)) (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    {C : ℝ} (hC : C < (2 * π) ^ (-(d : ℝ)) * sphereArea d *
      Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), C * Real.log (1 / s) ≤ q s := by
  have hA := (sphereArea_eq_toSphere hd).2
  set Cs := (2 * π) ^ (-(d : ℝ)) * sphereArea d *
    Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) with hCs
  have hCspos : 0 < Cs := by positivity
  set θ := max (C / Cs) 0 with hθ
  have hθ1 : θ < 1 := max_lt ((div_lt_one hCspos).mpr hC) one_pos
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hCθ : C ≤ θ * Cs := by
    have := le_max_left (C / Cs) 0
    rw [← hθ, div_le_iff₀ hCspos] at this
    exact this
  have hlim := origin_density_rate_critical hd D ha hcd μ hμ hq hμq
  filter_upwards [hlim.eventually (lt_mem_nhds hθ1), Ioc_mem_nhdsGT one_pos] with s hs hs1
  have hI := origin_transform_ball_log hd D ha hcd μ hμ hs1
  set I := ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re with hIdef
  have hlog : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by
    rw [le_div_iff₀ hs1.1]; simpa using hs1.2)
  have hpi : (0 : ℝ) < (2 * π) ^ (-(d : ℝ)) := by positivity
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  rcases eq_or_lt_of_le hI0 with hIz | hIpos
  · -- then `log (1/s) = 0`
    have hl0 : Real.log (1 / s) = 0 := by
      have h1 : sphereArea d * Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) *
          Real.log (1 / s) ≤ 0 := by rw [hIz]; exact hI
      have h2 : 0 < sphereArea d * Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) := by
        positivity
      nlinarith
    rw [← hIz, mul_zero, div_zero] at hs
    exact absurd hs (not_lt.mpr hθ0)
  · have hden : 0 < (2 * π) ^ (-(d : ℝ)) * I := mul_pos hpi hIpos
    have h1 : θ * ((2 * π) ^ (-(d : ℝ)) * I) < q s := (lt_div_iff₀ hden).mp hs
    have h2 : Cs * Real.log (1 / s) ≤ (2 * π) ^ (-(d : ℝ)) * I := by
      calc Cs * Real.log (1 / s) = (2 * π) ^ (-(d : ℝ)) * (sphereArea d *
            Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) * Real.log (1 / s)) := by
            rw [hCs]; ring
        _ ≤ (2 * π) ^ (-(d : ℝ)) * I := mul_le_mul_of_nonneg_left hI hpi.le
    calc C * Real.log (1 / s) ≤ θ * Cs * Real.log (1 / s) :=
          mul_le_mul_of_nonneg_right hCθ hlog
      _ = θ * (Cs * Real.log (1 / s)) := by ring
      _ ≤ θ * ((2 * π) ^ (-(d : ℝ)) * I) := mul_le_mul_of_nonneg_left h2 hθ0
      _ ≤ q s := h1.le

/-! ## The bundles, with the existence of the density -/

/-- **`prop:origin-rate-d`(1)**, in one statement: the law of a datum with Gaussian coefficient
`0` and `0 < c < d` has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`
(`radial_monotone_law`), and for every unit vector `e`, as `s ↓ 0`,
`μ{|x| ≤ s} ∼ R(d,c) |S^{d-1}| c⁻¹ μ̂(e/s)` and `q(s) ∼ R(d,c) s^{-d} μ̂(e/s)`. Spends A11, and
A8, A2 and A3(iii) for the existence of `q`. -/
theorem origin_rate (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (hcd : D.profileAtOrigin < d) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {e : Rd d} (he : ‖e‖ = 1) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        (rateConst d D.profileAtOrigin.toReal * sphereArea d / D.profileAtOrigin.toReal *
          (charFun μ (s⁻¹ • e)).re)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun s : ℝ => q s /
        (rateConst d D.profileAtOrigin.toReal * s ^ (-(d : ℝ)) * (charFun μ (s⁻¹ • e)).re))
        (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨q, hq0, hq, hμq⟩ :=
    radial_monotone_law hd D (Or.inr (D.not_ae_zero_of_profileAtOrigin_pos hc)) μ hμ
  exact ⟨q, hq0, hq, hμq, origin_ball_rate hd D ha hc hcd μ hμ he,
    origin_density_rate hd D ha hc hcd μ hμ he hq hμq⟩

/-- **`prop:origin-rate-d`(2)**, in one statement: the law of a datum with Gaussian coefficient
`0` and `c = d` has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)`, and, as
`s ↓ 0`, `μ{|x| ≤ s} ∼ (2π)^{-d} V_d s^d ∫_{|ξ| ≤ 1/s} μ̂` and `q(s) ∼ (2π)^{-d} ∫_{|ξ| ≤ 1/s} μ̂`;
the integral is at least `|S^{d-1}| e^{-13d/4 - 2C_k} log(1/s)` for `0 < s ≤ 1`, and
`q(s) ≥ C log(1/s)` for small `s`, for every `C` below `(2π)^{-d} |S^{d-1}| e^{-13d/4 - 2C_k}`.
Spends A11, and A8, A2 and A3(iii) for the existence of `q`. -/
theorem origin_rate_critical (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hcd : D.profileAtOrigin = d) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => (μ (closedBall 0 s)).toReal /
        ((2 * π) ^ (-(d : ℝ)) * (volume (ball (0 : Rd d) 1)).toReal * s ^ d *
          ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun s : ℝ => q s /
        ((2 * π) ^ (-(d : ℝ)) * ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re))
        (𝓝[>] 0) (𝓝 1) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1,
        sphereArea d * Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) * Real.log (1 / s)
          ≤ ∫ ξ in closedBall (0 : Rd d) (1 / s), (charFun μ ξ).re) ∧
      ∀ C : ℝ, C < (2 * π) ^ (-(d : ℝ)) * sphereArea d *
          Real.exp (-(13 / 4 * (d : ℝ)) - 2 * D.tailConst) →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), C * Real.log (1 / s) ≤ q s := by
  have hc : 0 < D.profileAtOrigin := by
    rw [hcd]
    exact_mod_cast hd
  obtain ⟨q, hq0, hq, hμq⟩ :=
    radial_monotone_law hd D (Or.inr (D.not_ae_zero_of_profileAtOrigin_pos hc)) μ hμ
  exact ⟨q, hq0, hq, hμq, origin_ball_rate_critical hd D ha hcd μ hμ,
    origin_density_rate_critical hd D ha hcd μ hμ hq hμq,
    fun s hs => origin_transform_ball_log hd D ha hcd μ hμ hs,
    fun C hC => origin_density_log_lower hd D ha hcd μ hμ hq hμq hC⟩

end AffineHemigroup
