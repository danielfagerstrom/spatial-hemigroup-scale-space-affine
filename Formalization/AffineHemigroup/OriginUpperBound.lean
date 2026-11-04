/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginLowerBound
import AffineHemigroup.RadialMonotone

/-!
# `prop:origin-upper-bound-d`: an upper bound at the origin, and the order of the density there

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:origin-upper-bound-d` (Q-0415).

For an isotropic origin datum `(0, k_d)` in dimension `d ≥ 1` with profile at the origin
`0 < c ≤ d`, and a law `μ` of it:

* `origin_upper_bound` (clauses (1) and (2)): for `0 < β < c` there is a constant `C'` of
  `thm:origin-boundedness-d`(4), `∫ g_t dμ ≤ C' t^{-(d-β)/2}` for every `t > 0`, and with
  `A = (2π)^{d/2} e^{1/2} C'`: `μ{|x| < r} ≤ A r^β` for every `r > 0`, and
  `q(r) ≤ (A/V_d) r^{β-d}` for every `r > 0` and every nonincreasing `q` on `(0,∞)` with
  `μ = q(|x|) dx`. `origin_upper_bound_of_heat` is the same with `C'` given: every constant of
  the heat bound will do;
* `origin_density_upper` (clause (2) with the existence of `q`, which is
  `prop:isotropic-radial-monotone`(2));
* `origin_density_lower` (clause (3)): for `d ≥ 2`, the bound `q(r) ≥ c₁ r^{c-d}` of
  `prop:origin-lower-bound-d` holds at every radius `0 < r < δ`, for every such `q`;
* `origin_density_log_order` and `origin_ball_log_order` (clause (3)): for `d ≥ 2`,
  `log q(|x|)/log(1/|x|) → d - c` as `x → 0` and `log μ{|x| < r}/log r → c` as `r ↓ 0`;
* `origin_density_order`: the bundle for `d ≥ 2`, a nonincreasing `q` with `μ = q(|x|) dx`, the
  two bounds and the limit.

**What is spent.** `origin_upper_bound`, `origin_upper_bound_of_heat` and every helper before them
name the law and the density as hypotheses and spend nothing. `origin_density_lower`,
`origin_density_log_order` and `origin_ball_log_order` spend A3(iii), through
`origin_lower_bound`. The two bundles spend A8, A2 and A3(iii), through `radial_monotone_law`.

**The route.** On the ball `|x| < r` the heat kernel `g_{r²}` is at least
`(2π)^{-d/2} e^{-1/2} r^{-d}` (`heatKernel_sq_ge`), so
`μ{|x| < r} ≤ (2π)^{d/2} e^{1/2} r^d ∫ g_{r²} dμ` (`measure_ball_le_heatKernel`), and the upper
bound of `thm:origin-boundedness-d`(4) (`heat_upper`) at `t = r²` gives clause (1). A
nonincreasing radial density is at least `q(r)` on the ball, so
`q(r) V_d r^d ≤ μ{|x| < r}` (`radial_density_le_ball`), which gives clause (2). For clause (3), a
radius `r₀ < δ` with `q(r₀) < c₁ r₀^{c-d}` would put the density below `c₁|x|^{c-d}` on a shell
`r₀ < |x| < r₁`, a nonempty open set, against the almost-everywhere bound of
`origin_lower_bound_density`. The two limits come from one squeeze, `tendsto_log_div_log_inv`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Real

variable {d : ℕ}

/-! ## The mass of a ball against the heat kernel (Mathlib types and `heatKernel`) -/

/-- On the ball `|x| < r` the heat kernel at `t = r²` is at least `(2π)^{-d/2} e^{-1/2} r^{-d}`. -/
theorem heatKernel_sq_ge {r : ℝ} (hr : 0 < r) {x : Rd d} (hx : ‖x‖ < r) :
    ((2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d)⁻¹ ≤ heatKernel d (r ^ 2) x := by
  unfold heatKernel
  have hpi : 0 < 2 * π := by positivity
  have hrd : (r ^ 2) ^ ((d : ℝ) / 2) = r ^ d := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r d]
    congr 1
    push_cast
    ring
  have h1 : (2 * π * r ^ 2) ^ (-(d : ℝ) / 2) = ((2 * π) ^ ((d : ℝ) / 2) * r ^ d)⁻¹ := by
    rw [Real.mul_rpow hpi.le (sq_nonneg r), neg_div, Real.rpow_neg hpi.le,
      Real.rpow_neg (sq_nonneg r), ← mul_inv, hrd]
  have hsq : ‖x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx.le 2
  have h2 : Real.exp (-(1 / 2)) ≤ Real.exp (-‖x‖ ^ 2 / (2 * r ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    linarith
  calc ((2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d)⁻¹
      = ((2 * π) ^ ((d : ℝ) / 2) * r ^ d)⁻¹ * Real.exp (-(1 / 2)) := by
        rw [Real.exp_neg, ← mul_inv]
        congr 1
        ring
    _ ≤ (2 * π * r ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * r ^ 2)) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The mass of a ball is at most a multiple of the heat average**: for a finite measure `μ` on
`ℝ^d` and `r > 0`, `μ{|x| < r} ≤ (2π)^{d/2} e^{1/2} r^d ∫ g_{r²} dμ`. -/
theorem measure_ball_le_heatKernel (μ : Measure (Rd d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) :
    (μ (ball 0 r)).toReal ≤
      (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d * ∫ x, heatKernel d (r ^ 2) x ∂μ := by
  have ht : 0 < r ^ 2 := by positivity
  have hK0 : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d := by positivity
  have hint : Integrable (heatKernel d (r ^ 2)) μ :=
    Integrable.of_bound continuous_heatKernel.aestronglyMeasurable _
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht x)]
        exact heatKernel_le ht x)
  have h1 : ((2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d)⁻¹ * (μ (ball 0 r)).toReal ≤
      ∫ x in ball 0 r, heatKernel d (r ^ 2) x ∂μ :=
    setIntegral_ge_of_const_le_real measurableSet_ball (measure_ne_top μ _)
      (fun x hx => heatKernel_sq_ge hr (mem_ball_zero_iff.mp hx)) hint.integrableOn
  have h2 : ∫ x in ball 0 r, heatKernel d (r ^ 2) x ∂μ ≤ ∫ x, heatKernel d (r ^ 2) x ∂μ :=
    setIntegral_le_integral hint (ae_of_all _ (heatKernel_nonneg ht))
  have h3 := h1.trans h2
  rwa [inv_mul_le_iff₀ hK0] at h3

/-! ## A nonincreasing radial density against the mass of a ball (Mathlib types) -/

/-- A measure with a radial density `q(|x|)`, `q` nonincreasing on `(0,∞)`, gives the ball
`|x| < r` at least `q(r)` times its volume: the density is at least `q(r)` there, off the origin. -/
theorem radial_density_mul_ball_le (hd : 1 ≤ d) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    {μ : Measure (Rd d)} (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)))
    {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (q r) * volume (ball (0 : Rd d) r) ≤ μ (ball 0 r) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  rw [hμ, withDensity_apply _ measurableSet_ball, ← setLIntegral_const]
  refine setLIntegral_mono_ae' measurableSet_ball ?_
  have h0 : ∀ᵐ x ∂(volume : Measure (Rd d)), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx0 hx
  exact ENNReal.ofReal_le_ofReal
    (hq (mem_Ioi.mpr (norm_pos_iff.mpr hx0)) (mem_Ioi.mpr hr) (mem_ball_zero_iff.mp hx).le)

/-- The volume of the unit ball of `ℝ^d` is positive and finite. -/
theorem volume_unitBall_toReal_pos : 0 < (volume (ball (0 : Rd d) 1)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The real form: `q(r) V_d r^d ≤ μ{|x| < r}`, `V_d` the volume of the unit ball. -/
theorem radial_density_le_ball (hd : 1 ≤ d) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) {r : ℝ} (hr : 0 < r) :
    q r * ((volume (ball (0 : Rd d) 1)).toReal * r ^ d) ≤ (μ (ball 0 r)).toReal := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have h := radial_density_mul_ball_le hd hq hμ hr
  have hV : volume (ball (0 : Rd d) r) = ENNReal.ofReal (r ^ d) * volume (ball (0 : Rd d) 1) := by
    rw [Measure.addHaar_ball volume (0 : Rd d) hr.le, finrank_Rd]
  have h' := ENNReal.toReal_mono (measure_ne_top μ _) h
  rw [ENNReal.toReal_mul, hV, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d),
    ENNReal.toReal_ofReal'] at h'
  calc q r * ((volume (ball (0 : Rd d) 1)).toReal * r ^ d)
      ≤ max (q r) 0 * (r ^ d * (volume (ball (0 : Rd d) 1)).toReal) := by
        rw [mul_comm (volume (ball (0 : Rd d) 1)).toReal]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ (μ (ball 0 r)).toReal := h'

/-! ## Clauses (1) and (2): the two upper bounds -/

/-- **`prop:origin-upper-bound-d`(1)–(2), from a heat bound**: if a finite measure `μ` on `ℝ^d`
satisfies `∫ g_t dμ ≤ C' t^{-(d-β)/2}` for every `t > 0`, then with `A = (2π)^{d/2} e^{1/2} C'`,
`μ{|x| < r} ≤ A r^β` for every `r > 0`, and `q(r) ≤ (A/V_d) r^{β-d}` for every `r > 0` and every
`q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx`. Every constant `C'` of the heat bound will do. -/
theorem origin_upper_bound_of_heat (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    {β C' : ℝ}
    (hheat : ∀ t : ℝ, 0 < t → ∫ x, heatKernel d t x ∂μ ≤ C' * t ^ (-((d : ℝ) - β) / 2)) :
    (∀ r : ℝ, 0 < r →
        (μ (ball 0 r)).toReal ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β) ∧
      ∀ q : ℝ → ℝ, AntitoneOn q (Ioi 0) →
        μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) → ∀ r : ℝ, 0 < r →
          q r ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' /
            (volume (ball (0 : Rd d) 1)).toReal * r ^ (β - d) := by
  have hK₀pos : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) := by positivity
  have key : ∀ r : ℝ, 0 < r →
      (μ (ball 0 r)).toReal ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β := by
    intro r hr
    have h1 := measure_ball_le_heatKernel μ hr
    have h2 := hheat (r ^ 2) (by positivity)
    have hpow : (r ^ 2) ^ (-((d : ℝ) - β) / 2) = r ^ (β - d) := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    have hpow2 : r ^ d * r ^ (β - d) = r ^ β := by
      rw [← Real.rpow_natCast r d, ← Real.rpow_add hr]
      congr 1
      ring
    rw [hpow] at h2
    calc (μ (ball 0 r)).toReal
        ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d *
            ∫ x, heatKernel d (r ^ 2) x ∂μ := h1
      _ ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * r ^ d * (C' * r ^ (β - d)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK₀pos.le (pow_nonneg hr.le d))
      _ = (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * (r ^ d * r ^ (β - d)) := by ring
      _ = (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β := by rw [hpow2]
  refine ⟨key, fun q hq hμq r hr => ?_⟩
  have hV := volume_unitBall_toReal_pos (d := d)
  have h1 := radial_density_le_ball hd hq hμq hr
  have h2 := key r hr
  have hrd : 0 < r ^ d := pow_pos hr d
  have hpow : r ^ (β - d) = r ^ β / r ^ d := by
    rw [Real.rpow_sub hr, Real.rpow_natCast]
  rw [hpow, div_mul_div_comm, le_div_iff₀ (mul_pos hV hrd)]
  exact h1.trans h2

/-- **`prop:origin-upper-bound-d`(1)–(2)**: for a datum with Gaussian coefficient `0` and
`0 < c ≤ d`, every law `μ` of it and every `0 < β < c`, there is a constant `C'` of
`thm:origin-boundedness-d`(4), `∫ g_t dμ ≤ C' t^{-(d-β)/2}` for every `t > 0`, such that with
`A = (2π)^{d/2} e^{1/2} C'`: `μ{|x| < r} ≤ A r^β` for every `r > 0` (clause (1)), and
`q(r) ≤ (A/V_d) r^{β-d}` for every `r > 0` and every `q` nonincreasing on `(0,∞)` with
`μ = q(|x|) dx` (clause (2)). The law and the density are hypotheses: nothing is spent. -/
theorem origin_upper_bound (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) {β : ℝ} (hβ0 : 0 < β)
    (hβc : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ C' : ℝ, 0 < C' ∧
      (∀ t : ℝ, 0 < t → ∫ x, heatKernel d t x ∂μ ≤ C' * t ^ (-((d : ℝ) - β) / 2)) ∧
      (∀ r : ℝ, 0 < r → μ (ball 0 r) ≤
        ENNReal.ofReal ((2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β)) ∧
      ∀ q : ℝ → ℝ, AntitoneOn q (Ioi 0) →
        μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) → ∀ r : ℝ, 0 < r →
          q r ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' /
            (volume (ball (0 : Rd d) 1)).toReal * r ^ (β - d) := by
  haveI := hμ.1
  obtain ⟨C', hC', hheat⟩ := heat_upper hd D ha hc μ hμ hcd hβ0 hβc
  obtain ⟨hball, hq⟩ := origin_upper_bound_of_heat hd μ hheat
  refine ⟨C', hC', hheat, fun r hr => ?_, hq⟩
  have hpos : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' := by positivity
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
    (mul_pos hpos (Real.rpow_pos_of_pos hr β)).le).mpr (hball r hr)

/-! ## The existence of the density -/

/-- A datum with `c = k_d(0+) > 0` has a profile that is not almost everywhere `0`: `k_d` is
positive at some radius, hence on an interval `(0, r]`, being nonincreasing. The converse of
`OriginDatum.profileAtOrigin_pos_of_nontrivial`. -/
theorem OriginDatum.not_ae_zero_of_profileAtOrigin_pos (D : OriginDatum d)
    (hc : 0 < D.profileAtOrigin) : ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0 := by
  intro hae
  rw [OriginDatum.profileAtOrigin] at hc
  obtain ⟨⟨r, hr⟩, hkr⟩ := lt_iSup_iff.mp hc
  have hkr' : 0 < D.k r := ENNReal.ofReal_pos.mp hkr
  have hr0 : (0 : ℝ) < r := hr
  have hex : ∃ s ∈ Ioo (0 : ℝ) r, D.k s = 0 := by
    by_contra hne
    push Not at hne
    have hsub : Ioo (0 : ℝ) r ⊆ {x | ¬ D.k x = 0} := fun x hx => hne x hx
    have h0 : (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 r) = 0 :=
      measure_mono_null hsub (ae_iff.mp hae)
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  obtain ⟨s, hs, hks⟩ := hex
  have hle : D.k r ≤ D.k s := D.k_antitone (mem_Ioi.mpr hs.1) (mem_Ioi.mpr hr0) hs.2.le
  linarith

/-- **`prop:origin-upper-bound-d`(2)**, with the existence of the density: the law has a density
`x ↦ q(|x|)` with `q ≥ 0` nonincreasing on `(0,∞)` (`radial_monotone_law`), and for every
`0 < β < c` there is `C` with `q(r) ≤ C r^{β-d}` for every `r > 0`. Spends A8, A2 and A3(iii),
through `radial_monotone_law`; the bound itself is `origin_upper_bound`. -/
theorem origin_density_upper (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      ∀ β : ℝ, 0 < β → ENNReal.ofReal β < D.profileAtOrigin →
        ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → q r ≤ C * r ^ (β - d) := by
  obtain ⟨q, hq0, hq, hμq⟩ :=
    radial_monotone_law hd D (Or.inr (D.not_ae_zero_of_profileAtOrigin_pos hc)) μ hμ
  refine ⟨q, hq0, hq, hμq, fun β hβ0 hβc => ?_⟩
  obtain ⟨C', hC', -, -, hb⟩ := origin_upper_bound hd D ha hc μ hμ hcd hβ0 hβc
  have hpos : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' := by positivity
  exact ⟨_, div_pos hpos volume_unitBall_toReal_pos, fun r hr => hb q hq hμq r hr⟩

/-! ## Clause (3): the lower bound at every radius -/

/-- **`prop:origin-upper-bound-d`(3), the lower bound**: for `d ≥ 2`, with `ε₀` and `c₁` as in
`origin_lower_bound`, every `q` nonincreasing on `(0,∞)` with `μ = q(|x|) dx` satisfies
`q(r) ≥ c₁ r^{c-d}` at every radius `0 < r < ε₀/2`, with no exceptional set. A radius where it
failed would put the density below `c₁|x|^{c-d}` on a shell, a nonempty open set, against the
almost-everywhere bound `origin_lower_bound_density`. -/
theorem origin_density_lower (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc0 : 0 < D.profileAtOrigin) (hctop : D.profileAtOrigin ≠ ⊤) (μ : Measure (Rd d))
    (hμ : IsLawOf D μ) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioc (0 : ℝ) 1)
    (hkε : D.profileAtOrigin.toReal / 2 ≤ D.k ε₀) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) (ε₀ / 2)) :
    lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
      r ^ (D.profileAtOrigin.toReal - d) ≤ q r := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hae : ∀ᵐ x ∂(volume : Measure (Rd d)), ‖x‖ < ε₀ / 2 →
      lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
        ‖x‖ ^ (D.profileAtOrigin.toReal - d) ≤ q ‖x‖ :=
    (origin_lower_bound_density hd D ha hc0 hctop μ hμ hε₀ hkε).2.1 (fun x => q ‖x‖) hμq
  by_contra hlt
  rw [not_le] at hlt
  have hcont : ContinuousAt (fun s : ℝ => lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
      s ^ (D.profileAtOrigin.toReal - d)) r :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hr.1.ne'))
  have hev : ∀ᶠ s in 𝓝 r, q r < lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
      s ^ (D.profileAtOrigin.toReal - d) := hcont.tendsto.eventually (lt_mem_nhds hlt)
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨r₁, hr₁, hr₁η, hr₁ε⟩ : ∃ r₁ : ℝ, r < r₁ ∧ r₁ ≤ r + η ∧ r₁ ≤ ε₀ / 2 :=
    ⟨min (r + η) (ε₀ / 2), lt_min (by linarith) hr.2, min_le_left _ _, min_le_right _ _⟩
  have hSopen : IsOpen {x : Rd d | r < ‖x‖ ∧ ‖x‖ < r₁} :=
    (isOpen_lt continuous_const continuous_norm).and (isOpen_lt continuous_norm continuous_const)
  have hSne : {x : Rd d | r < ‖x‖ ∧ ‖x‖ < r₁}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_norm_eq (d := d) (by omega) (r := (r + r₁) / 2) (by linarith [hr.1])
    refine ⟨x, ?_⟩
    rw [mem_setOf_eq, hx]
    constructor <;> linarith
  have hSpos : 0 < volume {x : Rd d | r < ‖x‖ ∧ ‖x‖ < r₁} := hSopen.measure_pos volume hSne
  have hSnull : volume {x : Rd d | r < ‖x‖ ∧ ‖x‖ < r₁} = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.mp hae)
    rw [mem_setOf_eq, Classical.not_imp, not_le]
    refine ⟨hx.2.trans_le hr₁ε, ?_⟩
    have h1 : q ‖x‖ ≤ q r := hq (mem_Ioi.mpr hr.1) (mem_Ioi.mpr (hr.1.trans hx.1)) hx.1.le
    have h2 : q r < lowerBoundConst d D.profileAtOrigin.toReal D.tailConst *
        ‖x‖ ^ (D.profileAtOrigin.toReal - d) := by
      refine hηb ?_
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
      have := hx.2
      linarith
    exact h1.trans_lt h2
  exact hSpos.ne' hSnull

/-! ## Clause (3): the two limits -/

/-- **A logarithmic order from two power bounds**: if `f(r) ≥ C r^{-L}` near `0+` and, for every
`ε > 0`, `f(r) ≤ C_ε r^{-(L+ε)}` near `0+`, then `log f(r)/log(1/r) → L` as `r ↓ 0`. Mathlib
types only. -/
theorem tendsto_log_div_log_inv {f : ℝ → ℝ} {L : ℝ}
    (hlow : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), C * r ^ (-L) ≤ f r)
    (hupp : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), f r ≤ C * r ^ (-(L + ε))) :
    Tendsto (fun r => Real.log (f r) / Real.log (1 / r)) (𝓝[>] 0) (𝓝 L) := by
  have hlog : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    simp_rw [one_div]; exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hlogpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < Real.log (1 / t) := fun t ht =>
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ht)
  have hratio : ∀ (K : ℝ), Tendsto (fun t : ℝ => K / Real.log (1 / t)) (𝓝[>] 0) (𝓝 0) :=
    fun K => tendsto_const_nhds.div_atTop hlog
  have hlogpow : ∀ (C a : ℝ), 0 < C → ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.log (C * t ^ (-a)) = Real.log C + a * Real.log (1 / t) := by
    intro C a hC t ht
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos ht.1 _).ne', Real.log_rpow ht.1, one_div,
      Real.log_inv]
    ring
  obtain ⟨C₁, hC₁, hlow'⟩ := hlow
  rw [tendsto_order]
  constructor
  · intro a' ha'
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), a' - L < Real.log C₁ / Real.log (1 / t) :=
      (hratio (Real.log C₁)).eventually (lt_mem_nhds (by linarith))
    filter_upwards [h2, hsmall, hlow'] with t h2t ht hft
    have hl := hlogpos t ht
    have hpos : 0 < C₁ * t ^ (-L) := mul_pos hC₁ (Real.rpow_pos_of_pos ht.1 _)
    have hlogP : Real.log C₁ + L * Real.log (1 / t) ≤ Real.log (f t) := by
      rw [← hlogpow C₁ L hC₁ t ht]
      exact Real.log_le_log hpos hft
    rw [lt_div_iff₀ hl]
    rw [lt_div_iff₀ hl] at h2t
    nlinarith
  · intro b hb
    obtain ⟨C, hC, hupp'⟩ := hupp ((b - L) / 2) (by linarith)
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Real.log C / Real.log (1 / t) < b - (L + (b - L) / 2) :=
      (hratio (Real.log C)).eventually (gt_mem_nhds (by linarith))
    filter_upwards [h2, hsmall, hlow', hupp'] with t h2t ht hft hfu
    have hl := hlogpos t ht
    have hfpos : 0 < f t := lt_of_lt_of_le (mul_pos hC₁ (Real.rpow_pos_of_pos ht.1 _)) hft
    have hlogP : Real.log (f t) ≤ Real.log C + (L + (b - L) / 2) * Real.log (1 / t) := by
      rw [← hlogpow C _ hC t ht]
      exact Real.log_le_log hfpos hfu
    rw [div_lt_iff₀ hl]
    rw [div_lt_iff₀ hl] at h2t
    nlinarith

/-- For `0 < c` and `ε > 0` there is a `β` with `0 < β < c` and `c - ε ≤ β`. -/
theorem exists_between_profile {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < c ∧ c - ε ≤ β :=
  ⟨max (c - ε) (c / 2), lt_of_lt_of_le (half_pos hc) (le_max_right _ _),
    max_lt (by linarith) (half_lt_self hc), le_max_left _ _⟩

/-- **`prop:origin-upper-bound-d`(3), the order of the density**: for `d ≥ 2`, a datum with
Gaussian coefficient `0` and `0 < c ≤ d`, every law `μ` of it and every `q` nonincreasing on
`(0,∞)` with `μ = q(|x|) dx`: `log q(|x|)/log(1/|x|) → d - c` as `x → 0`. Spends A3(iii), through
the lower bound. -/
theorem origin_density_log_order (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hμq : μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun x : Rd d => Real.log (q ‖x‖) / Real.log (1 / ‖x‖)) (𝓝[≠] 0)
      (𝓝 ((d : ℝ) - D.profileAtOrigin.toReal)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd
  obtain ⟨⟨ε₀, hε₀, hkε⟩, -⟩ := origin_lower_bound hd D ha hc hctop μ hμ
  have h1d : Tendsto (fun r : ℝ => Real.log (q r) / Real.log (1 / r)) (𝓝[>] 0)
      (𝓝 ((d : ℝ) - D.profileAtOrigin.toReal)) := by
    refine tendsto_log_div_log_inv
      ⟨lowerBoundConst d D.profileAtOrigin.toReal D.tailConst, lowerBoundConst_pos hd1 hc0, ?_⟩ ?_
    · filter_upwards [Ioo_mem_nhdsGT (half_pos hε₀.1)] with r hr
      rw [neg_sub]
      exact origin_density_lower hd D ha hc hctop μ hμ hε₀ hkε hq hμq hr
    · intro ε hε
      obtain ⟨β, hβ0, hβc, hβε⟩ := exists_between_profile hc0 hε
      have hβc' : ENNReal.ofReal β < D.profileAtOrigin :=
        (ENNReal.ofReal_lt_iff_lt_toReal hβ0.le hctop).mpr hβc
      obtain ⟨C', hC', -, -, hqb⟩ := origin_upper_bound hd1 D ha hc μ hμ hcd hβ0 hβc'
      have hCpos : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' /
          (volume (ball (0 : Rd d) 1)).toReal :=
        div_pos (by positivity) volume_unitBall_toReal_pos
      refine ⟨_, hCpos, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
      refine (hqb q hq hμq r hr.1).trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
      exact Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le (by linarith)
  exact h1d.comp tendsto_norm_nhdsNE_zero

/-- **`prop:origin-upper-bound-d`(3), the order of the mass of a ball**: for `d ≥ 2`, a datum with
Gaussian coefficient `0` and `0 < c ≤ d`, and every law `μ` of it:
`log μ{|x| < r}/log r → c` as `r ↓ 0`. No density is named. Spends A3(iii), through the lower
bound `origin_lower_bound_ball`. -/
theorem origin_ball_log_order (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    Tendsto (fun r : ℝ => Real.log (μ (ball 0 r)).toReal / Real.log r) (𝓝[>] 0)
      (𝓝 D.profileAtOrigin.toReal) := by
  have hd1 : 1 ≤ d := by omega
  haveI := hμ.1
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd
  obtain ⟨⟨ε₀, hε₀, hkε⟩, -⟩ := origin_lower_bound hd D ha hc hctop μ hμ
  have hc₁ := lowerBoundConst_pos (d := d) (Ck := D.tailConst) hd1 hc0
  have hA := (sphereArea_eq_toSphere hd1).2
  have h : Tendsto (fun r : ℝ => Real.log (μ (ball 0 r)).toReal / Real.log (1 / r)) (𝓝[>] 0)
      (𝓝 (-D.profileAtOrigin.toReal)) := by
    refine tendsto_log_div_log_inv
      ⟨lowerBoundConst d D.profileAtOrigin.toReal D.tailConst * sphereArea d /
        D.profileAtOrigin.toReal, by positivity, ?_⟩ ?_
    · filter_upwards [Ioo_mem_nhdsGT (half_pos hε₀.1)] with r hr
      rw [neg_neg]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mp
        (origin_lower_bound_ball hd D ha hc hctop μ hμ hε₀ hkε ⟨hr.1, hr.2.le⟩)
    · intro ε hε
      obtain ⟨β, hβ0, hβc, hβε⟩ := exists_between_profile hc0 hε
      have hβc' : ENNReal.ofReal β < D.profileAtOrigin :=
        (ENNReal.ofReal_lt_iff_lt_toReal hβ0.le hctop).mpr hβc
      obtain ⟨C', hC', -, hball, -⟩ := origin_upper_bound hd1 D ha hc μ hμ hcd hβ0 hβc'
      have hApos : 0 < (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' := by positivity
      refine ⟨_, hApos, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
      have h1 : (μ (ball 0 r)).toReal ≤ (2 * π) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β :=
        (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
          (mul_pos hApos (Real.rpow_pos_of_pos hr.1 β)).le).mp (hball r hr.1)
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hApos.le)
      exact Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le (by linarith)
  have h' := h.neg
  rw [neg_neg] at h'
  refine h'.congr fun r => ?_
  rw [one_div, Real.log_inv, div_neg, neg_neg]

/-! ## The bundle for `d ≥ 2` -/

/-- **`prop:origin-upper-bound-d`**, for `d ≥ 2`, in one statement: the law of a datum with
Gaussian coefficient `0` and `0 < c ≤ d` has a density `x ↦ q(|x|)` with `q ≥ 0` nonincreasing on
`(0,∞)`; for every `0 < β < c` there is `C` with `q(r) ≤ C r^{β-d}` for every `r > 0`; there are
`δ > 0` and `c₁ > 0` with `q(r) ≥ c₁ r^{c-d}` for every `0 < r < δ`; and
`log q(|x|)/log(1/|x|) → d - c` as `x → 0`. Spends A8, A2 and A3(iii): the existence of `q` is
`radial_monotone_law`, the lower bound `origin_lower_bound`. -/
theorem origin_density_order (hd : 2 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ)
    (hcd : D.profileAtOrigin ≤ d) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      (∀ β : ℝ, 0 < β → ENNReal.ofReal β < D.profileAtOrigin →
        ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → q r ≤ C * r ^ (β - d)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
        ∀ r ∈ Ioo (0 : ℝ) δ, c₁ * r ^ (D.profileAtOrigin.toReal - d) ≤ q r) ∧
      Tendsto (fun x : Rd d => Real.log (q ‖x‖) / Real.log (1 / ‖x‖)) (𝓝[≠] 0)
        (𝓝 ((d : ℝ) - D.profileAtOrigin.toReal)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hctop, hc0, -⟩ := D.profileAtOrigin_toReal_pos hc hcd
  obtain ⟨q, hq0, hq, hμq, hupper⟩ := origin_density_upper hd1 D ha hc μ hμ hcd
  obtain ⟨⟨ε₀, hε₀, hkε⟩, -⟩ := origin_lower_bound hd D ha hc hctop μ hμ
  exact ⟨q, hq0, hq, hμq, hupper,
    ⟨ε₀ / 2, half_pos hε₀.1, _, lowerBoundConst_pos hd1 hc0, fun r hr =>
      origin_density_lower hd D ha hc hctop μ hμ hε₀ hkε hq hμq hr⟩,
    origin_density_log_order hd D ha hc μ hμ hcd hq hμq⟩

end AffineHemigroup
