/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.DilationRatio
import AffineHemigroup.Subordination
import AffineHemigroup.MaternEndpointProfile

/-!
# `prop:tempered-step-cone`: profiles stable at the origin keep the stable cone

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:tempered-step-cone` (wave 2, group D, Q-0281),
clauses (1), (3) and (4); clause (2) is the split child `prop:tempered-moments`. Clause (1) reads the
dilation ratio of `k = r^{-α}j` and the cone of `prop:orbit-step-cone`(2); its increments spend
A3(iii) through `orbit_density_order_increment`. Clauses (3)(b) and (4) are one subordination of
the heat kernel, computed here: an inverse Gamma integral, the substitution `s = |x|²t`, the heat
kernel's cosine integral, Tonelli, and a Gamma (resp. Frullani) integral in the subordinator.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Tempering factors -/

/-- A tempering factor is at most its limit at `0+`. -/
theorem IsTemperingProfile.le_of_tendsto {j : ℝ → ℝ} (hj : IsTemperingProfile j) {L : ℝ}
    (hL : Tendsto j (𝓝[>] 0) (𝓝 L)) {r : ℝ} (hr : 0 < r) : j r ≤ L :=
  ge_of_tendsto hL (by
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hj.2.1 hs.1 hr hs.2.le)

/-- `r² · r^{-α}/r^d = r^{2-d-α}` and `r^{-α}/r^d = r^{-d-α}` for `r > 0`. -/
theorem rpow_neg_div_pow {r : ℝ} (hr : 0 < r) (α : ℝ) :
    r ^ (-α) / r ^ d = r ^ (-(d : ℝ) - α) := by
  rw [← Real.rpow_natCast, ← Real.rpow_sub hr]; ring_nf

/-- **`prop:tempered-step-cone`(1)**, the profile: `k(r) := r^{-α} j(r)` is a radial profile. -/
noncomputable def temperedProfile (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (j : ℝ → ℝ)
    (hj : IsTemperingProfile j) : RadialProfile d where
  k := fun r => r ^ (-α) * j r
  k_nonneg := fun r hr => mul_nonneg (Real.rpow_nonneg (le_of_lt hr) _) (hj.1 r hr)
  k_antitone := fun r hr s hs hrs =>
    mul_le_mul (Real.rpow_le_rpow_of_nonpos hr hrs (by linarith)) (hj.2.1 hr hs hrs) (hj.1 s hs)
      (Real.rpow_nonneg (le_of_lt hr) _)
  k_ne_zero := by
    obtain ⟨L, hL0, hL⟩ := hj.2.2
    obtain ⟨r, hr, hjr⟩ := (IsTemperingProfile.eventually_pos hL0 hL).exists
    exact ⟨r, hr, (mul_pos (Real.rpow_pos_of_pos hr _) hjr).ne'⟩
  integrable := by
    haveI : NeZero d := ⟨by omega⟩
    obtain ⟨L, hL0, hL⟩ := hj.2.2
    have hint := (integrable_stableConstBound (d := d) hα0 hα2).const_mul (2 * L)
    refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne (lintegral_mono fun x => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rcases (norm_nonneg x).lt_or_eq with hx | hx
    · set r := ‖x‖ with hrdef
      have hjr := hj.le_of_tendsto hL hx
      have hj0 := hj.1 r hx
      have hkr : r ^ (-α) * j r / r ^ d ≤ L * r ^ (-(d : ℝ) - α) := by
        rw [mul_div_right_comm, rpow_neg_div_pow hx, mul_comm]
        exact mul_le_mul_of_nonneg_right hjr (by positivity)
      rcases le_or_gt r 1 with h1 | h1
      · have hb : stableConstBound d α r = r ^ (2 - (d : ℝ) - α) / 2 := by
          simp only [stableConstBound, indicator_of_mem (show r ∈ Ioc 0 1 from ⟨hx, h1⟩),
            indicator_of_notMem (show r ∉ Ioi 1 from not_lt.2 h1), add_zero]
        rw [hb, min_eq_left (by nlinarith)]
        have h2 : r ^ 2 * r ^ (-(d : ℝ) - α) = r ^ (2 - (d : ℝ) - α) := by
          rw [← Real.rpow_two, ← Real.rpow_add hx]; ring_nf
        calc r ^ 2 * (r ^ (-α) * j r / r ^ d) ≤ r ^ 2 * (L * r ^ (-(d : ℝ) - α)) :=
              mul_le_mul_of_nonneg_left hkr (by positivity)
          _ = 2 * L * (r ^ (2 - (d : ℝ) - α) / 2) := by rw [← h2]; ring
      · have hb : stableConstBound d α r = 2 * r ^ (-(d : ℝ) - α) := by
          simp only [stableConstBound, indicator_of_mem (show r ∈ Ioi 1 from h1),
            indicator_of_notMem (show r ∉ Ioc 0 1 from fun h => not_le.2 h1 h.2), zero_add]
        rw [hb, min_eq_right (by nlinarith), one_mul]
        calc r ^ (-α) * j r / r ^ d ≤ L * r ^ (-(d : ℝ) - α) := hkr
          _ ≤ 2 * L * (2 * r ^ (-(d : ℝ) - α)) := by
              have : 0 ≤ L * r ^ (-(d : ℝ) - α) := by positivity
              nlinarith
    · rw [← hx]
      have : 0 ≤ stableConstBound d α 0 := by
        simp [stableConstBound]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, min_eq_left zero_le_one,
        zero_mul]
      positivity

/-- **`prop:tempered-step-cone`(1)**: `k(r) = r^{-α}j` satisfies the hypotheses of
`prop:orbit-step-cone`. -/
theorem tempered_profile_exists (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (j : ℝ → ℝ)
    (hj : IsTemperingProfile j) :
    ∃ K : RadialProfile d, ∀ r : ℝ, 0 < r → K.k r = r ^ (-α) * j r :=
  ⟨temperedProfile hd hα0 hα2 j hj, fun _ _ => rfl⟩

/-- **A profile with ratio `λ^α` has the stable cone**: if `R(λ) = λ^α` for `λ ≥ 1`, then
`n_Σ ≤ n_{Σ'}` off the origin if and only if `Σ ≼_α Σ'` (as in `orbit_density_order_stable`). -/
theorem orbit_density_order_iff_stableLE (hd : 1 ≤ d) (K : RadialProfile d) {α : ℝ}
    (hα0 : 0 < α) (hR : ∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ α) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) :
    (∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔ stableLE α S S' := by
  haveI : NeZero d := ⟨by omega⟩
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hl := lamMin_pos hM
  rw [(orbit_density_order_iff hd K hS hS').1]
  constructor
  · rintro ⟨hl1, hdet⟩
    refine ⟨hS, hS', hM, ?_⟩
    rwa [hR _ (Real.one_le_sqrt.2 hl1), pow_mul_sqrt_rpow_sq hl] at hdet
  · rintro ⟨-, -, -, hdet⟩
    have hl1 := one_le_lamMin_of_stable hα0 hM hdet
    refine ⟨hl1, ?_⟩
    rwa [hR _ (Real.one_le_sqrt.2 hl1), pow_mul_sqrt_rpow_sq hl]

/-- **`prop:tempered-step-cone`(1)**, the stable cone: the dilation ratio of `k = r^{-α}j` is
`λ^α`; the densities of the orbit are ordered exactly when condition (c) of `prop:stable-step-cone`
holds; and then `μ_{Σ'} = μ_Σ * ρ` with `ρ` an infinitely divisible probability measure. -/
theorem tempered_step_cone (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) (j : ℝ → ℝ)
    (hj : IsTemperingProfile j) (K : RadialProfile d)
    (hK : ∀ r : ℝ, 0 < r → K.k r = r ^ (-α) * j r) :
    (∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ α) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔ stableLE α S S') ∧
        (stableLE α S S' → ∀ μI : Measure (Rd d), IsProfileLaw K μI →
          ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
            affineOrbit μI S' = affineOrbit μI S ∗ ρ) := by
  obtain ⟨L, hL0, hL⟩ := hj.2.2
  have hR : ∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ α := by
    intro lam hlam
    have hl0 : 0 < lam := by linarith
    refine le_antisymm ?_ (le_dilRatio K fun r hr hk => ?_)
    · -- the quotients tend to `λ^α` at `0+`
      have hdiv : Tendsto (fun r : ℝ => r / lam) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := (continuous_id.div_const lam).tendsto 0
          simp only [id, zero_div] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact div_pos hr hl0
      have hq : Tendsto (fun r => lam ^ α * (j (r / lam) / j r)) (𝓝[>] 0)
          (𝓝 (lam ^ α * (L / L))) := ((hL.comp hdiv).div hL hL0.ne').const_mul _
      rw [div_self hL0.ne', mul_one] at hq
      refine ge_of_tendsto hq ?_
      filter_upwards [IsTemperingProfile.eventually_pos hL0 hL] with r ⟨hr, hjr⟩
      have hkr : 0 < K.k r := by rw [hK r hr]; exact mul_pos (Real.rpow_pos_of_pos hr _) hjr
      have h1 := dilRatio_le hd K hlam hr hkr
      rw [hK r hr, hK _ (div_pos hr hl0)] at h1
      have heq : (r / lam) ^ (-α) = lam ^ α * r ^ (-α) := by
        rw [Real.div_rpow hr.le hl0.le, Real.rpow_neg hl0.le, div_inv_eq_mul, mul_comm]
      rw [heq] at h1
      have hra : 0 < r ^ (-α) := Real.rpow_pos_of_pos hr _
      rw [← mul_div_assoc, le_div_iff₀ hjr]
      have h2 : dilRatio K.k lam * j r * r ^ (-α) ≤ lam ^ α * j (r / lam) * r ^ (-α) := by
        linarith
      exact le_of_mul_le_mul_right h2 hra
    · rw [hK r hr] at hk ⊢
      rw [hK _ (div_pos hr hl0)]
      have hra : 0 < r ^ (-α) := Real.rpow_pos_of_pos hr _
      have hjr : 0 < j r := pos_of_mul_pos_right hk hra.le
      have heq : (r / lam) ^ (-α) = lam ^ α * r ^ (-α) := by
        rw [Real.div_rpow hr.le hl0.le, Real.rpow_neg hl0.le, div_inv_eq_mul, mul_comm]
      rw [heq]
      have hjj : j r ≤ j (r / lam) := hj.2.1 (div_pos hr hl0) hr (div_le_self hr.le hlam)
      have hla : 0 < lam ^ α := Real.rpow_pos_of_pos hl0 _
      calc lam ^ α * (r ^ (-α) * j r) = lam ^ α * r ^ (-α) * j r := by ring
        _ ≤ lam ^ α * r ^ (-α) * j (r / lam) :=
            mul_le_mul_of_nonneg_left hjj (by positivity)
  refine ⟨hR, fun S S' hS hS' => ⟨orbit_density_order_iff_stableLE hd K hα0 hR hS hS',
    fun h μI hμI => ?_⟩⟩
  obtain ⟨ρ, hρ, hid, -, heq⟩ := orbit_density_order_increment hd K hS hS'
    ((orbit_density_order_iff_stableLE hd K hα0 hR hS hS').2 h) μI hμI
  exact ⟨ρ, hρ, hid, heq⟩

/-- **`prop:tempered-step-cone`(3)(a)**: for `ℓ > 0`, `j(r) = e^{-r/ℓ}` satisfies the hypotheses,
and those of (2) with `β = 1/ℓ`. -/
theorem tempered_exp_example {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsTemperingProfile (fun r => Real.exp (-r / ℓ)) ∧
      ∫⁻ r in Ioi (1 : ℝ),
        ENNReal.ofReal (Real.exp (ℓ⁻¹ * r) * r ^ (-1 - α) * Real.exp (-r / ℓ)) ≠ ⊤ := by
  refine ⟨⟨fun r _ => (Real.exp_pos _).le, fun r _ s _ hrs => ?_, 1, one_pos, ?_⟩, ?_⟩
  · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hℓ.le)
  · have h : Continuous fun r : ℝ => Real.exp (-r / ℓ) := by fun_prop
    have := h.tendsto 0
    simp only [neg_zero, zero_div, Real.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hint : IntegrableOn (fun r : ℝ => r ^ (-1 - α)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne
      (setLIntegral_mono' measurableSet_Ioi fun r _ => ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    field_simp
    simp

/-! ## Clauses (3)(b) and (4): the subordinated heat kernel -/

/-- **`prop:tempered-step-cone`(3)(b)**: `j(r) = (α/2)/Γ(1-α/2) ∫₀^∞ (4πt)^{-d/2} t^{-1-α/2}
e^{-1/(4t) - r²t} dt` satisfies the hypotheses, and those of (2) for every `0 < β < 1`; the law of
`k = r^{-α}j` has `μ̂_I(ω) = exp[-((1+|ω|²)^{α/2} - 1)]`, its orbit
`μ̂_Σ(ω) = exp[-((1+⟨ω,Σω⟩)^{α/2} - 1)]`, which at `Σ = ℓ²I` is
`exp[-((1+ℓ²|ω|²)^{α/2} - 1)]`. -/
theorem tempered_subordinated_example (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    let j : ℝ → ℝ := fun r => (α / 2) / Real.Gamma (1 - α / 2) *
      ∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - α / 2) *
        Real.exp (-1 / (4 * t) - r ^ 2 * t)
    IsTemperingProfile j ∧
      (∀ β : ℝ, 0 < β → β < 1 →
        ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (β * r) * r ^ (-1 - α) * j r) ≠ ⊤) ∧
      ∀ K : RadialProfile d, (∀ r : ℝ, 0 < r → K.k r = r ^ (-α) * j r) →
        ∀ μI : Measure (Rd d), IsProfileLaw K μI →
          (∀ ω : Rd d, charFun μI ω =
            ((Real.exp (-((1 + ‖ω‖ ^ 2) ^ (α / 2) - 1)) : ℝ) : ℂ)) ∧
          (∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (affineOrbit μI S) ω =
            ((Real.exp (-((1 + quad S ω) ^ (α / 2) - 1)) : ℝ) : ℂ)) ∧
          ∀ ℓ : ℝ, 0 < ℓ → ∀ ω : Rd d, charFun (affineOrbit μI (ℓ ^ 2 • (1 : Mat d))) ω =
            ((Real.exp (-((1 + ℓ ^ 2 * ‖ω‖ ^ 2) ^ (α / 2) - 1)) : ℝ) : ℂ) := by
  intro j
  have ha0 : 0 < α / 2 := by linarith
  have ha1 : α / 2 < 1 := by linarith
  have hΓ : 0 < Real.Gamma (1 - α / 2) := Real.Gamma_pos_of_pos (by linarith)
  set c := (α / 2) / Real.Gamma (1 - α / 2) with hcdef
  have hc0 : 0 < c := div_pos ha0 hΓ
  have hj : ∀ r, j r = c * subProfile d (α / 2) r := fun r => rfl
  have hF0 := subProfile_zero_pos hd ha0.le (d := d)
  refine ⟨⟨fun r _ => by rw [hj]; exact mul_nonneg hc0.le (subProfile_nonneg _ _),
    fun r hr s hs hrs => ?_, c * subProfile d (α / 2) 0, mul_pos hc0 hF0, ?_⟩, fun β hβ0 hβ1 => ?_,
    fun K hK μI hμI => ?_⟩
  · rw [hj, hj]
    exact mul_le_mul_of_nonneg_left (subProfile_antitone hd ha0.le (mem_Ici.2 (le_of_lt hr))
      (mem_Ici.2 (le_of_lt hs)) hrs) hc0.le
  · have h : Tendsto (fun r => c * subProfile d (α / 2) r) (𝓝[>] 0)
        (𝓝 (c * subProfile d (α / 2) 0)) :=
      ((continuous_const.mul (continuous_subProfile hd ha0.le (d := d))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact h
  · -- the exponential moments: `j(r) ≤ c C_η e^{-(1-η)r}`, `η = (1-β)/2`
    set η := (1 - β) / 2 with hη
    have hη0 : 0 < η := by linarith
    have hη1 : η < 1 := by linarith
    set C := ∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t ^ (-1 - α / 2) *
        Real.exp (-η / (4 * t)) with hC
    have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have : (0 : ℝ) < t := ht
      positivity
    have hint : IntegrableOn (fun r : ℝ => c * C * Real.exp (-((1 - β) / 2) * r)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi 1 (by linarith)).const_mul _
    refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne
      (setLIntegral_mono' measurableSet_Ioi fun r hr => ENNReal.ofReal_le_ofReal ?_)
    have hr1 : (1 : ℝ) < r := hr
    have hr0 : (0 : ℝ) < r := by linarith
    have hpow : r ^ (-1 - α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1.le (by linarith)
    have hF := subProfile_le_exp hd ha0.le hη0 hη1 hr0.le (d := d)
    rw [hj]
    calc Real.exp (β * r) * r ^ (-1 - α) * (c * subProfile d (α / 2) r)
        ≤ Real.exp (β * r) * 1 * (c * (C * Real.exp (-(1 - η) * r))) := by
          gcongr
          · exact mul_nonneg hc0.le (subProfile_nonneg _ _)
      _ = c * C * (Real.exp (β * r) * Real.exp (-(1 - η) * r)) := by ring
      _ = c * C * Real.exp (-((1 - β) / 2) * r) := by
          rw [← Real.exp_add]; congr 2; rw [hη]; ring
  · -- the transforms
    haveI := hμI.1
    have hK2 : ∀ r : ℝ, 0 < r → K.k r = r ^ (-(2 * (α / 2))) * (c * subProfile d (α / 2) r) :=
      fun r hr => by rw [hK r hr, hj]; ring_nf
    have hexp : ∀ ω : Rd d, K.exponent ω = (1 + ‖ω‖ ^ 2) ^ (α / 2) - 1 := by
      intro ω
      have hu : 0 ≤ ‖ω‖ ^ 2 := sq_nonneg _
      have hone : 0 ≤ (1 + ‖ω‖ ^ 2) ^ (α / 2) - 1 := by
        have := Real.one_le_rpow (show (1 : ℝ) ≤ 1 + ‖ω‖ ^ 2 by linarith) ha0.le
        linarith
      rw [RadialProfile.exponent, exponentL_of_subProfile hd K ha0.le hc0.le hK2 ω,
        lintegral_gamma_subordinator ha0 ha1 hu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le,
        ENNReal.toReal_ofReal (mul_nonneg (div_nonneg hΓ.le ha0.le) hone)]
      have hca : c * (Real.Gamma (1 - α / 2) / (α / 2)) = 1 := by
        rw [hcdef, div_mul_div_comm, mul_comm (α / 2), div_self (mul_ne_zero hΓ.ne' ha0.ne')]
      rw [← mul_assoc, hca, one_mul]
    have hμ : ∀ ω : Rd d, charFun μI ω =
        ((Real.exp (-((1 + ‖ω‖ ^ 2) ^ (α / 2) - 1)) : ℝ) : ℂ) := fun ω => by
      rw [hμI.2, hexp]
    have horb : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (affineOrbit μI S) ω =
        ((Real.exp (-((1 + quad S ω) ^ (α / 2) - 1)) : ℝ) : ℂ) := fun S hS ω => by
      rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hS), msqrt_transpose, hμ,
        norm_sq_lin_msqrt hS.posSemidef]
    refine ⟨hμ, horb, fun ℓ hℓ ω => ?_⟩
    rw [horb _ (Matrix.PosDef.one.smul (by positivity)), quad_smul, quad_one]

/-- **`prop:tempered-step-cone`(4)**, the Matérn is the endpoint `α = 0`: for `γ > 0`,
`k₀(r) = γ ∫₀^∞ (4πt)^{-d/2} t⁻¹ e^{-1/(4t) - r²t} dt` satisfies the hypotheses of
`prop:orbit-step-cone` with `k₀(0+) = γ π^{-d/2} Γ(d/2)`; its law is the Matérn law of index `γ`;
its dilation ratio is `R ≡ 1` and its ordered-density cone is the rays. -/
theorem matern_endpoint (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) :
    let k₀ : ℝ → ℝ := fun r => γ *
      ∫ t in Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * t⁻¹ * Real.exp (-1 / (4 * t) - r ^ 2 * t)
    (∃ K : RadialProfile d, ∀ r : ℝ, 0 < r → K.k r = k₀ r) ∧
      Tendsto k₀ (𝓝[>] 0) (𝓝 (γ * Real.pi ^ (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2))) ∧
      ∀ K : RadialProfile d, (∀ r : ℝ, 0 < r → K.k r = k₀ r) →
        (∀ μI : Measure (Rd d), IsProfileLaw K μI → IsMaternLaw γ μI) ∧
        (∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = 1) ∧
        ∀ S S' : Mat d, S.PosDef → S'.PosDef →
          ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔
            ∃ lam : ℝ, 1 ≤ lam ∧ S' = lam ^ 2 • S) := by
  intro k₀
  have hk : ∀ r, k₀ r = γ * subProfile d 0 r := by
    intro r
    show γ * _ = γ * _
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp [subIntegrand, Real.rpow_neg_one]
  have hval : γ * subProfile d 0 0 = γ * Real.pi ^ (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    rw [subProfile_zero hd le_rfl, zero_add, Real.mul_rpow (by norm_num) Real.pi_pos.le]
    have h4 : (4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf; exact Real.rpow_zero _
    calc γ * ((4 : ℝ) ^ (-(d : ℝ) / 2) * Real.pi ^ (-(d : ℝ) / 2) *
          ((4 : ℝ) ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)))
        = γ * ((4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2)) * Real.pi ^ (-(d : ℝ) / 2) *
            Real.Gamma ((d : ℝ) / 2) := by ring
      _ = _ := by rw [h4, mul_one]
  have hlim : Tendsto k₀ (𝓝[>] 0) (𝓝 (γ * subProfile d 0 0)) := by
    have h : Tendsto (fun r => γ * subProfile d 0 r) (𝓝[>] 0) (𝓝 (γ * subProfile d 0 0)) :=
      ((continuous_const.mul (continuous_subProfile hd le_rfl (d := d))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact h.congr fun r => (hk r).symm
  refine ⟨⟨maternEndpointProfile hd γ hγ, fun r _ => (hk r).symm⟩, hval ▸ hlim, fun K hK => ?_⟩
  have hKlim : Tendsto K.k (𝓝[>] 0) (𝓝 (γ * subProfile d 0 0)) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun r hr => (hK r hr).symm)
  obtain ⟨hR, hcone⟩ := orbit_density_order_bounded hd K _ hKlim
  refine ⟨fun μI hμI => ⟨hμI.1, fun ω => ?_⟩, hR, hcone⟩
  have hK2 : ∀ r : ℝ, 0 < r → K.k r = r ^ (-(2 * (0 : ℝ))) * (γ * subProfile d 0 r) :=
    fun r hr => by rw [hK r hr, hk]; simp
  have hu : 0 ≤ ‖ω‖ ^ 2 := sq_nonneg _
  have hlog : 0 ≤ Real.log (1 + ‖ω‖ ^ 2) := Real.log_nonneg (by linarith)
  rw [hμI.2, RadialProfile.exponent, exponentL_of_subProfile hd K le_rfl hγ.le hK2 ω,
    lintegral_frullani_subordinator hu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ.le,
    ENNReal.toReal_ofReal hlog, exp_neg_mul_log_one_add hu]

end AffineHemigroup
