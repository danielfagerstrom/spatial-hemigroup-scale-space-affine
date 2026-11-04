/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.LogOrbitRays
import AffineHemigroup.OrbitStepCone
import AffineHemigroup.MaternOrbit
import AffineHemigroup.ExponentLog
import AffineHemigroup.RadialProfileDatum

/-!
# `prop:matern-steps` and `prop:bounded-profile-rays`: two orbits whose positive steps are the rays

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:matern-steps` (the collation of
`prop:log-orbit-rays` and `prop:affine-orbits`(4)) and `prop:bounded-profile-rays` (the join of
`prop:orbit-step-cone`, `prop:log-orbit-rays` and `lem:isotropic-exponent-log`(2)). Wave 2,
group C, Q-0281. The sign of the ray is read off `|ρ̂| ≤ 1`.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real Filter Complex
open scoped MatrixOrder RealInnerProductSpace ENNReal Topology

variable {d : ℕ}

/-- **The sign of a ray step**: if `μ_{cΣ} = μ_Σ * ρ` for a finite `ρ` and the orbit's exponent has
`g(cu) - g(u) → κ log c` with `κ > 0`, then `c ≥ 1` (the increment's transform is at most `1`). -/
theorem one_le_of_ray_increment {g : ℝ → ℝ} {μI : Measure (Rd d)} [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c)
    (hlog : Tendsto (fun u => g (c * u) - g u) atTop (𝓝 (κ * Real.log c)))
    (hd : 1 ≤ d) {S : Mat d} (hS : S.PosDef) {ρ : Measure (Rd d)} [IsFiniteMeasure ρ]
    (h : affineOrbit μI (c • S) = affineOrbit μI S ∗ ρ) : 1 ≤ c := by
  haveI : NeZero d := ⟨by omega⟩
  have hcS : (c • S).PosDef := hS.smul hc
  have hρ := charFun_orbit_increment hμI hS hcS h
  -- `ρ` is a probability measure
  haveI : IsProbabilityMeasure ρ := by
    have h0 := hρ 0
    rw [charFun_zero, quad_eq_dotProduct, quad_eq_dotProduct] at h0
    simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, sub_self, neg_zero,
      Real.exp_zero, Complex.ofReal_one] at h0
    have h1 : ρ.real univ = 1 := by exact_mod_cast h0
    rw [Measure.real, ENNReal.toReal_eq_one_iff] at h1
    exact ⟨h1⟩
  by_contra hlt
  push Not at hlt
  have hneg : κ * Real.log c < 0 := mul_neg_of_pos_of_neg hκ (Real.log_neg hc hlt)
  -- along `ω = t e`, `u = t² ⟨e,Σe⟩ → ∞`, the transform exceeds `1`
  set e : Rd d := ebasis (0 : Fin d) with he
  have he0 : e ≠ 0 := by
    intro h0
    have := congrArg (fun y : Rd d => y 0) h0
    simp [he, ebasis] at this
  have hq := quad_pos hS he0
  obtain ⟨U, hU⟩ := eventually_atTop.1 (hlog.eventually
    (gt_mem_nhds (by linarith : κ * Real.log c < κ * Real.log c / 2)))
  set t := Real.sqrt (max U 0 / quad S e) + 1 with ht
  have ht0 : 0 < t := by positivity
  have hu : U ≤ t ^ 2 * quad S e := by
    have h2 : max U 0 / quad S e < t ^ 2 := by
      have hs := Real.sq_sqrt (show 0 ≤ max U 0 / quad S e by positivity)
      nlinarith [Real.sqrt_nonneg (max U 0 / quad S e)]
    rw [div_lt_iff₀ hq] at h2
    linarith [le_max_left U 0]
  have hval := hU _ hu
  have hρt := hρ (t • e)
  rw [quad_smul_vec, quad_smul_vec, quad_smul, mul_left_comm] at hρt
  have hnorm := norm_charFun_le_one (μ := ρ) (t • e)
  rw [hρt, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff] at hnorm
  linarith

/-! ## `prop:matern-steps` -/

/-- The Matérn law's transform in the form `e^{-g(|ω|²)}`, `g(u) = γ log(1 + u)`. -/
theorem IsMaternLaw.charFun_exp {γ : ℝ} {μI : Measure (Rd d)} (hμI : IsMaternLaw γ μI)
    (ω : Rd d) :
    charFun μI ω = ((Real.exp (-(γ * Real.log (1 + ‖ω‖ ^ 2))) : ℝ) : ℂ) := by
  rw [hμI.2, exp_neg_mul_log_one_add (sq_nonneg _)]

/-- `γ log((1 + cu)/(1 + u)) → γ log c`. -/
theorem tendsto_matern_log {γ c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => γ * Real.log (1 + c * u) - γ * Real.log (1 + u)) atTop
      (𝓝 (γ * Real.log c)) := by
  have hq : Tendsto (fun u : ℝ => (1 + c * u) / (1 + u)) atTop (𝓝 c) := by
    have h1 : Tendsto (fun u : ℝ => (u⁻¹ + c) / (u⁻¹ + 1)) atTop (𝓝 ((0 + c) / (0 + 1))) :=
      ((tendsto_inv_atTop_zero.add tendsto_const_nhds).div
        (tendsto_inv_atTop_zero.add tendsto_const_nhds) (by norm_num))
    rw [zero_add, zero_add, div_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    field_simp
  have hlogc := ((Real.continuousAt_log hc.ne').tendsto.comp hq).const_mul γ
  refine hlogc.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  simp only [Function.comp_apply]
  rw [Real.log_div (by positivity) (by positivity)]
  ring

/-- **`prop:matern-steps`**: for the Matérn orbit of index `γ > 0` and `Σ ≠ Σ'` in `PD(d)`, a
positive finite `ρ` with `μ_{Σ'} = μ_Σ * ρ` exists if and only if `Σ' = λ²Σ` for some `λ > 1`; and
then `ρ` is unique, the probability measure `(Σ^{1/2})_*ν_λ`. -/
theorem matern_steps (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (μI : Measure (Rd d))
    (hμI : IsMaternLaw γ μI) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hne : S' ≠ S) :
    ((∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ affineOrbit μI S' = affineOrbit μI S ∗ ρ) ↔
        ∃ lam : ℝ, 1 < lam ∧ S' = lam ^ 2 • S) ∧
      ∀ lam : ℝ, 1 < lam → S' = lam ^ 2 • S →
        IsProbabilityMeasure (push (msqrt S) (maternRayLaw d γ lam)) ∧
        ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
          (affineOrbit μI S' = affineOrbit μI S ∗ ρ ↔ ρ = push (msqrt S) (maternRayLaw d γ lam)) := by
  haveI := hμI.1
  set g : ℝ → ℝ := fun u => γ * Real.log (1 + u) with hg
  have hμg : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) :=
    hμI.charFun_exp
  have horb := matern_orbit hd γ hγ
  -- the ray identity for `(Σ^{1/2})_*ν_λ`
  have hray : ∀ lam : ℝ, 1 < lam →
      IsProbabilityMeasure (push (msqrt S) (maternRayLaw d γ lam)) ∧
      affineOrbit μI (lam ^ 2 • S) = affineOrbit μI S ∗ push (msqrt S) (maternRayLaw d γ lam) := by
    intro lam hlam
    obtain ⟨-, hprob, hid⟩ := horb.2.2.2.2.2.2.2.2 lam hlam
    haveI := hprob
    refine ⟨inferInstance, ?_⟩
    have hl2 : (lam ^ 2 • S).PosDef := hS.smul (by positivity)
    haveI : IsProbabilityMeasure (affineOrbit μI (lam ^ 2 • S)) := by
      unfold affineOrbit; infer_instance
    haveI : IsProbabilityMeasure (affineOrbit μI S) := by unfold affineOrbit; infer_instance
    refine eq_of_charFun_eq fun ω => ?_
    have hT : ∀ T : Mat d, T.PosDef → charFun (affineOrbit μI T) ω =
        ((Real.exp (-g (quad T ω)) : ℝ) : ℂ) := fun T hT => by
      rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hT), msqrt_transpose, hμg,
        norm_sq_lin_msqrt hT.posSemidef]
    rw [charFun_conv, hT _ hl2, hT _ hS, charFun_push _ (msqrt_mem_glSet hS), msqrt_transpose,
      quad_smul]
    have := hid (lin (msqrt S) ω)
    rw [norm_sq_lin_msqrt hS.posSemidef] at this
    exact this
  have hcancel : ∀ lam : ℝ, 1 < lam → S' = lam ^ 2 • S → ∀ ρ : Measure (Rd d),
      IsFiniteMeasure ρ →
      (affineOrbit μI S' = affineOrbit μI S ∗ ρ ↔ ρ = push (msqrt S) (maternRayLaw d γ lam)) := by
    intro lam hlam hSS ρ hρ
    obtain ⟨hprob, hid⟩ := hray lam hlam
    haveI : IsProbabilityMeasure (affineOrbit μI S) := by unfold affineOrbit; infer_instance
    constructor
    · intro h
      refine conv_left_cancel_finite (μ := affineOrbit μI S) (fun ω => ?_) ?_
      · rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hS), hμg]
        exact_mod_cast (Real.exp_pos _).ne'
      · rw [← h, hSS, hid]
    · rintro rfl
      rw [hSS]; exact hid
  refine ⟨⟨fun ⟨ρ, hρ, h⟩ => ?_, fun ⟨lam, hlam, hSS⟩ =>
    ⟨push (msqrt S) (maternRayLaw d γ lam), by haveI := (hray lam hlam).1; infer_instance,
      by rw [hSS]; exact (hray lam hlam).2⟩⟩,
    fun lam hlam hSS => ⟨(hray lam hlam).1, hcancel lam hlam hSS⟩⟩
  -- necessity: a ray, by `prop:log-orbit-rays`, and `c > 1`
  obtain ⟨c, hc, hSS⟩ := matern_log_orbit_rays hd γ hγ μI hμI S S' hS hS' ρ hρ h
  have hc1 : 1 ≤ c := by
    rw [hSS] at h
    exact one_le_of_ray_increment hμg hγ hc (tendsto_matern_log hc) hd hS h
  have hc1' : 1 < c := by
    rcases hc1.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (by rw [hSS, ← h1, one_smul]) hne
  refine ⟨Real.sqrt c, Real.lt_sqrt (by norm_num) |>.2 (by simpa using hc1'), ?_⟩
  rw [Real.sq_sqrt hc.le, hSS]

/-! ## `prop:bounded-profile-rays`

The origin datum of a radial profile (`RadialProfile.toOriginDatum`, with its exponent and its
profile at the origin) is in `AffineHemigroup.RadialProfileDatum` since Q-0452. -/

/-- **`prop:bounded-profile-rays`**: for a profile with `k(0+)` finite and a unit vector `e`,
`g(u) = ψ_I(√u e)` satisfies the hypotheses of `prop:affine-orbits` and of `prop:log-orbit-rays` with
`κ = ½|S^{d-1}|k(0+) > 0`; and for `Σ, Σ' ∈ PD(d)` the following are equivalent: (1) a positive
finite increment; (2) `n_Σ ≤ n_{Σ'}` everywhere; (3) `Σ' = cΣ` with `c ≥ 1`. -/
theorem bounded_profile_rays (hd : 1 ≤ d) (K : RadialProfile d) (L : ℝ)
    (hL : Tendsto K.k (𝓝[>] 0) (𝓝 L)) (μI : Measure (Rd d)) (hμI : IsProfileLaw K μI)
    (e : Rd d) (he : ‖e‖ = 1) :
    let g : ℝ → ℝ := fun u => K.exponent (Real.sqrt u • e)
    ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      0 < sphereArea d * L / 2 ∧
      (∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop
        (𝓝 (sphereArea d * L / 2 * Real.log c))) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        List.TFAE
          [∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ affineOrbit μI S' = affineOrbit μI S ∗ ρ,
            ∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x,
            ∃ c : ℝ, 1 ≤ c ∧ S' = c • S] := by
  intro g
  haveI := hμI.1
  set D := K.toOriginDatum hd with hD
  have hA := (sphereArea_eq_toSphere hd).2
  -- `L > 0`
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  have hLpos : 0 < L := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), K.k r0 ≤ K.k r := by
      filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
      exact K.k_antitone hr.1 hr0 hr.2.le
    exact lt_of_lt_of_le hk0 (ge_of_tendsto hL hev)
  have hprof := K.toOriginDatum_profileAtOrigin hd hL
  have hprofne : D.profileAtOrigin ≠ ⊤ := by rw [hD, hprof]; exact ENNReal.ofReal_ne_top
  have hprofval : D.profileAtOrigin.toReal = sphereArea d * L := by
    rw [hD, hprof, ENNReal.toReal_ofReal (by positivity)]
  have hexp : ∀ ξ, K.exponent ξ = D.exponent ξ := fun ξ => (K.toOriginDatum_exponent hd ξ).symm
  -- the exponent is radial
  have hrad : ∀ ω : Rd d, K.exponent ω = g (‖ω‖ ^ 2) := by
    intro ω
    simp only [g]
    rw [Real.sqrt_sq (norm_nonneg _), hexp, hexp]
    exact D.exponent_eq_of_norm_eq (by rw [norm_smul, he, mul_one, norm_norm])
  have hchar : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) := fun ω => by
    rw [hμI.2, hrad]
  have hκ : 0 < sphereArea d * L / 2 := by positivity
  have hlog : ∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop
      (𝓝 (sphereArea d * L / 2 * Real.log c)) := by
    intro c hc
    have h := (isotropic_exponent_log_limit hd D rfl hprofne c hc).2 e he
    rw [hprofval] at h
    refine h.congr fun u => ?_
    simp only [g, hexp]
  have hcont : ContinuousOn g (Ici 0) := by
    -- continuity through `-log Re μ̂_I`
    have hg : ∀ u : ℝ, g u = -Real.log (charFun μI (Real.sqrt u • e)).re := by
      intro u
      rw [hμI.2, Complex.ofReal_re, Real.log_exp, neg_neg]
    have hpos : ∀ u : ℝ, 0 < (charFun μI (Real.sqrt u • e)).re := fun u => by
      rw [hμI.2, Complex.ofReal_re]; exact Real.exp_pos _
    intro u _
    have hc : ContinuousAt (fun u : ℝ => (charFun μI (Real.sqrt u • e)).re) u :=
      (Complex.continuous_re.comp (continuous_charFun.comp
        (Real.continuous_sqrt.smul continuous_const))).continuousAt
    have := (hc.log (hpos u).ne').neg
    exact (this.congr_of_eventuallyEq (Eventually.of_forall fun v => hg v)).continuousWithinAt
  have hg0 : g 0 = 0 := by
    simp only [g, Real.sqrt_zero, zero_smul, RadialProfile.exponent, RadialProfile.exponentL]
    simp
  refine ⟨hcont, fun u _ => ENNReal.toReal_nonneg, hg0, hchar, hκ, hlog, fun S S' hS hS' => ?_⟩
  tfae_have 1 → 3 := by
    rintro ⟨ρ, hρ, h⟩
    obtain ⟨c, hc, hSS⟩ := log_orbit_rays hd g hcont (fun u _ => ENNReal.toReal_nonneg)
      hg0 μI hchar _ hκ hlog S S' hS hS' ρ hρ h
    refine ⟨c, ?_, hSS⟩
    rw [hSS] at h
    exact one_le_of_ray_increment hchar hκ hc (hlog c hc) hd hS h
  tfae_have 3 → 2 := by
    rintro ⟨c, hc, rfl⟩
    have := (orbit_density_order_props hd K).2.2.1 S hS (Real.sqrt c) (Real.one_le_sqrt.2 hc)
    rw [Real.sq_sqrt (by linarith)] at this
    exact this.2.2
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨ρ, hprob, -, -, hρ⟩ := orbit_density_order_increment hd K hS hS' h μI hμI
    exact ⟨ρ, inferInstance, hρ⟩
  tfae_finish

end AffineHemigroup
