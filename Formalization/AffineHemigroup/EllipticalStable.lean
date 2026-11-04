/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.FiltrationStrict
import AffineHemigroup.RadialMonotone
import AffineHemigroup.StableTail
import AffineHemigroup.StableExponent
import AffineHemigroup.KernelsFromOrigin

/-!
# `lem:elliptical-stable` and `prop:stable-step-cone`: the stable laws and the stable step cone

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:elliptical-stable` (clause (2) and the
orbit; the arithmetic is `lem:elliptical-stable-density`, proved in wave 1) and
`prop:stable-step-cone` (clause (1) and the increments of (2); the order is `lem:stable-step-order`,
proved in wave 1). Wave 2, group C, Q-0281. Each spends ledger A3(iii) where its node says, through
one construction: **the symmetric triplet of a density** (`densTriplet`), `(0, n(x)dx, 0)` for an
even density `n` with `∫ (|x|² ∧ 1) n < ∞`, whose exponent is `-∫ (1 - cos⟨z,x⟩) n(x) dx`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The symmetric triplet of a density -/

/-- **The triplet `(0, n(x)dx, 0)`** of a measurable density `n` on `ℝ^d ∖ {0}` with
`∫ (|x|² ∧ 1) n(x) dx < ∞` (the negative part of `n`, if any, is cut off by `ofReal`). -/
noncomputable def densTriplet (n : Rd d → ℝ) (hn : Measurable n)
    (hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n x) ≠ ⊤) :
    LevyTriplet d where
  A := 0
  ν := (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity (fun x => ENNReal.ofReal (n x))
  γ := 0
  A_posSemidef := PosSemidef.zero
  ν_zero := by
    rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict
      (measurableSet_singleton 0)]
    simp
  ν_integrable := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hn.ennreal_ofReal
      (by fun_prop : Measurable fun x : Rd d => ENNReal.ofReal (min (‖x‖ ^ 2) 1))]
    refine ne_of_eq_of_ne (lintegral_congr fun x => ?_) hfin
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **The exponent of `(0, n(x)dx, 0)`** for an even `n`: `-∫ (1 - cos⟨z,x⟩) n(x) dx`. -/
theorem densTriplet_lkExponent [NeZero d] (n : Rd d → ℝ) (hn : Measurable n)
    (hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n x) ≠ ⊤)
    (heven : ∀ x, n (-x) = n x) (z : Rd d) :
    (densTriplet n hn hfin).lkExponent z = -(((∫⁻ x in ({0}ᶜ : Set (Rd d)),
      ENNReal.ofReal ((1 - Real.cos ⟪z, x⟫) * n x)).toReal : ℝ) : ℂ) := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  set T := densTriplet n hn hfin
  have hν : T.ν = (volume : Measure (Rd d)).withDensity (fun x => ENNReal.ofReal (n x)) := by
    change (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity _ = _
    rw [restrict_compl_singleton]
  have hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν := by
    rw [hν]
    exact map_withDensity_isometry _ hn.ennreal_ofReal fun x => by
      simp [heven]
  rw [T.lkExponent_of_symm (a := 0) (by simp [T, densTriplet]) rfl hsym z]
  congr 2
  rw [zero_mul, zero_div, zero_add]
  have hnn : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪z, x⟫ := fun x => by
    linarith [Real.cos_le_one ⟪z, x⟫]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) (by fun_prop)]
  congr 1
  change ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪z, x⟫) ∂((volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
    (fun x => ENNReal.ofReal (n x))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hn.ennreal_ofReal (by fun_prop)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (hnn x), mul_comm]

/-- **A law of `(0, n(x)dx, 0)`** (A3(iii)) has the transform `exp(-∫ (1 - cos⟨z,x⟩) n(x) dx)`. -/
theorem exists_law_densTriplet [NeZero d] (n : Rd d → ℝ) (hn : Measurable n)
    (hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n x) ≠ ⊤)
    (heven : ∀ x, n (-x) = n x) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧
      HasTriplet μ (densTriplet n hn hfin) ∧
      ∀ z : Rd d, charFun μ z = ((Real.exp (-(∫⁻ x in ({0}ᶜ : Set (Rd d)),
        ENNReal.ofReal ((1 - Real.cos ⟪z, x⟫) * n x)).toReal) : ℝ) : ℂ) := by
  obtain ⟨μ, hprob, hid, hT⟩ := levy_khintchine_converse (densTriplet n hn hfin)
  refine ⟨μ, hprob, hid, hT, fun z => ?_⟩
  rw [hT z, densTriplet_lkExponent n hn hfin heven z, Complex.ofReal_exp, Complex.ofReal_neg]

/-! ## `lem:elliptical-stable`, clause (2) and the orbit -/

theorem stableExp_nonneg (α : ℝ) {H : Mat d} (hH : H.PosSemidef) (ω : Rd d) :
    0 ≤ stableExp α H ω :=
  Real.rpow_nonneg (quad_nonneg hH ω) _

/-- `S_α(H)` as the law of `(0, n_H(x)dx, 0)`: the transform of every law of that triplet is
`e^{-ψ_H}`. -/
theorem exists_ellipticalStable [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) :
    ∃ μ : Measure (Rd d), IsEllipticalStable α H μ ∧ IsInfinitelyDivisible μ ∧
      ∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
          (fun x => ENNReal.ofReal (stableDensity α H x)) ∧ T.γ = 0 ∧ HasTriplet μ T := by
  obtain ⟨hψ, hfin⟩ := stableExp_eq_lintegral hα0 hα2 hH
  obtain ⟨μ, hprob, hid, hT, hchar⟩ := exists_law_densTriplet (stableDensity α H)
    (measurable_stableDensity α H) hfin (stableDensity_neg α H)
  refine ⟨μ, ⟨hprob, fun ω => ?_⟩, hid, _, rfl, rfl, rfl, hT⟩
  rw [hchar ω, ← hψ ω, ENNReal.toReal_ofReal (stableExp_nonneg α hH.posSemidef ω)]

/-- **`lem:elliptical-stable`(2)**: for every `H ∈ PD(d)` there is a unique probability measure
`S_α(H)` with transform `e^{-ψ_H}`. Spends A3(iii). -/
theorem ellipticalStable_exists_unique [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) : ∃! μ : Measure (Rd d), IsEllipticalStable α H μ := by
  obtain ⟨μ, hμ, -⟩ := exists_ellipticalStable hα0 hα2 hH
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  haveI := hμ.1
  haveI := hν.1
  exact eq_of_charFun_eq fun ω => by rw [hμ.2, hν.2]

/-- Two laws `S_α(H)` are equal. -/
theorem IsEllipticalStable.eq {α : ℝ} {H : Mat d} {μ ν : Measure (Rd d)}
    (hμ : IsEllipticalStable α H μ) (hν : IsEllipticalStable α H ν) : μ = ν := by
  haveI := hμ.1
  haveI := hν.1
  exact eq_of_charFun_eq fun ω => by rw [hμ.2, hν.2]

/-- `A_*S_α(H) = S_α(AHAᵀ)`. -/
theorem IsEllipticalStable.push {α : ℝ} {H : Mat d} {μ : Measure (Rd d)}
    (hμ : IsEllipticalStable α H μ) {A : Mat d} (hA : A ∈ glSet d) :
    IsEllipticalStable α (act A H) (push A μ) := by
  haveI := hμ.1
  refine ⟨inferInstance, fun ω => ?_⟩
  rw [charFun_push A hA, hμ.2, stableExp, stableExp, quad_act]

/-- **`lem:elliptical-stable`(2)**: `S_α(H)` is infinitely divisible with generating triplet
`(0, n_H(x)dx, 0)`, and `A_*S_α(H) = S_α(AHAᵀ)` for every `A ∈ GL(d)`. -/
theorem ellipticalStable_props [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) (μ : Measure (Rd d)) (hμ : IsEllipticalStable α H μ) :
    IsInfinitelyDivisible μ ∧
      (∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
          (fun x => ENNReal.ofReal (stableDensity α H x)) ∧ T.γ = 0 ∧ HasTriplet μ T) ∧
      ∀ A ∈ glSet d, IsEllipticalStable α (act A H) (push A μ) := by
  obtain ⟨μ', hμ', hid, hT⟩ := exists_ellipticalStable hα0 hα2 hH
  rw [hμ.eq hμ']
  exact ⟨hid, hT, fun A hA => hμ'.push hA⟩

/-- **`lem:elliptical-stable`**, in particular: `g(u) = u^{α/2}` satisfies the hypothesis of
`prop:affine-orbits` with `μ_I = S_α(I)`, and the affine orbit of `S_α(I)` is `μ_Σ = S_α(Σ)`, the
stable orbit. -/
theorem ellipticalStable_orbit [NeZero d] {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2)
    (μ : Measure (Rd d)) (hμ : IsEllipticalStable α 1 μ) :
    let g : ℝ → ℝ := fun u => u ^ (α / 2)
    ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∀ ω : Rd d, charFun μ ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      ∀ S : Mat d, S.PosDef → IsEllipticalStable α S (affineOrbit μ S) := by
  intro g
  refine ⟨fun u _ => (Real.continuousAt_rpow_const u (α / 2)
      (Or.inr (by positivity))).continuousWithinAt,
    fun u hu => Real.rpow_nonneg hu _, Real.zero_rpow (by positivity), fun ω => ?_,
    fun S hS => ?_⟩
  · rw [hμ.2, stableExp, quad_one]
  · have h := hμ.push (msqrt_mem_glSet hS)
    rwa [act_msqrt_one hS.posSemidef] at h

/-! ## `prop:stable-step-cone`, clause (1) and the increments of (2) -/

/-- A transform without zeros cancels: `μ * ρ = μ * ρ'` with `μ̂ ≠ 0` and `ρ, ρ'` finite forces
`ρ = ρ'`. -/
theorem conv_left_cancel_finite {μ ρ ρ' : Measure (Rd d)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] (hz : ∀ ω, charFun μ ω ≠ 0)
    (h : μ ∗ ρ = μ ∗ ρ') : ρ = ρ' := by
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have h2 := congrArg (fun m => charFun m ω) h
  simp only [charFun_conv] at h2
  exact mul_left_cancel₀ (hz ω) h2

theorem charFun_ellipticalStable_ne_zero {α : ℝ} {H : Mat d} {μ : Measure (Rd d)}
    (hμ : IsEllipticalStable α H μ) (ω : Rd d) : charFun μ ω ≠ 0 := by
  rw [hμ.2]
  exact_mod_cast (Real.exp_pos _).ne'

/-- The increment `ρ` of a step `μ_{Σ'} = μ_Σ * ρ` of the stable orbit has the transform
`e^{-ψ_{Σ'} + ψ_Σ}`. -/
theorem charFun_stable_increment {α : ℝ} {S S' : Mat d} {μ μ' ρ : Measure (Rd d)}
    [IsFiniteMeasure ρ] (hμ : IsEllipticalStable α S μ) (hμ' : IsEllipticalStable α S' μ')
    (h : μ' = μ ∗ ρ) (ω : Rd d) :
    charFun ρ ω = ((Real.exp (-quad 0 ω - stableExp α S' ω + stableExp α S ω) : ℝ) : ℂ) := by
  haveI := hμ.1
  have h2 := congrArg (fun m => charFun m ω) h
  simp only [charFun_conv, hμ.2, hμ'.2] at h2
  have hne : ((Real.exp (-stableExp α S ω) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  rw [quad_zero, neg_zero, zero_sub]
  rw [show (-stableExp α S' ω + stableExp α S ω) = -stableExp α S' ω - (-stableExp α S ω) by ring,
    Real.exp_sub, Complex.ofReal_div, h2, mul_div_cancel_left₀ _ hne]

/-- The increment density `n_{Σ'} - n_Σ` satisfies the hypotheses of `densTriplet`, and the
transform of its law is `e^{-ψ_{Σ'} + ψ_Σ}`. -/
theorem exists_stable_increment [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef)
    (hord : ∀ x : Rd d, x ≠ 0 → stableDensity α S x ≤ stableDensity α S' x) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
      (∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
          (fun x => ENNReal.ofReal (stableDensity α S' x - stableDensity α S x)) ∧
        T.γ = 0 ∧ HasTriplet ρ T) ∧
      ∀ ω : Rd d, charFun ρ ω =
        ((Real.exp (-(stableExp α S' ω - stableExp α S ω)) : ℝ) : ℂ) := by
  set n : Rd d → ℝ := fun x => stableDensity α S' x - stableDensity α S x with hn
  have hnm : Measurable n := (measurable_stableDensity α S').sub (measurable_stableDensity α S)
  obtain ⟨hψ', hfin'⟩ := stableExp_eq_lintegral hα0 hα2 hS'
  obtain ⟨hψ, -⟩ := stableExp_eq_lintegral hα0 hα2 hS
  have hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin' (setLIntegral_mono' (measurableSet_singleton 0).compl
      fun x hx => ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ stableDensity α S x := by
      unfold stableDensity
      have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
      exact mul_nonneg (mul_nonneg (inv_pos.2 hc).le (Real.rpow_nonneg hS.det_pos.le _))
        (Real.rpow_nonneg (quad_nonneg hS.inv.posSemidef x) _)
    exact mul_le_mul_of_nonneg_left (by simp only [hn]; linarith) (by positivity)
  have heven : ∀ x, n (-x) = n x := fun x => by
    simp only [hn, stableDensity_neg]
  obtain ⟨ρ, hprob, hid, hT, hchar⟩ := exists_law_densTriplet n hnm hfin heven
  refine ⟨ρ, hprob, hid, ⟨_, rfl, rfl, rfl, hT⟩, fun ω => ?_⟩
  rw [hchar ω]
  congr 3
  -- `∫ (1 - cos) (n' - n) = ψ' - ψ`
  have hnn : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪ω, x⟫ := fun x => by
    linarith [Real.cos_le_one ⟪ω, x⟫]
  have h0 : ∀ x : Rd d, 0 ≤ stableDensity α S x := fun x => by
    unfold stableDensity
    have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
    exact mul_nonneg (mul_nonneg (inv_pos.2 hc).le (Real.rpow_nonneg hS.det_pos.le _))
      (Real.rpow_nonneg (quad_nonneg hS.inv.posSemidef x) _)
  have hadd : (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n x)) +
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
        stableDensity α S x) =
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) *
        stableDensity α S' x) := by
    rw [← lintegral_add_right _ (Measurable.ennreal_ofReal (by
      exact (by fun_prop : Measurable fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).mul
        (measurable_stableDensity α S)))]
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    rw [← ENNReal.ofReal_add (mul_nonneg (hnn x) (by simp only [hn]; linarith [hord x hx]))
      (mul_nonneg (hnn x) (h0 x))]
    congr 1
    simp only [hn]
    ring
  rw [← hψ', ← hψ] at hadd
  have hfin1 : (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n x)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hadd ▸ le_self_add)
  have := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (stableExp_nonneg α hS.posSemidef ω),
    ENNReal.toReal_ofReal (stableExp_nonneg α hS'.posSemidef ω)] at this
  linarith

/-- **`prop:stable-step-cone`(1)**: for the stable orbit and `Σ, Σ' ∈ PD(d)` with
`M = Σ^{-1/2}Σ'Σ^{-1/2}`, the following are equivalent: (a) `μ_{Σ'} = μ_Σ * ρ` for a positive
finite measure `ρ`; (b) `n_Σ ≤ n_{Σ'}` off the origin; (c) `λ_min(M)^{d+α} ≥ det M`. -/
theorem stable_step_cone_tfae [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (μ : Mat d → Measure (Rd d)) (hμ : ∀ S : Mat d, S.PosDef → IsEllipticalStable α S (μ S))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) :
    List.TFAE
      [∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ μ S' = μ S ∗ ρ,
        ∀ x : Rd d, x ≠ 0 → stableDensity α S x ≤ stableDensity α S' x,
        (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α)] := by
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  tfae_have 1 → 2 := by
    rintro ⟨ρ, hρ, h⟩
    exact (stable_tail hα0 hα2 hS hS' ρ
      (charFun_stable_increment (hμ S hS) (hμ S' hS') h)).2.2
  tfae_have 2 → 3 := fun h => ((stableLE_iff_density hα0 hα2 hS hS').2 h).2.2.2
  tfae_have 3 → 1 := by
    intro h
    have hord := (stableLE_iff_density hα0 hα2 hS hS').1 ⟨hS, hS', hM, h⟩
    obtain ⟨ρ, hprob, -, -, hchar⟩ := exists_stable_increment hα0 hα2 hS hS' hord
    refine ⟨ρ, inferInstance, ?_⟩
    haveI := (hμ S hS).1
    haveI := (hμ S' hS').1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, (hμ S hS).2, (hμ S' hS').2, hchar, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  tfae_finish

/-- **`prop:stable-step-cone`(1)**: when (a)–(c) hold, `ρ` is unique, and it is the infinitely
divisible probability measure `ρ_{Σ,Σ'}` with generating triplet `(0, (n_{Σ'} - n_Σ)(x)dx, 0)`. -/
theorem stable_step_cone_increment [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (μ : Mat d → Measure (Rd d)) (hμ : ∀ S : Mat d, S.PosDef → IsEllipticalStable α S (μ S))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef)
    (hc : (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α)) :
    (∃! ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ μ S' = μ S ∗ ρ) ∧
      ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ → μ S' = μ S ∗ ρ →
        IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
        ∃ T : LevyTriplet d, T.A = 0 ∧
          T.ν = (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
            (fun x => ENNReal.ofReal (stableDensity α S' x - stableDensity α S x)) ∧
          T.γ = 0 ∧ HasTriplet ρ T := by
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hord := (stableLE_iff_density hα0 hα2 hS hS').1 ⟨hS, hS', hM, hc⟩
  obtain ⟨ρ₀, hprob, hid, hT, hchar⟩ := exists_stable_increment hα0 hα2 hS hS' hord
  haveI := (hμ S hS).1
  haveI := (hμ S' hS').1
  have hρ₀ : μ S' = μ S ∗ ρ₀ := by
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, (hμ S hS).2, (hμ S' hS').2, hchar, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have huniq : ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ → μ S' = μ S ∗ ρ → ρ = ρ₀ :=
    fun ρ hρ h => conv_left_cancel_finite (charFun_ellipticalStable_ne_zero (hμ S hS))
      (h.symm.trans hρ₀)
  refine ⟨⟨ρ₀, ⟨inferInstance, hρ₀⟩, fun ρ ⟨hρ, h⟩ => huniq ρ hρ h⟩, fun ρ hρ h => ?_⟩
  rw [huniq ρ hρ h]
  exact ⟨hprob, hid, hT⟩

/-- **`prop:stable-step-cone`(2)**, the increments: for any increments `ρ_{Σ,Σ'}` of the pairs of
`≼_α`, `ρ_{Σ,Σ} = δ₀`, `ρ_{Σ,Σ''} = ρ_{Σ',Σ''} * ρ_{Σ,Σ'}` whenever `Σ ≼_α Σ' ≼_α Σ''`, and
`A_*ρ_{Σ,Σ'} = ρ_{AΣAᵀ,AΣ'Aᵀ}`. -/
theorem stable_step_increments [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (μ : Mat d → Measure (Rd d)) (hμ : ∀ S : Mat d, S.PosDef → IsEllipticalStable α S (μ S))
    (ρ : Mat d → Mat d → Measure (Rd d))
    (hρ : ∀ S S' : Mat d, stableLE α S S' → IsFiniteMeasure (ρ S S') ∧ μ S' = μ S ∗ ρ S S') :
    (∀ S : Mat d, S.PosDef → ρ S S = Measure.dirac 0) ∧
      (∀ S S' S'' : Mat d, stableLE α S S' → stableLE α S' S'' →
        ρ S S'' = ρ S' S'' ∗ ρ S S') ∧
      ∀ A ∈ glSet d, ∀ S S' : Mat d, stableLE α S S' → push A (ρ S S') = ρ (act A S) (act A S') := by
  have hpo := stableLE_partialOrder (d := d) hα0 hα2
  refine ⟨fun S hS => ?_, fun S S' S'' h h' => ?_, fun A hA S S' h => ?_⟩
  · obtain ⟨hfin, hstep⟩ := hρ S S (hpo.1.refl S hS)
    haveI := hfin
    haveI := (hμ S hS).1
    refine conv_left_cancel_finite (charFun_ellipticalStable_ne_zero (hμ S hS)) ?_
    rw [← hstep, Measure.conv_dirac_zero]
  · have h'' := hpo.1.trans S h.1 S' h.2.1 S'' h'.2.1 h h'
    obtain ⟨hfin1, h1⟩ := hρ S S' h
    obtain ⟨hfin2, h2⟩ := hρ S' S'' h'
    obtain ⟨hfin3, h3⟩ := hρ S S'' h''
    haveI := hfin1; haveI := hfin2; haveI := hfin3
    haveI := (hμ S h.1).1
    refine conv_left_cancel_finite (charFun_ellipticalStable_ne_zero (hμ S h.1)) ?_
    rw [← h3, h2, h1, Measure.conv_assoc, Measure.conv_comm (ρ S S')]
  · have hA' := (hpo.2.2 A hA S S' h.1 h.2.1).1 h
    obtain ⟨hfin1, h1⟩ := hρ S S' h
    obtain ⟨hfin2, h2⟩ := hρ _ _ hA'
    haveI := hfin1; haveI := hfin2
    haveI := (hμ S h.1).1
    have hAS := (posDef_act_iff hA S).2 h.1
    have hAS' := (posDef_act_iff hA S').2 h.2.1
    haveI := (hμ _ hAS).1
    haveI : IsFiniteMeasure (push A (ρ S S')) := by
      unfold AffineHemigroup.push; infer_instance
    refine conv_left_cancel_finite (charFun_ellipticalStable_ne_zero (hμ _ hAS)) ?_
    have e1 : push A (μ S) = μ (act A S) := ((hμ S h.1).push hA).eq (hμ _ hAS)
    have e2 : push A (μ S') = μ (act A S') := ((hμ S' h.2.1).push hA).eq (hμ _ hAS')
    rw [← h2, ← e1, ← e2, h1, push_conv]

end AffineHemigroup
