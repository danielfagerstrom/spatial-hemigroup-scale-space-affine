/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityCascade
import AffineHemigroup.SimilarityBounded
import AffineHemigroup.TemperedStepCone
import AffineHemigroup.IsotropicCorner

/-!
# `prop:similarity-stable-order-families`: (similarities, stable order), the families and the shape

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-stable-order-families`
(clause (1) is the split child `lem:stable-order-psd`, proved in `AffineHemigroup.StableOrderPSD`).
Clauses (3)–(5) below are the node `prop:similarity-stable-order-kernels` (round 2 of the
external review), as its clauses (1)–(3); the docstrings name them by that node.

(2) The orbit of a profile with `R(λ) ≥ λ^α` is the family of kernels from the origin of a
`(GL(d), ≤_α)`-cascade family, in particular the stable laws `S_β(I)` and the tempered profiles of
index `β ∈ [α, 2)`; (3) the kernels of a `(G, ≤_α)`-family, `G ⊇ S(d)`, are infinitely divisible
and form a family as in `prop:similarity-general-sandwich`, and the isotropic members for `G = S(d)`
are the rotation-invariant self-decomposable laws other than `δ₀`; (4) the sandwich between two
multiples of `I`, along `≤_α` and along the Loewner order, and the shape bounds it gives; (5) a family
in the cell `(S(d), ≤_α)` in neither neighbour.

## Routes

The blueprint's. **(2)'s ray increments** for a singular `Σ` are the image under `Σ^{1/2}` of the
increment of `I ≤ cI`, which is in the cone of `prop:orbit-step-cone`(2) since `R ≥ 1`. That the law
of a profile is not `δ₀` is read from its exponent, which is not identically `0` (a dense sequence of
directions). **(4)** is one lemma, `sim_sandwich_of_steps`, read twice: any `ε ≤ t` with
infinitely divisible steps `εI → Σ → tI` and ray increments give the bounds with `t/ε`.
**(5)**: the stable increments are those of clause (2) at `β = α`; the failure of `GL(d)`-covariance is
read at `A = (I + e₁e₁ᵀ)^{1/2}` and `ω = e₁`, where the exponents differ by `bκ(d - 1)`.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The law of a profile is not `δ₀` -/

/-- **The exponent of a profile is not identically `0`.** -/
theorem RadialProfile.exists_exponent_ne_zero (hd : 1 ≤ d) (K : RadialProfile d) :
    ∃ ω : Rd d, K.exponent ω ≠ 0 := by
  haveI : NeZero d := ⟨by omega⟩
  by_contra hcon
  push Not at hcon
  have hL : ∀ ω, K.exponentL ω = 0 := fun ω => by
    have := hcon ω
    rwa [RadialProfile.exponent, ENNReal.toReal_eq_zero_iff,
      or_iff_left (K.exponentL_ne_top hd ω)] at this
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (Rd d)
  have hmeas : ∀ ω : Rd d, Measurable fun x : Rd d =>
      ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.m ‖x‖) := fun ω =>
    ((by fun_prop : Measurable fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).mul
      (K.measurable_m_norm hd)).ennreal_ofReal
  have hae : ∀ᵐ x ∂(volume : Measure (Rd d)), ∀ n, (1 - Real.cos ⟪q n, x⟫) * K.m ‖x‖ ≤ 0 := by
    rw [ae_all_iff]
    intro n
    have h := hL (q n)
    rw [RadialProfile.exponentL, lintegral_eq_zero_iff (hmeas _)] at h
    filter_upwards [h] with x hx
    exact ENNReal.ofReal_eq_zero.1 hx
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  set U : Set (Rd d) := {x | 0 < ‖x‖ ∧ ‖x‖ < r0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hUne : U.Nonempty := ⟨(r0 / 2) • ebasis 0, by
    simp only [hU, mem_setOf_eq, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ r0 / 2)]
    constructor <;> linarith⟩
  have hpos : 0 < (volume : Measure (Rd d)) U := hUo.measure_pos volume hUne
  obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, ∀ n, (1 - Real.cos ⟪q n, x⟫) * K.m ‖x‖ ≤ 0 := by
    by_contra hcon'
    push Not at hcon'
    have h0 : (volume : Measure (Rd d)) U = 0 := measure_mono_null (fun y hy => by
      obtain ⟨n, hn⟩ := hcon' y hy
      intro hall; exact absurd (hall n) (not_le.2 hn)) (ae_iff.1 hae)
    exact hpos.ne' h0
  obtain ⟨hx0, hxr⟩ := hxU
  have hm : 0 < K.m ‖x‖ := by
    unfold RadialProfile.m
    have : K.k r0 ≤ K.k ‖x‖ := K.k_antitone hx0 hr0 hxr.le
    exact div_pos (lt_of_lt_of_le hk0 this) (pow_pos hx0 _)
  have hcos : ∀ n, Real.cos ⟪q n, x⟫ = 1 := fun n => by
    have h1 := hx n
    have h2 : 0 ≤ 1 - Real.cos ⟪q n, x⟫ := by linarith [Real.cos_le_one ⟪q n, x⟫]
    have h3 : 1 - Real.cos ⟪q n, x⟫ ≤ 0 := by
      by_contra h4
      push Not at h4
      exact absurd h1 (not_le.2 (mul_pos h4 hm))
    linarith
  have hcont : Continuous fun ω : Rd d => Real.cos ⟪ω, x⟫ := by fun_prop
  have hall : (fun ω : Rd d => Real.cos ⟪ω, x⟫) = fun _ => 1 :=
    hcont.ext_on hq continuous_const (by rintro _ ⟨n, rfl⟩; exact hcos n)
  have := congrFun hall ((Real.pi / ‖x‖ ^ 2) • x)
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_ne_zero 2 hx0.ne'), Real.cos_pi] at this
  norm_num at this

/-- **The law of a profile is not `δ₀`.** -/
theorem profileLaw_ne_dirac (hd : 1 ≤ d) (K : RadialProfile d) {μI : Measure (Rd d)}
    (hμI : IsProfileLaw K μI) : μI ≠ Measure.dirac 0 := by
  intro h
  obtain ⟨ω, hω⟩ := K.exists_exponent_ne_zero hd
  have h1 := hμI.2 ω
  rw [h, charFun_dirac] at h1
  simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
  have h2 : Real.exp (-K.exponent ω) = 1 := by exact_mod_cast h1.symm
  rw [Real.exp_eq_one_iff, neg_eq_zero] at h2
  exact hω h2

/-! ## The orbit of a rotation-invariant law as kernels from the origin -/

/-- **(a)–(c) of `lem:gw-kernels-from-origin`(2) for an affine orbit** under `GL(d)`: the orbit of a
rotation-invariant law other than `δ₀` (the proof of `prop:gw-ray-families`(3)). -/
theorem affineOrbit_isOriginKernels [NeZero d] {μI : Measure (Rd d)} [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hne : μI ≠ Measure.dirac 0) :
    IsOriginKernels (glSet d) (affineOrbit μI) := by
  have hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (affineOrbit μI S) :=
    fun S _ => inferInstance
  have hm1 : affineOrbit μI 1 = μI := by
    apply eq_of_charFun_eq
    intro ω
    rw [charFun_affineOrbit hrot PosSemidef.one, quad_one, Real.sqrt_sq (norm_nonneg _),
      ← charFun_eq_norm_smul_ebasis hrot]
  refine ⟨hprob, ?_, by rw [hm1]; exact hne, ?_, ?_⟩
  · apply eq_of_charFun_eq
    intro ω
    rw [charFun_affineOrbit hrot PosSemidef.zero, quad_zero, Real.sqrt_zero, zero_smul,
      charFun_zero, charFun_dirac]
    simp
  · intro A _ S hS
    apply eq_of_charFun_eq
    intro ω
    rw [push, charFun_map_lin, charFun_affineOrbit hrot hS,
      charFun_affineOrbit hrot (posSemidef_act A hS), quad_act]
  · intro ω
    have hc : Continuous fun S : Mat d => charFun μI (Real.sqrt (quad S ω) • ebasis 0) :=
      continuous_charFun.comp ((Real.continuous_sqrt.comp (continuous_quad ω)).smul continuous_const)
    exact hc.continuousOn.congr fun S hS => charFun_affineOrbit hrot hS ω

/-! ## Clause (2) -/

/-- **`prop:similarity-stable-order-families`(2)**, the general linear row: for a profile `k` whose
dilation ratio has `R(λ) ≥ λ^α` for `λ ≥ 1`, and `μ_I` its law, `Σ ↦ (Σ^{1/2})_*μ_I` is the family
of kernels from the origin of a `(GL(d), ≤_α)`-cascade family. Spends A3(iii). -/
theorem stable_order_gl_row (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (K : RadialProfile d) (hR : ∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam)
    (μI : Measure (Rd d)) (hμI : IsProfileLaw K μI) :
    IsKernelsFromOrigin (glSet d) (stablePlusLE α) (affineOrbit μI) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := hμI.1
  have hrot := (profileLaw_props hd1 K μI hμI).1
  have hne := profileLaw_ne_dirac hd1 K hμI
  have hW : IsWedgeDatum (glSet d) (stablePlusLE α) :=
    (stablePlusLE_order hd hα0 hα2).2.2.2.2.2.1 _ glSet_isClosedSubgroupGL.1
      glSet_isClosedSubgroupGL.2
  have hm := affineOrbit_isOriginKernels hrot hne
  have hz : HasNoZeros (affineOrbit μI) := fun S hS ω => by
    rw [charFun_affineOrbit hrot hS, hμI.2]
    exact_mod_cast (Real.exp_pos _).ne'
  refine (gw_kernels_from_origin_converse hW _ hm hz ?_).1
  intro S S' hS hS' hle
  rcases hle with rfl | ⟨c, hc, rfl⟩ | ⟨hSpd, hS'pd, hst⟩
  · refine ⟨affineOrbit μI S', inferInstance, ?_⟩
    rw [hm.zero, Measure.dirac_zero_conv]
  · -- the ray: the increment of `I ≤ cI`, carried by `Σ^{1/2}`
    have hc0 : 0 < c := by linarith
    have hcI : (c • (1 : Mat d)).PosDef := PosDef.one.smul hc0
    have hord : ∀ x : Rd d, x ≠ 0 → K.orbitDensity 1 x ≤ K.orbitDensity (c • 1) x := by
      refine (orbit_density_order_iff hd1 K PosDef.one hcI).1.2 ⟨?_, ?_⟩
      · rw [relStep_one_left, lamMin_smul hc0.le, lamMin_one, mul_one]; exact hc
      · rw [relStep_one_left, lamMin_smul hc0.le, lamMin_one, mul_one, det_smul_one]
        have hR1 := (dilRatio_mem hd1 K _ (Real.one_le_sqrt.2 hc)).2
        nlinarith [pow_pos hc0 d, sq_nonneg (dilRatio K.k (Real.sqrt c) - 1)]
    obtain ⟨ρ, hρ, -, -, hinc⟩ := orbit_density_order_increment hd1 K PosDef.one hcI hord μI hμI
    rw [affineOrbit_one] at hinc
    refine ⟨push (msqrt S) ρ, inferInstance, ?_⟩
    have h1 : affineOrbit μI (c • S) = push (msqrt S) (affineOrbit μI (c • (1 : Mat d))) := by
      rw [affineOrbit, affineOrbit, msqrt_smul hc0.le hS, msqrt_smul_one, push_push,
        Matrix.mul_smul, Matrix.mul_one]
    rw [h1, hinc, push_conv]
    rfl
  · -- the cone of `prop:orbit-step-cone`(2)
    have hM : (relStep S S').PosDef := (posDef_relStep_iff hSpd S').2 hS'pd
    have hl := lamMin_pos hM
    have hl1 := one_le_lamMin_of_stable hα0 hM hst.2.2.2
    have hord := (orbit_density_order_iff hd1 K hSpd hS'pd).1.2 ⟨hl1, by
      have hRl := hR _ (Real.one_le_sqrt.2 hl1)
      have hsq : (Real.sqrt (lamMin (relStep S S')) ^ α) ^ 2 ≤
          dilRatio K.k (Real.sqrt (lamMin (relStep S S'))) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hRl 2
      calc (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α) := hst.2.2.2
        _ = lamMin (relStep S S') ^ d * (Real.sqrt (lamMin (relStep S S')) ^ α) ^ 2 :=
            (pow_mul_sqrt_rpow_sq hl α).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq (pow_nonneg hl.le _)⟩
    obtain ⟨ρ, hρ, -, -, hinc⟩ := orbit_density_order_increment hd1 K hSpd hS'pd hord μI hμI
    exact ⟨ρ, hρ, hinc⟩

/-- The constant `j ≡ c > 0` is a tempering factor. -/
theorem isTemperingProfile_const {c : ℝ} (hc : 0 < c) : IsTemperingProfile fun _ => c :=
  ⟨fun _ _ => hc.le, fun _ _ _ _ _ => le_rfl, c, hc, tendsto_const_nhds⟩

/-- **The stable law `S_β(I)` as the law of the profile `c_{d,β}⁻¹ r^{-β}`.** -/
theorem ellipticalStable_isProfileLaw [NeZero d] (hd : 1 ≤ d) {β : ℝ} (hβ0 : 0 < β)
    (hβ2 : β < 2) {μ : Measure (Rd d)} (hμ : IsEllipticalStable β 1 μ) :
    IsProfileLaw (temperedProfile hd hβ0 hβ2 (fun _ => (stableConst (d := d) β)⁻¹)
      (isTemperingProfile_const (inv_pos.2 (stableConst_pos_finite (d := d) hβ0 hβ2).2))) μ := by
  refine ⟨hμ.1, fun ω => ?_⟩
  rw [hμ.2]
  congr 3
  set K := temperedProfile hd hβ0 hβ2 (fun _ => (stableConst (d := d) β)⁻¹)
    (isTemperingProfile_const (inv_pos.2 (stableConst_pos_finite (d := d) hβ0 hβ2).2)) with hK
  have h := (stableExp_eq_lintegral hβ0 hβ2 (PosDef.one (n := Fin d))).1 ω
  rw [restrict_compl_singleton] at h
  have hc := (stableConst_pos_finite (d := d) hβ0 hβ2).2
  have heq : K.exponentL ω = ENNReal.ofReal (stableExp β 1 ω) := by
    rw [h, RadialProfile.exponentL]
    refine lintegral_congr fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    congr 2
    rw [RadialProfile.m, hK]
    change ‖x‖ ^ (-β) * (stableConst β)⁻¹ / ‖x‖ ^ d = stableDensity β 1 x
    have hpow : (‖x‖ ^ 2) ^ (-((d : ℝ) + β) / 2) = ‖x‖ ^ (-(d : ℝ) - β) := by
      rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [stableDensity, det_one, Real.one_rpow, mul_one, inv_one, quad_one, mul_div_right_comm,
      rpow_neg_div_pow hx', hpow, mul_comm]
  rw [RadialProfile.exponent, heq, ENNReal.toReal_ofReal (stableExp_nonneg β PosSemidef.one ω)]

/-- **`prop:similarity-stable-order-families`(2)**, the instances: this applies to `S_β(I)` for
every `β ∈ [α, 2)` and to the profiles `r^{-β} j(r)` of `prop:tempered-step-cone` of every index
`β ∈ [α, 2)`. -/
theorem stable_order_gl_row_examples (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    (∀ β : ℝ, α ≤ β → β < 2 → ∀ μ : Measure (Rd d), IsEllipticalStable β 1 μ →
      IsKernelsFromOrigin (glSet d) (stablePlusLE α) (affineOrbit μ)) ∧
    ∀ β : ℝ, α ≤ β → β < 2 → ∀ j : ℝ → ℝ, IsTemperingProfile j → ∀ K : RadialProfile d,
      (∀ r : ℝ, 0 < r → K.k r = r ^ (-β) * j r) → ∀ μI : Measure (Rd d), IsProfileLaw K μI →
        IsKernelsFromOrigin (glSet d) (stablePlusLE α) (affineOrbit μI) := by
  have hd1 : 1 ≤ d := by omega
  have htemp : ∀ β : ℝ, α ≤ β → β < 2 → ∀ j : ℝ → ℝ, IsTemperingProfile j →
      ∀ K : RadialProfile d, (∀ r : ℝ, 0 < r → K.k r = r ^ (-β) * j r) →
      ∀ μI : Measure (Rd d), IsProfileLaw K μI →
        IsKernelsFromOrigin (glSet d) (stablePlusLE α) (affineOrbit μI) := by
    intro β hαβ hβ2 j hj K hK μI hμI
    have hβ0 : 0 < β := lt_of_lt_of_le hα0 hαβ
    have hR := (tempered_step_cone hd1 hβ0 hβ2 j hj K hK).1
    refine stable_order_gl_row hd hα0 hα2 K (fun lam hlam => ?_) μI hμI
    rw [hR lam hlam]
    exact Real.rpow_le_rpow_of_exponent_le hlam hαβ
  refine ⟨fun β hαβ hβ2 μ hμ => ?_, htemp⟩
  haveI : NeZero d := ⟨by omega⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hα0 hαβ
  exact htemp β hαβ hβ2 (fun _ => (stableConst (d := d) β)⁻¹)
    (isTemperingProfile_const (inv_pos.2 (stableConst_pos_finite (d := d) hβ0 hβ2).2)) _
    (fun r _ => rfl) μ (ellipticalStable_isProfileLaw hd1 hβ0 hβ2 hμ)

/-! ## Clause (3) -/

/-- **The kernels of a similarity-covariant cascade family along an order with the path condition**
(`prop:similarity-cascade-families`(1), whose proof reads of the Loewner order only that it gives
these increments): infinitely divisible increments and kernels, and the setting of
`prop:similarity-general-sandwich`. Spends A6 and A3(i)–(ii). -/
theorem sim_family_of_wedge (hd : 2 ≤ d) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (hP : HasPathCondition le) (hsim : simSet d ⊆ G)
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G le μ) :
    (∀ p ∈ wedgePairs le, IsInfinitelyDivisible (μ p.1 p.2)) ∧
      (∀ S : Mat d, S.PosSemidef → IsInfinitelyDivisible (μ 0 S)) ∧
      (∃ (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)),
        IsSimGeneralFamily (fun S => μ 0 S) C L) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef → le S S' →
        IsInfinitelyDivisible (μ S S') ∧ μ 0 S' = μ 0 S ∗ μ S S' := by
  obtain ⟨hpair, hzero⟩ := gw_family_infinitelyDivisible (by omega) hW hP μ hμ
  have hpsd0 : (0 : Mat d).PosSemidef := PosSemidef.zero
  have hle0 : ∀ S : Mat d, S.PosSemidef → le 0 S := fun S hS => wedge_zero_le hW hS
  have hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (μ 0 S) := fun S hS =>
    hμ.isProbability (0, S) ⟨hpsd0, hS, hle0 S hS⟩
  have hsymm : ∀ S : Mat d, S.PosSemidef → push (-1) (μ 0 S) = μ 0 S := fun S hS => by
    have h := hμ.covariant (-1) (hsim neg_one_mem_simSet) (0, S) ⟨hpsd0, hS, hle0 S hS⟩
    rw [h, act_zero]
    congr 1
    simp [act]
  have hker : ∀ S : Mat d, S.PosDef → ∃ T : LevyTriplet d, T.γ = 0 ∧ HasTriplet (μ 0 S) T :=
    fun S hS => by
      haveI := hprob S hS.posSemidef
      obtain ⟨T, hT⟩ := levy_khintchine_exists (μ 0 S) (hzero S hS.posSemidef)
      exact ⟨T, (symm_triplet_of_symm (hzero S hS.posSemidef) (hsymm S hS.posSemidef) hT).1, hT⟩
  classical
  let T : Mat d → LevyTriplet d := fun S =>
    if hS : S.PosDef then Classical.choose (hker S hS) else Classical.choose (hker 1 PosDef.one)
  have hT : ∀ S : Mat d, S.PosDef → (T S).γ = 0 ∧ HasTriplet (μ 0 S) (T S) := fun S hS => by
    simp only [T, dif_pos hS]
    exact Classical.choose_spec (hker S hS)
  refine ⟨hpair, hzero, ⟨fun S => (T S).A, fun S => (T S).ν,
    { isProbability := fun S hS => hprob S hS.posSemidef
      symmetric := fun S hS => hsymm S hS.posSemidef
      infinitelyDivisible := fun S hS => hzero S hS.posSemidef
      triplet := fun S hS => ⟨T S, rfl, rfl, (hT S hS).1, (hT S hS).2⟩
      covariant := fun S hS c hc Q hQ => by
        have h := hμ.covariant _ (hsim (sqrt_smul_mem_simSet hc hQ)) (0, S)
          ⟨hpsd0, hS.posSemidef, hle0 S hS.posSemidef⟩
        rw [h, act_zero, act_sqrt_smul c hc.le] }⟩, fun S S' hS hS' hle => ?_⟩
  refine ⟨hpair (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩, ?_⟩
  haveI := hprob S hS.posSemidef
  haveI := hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩
  rw [hμ.cascade 0 S S' hpsd0 hS.posSemidef hS'.posSemidef (hle0 S hS.posSemidef) hle,
    Measure.conv_comm]

/-- **`prop:similarity-stable-order-kernels`(1)**, the kernels of the similarity row: for a closed
subgroup `G ⊇ S(d)` and a `(G, ≤_α)`-cascade family, every increment and every kernel from the
origin is infinitely divisible; `(μ_Σ)_{Σ ∈ PD(d)}` is a family as in
`prop:similarity-general-sandwich`; and every `≤_α`-step in `PD(d)` has the infinitely divisible
increment `μ_{Σ,Σ'}`. Spends A6 and A3(i)–(ii). -/
theorem stable_order_sim_kernels (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (G : Set (Mat d)) (hG : IsClosedSubgroupGL G) (hsim : simSet d ⊆ G)
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G (stablePlusLE α) μ) :
    (∀ p ∈ wedgePairs (stablePlusLE α), IsInfinitelyDivisible (μ p.1 p.2)) ∧
      (∀ S : Mat d, S.PosSemidef → IsInfinitelyDivisible (μ 0 S)) ∧
      (∃ (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)),
        IsSimGeneralFamily (fun S => μ 0 S) C L) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef → stablePlusLE α S S' →
        IsInfinitelyDivisible (μ S S') ∧ μ 0 S' = μ 0 S ∗ μ S S' := by
  have hord := stablePlusLE_order hd hα0 hα2
  exact sim_family_of_wedge hd (hord.2.2.2.2.2.1 G hG fun c hc => hsim (smul_one_mem_simSet hc))
    hord.2.2.2.2.1 hsim μ hμ

/-- **`prop:similarity-stable-order-kernels`(1)**, the isotropic members: for `G = S(d)` they are
exactly the rotation-invariant self-decomposable laws other than `δ₀`. -/
theorem stable_order_sim_isotropic (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (μI : Measure (Rd d)) :
    (∃ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (simSet d) (stablePlusLE α) μ ∧
        μ 0 1 = μI) ↔
      IsProbabilityMeasure μI ∧ IsRotationInvariant μI ∧ IsSelfDecomposable μI ∧
        μI ≠ Measure.dirac 0 := by
  have hord := stablePlusLE_order hd hα0 hα2
  exact similarity_row_isotropic_members (by omega) (stablePlusLE α) hord.1
    (fun A hA S S' hS hS' h => hord.2.1 A (simSet_subset_glSet hA) S S' hS hS' h) hord.2.2.1
    hord.2.2.2.1 μI

/-! ## Clause (4) -/

/-- **A rotation-invariant measure has a radial Lévy exponent**: `ψ_L(ω) = ψ_L(ω')` when
`|ω| = |ω'|`, by invariance under the reflection in `(ω - ω')^⊥`. -/
theorem levyExp_eq_of_norm_eq {L : Measure (Rd d)} (hL : IsRotationInvariant L) {ω ω' : Rd d}
    (h : ‖ω‖ = ‖ω'‖) : levyExp L ω = levyExp L ω' := by
  set e : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (ω - ω'))ᗮ with he
  set A : Mat d :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (e.symm : Rd d →L[ℝ] Rd d) with hAdef
  have hlinA : lin A = (e.symm : Rd d →L[ℝ] Rd d) := by
    simp only [lin, hAdef, StarAlgEquiv.apply_symm_apply]
  have hlinAT : lin Aᵀ = (e : Rd d →L[ℝ] Rd d) := by
    rw [lin_transpose, hlinA, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  have hAAT : A * Aᵀ = 1 := by
    apply lin_injective
    rw [lin_mul, hlinA, hlinAT, lin_one]
    ext x
    simp
  have hA : A ∈ orthSet d := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).2 hAAT
  have h2 := levyExp_push A L ω
  rw [hL A hA, hlinAT] at h2
  rw [h2]
  change levyExp L (e ω) = _
  rw [he, Submodule.reflection_sub h]

/-- **The doubling bound of a Lévy exponent**: `ψ_L(2ω) ≤ 4ψ_L(ω)`. -/
theorem levyExp_two_smul_le {L : Measure (Rd d)} (hL : IsLevyMeasure L) (ω : Rd d) :
    levyExp L ((2 : ℝ) • ω) ≤ 4 * levyExp L ω := by
  have h : levyExpL L ((2 : ℝ) • ω) ≤ 4 * levyExpL L ω := by
    unfold levyExpL
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by norm_num), real_inner_smul_left]
    exact ENNReal.ofReal_le_ofReal (one_sub_cos_two_mul_le _)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hL.levyExpL_ne_top ω)) h
  rw [ENNReal.toReal_mul, show (4 : ℝ≥0∞).toReal = 4 by simp] at this
  exact this

/-- **The doubling bound, compared on two vectors**: a nonnegative radial `F` with `F(0) = 0`,
nondecreasing along rays and with `F(2ξ) ≤ 4F(ξ)`, has `F(ξ') ≤ 4c F(ξ)` for `c ≥ 1` and
`|ξ'| ≤ √c |ξ|` (the argument of `RadialProfile.exponent_le_four_mul`, for any such `F`). -/
theorem le_four_mul_of_doubling {F : Rd d → ℝ} (h0 : F 0 = 0) (hnn : ∀ η, 0 ≤ F η)
    (hrad : ∀ η η' : Rd d, ‖η‖ = ‖η'‖ → F η = F η')
    (hmono : ∀ (η : Rd d) (b : ℝ), 1 ≤ b → F η ≤ F (b • η))
    (hdouble : ∀ η, F ((2 : ℝ) • η) ≤ 4 * F η) {c : ℝ} (hc : 1 ≤ c) {ξ ξ' : Rd d}
    (h : ‖ξ'‖ ≤ Real.sqrt c * ‖ξ‖) : F ξ' ≤ 4 * c * F ξ := by
  have hpow : ∀ n : ℕ, ∀ η, F ((2 : ℝ) ^ n • η) ≤ 4 ^ n * F η := by
    intro n
    induction n with
    | zero => intro η; simp
    | succ n ih =>
      intro η
      rw [pow_succ, mul_smul]
      calc F ((2 : ℝ) ^ n • (2 : ℝ) • η) ≤ 4 ^ n * F ((2 : ℝ) • η) := ih _
        _ ≤ 4 ^ n * (4 * F η) := mul_le_mul_of_nonneg_left (hdouble η) (by positivity)
        _ = 4 ^ (n + 1) * F η := by ring
  have hsc : 1 ≤ Real.sqrt c := Real.one_le_sqrt.2 hc
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hsc (by norm_num : (1 : ℝ) < 2)
  have hstep : F ξ' ≤ F ((2 : ℝ) ^ (n + 1) • ξ) := by
    rcases eq_or_ne ξ' 0 with h0' | h0'
    · rw [h0', h0]; exact hnn _
    · have hξ' : 0 < ‖ξ'‖ := norm_pos_iff.2 h0'
      have hb0 : 0 ≤ (2 : ℝ) ^ (n + 1) * ‖ξ‖ / ‖ξ'‖ := by positivity
      have hb1 : 1 ≤ (2 : ℝ) ^ (n + 1) * ‖ξ‖ / ‖ξ'‖ := by
        rw [le_div_iff₀ hξ', one_mul]
        calc ‖ξ'‖ ≤ Real.sqrt c * ‖ξ‖ := h
          _ ≤ 2 ^ (n + 1) * ‖ξ‖ := mul_le_mul_of_nonneg_right hn2.le (norm_nonneg _)
      refine (hmono ξ' _ hb1).trans (le_of_eq (hrad _ _ ?_))
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hb0,
        Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hξ'.ne']
  calc F ξ' ≤ F ((2 : ℝ) ^ (n + 1) • ξ) := hstep
    _ ≤ 4 ^ (n + 1) * F ξ := hpow _ ξ
    _ ≤ 4 * c * F ξ := by
        refine mul_le_mul_of_nonneg_right ?_ (hnn ξ)
        have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h5 : ((2 : ℝ) ^ n) ^ 2 ≤ c := by
          calc ((2 : ℝ) ^ n) ^ 2 ≤ Real.sqrt c ^ 2 := pow_le_pow_left₀ (by positivity) hn1 2
            _ = c := Real.sq_sqrt (by linarith)
        rw [pow_succ, h4]
        nlinarith

/-- `λ_max(I) = 1`. -/
theorem lamMax_one [NeZero d] : lamMax (1 : Mat d) = 1 := by
  have he0 : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  refine le_antisymm ((lamMax_le_iff isHermitian_one 1).2 fun x hx => by
    rw [quad_one, hx, one_pow]) ?_
  have := quad_le_lamMax isHermitian_one he0
  rwa [quad_one, he0, one_pow] at this

/-- `λ_min(Σ) I ≤ Σ` for symmetric `Σ`. -/
theorem loewnerLE_lamMin_smul_one [NeZero d] {S : Mat d} (hSh : S.IsHermitian) :
    loewnerLE (lamMin S • (1 : Mat d)) S := by
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg (hSh.sub (isHermitian_one.smul (IsSelfAdjoint.all _)))
    fun x => ?_
  rw [quad_sub, quad_smul, quad_one]
  have h : lamMin S * ‖x‖ ^ 2 ≤ quad S x := lamMin_mul_norm_sq_le hSh x
  linarith

/-- **The condition number between two multiples of `I`**: `aI ≤ M ≤ bI` with `a > 0` gives
`cond M ≤ b/a`. -/
theorem condNum_le_of_sandwich [NeZero d] {M : Mat d} (hM : M.IsHermitian) {a b : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) (h1 : loewnerLE (a • (1 : Mat d)) M) (h2 : loewnerLE M (b • (1 : Mat d))) :
    condNum M ≤ ENNReal.ofReal (b / a) := by
  have hl : a ≤ lamMin M := by
    have := lamMin_mono (isHermitian_one.smul (IsSelfAdjoint.all _)) hM h1
    rwa [lamMin_smul ha.le, lamMin_one, mul_one] at this
  have hu : lamMax M ≤ b := by
    have := lamMax_mono hM (isHermitian_one.smul (IsSelfAdjoint.all _)) h2
    rwa [lamMax_smul hb, lamMax_one, mul_one] at this
  have hlpos : 0 < lamMin M := lt_of_lt_of_le ha hl
  rw [condNum, if_neg hlpos.ne']
  exact ENNReal.ofReal_le_ofReal (div_le_div₀ hb hu ha hl)

/-- `min(|x|², r²)` is integrable against a Lévy measure. -/
theorem IsLevyMeasure.integrable_min_sq {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ) :
    Integrable (fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2)) L :=
  Integrable.mono' (hL.integrable_min.const_mul (max 1 (r ^ 2)))
    (by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
      exact min_sq_le_max_mul _ r (sq_nonneg _))

/-- `T_r(L) = ∫ min(|x|², r²) L(dx)` is nondecreasing in `r ≥ 0`. -/
theorem momentTrace_mono {L : Measure (Rd d)} (hL : IsLevyMeasure L) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr' : r ≤ r') : momentTrace r L ≤ momentTrace r' L :=
  integral_mono (hL.integrable_min_sq r) (hL.integrable_min_sq r') fun _ =>
    min_le_min_left _ (pow_le_pow_left₀ hr hrr' 2)

/-- `T_r(L) > 0` for a Lévy measure `L ≠ 0` and `r > 0`. -/
theorem momentTrace_pos {L : Measure (Rd d)} (hL : IsLevyMeasure L) (hL0 : L ≠ 0) {r : ℝ}
    (hr : 0 < r) : 0 < momentTrace r L := by
  unfold momentTrace
  rw [integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (hL.integrable_min_sq r)]
  have hsupp : Function.support (fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2)) = {0}ᶜ := by
    ext x
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff]
    constructor
    · intro h hx; apply h; simp [hx, sq_nonneg r]
    · intro hx h
      exact (lt_min (pow_pos (norm_pos_iff.2 hx) 2) (pow_pos hr 2)).ne' h
  rw [hsupp, measure_compl (measurableSet_singleton 0) (by rw [hL.1]; simp), hL.1, tsub_zero]
  exact pos_iff_ne_zero.2 fun h => hL0 (Measure.measure_univ_eq_zero.1 h)

/-- `C(I) = c₀ I` with `c₀ ≥ 0`, for a family as in `prop:similarity-general-sandwich`. -/
theorem sim_general_C_one (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ C 1 = c0 • (1 : Mat d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hinv : ∀ Q ∈ orthSet d, act Q (C 1) = C 1 := fun Q hQ => by
    have h := ((sim_general_covariance hd μ C L hfam).1 1 PosDef.one 1 one_pos Q hQ).1
    rw [Matrix.mul_one, orth_mul_transpose hQ, one_smul, one_smul] at h
    exact h.symm
  exact ⟨C 1 0 0, (hfam.C_psd PosDef.one).diag_nonneg, eq_smul_one_of_orth_invariant hinv⟩

/-- **The sandwich between two multiples of `I`**, for a family as in
`prop:similarity-general-sandwich` whose steps `εI → Σ`, `Σ → tI` and `I → bI` (`b ≥ 1`) have
infinitely divisible increments: the four bounds and the three shape bounds of
`prop:similarity-stable-order-kernels`(2), with `t/ε` in place of the eccentricity term. -/
theorem sim_sandwich_of_steps (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hC1 : C 1 = c0 • (1 : Mat d))
    (hray : ∀ b : ℝ, 1 ≤ b → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      IsInfinitelyDivisible ρ ∧ μ (b • (1 : Mat d)) = μ 1 ∗ ρ)
    {S : Mat d} (hS : S.PosDef) {ε t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t)
    (hlo : ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
      μ S = μ (ε • (1 : Mat d)) ∗ ρ)
    (hhi : ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
      μ (t • (1 : Mat d)) = μ S ∗ ρ) :
    loewnerLE ((ε * c0) • (1 : Mat d)) (C S) ∧
      loewnerLE (C S) ((t * c0) • (1 : Mat d)) ∧
      push (Real.sqrt ε • (1 : Mat d)) (L 1) ≤ L S ∧
      L S ≤ push (Real.sqrt t • (1 : Mat d)) (L 1) ∧
      (∀ ω : Rd d, levyExp (L 1) (Real.sqrt ε • ω) ≤ levyExp (L S) ω ∧
        levyExp (L S) ω ≤ levyExp (L 1) (Real.sqrt t • ω)) ∧
      (0 < c0 → condNum (C S) ≤ ENNReal.ofReal (t / ε)) ∧
      (L 1 ≠ 0 → ∀ s : ℝ, 0 < s → condNum (momentMatrix s (L S)) ≤ ENNReal.ofReal (t / ε)) ∧
      expSpread (levyExp (L S)) ≤ ENNReal.ofReal (4 * (t / ε)) := by
  haveI : NeZero d := ⟨by omega⟩
  have ht : 0 < t := lt_of_lt_of_le hε hεt
  have hεI : (ε • (1 : Mat d)).PosDef := PosDef.one.smul hε
  have htI : (t • (1 : Mat d)).PosDef := PosDef.one.smul ht
  obtain ⟨ρ1, hρ1, hρ1id, heq1⟩ := hlo
  obtain ⟨ρ2, hρ2, hρ2id, heq2⟩ := hhi
  have hlo' := sim_general_id_increment hd μ C L hfam _ _ hεI hS ρ1 hρ1 hρ1id heq1
  have hhi' := sim_general_id_increment hd μ C L hfam _ _ hS htI ρ2 hρ2 hρ2id heq2
  have hCs : ∀ c : ℝ, 0 < c → C (c • (1 : Mat d)) = (c * c0) • (1 : Mat d) := fun c hc => by
    have h := ((sim_general_covariance hd μ C L hfam).1 1 PosDef.one c hc 1
      (Matrix.orthogonalGroup (Fin d) ℝ).one_mem).1
    simp only [Matrix.mul_one, transpose_one, Matrix.one_mul] at h
    rw [h, hC1, smul_smul]
  have hLs : ∀ c : ℝ, 0 < c → L (c • (1 : Mat d)) = push (Real.sqrt c • (1 : Mat d)) (L 1) :=
    fun c hc => (sim_general_scale hd hfam PosDef.one hc).1
  have hψs : ∀ c : ℝ, 0 < c → ∀ ω : Rd d,
      levyExp (L (c • (1 : Mat d))) ω = levyExp (L 1) (Real.sqrt c • ω) :=
    fun c hc => (sim_general_scale hd hfam PosDef.one hc).2
  have hCS1 : loewnerLE ((ε * c0) • (1 : Mat d)) (C S) := by rw [← hCs ε hε]; exact hlo'.1
  have hCS2 : loewnerLE (C S) ((t * c0) • (1 : Mat d)) := by rw [← hCs t ht]; exact hhi'.1
  have hL1 : push (Real.sqrt ε • (1 : Mat d)) (L 1) ≤ L S := by rw [← hLs ε hε]; exact hlo'.2.1
  have hL2 : L S ≤ push (Real.sqrt t • (1 : Mat d)) (L 1) := by rw [← hLs t ht]; exact hhi'.2.1
  have hψ : ∀ ω : Rd d, levyExp (L 1) (Real.sqrt ε • ω) ≤ levyExp (L S) ω ∧
      levyExp (L S) ω ≤ levyExp (L 1) (Real.sqrt t • ω) := fun ω =>
    ⟨by rw [← hψs ε hε]; exact hlo'.2.2 ω, by rw [← hψs t ht]; exact hhi'.2.2 ω⟩
  have hrot1 := (sim_general_covariance hd μ C L hfam).2.1
  have hLev1 : IsLevyMeasure (L 1) := hfam.isLevy PosDef.one
  have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨hCS1, hCS2, hL1, hL2, hψ, fun hc0' => ?_, fun hL0 s hs => ?_, ?_⟩
  · have := condNum_le_of_sandwich (hfam.C_psd hS).isHermitian (mul_pos hε hc0')
      (mul_nonneg ht.le hc0) hCS1 hCS2
    rwa [mul_div_mul_right _ _ hc0'.ne'] at this
  · have hT0 : ∀ r : ℝ, 0 ≤ momentTrace r (L 1) := fun r =>
      integral_nonneg fun x => le_min (sq_nonneg _) (sq_nonneg _)
    have hmom : ∀ c : ℝ, 0 < c → momentMatrix s (L (c • (1 : Mat d))) =
        (c * (momentTrace (s / Real.sqrt c) (L 1) / d)) • (1 : Mat d) := fun c hc => by
      rw [hLs c hc, momentMatrix_push hLev1 (Real.sqrt_pos.2 hc)
        (Matrix.orthogonalGroup (Fin d) ℝ).one_mem, Real.sq_sqrt hc.le, Matrix.one_mul,
        transpose_one, Matrix.mul_one, momentMatrix_rot hLev1 hrot1, smul_smul]
    have hlowM : loewnerLE ((ε * (momentTrace (s / Real.sqrt ε) (L 1) / d)) • (1 : Mat d))
        (momentMatrix s (L S)) := by
      rw [← hmom ε hε]
      exact momentMatrix_mono (hfam.isLevy hεI) (hfam.isLevy hS) hlo'.2.1 s
    have hupM : loewnerLE (momentMatrix s (L S))
        ((t * (momentTrace (s / Real.sqrt t) (L 1) / d)) • (1 : Mat d)) := by
      rw [← hmom t ht]
      exact momentMatrix_mono (hfam.isLevy hS) (hfam.isLevy htI) hhi'.2.1 s
    have hTε : 0 < momentTrace (s / Real.sqrt ε) (L 1) :=
      momentTrace_pos hLev1 hL0 (div_pos hs (Real.sqrt_pos.2 hε))
    have hTle : momentTrace (s / Real.sqrt t) (L 1) / d ≤
        momentTrace (s / Real.sqrt ε) (L 1) / d :=
      div_le_div_of_nonneg_right (momentTrace_mono hLev1 (div_nonneg hs.le (Real.sqrt_nonneg _))
        (div_le_div_of_nonneg_left hs.le (Real.sqrt_pos.2 hε) (Real.sqrt_le_sqrt hεt))) hd0.le
    have hTεd : 0 < momentTrace (s / Real.sqrt ε) (L 1) / d := div_pos hTε hd0
    have h := condNum_le_of_sandwich (momentMatrix_isHermitian s _) (mul_pos hε hTεd)
      (mul_nonneg ht.le (div_nonneg (hT0 _) hd0.le)) hlowM hupM
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (mul_pos hε hTεd) hε]
    have := mul_le_mul_of_nonneg_left hTle (mul_nonneg ht.le hε.le)
    nlinarith
  · have hrad : ∀ η η' : Rd d, ‖η‖ = ‖η'‖ → levyExp (L 1) η = levyExp (L 1) η' :=
      fun η η' h => levyExp_eq_of_norm_eq hrot1 h
    have hmono : ∀ (η : Rd d) (b : ℝ), 1 ≤ b → levyExp (L 1) η ≤ levyExp (L 1) (b • η) := by
      intro η b hb
      have hb0 : 0 < b := by linarith
      have hb2 : 1 ≤ b ^ 2 := by nlinarith
      obtain ⟨ρ, hρ, hρid, heq⟩ := hray _ hb2
      have := (sim_general_id_increment hd μ C L hfam _ _ PosDef.one
        (PosDef.one.smul (by positivity)) ρ hρ hρid heq).2.2 η
      rwa [hψs _ (by positivity), Real.sqrt_sq hb0.le] at this
    have h0 : levyExp (L 1) 0 = 0 := by simp [levyExp, levyExpL]
    have hc1 : 1 ≤ t / ε := (one_le_div hε).2 hεt
    refine expSpread_le (by linarith) fun R hR ω => ?_
    have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    calc levyExp (L S) (lin R ω) ≤ levyExp (L 1) (Real.sqrt t • lin R ω) := (hψ _).2
      _ ≤ 4 * (t / ε) * levyExp (L 1) (Real.sqrt ε • ω) :=
          le_four_mul_of_doubling h0 (levyExp_nonneg _) hrad hmono (levyExp_two_smul_le hLev1)
            hc1 (le_of_eq (by
              rw [norm_smul, norm_smul, norm_lin_of_orth hR,
                Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hsε.le,
                Real.sqrt_div ht.le]
              field_simp))
      _ ≤ 4 * (t / ε) * levyExp (L S) ω :=
          mul_le_mul_of_nonneg_left (hψ ω).1 (by positivity)

/-- **`prop:similarity-stable-order-kernels`(2)**, the sandwich and the shape, along `≤_α`: in the
setting of (1), with `ε := ε_α(Σ)`, `t := t_α(Σ)`, `C(I) = c₀I` with `c₀ ≥ 0`,
`εc₀I ≤ C(Σ) ≤ tc₀I`, `(√ε I)_*L_I ≤ L_Σ ≤ (√t I)_*L_I`,
`ψ_I(√ε ω) ≤ ψ_Σ(ω) ≤ ψ_I(√t ω)`; so `cond C(Σ) ≤ ecc(Σ)^{(d+α)/α}` if `c₀ > 0`,
`cond 𝓜_s(L_Σ) ≤ ecc(Σ)^{(d+α)/α}` if `L_I ≠ 0`, and `es(ψ_Σ) ≤ 4 ecc(Σ)^{(d+α)/α}`. -/
theorem stable_order_sandwich (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (G : Set (Mat d)) (hG : IsClosedSubgroupGL G) (hsim : simSet d ⊆ G)
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G (stablePlusLE α) μ)
    (C : Mat d → Mat d) (L : Mat d → Measure (Rd d))
    (hfam : IsSimGeneralFamily (fun S => μ 0 S) C L) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ C 1 = c0 • (1 : Mat d) ∧ ∀ S : Mat d, S.PosDef →
      loewnerLE ((epsAlpha α S * c0) • (1 : Mat d)) (C S) ∧
      loewnerLE (C S) ((tAlpha α S * c0) • (1 : Mat d)) ∧
      push (Real.sqrt (epsAlpha α S) • (1 : Mat d)) (L 1) ≤ L S ∧
      L S ≤ push (Real.sqrt (tAlpha α S) • (1 : Mat d)) (L 1) ∧
      (∀ ω : Rd d, levyExp (L 1) (Real.sqrt (epsAlpha α S) • ω) ≤ levyExp (L S) ω ∧
        levyExp (L S) ω ≤ levyExp (L 1) (Real.sqrt (tAlpha α S) • ω)) ∧
      (0 < c0 → condNum (C S) ≤ ENNReal.ofReal (ecc S ^ (((d : ℝ) + α) / α))) ∧
      (L 1 ≠ 0 → ∀ s : ℝ, 0 < s →
        condNum (momentMatrix s (L S)) ≤ ENNReal.ofReal (ecc S ^ (((d : ℝ) + α) / α))) ∧
      expSpread (levyExp (L S)) ≤ ENNReal.ofReal (4 * ecc S ^ (((d : ℝ) + α) / α)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, hray, -, -, -, -, heps, htα, hratio⟩ := stablePlusLE_order hd hα0 hα2
  obtain ⟨-, -, -, hinc⟩ := stable_order_sim_kernels hd hα0 hα2 G hG hsim μ hμ
  have hstep : ∀ S S' : Mat d, S.PosDef → S'.PosDef → stablePlusLE α S S' →
      ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
        μ 0 S' = μ 0 S ∗ ρ :=
    fun S S' hS hS' h => ⟨μ S S', hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, h⟩,
      (hinc S S' hS hS' h).1, (hinc S S' hS hS' h).2⟩
  obtain ⟨c0, hc0, hC1⟩ := sim_general_C_one hd hfam
  refine ⟨c0, hc0, hC1, fun S hS => ?_⟩
  have hD := hS.det_pos
  have hlm := lamMin_pos hS
  have hεp : 0 < epsAlpha α S := by unfold epsAlpha; positivity
  have hecc : 1 ≤ ecc S ^ (((d : ℝ) + α) / α) := Real.one_le_rpow
    (by unfold ecc; rw [one_le_div hlm]; exact lamMin_le_lamMax hS.isHermitian) (by positivity)
  have hεt : epsAlpha α S ≤ tAlpha α S := by
    have : 1 ≤ tAlpha α S / epsAlpha α S := by rw [hratio S hS]; exact hecc
    rwa [one_le_div hεp] at this
  have h := sim_sandwich_of_steps hd hfam hc0 hC1
    (fun b hb => hstep _ _ PosDef.one (PosDef.one.smul (by linarith)) (by
      have := hray 1 PosSemidef.one 1 b zero_le_one hb
      rwa [one_smul] at this))
    hS hεp hεt (hstep _ _ (PosDef.one.smul hεp) hS ((heps S hS _ hεp.le).2 le_rfl))
    (hstep _ _ hS (PosDef.one.smul (hεp.trans_le hεt)) ((htα S hS _ (hεp.le.trans hεt)).2 le_rfl))
  rw [hratio S hS] at h
  exact h

/-- **`prop:similarity-stable-order-kernels`(2)**, the Loewner reading: for a
`(G, Loewner)`-cascade family the same holds with `ε := λ_min(Σ)`, `t := λ_max(Σ)` and `ecc(Σ)` in
place of `ecc(Σ)^{(d+α)/α}`. -/
theorem loewner_order_sandwich (hd : 2 ≤ d) (G : Set (Mat d)) (hG : IsClosedSubgroupGL G)
    (hsim : simSet d ⊆ G) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G loewnerLE μ) (C : Mat d → Mat d) (L : Mat d → Measure (Rd d))
    (hfam : IsSimGeneralFamily (fun S => μ 0 S) C L) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ C 1 = c0 • (1 : Mat d) ∧ ∀ S : Mat d, S.PosDef →
      loewnerLE ((lamMin S * c0) • (1 : Mat d)) (C S) ∧
      loewnerLE (C S) ((lamMax S * c0) • (1 : Mat d)) ∧
      push (Real.sqrt (lamMin S) • (1 : Mat d)) (L 1) ≤ L S ∧
      L S ≤ push (Real.sqrt (lamMax S) • (1 : Mat d)) (L 1) ∧
      (∀ ω : Rd d, levyExp (L 1) (Real.sqrt (lamMin S) • ω) ≤ levyExp (L S) ω ∧
        levyExp (L S) ω ≤ levyExp (L 1) (Real.sqrt (lamMax S) • ω)) ∧
      (0 < c0 → condNum (C S) ≤ ENNReal.ofReal (ecc S)) ∧
      (L 1 ≠ 0 → ∀ s : ℝ, 0 < s → condNum (momentMatrix s (L S)) ≤ ENNReal.ofReal (ecc S)) ∧
      expSpread (levyExp (L S)) ≤ ENNReal.ofReal (4 * ecc S) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, -, hinc⟩ := sim_cascade_infinitelyDivisible hd G hG hsim μ hμ
  have hstep : ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
      ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
        μ 0 S' = μ 0 S ∗ ρ :=
    fun S S' hS hS' h => ⟨μ S S', hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, h⟩,
      (hinc S S' hS hS' h).1, (hinc S S' hS hS' h).2⟩
  obtain ⟨c0, hc0, hC1⟩ := sim_general_C_one hd hfam
  refine ⟨c0, hc0, hC1, fun S hS => ?_⟩
  have hlm := lamMin_pos hS
  have hεt := lamMin_le_lamMax hS.isHermitian
  have h := sim_sandwich_of_steps hd hfam hc0 hC1
    (fun b hb => hstep _ _ PosDef.one (PosDef.one.smul (by linarith)) (by
      unfold loewnerLE
      rw [show b • (1 : Mat d) - 1 = (b - 1) • (1 : Mat d) by rw [sub_smul, one_smul]]
      exact PosSemidef.one.smul (by linarith)))
    hS hlm hεt (hstep _ _ (PosDef.one.smul hlm) hS (loewnerLE_lamMin_smul_one hS.isHermitian))
    (hstep _ _ hS (PosDef.one.smul (hlm.trans_le hεt)) (loewnerLE_lamMax_smul_one hS.isHermitian))
  have hecc : lamMax S / lamMin S = ecc S := rfl
  rw [hecc] at h
  exact h

/-! ## Clause (5) -/

/-- **The stable orbit's transform**: `(Σ^{1/2})_*S_α(I)` has transform `e^{-⟨ω,Σω⟩^{α/2}}` for
every `Σ ∈ PSD(d)`, singular or not. -/
theorem charFun_affineOrbit_stable {α : ℝ} {σI : Measure (Rd d)}
    (hσI : IsEllipticalStable α 1 σI) {S : Mat d} (hS : S.PosSemidef) (ω : Rd d) :
    charFun (affineOrbit σI S) ω = ((Real.exp (-stableExp α S ω) : ℝ) : ℂ) := by
  rw [affineOrbit, push, charFun_map_lin, hσI.2, ← stableExp_act, act_msqrt_one hS]

/-- **`prop:similarity-stable-order-kernels`(3)**, the cell is not the union of its neighbours:
for `b, κ > 0`, `S_α(Σ) := (Σ^{1/2})_*S_α(I)` and
`μ_Σ := N(0, 2b(Σ + κ tr(Σ) I)) * S_α(Σ)`, `(μ_Σ)` is the family of kernels from the origin of an
`(S(d), ≤_α)`-cascade family; it is not `GL(d)`-covariant, hence the kernels of no
`(GL(d), ≤_α)`-family; for `P ∈ PSD(d)` with `0 < rank P < d` no positive finite `ρ` has
`μ_{I+P} = μ_I * ρ`, so it is the family of kernels of no `(S(d), Loewner)`-cascade family.
Spends A3(iii). -/
theorem stable_order_cell_strict (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (b κ : ℝ)
    (hb : 0 < b) (hκ : 0 < κ) (σI : Measure (Rd d)) (hσI : IsEllipticalStable α 1 σI) :
    let μ : Mat d → Measure (Rd d) := fun S =>
      multivariateGaussian 0 ((2 * b) • (S + (κ * S.trace) • (1 : Mat d))) ∗ affineOrbit σI S
    IsKernelsFromOrigin (simSet d) (stablePlusLE α) μ ∧
      ¬ (∀ A ∈ glSet d, ∀ S : Mat d, S.PosSemidef → push A (μ S) = μ (act A S)) ∧
      ¬ IsKernelsFromOrigin (glSet d) (stablePlusLE α) μ ∧
      (∀ P : Mat d, P.PosSemidef → 0 < P.rank → P.rank < d →
        ¬ ∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ μ (1 + P) = μ 1 ∗ ρ) ∧
      ¬ IsKernelsFromOrigin (simSet d) loewnerLE μ := by
  haveI : NeZero d := ⟨by omega⟩
  intro μ
  haveI := hσI.1
  have hord := stablePlusLE_order hd hα0 hα2
  have hHpsd : ∀ S : Mat d, S.PosSemidef → (traceGauge κ S).PosSemidef := fun S hS =>
    hS.add (PosSemidef.one.smul (mul_nonneg hκ.le hS.trace_nonneg))
  have hμdef : ∀ S : Mat d, μ S =
      multivariateGaussian 0 ((2 * b) • traceGauge κ S) ∗ affineOrbit σI S := fun S => rfl
  have hprob : ∀ S : Mat d, IsProbabilityMeasure (μ S) := fun S => by
    rw [hμdef]; infer_instance
  -- the transform `exp[-b⟨ω, h(Σ)ω⟩ - ⟨ω, Σω⟩^{α/2}]`
  have hchar : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d, charFun (μ S) ω =
      ((Real.exp (-(b * quad (traceGauge κ S) ω + stableExp α S ω)) : ℝ) : ℂ) := by
    intro S hS ω
    rw [hμdef, charFun_conv, charFun_multivariateGaussian_zero ((hHpsd S hS).smul (by positivity)),
      charFun_affineOrbit_stable hσI hS, ← Complex.ofReal_mul, ← Real.exp_add, quad_smul]
    congr 2
    ring
  have he0 : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hW : IsWedgeDatum (simSet d) (stablePlusLE α) :=
    hord.2.2.2.2.2.1 _ simSet_isClosedSubgroupGL.1 simSet_isClosedSubgroupGL.2
  -- (a)–(c) of `lem:gw-kernels-from-origin`(2)
  have hm : IsOriginKernels (simSet d) μ := by
    refine ⟨fun S _ => hprob S, ?_, ?_, ?_, ?_⟩
    · haveI := hprob 0
      refine eq_of_charFun_eq fun ω => ?_
      rw [hchar 0 PosSemidef.zero, traceGauge_zero, quad_zero, stableExp_zero_mat hα0,
        charFun_dirac]
      simp
    · intro h1
      have h := congrArg (fun m => charFun m (ebasis (0 : Fin d))) h1
      rw [hchar 1 PosSemidef.one, charFun_dirac] at h
      simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
      have h2 : Real.exp (-(b * quad (traceGauge κ (1 : Mat d)) (ebasis 0) +
          stableExp α (1 : Mat d) (ebasis 0))) = 1 := by exact_mod_cast h
      rw [Real.exp_eq_one_iff] at h2
      have hq : 0 ≤ quad (traceGauge κ (1 : Mat d)) (ebasis 0) :=
        quad_nonneg (hHpsd 1 PosSemidef.one) _
      have hs : stableExp α 1 (ebasis (0 : Fin d)) = 1 := by
        rw [stableExp, quad_one, he0, one_pow, Real.one_rpow]
      nlinarith
    · intro A hA S hS
      haveI := hprob S
      haveI := hprob (act A S)
      refine eq_of_charFun_eq fun ω => ?_
      rw [push, charFun_map_lin, hchar S hS, hchar _ (posSemidef_act A hS),
        traceGauge_act_sim κ hA, quad_act, stableExp_act]
    · intro ω
      have hc : Continuous fun S : Mat d =>
          ((Real.exp (-(b * quad (traceGauge κ S) ω + stableExp α S ω)) : ℝ) : ℂ) := by
        refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
        refine ((((continuous_quad ω).comp (continuous_traceGauge κ)).const_mul b).add ?_).neg
        unfold stableExp
        exact (Real.continuous_rpow_const (by positivity)).comp (continuous_quad ω)
      exact hc.continuousOn.congr fun S hS => hchar S hS ω
  have hz : HasNoZeros μ := fun S hS ω => by
    rw [hchar S hS ω]
    exact_mod_cast (Real.exp_pos _).ne'
  -- (d): an increment from a stable increment and the Gaussian of `h(Σ') - h(Σ)`
  have hincr : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      (∃ τ : Measure (Rd d), IsProbabilityMeasure τ ∧ ∀ ω : Rd d,
        charFun τ ω = ((Real.exp (-(stableExp α S' ω - stableExp α S ω)) : ℝ) : ℂ)) →
      ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ μ S' = μ S ∗ ρ := by
    rintro S S' hS hS' hle ⟨τ, hτ, hτc⟩
    haveI := hτ
    have hle' : (S' - S).PosSemidef := hle
    have hP : (traceGauge κ S' - traceGauge κ S).PosSemidef := by
      have : traceGauge κ S' - traceGauge κ S =
          (S' - S) + (κ * (S' - S).trace) • (1 : Mat d) := by
        simp only [traceGauge, trace_sub]
        rw [mul_sub, sub_smul]
        abel
      rw [this]
      exact hle'.add (PosSemidef.one.smul (mul_nonneg hκ.le hle'.trace_nonneg))
    refine ⟨multivariateGaussian 0 ((2 * b) • (traceGauge κ S' - traceGauge κ S)) ∗ τ,
      inferInstance, ?_⟩
    haveI := hprob S
    haveI := hprob S'
    refine eq_of_charFun_eq fun ω => ?_
    rw [hchar S' hS', charFun_conv, hchar S hS, charFun_conv,
      charFun_multivariateGaussian_zero (hP.smul (by positivity)), hτc, quad_smul, quad_sub]
    simp only [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  -- the stable increments: clause (2) at `β = α`
  have hWgl : IsWedgeDatum (glSet d) (stablePlusLE α) :=
    hord.2.2.2.2.2.1 _ glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  obtain ⟨ν, hν, hν0⟩ := (stable_order_gl_row_examples hd hα0 hα2).1 α le_rfl hα2 σI hσI
  have hinc : HasIncrements (stablePlusLE α) μ := by
    intro S S' hS hS' hle
    refine hincr S S' hS hS' (stablePlusLE_loewner hα0 hα2 hS hS' hle) ?_
    obtain ⟨hp, hc⟩ := (gw_kernels_from_origin hWgl ν hν).2 S S' hS hS' hle
    haveI := hp
    refine ⟨ν S S', hp, fun ω => ?_⟩
    have h := congrArg (fun m => charFun m ω) hc
    rw [hν0 S' hS', hν0 S hS, charFun_conv, charFun_affineOrbit_stable hσI hS',
      charFun_affineOrbit_stable hσI hS] at h
    have hne : ((Real.exp (-stableExp α S ω) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    rw [show -(stableExp α S' ω - stableExp α S ω) = -stableExp α S' ω - (-stableExp α S ω) by ring,
      Real.exp_sub, Complex.ofReal_div, h, mul_div_cancel_left₀ _ hne]
  -- the rank-one diagonal matrix `e₁e₁ᵀ`
  set D : Mat d := diagonal (Pi.single 0 1) with hD
  have hDpsd : D.PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  have hqD : quad D (ebasis 0) = 1 := by
    rw [hD, quad_diagonal_single]
    simp [ebasis]
  have hq1 : quad (1 : Mat d) (ebasis 0) = 1 := by rw [quad_one, he0, one_pow]
  have htrD : D.trace = 1 := by simp [hD, Matrix.trace_diagonal]
  -- not `GL(d)`-covariant: `A := (I + e₁e₁ᵀ)^{1/2}` at `ω = e₁`
  have hnotGL : ¬ (∀ A ∈ glSet d, ∀ S : Mat d, S.PosSemidef → push A (μ S) = μ (act A S)) := by
    intro hcov
    have hMpd : (1 + D).PosDef := PosDef.one.add_posSemidef hDpsd
    have hAM : act (msqrt (1 + D)) 1 = 1 + D := act_msqrt_one hMpd.posSemidef
    have h := congrArg (fun m => charFun m (ebasis (0 : Fin d)))
      (hcov _ (msqrt_mem_glSet hMpd) 1 PosSemidef.one)
    rw [push, charFun_map_lin, hchar 1 PosSemidef.one, hchar _ (posSemidef_act _ PosSemidef.one),
      ← quad_act, ← stableExp_act, traceGauge, traceGauge, act_add, act_smul, hAM] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    simp only [quad_add, quad_smul, hq1, hqD, trace_add, trace_one, htrD, Fintype.card_fin] at h2
    have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_pos (mul_pos hb hκ) (by linarith : (0 : ℝ) < d - 1)]
  -- no rank-deficient step
  have hnorank : ∀ P : Mat d, P.PosSemidef → 0 < P.rank → P.rank < d →
      ¬ ∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ μ (1 + P) = μ 1 ∗ ρ := by
    rintro P hP hr0 hrd ⟨ρ, hρ, heq⟩
    haveI := hρ
    haveI := hprob 1
    have h1P : (1 + P).PosDef := PosDef.one.add_posSemidef hP
    have hρc : ∀ ω : Rd d, charFun ρ ω =
        ((Real.exp (-quad (b • (P + (κ * P.trace) • (1 : Mat d))) ω - stableExp α (1 + P) ω +
          stableExp α 1 ω) : ℝ) : ℂ) := by
      intro ω
      have h := congrArg (fun m => charFun m ω) heq
      rw [hchar _ h1P.posSemidef, charFun_conv, hchar 1 PosSemidef.one] at h
      have hne : ((Real.exp (-(b * quad (traceGauge κ (1 : Mat d)) ω + stableExp α 1 ω)) : ℝ) :
          ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
      have h' : charFun ρ ω =
          ((Real.exp (-(b * quad (traceGauge κ (1 + P)) ω + stableExp α (1 + P) ω)) : ℝ) : ℂ) /
            ((Real.exp (-(b * quad (traceGauge κ (1 : Mat d)) ω + stableExp α 1 ω)) : ℝ) : ℂ) := by
        rw [eq_div_iff hne, mul_comm]
        exact h.symm
      rw [h', ← Complex.ofReal_div, ← Real.exp_sub]
      congr 2
      simp only [traceGauge, quad_add, quad_smul, trace_add]
      ring
    obtain ⟨-, -, hdens⟩ := stable_tail hα0 hα2 PosDef.one h1P ρ hρc
    exact (stableLE_rays_not_rank_deficient hα0 hα2).2 1 P PosDef.one hP hr0 hrd
      ((stableLE_iff_density hα0 hα2 PosDef.one h1P).2 hdens)
  refine ⟨(gw_kernels_from_origin_converse hW μ hm hz hinc).1, hnotGL, ?_, hnorank, ?_⟩
  · rintro ⟨ν, hν, hν0⟩
    apply hnotGL
    intro A hA S hS
    have := (gw_kernels_from_origin hWgl ν hν).1.covariant A hA S hS
    rwa [hν0 S hS, hν0 _ (posSemidef_act A hS)] at this
  · rintro ⟨ν, hν, hν0⟩
    have hrank : D.rank = 1 := by
      classical
      rw [hD, rank_diagonal, Fintype.card_eq_one_iff]
      refine ⟨⟨0, by simp⟩, ?_⟩
      rintro ⟨j, hj⟩
      apply Subtype.ext
      by_contra hne
      exact hj (by simp [hne])
    have hW' : IsWedgeDatum (simSet d) loewnerLE :=
      isWedgeDatum_loewner simSet_isClosedSubgroupGL.1 simSet_isClosedSubgroupGL.2
    have hIP : loewnerLE (1 : Mat d) (1 + D) := by
      rw [loewnerLE, add_sub_cancel_left]
      exact hDpsd
    obtain ⟨hp, hc⟩ := (gw_kernels_from_origin hW' ν hν).2 1 (1 + D) PosSemidef.one
      (PosSemidef.one.add hDpsd) hIP
    haveI := hp
    refine hnorank D hDpsd (by rw [hrank]; norm_num) (by rw [hrank]; omega)
      ⟨ν 1 (1 + D), inferInstance, ?_⟩
    rw [← hν0 _ (PosSemidef.one.add hDpsd), ← hν0 1 PosSemidef.one]
    exact hc

end AffineHemigroup
