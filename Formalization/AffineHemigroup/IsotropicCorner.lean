/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ParameterSpace
import AffineHemigroup.RayFamilies
import AffineHemigroup.MarginalFamily
import AffineHemigroup.GaussVar
import AffineHemigroup.Upstream
import AffineHemigroup.GaugeFacts

/-!
# `prop:isotropic-corner`: the slice of the isotropic corner is the isotropic theory

Blueprint: `blueprint/src/parts/04-classical.tex`, `prop:isotropic-corner`. Wave 2, group C,
Q-0281.

## The route

The blueprint's. The fact used twice ([V, Lem. 6.3]'s argument) is
`eq_dirac_of_push_smul_eq`. Clause (2) reads the shared library's `ScaleSpace.canonical_gauge`
([V, Prop. 6.6]) on the marginal family of `lem:isotropic-marginal-family` for the gauge, and then works for every gauge
with the relation (`isotropic_corner_gauge_forall`): the isotropic member is `m := μ_{0,t₁}` with
`χ(t₁) = 1`, and the family is the one of `prop:gw-ray-families`(3) through `m`. The similarities
`S(d)` are shown to be a closed subgroup of `GL(d)` here (`simSet_isClosedSubgroupGL`), which is
the part of `prop:similarity-ray-families`(1) that clause (4) needs; the two families of (4) are
the affine orbit and the shape-blind family of `m`, and they differ off the multiples of `I`
because `Stab(m) = O(d)` (`lem:parameter-space`(2)).
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Helpers -/

theorem smul_one_mul_smul_one (a b : ℝ) :
    (a • (1 : Mat d)) * (b • (1 : Mat d)) = (a * b) • (1 : Mat d) := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

/-- The image of `δ₀` under a matrix is `δ₀`. -/
theorem push_dirac_zero (A : Mat d) : push A (Measure.dirac (0 : Rd d)) = Measure.dirac 0 := by
  refine eq_of_charFun_eq fun ω => ?_
  rw [push, charFun_map_lin, charFun_dirac, charFun_dirac]
  simp

/-- The image of a probability measure under the zero matrix is `δ₀`. -/
theorem push_zero_mat (m : Measure (Rd d)) [IsProbabilityMeasure m] :
    push (0 : Mat d) m = Measure.dirac 0 := by
  have h : (lin (0 : Mat d) : Rd d → Rd d) = fun _ => 0 := by
    funext x
    apply WithLp.ofLp_injective 2
    rw [ofLp_lin]
    simp
  rw [push, h, Measure.map_const, measure_univ, one_smul]

/-- `(c⁻¹I)_*(cI)_*m = m` for `c ≠ 0`. -/
theorem push_smul_one_inv_cancel {c : ℝ} (hc : c ≠ 0) (m : Measure (Rd d)) :
    push (c⁻¹ • (1 : Mat d)) (push (c • (1 : Mat d)) m) = m := by
  rw [push_push, smul_one_mul_smul_one, inv_mul_cancel₀ hc, one_smul, push_one]

/-- **A law fixed by one dilation `a ≠ 1` is `δ₀`** ([V, Lem. 6.3]'s argument): its transform is
constant along `ξ, aξ, a²ξ, …` and continuous at `0`. -/
theorem eq_dirac_of_push_smul_eq (m : Measure (Rd d)) [IsProbabilityMeasure m] {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) (h : push (a • (1 : Mat d)) m = m) : m = Measure.dirac 0 := by
  have hfix : ∀ ξ : Rd d, charFun m (a • ξ) = charFun m ξ := fun ξ => by
    rw [← charFun_push_smul_one, h]
  obtain ⟨b, hb0, hb1, hbfix⟩ : ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ ξ : Rd d, charFun m (b • ξ) = charFun m ξ := by
    rcases lt_or_gt_of_ne ha1 with h1 | h1
    · exact ⟨a, ha, h1, hfix⟩
    · refine ⟨a⁻¹, inv_pos.2 ha, inv_lt_one_of_one_lt₀ h1, fun ξ => ?_⟩
      rw [← hfix (a⁻¹ • ξ), smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hpow : ∀ (n : ℕ) (ξ : Rd d), charFun m ((b ^ n) • ξ) = charFun m ξ := by
    intro n
    induction n with
    | zero => intro ξ; simp
    | succ n ih => intro ξ; rw [pow_succ, mul_smul, ih, hbfix]
  refine eq_of_charFun_eq fun ξ => ?_
  have ht : Tendsto (fun n : ℕ => charFun m ((b ^ n) • ξ)) atTop (𝓝 (charFun m 0)) := by
    have h0 : Tendsto (fun n : ℕ => (b ^ n) • ξ) atTop (𝓝 (0 : Rd d)) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).smul_const ξ
      simpa using this
    exact (continuous_charFun.tendsto 0).comp h0
  simp only [hpow] at ht
  rw [tendsto_const_nhds_iff.1 ht, charFun_zero, charFun_dirac]
  simp

/-- **The kernels from the origin on the slice**: for a `(G, W)`-cascade family,
`ν_{uI} = (√u I)_*ν_I` for `u ≥ 0`, by (K3) at the dilation `√u I` and (K1) at `u = 0`. -/
theorem gw_kernel_smul_one {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (ν : Mat d → Mat d → Measure (Rd d)) (hν : IsGWCascadeFamily G le ν)
    {u : ℝ} (hu : 0 ≤ u) : ν 0 (u • (1 : Mat d)) = push (Real.sqrt u • (1 : Mat d)) (ν 0 1) := by
  have h01 := wedge_zero_one_mem hW
  haveI : IsProbabilityMeasure (ν 0 1) := hν.isProbability _ h01
  rcases hu.lt_or_eq with hu | hu
  · have h := hν.covariant _ (hW.dilations _ (Real.sqrt_pos.2 hu)) _ h01
    dsimp only at h
    rw [h, act_zero, act_smul_one, Real.sq_sqrt hu.le]
  · subst hu
    rw [zero_smul, Real.sqrt_zero, zero_smul, push_zero_mat, hν.diag 0 PosSemidef.zero]

/-- A `(GL(d), W)`-cascade family is a `(G, W)`-cascade family for every `G ⊆ GL(d)`: only (K3)
changes, and it is asked for fewer matrices. -/
theorem gw_family_of_subset {G G' : Set (Mat d)} {le : Mat d → Mat d → Prop} (hG : G ⊆ G')
    (ν : Mat d → Mat d → Measure (Rd d)) (hν : IsGWCascadeFamily G' le ν) :
    IsGWCascadeFamily G le ν :=
  ⟨hν.isProbability, hν.diag, hν.cascade, hν.continuous, fun A hA => hν.covariant A (hG hA),
    hν.nondegenerate⟩

/-! ## Clause (1): the slice -/

/-- **`prop:isotropic-corner`(1)**: if `O(d) ⊆ G`, the slice `(ν_{sI,tI})` of a
`(G, W)`-cascade family of kernels is an isotropic cascade family with `S_λ s = λ² s`; in
particular `ν_{sI,tI} ≠ δ₀` for `s < t`. -/
theorem isotropic_corner_slice (_hd : 1 ≤ d) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (hO : orthSet d ⊆ G) (ν : Mat d → Mat d → Measure (Rd d))
    (hν : IsGWCascadeFamily G le ν) :
    IsIsotropicCascadeFamily (fun s t => ν (s • (1 : Mat d)) (t • 1))
      (fun lam s => lam ^ 2 * s) := by
  have hpsd : ∀ s : ℝ, 0 ≤ s → (s • (1 : Mat d)).PosSemidef := fun s hs => PosSemidef.one.smul hs
  have hle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → le (s • (1 : Mat d)) (t • 1) := fun s t hs hst =>
    hW.rays 1 PosSemidef.one s t hs hst
  have hmem : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ((s • (1 : Mat d)), (t • (1 : Mat d))) ∈ wedgePairs le :=
    fun s t hs hst => ⟨hpsd s hs, hpsd t (hs.trans hst), hle s t hs hst⟩
  have h01 := wedge_zero_one_mem hW
  haveI : IsProbabilityMeasure (ν 0 1) := hν.isProbability _ h01
  refine ⟨fun s t hs hst => hν.isProbability _ (hmem s t hs hst), fun t ht => hν.diag _ (hpsd t ht),
    fun r s t hr hrs hst => hν.cascade _ _ _ (hpsd r hr) (hpsd s (hr.trans hrs))
      (hpsd t ((hr.trans hrs).trans hst)) (hle r s hr hrs) (hle s t (hr.trans hrs) hst),
    fun ξ => ?_, fun Q hQ s t hs hst => ?_, fun lam hlam => ?_, fun lam hlam s t hs hst => ?_,
    fun s t hs hst h => ?_⟩
  · -- (I2)
    have hc : Continuous fun p : ℝ × ℝ => (p.1 • (1 : Mat d), p.2 • (1 : Mat d)) :=
      (continuous_fst.smul continuous_const).prodMk (continuous_snd.smul continuous_const)
    exact (hν.continuous ξ).comp hc.continuousOn fun p hp => hmem p.1 p.2 hp.1 hp.2
  · -- (I3)
    have h := hν.covariant Q (hO hQ) _ (hmem s t hs hst)
    dsimp only at h
    rw [h, act_smul, act_smul, act_orth_one hQ]
  · -- (I4), the action
    have hl2 : 0 < lam ^ 2 := by positivity
    refine ⟨fun x hx => mul_nonneg hl2.le hx, fun x _ y _ hxy => mul_lt_mul_of_pos_left hxy hl2,
      fun y hy => ⟨y / lam ^ 2, div_nonneg hy hl2.le, by field_simp⟩⟩
  · -- (I4), the covariance
    have h := hν.covariant _ (hW.dilations lam hlam) _ (hmem s t hs hst)
    dsimp only at h
    rw [h, act_smul_one, act_smul_one, smul_smul, smul_smul]
  · -- (ND)
    have hne := hν.nondegenerate
    have ht : 0 < t := lt_of_le_of_lt hs hst
    have hcasc := hν.cascade 0 (s • 1) (t • 1) PosSemidef.zero (hpsd s hs) (hpsd t ht.le)
      (by simpa using hle 0 s le_rfl hs) (hle s t hs hst.le)
    haveI : IsProbabilityMeasure (ν 0 (s • 1)) :=
      hν.isProbability ((0 : Mat d), s • (1 : Mat d))
        ⟨PosSemidef.zero, hpsd s hs, by simpa using hle 0 s le_rfl hs⟩
    rw [h, Measure.dirac_zero_conv] at hcasc
    rw [gw_kernel_smul_one hW ν hν ht.le, gw_kernel_smul_one hW ν hν hs] at hcasc
    have hst' : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
    have h2 := congrArg (push ((Real.sqrt t)⁻¹ • (1 : Mat d))) hcasc
    rw [push_smul_one_inv_cancel hst', push_push, smul_one_mul_smul_one] at h2
    rcases hs.lt_or_eq with hs' | hs'
    · refine hne (eq_dirac_of_push_smul_eq (ν 0 1) (a := (Real.sqrt t)⁻¹ * Real.sqrt s)
        (mul_pos (inv_pos.2 (Real.sqrt_pos.2 ht)) (Real.sqrt_pos.2 hs')) ?_ h2.symm)
      intro h1
      have : Real.sqrt s = Real.sqrt t := by
        field_simp at h1
        linarith
      have := (Real.sqrt_inj hs ht.le).1 this
      linarith
    · subst hs'
      rw [Real.sqrt_zero, mul_zero, zero_smul, push_zero_mat] at h2
      exact hne h2

/-! ## Gauges -/

/-- The point `t₁ ≥ 0` with `χ(t₁) = 1`; it is positive. -/
theorem IsGauge.exists_eq_one {χ : ℝ → ℝ} (hχ : IsGauge χ) : ∃ t₁ : ℝ, 0 < t₁ ∧ χ t₁ = 1 := by
  obtain ⟨t₁, ht₁, hχ1⟩ := hχ.2.2 (mem_Ici.2 (zero_le_one : (0 : ℝ) ≤ 1))
  refine ⟨t₁, lt_of_le_of_ne (mem_Ici.1 ht₁) ?_, hχ1⟩
  rintro rfl
  rw [hχ.1] at hχ1
  exact zero_ne_one hχ1

/-- The similarities are invertible. -/
theorem simSet_subset_glSet : simSet d ⊆ glSet d := by
  rintro _ ⟨c, hc, Q, hQ, rfl⟩
  have hQ' : IsUnit Q.det := orthSet_subset_glSet hQ
  change IsUnit (c • Q).det
  rw [det_smul]
  exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hc.ne')).mul hQ'

theorem glSet_isWedgeDatum_ray : IsWedgeDatum (glSet d) rayLE :=
  isWedgeDatum_ray glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2

/-! ## Clause (2): every isotropic family is a slice -/

/-- **`prop:isotropic-corner`(2)**, for every gauge (blind review R1-3): for an isotropic cascade
family with dilation action `S` and **every** gauge `χ` with `χ(S_λ t) = λχ(t)`, there is exactly
one (on the pairs) `(GL(d), rays)`-cascade family `ν` with `μ_{s,t} = ν_{χ(s)²I, χ(t)²I}`, and `ν`
is also an `(S(d), rays)`-cascade family. -/
theorem isotropic_corner_gauge_forall (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (S : ℝ → ℝ → ℝ) (hμ : IsIsotropicCascadeFamily μ S) (χ : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t) :
    ∃ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE ν ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1)) ∧
      (∀ ν' : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE ν' →
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν' ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1)) →
        EqOnPairs rayLE ν ν') ∧
      IsGWCascadeFamily (simSet d) rayLE ν := by
  haveI : NeZero d := ⟨by omega⟩
  have hinj : InjOn χ (Ici 0) := hχ.2.1.injOn
  obtain ⟨t₁, ht₁pos, hχ1⟩ := hχ.exists_eq_one
  have ht₁ := ht₁pos.le
  haveI hmP : IsProbabilityMeasure (μ 0 t₁) := hμ.isProbability 0 t₁ le_rfl ht₁
  -- `S_λ 0 = 0`
  have hS0 : ∀ lam : ℝ, 0 < lam → S lam 0 = 0 := fun lam hlam => by
    have h : χ (S lam 0) = χ 0 := by rw [hχS lam 0 hlam le_rfl, hχ.1, mul_zero]
    exact hinj ((hμ.scale_bij lam hlam).mapsTo self_mem_Ici) self_mem_Ici h
  -- the kernels from the origin: `μ_{0,t} = (χ(t) I)_* m`, `m := μ_{0,t₁}`
  have hkern : ∀ t : ℝ, 0 ≤ t → μ 0 t = push (χ t • (1 : Mat d)) (μ 0 t₁) := by
    intro t ht
    rcases ht.lt_or_eq with ht | ht
    · have hpos := hχ.pos ht
      have h := hμ.scale (χ t) hpos 0 t₁ le_rfl ht₁
      rw [hS0 _ hpos] at h
      have hSt : S (χ t) t₁ = t := by
        refine hinj ((hμ.scale_bij _ hpos).mapsTo (mem_Ici.2 ht₁)) (mem_Ici.2 ht.le) ?_
        rw [hχS _ _ hpos ht₁, hχ1, mul_one]
      rw [hSt] at h
      exact h.symm
    · subst ht
      rw [hχ.1, zero_smul, push_zero_mat, hμ.diag 0 le_rfl]
  -- `m` is rotation invariant, self-decomposable and not `δ₀`
  have hrot : IsRotationInvariant (μ 0 t₁) := fun Q hQ => hμ.rotation Q hQ 0 t₁ le_rfl ht₁
  have hne : μ 0 t₁ ≠ Measure.dirac 0 := hμ.nondegenerate 0 t₁ le_rfl ht₁pos
  have hsd : IsSelfDecomposable (μ 0 t₁) := by
    haveI := hμ.isProbability 0 t₁ le_rfl ht₁
    rw [isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    obtain ⟨tc, htc, hχc⟩ := hχ.2.2 (mem_Ici.2 hc0.le)
    have htc' : 0 ≤ tc := htc
    have htc1 : tc ≤ t₁ := by
      by_contra h
      push Not at h
      have := hχ.2.1 (mem_Ici.2 ht₁) htc h
      rw [hχ1, hχc] at this
      linarith
    haveI := hμ.isProbability tc t₁ htc' htc1
    haveI := hμ.isProbability 0 tc le_rfl htc'
    refine ⟨μ tc t₁, inferInstance, fun ξ => ?_⟩
    have h := hμ.cascade 0 tc t₁ le_rfl htc' htc1
    have hk := hkern tc htc'
    rw [hχc] at hk
    conv_lhs => rw [h]
    rw [charFun_conv, hk, charFun_push_smul_one, mul_comm]
  obtain ⟨⟨ν, hν, hν1⟩, huniq⟩ := gw_ray_families_gl_converse (μ 0 t₁) hrot hsd hne
  have hWgl : IsWedgeDatum (glSet d) rayLE := glSet_isWedgeDatum_ray
  have hνu : ∀ t : ℝ, 0 ≤ t → ν 0 ((χ t ^ 2) • (1 : Mat d)) = μ 0 t := by
    intro t ht
    rw [gw_kernel_smul_one hWgl ν hν (sq_nonneg _), Real.sqrt_sq (hχ.nonneg ht), hν1, hkern t ht]
  have hz := gw_kernels_hasNoZeros hWgl ν hν
  have hpsd : ∀ u : ℝ, 0 ≤ u → (u • (1 : Mat d)).PosSemidef := fun u hu => PosSemidef.one.smul hu
  have hslice : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      μ s t = ν ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1) := by
    intro s t hs hst
    have ht := hs.trans hst
    have hle : χ s ^ 2 ≤ χ t ^ 2 :=
      pow_le_pow_left₀ (hχ.nonneg hs) (hχ.2.1.monotoneOn (mem_Ici.2 hs) (mem_Ici.2 ht) hst) 2
    haveI := hμ.isProbability s t hs hst
    haveI := hμ.isProbability 0 s le_rfl hs
    refine (gw_kernels_from_origin_unique hWgl ν hν hz).1 _ _ (hpsd _ (sq_nonneg _))
      (hpsd _ (sq_nonneg _)) (hWgl.rays 1 PosSemidef.one _ _ (sq_nonneg _) hle) (μ s t)
      inferInstance ?_
    rw [hνu t ht, hνu s hs, hμ.cascade 0 s t le_rfl hs hst, Measure.conv_comm]
  refine ⟨ν, hν, hslice, fun ν' hν' h' => ?_, gw_family_of_subset simSet_subset_glSet ν hν⟩
  have h1 := h' 0 t₁ le_rfl ht₁
  rw [hχ.1, hχ1] at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, one_pow,
    one_smul] at h1
  exact huniq ν ν' hν hν' hν1 h1.symm

/-- **`prop:isotropic-corner`(2)**: for an isotropic cascade family with dilation action `S`,
there is a gauge `χ` with `χ(S_λ t) = λχ(t)`; `φ := χ²` is a gauge; there is exactly one (on the
pairs) `(GL(d), rays)`-cascade family `ν` with `μ_{s,t} = ν_{φ(s)I, φ(t)I}`; and `ν` is also an
`(S(d), rays)`-cascade family. The gauge is Paper V's `canonical_gauge` of the marginal family. -/
theorem isotropic_corner_gauge (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ)
    (hμ : IsIsotropicCascadeFamily μ S) :
    ∃ χ : ℝ → ℝ, IsGauge χ ∧ (∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t) ∧
      IsGauge (fun t => χ t ^ 2) ∧
      ∃ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE ν ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1)) ∧
        (∀ ν' : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE ν' →
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν' ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1)) →
          EqOnPairs rayLE ν ν') ∧
        IsGWCascadeFamily (simSet d) rayLE ν := by
  obtain ⟨e, he⟩ : ∃ e : Rd d, ‖e‖ = 1 := ⟨ebasis ⟨0, by omega⟩, by simp [ebasis]⟩
  obtain ⟨-, -, Fam, hFS, hker⟩ := isotropic_marginal_family hμ e he
  have hcov : ScaleSpace.IsScaleCovariant Fam.Φ (Ioi 0) S := hFS ▸ Fam.covariant
  obtain ⟨-, χ, h0, hmono, hsurj, -, hrel, -⟩ :=
    ScaleSpace.canonical_gauge Fam.toPreCascadeCore _ hker Fam.nondegenerate S hcov
  have hχ : IsGauge χ := ⟨h0, hmono, hsurj⟩
  exact ⟨χ, hχ, hrel, hχ.sq, isotropic_corner_gauge_forall hd μ S hμ χ hχ hrel⟩

/-! ## Clause (3): the change of gauge -/

/-- **`prop:isotropic-corner`(3)**: in the setting of (2), a gauge `ψ`, a wedge datum `(G, W)` and
a `(G, W)`-cascade family `ν'` with `μ_{s,t} = ν'_{ψ(s)I, ψ(t)I}` force `ψ = cφ` for some
`c > 0`. -/
theorem isotropic_corner_gauge_unique (_hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (S : ℝ → ℝ → ℝ) (_hμ : IsIsotropicCascadeFamily μ S) (χ : ℝ → ℝ) (hχ : IsGauge χ)
    (_hχS : ∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t)
    (ν : Mat d → Mat d → Measure (Rd d)) (hν : IsGWCascadeFamily (glSet d) rayLE ν)
    (hνμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1))
    (ψ : ℝ → ℝ) (hψ : IsGauge ψ) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (ν' : Mat d → Mat d → Measure (Rd d))
    (hν' : IsGWCascadeFamily G le ν')
    (hν'μ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν' (ψ s • (1 : Mat d)) (ψ t • 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → ψ t = c * χ t ^ 2 := by
  have hWgl : IsWedgeDatum (glSet d) rayLE := glSet_isWedgeDatum_ray
  obtain ⟨t₁, ht₁pos, hχ1⟩ := hχ.exists_eq_one
  have h01 := wedge_zero_one_mem hW
  haveI : IsProbabilityMeasure (ν' 0 1) := hν'.isProbability _ h01
  have hA : ∀ t, 0 ≤ t → μ 0 t = push (Real.sqrt (ψ t) • (1 : Mat d)) (ν' 0 1) := by
    intro t ht
    rw [hν'μ 0 t le_rfl ht, hψ.1, zero_smul, gw_kernel_smul_one hW ν' hν' (hψ.nonneg ht)]
  have hB : ∀ t, 0 ≤ t → μ 0 t = push (χ t • (1 : Mat d)) (ν 0 1) := by
    intro t ht
    rw [hνμ 0 t le_rfl ht, hχ.1, zero_pow two_ne_zero, zero_smul,
      gw_kernel_smul_one hWgl ν hν (sq_nonneg _), Real.sqrt_sq (hχ.nonneg ht)]
  have hc : 0 < ψ t₁ := hψ.pos ht₁pos
  have hm : ν 0 1 = push (Real.sqrt (ψ t₁) • (1 : Mat d)) (ν' 0 1) := by
    have := (hB t₁ ht₁pos.le).symm.trans (hA t₁ ht₁pos.le)
    rwa [hχ1, one_smul, push_one] at this
  refine ⟨ψ t₁, hc, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | ht
  · have hψt := hψ.pos ht
    have hχt := hχ.pos ht
    have h := (hA t ht.le).symm.trans (hB t ht.le)
    rw [hm, push_push, smul_one_mul_smul_one] at h
    have hsq : Real.sqrt (ψ t) ≠ 0 := (Real.sqrt_pos.2 hψt).ne'
    have h2 := congrArg (push ((Real.sqrt (ψ t))⁻¹ • (1 : Mat d))) h
    rw [push_smul_one_inv_cancel hsq, push_push, smul_one_mul_smul_one] at h2
    by_contra hne
    refine hν'.nondegenerate (eq_dirac_of_push_smul_eq (ν' 0 1)
      (a := (Real.sqrt (ψ t))⁻¹ * (χ t * Real.sqrt (ψ t₁)))
      (mul_pos (inv_pos.2 (Real.sqrt_pos.2 hψt)) (mul_pos hχt (Real.sqrt_pos.2 hc))) ?_ h2.symm)
    intro h1
    apply hne
    have h3 : χ t * Real.sqrt (ψ t₁) = Real.sqrt (ψ t) := by
      field_simp at h1
      linarith
    have h4 := congrArg (· ^ 2) h3
    simp only [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hψt.le] at h4
    linarith
  · subst ht
    rw [hψ.1, hχ.1]
    ring

/-- **`prop:isotropic-corner`(3)**, the converse: for every `c > 0`, `(ν_{c⁻¹Σ, c⁻¹Σ'})` is a
`(GL(d), rays)`-cascade family of kernels with the property of (2) for `ψ = cφ`. -/
theorem isotropic_corner_rescale (_hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ)
    (_hμ : IsIsotropicCascadeFamily μ S) (χ : ℝ → ℝ) (_hχ : IsGauge χ)
    (_hχS : ∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t)
    (ν : Mat d → Mat d → Measure (Rd d)) (hν : IsGWCascadeFamily (glSet d) rayLE ν)
    (hνμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν ((χ s ^ 2) • (1 : Mat d)) ((χ t ^ 2) • 1))
    (c : ℝ) (hc : 0 < c) :
    IsGWCascadeFamily (glSet d) rayLE (fun A B => ν (c⁻¹ • A) (c⁻¹ • B)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        μ s t = ν (c⁻¹ • ((c * χ s ^ 2) • (1 : Mat d))) (c⁻¹ • ((c * χ t ^ 2) • (1 : Mat d))) := by
  have hWgl : IsWedgeDatum (glSet d) rayLE := glSet_isWedgeDatum_ray
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hmap : ∀ p ∈ wedgePairs (d := d) rayLE, (c⁻¹ • p.1, c⁻¹ • p.2) ∈ wedgePairs (d := d) rayLE := by
    rintro ⟨S, S'⟩ ⟨hS, hS', hle⟩
    refine ⟨hS.smul hci.le, hS'.smul hci.le, ?_⟩
    rcases hle with h | ⟨k, hk, h⟩
    · left
      dsimp only at h ⊢
      rw [h, smul_zero]
    · right
      refine ⟨k, hk, ?_⟩
      dsimp only at h ⊢
      rw [h, smul_comm]
  have h01 := wedge_zero_one_mem hWgl
  haveI : IsProbabilityMeasure (ν 0 1) := hν.isProbability _ h01
  refine ⟨⟨fun p hp => hν.isProbability _ (hmap p hp), fun S hS => hν.diag _ (hS.smul hci.le),
    fun S S' S'' hS hS' hS'' h h' => ?_, fun ω => ?_, fun A hA p hp => ?_, ?_⟩,
    fun s t hs hst => ?_⟩
  · have h1 := hmap (S, S') ⟨hS, hS', h⟩
    have h2 := hmap (S', S'') ⟨hS', hS'', h'⟩
    exact hν.cascade _ _ _ (hS.smul hci.le) (hS'.smul hci.le) (hS''.smul hci.le) h1.2.2 h2.2.2
  · have hcont : Continuous fun p : Mat d × Mat d => (c⁻¹ • p.1, c⁻¹ • p.2) :=
      (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)
    exact (hν.continuous ω).comp hcont.continuousOn fun p hp => hmap p hp
  · have h := hν.covariant A hA _ (hmap p hp)
    dsimp only at h ⊢
    rw [h, act_smul, act_smul]
  · intro h
    rw [smul_zero, gw_kernel_smul_one hWgl ν hν hci.le] at h
    have hs : Real.sqrt c⁻¹ ≠ 0 := (Real.sqrt_pos.2 hci).ne'
    have h2 := congrArg (push ((Real.sqrt c⁻¹)⁻¹ • (1 : Mat d))) h
    rw [push_smul_one_inv_cancel hs, push_dirac_zero] at h2
    exact hν.nondegenerate h2
  · rw [smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, one_mul]
    exact hνμ s t hs hst

/-! ## Clause (4): what the slice determines -/

/-- `(det(cQ Σ (cQ)ᵀ))^{1/(2d)} = c (det Σ)^{1/(2d)}` for `c > 0`, `Q ∈ O(d)`, `Σ ∈ PSD(d)`. -/
theorem volScale_act_sim [NeZero d] {a : ℝ} (ha : 0 < a) {Q : Mat d} (hQ : Q * Qᵀ = 1)
    {S : Mat d} (hS : S.PosSemidef) : volScale (act (a • Q) S) = a * volScale S := by
  have hdQ : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rwa [det_mul, det_transpose, det_one] at this
  have hdet : (act (a • Q) S).det = a ^ (2 * d) * S.det := by
    rw [act, det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin]
    calc a ^ d * Q.det * S.det * (a ^ d * Q.det) = a ^ (2 * d) * (Q.det * Q.det) * S.det := by ring
      _ = a ^ (2 * d) * S.det := by rw [hdQ, mul_one]
  have hd0 : (2 * d : ℕ) ≠ 0 := by have := NeZero.ne d; omega
  have he : (1 : ℝ) / (2 * d) = ((2 * d : ℕ) : ℝ)⁻¹ := by push_cast; ring
  rw [volScale, volScale, hdet, Real.mul_rpow (by positivity) hS.det_nonneg, he,
    Real.pow_rpow_inv_natCast ha.le hd0]

/-- **The shape-blind family has properties (a)–(c)** for the similarities
(`prop:similarity-ray-families`(3)(ii)): `ν_Σ := ((det Σ)^{1/(2d)} I)_*μ_I` for a rotation-invariant
`μ_I ≠ δ₀`. -/
theorem shapeBlind_isOriginKernels [NeZero d] (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hne : μI ≠ Measure.dirac 0) :
    IsOriginKernels (simSet d) (shapeBlind μI) := by
  have hd0 : (1 : ℝ) / (2 * d) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  refine ⟨fun S _ => isProbabilityMeasure_push _ _, ?_, ?_, ?_, fun ω => ?_⟩
  · rw [shapeBlind, volScale, det_zero ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩,
      Real.zero_rpow hd0, zero_smul, push_zero_mat]
  · rw [shapeBlind, volScale, det_one, Real.one_rpow, one_smul, push_one]
    exact hne
  · rintro _ ⟨a, ha, Q, hQ, rfl⟩ S hS
    have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    rw [shapeBlind, shapeBlind, volScale_act_sim ha hQQ hS, push_push]
    have hQ1 : (a * volScale S) • (1 : Mat d) * Q = a • Q * (volScale S • (1 : Mat d)) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        mul_comm]
    rw [← hQ1, ← push_push, hrot Q hQ]
  · have hvc : Continuous fun S : Mat d => volScale S :=
      (continuous_id.matrix_det).rpow_const fun _ => Or.inr (by positivity)
    have he : (fun S => charFun (shapeBlind μI S) ω) =
        fun S => charFun μI (volScale S • ω) := by
      funext S
      rw [shapeBlind, charFun_push_smul_one]
    rw [he]
    exact (continuous_charFun.comp (hvc.smul continuous_const)).continuousOn

/-- **`prop:isotropic-corner`(4)**: a `(GL(d), rays)`-cascade family of kernels is determined by
its slice. -/
theorem isotropic_corner_gl_determined (hd : 1 ≤ d) (ν ν' : Mat d → Mat d → Measure (Rd d))
    (hν : IsGWCascadeFamily (glSet d) rayLE ν) (hν' : IsGWCascadeFamily (glSet d) rayLE ν')
    (h : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν (s • (1 : Mat d)) (t • 1) = ν' (s • (1 : Mat d)) (t • 1)) :
    EqOnPairs rayLE ν ν' := by
  haveI : NeZero d := ⟨by omega⟩
  have h01 : ν 0 1 = ν' 0 1 := by simpa using h 0 1 le_rfl zero_le_one
  obtain ⟨-, hrot, hsd, hne, -⟩ := gw_ray_families_gl ν hν
  haveI : IsProbabilityMeasure (ν 0 1) := hν.isProbability _ (wedge_zero_one_mem glSet_isWedgeDatum_ray)
  exact (gw_ray_families_gl_converse (ν 0 1) hrot hsd hne).2 ν ν' hν hν' rfl h01.symm

/-- **The similarities `S(d)` form a closed subgroup of `GL(d)` containing the dilations** (the
part of `prop:similarity-ray-families`(1) that clause (4) reads). Closedness: on the closure,
`AAᵀ` is a multiple `kI` of the identity, `k > 0` when `A` is invertible, and
`A = √k (A/√k)` with `A/√k` orthogonal. -/
theorem simSet_isClosedSubgroupGL [NeZero d] :
    IsClosedSubgroupGL (simSet d) ∧ ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ simSet d := by
  have horth1 : (1 : Mat d) ∈ Matrix.orthogonalGroup (Fin d) ℝ := one_mem _
  refine ⟨⟨simSet_subset_glSet, ⟨1, one_pos, 1, horth1, (one_smul _ _).symm⟩, ?_, ?_, ?_⟩,
    fun c hc => ⟨c, hc, 1, horth1, rfl⟩⟩
  · rintro _ ⟨a, ha, P, hP, rfl⟩ _ ⟨b, hb, Q, hQ, rfl⟩
    exact ⟨a * b, mul_pos ha hb, P * Q, mul_mem hP hQ, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]⟩
  · rintro _ ⟨a, ha, P, hP, rfl⟩
    have hPP : P * Pᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
    refine ⟨a⁻¹, inv_pos.2 ha, Pᵀ, transpose_mem_orthSet hP, ?_⟩
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hPP]
  · intro A hA hdet
    set i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi₀
    have hcM : Continuous fun M : Mat d => M * Mᵀ :=
      continuous_id.matrix_mul continuous_id.matrix_transpose
    have hC : IsClosed {M : Mat d | ∀ i j, (M * Mᵀ) i j =
        if i = j then (M * Mᵀ) i₀ i₀ else 0} := by
      simp only [setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq
        (hcM.matrix_elem i j) ?_
      split_ifs
      · exact hcM.matrix_elem i₀ i₀
      · exact continuous_const
    have hsub : simSet d ⊆ {M : Mat d | ∀ i j, (M * Mᵀ) i j =
        if i = j then (M * Mᵀ) i₀ i₀ else 0} := by
      rintro _ ⟨a, ha, P, hP, rfl⟩ i j
      have hPP : P * Pᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
      have h : (a • P) * (a • P)ᵀ = (a * a) • (1 : Mat d) := by
        rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPP]
      rw [h]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hAC := closure_minimal hsub hC hA
    set k := (A * Aᵀ) i₀ i₀ with hk
    have hAA : A * Aᵀ = k • (1 : Mat d) := by
      ext i j
      rw [hAC i j]
      by_cases hij : i = j
      · subst hij; simp [hk]
      · simp [hij]
    have hk0 : 0 ≤ k := by
      rw [hk, Matrix.mul_apply]
      exact Finset.sum_nonneg fun j _ => by rw [transpose_apply]; exact mul_self_nonneg _
    have hkpos : 0 < k := by
      refine lt_of_le_of_ne hk0 fun h0 => ?_
      have hU : IsUnit (A * Aᵀ).det := by
        rw [det_mul, det_transpose]; exact hdet.mul hdet
      rw [hAA, ← h0, zero_smul, det_zero ⟨i₀⟩] at hU
      exact not_isUnit_zero hU
    have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hkpos
    refine ⟨Real.sqrt k, hs, (Real.sqrt k)⁻¹ • A, ?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff]
      change ((Real.sqrt k)⁻¹ • A) * ((Real.sqrt k)⁻¹ • A)ᵀ = 1
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA, smul_smul,
        ← mul_inv, Real.mul_self_sqrt hkpos.le, inv_mul_cancel₀ hkpos.ne', one_smul]
    · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- **`prop:isotropic-corner`(4)**: for `d ≥ 2` an `(S(d), rays)`-cascade family is not
determined by its slice: its slice is the slice of two such families whose kernels from the
origin differ at every `Σ ∈ PD(d)` that is not a multiple of `I`. The two are the affine orbit
`(Σ^{1/2})_*ν_I` and the shape-blind family `((det Σ)^{1/(2d)} I)_*ν_I`. -/
theorem isotropic_corner_sim_not_determined (hd : 2 ≤ d) (ν : Mat d → Mat d → Measure (Rd d))
    (hν : IsGWCascadeFamily (simSet d) rayLE ν) :
    ∃ ν₁ ν₂ : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (simSet d) rayLE ν₁ ∧ IsGWCascadeFamily (simSet d) rayLE ν₂ ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        ν₁ (s • (1 : Mat d)) (t • 1) = ν (s • (1 : Mat d)) (t • 1) ∧
        ν₂ (s • (1 : Mat d)) (t • 1) = ν (s • (1 : Mat d)) (t • 1)) ∧
      ∀ S : Mat d, S.PosDef → (∀ c : ℝ, S ≠ c • (1 : Mat d)) → ν₁ 0 S ≠ ν₂ 0 S := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hGs, hdils⟩ := simSet_isClosedSubgroupGL (d := d)
  have hWs : IsWedgeDatum (simSet d) rayLE := isWedgeDatum_ray hGs hdils
  have h01 := wedge_zero_one_mem hWs
  haveI : IsProbabilityMeasure (ν 0 1) := hν.isProbability _ h01
  have horth : orthSet d ⊆ simSet d := fun Q hQ => ⟨1, one_pos, Q, hQ, (one_smul _ _).symm⟩
  have hrot : IsRotationInvariant (ν 0 1) := fun Q hQ => by
    have h := hν.covariant Q (horth hQ) _ h01
    dsimp only at h
    rw [h, act_zero, act_orth_one hQ]
  have hsd : IsSelfDecomposable (ν 0 1) := gw_kernels_selfDecomposable hWs ν hν 1 PosSemidef.one
  have hne : ν 0 1 ≠ Measure.dirac 0 := hν.nondegenerate
  -- the affine orbit
  obtain ⟨⟨ν₁, hν₁gl, hν₁1⟩, -⟩ := gw_ray_families_gl_converse (ν 0 1) hrot hsd hne
  have hν₁ := gw_family_of_subset simSet_subset_glSet ν₁ hν₁gl
  -- the shape-blind family
  have hok : IsOriginKernels (simSet d) (shapeBlind (ν 0 1)) :=
    shapeBlind_isOriginKernels (ν 0 1) hrot hne
  obtain ⟨ν₂, hν₂, hν₂0⟩ := (gw_ray_families hWs (shapeBlind (ν 0 1))
    (fun S _ => isProbabilityMeasure_push _ _)).2
    ⟨hok, fun S _ => (selfDecomposable_charFun_ne_zero (ν 0 1) hsd).2 _⟩
  have hν₂1 : ν₂ 0 1 = ν 0 1 := by
    rw [hν₂0 1 PosSemidef.one, shapeBlind, volScale, det_one, Real.one_rpow, one_smul, push_one]
  -- the slices agree: the increments are determined by the kernels from the origin
  have hpsd : ∀ u : ℝ, 0 ≤ u → (u • (1 : Mat d)).PosSemidef := fun u hu => PosSemidef.one.smul hu
  have hslice : ∀ ν'' : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (simSet d) rayLE ν'' → ν'' 0 1 = ν 0 1 →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν'' (s • (1 : Mat d)) (t • 1) = ν (s • (1 : Mat d)) (t • 1) := by
    intro ν'' hν'' h1 s t hs hst
    have ht := hs.trans hst
    have hle := hWs.rays 1 PosSemidef.one s t hs hst
    obtain ⟨hp, hc⟩ := (gw_kernels_from_origin hWs ν'' hν'').2 _ _ (hpsd s hs) (hpsd t ht) hle
    refine (gw_kernels_from_origin_unique hWs ν hν (gw_kernels_hasNoZeros hWs ν hν)).1 _ _
      (hpsd s hs) (hpsd t ht) hle _ hp ?_
    rw [gw_kernel_smul_one hWs ν hν ht, gw_kernel_smul_one hWs ν hν hs, ← h1,
      ← gw_kernel_smul_one hWs ν'' hν'' ht, ← gw_kernel_smul_one hWs ν'' hν'' hs]
    exact hc
  refine ⟨ν₁, ν₂, hν₁, hν₂, fun s t hs hst =>
    ⟨hslice ν₁ hν₁ hν₁1 s t hs hst, hslice ν₂ hν₂ hν₂1 s t hs hst⟩, fun S hS hnot h => ?_⟩
  -- the kernels from the origin differ off the multiples of `I`: `Stab(ν_I) = O(d)`
  rw [(gw_ray_families_gl ν₁ hν₁gl).1 S hS.posSemidef, hν₁1, hν₂0 S hS.posSemidef] at h
  have hv : 0 < volScale S := Real.rpow_pos_of_pos hS.det_pos _
  have hstab := (isFull_of_isRotationInvariant (by omega) (ν 0 1) hrot hne).2
  have hP : (volScale S)⁻¹ • msqrt S ∈ stab (ν 0 1) := by
    refine ⟨?_, ?_⟩
    · have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
      change IsUnit ((volScale S)⁻¹ • msqrt S).det
      rw [det_smul]
      exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (inv_ne_zero hv.ne'))).mul hU
    · rw [show (volScale S)⁻¹ • msqrt S = ((volScale S)⁻¹ • (1 : Mat d)) * msqrt S by
        rw [Matrix.smul_mul, Matrix.one_mul], ← push_push]
      change push _ (affineOrbit (ν 0 1) S) = _
      rw [h, shapeBlind, push_smul_one_inv_cancel hv.ne']
  rw [hstab] at hP
  have hPP := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
  change ((volScale S)⁻¹ • msqrt S) * ((volScale S)⁻¹ • msqrt S)ᵀ = 1 at hPP
  rw [transpose_smul, msqrt_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    msqrt_mul_self hS.posSemidef] at hPP
  apply hnot (volScale S ^ 2)
  have h2 := congrArg (fun M => (volScale S ^ 2) • M) hPP
  simp only [smul_smul] at h2
  rw [show volScale S ^ 2 * ((volScale S)⁻¹ * (volScale S)⁻¹) = 1 by field_simp, one_smul] at h2
  exact h2

end AffineHemigroup
