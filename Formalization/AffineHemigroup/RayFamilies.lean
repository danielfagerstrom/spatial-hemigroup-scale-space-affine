/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KernelsFromOrigin
import AffineHemigroup.Gauge
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import AffineHemigroup.RadialTransform

/-!
# `prop:gw-ray-families` — the ray column: covariant fields of self-decomposable laws

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:gw-ray-families`. Lean core only:
neither ledger A4 (a self-decomposable law is infinitely divisible) nor A6 is spent; the
transforms have no zeros by the two-paragraph argument of the node's proof.

## The route

The blueprint's, with three choices of the Lean proof:

* **Clause (1) is the shared library's** since Q-0365 (`ScaleSpaceCore.SelfDecomposable`, SSL-3,
  where this module's argument moved): `ScaleSpace.IsSelfDecomposable.charFun_ne_zero` proves the
  doubling inequality `1 - |ρ̂(2ξ)|² ≤ 4(1 - |ρ̂(ξ)|²)` for the transform of the symmetrisation
  `κ = ρ * (-I)_*ρ`, whose transform is `|ρ̂|²`, from `1 - cos 2τ ≤ 4(1 - cos τ)` under the
  integral, and at the first zero `z₀` takes the contradiction in the limit `c ↑ 1` of
  `|μ̂(z₀/2)|² ≤ ¾ |μ̂(cz₀/2)|²`; the images are `ScaleSpace.IsSelfDecomposable.map`.
* **Necessity in (2) holds for every wedge datum** (`gw_kernels_selfDecomposable`): it reads only
  that `W` contains the rays and `G` the dilations, which every wedge datum has.
* **(3) does not read `prop:ray-families`**: on `PD(d)` the covariance (b) at `A = Σ^{1/2}` gives
  `μ_Σ = (Σ^{1/2})_*μ_I` directly, and the boundary of `PSD(d)` is reached by continuity, as the
  blueprint has it. The radial form `μ̂_I(z) = F(|z|²)` uses the reflection in `(z - |z|e₁)^⊥`, as
  `lem:affine-reduction` does.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## Clause (1): self-decomposable laws

Since Q-0452 clause (1), `selfDecomposable_charFun_ne_zero`, and the radial form of the transform
of a rotation-invariant law that clause (3) reads are in `AffineHemigroup.RadialTransform`, which
this file imports; the transform of an image under a dilation is in
`AffineHemigroup.MatrixCalculus`. -/

/-! ## Clause (2): the families -/

/-- **The kernels from the origin of every `(G, W)`-cascade family are self-decomposable**: `W`
contains the rays and `G` the dilations, so `μ_{λ²Σ} = (λI)_*μ_Σ = μ_Σ * μ_{Σ,λ²Σ}` for `λ > 1`.
This is necessity in `prop:gw-ray-families`(2), which reads nothing of the ray order beyond what
every wedge datum has. -/
theorem gw_kernels_selfDecomposable {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) (S : Mat d) (hS : S.PosSemidef) :
    IsSelfDecomposable (μ 0 S) := by
  have hk := gw_kernels_from_origin hW μ hμ
  haveI := hk.1.isProbability S hS
  rw [isSelfDecomposable_iff_charFun]
  intro c hc0 hc1
  set lam : ℝ := c⁻¹ with hlam
  have hlam1 : 1 ≤ lam ^ 2 := by
    have : 1 ≤ lam := by rw [hlam]; exact (one_le_inv₀ hc0).2 hc1.le
    nlinarith
  have hS2 : (lam ^ 2 • S).PosSemidef := hS.smul (by positivity)
  have hle : le S (lam ^ 2 • S) := by
    simpa using hW.rays S hS 1 (lam ^ 2) zero_le_one hlam1
  obtain ⟨hp, hc⟩ := hk.2 S _ hS hS2 hle
  haveI := hk.1.isProbability S hS
  refine ⟨push (c • (1 : Mat d)) (μ S (lam ^ 2 • S)), inferInstance, fun ξ => ?_⟩
  have hb := hk.1.covariant _ (hW.dilations lam (by positivity)) S hS
  rw [act_smul_one] at hb
  have h := congrArg (fun m => charFun m (c • ξ)) (hb.trans hc)
  simp only [charFun_push_smul_one, charFun_conv, smul_smul] at h
  rw [charFun_push_smul_one, ← h, hlam, inv_mul_cancel₀ hc0.ne', one_smul]

/-- **The kernels from the origin of every `(G, W)`-cascade family have transforms without zeros**
(`lem:gw-kernels-self-decomposable`): they are self-decomposable, and the transform of a
self-decomposable law has no zero (`prop:gw-ray-families`(1)). -/
theorem gw_kernels_hasNoZeros {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) : HasNoZeros fun S => μ 0 S := fun S hS =>
  haveI := (gw_kernels_from_origin hW μ hμ).1.isProbability S hS
  (selfDecomposable_charFun_ne_zero (μ 0 S) (gw_kernels_selfDecomposable hW μ hμ S hS)).1

/-- **Every `(G, W)`-cascade family is determined by its kernels from the origin**, for every wedge
datum (`lem:gw-kernels-self-decomposable`, through the uniqueness of `lem:gw-kernels-from-origin`(2)):
two families with the same kernels from the origin agree on `P_W`. -/
theorem gw_family_determined_by_kernels {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ ν : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) (hν : IsGWCascadeFamily G le ν)
    (h : ∀ S : Mat d, S.PosSemidef → ν 0 S = μ 0 S) : EqOnPairs le μ ν :=
  (gw_kernels_from_origin_unique hW μ hμ (gw_kernels_hasNoZeros hW μ hμ)).2 ν hν h

/-- The ray order's increments, from self-decomposability: if `μ_Σ` is self-decomposable and
`(c^{1/2}I)_*μ_Σ = μ_{cΣ}`, `c ≥ 1`, then `μ_{cΣ} = μ_Σ * ρ` for a probability measure `ρ`. -/
private theorem ray_increment (m : Measure (Rd d)) [IsProbabilityMeasure m]
    (hsd : IsSelfDecomposable m) (c : ℝ) (hc : 1 ≤ c) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      push (Real.sqrt c • (1 : Mat d)) m = m ∗ ρ := by
  rcases eq_or_lt_of_le hc with rfl | hc1
  · refine ⟨Measure.dirac 0, inferInstance, ?_⟩
    apply eq_of_charFun_eq
    intro ω
    rw [charFun_push_smul_one, charFun_conv, charFun_dirac, Real.sqrt_one, one_smul]
    simp
  · have hs1 : 1 < Real.sqrt c := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hc1
    have hs0 : 0 < Real.sqrt c := by linarith
    obtain ⟨ρ', hρ', hfac⟩ := (isSelfDecomposable_iff_charFun m).1 hsd (Real.sqrt c)⁻¹
      (inv_pos.2 hs0) (inv_lt_one_of_one_lt₀ hs1)
    refine ⟨push (Real.sqrt c • (1 : Mat d)) ρ', inferInstance, ?_⟩
    apply eq_of_charFun_eq
    intro ω
    rw [charFun_push_smul_one, charFun_conv, charFun_push_smul_one, hfac, smul_smul,
      inv_mul_cancel₀ hs0.ne', one_smul]

/-- **`prop:gw-ray-families`(2)**: for a wedge datum whose order is the ray order, a map
`Σ ↦ μ_Σ` from `PSD(d)` into the probability measures is the family of kernels from the origin of
a `(G, W)`-cascade family if and only if it satisfies (a)–(c) and every `μ_Σ` is
self-decomposable. -/
theorem gw_ray_families {G : Set (Mat d)} (hW : IsWedgeDatum G rayLE)
    (m : Mat d → Measure (Rd d)) (hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S)) :
    IsKernelsFromOrigin G rayLE m ↔
      IsOriginKernels G m ∧ ∀ S : Mat d, S.PosSemidef → IsSelfDecomposable (m S) := by
  constructor
  · rintro ⟨μ, hμ, hμm⟩
    have hk := (gw_kernels_from_origin hW μ hμ).1
    refine ⟨⟨hprob, ?_, ?_, ?_, ?_⟩, fun S hS => ?_⟩
    · rw [← hμm 0 PosSemidef.zero]; exact hk.zero
    · rw [← hμm 1 PosSemidef.one]; exact hk.one_ne
    · intro A hA S hS
      rw [← hμm S hS, ← hμm _ (posSemidef_act A hS)]
      exact hk.covariant A hA S hS
    · intro ω
      exact (hk.continuous ω).congr fun S hS => by
        show charFun (m S) ω = charFun (μ 0 S) ω
        rw [hμm S hS]
    · rw [← hμm S hS]
      exact gw_kernels_selfDecomposable hW μ hμ S hS
  · rintro ⟨hm, hsd⟩
    have hz : HasNoZeros m := fun S hS =>
      haveI := hprob S hS
      (selfDecomposable_charFun_ne_zero (m S) (hsd S hS)).1
    have hinc : HasIncrements rayLE m := by
      intro S S' hS hS' h
      haveI := hprob S hS
      haveI := hprob S' hS'
      rcases h with rfl | ⟨c, hc, rfl⟩
      · refine ⟨m S', inferInstance, ?_⟩
        apply eq_of_charFun_eq
        intro ω
        rw [charFun_conv, hm.zero, charFun_dirac]
        simp
      · obtain ⟨ρ, hρ, h⟩ := ray_increment (m S) (hsd S hS) c hc
        refine ⟨ρ, hρ, ?_⟩
        rw [← h, hm.covariant _ (hW.dilations _ (Real.sqrt_pos.2 (by linarith))) S hS,
          act_smul_one, Real.sq_sqrt (by linarith)]
    exact (gw_kernels_from_origin_converse hW m hm hz hinc).1

/-- **`prop:gw-ray-families`(2)**, uniqueness: the family is determined (on the pairs) by its
kernels from the origin, and its increments are `μ̂_{Σ,cΣ} = μ̂_{cΣ}/μ̂_Σ`, `c ≥ 1`. -/
theorem gw_ray_families_unique {G : Set (Mat d)} (hW : IsWedgeDatum G rayLE)
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G rayLE μ) :
    (∀ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily G rayLE ν →
        (∀ S : Mat d, S.PosSemidef → ν 0 S = μ 0 S) → EqOnPairs rayLE μ ν) ∧
      ∀ S : Mat d, S.PosSemidef → ∀ c : ℝ, 1 ≤ c → ∀ ω : Rd d,
        charFun (μ S (c • S)) ω = charFun (μ 0 (c • S)) ω / charFun (μ 0 S) ω := by
  have hk := gw_kernels_from_origin hW μ hμ
  have hz := gw_kernels_hasNoZeros hW μ hμ
  refine ⟨(gw_kernels_from_origin_unique hW μ hμ hz).2, ?_⟩
  intro S hS c hc ω
  have hcS : (c • S).PosSemidef := hS.smul (by linarith)
  obtain ⟨hp, h⟩ := hk.2 S (c • S) hS hcS (Or.inr ⟨c, hc, rfl⟩)
  haveI := hk.1.isProbability S hS
  rw [h, charFun_conv, mul_div_cancel_left₀ _ (hz S hS ω)]

/-! ## Clause (3): the general linear group -/

/-- **The transform of an affine orbit of a rotation-invariant law**:
`\widehat{(Σ^{1/2})_*μ_I}(ω) = μ̂_I(⟨ω, Σω⟩^{1/2} e₁)` for `Σ ∈ PSD(d)`. -/
theorem charFun_affineOrbit [NeZero d] {μI : Measure (Rd d)} (hμ : IsRotationInvariant μI)
    {S : Mat d} (hS : S.PosSemidef) (ω : Rd d) :
    charFun (affineOrbit μI S) ω = charFun μI (Real.sqrt (quad S ω) • ebasis 0) := by
  rw [affineOrbit, push, charFun_map_lin, msqrt_transpose, charFun_eq_norm_smul_ebasis hμ]
  congr 2
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq]
  congr 1
  rw [inner_lin_left, msqrt_transpose]
  conv_rhs => rw [quad, ← msqrt_mul_self hS, lin_mul]
  rfl

/-- An affine orbit of a probability measure is a probability measure. -/
instance isProbabilityMeasure_affineOrbit (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (S : Mat d) : IsProbabilityMeasure (affineOrbit μI S) := by
  rw [affineOrbit]
  infer_instance

/-- **`prop:gw-ray-families`(3)**, the general linear group: the kernels from the origin of a
`(GL(d), W)`-cascade family are `μ_Σ = (Σ^{1/2})_*μ_I` for every `Σ ∈ PSD(d)`, with `μ_I` rotation
invariant, self-decomposable and not `δ₀`, and `μ̂_Σ(ω) = ϑ(⟨ω, Σω⟩)` with
`ϑ(u) := μ̂_I(√u e₁)`. -/
theorem gw_ray_families_gl [NeZero d] (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (glSet d) rayLE μ) :
    (∀ S : Mat d, S.PosSemidef → μ 0 S = affineOrbit (μ 0 1) S) ∧
      IsRotationInvariant (μ 0 1) ∧ IsSelfDecomposable (μ 0 1) ∧ μ 0 1 ≠ Measure.dirac 0 ∧
      ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
        charFun (μ 0 S) ω = charFun (μ 0 1) (Real.sqrt (quad S ω) • ebasis 0) := by
  have hW : IsWedgeDatum (glSet d) rayLE :=
    isWedgeDatum_ray glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  have hk := (gw_kernels_from_origin hW μ hμ).1
  haveI hI : IsProbabilityMeasure (μ 0 1) := hk.isProbability 1 PosSemidef.one
  have hrot : IsRotationInvariant (μ 0 1) := by
    intro Q hQ
    rw [hk.covariant Q (orthSet_subset_glSet hQ) 1 PosSemidef.one, act_orth_one hQ]
  set φ : ℝ → ℂ := fun u => charFun (μ 0 1) (Real.sqrt u • ebasis 0) with hφdef
  have hφcont : Continuous φ :=
    continuous_charFun.comp (Real.continuous_sqrt.smul continuous_const)
  /- On `PD(d)`, by (b) at `A = Σ^{1/2}`. -/
  have hPD : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    have h := hk.covariant (msqrt S) (msqrt_mem_glSet hS) 1 PosSemidef.one
    rw [act_msqrt_one hS.posSemidef] at h
    rw [← h, ← affineOrbit, charFun_affineOrbit hrot hS.posSemidef]
  /- On `PSD(d)`, by (c) along `Σ + εI → Σ`. -/
  have hPSD : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    have hmem : ∀ ε : ℝ, 0 ≤ ε → S + ε • (1 : Mat d) ∈ psdSet d := fun ε hε =>
      hS.add (PosSemidef.one.smul hε)
    have hc : ContinuousOn (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (Ici 0) :=
      (hk.continuous ω).comp (by fun_prop : Continuous fun ε : ℝ => S + ε • (1 : Mat d)).continuousOn
        (fun ε hε => hmem ε hε)
    have h1 : Tendsto (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (𝓝[>] 0)
        (𝓝 (charFun (μ 0 S) ω)) := by
      have := (hc 0 self_mem_Ici).tendsto
      simp only [zero_smul, add_zero] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 : Tendsto (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) (𝓝[>] 0)
        (𝓝 (φ (quad S ω))) := by
      have hc2 : Continuous fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω) :=
        hφcont.comp ((continuous_quad ω).comp (by fun_prop))
      have := hc2.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have heq : (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hPD _ (PosDef.posSemidef_add hS (PosDef.one.smul hε)) ω
    exact tendsto_nhds_unique (h1.congr' heq) h2
  refine ⟨fun S hS => ?_, hrot, gw_kernels_selfDecomposable hW μ hμ 1 PosSemidef.one,
    hμ.nondegenerate, hPSD⟩
  haveI := hk.isProbability S hS
  apply eq_of_charFun_eq
  intro ω
  rw [hPSD S hS ω, charFun_affineOrbit hrot hS]

/-- **`prop:gw-ray-families`(3)**, the converse: every rotation-invariant self-decomposable
`μ_I ≠ δ₀` is the isotropic member of exactly one (on the pairs) `(GL(d), W)`-cascade family. -/
theorem gw_ray_families_gl_converse [NeZero d] (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI) (hne : μI ≠ Measure.dirac 0) :
    (∃ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE μ ∧ μ 0 1 = μI) ∧
      ∀ μ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (glSet d) rayLE μ →
        IsGWCascadeFamily (glSet d) rayLE ν → μ 0 1 = μI → ν 0 1 = μI → EqOnPairs rayLE μ ν := by
  have hW : IsWedgeDatum (glSet d) rayLE :=
    isWedgeDatum_ray glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  set m : Mat d → Measure (Rd d) := affineOrbit μI with hmdef
  have hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S) := fun S _ => by
    rw [hmdef, affineOrbit]; infer_instance
  have hm1 : m 1 = μI := by
    haveI := hprob 1 PosSemidef.one
    apply eq_of_charFun_eq
    intro ω
    rw [hmdef, charFun_affineOrbit hrot PosSemidef.one, quad_one,
      Real.sqrt_sq (norm_nonneg _), ← charFun_eq_norm_smul_ebasis hrot]
  have hm : IsOriginKernels (glSet d) m := by
    refine ⟨hprob, ?_, by rw [hm1]; exact hne, ?_, ?_⟩
    · haveI := hprob 0 PosSemidef.zero
      apply eq_of_charFun_eq
      intro ω
      rw [hmdef, charFun_affineOrbit hrot PosSemidef.zero, quad_zero, Real.sqrt_zero, zero_smul,
        charFun_zero, charFun_dirac]
      simp
    · intro A _ S hS
      haveI := hprob S hS
      haveI := hprob _ (posSemidef_act A hS)
      apply eq_of_charFun_eq
      intro ω
      rw [push, charFun_map_lin, hmdef, charFun_affineOrbit hrot hS,
        charFun_affineOrbit hrot (posSemidef_act A hS), quad_act]
    · intro ω
      have hc : Continuous fun S : Mat d => charFun μI (Real.sqrt (quad S ω) • ebasis 0) :=
        continuous_charFun.comp
          ((Real.continuous_sqrt.comp (continuous_quad ω)).smul continuous_const)
      exact hc.continuousOn.congr fun S hS => charFun_affineOrbit hrot hS ω
  have hmsd : ∀ S : Mat d, S.PosSemidef → IsSelfDecomposable (m S) := fun S _ =>
    (selfDecomposable_charFun_ne_zero μI hsd).2 (msqrt S)
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hμm⟩ := (gw_ray_families hW m hprob).2 ⟨hm, hmsd⟩
    exact ⟨μ, hμ, by rw [hμm 1 PosSemidef.one, hm1]⟩
  · intro μ ν hμ hν hμI hνI
    have hμk := (gw_ray_families_gl μ hμ).1
    have hνk := (gw_ray_families_gl ν hν).1
    refine (gw_ray_families_unique hW μ hμ).1 ν hν fun S hS => ?_
    rw [hμk S hS, hνk S hS, hμI, hνI]

end AffineHemigroup
