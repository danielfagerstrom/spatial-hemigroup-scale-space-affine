/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Scheme
import AffineHemigroup.Defs.SmallerGroups
import AffineHemigroup.MatrixCalculus

/-!
# `lem:gw-kernels-from-origin` — a `(G, W)` family is its kernels from the origin

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `lem:gw-kernels-from-origin`. Lean core
only: the uniqueness of the transform is Mathlib's `Measure.ext_of_charFun`, and the transform of a
convolution `charFun_conv`.

## The route

The blueprint's, step for step. Clause (1) reads the `(G', W')` fields on the smaller set of
pairs; clause (2) reads (K1)–(K4) at pairs `(0, Σ)`; clause (3) defines nothing new: the given
increments `ρ_{Σ,Σ'}` have the quotient transform `μ̂_{Σ'}/μ̂_Σ`, and every field of the family is
an identity of transforms. Two notes on the Lean form:

* **(d) is stated `μ_{Σ'} = μ_Σ * ρ`**, where (K1) gives `μ_{0,Σ'} = μ_{Σ,Σ'} * μ_{0,Σ}`; the two
  are the same by commutativity of convolution (`Measure.conv_comm`).
* **The hypotheses on the wedge datum are read where the proof reads them**: clause (1) needs
  neither datum to be a wedge datum (`_hW`, `_hW'`), only `G ⊆ G'` and the inclusion of orders.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder

variable {d : ℕ}

/-! ## Clause (1), restriction -/

/-- **`lem:gw-kernels-from-origin`(1)**, restriction: for wedge data `(G, W)`, `(G', W')` with
`G ⊆ G'` and `Σ ≤_{W'} Σ'` whenever `Σ ≤_W Σ'`, a `(G', W')`-cascade family of kernels, read on
`P_W`, is a `(G, W)`-cascade family of kernels (with, being the same function, the same kernels
from the origin). -/
theorem gw_family_restrict {G G' : Set (Mat d)} {le le' : Mat d → Mat d → Prop}
    (_hW : IsWedgeDatum G le) (_hW' : IsWedgeDatum G' le') (hG : G ⊆ G')
    (hle : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → le' S S')
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G' le' μ) :
    IsGWCascadeFamily G le μ := by
  have hsub : wedgePairs le ⊆ wedgePairs le' := fun p hp => ⟨hp.1, hp.2.1, hle _ _ hp.1 hp.2.1 hp.2.2⟩
  exact
    { isProbability := fun p hp => hμ.isProbability p (hsub hp)
      diag := hμ.diag
      cascade := fun S S' S'' hS hS' hS'' h1 h2 =>
        hμ.cascade S S' S'' hS hS' hS'' (hle _ _ hS hS' h1) (hle _ _ hS' hS'' h2)
      continuous := fun ω => (hμ.continuous ω).mono hsub
      covariant := fun A hA p hp => hμ.covariant A (hG hA) p (hsub hp)
      nondegenerate := hμ.nondegenerate }

/-! ## Clause (2), the kernels from the origin -/

/-- **`lem:gw-kernels-from-origin`(2)**: the kernels from the origin `μ_Σ = μ_{0,Σ}` of a
`(G, W)`-cascade family satisfy (a)–(c) (`IsOriginKernels`) and (d), with `ρ = μ_{Σ,Σ'}`. -/
theorem gw_kernels_from_origin {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) :
    IsOriginKernels G (fun S => μ 0 S) ∧
      ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' →
        IsProbabilityMeasure (μ S S') ∧ μ 0 S' = μ 0 S ∗ μ S S' := by
  have hmem : ∀ S : Mat d, S.PosSemidef → ((0 : Mat d), S) ∈ wedgePairs le :=
    fun S hS => ⟨PosSemidef.zero, hS, wedge_zero_le hW hS⟩
  refine ⟨⟨fun S hS => hμ.isProbability _ (hmem S hS), hμ.diag 0 PosSemidef.zero,
    hμ.nondegenerate, ?_, ?_⟩, ?_⟩
  · intro A hA S hS
    have h := hμ.covariant A hA _ (hmem S hS)
    simpa using h
  · intro ω
    exact (hμ.continuous ω).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun S hS => hmem S hS)
  · intro S S' hS hS' h
    haveI := hμ.isProbability _ (hmem S hS)
    haveI := hμ.isProbability (S, S') ⟨hS, hS', h⟩
    refine ⟨inferInstance, ?_⟩
    rw [hμ.cascade 0 S S' PosSemidef.zero hS hS' (wedge_zero_le hW hS) h, Measure.conv_comm]

/-- An increment is unique when the transform it divides has no zero: if `μ̂` has no zero and
`ν = μ * ρ = μ * ρ'` for probability measures, then `ρ = ρ'`. -/
theorem conv_left_cancel {μ ν ρ ρ' : Measure (Rd d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ'] (hz : ∀ ω, charFun μ ω ≠ 0)
    (h : ν = μ ∗ ρ) (h' : ν = μ ∗ ρ') : ρ = ρ' := by
  apply eq_of_charFun_eq
  intro ω
  have h2 := congrArg (fun m => charFun m ω) (h.symm.trans h')
  simp only [charFun_conv] at h2
  exact mul_left_cancel₀ (hz ω) h2

/-- **`lem:gw-kernels-from-origin`(2)**, uniqueness: if no `μ̂_Σ` has a zero, `μ_{Σ,Σ'}` is the
only probability measure `ρ` with `μ_{Σ'} = μ_Σ * ρ`, so the family is determined (on `P_W`) by its
kernels from the origin. -/
theorem gw_kernels_from_origin_unique {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) (hz : HasNoZeros fun S => μ 0 S) :
    (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → ∀ ρ : Measure (Rd d),
        IsProbabilityMeasure ρ → μ 0 S' = μ 0 S ∗ ρ → ρ = μ S S') ∧
      ∀ ν : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily G le ν →
        (∀ S : Mat d, S.PosSemidef → ν 0 S = μ 0 S) → EqOnPairs le μ ν := by
  have hk := gw_kernels_from_origin hW μ hμ
  have first : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → ∀ ρ : Measure (Rd d),
      IsProbabilityMeasure ρ → μ 0 S' = μ 0 S ∗ ρ → ρ = μ S S' := by
    intro S S' hS hS' h ρ hρ hc
    haveI := hk.1.isProbability S hS
    obtain ⟨hp, hc'⟩ := hk.2 S S' hS hS' h
    exact conv_left_cancel (hz S hS) hc hc'
  refine ⟨first, ?_⟩
  intro ν hν hνμ p hp
  obtain ⟨hp1, hp2, hle⟩ := hp
  obtain ⟨hνp, hνc⟩ := (gw_kernels_from_origin hW ν hν).2 p.1 p.2 hp1 hp2 hle
  rw [hνμ _ hp1, hνμ _ hp2] at hνc
  exact (first p.1 p.2 hp1 hp2 hle _ hνp hνc).symm

/-! ## Clause (3), the converse -/

/-- **`lem:gw-kernels-from-origin`(3)**, the converse: probability measures `(μ_Σ)` without zeros
of their transforms and with (a)–(d) are the kernels from the origin of a `(G, W)`-cascade family;
and any family `(μ_{Σ,Σ'})` of the measures `ρ` of (d) is such a family, with kernels from the
origin `μ_Σ` and `μ̂_{Σ,Σ'} = μ̂_{Σ'}/μ̂_Σ`. -/
theorem gw_kernels_from_origin_converse {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (m : Mat d → Measure (Rd d)) (hm : IsOriginKernels G m)
    (hz : HasNoZeros m) (hinc : HasIncrements le m) :
    IsKernelsFromOrigin G le m ∧
      ∀ ρ : Mat d → Mat d → Measure (Rd d),
        (∀ p ∈ wedgePairs le, IsProbabilityMeasure (ρ p.1 p.2) ∧ m p.2 = m p.1 ∗ ρ p.1 p.2) →
        IsGWCascadeFamily G le ρ ∧ (∀ S : Mat d, S.PosSemidef → ρ 0 S = m S) ∧
          ∀ p ∈ wedgePairs le, ∀ ω : Rd d,
            charFun (ρ p.1 p.2) ω = charFun (m p.2) ω / charFun (m p.1) ω := by
  have second : ∀ ρ : Mat d → Mat d → Measure (Rd d),
      (∀ p ∈ wedgePairs le, IsProbabilityMeasure (ρ p.1 p.2) ∧ m p.2 = m p.1 ∗ ρ p.1 p.2) →
      IsGWCascadeFamily G le ρ ∧ (∀ S : Mat d, S.PosSemidef → ρ 0 S = m S) ∧
        ∀ p ∈ wedgePairs le, ∀ ω : Rd d,
          charFun (ρ p.1 p.2) ω = charFun (m p.2) ω / charFun (m p.1) ω := by
    intro ρ hρ
    /- The quotient formula. -/
    have hq : ∀ p ∈ wedgePairs le, ∀ ω : Rd d,
        charFun (ρ p.1 p.2) ω = charFun (m p.2) ω / charFun (m p.1) ω := by
      intro p hp ω
      haveI := (hρ p hp).1
      haveI := hm.isProbability p.1 hp.1
      rw [(hρ p hp).2, charFun_conv, mul_div_cancel_left₀ _ (hz p.1 hp.1 ω)]
    have hq' : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → ∀ ω : Rd d,
        charFun (ρ S S') ω = charFun (m S') ω / charFun (m S) ω :=
      fun S S' hS hS' h ω => hq (S, S') ⟨hS, hS', h⟩ ω
    have hprob : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' →
        IsProbabilityMeasure (ρ S S') := fun S S' hS hS' h => (hρ (S, S') ⟨hS, hS', h⟩).1
    have hm0 : ∀ ω : Rd d, charFun (m 0) ω = 1 := fun ω => by rw [hm.zero, charFun_dirac]; simp
    /- The kernels from the origin. -/
    have horig : ∀ S : Mat d, S.PosSemidef → ρ 0 S = m S := by
      intro S hS
      haveI := hprob 0 S PosSemidef.zero hS (wedge_zero_le hW hS)
      haveI := hm.isProbability S hS
      apply eq_of_charFun_eq
      intro ω
      rw [hq' 0 S PosSemidef.zero hS (wedge_zero_le hW hS), hm0, div_one]
    refine ⟨⟨fun p hp => (hρ p hp).1, ?_, ?_, ?_, ?_, ?_⟩, horig, hq⟩
    · -- (K1), the diagonal
      intro S hS
      haveI := hprob S S hS hS (hW.refl S hS)
      apply eq_of_charFun_eq
      intro ω
      rw [hq' S S hS hS (hW.refl S hS), div_self (hz S hS ω), charFun_dirac]
      simp
    · -- (K1), the cascade
      intro S S' S'' hS hS' hS'' h1 h2
      have h3 := hW.trans S S' S'' hS hS' hS'' h1 h2
      haveI := hprob S S'' hS hS'' h3
      haveI := hprob S S' hS hS' h1
      haveI := hprob S' S'' hS' hS'' h2
      apply eq_of_charFun_eq
      intro ω
      rw [charFun_conv, hq' S S'' hS hS'' h3, hq' S S' hS hS' h1, hq' S' S'' hS' hS'' h2]
      field_simp [hz S hS ω, hz S' hS' ω]
    · -- (K2)
      intro ω
      have hc : ContinuousOn (fun p : Mat d × Mat d => charFun (m p.2) ω / charFun (m p.1) ω)
          (wedgePairs le) := by
        apply ContinuousOn.div
        · exact (hm.continuous ω).comp continuous_snd.continuousOn (fun p hp => hp.2.1)
        · exact (hm.continuous ω).comp continuous_fst.continuousOn (fun p hp => hp.1)
        · exact fun p hp => hz p.1 hp.1 ω
      exact hc.congr fun p hp => hq p hp ω
    · -- (K3)
      intro A hA p hp
      have hAp : (act A p.1, act A p.2) ∈ wedgePairs le :=
        ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1,
          hW.invariant A hA _ _ hp.1 hp.2.1 hp.2.2⟩
      haveI := (hρ p hp).1
      haveI := (hρ _ hAp).1
      apply eq_of_charFun_eq
      intro ω
      have hb1 := congrArg (fun μ => charFun μ ω) (hm.covariant A hA p.1 hp.1)
      have hb2 := congrArg (fun μ => charFun μ ω) (hm.covariant A hA p.2 hp.2.1)
      simp only [push, charFun_map_lin] at hb1 hb2
      rw [push, charFun_map_lin, hq p hp, hq _ hAp]
      simp only
      rw [hb1, hb2]
    · -- (K4)
      rw [horig 1 PosSemidef.one]
      exact hm.one_ne
  refine ⟨?_, second⟩
  /- A family of increments, by choice, and the family it makes. -/
  classical
  let ρ : Mat d → Mat d → Measure (Rd d) := fun S S' =>
    if h : S.PosSemidef ∧ S'.PosSemidef ∧ le S S' then (hinc S S' h.1 h.2.1 h.2.2).choose
    else 0
  have hρ : ∀ p ∈ wedgePairs le, IsProbabilityMeasure (ρ p.1 p.2) ∧ m p.2 = m p.1 ∗ ρ p.1 p.2 := by
    intro p hp
    have h : p.1.PosSemidef ∧ p.2.PosSemidef ∧ le p.1 p.2 := hp
    simp only [ρ, dif_pos h]
    exact (hinc p.1 p.2 h.1 h.2.1 h.2.2).choose_spec
  obtain ⟨hfam, horig, -⟩ := second ρ hρ
  exact ⟨ρ, hfam, horig⟩

end AffineHemigroup
