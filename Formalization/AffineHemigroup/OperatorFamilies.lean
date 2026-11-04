/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OperatorsKernels
import AffineHemigroup.LoewnerWedge

/-!
# `lem:operators-to-kernels-families`: from operator families to kernel families

Blueprint: `blueprint/src/parts/04-classical.tex`, clauses (4) and (5) of
`lem:operators-to-kernels`, split off (ADR-0025). Q-0281, wave M, phase 2.

Each kernel axiom is the corresponding operator axiom read through the uniqueness of the
representing measure (`eq_of_mconvL1E_eq`): the cascade through `ScaleSpace.mconvL1E_comp`, the
diagonal through `ScaleSpace.eq_dirac_of_mconvL1E_eq_id`, covariance (and the rotation and dilation
axioms of the isotropic family) through the transport of `lem:operators-to-kernels`(2), and (K2)
from the continuity of `p ↦ Φ_p φ` by `μ̂_p(ω) = (Φ_p φ)^(ω) / φ̂(ω)`
(`continuousOn_charFun_of_conv`), without sequences.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory Complex
open scoped Topology MatrixOrder RealInnerProductSpace
open ScaleSpace (transL1E dilL1E matEquiv mconvL1E charCLME)

variable {d : ℕ}

/-! ## `lem:operators-to-kernels-families`: (4) and (5) -/

/-- Reading `IsConvOnPairs` at a pair: the measure is a probability measure. -/
theorem IsConvOnPairs.prob {le : Mat d → Mat d → Prop} {Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)}
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsConvOnPairs le Φ μ) {p : Mat d × Mat d}
    (hp : p ∈ wedgePairs le) : IsProbabilityMeasure (μ p.1 p.2) :=
  (hμ p hp).1

/-- Reading `IsConvOnPairs` at a pair: the operator is convolution by the measure. -/
theorem IsConvOnPairs.eq {le : Mat d → Mat d → Prop} {Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)}
    {μ : Mat d → Mat d → Measure (Rd d)} (hμ : IsConvOnPairs le Φ μ) {p : Mat d × Mat d}
    (hp : p ∈ wedgePairs le) :
    haveI := hμ.prob hp
    Φ p.1 p.2 = mconvL1E (μ p.1 p.2) :=
  (hμ p hp).2

/-- **(K2) from continuity into `L¹`**: on a set of parameters where `Φ_p = μ_p ∗ ·`, the
continuity of `p ↦ Φ_p φ` gives that of `p ↦ μ̂_p(ω)`. -/
theorem continuousOn_charFun_of_conv {P : Type*} [TopologicalSpace P] {s : Set P}
    (Φ : P → (L1 d →L[ℝ] L1 d)) (μ : P → Measure (Rd d))
    (hμ : ∀ p ∈ s, ∃ _ : IsProbabilityMeasure (μ p), Φ p = mconvL1E (μ p))
    (hΦ : ContinuousOn (fun p => Φ p (gaussL1 d)) s) (ω : Rd d) :
    ContinuousOn (fun p => charFun (μ p) ω) s := by
  refine (((charCLME ω).continuous.comp_continuousOn hΦ).mul
    (continuousOn_const (c := (charCLME ω (gaussL1 d))⁻¹))).congr
    fun p hp => ?_
  obtain ⟨_, hp'⟩ := hμ p hp
  change charFun (μ p) ω = charCLME ω (Φ p (gaussL1 d)) * (charCLME ω (gaussL1 d))⁻¹
  rw [hp']
  exact charFun_eq_charCLME_div (μ p) ω

/-- **`lem:operators-to-kernels-families`(4)**: for a wedge datum `(G, W)` and a
`(G, W)`-cascade family of operators, the measures representing the operators form a
`(G, W)`-cascade family of kernels. -/
theorem operators_to_kernels_gw (_hd : 1 ≤ d) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d))
    (hΦ : IsGWOperatorFamily G le Φ) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsConvOnPairs le Φ μ) :
    IsGWCascadeFamily G le μ where
  isProbability p hp := hμ.prob hp
  diag S hS := by
    have hp : (S, S) ∈ wedgePairs le := ⟨hS, hS, hW.refl S hS⟩
    haveI := hμ.prob hp
    refine ScaleSpace.eq_dirac_of_mconvL1E_eq_id ?_
    exact (hμ.eq hp).symm.trans (hΦ.diag S hS)
  cascade S S' S'' hS hS' hS'' h1 h2 := by
    have hp1 : (S, S') ∈ wedgePairs le := ⟨hS, hS', h1⟩
    have hp2 : (S', S'') ∈ wedgePairs le := ⟨hS', hS'', h2⟩
    have hp3 : (S, S'') ∈ wedgePairs le := ⟨hS, hS'', hW.trans S S' S'' hS hS' hS'' h1 h2⟩
    haveI := hμ.prob hp1
    haveI := hμ.prob hp2
    haveI := hμ.prob hp3
    have h := hΦ.cascade S S' S'' hS hS' hS'' h1 h2
    rw [hμ.eq hp1, hμ.eq hp2, hμ.eq hp3, ScaleSpace.mconvL1E_comp] at h
    rw [Measure.conv_comm]
    exact (eq_of_mconvL1E_eq h).symm
  continuous ω := continuousOn_charFun_of_conv (fun p => Φ p.1 p.2) (fun p => μ p.1 p.2)
    (fun p hp => hμ p hp) (hΦ.continuous (gaussL1 d)) ω
  covariant A hA p hp := by
    have hAu : IsUnit A.det := hW.closedSubgroup.subset_gl hA
    have hq : (act A p.1, act A p.2) ∈ wedgePairs le :=
      ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1,
        hW.invariant A hA p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
    haveI := hμ.prob hp
    haveI := hμ.prob hq
    have h := hΦ.covariant A hA hAu p hp
    rw [hμ.eq hp, hμ.eq hq] at h
    exact (operators_to_kernels_transport_iff _hd _ _ A hAu).mp h
  nondegenerate := by
    intro h
    have hp := wedge_zero_one_mem hW
    haveI := hμ.prob hp
    refine hΦ.nondegenerate ?_
    rw [hμ.eq hp]
    change mconvL1E (μ 0 1) = _
    rw [ScaleSpace.mconvL1E_congr h, ScaleSpace.mconvL1E_dirac_zero]

/-- **`lem:operators-to-kernels-families`(4)**, the affine family: operators with the axioms of
the case `(GL(d), Loewner)` give an affine cascade family. -/
theorem operators_to_kernels_affine (hd : 1 ≤ d) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d))
    (hΦ : IsGWOperatorFamily (glSet d) loewnerLE Φ) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsConvOnPairs loewnerLE Φ μ) :
    IsAffineCascadeFamily μ :=
  operators_to_kernels_gw hd
    (isWedgeDatum_loewner glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2) Φ hΦ μ hμ

/-- **`lem:operators-to-kernels-families`(5)**: operators with the isotropic
axioms give an isotropic cascade family, with the same dilation action. -/
theorem operators_to_kernels_isotropic (_hd : 1 ≤ d) (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d))
    (S : ℝ → ℝ → ℝ) (hΦ : IsIsotropicOperatorFamily Φ S) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t)) :
    IsIsotropicCascadeFamily μ S where
  isProbability s t hs hst := (hμ s t hs hst).1
  diag t ht := by
    obtain ⟨_, h⟩ := hμ t t ht le_rfl
    exact ScaleSpace.eq_dirac_of_mconvL1E_eq_id (h.symm.trans (hΦ.diag t ht))
  cascade r s t hr hrs hst := by
    obtain ⟨_, h1⟩ := hμ r s hr hrs
    obtain ⟨_, h2⟩ := hμ s t (hr.trans hrs) hst
    obtain ⟨_, h3⟩ := hμ r t hr (hrs.trans hst)
    have h := hΦ.cascade r s t hr hrs hst
    rw [h1, h2, h3, ScaleSpace.mconvL1E_comp] at h
    rw [Measure.conv_comm]
    exact (eq_of_mconvL1E_eq h).symm
  continuous ξ := continuousOn_charFun_of_conv (fun p : ℝ × ℝ => Φ p.1 p.2)
    (fun p : ℝ × ℝ => μ p.1 p.2) (fun p hp => hμ p.1 p.2 hp.1 hp.2) (hΦ.continuous (gaussL1 d)) ξ
  rotation Q hQ s t hs hst := by
    obtain ⟨_, h⟩ := hμ s t hs hst
    have hrot := hΦ.rotation Q hQ s t hs hst
    rw [h] at hrot
    have hconj := (dil_conj_eq_iff Q (isUnit_det_of_mem_orthSet hQ) (mconvL1E (μ s t))
      (mconvL1E (μ s t))).mpr hrot.symm
    exact (operators_to_kernels_transport_iff _hd _ _ Q (isUnit_det_of_mem_orthSet hQ)).mp hconj
  scale_bij := hΦ.scale_bij
  scale lam hlam s t hs hst := by
    have hb := hΦ.scale_bij lam hlam
    have hSs : 0 ≤ S lam s := hb.mapsTo (show s ∈ Ici 0 from hs)
    have hSst : S lam s ≤ S lam t :=
      hb.strictMonoOn.monotoneOn (show s ∈ Ici 0 from hs) (show t ∈ Ici 0 from hs.trans hst) hst
    obtain ⟨_, h⟩ := hμ s t hs hst
    obtain ⟨_, h'⟩ := hμ (S lam s) (S lam t) hSs hSst
    have hsc := hΦ.scale lam hlam s t hs hst
    rw [h, h'] at hsc
    have hconj := (dil_conj_eq_iff _ (isUnit_det_smul_one hlam) (mconvL1E (μ s t))
      (mconvL1E (μ (S lam s) (S lam t)))).mpr hsc
    exact (operators_to_kernels_transport_iff _hd _ _ _ (isUnit_det_smul_one hlam)).mp hconj
  nondegenerate s t hs hst := by
    intro h0
    obtain ⟨_, h⟩ := hμ s t hs hst.le
    refine hΦ.nondegenerate s t hs hst ?_
    rw [h, ScaleSpace.mconvL1E_congr h0, ScaleSpace.mconvL1E_dirac_zero]

end AffineHemigroup
