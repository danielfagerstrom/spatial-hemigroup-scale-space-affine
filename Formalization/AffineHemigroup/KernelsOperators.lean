/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KernelsContinuity
import AffineHemigroup.OperatorFamilies
import AffineHemigroup.MatrixCalculus

/-!
# `lem:kernels-to-operators`(2), (3): from kernel families to operator families

Blueprint: `blueprint/src/parts/04-classical.tex`. Q-0281, wave M, phase 2.

The converses of `lem:operators-to-kernels-families`. Each operator axiom is a kernel axiom read
through `lem:operators-to-kernels`(1)–(2): the single-operator axioms are the converse of (1), the
cascade is `ScaleSpace.mconvL1E_comp`, the diagonal `ScaleSpace.mconvL1E_dirac_zero`, covariance
(and the rotation and dilation axioms) the transport, (ND) uniqueness. Continuity in `L¹` is
clause (1), `AffineHemigroup.KernelsContinuity`, read sequentially (`continuousOn_mconvL1E`):
the parameter spaces are first countable. The correspondence is stated as round trips on `P_W`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder
open ScaleSpace (dilL1E matEquiv mconvL1E)

variable {d : ℕ}

/-- **Continuity on a parameter set, from (K2) and clause (1)**: if the transforms of a family of
probability measures are continuous on `s` at every frequency, then `p ↦ ν_p ∗ f` is continuous on
`s` into `L¹(ℝ^d)`; continuity on a subset of a first-countable space is sequential. -/
theorem continuousOn_mconvL1E (hd : 1 ≤ d) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] {s : Set P} (ν : P → Measure (Rd d))
    [∀ p, IsProbabilityMeasure (ν p)] (hc : ∀ ω, ContinuousOn (fun p => charFun (ν p) ω) s)
    (f : L1 d) :
    ContinuousOn (fun p => mconvL1E (ν p) f) s := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro x hx
  exact kernels_to_operators_continuity hd (fun n => ν (x n)) (ν p)
    (fun ω => (hc ω p hp).tendsto.comp hx) f

/-- A family read on `P_W`, extended by `δ₀` off it: a probability measure at every pair. -/
noncomputable def extendOnPairs (le : Mat d → Mat d → Prop) (μ : Mat d → Mat d → Measure (Rd d))
    (p : Mat d × Mat d) : Measure (Rd d) :=
  open Classical in if p ∈ wedgePairs le then μ p.1 p.2 else Measure.dirac 0

/-- The extension by `δ₀` is a probability measure at every pair. -/
theorem isProbabilityMeasure_extendOnPairs {le : Mat d → Mat d → Prop}
    {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : ∀ p ∈ wedgePairs le, IsProbabilityMeasure (μ p.1 p.2)) (p : Mat d × Mat d) :
    IsProbabilityMeasure (extendOnPairs le μ p) := by
  unfold extendOnPairs
  split_ifs with h
  · exact hμ p h
  · infer_instance

/-- **`lem:kernels-to-operators`(2)**: for a wedge datum `(G, W)` and a `(G, W)`-cascade family
of kernels `μ`, operators that are convolution by `μ` on `P_W` form a `(G, W)`-cascade family of
operators, and the measure that `lem:operators-to-kernels`(1) gives for `Φ_{Σ,Σ'}` is
`μ_{Σ,Σ'}`. -/
theorem kernels_to_operators_gw (hd : 1 ≤ d) {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G le μ) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d))
    (hΦ : IsConvOnPairs le Φ μ) :
    IsGWOperatorFamily G le Φ ∧
      ∀ p ∈ wedgePairs le, ∀ ν : Measure (Rd d), ∀ _ : IsProbabilityMeasure ν,
        Φ p.1 p.2 = mconvL1E ν → ν = μ p.1 p.2 := by
  refine ⟨⟨fun p hp => ?_, fun S hS => ?_, fun S S' S'' hS hS' hS'' h1 h2 => ?_, fun f => ?_, ?_,
    fun A hA hAu p hp => ?_⟩, fun p hp ν _ h => ?_⟩
  · haveI := hΦ.prob hp
    rw [hΦ.eq hp]
    exact operators_to_kernels_converse hd _
  · have hp : (S, S) ∈ wedgePairs le := ⟨hS, hS, hW.refl S hS⟩
    haveI := hΦ.prob hp
    rw [hΦ.eq hp]
    change mconvL1E (μ S S) = _
    rw [ScaleSpace.mconvL1E_congr (hμ.diag S hS), ScaleSpace.mconvL1E_dirac_zero]
  · have hp1 : (S, S') ∈ wedgePairs le := ⟨hS, hS', h1⟩
    have hp2 : (S', S'') ∈ wedgePairs le := ⟨hS', hS'', h2⟩
    have hp3 : (S, S'') ∈ wedgePairs le := ⟨hS, hS'', hW.trans S S' S'' hS hS' hS'' h1 h2⟩
    haveI := hΦ.prob hp1
    haveI := hΦ.prob hp2
    haveI := hΦ.prob hp3
    rw [hΦ.eq hp1, hΦ.eq hp2, hΦ.eq hp3]
    change (mconvL1E (μ S' S'')).comp (mconvL1E (μ S S')) = mconvL1E (μ S S'')
    rw [ScaleSpace.mconvL1E_comp, ScaleSpace.mconvL1E_congr
      ((hμ.cascade S S' S'' hS hS' hS'' h1 h2).trans (Measure.conv_comm _ _)).symm]
  · haveI := isProbabilityMeasure_extendOnPairs (fun p hp => hμ.isProbability p hp)
    refine (continuousOn_mconvL1E hd (extendOnPairs le μ) (fun ω => ?_) f).congr fun p hp => ?_
    · refine (hμ.continuous ω).congr fun q hq => ?_
      simp only [extendOnPairs, if_pos hq]
    · haveI := hΦ.prob hp
      change Φ p.1 p.2 f = mconvL1E (extendOnPairs le μ p) f
      rw [hΦ.eq hp]
      congr 1
      exact ScaleSpace.mconvL1E_congr (by simp only [extendOnPairs, if_pos hp])
  · intro h
    have hp := wedge_zero_one_mem hW
    haveI := hΦ.prob hp
    refine hμ.nondegenerate (ScaleSpace.eq_dirac_of_mconvL1E_eq_id ?_)
    exact (hΦ.eq hp).symm.trans h
  · have hq : (act A p.1, act A p.2) ∈ wedgePairs le :=
      ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1,
        hW.invariant A hA p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
    haveI := hΦ.prob hp
    haveI := hΦ.prob hq
    rw [hΦ.eq hp, hΦ.eq hq, dil_conj_mconvL1E]
    exact ScaleSpace.mconvL1E_congr (hμ.covariant A hA p hp)
  · haveI := hΦ.prob hp
    exact eq_of_mconvL1E_eq (h.symm.trans (hΦ.eq hp))

/-- **`lem:kernels-to-operators`(2)**, the correspondence: for a wedge datum, convolution is a
one-to-one correspondence between the `(G, W)`-cascade families of kernels and those of
operators, read on `P_W`. -/
theorem kernels_operators_correspondence (hd : 1 ≤ d) {G : Set (Mat d)}
    {le : Mat d → Mat d → Prop} (hW : IsWedgeDatum G le) :
    (∀ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily G le μ →
        ∃ Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d), IsConvOnPairs le Φ μ) ∧
      (∀ Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d), IsGWOperatorFamily G le Φ →
        ∃ μ : Mat d → Mat d → Measure (Rd d), IsConvOnPairs le Φ μ) ∧
      (∀ (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)) (μ : Mat d → Mat d → Measure (Rd d)),
        IsConvOnPairs le Φ μ → (IsGWOperatorFamily G le Φ ↔ IsGWCascadeFamily G le μ)) ∧
      (∀ (Φ Φ' : Mat d → Mat d → (L1 d →L[ℝ] L1 d)) (μ μ' : Mat d → Mat d → Measure (Rd d)),
        IsConvOnPairs le Φ μ → IsConvOnPairs le Φ' μ' →
          ((∀ p ∈ wedgePairs le, Φ p.1 p.2 = Φ' p.1 p.2) ↔ EqOnPairs le μ μ')) := by
  classical
  refine ⟨fun μ hμ => ?_, fun Φ hΦ => ?_, fun Φ μ hc => ⟨fun hΦ => ?_, fun hμ => ?_⟩,
    fun Φ Φ' μ μ' hc hc' => ⟨fun h p hp => ?_, fun h p hp => ?_⟩⟩
  · haveI := isProbabilityMeasure_extendOnPairs (fun p hp => hμ.isProbability p hp)
    refine ⟨fun S S' => mconvL1E (extendOnPairs le μ (S, S')), fun p hp => ?_⟩
    haveI := hμ.isProbability p hp
    refine ⟨inferInstance, ScaleSpace.mconvL1E_congr ?_⟩
    simp only [extendOnPairs, if_pos hp]
  · have hex : ∀ S S' : Mat d, ∃ μ : Measure (Rd d),
        (S, S') ∈ wedgePairs le → ∃ _ : IsProbabilityMeasure μ, Φ S S' = mconvL1E μ := by
      intro S S'
      by_cases h : (S, S') ∈ wedgePairs le
      · obtain ⟨μ, hμ, -⟩ := operators_to_kernels_repr hd (Φ S S') (hΦ.single _ h)
        exact ⟨μ, fun _ => hμ⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose μ hμ using hex
    exact ⟨μ, fun p hp => hμ p.1 p.2 hp⟩
  · exact operators_to_kernels_gw hd hW Φ hΦ μ hc
  · exact (kernels_to_operators_gw hd hW μ hμ Φ hc).1
  · haveI := hc.prob hp
    haveI := hc'.prob hp
    have := h p hp
    rw [hc.eq hp, hc'.eq hp] at this
    exact eq_of_mconvL1E_eq this
  · haveI := hc.prob hp
    haveI := hc'.prob hp
    rw [hc.eq hp, hc'.eq hp]
    exact ScaleSpace.mconvL1E_congr (h p hp)

/-- The isotropic parameter set `{0 ≤ s ≤ t}`, extended by `δ₀` off it. -/
noncomputable def extendOnScales (μ : ℝ → ℝ → Measure (Rd d)) (p : ℝ × ℝ) : Measure (Rd d) :=
  open Classical in if 0 ≤ p.1 ∧ p.1 ≤ p.2 then μ p.1 p.2 else Measure.dirac 0

/-- The extension by `δ₀` is a probability measure at every pair of scales. -/
theorem isProbabilityMeasure_extendOnScales {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (p : ℝ × ℝ) :
    IsProbabilityMeasure (extendOnScales μ p) := by
  unfold extendOnScales
  split_ifs with h
  · exact hμ p.1 p.2 h.1 h.2
  · infer_instance

/-- **`lem:kernels-to-operators`(3)**: for an isotropic cascade family `μ` with dilation action
`S`, operators that are convolution by `μ` on `{0 ≤ s ≤ t}` satisfy the axioms of
`lem:operators-to-kernels`(5) with the same `S`, and the measure that
`lem:operators-to-kernels`(1) gives for `Φ_{s,t}` is `μ_{s,t}`. -/
theorem kernels_to_operators_isotropic (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (S : ℝ → ℝ → ℝ) (hμ : IsIsotropicCascadeFamily μ S) (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d))
    (hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t)) :
    IsIsotropicOperatorFamily Φ S ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ν : Measure (Rd d), ∀ _ : IsProbabilityMeasure ν,
        Φ s t = mconvL1E ν → ν = μ s t := by
  have hS : ∀ lam, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ S lam s ∧ S lam s ≤ S lam t :=
    fun lam hlam s t hs hst =>
      ⟨(hμ.scale_bij lam hlam).mapsTo (show s ∈ Ici 0 from hs),
        (hμ.scale_bij lam hlam).strictMonoOn.monotoneOn (show s ∈ Ici 0 from hs)
          (show t ∈ Ici 0 from hs.trans hst) hst⟩
  refine ⟨⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun f => ?_,
    fun Q hQ s t hs hst => ?_, hμ.scale_bij, fun lam hlam s t hs hst => ?_,
    fun s t hs hst => ?_⟩, fun s t hs hst ν _ h => ?_⟩
  · obtain ⟨_, h⟩ := hΦ s t hs hst
    rw [h]
    exact operators_to_kernels_converse hd _
  · obtain ⟨_, h⟩ := hΦ t t ht le_rfl
    rw [h, ScaleSpace.mconvL1E_congr (hμ.diag t ht), ScaleSpace.mconvL1E_dirac_zero]
  · obtain ⟨_, h1⟩ := hΦ r s hr hrs
    obtain ⟨_, h2⟩ := hΦ s t (hr.trans hrs) hst
    obtain ⟨_, h3⟩ := hΦ r t hr (hrs.trans hst)
    rw [h1, h2, h3, ScaleSpace.mconvL1E_comp, ScaleSpace.mconvL1E_congr
      ((hμ.cascade r s t hr hrs hst).trans (Measure.conv_comm _ _)).symm]
  · haveI := isProbabilityMeasure_extendOnScales hμ.isProbability
    refine (continuousOn_mconvL1E hd (extendOnScales μ) (fun ω => ?_) f).congr fun p hp => ?_
    · refine (hμ.continuous ω).congr fun q hq => ?_
      simp only [extendOnScales, if_pos (show 0 ≤ q.1 ∧ q.1 ≤ q.2 from hq)]
    · obtain ⟨_, h⟩ := hΦ p.1 p.2 hp.1 hp.2
      change Φ p.1 p.2 f = mconvL1E (extendOnScales μ p) f
      rw [h]
      congr 1
      exact ScaleSpace.mconvL1E_congr
        (by simp only [extendOnScales, if_pos (show 0 ≤ p.1 ∧ p.1 ≤ p.2 from hp)])
  · obtain ⟨_, h⟩ := hΦ s t hs hst
    rw [h]
    have hconj := dil_conj_mconvL1E (μ s t) Q (isUnit_det_of_mem_orthSet hQ)
    rw [ScaleSpace.mconvL1E_congr (hμ.rotation Q hQ s t hs hst)] at hconj
    exact ((dil_conj_eq_iff _ _ _ _).mp hconj).symm
  · obtain ⟨h0, h01⟩ := hS lam hlam s t hs hst
    obtain ⟨_, h⟩ := hΦ s t hs hst
    obtain ⟨_, h'⟩ := hΦ (S lam s) (S lam t) h0 h01
    rw [h, h']
    have hconj := dil_conj_mconvL1E (μ s t) _ (isUnit_det_smul_one hlam)
    rw [ScaleSpace.mconvL1E_congr (hμ.scale lam hlam s t hs hst)] at hconj
    exact (dil_conj_eq_iff _ _ _ _).mp hconj
  · intro h1
    obtain ⟨_, h⟩ := hΦ s t hs hst.le
    exact hμ.nondegenerate s t hs hst (ScaleSpace.eq_dirac_of_mconvL1E_eq_id (h.symm.trans h1))
  · obtain ⟨_, h'⟩ := hΦ s t hs hst
    exact eq_of_mconvL1E_eq (h.symm.trans h')

end AffineHemigroup
