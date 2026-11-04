/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityGeneral
import AffineHemigroup.CascadeDivisible
import AffineHemigroup.SimilarityRays

/-!
# `prop:similarity-cascade-families`: infinitely divisible increments are a theorem of the axioms

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-cascade-families`.

For a closed subgroup `G ⊇ S(d)` and a `(G, Loewner)`-cascade family: (1) every increment and every
kernel from the origin is infinitely divisible (A6 through `thm:cascade-infinitely-divisible`(2), the
path condition by the segment, `lem:path-condition-orders`(3)(a)); every `μ_Σ`, `Σ ∈ PD(d)`, is
symmetric with a triplet `(C, L, 0)`, `L` symmetric (A3(i)–(ii)); similarity covariance; and every
Loewner step of `PD(d)` has the infinitely divisible increment `μ_{Σ,Σ'}`; (2) so the family of
kernels from the origin is in the setting of `prop:similarity-general-sandwich`, with infinitely
divisible Loewner increments; (3) for elliptical parts, `prop:similarity-orbit-family`(2)–(3) hold.

## Route

The blueprint's: the drift `β = 0` and the symmetry of `L` come from the reflected triplet
`(C, (-I)_*L, -β)` of `(-I)_*μ_Σ = μ_Σ` and the uniqueness A3(ii) (`LevyTriplet.pushIso` at
`x ↦ -x`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **A symmetric infinitely divisible law has drift `0` and a symmetric Lévy measure** (A3(ii)). -/
theorem symm_triplet_of_symm {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hs : push (-1) μ = μ) {T : LevyTriplet d}
    (hT : HasTriplet μ T) :
    T.γ = 0 ∧ T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν := by
  have hT' : HasTriplet μ (T.pushIso (LinearIsometryEquiv.neg ℝ)) := fun z => by
    rw [T.lkExponent_pushIso, ← hT]
    have h := charFun_map_lin (-1 : Mat d) μ z
    rw [← push, hs, transpose_neg, transpose_one, lin_neg_one_apply] at h
    rw [h]
    rfl
  obtain ⟨-, hν, hγ⟩ := levy_khintchine_unique μ hid T _ hT hT'
  refine ⟨?_, hν.symm⟩
  have hγ' : T.γ = -T.γ := hγ
  have : (2 : ℝ) • T.γ = 0 := by rw [two_smul]; nth_rewrite 2 [hγ']; exact add_neg_cancel _
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

theorem push_neg_one_eq_map_neg (M : Measure (Rd d)) :
    push (-1) M = M.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) := by
  unfold push
  congr 1
  funext x
  rw [lin_neg_one_apply]
  rfl

/-- `S(d)` contains the dilations `cI`. -/
theorem smul_one_mem_simSet {c : ℝ} (hc : 0 < c) : c • (1 : Mat d) ∈ simSet d :=
  ⟨c, hc, 1, (Matrix.orthogonalGroup (Fin d) ℝ).one_mem, rfl⟩

theorem sqrt_smul_mem_simSet {c : ℝ} (hc : 0 < c) {Q : Mat d} (hQ : Q ∈ orthSet d) :
    Real.sqrt c • Q ∈ simSet d :=
  ⟨Real.sqrt c, Real.sqrt_pos.2 hc, Q, hQ, rfl⟩

/-- **`prop:similarity-cascade-families`(1)**: for a closed subgroup `G ⊇ S(d)` and a
`(G, Loewner)`-cascade family, every increment is infinitely divisible; every kernel from the origin
`μ_Σ`, `Σ ∈ PD(d)`, is a symmetric infinitely divisible law with a triplet `(C, L, 0)`, `L`
symmetric; `(√c Q)_*μ_Σ = μ_{cQΣQᵀ}`; and every Loewner step in `PD(d)` has the infinitely divisible
increment `μ_{Σ,Σ'}`. Spends A6 and A3(i)–(ii). -/
theorem sim_cascade_infinitelyDivisible (hd : 2 ≤ d) (G : Set (Mat d))
    (hG : IsClosedSubgroupGL G) (hsim : simSet d ⊆ G) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G loewnerLE μ) :
    (∀ p ∈ wedgePairs loewnerLE, IsInfinitelyDivisible (μ p.1 p.2)) ∧
      (∀ S : Mat d, S.PosDef → IsProbabilityMeasure (μ 0 S) ∧ push (-1) (μ 0 S) = μ 0 S ∧
        IsInfinitelyDivisible (μ 0 S) ∧
        ∃ T : LevyTriplet d, T.γ = 0 ∧ push (-1) T.ν = T.ν ∧ HasTriplet (μ 0 S) T) ∧
      (∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
        push (Real.sqrt c • Q) (μ 0 S) = μ 0 (c • (Q * S * Qᵀ))) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
        IsInfinitelyDivisible (μ S S') ∧ μ 0 S' = μ 0 S ∗ μ S S' := by
  have hW : IsWedgeDatum G loewnerLE :=
    isWedgeDatum_loewner hG fun c hc => hsim (smul_one_mem_simSet hc)
  have hP : HasPathCondition (loewnerLE (d := d)) := fun S S' hS hS' hle =>
    ⟨_, chain_loewner S S' hS hS' hle⟩
  obtain ⟨hpair, hzero⟩ := gw_family_infinitelyDivisible (by omega) hW hP μ hμ
  have hpsd0 : (0 : Mat d).PosSemidef := PosSemidef.zero
  have hle0 : ∀ S : Mat d, S.PosSemidef → loewnerLE 0 S := fun S hS => by
    unfold loewnerLE; rwa [sub_zero]
  have hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (μ 0 S) := fun S hS =>
    hμ.isProbability (0, S) ⟨hpsd0, hS, hle0 S hS⟩
  have hsymm : ∀ S : Mat d, S.PosSemidef → push (-1) (μ 0 S) = μ 0 S := fun S hS => by
    have h := hμ.covariant (-1) (hsim neg_one_mem_simSet) (0, S) ⟨hpsd0, hS, hle0 S hS⟩
    rw [h, act_zero]
    congr 1
    simp [act]
  refine ⟨hpair, fun S hS => ?_, fun S hS c hc Q hQ => ?_, fun S S' hS hS' hle => ?_⟩
  · haveI := hprob S hS.posSemidef
    obtain ⟨T, hT⟩ := levy_khintchine_exists (μ 0 S) (hzero S hS.posSemidef)
    obtain ⟨hγ, hν⟩ := symm_triplet_of_symm (hzero S hS.posSemidef) (hsymm S hS.posSemidef) hT
    exact ⟨inferInstance, hsymm S hS.posSemidef, hzero S hS.posSemidef, T, hγ,
      by rw [push_neg_one_eq_map_neg, hν], hT⟩
  · have h := hμ.covariant _ (hsim (sqrt_smul_mem_simSet hc hQ)) (0, S)
      ⟨hpsd0, hS.posSemidef, hle0 S hS.posSemidef⟩
    rw [h, act_zero, act_sqrt_smul c hc.le]
  · refine ⟨hpair (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩, ?_⟩
    haveI := hprob S hS.posSemidef
    haveI := hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩
    rw [hμ.cascade 0 S S' hpsd0 hS.posSemidef hS'.posSemidef (hle0 S hS.posSemidef) hle,
      Measure.conv_comm]

/-- **`prop:similarity-cascade-families`(2)**, the general part: `(μ_Σ)_{Σ ∈ PD(d)}` is a family as
in `prop:similarity-general-sandwich`, and every Loewner step in `PD(d)` has an infinitely divisible
increment; so the clauses of `prop:similarity-general-sandwich`,
`prop:similarity-general-bounded-shape` and `prop:similarity-general-index-zero` apply to it under
their remaining hypotheses alone. -/
theorem sim_cascade_general (hd : 2 ≤ d) (G : Set (Mat d)) (hG : IsClosedSubgroupGL G)
    (hsim : simSet d ⊆ G) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G loewnerLE μ) :
    (∃ (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)), IsSimGeneralFamily (fun S => μ 0 S) C L) ∧
      HasIDLoewnerIncrements fun S => μ 0 S := by
  obtain ⟨-, hker, hcov, hinc⟩ := sim_cascade_infinitelyDivisible hd G hG hsim μ hμ
  classical
  let T : Mat d → LevyTriplet d := fun S =>
    if hS : S.PosDef then Classical.choose (hker S hS).2.2.2 else
      (Classical.choose (hker 1 PosDef.one).2.2.2)
  have hT : ∀ S : Mat d, S.PosDef → (T S).γ = 0 ∧ push (-1) (T S).ν = (T S).ν ∧
      HasTriplet (μ 0 S) (T S) := fun S hS => by
    simp only [T, dif_pos hS]
    exact Classical.choose_spec (hker S hS).2.2.2
  refine ⟨⟨fun S => (T S).A, fun S => (T S).ν,
    { isProbability := fun S hS => (hker S hS).1
      symmetric := fun S hS => (hker S hS).2.1
      infinitelyDivisible := fun S hS => (hker S hS).2.2.1
      triplet := fun S hS => ⟨T S, rfl, rfl, (hT S hS).1, (hT S hS).2.2⟩
      covariant := hcov }⟩, fun S S' hS hS' hle => ?_⟩
  obtain ⟨hid, heq⟩ := hinc S S' hS hS' hle
  exact ⟨μ S S', hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩, hid, heq⟩

/-- **`prop:similarity-cascade-families`(3)**, elliptical parts: if moreover
`μ_Σ = N(0, C(Σ)) * ν_{h(Σ)}` on `PD(d)` as in `prop:similarity-orbit-family`, that node's clauses
(2) and (3) hold under their remaining hypotheses alone, with or without a Gaussian part. -/
theorem sim_cascade_elliptical (hd : 2 ≤ d) (G : Set (Mat d)) (hG : IsClosedSubgroupGL G)
    (hsim : simSet d ⊆ G) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily G loewnerLE μ) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) (νI : Measure (Rd d))
    (hνI : IsProfileLaw K νI) (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef)
    (hform : ∀ S : Mat d, S.PosDef → μ 0 S = multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S))
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ)) :
    (∀ hbar : Mat d → Mat d, (∀ S : Mat d, S.PosDef → hbar S = h S) →
      ContinuousOn hbar {S | S.PosSemidef ∧ S ≠ 0} →
      (∀ S : Mat d, S.PosSemidef → S ≠ 0 → (hbar S).PosDef) →
      ∃ h0 : ℝ, 0 < h0 ∧ h 1 = h0 • (1 : Mat d) ∧ ∀ S : Mat d, S.PosDef →
        ecc (h S) ≤ dilRatio K.k (Real.sqrt (h0 / lamMax (hbar (sigmaEps d 0)))) ^ 2) ∧
      ((∃ L0 : ℝ, Tendsto K.k (𝓝[>] 0) (𝓝 L0)) →
        ∀ S : Mat d, S.PosDef → ∃ c : ℝ, h S = c • (1 : Mat d)) := by
  have hID : HasIDLoewnerIncrements
      fun S => multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S) := by
    intro S S' hS hS' hle
    obtain ⟨-, -, -, hinc⟩ := sim_cascade_infinitelyDivisible hd G hG hsim μ hμ
    obtain ⟨hid, heq⟩ := hinc S S' hS hS' hle
    refine ⟨μ S S', hμ.isProbability (S, S') ⟨hS.posSemidef, hS'.posSemidef, hle⟩, hid, ?_⟩
    show multivariateGaussian 0 (C S') ∗ affineOrbit νI (h S') =
      (multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S)) ∗ μ S S'
    rw [← hform S hS, ← hform S' hS']
    exact heq
  refine ⟨fun hbar hbar_eq hbar_cont hbar_pd => sim_orbit_bounded_shape hd K hrc νI hνI h C hh hC
    hequiv hbar hbar_eq hbar_cont hbar_pd hID, fun ⟨L0, hk0⟩ =>
    sim_orbit_index_zero hd K hrc νI hνI h C hh hC L0 hk0 hequiv hID⟩

end AffineHemigroup
