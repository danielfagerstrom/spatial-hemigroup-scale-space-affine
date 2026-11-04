/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.Defs.GWFamily

/-!
# `lem:gw-scheme-claims`(1) and (2): `(0, I) ∈ P_W`, and the Loewner order as a wedge datum

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:gw-scheme-claims`. The claims that the
correspondence between operators and kernels reads (`AffineHemigroup.OperatorFamilies`,
`AffineHemigroup.KernelsOperators`): `0 ≤_W Σ` and `(0, I) ∈ P_W` for every wedge datum, the
Loewner order as a wedge datum for every closed subgroup of `GL(d)` containing the dilations,
and `GL(d)` as such a subgroup. Lean core only.

The four declarations stood in `AffineHemigroup.Scheme`, which imports this file and keeps the
ray order and the affine Gaussian law; they are here unchanged (Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- **`lem:gw-scheme-claims`(1)**: since `W` contains the rays, `0 ≤_W Σ` for every
`Σ ∈ PSD(d)`. -/
theorem wedge_zero_le {G : Set (Mat d)} {le : Mat d → Mat d → Prop} (hW : IsWedgeDatum G le)
    {S : Mat d} (hS : S.PosSemidef) : le 0 S := by
  simpa using hW.rays S hS 0 1 le_rfl zero_le_one

/-- **`lem:gw-scheme-claims`(1)**, in particular: `(0, I) ∈ P_W`. -/
theorem wedge_zero_one_mem {G : Set (Mat d)} {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum G le) : ((0 : Mat d), (1 : Mat d)) ∈ wedgePairs le :=
  ⟨PosSemidef.zero, PosSemidef.one, wedge_zero_le hW PosSemidef.one⟩

/-- **`lem:gw-scheme-claims`(2)**, the Loewner order: for every closed subgroup `G` of `GL(d)`
containing the dilations, `(G, Loewner)` is a wedge datum. -/
theorem isWedgeDatum_loewner {G : Set (Mat d)} (hG : IsClosedSubgroupGL G)
    (hdil : ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G) : IsWedgeDatum G loewnerLE where
  closedSubgroup := hG
  dilations := hdil
  refl S _ := by simp [loewnerLE, PosSemidef.zero]
  antisymm S S' _ _ h1 h2 := le_antisymm ((loewnerLE_iff_le _ _).1 h1) ((loewnerLE_iff_le _ _).1 h2)
  trans S S' S'' _ _ _ h1 h2 :=
    (loewnerLE_iff_le _ _).2 (le_trans ((loewnerLE_iff_le _ _).1 h1) ((loewnerLE_iff_le _ _).1 h2))
  invariant A _ S S' _ _ h := loewnerLE_act A h
  rays S hS c c' _ hcc' := by
    unfold loewnerLE
    rw [← sub_smul]
    exact hS.smul (sub_nonneg.2 hcc')

/-- **`lem:gw-scheme-claims`(2)**, the group: `GL(d)` is a closed subgroup of itself containing
the dilations. -/
theorem glSet_isClosedSubgroupGL :
    IsClosedSubgroupGL (glSet d) ∧ ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ glSet d := by
  refine ⟨⟨fun _ h => h, ?_, ?_, ?_, fun _ _ h => h⟩, ?_⟩
  · change IsUnit (1 : Mat d).det
    simp
  · intro A hA B hB
    change IsUnit (A * B).det
    rw [det_mul]
    exact hA.mul hB
  · intro A hA
    exact Matrix.isUnit_nonsing_inv_det A hA
  · intro c hc
    change IsUnit (c • (1 : Mat d)).det
    rw [det_smul, det_one, mul_one]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero _ hc.ne')

end

end AffineHemigroup
