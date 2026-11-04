/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.GLPlus
import AffineHemigroup.KernelsOperators

/-!
# `lem:glplus-operator-families`: the operator families under `GL⁺(d)`

Blueprint: `blueprint/src/parts/05-landscape.tex`, the operator half of `prop:glplus-families`(2),
split off (ADR-0025). Q-0281, wave M, phase 2.

The proof of record: each operator is convolution by a kernel (`lem:operators-to-kernels`(1)), the
kernels form a `(GL⁺(d), W)`-family (`lem:operators-to-kernels-families`(4)), hence a
`(GL(d), W)`-family (`gw_family_glPlus_iff`), and the transport of `lem:operators-to-kernels`(2)
turns their covariance into the operators' (here through `lem:kernels-to-operators`(2), which
assembles exactly that). The converse is the inclusion of the groups.
-/

namespace AffineHemigroup

open MeasureTheory

variable {d : ℕ}

/-- **`lem:glplus-operator-families`**: for `d ≥ 2` and a wedge datum `(GL⁺(d), W)`, a family of
operators indexed by `P_W` is a `(GL⁺(d), W)`-cascade family of operators if and only if it is a
`(GL(d), W)`-cascade family of operators. -/
theorem gw_operator_family_glPlus_iff (hd : 2 ≤ d) {le : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum (glPlusSet d) le) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)) :
    IsGWOperatorFamily (glPlusSet d) le Φ ↔ IsGWOperatorFamily (glSet d) le Φ := by
  have hd1 : 1 ≤ d := by omega
  have hWgl : IsWedgeDatum (glSet d) le := (isWedgeDatum_glPlus_iff hd1 le).mp hW
  constructor
  · intro hΦ
    obtain ⟨μ, hμ⟩ := (kernels_operators_correspondence hd1 hW).2.1 Φ hΦ
    have hk := operators_to_kernels_gw hd1 hW Φ hΦ μ hμ
    exact (kernels_to_operators_gw hd1 hWgl μ ((gw_family_glPlus_iff hd hW μ).mp hk) Φ hμ).1
  · intro hΦ
    exact ⟨hΦ.single, hΦ.diag, hΦ.cascade, hΦ.continuous, hΦ.nondegenerate,
      fun A hA => hΦ.covariant A (glPlusSet_subset_glSet hA)⟩

end AffineHemigroup
