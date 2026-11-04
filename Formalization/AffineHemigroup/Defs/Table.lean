/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Spectral

/-!
# The notation of § 5.7, the overview table: the chain of cones and the general linear row

Blueprint: `blueprint/src/parts/05-table.tex`, `thm:wedge-axis` (Q-0281, dispatch 5). These objects
are introduced inside the theorem's statement; they are named here so that the theorem and its split
child `lem:wedge-axis-chain` share one type. Every definition is vocabulary: nothing in this file
claims anything, and the claims the statement makes about them (that the largest value defining
`β(C)` is attained, that `β(C)` is the least `α` with `C ⊆ C_α`) are skeleton statements.

## Readings fixed here

* **The index `α ∈ [0, ∞]`** of the chain `C_α` is an element of `WithTop ℝ`, read at `α ≥ 0`;
  `C_∞ := PSD(d)` (`prop:stable-order-generated`). The order `≼_α` on `PD(d)` is
  `causalLE (stableGenConeTop d α)` and `≼⁺_{C_α}` on `PSD(d)` is
  `causalPlusLE (stableGenConeTop d α)`, both of `AffineHemigroup.Defs.Cones`.
* **`β(C)`, "the largest value of `tr X/λ_min(X) - d` over `X ∈ C ∖ {0}`"**, is the supremum of
  those values (`coneIndex`); that it is attained, hence a largest value, is the theorem's claim in
  case (2)(c), the only case that reads it. Outside that case the value is junk and is never read.
* **`𝔉_α`, the set of laws `μ_I` of `(GL(d), ≼⁺_{C_α})`-cascade families of kernels**, is
  `rowLaws d α`: the measures `μ_{0,I}` of the totalised families.
-/

namespace AffineHemigroup

open MeasureTheory Set

variable {d : ℕ}

/-- **The cone `C_α` for `α ∈ [0, ∞]`** (`thm:wedge-axis`; `prop:stable-order-generated`):
`stableGenCone d α` for finite `α` and `C_∞ := PSD(d)`. -/
def stableGenConeTop (d : ℕ) : WithTop ℝ → Set (Mat d)
  | ⊤ => psdSet d
  | (α : ℝ) => stableGenCone d α

/-- **`β(C)`** (`thm:wedge-axis`(2)(c)): the supremum of `tr X/λ_min(X) - d` over the nonzero
members `X` of `C`. -/
noncomputable def coneIndex (C : Set (Mat d)) : ℝ :=
  sSup ((fun X : Mat d => X.trace / lamMin X - d) '' (C \ {0}))

/-- **`𝔉_α`** (`thm:wedge-axis`(3)): the laws `μ_I = μ_{0,I}` of the
`(GL(d), ≼⁺_{C_α})`-cascade families of kernels. -/
def rowLaws (d : ℕ) (α : WithTop ℝ) : Set (Measure (Rd d)) :=
  {m | ∃ μ : Mat d → Mat d → Measure (Rd d),
    IsGWCascadeFamily (glSet d) (causalPlusLE (stableGenConeTop d α)) μ ∧ μ 0 1 = m}

/-- **`𝔉(C)`** (`prop:wedge-axis-profiles`): the laws `μ_I = μ_{0,I}` of the
`(GL(d), ≼⁺_C)`-cascade families of kernels, for a cone `C`; `𝔉_α` is `coneLaws (C_α)` for finite
`α` (`rowLaws_coe_eq_coneLaws`). -/
def coneLaws (C : Set (Mat d)) : Set (Measure (Rd d)) :=
  {m | ∃ μ : Mat d → Mat d → Measure (Rd d),
    IsGWCascadeFamily (glSet d) (causalPlusLE C) μ ∧ μ 0 1 = m}

end AffineHemigroup
