/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Scheme
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import AffineHemigroup.Defs.LevyExponent

/-!
# Step sets, cone fields, the stable orders, and the anisotropy functionals

Blueprint: `blueprint/src/parts/05-wedges.tex` (`prop:invariant-orders`, `thm:cone-orders`),
`05-orbits.tex` (`prop:stable-step-cone`, `prop:stable-exponent-cone`) and
`05-smaller-groups.tex` (`prop:similarity-general-bounded-shape`,
`prop:similarity-stable-order-families`); PRICING.md items D20, D21.

## A reading: absolutely continuous curves in `PD(d)` (PRICING finding 6)

`thm:cone-orders` asks for an absolutely continuous `γ : [0,1] → PD(d)` and a condition on
`γ(t)^{-1/2} γ'(t) γ(t)^{-1/2}` for almost every `t`. Mathlib has absolute continuity for
functions into a metric space and none for matrices, which carry no global norm instance. The
reading fixed here is **entrywise**: every entry `t ↦ γ(t)ᵢⱼ` is absolutely continuous on
`[0,1]`, and `γ'(t)` is the matrix of the entries' derivatives. On a finite-dimensional space every
norm gives the same absolutely continuous curves and the same a.e. derivative, so this is the
blueprint's notion.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix
open scoped ENNReal MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Step sets and the relations they define (`prop:invariant-orders`) -/

/-- **A step set** (D20; `prop:invariant-orders`): `𝒦 ⊆ PD(d)` with `Q M Qᵀ ∈ 𝒦` whenever
`M ∈ 𝒦` and `Q ∈ O(d)`. -/
def IsStepSet (K : Set (Mat d)) : Prop :=
  K ⊆ pdSet d ∧ ∀ M ∈ K, ∀ Q ∈ orthSet d, Q * M * Qᵀ ∈ K

/-- **`Σ ≤_𝒦 Σ'`** (D20; `prop:invariant-orders`): `Σ, Σ' ∈ PD(d)` and the relative step
`Σ^{-1/2} Σ' Σ^{-1/2}` lies in `𝒦`. -/
def stepLE (K : Set (Mat d)) (S S' : Mat d) : Prop :=
  S.PosDef ∧ S'.PosDef ∧ relStep S S' ∈ K

/-- **`𝒮_𝒦 := {A ∈ GL(d) : A Aᵀ ∈ 𝒦}`** (`prop:invariant-orders`). -/
def stepSemigroup (K : Set (Mat d)) : Set (Mat d) := {A | A ∈ glSet d ∧ A * Aᵀ ∈ K}

/-- **The infinitesimal cone** `C(𝒦) := {X ∈ Sym(d) : e^{tX} ∈ 𝒦 for every t ≥ 0}`
(`prop:invariant-orders`(4)). -/
def infCone (K : Set (Mat d)) : Set (Mat d) :=
  {X | X.IsSymm ∧ ∀ t : ℝ, 0 ≤ t → mexp (t • X) ∈ K}

/-- **`exp C := {e^X : X ∈ C}`** (`lem:spectral-cones`(5), `thm:cone-orders`). -/
def expSet (C : Set (Mat d)) : Set (Mat d) := {M | ∃ X ∈ C, M = mexp X}

/-- **The entrywise derivative** of a matrix-valued curve (the reading of the module docstring). -/
noncomputable def mderiv (γ : ℝ → Mat d) (t : ℝ) : Mat d :=
  Matrix.of fun i j => deriv (fun s => γ s i j) t

/-- **A `C`-causal curve** (D20; `thm:cone-orders`): an absolutely continuous
`γ : [0,1] → PD(d)` (entrywise) with `γ(t)^{-1/2} γ'(t) γ(t)^{-1/2} ∈ C` for almost every
`t ∈ [0,1]`. -/
structure IsCausalCurve (C : Set (Mat d)) (γ : ℝ → Mat d) : Prop where
  mem_pd : ∀ t ∈ Icc (0 : ℝ) 1, (γ t).PosDef
  absolutelyContinuous : ∀ i j, AbsolutelyContinuousOnInterval (fun t => γ t i j) 0 1
  causal : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), relStep (γ t) (mderiv γ t) ∈ C

/-- **`Σ ≼_C Σ'`** (D20; `thm:cone-orders`): a `C`-causal curve runs from `Σ` to `Σ'`. -/
def causalLE (C : Set (Mat d)) (S S' : Mat d) : Prop :=
  ∃ γ : ℝ → Mat d, IsCausalCurve C γ ∧ γ 0 = S ∧ γ 1 = S'

/-- **`Σ ≼⁺_C Σ'` on `PSD(d)`** (`thm:cone-orders`(4)): `Σ = 0`, or `Σ' = cΣ` with `c ≥ 1`, or
`Σ, Σ' ∈ PD(d)` with `Σ ≼_C Σ'`. -/
def causalPlusLE (C : Set (Mat d)) (S S' : Mat d) : Prop :=
  S = 0 ∨ (∃ c : ℝ, 1 ≤ c ∧ S' = c • S) ∨ (S.PosDef ∧ S'.PosDef ∧ causalLE C S S')

/-! ## The stable orders (`prop:stable-step-cone`, `prop:stable-exponent-cone`,
`prop:similarity-stable-order-families`) -/

/-- **The stable step set** `𝒦_α := {M ∈ PD(d) : λ_min(M)^{d+α} ≥ det M}`
(`thm:cascade-infinitely-divisible`(3)(c), `prop:stable-step-cone`(1)(c)). -/
def stableStepSet (d : ℕ) (α : ℝ) : Set (Mat d) :=
  {M | M.PosDef ∧ M.det ≤ lamMin M ^ ((d : ℝ) + α)}

/-- **`Σ ≼_α Σ'`** on `PD(d)` (`prop:stable-step-cone`(2)): condition (c),
`λ_min(M)^{d+α} ≥ det M` for the relative step `M`. -/
def stableLE (α : ℝ) (S S' : Mat d) : Prop := stepLE (stableStepSet d α) S S'

/-- **`Σ ≤_α Σ'` on `PSD(d)`** (`prop:similarity-stable-order-families`(1)): `Σ = 0`, or
`Σ' = cΣ` with `c ≥ 1`, or `Σ, Σ' ∈ PD(d)` with `Σ ≼_α Σ'`. -/
def stablePlusLE (α : ℝ) (S S' : Mat d) : Prop :=
  S = 0 ∨ (∃ c : ℝ, 1 ≤ c ∧ S' = c • S) ∨ (S.PosDef ∧ S'.PosDef ∧ stableLE α S S')

/-- **The cone `{X ∈ Sym(d) : (d+α) λ_min(X) ≥ tr X}`** whose exponentials are `𝒦_α`
(`thm:cascade-infinitely-divisible`(3)(c)). -/
def stableSymCone (d : ℕ) (α : ℝ) : Set (Mat d) :=
  {X | X.IsSymm ∧ X.trace ≤ ((d : ℝ) + α) * lamMin X}

/-- **The exponent cone `𝔨_α`** (`prop:stable-exponent-cone`, `eq:stable-exponent-cone`): the real
`B` with `(d+α) λ_min(sym B) ≥ tr B`. -/
def stableExpCone (d : ℕ) (α : ℝ) : Set (Mat d) :=
  {B | B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B)}

/-! ## The anisotropy functionals (D21; `prop:similarity-general-bounded-shape`) -/

/-- **The rotational spread** `rs(L) := inf {K ≥ 1 : R_*L ≤ K L for every R ∈ O(d)}`, the
infimum of the empty set being `∞`. -/
noncomputable def rotSpread (L : Measure (Rd d)) : ℝ≥0∞ :=
  ⨅ K : {K : ℝ≥0∞ // 1 ≤ K ∧ ∀ R ∈ orthSet d, push R L ≤ K • L}, K.1

/-- **The exponent spread** `es(ψ) := inf {K ≥ 1 : ψ(Rω) ≤ K ψ(ω) for every R ∈ O(d), ω}`, the
infimum of the empty set being `∞`. -/
noncomputable def expSpread (ψ : Rd d → ℝ) : ℝ≥0∞ :=
  ⨅ K : {K : ℝ // 1 ≤ K ∧ ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) ≤ K * ψ ω},
    ENNReal.ofReal K.1

/-- **The moment matrix at scale `s`** `𝓜_s(L) := ∫ (|x|² ∧ s²) x xᵀ/|x|² L(dx)`, entrywise. -/
noncomputable def momentMatrix (s : ℝ) (L : Measure (Rd d)) : Mat d :=
  Matrix.of fun i j => ∫ x, min (‖x‖ ^ 2) (s ^ 2) * (x i * x j) / ‖x‖ ^ 2 ∂L

/-- **`T_s(L) := ∫ (|x|² ∧ s²) L(dx)`**, the trace of the moment matrix. -/
noncomputable def momentTrace (s : ℝ) (L : Measure (Rd d)) : ℝ :=
  ∫ x, min (‖x‖ ^ 2) (s ^ 2) ∂L

/-- **`cond M := λ_max(M)/λ_min(M) ∈ [1,∞]`** for `M ∈ PSD(d) ∖ {0}`, `∞` when `λ_min(M) = 0`. -/
noncomputable def condNum (M : Mat d) : ℝ≥0∞ :=
  if lamMin M = 0 then ⊤ else ENNReal.ofReal (lamMax M / lamMin M)

end AffineHemigroup
