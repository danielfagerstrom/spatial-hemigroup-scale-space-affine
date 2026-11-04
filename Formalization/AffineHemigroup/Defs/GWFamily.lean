/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic

/-!
# Wedge data and the `(G, W)`-cascade families of kernels

Blueprint: `def:gw-cascade-family`(2) and `def:affine-cascade-family`
(`blueprint/src/parts/04-classical.tex`); PRICING.md items D7, D8, D10.

The definitions in which the correspondence between operators and kernels is stated
(`AffineHemigroup.OperatorFamilies`, `AffineHemigroup.KernelsOperators`): `IsWedgeDatum`,
`wedgePairs`, `EqOnPairs`, `IsGWCascadeFamily` and `IsAffineCascadeFamily`. They stood in
`AffineHemigroup.Defs.Scheme`, which imports this file and whose header says how they are to be
read (data, then propositions about it; a family is totalised and read on `P_W` only). They are
here unchanged, so that a file can read them without the rest of the scheme (Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-- **A wedge datum in dimension `d`** (D7; `def:gw-cascade-family`): a closed subgroup `G` of
`GL(d)` containing the dilations `λ I`, `λ > 0`, and a partial order `≤_W` on `PSD(d)` that is
`G`-invariant and contains the rays. The relation `le` is read on `PSD(d)` only. -/
structure IsWedgeDatum (G : Set (Mat d)) (le : Mat d → Mat d → Prop) : Prop where
  /-- `G` is a closed subgroup of `GL(d)`. -/
  closedSubgroup : IsClosedSubgroupGL G
  /-- `G` contains the dilations `λ I`, `λ > 0`. -/
  dilations : ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ G
  /-- `≤_W` is reflexive on `PSD(d)`. -/
  refl : ∀ S : Mat d, S.PosSemidef → le S S
  /-- `≤_W` is antisymmetric on `PSD(d)`. -/
  antisymm : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → le S' S → S = S'
  /-- `≤_W` is transitive on `PSD(d)`. -/
  trans : ∀ S S' S'' : Mat d, S.PosSemidef → S'.PosSemidef → S''.PosSemidef →
    le S S' → le S' S'' → le S S''
  /-- `≤_W` is `G`-invariant: `Σ ≤_W Σ'` implies `A · Σ ≤_W A · Σ'` for `A ∈ G`. -/
  invariant : ∀ A ∈ G, ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef →
    le S S' → le (act A S) (act A S')
  /-- `≤_W` contains the rays: `c Σ ≤_W c' Σ` for `Σ ∈ PSD(d)` and `0 ≤ c ≤ c'`. -/
  rays : ∀ S : Mat d, S.PosSemidef → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → le (c • S) (c' • S)

/-- **`P_W`**: the pairs `(Σ, Σ')` of `PSD(d)` with `Σ ≤_W Σ'` (`def:gw-cascade-family`). -/
def wedgePairs (le : Mat d → Mat d → Prop) : Set (Mat d × Mat d) :=
  {p | p.1.PosSemidef ∧ p.2.PosSemidef ∧ le p.1 p.2}

/-- Two kernel families are **the same family** when they agree on `P_W`: the totalised
families read nothing else. -/
def EqOnPairs (le : Mat d → Mat d → Prop) (μ ν : Mat d → Mat d → Measure (Rd d)) : Prop :=
  ∀ p ∈ wedgePairs le, μ p.1 p.2 = ν p.1 p.2

/-- **A `(G, W)`-cascade family of kernels** (D8; `def:gw-cascade-family`(2)): probability
measures `μ Σ Σ'` on `ℝ^d`, `(Σ, Σ') ∈ P_W`, with (K1)–(K4). The kernel from the origin is
`μ 0 Σ`. -/
structure IsGWCascadeFamily (G : Set (Mat d)) (le : Mat d → Mat d → Prop)
    (μ : Mat d → Mat d → Measure (Rd d)) : Prop where
  /-- Each `μ Σ Σ'`, `(Σ, Σ') ∈ P_W`, is a probability measure. -/
  isProbability : ∀ p ∈ wedgePairs le, IsProbabilityMeasure (μ p.1 p.2)
  /-- **(K1)**, the diagonal: `μ Σ Σ = δ₀`. -/
  diag : ∀ S : Mat d, S.PosSemidef → μ S S = Measure.dirac 0
  /-- **(K1)**, the cascade: `μ Σ Σ'' = μ Σ' Σ'' ∗ μ Σ Σ'` whenever `Σ ≤_W Σ' ≤_W Σ''`. -/
  cascade : ∀ S S' S'' : Mat d, S.PosSemidef → S'.PosSemidef → S''.PosSemidef →
    le S S' → le S' S'' → μ S S'' = μ S' S'' ∗ μ S S'
  /-- **(K2)**: for every `ω`, `(Σ, Σ') ↦ μ̂_{Σ,Σ'}(ω)` is continuous on `P_W`. -/
  continuous : ∀ ω : Rd d,
    ContinuousOn (fun p : Mat d × Mat d => charFun (μ p.1 p.2) ω) (wedgePairs le)
  /-- **(K3)**: `A_* μ_{Σ,Σ'} = μ_{A·Σ, A·Σ'}` for `A ∈ G` and `(Σ, Σ') ∈ P_W`. -/
  covariant : ∀ A ∈ G, ∀ p ∈ wedgePairs le, push A (μ p.1 p.2) = μ (act A p.1) (act A p.2)
  /-- **(K4)**: `μ_{0,I} ≠ δ₀`. -/
  nondegenerate : μ 0 1 ≠ Measure.dirac 0

/-- **An affine cascade family in dimension `d`** (D10; `def:affine-cascade-family`): a
`(GL(d), Loewner)`-cascade family of kernels. Unfolding `IsGWCascadeFamily` gives the node's
(K1)–(K4) verbatim, the pairs being the Loewner pairs of `PSD(d)`. -/
def IsAffineCascadeFamily (μ : Mat d → Mat d → Measure (Rd d)) : Prop :=
  IsGWCascadeFamily (glSet d) loewnerLE μ

end

end AffineHemigroup
