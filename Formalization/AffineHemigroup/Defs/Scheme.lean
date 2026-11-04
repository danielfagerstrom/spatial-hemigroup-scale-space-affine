/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic
import AffineHemigroup.Defs.GWFamily

/-!
# `def:gw-cascade-family` and `def:affine-cascade-family`: the `(G, W)` scheme on kernels

Blueprint: `blueprint/src/parts/04-classical.tex`, `def:gw-cascade-family` (2) and
`def:affine-cascade-family`; PRICING.md items D7, D8, D10. The operator form (1) is
`AffineHemigroup.Defs.Operators`.

## The pattern: data, then propositions about it

A **wedge datum** is a pair `(G, W)`: a set of matrices and a relation on matrices. That the pair
*is* a wedge datum is the proposition `IsWedgeDatum G le`, and a `(G, W)`-cascade family of kernels
is a function `μ : Mat d → Mat d → Measure (Rd d)` together with the proposition
`IsGWCascadeFamily G le μ`. Nothing here bundles a proof into data, so that a node may say "let
`(G, W)` be a wedge datum" as a hypothesis and another may *prove* that a named pair is one
(`lem:gw-scheme-claims`, `prop:similarity-ray-families`(1)).

## The family is totalised, as Paper V's is

Paper V indexes its operators by all pairs of reals and constrains them on `0 ≤ s ≤ t`
(`ScaleSpace.PreCascadeCore`). Here the kernels are indexed by all pairs of matrices and
constrained on `P_W = {(Σ, Σ') : Σ, Σ' ∈ PSD(d), Σ ≤_W Σ'}` (`wedgePairs`): every field reads the
family on `P_W` only. So two functions that agree on `P_W` are the same family (`EqOnPairs`), and a
uniqueness clause ("exactly one family") is stated up to `EqOnPairs`. (K2) is `ContinuousOn` on
`P_W` with the subspace topology of `Mat d × Mat d`, which is the blueprint's "the topology of
`PSD(d) × PSD(d)`" (PRICING finding 6).

## What is a hypothesis and what is not

`IsGWCascadeFamily` does not assume `IsWedgeDatum`: the blueprint defines the family for a wedge
datum, and each node that needs the datum's properties says so in its own hypotheses. For the
affine family the datum `(GL(d), Loewner)` is a wedge datum by `lem:gw-scheme-claims`(2).
-/

namespace AffineHemigroup

open MeasureTheory Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-- **The affine Gaussian scale space with constant `b`** (D10; `def:affine-cascade-family`,
`eq:affine-gaussian`): `μ_{Σ,Σ'}` is the centred Gaussian law with covariance matrix
`2b(Σ' - Σ)`, Mathlib's `multivariateGaussian` (which allows a singular covariance, the law then
being carried by its range). Its transform is `lem:affine-gaussian-transform`. -/
noncomputable def affineGaussian (b : ℝ) (S S' : Mat d) : Measure (Rd d) :=
  ProbabilityTheory.multivariateGaussian 0 ((2 * b) • (S' - S))

/-! ## Chains and the path condition (`thm:cascade-infinitely-divisible`(2)) -/

/-- **`le` is a partial order on the set `𝒫`** (`thm:cascade-infinitely-divisible`(2),
(3)(c)): reflexive, antisymmetric and transitive on `𝒫`. -/
structure IsPartialOrderOn (P : Set (Mat d)) (le : Mat d → Mat d → Prop) : Prop where
  refl : ∀ S ∈ P, le S S
  antisymm : ∀ S ∈ P, ∀ S' ∈ P, le S S' → le S' S → S = S'
  trans : ∀ S ∈ P, ∀ S' ∈ P, ∀ S'' ∈ P, le S S' → le S' S'' → le S S''

/-- **A `W`-chain from `Σ` to `Σ'` in `𝒫`** (`thm:cascade-infinitely-divisible`(2)): a
continuous `γ : [0,1] → 𝒫` with `γ(s) ≤_W γ(t)` for `s ≤ t`, `γ(0) = Σ`, `γ(1) = Σ'`. The curve
is a function on `ℝ` read on `[0,1]`. -/
structure IsWChain (P : Set (Mat d)) (le : Mat d → Mat d → Prop) (γ : ℝ → Mat d)
    (S S' : Mat d) : Prop where
  continuousOn : ContinuousOn γ (Set.Icc 0 1)
  mem : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ P
  mono : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, s ≤ t → le (γ s) (γ t)
  start : γ 0 = S
  finish : γ 1 = S'

/-- **The path condition (P)** (`thm:cascade-infinitely-divisible`(2)): every pair
`Σ ≤_W Σ'` in `PSD(d)` is joined by a `W`-chain in `PSD(d)`. -/
def HasPathCondition (le : Mat d → Mat d → Prop) : Prop :=
  ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' → ∃ γ, IsWChain (psdSet d) le γ S S'

end AffineHemigroup
