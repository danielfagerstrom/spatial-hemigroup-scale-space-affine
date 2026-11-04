/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix

/-!
# The ambient vocabulary: `ℝ^d`, matrices, their action on `PSD(d)` and on measures

Blueprint: the opening paragraph of `def:gw-cascade-family`
(`blueprint/src/parts/04-classical.tex`), which every node of chapters 3–5 reads; PRICING.md
§ "The shared definitions", items D1–D6.

## Readings fixed here, once

* **`ℝ^d` is `EuclideanSpace ℝ (Fin d)`** (`Rd d`), so that Mathlib's `charFun`, written
  `∫ exp(⟪x, t⟫ i) dμ`, is the blueprint's `μ̂(ω) = ∫ e^{i⟨ω,x⟩} μ(dx)`, convention and sign.
* **Matrices act through `Matrix.toEuclideanCLM`** (`lin A`), the map Mathlib's
  `multivariateGaussian` uses, so that the Gaussian member of the scheme needs no translation.
* **Groups are sets of matrices**, not subgroups of `GL (Fin d) ℝ`. The blueprint's groups —
  `GL(d)`, the similarities, `O(d)`, the invertible diagonal matrices — appear in statements
  through membership `A ∈ G`, the action `A Σ Aᵀ` and the image `A_*μ`, all of which are
  stated on the matrix. A set of matrices keeps those statements free of coercions out of the
  unit group, and the claim that a named set *is* a closed subgroup of `GL(d)` becomes a
  proposition (`IsClosedSubgroupGL`) proved in a node, never an obligation hidden in a
  definition (`prop:similarity-ray-families`(1) proves it for the similarities).
* **Covariance matrices are matrices**, `Σ` is written `S` (`Σ` is Lean syntax), and `PSD(d)`,
  `PD(d)` are the predicates `Matrix.PosSemidef`, `Matrix.PosDef`. Square roots, powers and
  logarithms are Mathlib's continuous functional calculus, whose order instances on matrices are
  scoped to `MatrixOrder`; under that scope `S ≤ S'` *is* the Loewner order.

Every definition here is vocabulary: nothing in this file claims anything.
-/

namespace AffineHemigroup

open MeasureTheory Matrix
open scoped MatrixOrder RealInnerProductSpace

/-- **`ℝ^d`** (D1): Euclidean space of dimension `d`, with its inner product, Lebesgue measure
and Borel σ-algebra. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **Real `d × d` matrices** (D2). -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

variable {d : ℕ}

/-- **The linear map of a matrix** on `ℝ^d` (D2), `x ↦ A x`. -/
noncomputable def lin (A : Mat d) : Rd d →L[ℝ] Rd d := Matrix.toEuclideanCLM (𝕜 := ℝ) A

/-- **The image of a measure**, `A_*μ := μ ∘ A⁻¹` (D2; `def:gw-cascade-family`, first
paragraph). Defined for every matrix; the blueprint uses it for `A ∈ GL(d)`. -/
noncomputable def push (A : Mat d) (μ : Measure (Rd d)) : Measure (Rd d) := μ.map (lin A)

/-- **The action of `GL(d)` on `PSD(d)`**, `A · Σ := A Σ Aᵀ` (D4; `def:gw-cascade-family`). -/
def act (A S : Mat d) : Mat d := A * S * Aᵀ

/-- **The quadratic form** `⟨ω, Σ ω⟩`. -/
noncomputable def quad (S : Mat d) (ω : Rd d) : ℝ := ⟪ω, lin S ω⟫

/-- The `j`-th standard basis vector `e_j` of `ℝ^d`. -/
noncomputable def ebasis (j : Fin d) : Rd d := EuclideanSpace.single j 1

/-! ## The groups (D3) -/

/-- **`GL(d)`**: the invertible real `d × d` matrices. -/
def glSet (d : ℕ) : Set (Mat d) := {A | IsUnit A.det}

/-- **`O(d)`**: the orthogonal matrices, Mathlib's `Matrix.orthogonalGroup` as a set. -/
def orthSet (d : ℕ) : Set (Mat d) := {Q | Q ∈ Matrix.orthogonalGroup (Fin d) ℝ}

/-- **`S(d)`, the similarities**: `{c Q : c > 0, Q ∈ O(d)}` (`prop:isotropic-corner`). -/
def simSet (d : ℕ) : Set (Mat d) :=
  {A | ∃ c : ℝ, 0 < c ∧ ∃ Q ∈ Matrix.orthogonalGroup (Fin d) ℝ, A = c • Q}

/-- **The invertible diagonal matrices** (`lem:parameter-space`(5)'s example). -/
def diagGLSet (d : ℕ) : Set (Mat d) := {A | ∃ v : Fin d → ℝ, (∀ i, v i ≠ 0) ∧ A = diagonal v}

/-- **`D₊(d)`, the diagonal matrices with positive diagonal** (chapter 5's diagonal cells). -/
def diagPosSet (d : ℕ) : Set (Mat d) := {A | ∃ v : Fin d → ℝ, (∀ i, 0 < v i) ∧ A = diagonal v}

/-- **A closed subgroup of `GL(d)`** (D3), stated on a set of matrices.

Reading: "closed in `GL(d)`" is closedness relative to the open set of invertible matrices,
`closure G ∩ GL(d) ⊆ G`. On `GL(d)` the topology of the unit group and the subspace topology
from the matrices agree (inversion is continuous there), so this is the blueprint's closedness. -/
structure IsClosedSubgroupGL (G : Set (Mat d)) : Prop where
  /-- `G ⊆ GL(d)`. -/
  subset_gl : G ⊆ glSet d
  one_mem : (1 : Mat d) ∈ G
  mul_mem : ∀ A ∈ G, ∀ B ∈ G, A * B ∈ G
  inv_mem : ∀ A ∈ G, A⁻¹ ∈ G
  /-- Closed in `GL(d)`. -/
  isClosed : ∀ A ∈ closure G, IsUnit A.det → A ∈ G

/-! ## The two orders that the scheme names (D5) -/

/-- **The Loewner order**, `Σ ≤ Σ'` when `Σ' - Σ ∈ PSD(d)` (`def:gw-cascade-family`,
`def:affine-cascade-family`). Under `open scoped MatrixOrder` this is `S ≤ S'`
(`loewnerLE_iff_le`). -/
def loewnerLE (S S' : Mat d) : Prop := (S' - S).PosSemidef

theorem loewnerLE_iff_le (S S' : Mat d) : loewnerLE S S' ↔ S ≤ S' := Iff.rfl

/-- **The ray order** (`def:gw-cascade-family`): `Σ ≤_W Σ'` when `Σ = 0` or `Σ' = c Σ` for some
`c ≥ 1`. -/
def rayLE (S S' : Mat d) : Prop := S = 0 ∨ ∃ c : ℝ, 1 ≤ c ∧ S' = c • S

/-- `PSD(d)` as a set. -/
def psdSet (d : ℕ) : Set (Mat d) := {S | S.PosSemidef}

/-- `PD(d)` as a set. -/
def pdSet (d : ℕ) : Set (Mat d) := {S | S.PosDef}

/-! ## Functions of a matrix (D6) -/

/-- **`Σ^{1/2}`**, the positive semidefinite square root (continuous functional calculus). -/
noncomputable def msqrt (S : Mat d) : Mat d := CFC.sqrt S

/-- **`M^τ`** for a positive (semi)definite `M` and real `τ` (continuous functional calculus). -/
noncomputable def mrpow (M : Mat d) (τ : ℝ) : Mat d := CFC.rpow M τ

/-- **`log M`** for a positive definite `M` (continuous functional calculus). -/
noncomputable def mlog (M : Mat d) : Mat d := cfc Real.log M

/-- **`e^B`**, the matrix exponential. -/
noncomputable def mexp (B : Mat d) : Mat d := NormedSpace.exp B

/-- **The relative step** `Σ^{-1/2} Σ' Σ^{-1/2}` (`prop:invariant-orders`;
`thm:cascade-infinitely-divisible`(3)(c); `prop:stable-step-cone`'s `M`). -/
noncomputable def relStep (S S' : Mat d) : Mat d := (msqrt S)⁻¹ * S' * (msqrt S)⁻¹

/-- **`sym B := (B + Bᵀ)/2`** (`prop:stable-exponent-cone`). -/
noncomputable def symPart (B : Mat d) : Mat d := (1 / 2 : ℝ) • (B + Bᵀ)

/-- **`λ_min(M)`**, the least eigenvalue of a symmetric `M`, as the infimum of the Rayleigh
quotient over unit vectors. Reading: for a symmetric matrix and `d ≥ 1` the infimum is attained
and is the least eigenvalue (the spectral theorem), which is how every node uses it; the
blueprint writes it `λ_min(M)` too. At `d = 0` the infimum is over the empty set and
the value is the junk `0`, which a statement can read: one that would be false at `d = 0` carries
`d ≥ 1` (`[NeZero d]` or `1 ≤ d`), as `stepSet_stable` does (blind review R1-1: without it the
stable step set `{M : λ_min(M)^{d+α} ≥ det M}` is empty at `d = 0`). -/
noncomputable def lamMin (M : Mat d) : ℝ := ⨅ x : {x : Rd d // ‖x‖ = 1}, ⟪(x : Rd d), lin M x⟫

/-- **`λ_max(M)`**, the largest eigenvalue of a symmetric `M`, as the supremum of the Rayleigh
quotient over unit vectors; the reading of `lamMin`. -/
noncomputable def lamMax (M : Mat d) : ℝ := ⨆ x : {x : Rd d // ‖x‖ = 1}, ⟪(x : Rd d), lin M x⟫

/-- **`ecc(H) := λ_max(H)/λ_min(H)`**, the eccentricity of `H ∈ PD(d)`
(`prop:similarity-general-bounded-shape`, `prop:similarity-stable-order-families`). -/
noncomputable def ecc (H : Mat d) : ℝ := lamMax H / lamMin H

end AffineHemigroup
