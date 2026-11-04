/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Cones
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Convex.Basic
import AffineHemigroup.Defs.Eigenvalues

/-!
# Ordered spectra, majorization, eigenvalue cones, and scale--shape coordinates

Blueprint: `blueprint/src/parts/05-landscape.tex` (`lem:loewner-scale-shape`,
`prop:glplus-families`), `05-wedges.tex` (`lem:spectral-cones`, `thm:cone-orders`,
`prop:stable-order-generated`). These objects are introduced inside the statements of chapter 5's
nodes; they are named here so that the nodes that read them share one type (Q-0281, dispatch 2).
Every definition is vocabulary: nothing in this file claims anything.

## Readings fixed here

* **The ordered spectrum** `λ↑(X)` (`lem:spectral-cones`) is `eigUp X`: the roots of the
  characteristic polynomial, with multiplicity, sorted increasingly, read at the indices
  `0, …, d-1`. For a symmetric `X` the characteristic polynomial splits over `ℝ` with exactly `d`
  roots (Mathlib's `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`), so `eigUp X` is the list of
  eigenvalues in increasing order. For a matrix that is not symmetric the value is junk and is never
  read, with one exception: for a product `MN` of two positive definite matrices the characteristic
  polynomial is that of the symmetric `M^{1/2}NM^{1/2}` (`charpoly_mul_comm`), so `eigUp (M * N)`
  lists the eigenvalues of `MN` with multiplicity, which is how ledger A9
  (`gelfand_naimark_logMajorized`, wave 2, group F) reads it. `λ↑₁(X) = λ_min(X)` and
  `λ↑_d(X) = λ_max(X)` (the Rayleigh forms `lamMin`, `lamMax` of `AffineHemigroup.Defs.Basic`) is
  a skeleton lemma, `AffineHemigroup.eigUp_spec`.
* **Vectors of `ℝ^d` in eigenvalue space** are functions `Fin d → ℝ` with the pairing
  `∑ᵢ wᵢ xᵢ`; on a finite-dimensional space every norm gives the same closed sets, so closedness of
  a cone `D ⊆ ℝ^d` is the blueprint's.
* **A closed convex cone** contains `0` (`IsClosedConvexCone`): the blueprint's cones are nonempty
  (`thm:cone-orders`(1) calls `≼_C` a preorder, which the empty cone would not give).
* **Index `k` of a partial sum** is a natural number: `s_k(x) = x↑₁ + ⋯ + x↑_k` is
  `partialSumUp k x`, the sum of the `k` smallest entries, `s_0 = 0`.
-/

namespace AffineHemigroup

open Matrix Set
open scoped MatrixOrder

variable {d : ℕ}

/-! ## The ordered spectrum and rearrangements (`lem:spectral-cones`) -/

/-- **`ℓ(M) := λ↑(log M)`** for `M ∈ PD(d)` (`lem:spectral-cones`). -/
noncomputable def logSpec (M : Mat d) : Fin d → ℝ := eigUp (mlog M)

/-- **`x↑`, the increasing rearrangement** of `x ∈ ℝ^d` (`lem:spectral-cones`). -/
noncomputable def sortUp (x : Fin d → ℝ) : Fin d → ℝ := x ∘ Tuple.sort x

/-- **`x↓`, the decreasing rearrangement** of `x ∈ ℝ^d` (`lem:spectral-cones`). -/
noncomputable def sortDown (x : Fin d → ℝ) : Fin d → ℝ := sortUp x ∘ Fin.rev

/-- **`s_k(x) := x↑₁ + ⋯ + x↑_k`**, the sum of the `k` smallest entries (`lem:spectral-cones`). -/
noncomputable def partialSumUp (k : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), sortUp x i

/-- **Majorization `x ≺ y`** (`lem:spectral-cones`): `s_k(x) ≥ s_k(y)` for `1 ≤ k < d` and
`s_d(x) = s_d(y)`. -/
def IsMajorized (x y : Fin d → ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < d → partialSumUp k y ≤ partialSumUp k x) ∧
    partialSumUp d x = partialSumUp d y

/-- **A symmetric set** of `ℝ^d` (`lem:spectral-cones`): invariant under permutations of the
coordinates. -/
def IsPermSymmetric (D : Set (Fin d → ℝ)) : Prop :=
  ∀ σ : Equiv.Perm (Fin d), ∀ x ∈ D, x ∘ σ ∈ D

/-- **`D^# := {w : ⟨w, x⟩ ≥ 0 for every x ∈ D}`** (`lem:spectral-cones`). -/
def dualCone (D : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {w | ∀ x ∈ D, 0 ≤ ∑ i, w i * x i}

/-! ## Cones -/

/-- **A closed convex cone** in a real topological vector space: closed, convex, containing `0`,
and closed under multiplication by every `c ≥ 0`. -/
def IsClosedConvexCone {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (C : Set V) : Prop :=
  IsClosed C ∧ Convex ℝ C ∧ (0 : V) ∈ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ x ∈ C, c • x ∈ C

/-- **`Sym(d)`**, the real symmetric `d × d` matrices (`prop:invariant-orders`). -/
def symSet (d : ℕ) : Set (Mat d) := {X | X.IsSymm}

/-- **Invariance under orthogonal conjugation** `X ↦ Q X Qᵀ`, `Q ∈ O(d)`. -/
def IsOrthInvariant (C : Set (Mat d)) : Prop :=
  ∀ Q ∈ orthSet d, ∀ X ∈ C, Q * X * Qᵀ ∈ C

/-- **`C_D := {X ∈ Sym(d) : λ↑(X) ∈ D}`** (`lem:spectral-cones`(4)). -/
noncomputable def specCone (D : Set (Fin d → ℝ)) : Set (Mat d) :=
  {X | X.IsSymm ∧ eigUp X ∈ D}

/-- **The cone `C_α`** (`prop:stable-order-generated`), for `0 ≤ α < ∞`:
`{X ∈ Sym(d) : X ≥ 0, (d+α) λ_min(X) ≥ tr X}`; `C_∞ := PSD(d)` is `psdSet d`. -/
def stableGenCone (d : ℕ) (α : ℝ) : Set (Mat d) :=
  {X | X.PosSemidef ∧ X.trace ≤ ((d : ℝ) + α) * lamMin X}

/-- **The causal-curve geodesic** `γ(t) := Σ^{1/2} M^t Σ^{1/2}` with `M` the relative step of
`(Σ, Σ')` (`thm:cone-orders`(1), `prop:stable-order-generated`(1)). -/
noncomputable def stepGeodesic (S S' : Mat d) (t : ℝ) : Mat d :=
  msqrt S * mrpow (relStep S S') t * msqrt S

/-! ## The stable orders in Loewner coordinates (`prop:stable-order-generated`(3)) -/

/-- **`Φ_α(Σ) := (det Σ)^{-1/(d+α)} Σ`** on `PD(d)` (`prop:stable-order-generated`(3)). -/
noncomputable def phiAlpha (d : ℕ) (α : ℝ) (S : Mat d) : Mat d :=
  (S.det ^ (-(1 : ℝ) / ((d : ℝ) + α))) • S

/-- **`ψ_α(A) := |det A|^{-1/(d+α)} A`** on `GL(d)` (`prop:stable-order-generated`(3)). -/
noncomputable def psiAlpha (d : ℕ) (α : ℝ) (A : Mat d) : Mat d :=
  (|A.det| ^ (-(1 : ℝ) / ((d : ℝ) + α))) • A

/-! ## Scale and shape (`lem:loewner-scale-shape`) -/

/-- **The volume scale** `t(Σ) := (det Σ)^{1/2d}` of `Σ ∈ PD(d)`. -/
noncomputable def volScale (S : Mat d) : ℝ := S.det ^ ((1 : ℝ) / (2 * d))

/-- **The shape** `S(Σ) := t(Σ)^{-2} Σ` of `Σ ∈ PD(d)`. -/
noncomputable def shapeOf (S : Mat d) : Mat d := (volScale S ^ 2)⁻¹ • S

/-! ## The orientation-preserving group (`prop:glplus-families`) -/

/-- **`GL⁺(d) := {A ∈ GL(d) : det A > 0}`** (`prop:glplus-families`). -/
def glPlusSet (d : ℕ) : Set (Mat d) := {A | 0 < A.det}

end AffineHemigroup
