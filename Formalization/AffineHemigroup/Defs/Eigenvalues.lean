/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The eigenvalues of a matrix in increasing order

`eigUp X`: the roots of the characteristic polynomial, with multiplicity, sorted increasingly.
It stood in `AffineHemigroup.Defs.Spectral`, which imports this file; it is here unchanged, so
that the cited fact A9 (`AffineHemigroup.Interfaces`, `gelfand_naimark_logMajorized`), which is
stated in it, can be read without the eigenvalue cones (Q-0452).
-/

namespace AffineHemigroup

section

open Matrix Set
open scoped MatrixOrder

variable {d : ℕ}

/-- **`λ↑(X)`, the eigenvalues in increasing order** (`lem:spectral-cones`): the roots of the
characteristic polynomial, with multiplicity, sorted increasingly; meaningful for symmetric `X`,
and for a product of two positive definite matrices (ledger A9). -/
noncomputable def eigUp (X : Mat d) : Fin d → ℝ :=
  fun k => ((X.charpoly.roots).sort (· ≤ ·)).getD k 0

end

end AffineHemigroup
