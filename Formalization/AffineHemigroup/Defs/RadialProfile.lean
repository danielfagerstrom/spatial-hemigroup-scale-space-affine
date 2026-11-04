/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic

/-!
# Radial profiles

A radial profile in dimension `d` (PRICING.md item D18; `prop:orbit-step-cone`,
`blueprint/src/parts/05-orbits.tex`): `k : (0,∞) → [0,∞)` nonincreasing and not identically
`0`, with `m(r) = k(r) r^{-d}` a Lévy density; its radial density `m` and its exponent. They
stood in `AffineHemigroup.Defs.Orbits`, which imports this file; they are here unchanged, so
that the formal example at the Matérn law (`AffineHemigroup.Witnesses`, `maternOriginDatum`)
can read them without the affine orbits (Q-0452).
-/

namespace AffineHemigroup

section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- **A radial profile in dimension `d`** (D18; `prop:orbit-step-cone`): `k : (0,∞) → [0,∞)`
nonincreasing and not identically `0`, with `m(r) := k(r) r^{-d}` satisfying
`∫ (|x|² ∧ 1) m(|x|) dx < ∞`. -/
structure RadialProfile (d : ℕ) where
  /-- The profile `k`, read on `(0,∞)`. -/
  k : ℝ → ℝ
  k_nonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  k_ne_zero : ∃ r ∈ Ioi (0 : ℝ), k r ≠ 0
  integrable : ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (k ‖x‖ / ‖x‖ ^ d)) ≠ ⊤

namespace RadialProfile

/-- **The radial Lévy density** `m(r) := k(r) r^{-d}` (`prop:orbit-step-cone`). -/
noncomputable def m (K : RadialProfile d) (r : ℝ) : ℝ := K.k r / r ^ d

/-- **The exponent of the law of `K`**, `ψ_I(ω) = ∫ (1 - cos⟨ω, x⟩) m(|x|) dx`
(`prop:orbit-step-cone`(1)), `ℝ≥0∞`-valued. -/
noncomputable def exponentL (K : RadialProfile d) (ω : Rd d) : ℝ≥0∞ :=
  ∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.m ‖x‖)

/-- The real-valued exponent `ψ_I`. -/
noncomputable def exponent (K : RadialProfile d) (ω : Rd d) : ℝ := (K.exponentL ω).toReal

end RadialProfile

end

end AffineHemigroup
