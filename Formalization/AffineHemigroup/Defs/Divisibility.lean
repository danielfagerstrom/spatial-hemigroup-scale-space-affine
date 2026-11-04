/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic
import ScaleSpaceCore.SelfDecomposable
import ScaleSpaceCore.ConvPow

/-!
# Infinite divisibility, self-decomposability, Lévy triplets, and the stabilizer of a law

Blueprint: `eq:self-decomposable` in `def:isotropic-kernel-family`
(`blueprint/src/parts/03-isotropic.tex`); `prop:stable-exponent-cone`'s `B`-self-decomposability
(`05-orbits.tex`); `lem:parameter-space`'s fullness, stabilizer and orbit (`04-classical.tex`); the
vocabulary of ledger entries A3–A6 (`blueprint/AXIOMS.md`, transcribed in
`blueprint/AXIOMS-verbatim.md`). PRICING.md items D13 and D22, and finding 5.

Mathlib has none of these notions; this module makes them, except self-decomposability.
**Infinite divisibility** is Sato's Definition 7.1 at the letter. **Self-decomposability** is the
shared library's `ScaleSpace.IsSelfDecomposable` (`ScaleSpaceCore.SelfDecomposable`, SSL-3 of
SECOND-DEMAND.md, at `v0.3.0`; Q-0365 switched this development onto it): the measure form
`μ = (c •)_* μ ∗ ρ_c`, `c ∈ (0,1)`. For a finite measure on a finite-dimensional inner product
space it is the blueprint's `eq:self-decomposable`, `μ̂(ξ) = μ̂(cξ) ρ̂_c(ξ)`, by
`ScaleSpace.isSelfDecomposable_iff_charFun`; every law this development calls self-decomposable
is a probability measure on `ℝ^d` or `ℝ`. Sato's Definition 15.1 (`b > 1`,
`μ̂(z) = μ̂(b⁻¹z) ρ̂_b(z)`) is `IsSelfDecomposableSato`, the form ledger entries A2 and A4 are
stated in; the two are the same class with `c = b⁻¹` (`isSelfDecomposable_iff_sato`).
**Operator self-decomposability** `IsBSelfDecomposable B` is the shared library's
`ScaleSpace.IsBSelfDecomposable` at the linear map `lin B` of the matrix, and
`isBSelfDecomposable_iff` gives it back in the matrix form `μ = (e^{-tB})_* μ ∗ ρ_t`.
-/

namespace AffineHemigroup

open MeasureTheory Matrix Complex
open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun convPow)
open scoped MatrixOrder RealInnerProductSpace

section General

variable {E : Type*} [MeasurableSpace E]

/-! The `n`-fold convolution power `ν^{n*}` (with `ν^{0*} = δ₀`) is the shared library's
`ScaleSpace.convPow` (`ScaleSpaceCore.ConvPow`, v0.4.0, moved there from this file by Q-0361, the
definition unchanged), opened above. -/

/-- **The convolution of a finite list of measures**, `μ₁ ∗ ⋯ ∗ μ_r`, with the empty
convolution `δ₀`. -/
noncomputable def convList [AddMonoid E] : List (Measure E) → Measure E
  | [] => Measure.dirac 0
  | μ :: l => μ ∗ convList l

/-- **Infinite divisibility** (D13; PRICING finding 5; Sato Definition 7.1, p. 31): for every
positive integer `n` there is a probability measure `ν` with `μ = ν^{n*}`. -/
def IsInfinitelyDivisible [AddMonoid E] (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E, IsProbabilityMeasure ν ∧ convPow ν n = μ

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Self-decomposability at Sato's letter** (Definition 15.1, p. 90, transcribed in
`blueprint/AXIOMS-verbatim.md` § A4): for any `b > 1` there is a probability measure `ρ_b` with
`μ̂(z) = μ̂(b⁻¹ z) ρ̂_b(z)`. The form in which the interfaces A2 and A4 are stated. -/
def IsSelfDecomposableSato (μ : Measure E) : Prop :=
  ∀ b : ℝ, 1 < b → ∃ ρ : Measure E, IsProbabilityMeasure ρ ∧
    ∀ z : E, charFun μ z = charFun μ (b⁻¹ • z) * charFun ρ z

/-- The blueprint's self-decomposability and Sato's are the same class (`c = b⁻¹`), for a finite
measure on a finite-dimensional space, where the shared library's measure form is the transform
form (`ScaleSpace.isSelfDecomposable_iff_charFun`). -/
theorem isSelfDecomposable_iff_sato [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] : IsSelfDecomposable μ ↔ IsSelfDecomposableSato μ := by
  rw [isSelfDecomposable_iff_charFun]
  constructor
  · intro h b hb
    have hb0 : 0 < b := lt_trans one_pos hb
    exact h b⁻¹ (inv_pos.mpr hb0) (inv_lt_one_of_one_lt₀ hb)
  · intro h c hc0 hc1
    obtain ⟨ρ, hρ, hfac⟩ := h c⁻¹ (one_lt_inv₀ hc0 |>.mpr hc1)
    exact ⟨ρ, hρ, fun ξ => by simpa [inv_inv] using hfac ξ⟩

end General

variable {d : ℕ}

/-- **Operator self-decomposability** (D13; `prop:stable-exponent-cone`): `μ` is
*`B`-self-decomposable* if for every `t > 0` there is a probability measure `ρ_t` with
`μ = (e^{-tB})_* μ ∗ ρ_t`. Jurek–Mason's `exp(-tQ)`-decomposability (3.4.1), p. 89, with `Q = B`;
ledger A5 is stated with `t ≥ 0`, which adds only `t = 0`, where `ρ_0 = δ₀`.

The shared library's `ScaleSpace.IsBSelfDecomposable` at the linear map `lin B` of the matrix
(Q-0365); `isBSelfDecomposable_iff` is the matrix form above. -/
def IsBSelfDecomposable (B : Mat d) (μ : Measure (Rd d)) : Prop :=
  ScaleSpace.IsBSelfDecomposable (lin B) μ

/-- The linear map of a matrix exponential is the exponential of the linear map:
`lin (e^B) = e^{lin B}`, `lin` being a continuous algebra homomorphism. -/
theorem lin_mexp (B : Mat d) : lin (mexp B) = NormedSpace.exp (lin B) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).toRingEquiv.toRingHom
    (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).toAlgEquiv.toLinearMap) B

/-- **Operator self-decomposability in the matrix form**: for every `t > 0` there is a
probability measure `ρ_t` with `μ = (e^{-tB})_* μ ∗ ρ_t`. -/
theorem isBSelfDecomposable_iff (B : Mat d) (μ : Measure (Rd d)) :
    IsBSelfDecomposable B μ ↔ ∀ t : ℝ, 0 < t → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      μ = push (mexp (-t • B)) μ ∗ ρ := by
  have h : ∀ t : ℝ, push (mexp (-t • B)) μ
      = μ.map ⇑(NormedSpace.exp (-t • lin B) : Rd d →L[ℝ] Rd d) := by
    intro t
    rw [push, lin_mexp, show lin (-t • B) = -t • lin B from
      map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (-t) B]
  simp only [IsBSelfDecomposable, ScaleSpace.IsBSelfDecomposable, h]

/-- **`e^{-tB} → 0` as `t → ∞`** (`prop:anisotropy-budget`, `prop:one-parameter-families`; the
hypothesis of ledger A5; PRICING finding 6). The reading of `prop:one-parameter-families`(2)'s
"every eigenvalue of `B` has positive real part, that is `e^{tB} → 0` as `t → -∞`" is this
proposition (substitute `t ↦ -t`), the hypothesis ledger A5 states; the equivalence with the
eigenvalue condition, which the clause asserts with "that is", is the skeleton statement
`isExpContracting_iff` (through Gelfand's formula; blind review R4-2). The limit is in the topology
of `Mat d`, entrywise. -/
def IsExpContracting (B : Mat d) : Prop :=
  Filter.Tendsto (fun t : ℝ => mexp (-t • B)) Filter.atTop (nhds 0)

/-! ## Lévy triplets (D22; the vocabulary of ledger A3) -/

/-- **A generating triplet on `ℝ^d`** (D22; Sato Theorem 8.1 and Definition 8.2, pp. 37–38): a
symmetric nonnegative-definite `A`, a measure `ν` with (8.2) `ν{0} = 0` and
`∫ (|x|² ∧ 1) ν(dx) < ∞`, and `γ ∈ ℝ^d`. -/
structure LevyTriplet (d : ℕ) where
  /-- The Gaussian covariance matrix. -/
  A : Mat d
  /-- The Lévy measure. -/
  ν : Measure (Rd d)
  /-- The drift. -/
  γ : Rd d
  A_posSemidef : A.PosSemidef
  ν_zero : ν {0} = 0
  ν_integrable : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤

namespace LevyTriplet

/-- **The Lévy–Khintchine exponent** (8.1), the expression whose exponential is `μ̂(z)`:
`-½⟨z, Az⟩ + i⟨γ, z⟩ + ∫ (e^{i⟨z,x⟩} - 1 - i⟨z,x⟩ 1_D(x)) ν(dx)`, `D` the closed unit ball.
The integrand is `ν`-integrable by (8.2); the Bochner integral is used as written. -/
noncomputable def lkExponent (T : LevyTriplet d) (z : Rd d) : ℂ :=
  -((quad T.A z / 2 : ℝ) : ℂ) + I * ((⟪T.γ, z⟫ : ℝ) : ℂ)
    + ∫ x, (exp (((⟪z, x⟫ : ℝ) : ℂ) * I) - 1
        - I * ((⟪z, x⟫ : ℝ) : ℂ) * (Metric.closedBall (0 : Rd d) 1).indicator 1 x) ∂T.ν

end LevyTriplet

/-- **`μ` has generating triplet `T`**: `μ̂(z) = exp(lkExponent T z)` for every `z` (8.1). -/
def HasTriplet (μ : Measure (Rd d)) (T : LevyTriplet d) : Prop :=
  ∀ z : Rd d, charFun μ z = exp (T.lkExponent z)

/-! ## The parameter-space vocabulary (`lem:parameter-space`) -/

/-- **A full law** (`lem:parameter-space`): `μ(V) < 1` for every linear subspace `V ≠ ℝ^d`. -/
def IsFull (μ : Measure (Rd d)) : Prop :=
  ∀ V : Submodule ℝ (Rd d), V ≠ ⊤ → μ (V : Set (Rd d)) < 1

/-- **`Stab(μ)`** (`lem:parameter-space`): the `A ∈ GL(d)` with `A_*μ = μ`. -/
def stab (μ : Measure (Rd d)) : Set (Mat d) := {A | A ∈ glSet d ∧ push A μ = μ}

/-- **`Orb(μ)`** (`lem:parameter-space`): the images `A_*μ`, `A ∈ GL(d)`. -/
def orb (μ : Measure (Rd d)) : Set (Measure (Rd d)) := {ν | ∃ A ∈ glSet d, ν = push A μ}

/-- **Rotation invariance** of a measure: `Q_*μ = μ` for every `Q ∈ O(d)`. -/
def IsRotationInvariant (μ : Measure (Rd d)) : Prop := ∀ Q ∈ orthSet d, push Q μ = μ

end AffineHemigroup
