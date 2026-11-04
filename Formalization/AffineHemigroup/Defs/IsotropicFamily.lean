/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility
import ScaleSpaceCore.SDProfile
import ScaleSpaceCore.CausalCone

/-!
# `def:isotropic-kernel-family`: isotropic cascade families, gauges, and the classes `𝒜_d`, `𝒮`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `def:isotropic-kernel-family` and the first
sentences of `def:filtration-thresholds`; PRICING.md items D11, D12, D14.

## Mirroring Paper V, through the shared library

* (I4)'s "increasing bijections `S_λ` of `[0,∞)`" are `IsIncreasingBijection`, the three fields
  `S_mapsTo`, `S_strictMonoOn`, `S_surjOn` of the shared library's `ScaleSpace.IsScaleCovariant`
  (Paper V's structure, moved to `ScaleSpaceCore` at `v0.3.0` and read from there since Q-0365),
  so the marginal family of `lem:isotropic-marginal-family` meets V's structure field for field.
* A **gauge** is the conjunction the shared library's `ScaleSpace.main_analysis` and
  `ScaleSpace.canonical_gauge` output,
  `χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0)` (SECOND-DEMAND.md § 7). For a
  function on `[0,∞)` it says the same as "an increasing bijection of `[0,∞)`": a strictly
  increasing map with `χ 0 = 0` maps `[0,∞)` into itself, and an increasing bijection of
  `[0,∞)` fixes its least point.
* The admissible exponents on the line are `ScaleSpace.SDProfile`, `[V, (2.3)]`; the
  subordinated slice is read through the trunk's `ScaleSpace.CausalAdmissible`, `[B, Def. 4.1]`.

## A reading: `F` is a function on `[0,∞)`

`eq:admissible-line` defines `F(r)` for `r ≥ 0`, and `𝒜_d` reads `F` only at `|ξ| ≥ 0`. So
membership asks that `F` agree with an admissible exponent **on `[0,∞)`**, not on all of `ℝ` as
`ScaleSpace.IsAdmissibleExponent` does: a function that differs from an admissible one only on
the negative half-line is in `𝒜_d` here.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set
open scoped MatrixOrder

variable {d : ℕ}

/-- **An increasing bijection of `[0,∞)`** (I4), with Paper V's three fields. -/
structure IsIncreasingBijection (f : ℝ → ℝ) : Prop where
  mapsTo : MapsTo f (Ici 0) (Ici 0)
  strictMonoOn : StrictMonoOn f (Ici 0)
  surjOn : SurjOn f (Ici 0) (Ici 0)

/-- **A gauge** (D12; `def:isotropic-kernel-family`): an increasing bijection `χ` of `[0,∞)`,
written as the conjunction Paper V's theorems output. -/
def IsGauge (χ : ℝ → ℝ) : Prop :=
  χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0)

/-- **`def:isotropic-kernel-family`, the gauge**: Paper V's conjunction `IsGauge` and (I4)'s
`IsIncreasingBijection` say the same of a function on `[0,∞)`, "an increasing bijection of
`[0,∞)`". A strictly increasing map with `χ 0 = 0` maps `[0,∞)` into itself; an increasing
bijection of `[0,∞)` takes the value `0` somewhere on `[0,∞)`, and only at `0`, since `χ 0 ≥ 0`.
Not a clause of the node: it identifies the two Lean spellings (wave 1, blind review W1E-5). -/
theorem isGauge_iff_isIncreasingBijection (χ : ℝ → ℝ) :
    IsGauge χ ↔ IsIncreasingBijection χ := by
  constructor
  · rintro ⟨h0, hm, hs⟩
    refine ⟨fun x hx => ?_, hm, hs⟩
    have h := hm.monotoneOn (self_mem_Ici : (0 : ℝ) ∈ Ici 0) hx (mem_Ici.1 hx)
    rw [h0] at h
    exact h
  · rintro ⟨hmap, hm, hs⟩
    refine ⟨?_, hm, hs⟩
    obtain ⟨y, hy, hy0⟩ := hs (self_mem_Ici : (0 : ℝ) ∈ Ici 0)
    rcases eq_or_lt_of_le (mem_Ici.1 hy) with h | h
    · rw [← h] at hy0
      exact hy0
    · have h1 := hm (self_mem_Ici : (0 : ℝ) ∈ Ici 0) hy h
      have h2 : (0 : ℝ) ≤ χ 0 := hmap (self_mem_Ici : (0 : ℝ) ∈ Ici 0)
      rw [hy0] at h1
      linarith

/-- A gauge is nonnegative on `[0,∞)`. -/
theorem IsGauge.nonneg {χ : ℝ → ℝ} (hχ : IsGauge χ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ χ t := by
  have := hχ.2.1.monotoneOn (self_mem_Ici : (0 : ℝ) ∈ Ici 0) ht ht
  rw [hχ.1] at this; exact this

/-- **An isotropic cascade family in dimension `d`, with dilation action `S`** (D11;
`def:isotropic-kernel-family`, (I1)–(I4) and (ND)). Indexed by all pairs of reals and read on
`0 ≤ s ≤ t`, as Paper V's families are. The blueprint's "isotropic cascade family" is
`∃ S, IsIsotropicCascadeFamily μ S`: (I4) asserts that some action exists. -/
structure IsIsotropicCascadeFamily (μ : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ) : Prop where
  /-- Each `μ s t`, `0 ≤ s ≤ t`, is a probability measure. -/
  isProbability : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)
  /-- **(I1)**, the diagonal: `μ t t = δ₀`. -/
  diag : ∀ t : ℝ, 0 ≤ t → μ t t = Measure.dirac 0
  /-- **(I1)**, the cascade: `μ r t = μ s t ∗ μ r s` whenever `r ≤ s ≤ t`. -/
  cascade : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → μ r t = μ s t ∗ μ r s
  /-- **(I2)**: for every `ξ`, `(s, t) ↦ μ̂_{s,t}(ξ)` is continuous on `{0 ≤ s ≤ t}`. -/
  continuous : ∀ ξ : Rd d,
    ContinuousOn (fun p : ℝ × ℝ => charFun (μ p.1 p.2) ξ) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  /-- **(I3)**: `Q_* μ_{s,t} = μ_{s,t}` for every `Q ∈ O(d)`. -/
  rotation : ∀ Q ∈ orthSet d, ∀ s t : ℝ, 0 ≤ s → s ≤ t → push Q (μ s t) = μ s t
  /-- **(I4)**, the action: each `S λ`, `λ > 0`, is an increasing bijection of `[0,∞)`. -/
  scale_bij : ∀ lam : ℝ, 0 < lam → IsIncreasingBijection (S lam)
  /-- **(I4)**, the covariance: `(λI)_* μ_{s,t} = μ_{S_λ s, S_λ t}`. -/
  scale : ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    push (lam • (1 : Mat d)) (μ s t) = μ (S lam s) (S lam t)
  /-- **(ND)**: `μ_{s,t} ≠ δ₀` whenever `s < t`. -/
  nondegenerate : ∀ s t : ℝ, 0 ≤ s → s < t → μ s t ≠ Measure.dirac 0

/-- **The marginal** `π_*μ` of a measure on `ℝ^d` along a vector `e`, `π(x) = ⟨e, x⟩`
(`lem:radial-marginal`, `lem:isotropic-marginal-family`; dispatch 3). -/
noncomputable def marginal (e : Rd d) (μ : Measure (Rd d)) : Measure ℝ :=
  μ.map fun x => inner ℝ e x

/-- **The class `𝒜_d`** (D14; `def:isotropic-kernel-family`, `def:filtration-thresholds`): the
admissible `F` (`eq:admissible-line`, Paper V's `SDProfile` read on `[0,∞)`) for which there is a
self-decomposable probability measure `μ` on `ℝ^d` with `μ̂(ξ) = e^{-F(|ξ|)}`. -/
def classA (d : ℕ) (F : ℝ → ℝ) : Prop :=
  (∃ P : ScaleSpace.SDProfile, ∀ r : ℝ, 0 ≤ r → F r = P.exponent r) ∧
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
      ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)

/-- **The class `𝒜_∞`** (`def:filtration-thresholds`): the intersection of all the `𝒜_d`,
`d ≥ 1`. -/
def classAInf (F : ℝ → ℝ) : Prop := ∀ d : ℕ, 1 ≤ d → classA d F

/-- **The subordinated slice `𝒮`** (D14; `def:filtration-thresholds`, `[B, Prop. 4.9]`): the
`F` with `F(ω) = F_I(ω²/2)` on `[0,∞)` for a causally admissible `F_I` (`[B, Def. 4.1]`, the
trunk's `ScaleSpace.CausalAdmissible`). -/
def classS (F : ℝ → ℝ) : Prop :=
  ∃ FI : ScaleSpace.CausalAdmissible, ∀ r : ℝ, 0 ≤ r → F r = FI.exponent (r ^ 2 / 2)

end AffineHemigroup
