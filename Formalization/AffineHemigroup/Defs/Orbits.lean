/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Algebra.Polynomial.Eval.Defs
import AffineHemigroup.Defs.RadialProfile
import AffineHemigroup.Defs.GammaGaussLaw

/-!
# Affine orbits: radial profiles, the dilation ratio, and the elliptical stable data

Blueprint: `blueprint/src/parts/05-orbits.tex` — `prop:affine-orbits`, `lem:elliptical-stable`,
`prop:stable-step-cone`, `prop:orbit-step-cone`, `lem:dilation-ratio`; PRICING.md items D18, D19.

These objects are introduced inside the statements of chapter 5's nodes; they are named here so
that the nodes that read them share one type. The laws (`S_α(H)`, the law of a radial profile, the
Matérn law, a law with a rational symbol) are **by specification** (PRICING finding 1): a predicate
on a measure, never a definition by A3. The two laws `prop:affine-orbits`(4) *constructs* — the
law of `√(2V) Z` and the ray increment `ν_λ`, the law of `√(2W) Z` with `W` compound Poisson — are
definitions, because the node builds them by hand (Gamma mixture, compound Poisson sum) and spends
no interface (Q-0281, dispatch 2, which also added the dilation exponents of `lem:dilation-ratio`,
the tempering factors of `prop:tempered-step-cone`, and the Matérn kernel and functionals of
`prop:matern-cross-shape` and `prop:matern-negative-mass`).

**The density `K_Σ` of the Matérn law of index `1`** (`prop:matern-negative-mass`) is the
representative `(det Σ)^{-1/2} G(Σ^{-1/2}x)`, `G` the Laplace transform of the heat kernel: "the
density" is determined only almost everywhere, and the node's `q = ∇·P∇K_{Σ'}` is a pointwise
object, so the representative that is smooth off the origin is named (judgement 8).
-/

namespace AffineHemigroup

open MeasureTheory Set
open ScaleSpace (convPow)
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- **The affine orbit of a law** (`prop:affine-orbits`): `μ_Σ := (Σ^{1/2})_* μ_I`. -/
noncomputable def affineOrbit (μI : Measure (Rd d)) (S : Mat d) : Measure (Rd d) :=
  push (msqrt S) μI

namespace RadialProfile

/-- **The orbit's Lévy density** `n_Σ(x) := (det Σ)^{-1/2} m(|Σ^{-1/2} x|)`
(`prop:orbit-step-cone`(1)). -/
noncomputable def orbitDensity (K : RadialProfile d) (S : Mat d) (x : Rd d) : ℝ :=
  (S.det) ^ (-(1 : ℝ) / 2) * K.m ‖lin (msqrt S)⁻¹ x‖

end RadialProfile

/-- **The dilation ratio** (D18; `prop:orbit-step-cone`, `lem:dilation-ratio`):
`R(λ) := inf {k(r/λ)/k(r) : r > 0, k(r) > 0}` for `λ ≥ 1`. -/
noncomputable def dilRatio (k : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ⨅ r : {r : ℝ // 0 < r ∧ 0 < k r}, k (r.1 / lam) / k r.1

/-- **The constant `c_{d,α} := ∫ (1 - cos y₁) |y|^{-d-α} dy`** (D19; `lem:elliptical-stable`),
`y₁` the first coordinate. That it is finite and positive is the node's first claim. -/
noncomputable def stableConst [NeZero d] (α : ℝ) : ℝ :=
  ∫ y : Rd d, (1 - Real.cos (y 0)) * ‖y‖ ^ (-(d : ℝ) - α)

/-- **The elliptical stable Lévy density** `n_H(x) := c_{d,α}⁻¹ (det H)^{-1/2}
⟨x, H⁻¹x⟩^{-(d+α)/2}` (D19; `eq:stable-levy-density`). -/
noncomputable def stableDensity [NeZero d] (α : ℝ) (H : Mat d) (x : Rd d) : ℝ :=
  (stableConst (d := d) α)⁻¹ * H.det ^ (-(1 : ℝ) / 2) * quad H⁻¹ x ^ (-((d : ℝ) + α) / 2)

/-- **The elliptical stable exponent** `ψ_H(ω) := ⟨ω, Hω⟩^{α/2}` (D19;
`eq:stable-levy-density`). -/
noncomputable def stableExp (α : ℝ) (H : Mat d) (ω : Rd d) : ℝ := quad H ω ^ (α / 2)

/-- **`μ` is `S_α(H)`** (D19, by specification): a probability measure with transform
`e^{-ψ_H}`. That such a measure exists and is unique is `lem:elliptical-stable`(2). -/
def IsEllipticalStable (α : ℝ) (H : Mat d) (μ : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ω : Rd d, charFun μ ω = ((Real.exp (-stableExp α H ω) : ℝ) : ℂ)

/-! ## Laws by specification (PRICING finding 1; Q-0281, dispatch 2) -/

/-- **`μ` is the law of the radial profile `K`** (`prop:orbit-step-cone`(1), by specification): a
probability measure with transform `e^{-ψ_I}`. That such a measure exists is
`prop:orbit-step-cone`(1), which spends A3. -/
def IsProfileLaw (K : RadialProfile d) (μ : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ω : Rd d, charFun μ ω = ((Real.exp (-K.exponent ω) : ℝ) : ℂ)

/-- **`μ` is the Matérn law of index `γ`** (`prop:affine-orbits`(4), by specification): a
probability measure with transform `(1 + |ω|²)^{-γ}`. -/
def IsMaternLaw (γ : ℝ) (μ : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ω : Rd d, charFun μ ω = (((1 + ‖ω‖ ^ 2) ^ (-γ) : ℝ) : ℂ)

/-! ## The constructions of `prop:affine-orbits`(4) -/

/-- **The compound Poisson law with finite Lévy measure `L`** on `ℝ`:
`e^{-L(ℝ)} ∑_{n ≥ 0} L^{*n}/n!` (Sato, Definition 4.1), the law of `X₁ + ⋯ + X_N` with `N`
Poisson of mean `L(ℝ)` and the `Xᵢ` of law `L/L(ℝ)`, all independent. Meaningful for a finite
`L`. -/
noncomputable def compoundPoisson (L : Measure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-(L univ).toReal) / (n.factorial : ℝ)) • convPow L n

/-- **The Lévy measure of the Matérn ray increment** (`prop:affine-orbits`(4)):
`γ (e^{-x/λ²} - e^{-x}) x⁻¹ dx` on `(0,∞)`. -/
noncomputable def maternRayLevy (γ lam : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun x =>
    ENNReal.ofReal (γ * (Real.exp (-x / lam ^ 2) - Real.exp (-x)) / x)

/-- **The Matérn ray increment `ν_λ`** (`prop:affine-orbits`(4)): the law of `√(2W) Z`, with `Z`
standard normal on `ℝ^d` and `W ≥ 0`, independent of `Z`, compound Poisson with Lévy measure
`maternRayLevy γ λ`. -/
noncomputable def maternRayLaw (d : ℕ) (γ lam : ℝ) : Measure (Rd d) :=
  ((compoundPoisson (maternRayLevy γ lam)).prod (ProbabilityTheory.stdGaussian (Rd d))).map
    fun p => Real.sqrt (2 * p.1) • p.2

/-! ## The two exponents of the dilation ratio (`lem:dilation-ratio`) -/

/-- **`β₋(k) := inf_{λ>1} log R(λ)/log λ`** (`lem:dilation-ratio`(3)). That the quotients are
bounded (in `[0,2)`) is the node's claim, not assumed. -/
noncomputable def lowerExp (k : ℝ → ℝ) : ℝ :=
  ⨅ lam : Ioi (1 : ℝ), Real.log (dilRatio k lam) / Real.log lam

/-- **`β(k)`** (`lem:dilation-ratio`(3)), defined as `sup_{λ>1} log R(λ)/log λ`; that it is the
limit `lim_{λ→∞} log R(λ)/log λ` is the node's claim. -/
noncomputable def growthExp (k : ℝ → ℝ) : ℝ :=
  ⨆ lam : Ioi (1 : ℝ), Real.log (dilRatio k lam) / Real.log lam

/-! ## Tempered profiles (`prop:tempered-step-cone`) -/

/-- **A tempering factor** (`prop:tempered-step-cone`): `j : (0,∞) → [0,∞)` nonincreasing with
`j(0+) := lim_{r↓0} j(r)` in `(0,∞)`. -/
def IsTemperingProfile (j : ℝ → ℝ) : Prop :=
  (∀ r ∈ Ioi (0 : ℝ), 0 ≤ j r) ∧ AntitoneOn j (Ioi (0 : ℝ)) ∧
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto j (nhdsWithin 0 (Ioi 0)) (nhds L)

/-! ## The Matérn kernel of index `1` and the would-be increment (`prop:matern-cross-shape`,
`prop:matern-negative-mass`) -/

/-- **`G(y) := ∫₀^∞ e^{-t} h_t(y) dt`**, `h_t(y) = (4πt)^{-d/2} e^{-|y|²/4t}` the heat kernel
(`lem:matern-kernel-hessian`). -/
noncomputable def maternGreen (d : ℕ) (y : Rd d) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    Real.exp (-t) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(‖y‖ ^ 2) / (4 * t)))

/-- **`K_Σ(x) := (det Σ)^{-1/2} G(Σ^{-1/2} x)`**, the density of the Matérn law of index `1` at
`Σ`, the representative that is smooth off the origin (`prop:matern-negative-mass`). -/
noncomputable def maternDensity (S : Mat d) (x : Rd d) : ℝ :=
  S.det ^ (-(1 : ℝ) / 2) * maternGreen d (lin (msqrt S)⁻¹ x)

/-- **`∇·P∇f := ∑_{j,k} P_{jk} ∂_j∂_k f`** (`prop:matern-cross-shape`,
`prop:matern-negative-mass`), the second derivative read in the standard basis. -/
noncomputable def secondOrderOp (P : Mat d) (f : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∑ j, ∑ k, P j k * iteratedFDeriv ℝ 2 f x ![ebasis j, ebasis k]

/-- **`φ̂(ω) := ∫ e^{i⟨ω,x⟩} φ(x) dx`**, the transform with the blueprint's convention
(`lem:stable-tail`, `prop:matern-negative-mass`); Mathlib's `𝓕` has another normalisation. -/
noncomputable def fourierPlus (φ : Rd d → ℂ) (ω : Rd d) : ℂ :=
  ∫ x, Complex.exp (((⟪ω, x⟫ : ℝ) : ℂ) * Complex.I) * φ x

/-- **The would-be increment of the Matérn orbit of index `1`** (`prop:matern-negative-mass`), the
linear functional `ρ(φ) := (2π)^{-d} ∫ φ̂(ω) (1 + ⟨ω,Σω⟩)/(1 + ⟨ω,Σ'ω⟩) dω` on Schwartz
functions. -/
noncomputable def maternIncrement (S S' : Mat d) (φ : Rd d → ℂ) : ℂ :=
  ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
    ∫ ω, fourierPlus φ ω * (((1 + quad S ω) / (1 + quad S' ω) : ℝ) : ℂ)

/-- **`𝓑_d := ½ π^{-d/2} Γ(d/2)`** (`prop:matern-negative-mass`(2)). -/
noncomputable def maternBd (d : ℕ) : ℝ :=
  (1 / 2) * Real.pi ^ (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)

/-- **The angular factor** `d⟨ŷ, P'ŷ⟩ - tr P'`, `P' := Σ'^{-1/2}(Σ' - Σ)Σ'^{-1/2}`
(`prop:matern-negative-mass`(2)). -/
noncomputable def maternAngular (S S' : Mat d) (y : Rd d) : ℝ :=
  (d : ℝ) * quad (relStep S' (S' - S)) y - (relStep S' (S' - S)).trace

/-- **`Θ := ∫_{S^{d-1}} (d⟨ŷ,P'ŷ⟩ - tr P')₋ σ(dŷ)`** (`prop:matern-negative-mass`(3)), `σ` the
surface measure on the unit sphere (Mathlib's `volume.toSphere`). -/
noncomputable def maternTheta (S S' : Mat d) : ℝ :=
  ∫ y : Metric.sphere (0 : Rd d) 1, max (-maternAngular S S' y) 0 ∂(volume.toSphere)

/-- **`κ(s) := (4πs)^{-d/2} e^{-1/4s}`** (`lem:matern-kernel-hessian`(2)). -/
noncomputable def maternKappa (d : ℕ) (s : ℝ) : ℝ :=
  (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (4 * s))

/-- **`𝓐(r) := ∫₀^∞ e^{-r²s} κ(s) (4s²)^{-1} ds`** (`lem:matern-kernel-hessian`(2)). -/
noncomputable def maternA (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * maternKappa d s / (4 * s ^ 2)

/-- **`𝓑(r) := ∫₀^∞ e^{-r²s} κ(s) (2s)^{-1} ds`** (`lem:matern-kernel-hessian`(2)). -/
noncomputable def maternB (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(r ^ 2 * s)) * maternKappa d s / (2 * s)

/-! ## Rational symbols (`prop:rational-symbols`) -/

/-- **The hypotheses on `(P, Q)`** (`prop:rational-symbols`): real polynomials with
`deg P > deg Q` and `P(0) = Q(0)`, neither vanishing on `[0,∞)`. -/
def IsRationalSymbolPair (P Q : Polynomial ℝ) : Prop :=
  Q.natDegree < P.natDegree ∧ P.eval 0 = Q.eval 0 ∧ (∀ u : ℝ, 0 ≤ u → P.eval u ≠ 0) ∧
    ∀ u : ℝ, 0 ≤ u → Q.eval u ≠ 0

/-- **`μ` has the rational symbol `Q/P`** (`prop:rational-symbols`, by specification): a
probability measure with `μ̂(ω) = Q(|ω|²)/P(|ω|²)`. -/
def IsSymbolLaw (P Q : Polynomial ℝ) (μ : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ ω : Rd d, charFun μ ω = ((Q.eval (‖ω‖ ^ 2) / P.eval (‖ω‖ ^ 2) : ℝ) : ℂ)

end AffineHemigroup
