/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility
import AffineHemigroup.Defs.Kanter
import AffineHemigroup.Defs.Eigenvalues
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The cited interfaces of this module, as Lean axioms (ledger A1–A6, A8–A11)

**This file widens the project's trust base, and it is the only file that does.** Every `axiom`
here is admitted on a page-anchored entry of `blueprint/AXIOMS.md`, whose source wording is
transcribed from the page image in `blueprint/AXIOMS-verbatim.md`, and is named in
`blueprint/trust-boundary.txt`; `linkage axioms --check` refuses a name no ledger entry backs.

**Spent so far** (Q-0281, wave 2): A1 by `origin_dichotomy` (`thm:origin-boundedness-d`(5));
A2–A4 by the polar reading and classification (`polar_reading`, `polar_reading_unique`,
`polar_reading_admissible`, `classA_iff_originDatum`, `polar_classification`), by
`filtration_witness` and `filtration_strict` (`thm:filtration-strict`) and by
`no_cin_ray_in_the_plane`, the last two also calling A3(ii)–(iii) directly; A3(iii) also by
`origin_lower_bound` and its two clauses (`prop:origin-lower-bound-d`, wave 2, group B); A8 by
`radial_monotone_family` and `radial_monotone_law` (`prop:isotropic-radial-monotone`, wave 2,
group B); A6 by `cascade_interval_infinitelyDivisible` and the three clauses reduced to it
(`thm:cascade-infinitely-divisible`, wave 2, group C); A5 by `anisotropy_levy`, its one caller,
and through it by `anisotropy_budget` (`prop:anisotropy-budget`(1), wave 2, group G) and by
`wedge_axis_non_gaussian`, `wedge_axis_row` and `wedge_axis_row_members` (`thm:wedge-axis`(2)(c)
and (3), wave 2, group H), as the guard prints them. `CIAxiomGuard.lean` lists every spender,
`polar_classification` and `radial_monotone_family` included: both also print A3(ii)–(iii) through
`isotropic_classification` (Paper V's interface until Q-0365). `line_levy_unique`, the discharge of
the shared library's `SymLevyUnique`, `isotropic_classification` and its operator form
`isotropic_classification_operators` (`cor:isotropic-classification-operators`) are therefore
spenders of A3 too. A9, admitted on 2026-10-05 (wave 2, group F), is spent by
`logSpec_product_majorized` (`lem:spectral-cones-products`) and through it by the nodes of § 5.3
that read the spectrum of a product. A10, admitted on 2026-10-07 (wave N), is spent twice by
`classS_of_classAInf` (`lem:filtration-top`, the inclusion `𝒜_∞ ⊆ 𝒮`) and through it by
`filtration_top`, which `thm:filtration-strict` names. A11, admitted on 2026-10-11 (Q-0416), is
spent by `tendsto_ball_of_gauss` and through it by the declarations of `prop:origin-rate-d`
(`origin_ball_rate`, `origin_ball_rate_critical` and those that read them), once in each clause.

## How each is stated

At its page's letter, and no wider than the ledger's "Statement as used":

* the vocabulary is this module's: `IsInfinitelyDivisible` is Sato's Definition 7.1,
  `IsSelfDecomposableSato` his Definition 15.1 (`b > 1`), `LevyTriplet` and `HasTriplet` his
  Theorem 8.1(i) with (8.1)–(8.2), all in `AffineHemigroup.Defs.Divisibility`;
* Sato's characteristic function `μ̂(z) = ∫ e^{i⟨z,x⟩} μ(dx)` is Mathlib's `charFun`, with the
  same sign;
* a narrowing is taken where the page leaves a degenerate case open (A6: the rows are nonempty),
  or where the page states more than the use needs (A9: the partial sums of a majorization, whose
  totals are proved), and is said beside the axiom;
* a composite entry states only the directions its use reads (A10: the necessity direction of
  Schoenberg's radial theorem followed by the forward direction of the representation of a
  Bernstein function, with the class of Bernstein functions never named);
* an equivalence is admitted in the one direction its use reads, for the objects and the
  parameter range of the use (A11: the Tauberian direction of Karamata's theorem at the origin,
  for a finite measure on `[0,∞)` and positive constant and index).

The ten entries and their names (A7 is unused):

| entry | source | Lean |
|---|---|---|
| A1 | Sato Prop. 28.1, p. 190 | `density_of_integrable_charFun` |
| A2 | Sato Thm. 15.10, p. 95 | `sato_polar_criterion` |
| A3 | Sato Thm. 8.1, pp. 37–38 | `levy_khintchine_exists`, `_unique`, `_converse` |
| A4 | Sato Prop. 15.5, p. 93 | `selfDecomposable_infinitelyDivisible` |
| A5 | Jurek–Mason Thm. 3.3.5, § 3.4 | `operatorSelfDecomposable_infinitelyDivisible` |
| A6 | Sato Thm. 9.3, p. 47 | `khintchine_null_array` |
| A8 | Wolfe Thm. 2, p. 144; Kanter Defs. 1.2, 3.1 | `wolfe_symmetric_unimodal` |
| A9 | Bhatia MA Cor. III.4.6, (III.21), p. 73 | `gelfand_naimark_logMajorized` |
| A10 | SSV Thm. 13.14, p. 212; Def. 3.1, Thm. 3.2, p. 21 | `schoenberg_radial_bernstein` |
| A11 | Bingham–Goldie–Teugels Thm. 1.7.1′, p. 38 | `karamata_tauberian_zero` |
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ}

/-! ## A1 — Sato, Proposition 28.1, p. 190 -/

/-- **Ledger A1** (@sato1999levy Prop. 28.1, p. 190): *"If a probability measure `μ` on `ℝ^d`
satisfies (28.1) `∫_{ℝ^d} |μ̂(z)| |z|^n dz < ∞` for some `n ∈ ℤ₊`, then `μ` has a density `g(x)`
of class `C^n` and the partial derivatives of `g(x)` of orders `0, …, n` tend to `0` as
`|x| → ∞`."*

Reading: "the partial derivatives of order `k` tend to `0`" is stated as the `k`-th Fréchet
derivative tending to `0` along the cocompact filter; on `ℝ^d` the norm of the `k`-th derivative
and the largest `k`-th partial derivative bound each other, so the two say the same. The density is
a real function `g ≥ 0` with `μ = g · Lebesgue`: a density of a probability measure is nonnegative
by definition, and Sato's `g` is one. **Restated at the page's letter** on 2026-10-05 (the author's
decision, no new source): until then the conclusion did not say `0 ≤ g`, so that the measure
named was `g⁺ · Lebesgue` and the `C^n` function need not have been the density itself (blind review
R2-1). Spent by `thm:origin-boundedness-d`(2) and (5). -/
axiom density_of_integrable_charFun (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (n : ℕ)
    (h : ∫⁻ z, ENNReal.ofReal (‖charFun μ z‖ * ‖z‖ ^ n) ≠ ⊤) :
    ∃ g : Rd d → ℝ, (∀ x, 0 ≤ g x) ∧ ContDiff ℝ n g ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∀ k : ℕ, k ≤ n → Tendsto (fun x => iteratedFDeriv ℝ k g x) (cocompact (Rd d)) (𝓝 0)

/-! ## A2 — Sato, Theorem 15.10, p. 95 -/

/-- **Ledger A2** (@sato1999levy Thm. 15.10, p. 95): *"Let `μ` be an infinitely divisible
distribution on `ℝ^d` with generating triplet `(A, ν, γ)`. Then, `μ` is selfdecomposable if and
only if (15.8) `ν(B) = ∫_S λ(dξ) ∫_0^∞ 1_B(rξ) k_ξ(r) dr/r` with a finite measure `λ` on `S` and a
nonnegative function `k_ξ(r)` measurable in `ξ ∈ S` and decreasing in `r > 0`."*

`S` is the unit sphere, here the subtype `Metric.sphere 0 1`; "decreasing" is Sato's weak sense
(p. xi), `AntitoneOn` on `(0,∞)`; "measurable in `ξ`" is measurability of `ξ ↦ k_ξ(r)` for each
`r > 0`; (15.8) is asserted for every Borel `B`. Self-decomposability is Sato's Definition 15.1
(`IsSelfDecomposableSato`). Spent by `prop:isotropic-polar-reading` (both directions, in
`AffineHemigroup.PolarReading`) and, through it, by `prop:isotropic-polar-classification`,
`thm:filtration-strict` and `thm:no-cin-ray-in-the-plane`. (Not by `thm:origin-boundedness-d`
since Q-0286.) -/
axiom sato_polar_criterion (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet d) (hT : HasTriplet μ T) :
    IsSelfDecomposableSato μ ↔
      ∃ (lam : Measure (Metric.sphere (0 : Rd d) 1)) (k : Metric.sphere (0 : Rd d) 1 → ℝ → ℝ),
        IsFiniteMeasure lam ∧ (∀ ξ, ∀ r : ℝ, 0 < r → 0 ≤ k ξ r) ∧
        (∀ r : ℝ, 0 < r → Measurable fun ξ => k ξ r) ∧ (∀ ξ, AntitoneOn (k ξ) (Ioi 0)) ∧
        ∀ B : Set (Rd d), MeasurableSet B →
          T.ν B = ∫⁻ ξ, (∫⁻ r in Ioi (0 : ℝ),
            B.indicator 1 (r • (ξ : Rd d)) * ENNReal.ofReal (k ξ r / r)) ∂lam

/-! ## A3 — Sato, Theorem 8.1, pp. 37–38 -/

/-- **Ledger A3, clause (i)** (@sato1999levy Thm. 8.1(i), p. 37): *"If `μ` is an infinitely
divisible distribution on `ℝ^d`, then (8.1) `μ̂(z) = exp[-½⟨z, Az⟩ + i⟨γ, z⟩ + ∫_{ℝ^d}
(e^{i⟨z,x⟩} - 1 - i⟨z,x⟩ 1_D(x)) ν(dx)]`, `z ∈ ℝ^d`, where `A` is a symmetric
nonnegative-definite `d × d` matrix, `ν` is a measure on `ℝ^d` satisfying (8.2) `ν({0}) = 0` and
`∫_{ℝ^d} (|x|² ∧ 1) ν(dx) < ∞`, and `γ ∈ ℝ^d`."* `D` is the closed unit ball (p. 37). -/
axiom levy_khintchine_exists (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) : ∃ T : LevyTriplet d, HasTriplet μ T

/-- **Ledger A3, clause (ii)** (@sato1999levy Thm. 8.1(ii), p. 38): *"The representation of
`μ̂(z)` in (i) by `A`, `ν`, and `γ` is unique."* -/
axiom levy_khintchine_unique (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T T' : LevyTriplet d) (hT : HasTriplet μ T)
    (hT' : HasTriplet μ T') : T.A = T'.A ∧ T.ν = T'.ν ∧ T.γ = T'.γ

/-- **Ledger A3, clause (iii)** (@sato1999levy Thm. 8.1(iii), p. 38): *"Conversely, if `A` is a
symmetric nonnegative-definite `d × d` matrix, `ν` is a measure satisfying (8.2), and
`γ ∈ ℝ^d`, then there exists an infinitely divisible distribution `μ` whose characteristic
function is given by (8.1)."* -/
axiom levy_khintchine_converse (T : LevyTriplet d) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧ HasTriplet μ T

/-! ## A4 — Sato, Proposition 15.5, p. 93 -/

/-- **Ledger A4** (@sato1999levy Prop. 15.5, p. 93, first clause only): *"If `μ` is
selfdecomposable, then `μ` is infinitely divisible"*, with Definition 15.1, p. 90, for
"selfdecomposable" (`IsSelfDecomposableSato`). The rest of the sentence — the uniqueness and the
infinite divisibility of `ρ_b` — is not admitted (the ledger's "does NOT carry"). -/
axiom selfDecomposable_infinitelyDivisible (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposableSato μ) : IsInfinitelyDivisible μ

/-! ## A5 — Jurek–Mason, Theorem 3.3.5, p. 83, and § 3.4, pp. 89–90 -/

/-- **Ledger A5** (@jurek1993operator Thm. 3.3.5, p. 83, its last sentence; the opening of
§ 3.4, pp. 89–90; @urbanik1972levy Prop. 5.2, p. 134): *"For `Q` with `exp(-tQ) → 0` as
`t → ∞`, we say that a measure `μ` is `exp(-tQ)`-decomposable if for each `t ≥ 0`, there is a
measure `ν_t` such that (3.4.1) `μ = exp(-tQ)μ * ν_t`. From the last part of Theorem 3.3.5, each
`ν_t` is infinitely divisible. The assumption on `Q` implies `ν_t ⇒ μ` as `t → ∞`, so `μ` is also
infinitely divisible."*

Their `Q` is the ledger's `B`, with the same sign; their measures are probability measures (p. 53).
"Each `ν_t`" is read as every probability measure `ρ` satisfying (3.4.1) at some `t ≥ 0`: given the
hypothesis at every `t`, replacing one `ν_t` by such a `ρ` leaves a family the page's sentence
applies to. -/
axiom operatorSelfDecomposable_infinitelyDivisible (B : Mat d)
    (hB : Tendsto (fun t : ℝ => mexp (-t • B)) atTop (𝓝 0))
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : ∀ t : ℝ, 0 ≤ t → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      μ = push (mexp (-t • B)) μ ∗ ρ) :
    (∀ t : ℝ, 0 ≤ t → ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
      μ = push (mexp (-t • B)) μ ∗ ρ → IsInfinitelyDivisible ρ) ∧ IsInfinitelyDivisible μ

/-! ## A6 — Sato, Theorem 9.3, p. 47 -/

/-- **Ledger A6** (@sato1999levy Thm. 9.3, p. 47, with Definition 9.2 and (9.1), the same page;
Definition 2.2, p. 7; p. 8 for the law of a sum), in the measure form of the ledger: *"Let
`{Z_{nk}}` be a null array on `ℝ^d` with row sums `S_n`. If, for some `b_n ∈ ℝ^d`,
`n = 1, 2, …`, the distribution of `S_n - b_n` converges to a distribution `μ`, then `μ` is
infinitely divisible."*

The rows are the laws `μ n k`, `k < r n`; (9.1) is `max_k μ_{n,k}{|x| > ε} → 0`; the law of
`S_n - b_n` is `μ_{n,1} ∗ ⋯ ∗ μ_{n,r_n} ∗ δ_{-b_n}` (p. 8); "converges" is Definition 2.2, against
every bounded continuous function. **Narrowing**: the rows are nonempty, `r_n ≥ 1`, which the page's
indexing `k = 1, …, r_n` presupposes. -/
axiom khintchine_null_array (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (μ : (n : ℕ) → Fin (r n) → Measure (Rd d)) (hprob : ∀ n k, IsProbabilityMeasure (μ n k))
    (hnull : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ⨆ k, μ n k {x | ε < ‖x‖}) atTop (𝓝 0))
    (b : ℕ → Rd d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (hconv : ∀ f : Rd d →ᵇ ℝ, Tendsto
      (fun n => ∫ x, f x ∂(convList (List.ofFn (μ n)) ∗ Measure.dirac (-b n))) atTop
      (𝓝 (∫ x, f x ∂ν))) :
    IsInfinitelyDivisible ν

/-! ## A8 — Wolfe, Theorem 2, p. 144, read with Kanter's definition -/

/-- **Ledger A8** (@wolfe1978unimodality Thm. 2, p. 144, with the definition of `U_n` on the same
page; @kanter1977unimodality Defs. 1.2 and 3.1, pp. 66 and 70; @sato1999levy Def. 15.1, p. 90, and
Thm. 15.3(ii), p. 91, for "class L"): *"A symmetric `n`-dimensional distribution function of class
`L` is symmetric unimodal"*, where (Kanter, p. 70) a law on `ℝ^N` is *symmetric unimodal* if it is
in `U_N`, the measures `μ = ∫_{W_N} λ_K dν(λ_K)` with `ν` a measure on the set `W_N` of the
uniform laws `λ_K` of compact (convex, Def. 1.2) symmetric sets `K`, and `μ` is a probability
measure exactly when `ν` is.

Readings, each from the audited transcription (`blueprint/AXIOMS-verbatim.md` § A8):
* *symmetric* is Wolfe's p. 141, `P(B) = P(-B)` for every Borel `B`: `μ.map (-·) = μ`;
* *of class L* is reached from Sato's Definition 15.1 (`IsSelfDecomposableSato`) by his
  Theorem 15.3(ii), which writes a self-decomposable law as a limit of normed sums of an
  infinitesimal system, Wolfe's p. 141–142 definition with `B_k = 1/b_k`, `A_k = -c_k`;
* `λ_K` is `kanterUniform K`, with `K` nonempty (Kanter's quotient presupposes it; the audit, (a));
* the mixing measure `Λ` (Kanter's `ν`, Wolfe's `η`) is a probability measure on the measurable
  space of measures on `ℝ^d` (the Giry σ-algebra, generated by the evaluations `ν ↦ ν(A)`; on the
  probability measures of a Polish space it is the Borel σ-algebra of weak convergence, Kanter's
  convention on p. 70), **concentrated on `W_d`** in the sense that `Λ`-almost every measure is a
  `λ_K`. That `W_d` is itself a measurable set (Kanter's Cor. 3.1, p. 72) is **not** asserted: the
  audit (b) found its printed proof to cover only the `K` with nonempty interior. The reading
  uses a weaker fact (blind review W2B-1(a)): `W_d` is analytic, the image of the Polish space of
  nonempty compact convex symmetric sets under the Borel map `K ↦ λ_K`, hence universally
  measurable, so the image of Kanter's `ν` on `W_d` (relative σ-algebra) is a measure carried by a
  measurable subset of `W_d`, which is "`Λ`-almost every measure is a `λ_K`";
* `Λ` is a measure on **all** of `Measure (ℝ^d)`, where the page has it on the probability
  measures (W2B-1(b)): the two are equivalent, because the probability measures form a measurable
  set (`ν ↦ ν(ℝ^d)` is measurable) and `Λ`-almost every measure, being a `λ_K`, lies in it;
* the mixture `μ(A) = ∫ λ_K(A) Λ(dλ_K)` for every Borel `A` is `Λ.join = μ`.

Spent by `prop:isotropic-radial-monotone`, both clauses. Admitted by the author on 2026-10-05, after
the librarian's independent audit (verdict MATCH, read in Kanter's sense). -/
axiom wolfe_symmetric_unimodal (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x => -x) = μ) (hsd : IsSelfDecomposableSato μ) :
    ∃ Λ : Measure (Measure (Rd d)), IsProbabilityMeasure Λ ∧
      (∀ᵐ ν ∂Λ, IsKanterUniform ν) ∧ Λ.join = μ

/-! ## A9 — Bhatia, *Matrix Analysis*, Corollary III.4.6 (Lidskii), (III.21), p. 73 -/

/-- **Ledger A9** (@bhatia1997matrix Corollary III.4.6 (Lidskii), relation (III.21), printed p. 73;
`≺` as in (III.15), p. 71, and (II.2)–(II.3), p. 28; parallel @bhatia2007positive Exercise 6.5.3,
(6.47), p. 228): *"Let `A, B` be two positive matrices. Then all eigenvalues of `AB` are nonnegative
and `log λ↓(A) + log λ↑(B) ≺ log λ(AB) ≺ log λ↓(A) + log λ↓(B)`. (III.21)"* Only the second half is
stated.

Readings, each from the librarian's transcription (`blueprint/AXIOMS-verbatim.md` § A9):
* **the weak form.** The page states the *full* majorization: by (III.15) and (II.2)–(II.3) the
  partial sums of the `k` largest entries are bounded for `k = 1, …, n` and the totals are equal.
  This axiom states the partial sums only, a strict consequence of the page: for every
  `1 ≤ k ≤ d`, the sum of the `k` largest entries of `log λ(AB)` is at most that of
  `log λ↓(A) + log λ↓(B)`. The equality of the totals is `det(MN) = det M det N` and is proved, not
  admitted;
* `λ↓_i(X)` is `eigUp X (Fin.rev i)`, the `i`-th largest root of the characteristic polynomial,
  and `λ(AB)`, the eigenvalues of the product with multiplicity, compared through its decreasing
  rearrangement, is `eigUp (M * N)` read the same way: the characteristic polynomial of `MN` is
  that of `M^{1/2}NM^{1/2}` (`charpoly_mul_comm`), which splits over `ℝ` with positive roots;
* "positive" is read as positive definite: MA's positive matrices are semidefinite, with zero
  coordinates (a logarithm `-∞`) allowed; `log λ(AB)` needs every eigenvalue positive, so the axiom
  narrows to the definite case;
* the page is for complex matrices; a real positive definite matrix is a complex one with the same
  characteristic polynomial, so the real statement is a specialization.

Spent by `logSpec_product_majorized` (`lem:spectral-cones-products`) and through it by
`lem:spectral-cones`(5), `thm:cone-orders`, `lem:cone-orders-closed` and `lem:cone-orders-psd`.
Admitted by the author on 2026-10-05; re-read at *Matrix Analysis* p. 73 on 2026-10-06 (librarian),
the weak form standing and the axiom unchanged. -/
axiom gelfand_naimark_logMajorized {M N : Mat d} (hM : M.PosDef) (hN : N.PosDef) (k : ℕ)
    (hk : 1 ≤ k) (hkd : k ≤ d) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), Real.log (eigUp (M * N) (Fin.rev i)) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
        (Real.log (eigUp M (Fin.rev i)) + Real.log (eigUp N (Fin.rev i)))

/-! ## A10 — Schilling, Song, Vondraček, Theorem 13.14, p. 212, with Theorem 3.2, p. 21 -/

open scoped ComplexOrder in
/-- **Ledger A10** (@schilling2012bernstein Thm. 13.14 (Schoenberg; Bochner), printed p. 212;
Def. 3.1 and Thm. 3.2, printed p. 21; Def. 4.3, printed p. 36, with (4.8), pp. 45–46): *"A function
`f : (0,∞) → [0,∞)` is a Bernstein function if, and only if, for all `d ∈ ℕ` the function
`ξ ↦ f(|ξ|²)`, `ξ ∈ ℝ^d`, is continuous and negative definite"* (Thm. 13.14), only the direction
"if"; and *"A function `f : (0,∞) → ℝ` is a Bernstein function if, and only if, it admits the
representation `f(λ) = a + bλ + ∫_{(0,∞)} (1 - e^{-λt}) μ(dt)`, (3.2), where `a, b ≥ 0` and `μ` is a
measure on `(0,∞)` satisfying `∫_{(0,∞)} (1 ∧ t) μ(dt) < ∞`"* (Thm. 3.2), only the direction "only
if". The composite passes from the radial hypothesis to the representation and never names the
class of Bernstein functions (Def. 3.1).

Readings, each from the librarian's transcription (`blueprint/AXIOMS-verbatim.md` § A10):
* **negative definite** is Def. 4.3 on `(ℝ^d, +)` with the involution `ξ* = -ξ`, which on `ℝ^d` is
  (4.8): `∑_{j,k} (ψ(ξ_j) + conj ψ(ξ_k) - ψ(ξ_j - ξ_k)) c_j conj c_k ≥ 0` for every `n`, all
  `ξ_1, …, ξ_n ∈ ℝ^d` and all `c_1, …, c_n ∈ ℂ`, the inequality in `ℂ` (the sum real and
  nonnegative, `ComplexOrder`). For the real function `ψ(ξ) = f(|ξ|²)` the conjugate is `ψ(ξ_k)`
  itself, and Def. 4.3's other condition, that `ψ` is hermitian (`ψ(-ξ) = conj ψ(ξ)`), holds
  automatically, `ψ` being real and even, so it is not written;
* **continuous** is ordinary continuity of `ξ ↦ f(|ξ|²)` on `ℝ^d`; the book defines no other;
* **the value at `0`**, `f(0) := f(0+)`. The theorem is stated for `f` on `(0,∞)` but evaluates
  `f(|ξ|²)` at `ξ = 0`, and the book fixes `f(0)` nowhere at Thm. 13.14; its convention elsewhere
  is `f(0) := f(0+)` (p. 15, p. 211, and `a = f(0+)` in the proof of Thm. 3.2, p. 22). Here
  `f : ℝ → ℝ`, and the continuity hypothesis at `ξ = 0` forces `f(0) = lim_{σ↓0} f(σ)`, so the
  axiom applies only under that convention; the values of `f` on `(-∞, 0)` are never read;
* **`d` ranges over all of `ℕ`**, including `d = 0`. The book's `ℕ` is `{1, 2, 3, …}` (Index of
  notation), so the hypothesis here is at least as strong as the page's: at `d = 0` it asks
  `f(0) ≥ 0`, which continuity and `f ≥ 0` on `(0,∞)` already give;
* **the conclusion** is the representation (3.2) at every `σ > 0`, with `a, b ≥ 0`; "a measure on
  `(0,∞)`" is a measure `m` on `ℝ` with `m((-∞, 0]) = 0`, and `1 ∧ t` is `min 1 t`. The identity is
  stated in `[0,∞]`, every term being nonnegative: it is the real identity (3.2) with a finite
  integral, the form `CausalAdmissible.exponentL` uses.

**Not carried**: the converse of Thm. 13.14 (its sufficiency direction, Example 13.13); the
uniqueness of the triplet, the last sentence of Thm. 3.2, which
`lem:bernstein-triplet-unique` proves (`bernstein_triplet_unique`); the class of Bernstein functions
and anything about derivatives; the negative definiteness of the radial exponents, which
`lem:lk-negative-definite` proves from the polar reading. Spent twice by `classS_of_classAInf`
(`lem:filtration-top`): for `f = F(√(2·))` and for each `f - f(c²·)`, `0 < c ≤ 1`. Admitted by
the author on 2026-10-07. -/
axiom schoenberg_radial_bernstein (f : ℝ → ℝ) (hf : ∀ σ : ℝ, 0 < σ → 0 ≤ f σ)
    (hnd : ∀ d : ℕ, Continuous (fun ξ : Rd d => f (‖ξ‖ ^ 2)) ∧
      ∀ (n : ℕ) (ξ : Fin n → Rd d) (c : Fin n → ℂ),
        0 ≤ ∑ j, ∑ k, (((f (‖ξ j‖ ^ 2) + f (‖ξ k‖ ^ 2) - f (‖ξ j - ξ k‖ ^ 2) : ℝ) : ℂ) *
          c j * starRingEnd ℂ (c k))) :
    ∃ (a b : ℝ) (m : Measure ℝ), 0 ≤ a ∧ 0 ≤ b ∧ m (Iic 0) = 0 ∧
      ∫⁻ t, ENNReal.ofReal (min 1 t) ∂m ≠ ⊤ ∧
      ∀ σ : ℝ, 0 < σ → ENNReal.ofReal (f σ) =
        ENNReal.ofReal a + ENNReal.ofReal (b * σ) +
          ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(σ * t))) ∂m

/-! ## A11 — Bingham, Goldie, Teugels, *Regular Variation*, Theorem 1.7.1′, p. 38 -/

/-- **Ledger A11** (@bingham1987regular Thm. 1.7.1′, attributed there to Feller (1971), XIII,
§ 5, printed p. 38; the Laplace–Stieltjes transform (1.7.0a), printed p. 37; the definition of a
slowly varying function, (1.2.1), printed p. 6, and of the class `R₀`, printed p. 18): *"Let `U`
be non-decreasing on `ℝ`, `U(x) = 0` for all `x < 0`, and such that `Û(s) < ∞` for all large
`s`. Let `ℓ ∈ R₀`, `c ≥ 0`, `ρ ≥ 0`. The following are equivalent:
`U(x) ∼ c x^ρ ℓ(1/x)/Γ(1+ρ)` `(x → 0+)`, (1.7.1′); `Û(s) ∼ c s^{-ρ} ℓ(s)` `(s → ∞)`. (1.7.2′)"*
Only the direction (1.7.2′) ⇒ (1.7.1′) is stated, the Tauberian one.

Readings, each from the transcription (`blueprint/AXIOMS-verbatim.md` § A11):
* **`U` is the distribution function of a finite measure `ν` on `[0,∞)`**, `U(x) = ν((-∞, x])`.
  It is non-decreasing and right-continuous, it vanishes for `x < 0` because `ν((-∞,0)) = 0`,
  and its transform `Û(s) = ∫_{[0,∞)} e^{-sx} dU(x)` of (1.7.0a) is `∫ e^{-sx} ν(dx)`, finite for
  every `s ≥ 0`. The page takes every non-decreasing `U` vanishing on `(-∞,0)` with `Û` finite
  for large `s`; a finite measure is a narrowing;
* **`ℓ ∈ R₀`** is (1.2.1): positive, measurable, `ℓ(λx)/ℓ(x) → 1` as `x → ∞` for every `λ > 0`.
  The page asks positivity and measurability on a neighbourhood `[X,∞)` of infinity; the axiom
  asks positivity on `(0,∞)` and measurability on `ℝ`, a narrowing, and the book's own convention
  (p. 6: "we may (and often shall) suppose `ℓ` defined on `(0,∞)`");
* **`∼`** is asymptotic equality, the quotient tending to `1`. The page reads the case `c = 0`
  as `o(·)` (p. 37, after Theorem 1.7.1); the axiom takes `c > 0`, where the quotient form is the
  page's;
* **`ρ > 0`**, where the page has `ρ ≥ 0`: the two uses have `ρ = c/2` and `ρ = d/2`.

**Not carried**: the Abelian direction (1.7.1′) ⇒ (1.7.2′); the cases `c = 0` and `ρ = 0`;
Theorem 1.7.1, the form at `x → ∞`, `s → 0+`; the monotone density theorem (Thm. 1.7.2b),
Potter's bounds (Thm. 1.5.6) and Prop. 1.5.9a of the same book, whose uses in the proof of
`prop:origin-rate-d` are proved in the form it needs (`tendsto_radial_density_of_ball`,
`antitoneOn_dyadic_bound`, `IsRayProfile.tendsto_truncMoment_dilate`); and the behaviour of any
particular transform. Spent by `tendsto_ball_of_gauss`, for the image of a law on `ℝ^d` under
`x ↦ |x|²`, and through it by `prop:origin-rate-d`, once in each clause. Admitted on the author's
decision of 2026-10-11 (Q-0416: the rate at the centre as a proposition, on cited Tauberian
theorems). -/
axiom karamata_tauberian_zero (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0)
    (ℓ : ℝ → ℝ) (hℓm : Measurable ℓ) (hℓpos : ∀ x : ℝ, 0 < x → 0 < ℓ x)
    (hℓ : ∀ a : ℝ, 0 < a → Tendsto (fun x => ℓ (a * x) / ℓ x) atTop (𝓝 1))
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (h : Tendsto (fun s : ℝ => (∫ x, Real.exp (-(s * x)) ∂ν) / (c * s ^ (-ρ) * ℓ s)) atTop
      (𝓝 1)) :
    Tendsto (fun x : ℝ => (ν (Iic x)).toReal / (c * x ^ ρ * ℓ (1 / x) / Real.Gamma (1 + ρ)))
      (𝓝[>] 0) (𝓝 1)

end AffineHemigroup
