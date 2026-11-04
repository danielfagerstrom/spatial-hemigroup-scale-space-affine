# Verification of the external review, round 1: the prior art (the Hankel theorems, the Bessel potentials, the heat-kernel sentences, the filtration, Table 3)

**What this is.** Article-kit's `docs/PROCESS.md` § 9 asks that every finding of an external review
be verified against the sources before anything changes. This record verifies the prior-art shard
of `review-content-iso-review-1-GPT-6.1-Sol-Ultra.md`: its § 2 ("Rate at the centre"), its § 6
("Novelty and relation to prior work") and required changes 1 and 13. Nothing in the paper, the
blueprint or the Lean sources was edited, and nothing was committed.

**Against what.** The worktree `spatial-hemigroup-affine-q0417`, branch `queue/q-0423`, at
`8e63949` (2026-10-12), whose `paper-iso/` is the tag `iso-review-1`. Statement numbers are those of
`review-build-iso-review-1.pdf`: Theorem 3.12 (the threshold), Corollary 3.13, Proposition 3.14
(the shape), **Proposition 3.15 (the rate, `prop:origin-rate-d`)**, Propositions 3.16 and 3.17 (the
bounds), Theorem 3.19 (the filtration), Theorem 3.20 (the Cin rays), Lemma A.3
(`lem:isotropic-exponent-log`), Table 3 (`tab:in-print`, p. 21), (3.7) (`eq:matern-density`).

**Sources read for it, all through the librarian's CLI, formulas from page images.**

| source | read | note |
|---|---|---|
| Bingham–Inoue, *An Abel–Tauber theorem for Hankel transforms* (Hokkaido preprint 370, 1997) | pp. 1–8, every page at the image | `READING-bingham1997abel.md` |
| Bingham–Inoue, *Ratio Mercerian theorems …* (Hokkaido preprint 395, 1997) | pp. 1–8, 28, 29 at the image | `READING-bingham1999ratio.md` |
| Bingham–Goldie–Teugels, § 4.10 | pp. 240, 241 at the image | `READING-bingham1997abel.md` § 7 |
| Aronszajn–Smith, *Theory of Bessel potentials I* | pp. 414–418 at the image | `READING-aronszajn1961theory.md` |
| Cygan–Grzywny–Trojan (arXiv v2) | pp. 10, 11, 16 at the image, pp. 1–18 text layer | `READING-cygan2017asymptotic.md` |
| Grzywny–Ryznar–Trojan (published text) | pp. 63, 64 at the image (Example 3), p. 27 text layer (Thm. 3.10) | the existing `READING-grzywny2019asymptotic.md` |
| Sato's book | p. 109 at the image, p. 108 text layer (Theorem 17.5) | § 4 below |
| **[2nd pass]** Leonenko–Olenko, *Tauberian and Abelian theorems for long-range dependent random fields* (arXiv v1, 26 pp.) | pp. 3–10, 15, 17 at the image; pp. 1, 2, 11–14, 16, 25–26 text layer | `READING-leonenko2013tauberian.md`; § 1.9 below |
| the existing notes on Cho–Kang–Kim, Bogdan–Grzywny–Ryznar, Mimica, Knopova–Schilling, Gneiting, Schoenberg, and the memo `PRIOR-ART-origin-threshold-reading.md` | read, not re-verified at the page | |

**Computations.** `verify-round1-scripts/b_hankel_prior_art.py`
(`uv run --no-project --with mpmath python b_hankel_prior_art.py`), output in
`b_hankel_prior_art-output.txt`: 113 checks, all pass. Its blocks A–H are cited below.

**Second pass, 2026-10-12 (later the same day).** The first pass named the random-field literature
as its open flank ("What could not be read"). Leonenko–Olenko 2013 was then acquired and read at
the page. It closes the flank against the paper: **clause (1) of Proposition 3.15 is in print, for
the ball and for the density, in every dimension and for every 0 < c < d, with the paper's
constants.** What changed is marked **[2nd pass]**: this paragraph, the table of verdicts, "The
consequence", the new § 1.9, § 1.8(d), the rate row of § 5, § 6.1, § 7 and § 8. §§ 1.1–1.7 are the
first pass and stand as written; § 1.9 says where they are superseded.

**Verdicts in one table.**

| # | the referee's finding | verdict |
|---|---|---|
| 1 | Classical Hankel theorems give the rate for every 0 < c < d in d = 2, 3, for c > (d−3)/2 in general, and the boundary c = d in every d ≥ 2 | **CONFIRMED**, range exact. The theorem is older than cited (1972/1974, not 1997). A closer antecedent the referee did not name was found (§ 1.7). **[2nd pass] And the referee understates it:** the referee's reduction is itself a printed theorem (Leonenko–Olenko 2013, Theorem 2), and the subcritical rate is in print with no restriction on c (their Theorems 3 and 4, from Olenko 1991 and Leonenko 1999); § 1.9 |
| 2 | The Matérn example is Aronszajn–Smith's Bessel kernel, (4,2) and (4,6), with p(x) = 2^{d/2}G_{2γ}(√2x) | **CONFIRMED**, exactly |
| 3 | "The literature does not study one law" is wrong; "a limit τ → 0 says nothing about one kernel" is too categorical; Cygan–Grzywny–Trojan and Mimica need a positive index | **CONFIRMED** |
| 4 | Characteristic functions generate self-decomposable exponents through F(r) = ∫_0^r[1 − φ(u)]du/u, so the classical dimension literature is closer than the paper says | **CONFIRMED, and it goes further than the referee takes it**: the map carries Gneiting's strict inclusions to 𝒜_d ⊋ 𝒜_{d+1} at every d in a few lines |
| 5 | Table 3, row by row | every verdict of the referee **stands**; corrected cells in § 5 |

**The consequence, stated once.** The paper's lead claim, "the rate is new for d ≥ 2 as far as the
author has found", cannot stand. In the plane and in space, the dimensions of imaging, Proposition
3.15 is a corollary of a theorem of 1972–74 and its boundary case of 1997, with Watanabe's theorem
and one paragraph about the class. What is left that the printed Hankel theorem does not cover is
d ≥ 4 with 0 < c ≤ (d−3)/2, and that sliver is covered by a Tauberian argument that is itself in
print in ℝ^d, for another measure and with the same constants (§ 1.7). The rate belongs in the
second tier, with the threshold: stated here for the class from known theorems, not found stated.
The second lead claim, "the steps from 𝒜_3 on are new", is at risk in the same way (§ 4).

**[2nd pass] The consequence, restated.** The paragraph above is too kind to the claim. Clause (1)
of Proposition 3.15 is not a corollary to be assembled. It is a stated theorem about
rotation-invariant probability measures (Leonenko–Olenko, Theorems 3 and 4), in every dimension
and for every 0 < c < d, applied to a class for which its two hypotheses are themselves in print
(Grzywny–Ryznar–Trojan's Theorem 3.5; Watanabe). The sliver d ≥ 4, c ≤ (d−3)/2 is closed. What is
in no source read is clause (2), the boundary c = d, as a statement; it is a corollary of
Bingham–Inoue's Theorem 1.1 by the inversion formula, and its explicit lower bound is the paper's.
The rate is a known theorem, proved again here and machine-checked. It is not a contribution in
either tier, except for the boundary clause, which stays in the second.

---

## 1. The Hankel theorems and the rate — CONFIRMED

### 1.1 The statements, from the page

`READING-bingham1997abel.md` has the transcriptions. In short, for ν ≥ −1/2,
t^{ν+1/2}f(t) ∈ L¹_loc[0,∞) and **f ultimately decreasing to zero at infinity**, with

F_ν(x) := ∫_0^{∞−} f(t)(xt)^{1/2}J_ν(xt)dt (x > 0), an improper integral, (1.1)

- **Theorem 1.2** (p. 2; *"the following known Abel-Tauber theorem for Hankel transforms"*,
  attributed to [B1] Bingham 1972 and [RS] Ridenhour–Soni 1974, "see also" Soni–Soni 1975): for
  ρ ∈ (−ν − 3/2, 0) and ℓ slowly varying, f(t) ∼ t^ρℓ(t) (t → ∞) **if and only if**
  F_ν(x) ∼ x^{−ρ−1}ℓ(1/x)·2^{ρ+1/2}Γ(3/4 + ν/2 + ρ/2)/Γ(1/4 + ν/2 − ρ/2) (x → 0+).
- **Theorem 1.1** (pp. 1–2; Bingham and Inoue's own, the boundary ρ = −ν − 3/2): with
  F̄_ν(x) := x^{ν+1/2}F_ν(1/x), f(t) ∼ t^{−(ν+3/2)}ℓ(t) if and only if F̄_ν ∈ Π_ℓ with ℓ-index
  1/(2^νΓ(ν+1)), and both imply
  {F̄_ν(x) − (2^νΓ(ν+1))^{−1}∫_0^x t^{ν+1/2}f(t)dt}/(x^{ν+3/2}f(x)) → (2^νΓ(ν+1))^{−1}{log 2 − γ/2 + ½ψ(ν+1)}. (1.4)

What else the paper says of the earlier theorems: only the attribution above, and that the cosine
and sine cases ν = ∓1/2 of Theorem 1.1 were proved by Inoue in 1995. Bingham–Goldie–Teugels (1987),
p. 240, state the Fourier cases (Theorem 4.10.3, Pitman 1968 and Soni–Soni 1975) for f
non-increasing to 0 and 0 < α < 1, and on p. 241 point to *"Soni & Soni (1975), II, Bingham
(1972a)"* for *"the corresponding analogues"* for Hankel transforms. Which hypotheses the papers of
1972, 1974 and 1975 use themselves could not be read (they are not held).

**A correction to the referee's attribution.** The referee cites "Bingham–Inoue, Theorems 1.1–1.2".
Theorem 1.2, which carries the whole subcritical case, is not theirs: it is the theorem of Bingham
(1972) and Ridenhour–Soni (1974), restated. Only the boundary case is of 1997. So the antecedent of
clause (1) of Proposition 3.15 is fifty years old, six years older than Sato and Yamazato's theorem
on the line.

### 1.2 The reduction: the mass of a ball as a Hankel transform

Let μ be a rotation-invariant probability measure on ℝ^d, d ≥ 1, with μ(∂B_s) = 0 for the ball
B_s = {|x| ≤ s}, and χ(t) := μ̂(te) for a unit vector e. Put

**ν := d/2, f(t) := t^{(d−3)/2}χ(t).**

**Lemma (ball inversion).** If the improper integral (1.1) of this f converges at x = s, then

**μ(B_s) = (2^{1−d/2}/Γ(d/2))·s^{(d−1)/2}·F_{d/2}(s).**

*Proof.* The Fourier transform of the indicator of the ball is
∫_{B_s}e^{i⟨ξ,x⟩}dx = (2πs/|ξ|)^{d/2}J_{d/2}(s|ξ|). Let g_ε be the density of N(0, εI). By
Parseval's formula, both sides being integrable,
∫(1_{B_s} ∗ g_ε)dμ = (2π)^{−d}∫(2πs/|ξ|)^{d/2}J_{d/2}(s|ξ|)e^{−ε|ξ|²/2}μ̂(ξ)dξ. The left side tends
to μ(B_s) as ε → 0, because 1_{B_s} ∗ g_ε → 1_{B_s} off ∂B_s, is bounded by 1, and μ(∂B_s) = 0. In
polar coordinates the right side is
(2π)^{−d}|S^{d−1}|(2πs)^{d/2}∫_0^∞ h(t)e^{−εt²/2}dt, with h(t) := χ(t)t^{d/2−1}J_{d/2}(st), and
(2π)^{−d}|S^{d−1}|(2π)^{d/2} = 2^{1−d/2}/Γ(d/2). Let H(T) := ∫_0^T h. By parts,
∫_0^∞ h(t)e^{−εt²/2}dt = ∫_0^∞ H(t)·εte^{−εt²/2}dt, and εte^{−εt²/2}dt is a probability measure that
moves to infinity as ε → 0; since H is bounded with limit H(∞), the integral tends to H(∞).
Finally h(t) = s^{−1/2}f(t)(st)^{1/2}J_{d/2}(st), so H(∞) = s^{−1/2}F_{d/2}(s). ∎

This is the referee's "ball inversion", with the same ν and f. It was checked numerically at the
Matérn law in d = 1, 2, 3, 4 against the direct integral of the closed-form density (block A of
the script: agreement to 10^{−8} or better in six cases).

### 1.3 The hypotheses of the theorems, for the class

Let (0, k_d) be an isotropic origin datum with Gaussian coefficient 0 and 0 < c = k_d(0+) < ∞, μ
its law, F(t) the radial exponent, χ = e^{−F}.

**(i) Local integrability.** t^{ν+1/2}f(t) = t^{d−1}χ(t), bounded on bounded sets. ✓ for every d.

**(ii) No mass on spheres.** μ has a density (Proposition 3.14; Watanabe). ✓

**(iii) Regular variation.** f(t) = t^ρL(t) with **ρ = (d−3)/2 − c** and L(t) = t^cχ(t) slowly
varying (Lemma A.3(2); in print as Grzywny–Ryznar–Trojan's Theorem 3.5; for d ≥ 2 it also follows
at once from (v) below, since tL′(t)/L(t) = c − tF′(t) → 0).

**(iv) The index is in the range of Theorem 1.2** exactly when −(d+3)/2 < (d−3)/2 − c < 0, that
is **(d−3)/2 < c < d**. It is at the boundary of Theorem 1.1, ρ = −ν − 3/2, exactly when **c = d**.

**(v) "tF′(t) → c in d ≥ 2": true for every member of the class. Proof.** Let ϖ be the measure on
(0,∞) with ϖ((r,∞)) = k_d(r) for the right-continuous version of the profile; it has total mass
k_d(0+) = c, finite, and no mass at 0. With Ω_d(u) the mean of e^{iu⟨e,θ⟩} over the unit sphere and
H(x) := ∫_0^x (1 − Ω_d(u))du/u ≥ 0,

F(t) = ∫_0^∞ (1 − Ω_d(tr))k_d(r)dr/r = ∫_{(0,∞)} ϖ(ds)∫_0^s (1 − Ω_d(tr))dr/r = ∫_{(0,∞)} H(ts)ϖ(ds)

by Tonelli (the integrand is nonnegative; this is the referee's "layer cake"). Since
t∂_tH(ts) = 1 − Ω_d(ts) is bounded by 2 and ϖ is finite, F is continuously differentiable and

**tF′(t) = ∫_{(0,∞)} (1 − Ω_d(ts))ϖ(ds).**

For d ≥ 2, Ω_d(u) → 0 as u → ∞, so the integrand tends to 1 for every s > 0, and by dominated
convergence tF′(t) → ϖ((0,∞)) = c. ∎

**The same limit is false in d = 1**, where Ω_1 = cos: for the step profile k_1 = c·1_{(0,1)},
tF′(t) = c(1 − cos t). The referee's "in d ≥ 2" is exact. (Block D of the script: the values of
1 − Ω_d(t) at t near 50 and 500, for d = 1, 2, 3, 4, and a numerical derivative for d = 2.)

**(vi) "f ultimately decreasing to zero": for which (d, c).** What the theorem's proof uses is that
f is positive and non-increasing on some [X,∞) (its Step 1) and tends to 0.

- F is nondecreasing on (0,∞) in every dimension: F(t) = ∫_0^∞(1 − Ω_d(u))k_d(u/t)du/u, with
  1 − Ω_d ≥ 0 and k_d(u/t) nondecreasing in t. So χ is non-increasing.
- **d = 1, 2, 3:** t^{(d−3)/2} is non-increasing, so **f is non-increasing on all of (0,∞), for
  every c**, with no appeal to (v); and f → 0 since ρ < 0. (So the monotonicity holds on the line
  too, where (v) fails.)
- **d ≥ 4:** tf′(t)/f(t) = (d−3)/2 − tF′(t) → (d−3)/2 − c by (v). If **c > (d−3)/2**, f is
  eventually decreasing, and tends to 0. If **c < (d−3)/2**, f is eventually *increasing* and
  unbounded: it is not "decreasing to zero", the improper integral (1.1) does not converge, and
  the theorem does not apply in any form. If c = (d−3)/2, f = L is slowly varying and ρ = 0, which
  Theorem 1.2 excludes.

So the monotone hypothesis is exactly what the theorem needs, and it holds exactly where the index
condition (iv) holds. The two conditions do not bite separately.

### 1.4 The conclusion of the theorems, and the constant

**Below the threshold.** For (d−3)/2 < c < d, Theorem 1.2 with ν = d/2, ρ = (d−3)/2 − c, ℓ = L:
3/4 + ν/2 + ρ/2 = (d−c)/2, 1/4 + ν/2 − ρ/2 = 1 + c/2, ρ + 1/2 = d/2 − 1 − c, −ρ − 1 = c − (d−1)/2,
so

F_{d/2}(s) ∼ s^{c−(d−1)/2}L(1/s)·2^{d/2−1−c}Γ((d−c)/2)/Γ(1+c/2) (s → 0+),

and by the lemma, with s^cL(1/s) = χ(1/s) = μ̂(e/s),

**μ(B_s) ∼ [2^{−c}Γ((d−c)/2) / (Γ(d/2)Γ(1+c/2))]·μ̂(e/s).**

The bracket is the paper's R(d,c)·|S^{d−1}|/c:
R(d,c)|S^{d−1}|/c = Γ((d−c)/2)/(2^cπ^{d/2}Γ(c/2))·2π^{d/2}/(Γ(d/2)c) = 2^{−c}Γ((d−c)/2)/(Γ(d/2)Γ(1+c/2)).
**The constant comes out as the paper's**, and as the "I_c/Γ(1+c/2)" of its proof. (Block B: the
identity on 32 pairs (d,c), and the limit at the Matérn law in d = 2, 3.)

**At the threshold.** For c = d, Theorem 1.1 with ℓ(t) = t^{ν+3/2}f(t) = t^dχ(t) = L(t) and
P(x) := ∫_0^x t^{ν+1/2}f(t)dt = ∫_0^x t^{d−1}χ(t)dt: by (1.4),
F̄_{d/2}(x) = P(x)/(2^{d/2}Γ(d/2+1)) + O(L(x)). Since P(x) = P(1) + ∫_1^x L(t)dt/t and
L(x)/∫_1^x L(t)dt/t → 0 for every slowly varying L (Bingham–Goldie–Teugels, (1.5.8) and
Proposition 1.5.9a), F̄_{d/2}(x) ∼ P(x)/(2^{d/2}Γ(d/2+1)) whenever P is unbounded. With
F_{d/2}(s) = s^{(d+1)/2}F̄_{d/2}(1/s) and the lemma,

**μ(B_s) ∼ [2^{1−d}/(Γ(d/2)Γ(d/2+1))]·s^d·P(1/s) = (2π)^{−d}V_d·s^d·I(s),**

since I(s) = |S^{d−1}|P(1/s) and (2π)^{−d}V_d|S^{d−1}| = 2^{1−d}/(Γ(d/2)Γ(d/2+1)). This is the first
limit of clause (2). (Block C: the leading constant, and the second-order constant of (1.4) at
d = 2 and d = 3 to four digits.) That P is unbounded, and the explicit bound
I(s) ≥ |S^{d−1}|e^{−13d/4−2C_k}log(1/s), come from the lower bound L ≥ e^{−13c/4−2C_k} of Lemma
A.3(1), not from the Hankel theorem.

**From the ball to the density.** m(s) := μ(B_s) = |S^{d−1}|∫_0^s q(r)r^{d−1}dr with q
nonincreasing (Proposition 3.14; Watanabe 1983, p. 488), and m varies regularly at 0 with index c
(index d at the threshold). The monotone density theorem (Bingham–Goldie–Teugels, Theorem 1.7.2b,
in the volume variable, or the shell inequalities of the paper's Step 5) gives
q(s) ∼ c·m(s)/(|S^{d−1}|s^d), that is q(s) ∼ R(d,c)s^{−d}μ̂(e/s), and q(s) ∼ (2π)^{−d}I(s) at
c = d. The referee's "shell argument".

### 1.5 The range: the referee's is right

| | covered by Theorem 1.2 (c < d) or 1.1 (c = d) with §§ 1.2–1.4 | not covered |
|---|---|---|
| d = 1 | every 0 < c ≤ 1 (ν = 1/2, f = χ(t)/t, the sine transform) | — |
| d = 2 | every 0 < c ≤ 2 | — |
| d = 3 | every 0 < c ≤ 3 | — |
| d ≥ 4 | (d−3)/2 < c ≤ d | **0 < c ≤ (d−3)/2** |

- "This covers every 0 < c < d in dimensions two and three": **right.** In d ≤ 3 not even the
  layer-cake limit is needed.
- "c > (d−3)/2" in general: **right, and sharp for this theorem**: below it f is unbounded and the
  transform (1.1) does not exist.
- "At c = d, Theorem 1.1 … in every d ≥ 2": **right**; it holds in d = 1 as well.
- Neither too generous nor too narrow. The referee does not claim d = 1 (where the result is Sato
  and Yamazato's anyway), and does not claim d ≥ 4 with small c.

**Counter-check of the uncovered region** (block D): at the Matérn laws d = 4, c = 0.3 and d = 5,
c = 0.8, tf′/f → 0.2 > 0, so f increases and Theorem 1.2 does not apply, while the closed form
gives q(s)/(R(d,c)s^{−d}μ̂(e/s)) = 0.99997, 0.999999997, 1.0 at s = 10^{−2}, 10^{−4}, 10^{−6}. The
proposition is true there and the printed Hankel theorem is silent.

### 1.6 Does anything read widen the range?

No. `bingham1999ratio` (`READING-bingham1999ratio.md`) is Mercerian, keeps "f ultimately decreasing
to zero" in its Hankel theorems (Theorems 4 and 5, p. 6), and says (p. 7): *"The condition that f be
ultimately decreasing ensures that the integral giving the Hankel transform converges
(conditionally). Some such condition is needed. … This implies ρ ≤ 0."* Bingham–Goldie–Teugels
p. 241 is a pointer to Bingham 1972 and Soni–Soni 1975, with *"the Tauberian condition f↓0"* named
as what the inversion formulae use. A weaker condition of monotone type (quasi-monotonicity) would
gain nothing for the class, which has the monotonicity itself wherever ρ < 0. The obstruction at
c ≤ (d−3)/2 is the divergence of the integral, not a removable hypothesis.

Whether a Hankel theorem for a *summable* transform, or the theorem applied to Riesz means of the
ball mass (order d/2 + k of the Bessel function, f(t) = t^{(d−3)/2−k}χ(t)), reaches the remaining
cases was not found in what was read and was not worked out here. It would be a derivation, not a
citation.

### 1.7 A closer antecedent the referee did not name: Cygan–Grzywny–Trojan, Theorems 8–9

`READING-cygan2017asymptotic.md` § 3. For an isotropic unimodal Lévy process in ℝ^d, d ≥ 3, with
potential measure G and exponent ψ regularly varying at infinity with index α, at the image of
p. 16 of the arXiv version:

- Theorem 9: lim_{r→0+} ψ(r^{−1})G({|x| ≤ r}) = 2^{−α}Γ((d−α)/2)/(Γ(d/2)Γ(1+α/2)), α ∈ [0,2];
- Corollary 4: lim_{x→0} |x|^dψ(|x|^{−1})G(x) = 2^{−α}π^{−d/2}Γ((d−α)/2)/Γ(α/2), α ∈ (0,2].

The transform of G is 1/ψ. So Corollary 4 reads G(x) ∼ R(d,α)|x|^{−d}Ĝ(e/|x|) and Theorem 9 gives
the ball with the constant R(d,α)|S^{d−1}|/α: **the two limits of clause (1) of Proposition 3.15,
with the same constants, for the potential measure in place of the law** (block G). The proof
printed for the twin Theorem 8 is the paper's proof: the Gaussian average as a Laplace transform,
dominated convergence on the Fourier side, *"a Tauberian theorem (see e.g. [5, Theorem 1.7.1])"*,
and for the density *"the line of reasoning from the proof of Theorem 4"*, the monotone density
argument on shells.

This is a statement about one measure with no time in it, in ℝ^d, in the literature the paper
compares itself with, by the method the paper uses. It does not contain Proposition 3.15 (another
measure; the index is that of an exponent, so α ≤ 2; d ≥ 3), but with it the sentence "in ℝ^d the
literature read has the rate only as t → 0 along a semigroup or up to constants" is no longer an
accurate account of where the *method and the constant* were in print. The memo of 2026-10-11 listed
this paper as unread (`PRIOR-ART-origin-threshold-reading.md` § 9).

### 1.8 The four conclusions asked for

**(a) Is Proposition 3.15 a corollary of Bingham–Inoue's theorems plus facts about the class?**
Yes, for d = 1, 2, 3 with every 0 < c ≤ d, and for d ≥ 4 with (d−3)/2 < c ≤ d. The facts about the
class are: the density exists and is radially nonincreasing (Watanabe 1983); the transform along a
ray is nonincreasing (two lines) and varies regularly with index −c (Grzywny–Ryznar–Trojan, Theorem
3.5; the paper's Lemma A.3(2)); for d ≥ 4 the limit tF′(t) → c (the paragraph of § 1.3(v)); the
ball-inversion lemma (§ 1.2, a paragraph); and the monotone density theorem. Each is in print or a
paragraph. The specialization is not stated in the Hankel papers read, which never mention
probability laws.

**(b) What in the proposition is then not covered.**
- *d ≥ 4 with 0 < c ≤ (d−3)/2*: not covered, and not coverable by this theorem.
- *d = 1*: covered (and it is Sato–Yamazato's Theorem 1.7 in any case).
- *The density as against the ball*: covered, by Watanabe's theorem and the monotone density
  theorem; both are in print, and the paper's own proof needs the same two things.
- *The explicit logarithmic lower bound at c = d*: not from the Hankel theorem. It is Lemma
  A.3(1), whose content on the line is Trabs's and Sato–Yamazato's and whose explicit constant is
  the paper's.
- *The equivalence.* Theorem 1.2 is an "if and only if": for a rotation-invariant law with f
  ultimately decreasing to zero, the ball mass varies regularly with index c ∈ ((d−3)/2, d) exactly
  when the transform does with index −c. The proposition states one direction.

**(c) Is the paper's own proof the same theorem, or a different route with a different range?** A
different route. The Hankel theorem is an Abelian theorem for an oscillating, conditionally
convergent kernel: its condition is on the *transform* (monotone, so that the integral converges
and the second mean-value theorem controls the tail), and it stops at ρ < 0. The paper's proof
replaces the sharp cutoff by a Gaussian one, so that the Abelian step is dominated convergence
against a positive kernel with no condition on the transform beyond regular variation, and then
uses Karamata's theorem, whose Tauberian condition is the monotonicity of the *ball mass*, which a
measure has for free. Its range is every d ≥ 1 and every 0 < c ≤ d. The conclusions agree wherever
both apply. But the paper's route is not new either: it is Sato and Yamazato's on the line (the
paper says so) and Cygan, Grzywny and Trojan's in ℝ^d for the potential measure (§ 1.7; the paper
does not say so).

**(d) The honest sentence.** *Known:* for the Bessel (Matérn) kernels, the rate with its constant
in all three regimes and every dimension, since 1961 (Aronszajn–Smith). For a function on the
half-line that is ultimately decreasing to zero, the Abel–Tauber theorem for its Hankel transform
since 1972–74 (Bingham; Ridenhour–Soni), with the boundary case since 1997 (Bingham–Inoue); applied
to the inversion formula for the mass of a ball it gives the proposition's ball asymptotics for
every rotation-invariant law whose transform is monotone and varies regularly with index −c,
(d−3)/2 < c ≤ d, hence for every law of the class in the plane and in space. On the line, the rate
for the self-decomposable laws since 1978 (Sato–Yamazato). In ℝ^d, the same asymptotics with the
same constants for the potential measure since 2017 (Cygan–Grzywny–Trojan), and for the laws of the
semigroup as t → 0 and up to constants since 2019 (Grzywny–Ryznar–Trojan). *What the paper adds:*
the statement for the class of rotation-invariant self-decomposable laws with no Gaussian part, for
the ball and for the density, in every dimension and for every 0 < c ≤ d by one proof, including
d ≥ 4 with c ≤ (d−3)/2 where the printed Hankel theorem does not apply; the explicit logarithmic
lower bound at c = d; and a machine-checked proof. The author has not found the statement for the
class; it is not a new theorem in kind.

**[2nd pass] (d), superseded by § 1.9.** The "what the paper adds" above claimed too much. Read
§ 1.9(v) for the sentence that the sources now support.

### 1.9 [2nd pass] Leonenko–Olenko 2013: the subcritical rate is a printed theorem, in every dimension

`READING-leonenko2013tauberian.md` has the transcriptions; pp. 3–10, 15, 17 were read at the image.

**(i) The dictionary, confirmed at the page.** The survey treats a homogeneous isotropic random
field on ℝ^n with unit variance: its covariance B(r) is B(x) = ∫e^{i⟨x,u⟩}F(du) for the spectral
measure F, a probability measure (Proposition 1, p. 3; B(0) = 1, p. 7); G(λ) = F({‖u‖ < λ}) is the
spectral mass of a ball (p. 4); g is the density of F with respect to Lebesgue measure,
G′(λ) = |S^{n−1}|λ^{n−1}g(λ) (Definition 3, p. 5). Remark 3 (p. 10) says that these B are exactly
the characteristic functions of symmetric distributions in ℝ^n. **So μ is F, μ(B_s) is G(s), q is
g, and μ̂(re) is B(r)**, in the paper's Fourier convention, and the statements are for B at
infinity and G, g at zero: the paper's direction.

**(ii) Theorem 2 (p. 8) is the referee's reduction, printed.** From the inversion formula (4)
(p. 4; the lemma of § 1.2) and *"Theorem 1.2 in Bingham, Inoue 1997a with ν = n/2"*: if
r^{(n−3)/2}B(r) is ultimately decreasing to zero, then for (n−3)/2 < α < n,
r^αB(r) ∼ L(r) (r → ∞) **if and only if** G(λ)/λ^α ∼ L(1/λ)/c_1(n,α) (λ → 0+), with
c_1(n,α) = 2^αΓ(α/2+1)Γ(n/2)/Γ((n−α)/2). The same ν, the same function, the same range as
§§ 1.2–1.5. So the derivation of § 1.2–1.4, and the referee's, was already a theorem of 2013; what
§ 1.3 adds to it is only the check that the paper's laws satisfy the monotone hypothesis.

**(iii) Theorem 3 (p. 9) removes the restriction.** *"For some values of α it is even possible to
obtain similar results without assumptions about ultimately decreasing behaviour of covariance
functions. In Olenko 1991 and Leonenko 1999 it was shown that:* **Theorem 3.** *For 0 < α < n the
statement (a) in Theorem 2 implies the statement (b). For 0 < α < (n−3)/2, n ≥ 4, the statement
(b) implies the statement (a)."* That is: for a rotation-invariant probability law on ℝ^n whose
characteristic function satisfies r^αB(r) ∼ L(r) at infinity, L slowly varying, **for every
0 < α < n and every n ≥ 1, with no monotonicity**,

G(λ) ∼ λ^αL(1/λ)/c_1(n,α) as λ → 0+.

And 1/c_1(n,α) = Γ((n−α)/2)/(2^αΓ(α/2+1)Γ(n/2)) = R(d,c)|S^{d−1}|/c at n = d, α = c. **This is the
first limit of clause (1) of Proposition 3.15, with its constant, in every dimension.** The answer
to the question "does the implication from the transform at infinity to the ball at zero hold for
every 0 < α < n with no monotonicity condition" is yes, as stated on the page. No proof is printed;
it is cited. (The converse fails above (n−3)/2: Example 5, p. 13, n = 3, α = 2,
B(r) = 2(1 − cos(ar))/r².)

**(iv) Theorem 4 (p. 9) is the density.** *"Suppose that there exists an isotropic spectral density
g(λ), λ ∈ [0,∞), such that g(λ) is decreasing for all λ ∈ (0, ε], ε > 0. Then for 0 < α < n the
statement (a) in Theorem 3 implies (b′)* λ^{n−α}g(λ) ∼ L(1/λ)/c_2(n,α), λ → 0, *where*
c_2(n,α) := 2^απ^{n/2}Γ(α/2)/Γ((n−α)/2)" (*"follows from Theorem 3, see more general Theorem 7 in
Olenko 2005"*). 1/c_2(n,α) = R(n,α). **This is the second limit of clause (1):**
q(s) ∼ R(d,c)s^{c−d}L(1/s) = R(d,c)s^{−d}μ̂(e/s)(1+o(1)), under the hypothesis that the density is
monotone near the origin, which is the hypothesis the paper uses (through Watanabe). Remark 2:
c_2(1,α) = 2Γ(α)cos(απ/2), so 1/c_2(1,c) is the R(1,c) = 1/(2Γ(c)cos(cπ/2)) that the paper prints.
The constants were checked on 27 pairs (n,α) to 18 digits, and Theorem 3 numerically at three
Matérn laws with α ≤ (n−3)/2 (block H).

And **Example 3 (p. 10) is the paper's worked example**: the "Bessel covariance function"
B(r) = (1+r²)^{−κ/2}, called there *"the characteristic function of the multivariate Bessel
distribution"*, with spectral density (8) equal to Aronszajn–Smith's G_κ (block H), checked against
(b′) of Theorem 4 by the behaviour of K_ν at zero. That is the Matérn kernel of the isotropic paper
checked against clause (1), at κ < n.

**(v) What is in print now, and what is not.**

| part of Proposition 3.15 | in print? |
|---|---|
| clause (1), the ball, every d ≥ 1, every 0 < c < d | **Yes.** Leonenko–Olenko, Theorem 3 (from Olenko 1991, Leonenko 1999), for any rotation-invariant probability law with a regularly varying transform. For (d−3)/2 < c < d also their Theorem 2, as an equivalence |
| clause (1), the density | **Yes.** Their Theorem 4 (Olenko 2005, Theorem 7), for a density monotone near the origin |
| d ≥ 4 with c ≤ (d−3)/2 | **Yes**, by Theorem 3. The sliver of § 1.5 is closed |
| that the hypotheses hold for every law of the class | each in print: the transform varies regularly with index −c (Grzywny–Ryznar–Trojan, Theorem 3.5; the paper's Lemma A.3(2)); the density is radially nonincreasing (Watanabe). The combination, "for the class", is stated nowhere read; it is two citations |
| clause (2), c = d, the ball and the density asymptotic to the truncated integral | **Not in the survey** (p. 9 mentions α > n, by Inoue–Kikuchi 1999, "with additional terms"; α = n is not mentioned). It follows from Bingham–Inoue's Theorem 1.1 and (1.4) by the inversion formula (4), as in § 1.4, in every d ≥ 1; that corollary is not stated in anything read |
| the lower bound I(s) ≥ \|S^{d−1}\|e^{−13d/4−2C_k}log(1/s) | not in print; the paper's (Lemma A.3(1)), with Trabs and Sato–Yamazato behind it on the line |
| a proof on the page | the survey gives none for Theorems 3 and 4. The paper's proof is one; so is Cygan–Grzywny–Trojan's for the potential measure |

**The sentence the sources now support.** *Known:* for a rotation-invariant probability law on ℝ^d
whose characteristic function varies regularly at infinity with index −c, 0 < c < d, the mass of
the ball of radius s is asymptotic to R(d,c)|S^{d−1}|c^{−1} times the transform at 1/s, and, when
the density is monotone near the centre, the density to R(d,c)s^{−d} times it (Olenko 1991;
Leonenko 1999; Olenko 2005; as stated in Leonenko–Olenko 2013, Theorems 3 and 4; for
(d−3)/2 < c < d already from Bingham 1972 and Ridenhour–Soni 1974 through the inversion formula).
For the Bessel kernels this is Aronszajn–Smith 1961. *What the paper does:* it observes that every
rotation-invariant self-decomposable law with no Gaussian part and 0 < c < d satisfies the two
hypotheses (both known), so that the theorem applies to the whole class; it adds the boundary case
c = d, which follows from Bingham and Inoue's theorem, with an explicit logarithmic lower bound;
and it gives a self-contained, machine-checked proof of both clauses. **Nothing in clause (1) is
new, in any dimension.**

**(vi) Who is credited, and what a primary citation needs.** Theorem 3: *"Olenko 1991 and Leonenko
1999"*, that is A. Olenko's Kyiv dissertation and N. N. Leonenko, *Limit theorems for random
fields with singular spectrum* (Kluwer, 1999). Theorem 4: Olenko, *Tauberian theorems for random
fields with the OR asymptotics I*, Theory Probab. Math. Statist. 73 (2005), Theorem 7. Yadrenko
(1983) is cited for the averaged functionals and "special cases" only. None of these is held. To
cite a source with a proof, Leonenko's book (or Leonenko–Olenko, Ukrainian Math. J. 43 (1991),
1652–1664, and Olenko, Ukrainian Math. J. 48 (1996), 368–383) and Olenko 2005 would have to be
acquired. Until then the honest citation is the survey, by theorem number, as a statement cited
there without proof.

---

## 2. The Bessel potentials — CONFIRMED

`READING-aronszajn1961theory.md`. At the image, pp. 416–417:

- (4,1): G_α(x) = K_{(n−α)/2}(|x|)|x|^{(α−n)/2}/(2^{(n+α−2)/2}π^{n/2}Γ(α/2)), α > 0.
- (4,2), as x → 0: G_α(x) ∼ Γ((n−α)/2)/(2^απ^{n/2}Γ(α/2))·|x|^{α−n} if α < n;
  G_n(x) ∼ log(1/|x|)/(2^{n−1}π^{n/2}Γ(n/2)); G_α(x) ∼ Γ((α−n)/2)/(2^nπ^{n/2}Γ(α/2)) if α > n. The
  sign ∼ is the quotient tending to 1 (footnote 21, p. 415).
- (4,6): Ĝ_α(ξ) = (2π)^{−n/2}(1+|ξ|²)^{−α/2} for α > 0, with (4,6′) ∫G_α = 1: in the paper's
  convention the characteristic function of G_α is (1+|ξ|²)^{−α/2}.

**The identification.** If X has density G_{2γ} on ℝ^d then X/√2 has transform (1+|ξ|²/2)^{−γ},
the paper's Matérn kernel, and density p(x) = 2^{d/2}G_{2γ}(√2x). Substituting (4,1) gives
2/((2π)^{d/2}Γ(γ))·(|x|/√2)^{γ−d/2}K_{γ−d/2}(√2|x|), the paper's (3.7). **The same function**
(block E, six cases to 18 digits).

**The same three regimes, with the same constants** (block E):

| regime | (4,2) rescaled by p(x) = 2^{d/2}G_{2γ}(√2x) | the paper, pp. 24–25 |
|---|---|---|
| γ < d/2 | 2^{−γ}π^{−d/2}Γ(d/2−γ)Γ(γ)^{−1}\|x\|^{2γ−d} | the same |
| γ = d/2 | 2(2π)^{−d/2}Γ(d/2)^{−1}log(1/\|x\|) | the same |
| γ > d/2 | p(0) = Γ(γ−d/2)/((2π)^{d/2}Γ(γ)) | bounded; the value is not printed in the paper (1.18034 at d = 1, γ = 3/4, the referee's number) |

The constant in the first row of (4,2) is R(n,α): Aronszajn and Smith's display is
G_α(x) ∼ R(n,α)|x|^{α−n}.

**What the paper cites now.** For the closed form: Fischer et al. 2025, (24) and the display after
it, p. 241 (`03-isotropic.tex:971`), with Matérn 1960, Stein, Guttorp–Gneiting and Porcu et al. for
the covariance and its parameter range (`01-introduction.tex:167–168`, `03-isotropic.tex:978–980`).
For the behaviour at 0: Abramowitz–Stegun 9.6.6, 9.6.8, 9.6.9 (`03-isotropic.tex:1071`), with the
constants computed in the prose. None of these states the three regimes of the density at its
centre with their constants; Aronszajn–Smith does, in one display, for every dimension, and it is
the oldest of them.

**Where Aronszajn–Smith must be added.**
1. § 3.3, the worked example (`03-isotropic.tex:1070–1080`): the three regimes are (4,2), cited as
   such; Abramowitz–Stegun can stay as the source of the Bessel asymptotics, and "computations of
   the prose" becomes a check of a printed formula.
2. § 3.3, at (3.7) (`03-isotropic.tex:960–982`): the kernel is the Bessel kernel G_{2γ} at range
   1/√2 ((4,1) with (4,6)), for every γ > 0. The sentence "For γ ≤ d/2 the kernel keeps the name
   here, and its density is not a Matérn covariance" should say that it is the classical Bessel
   kernel.
3. Table 3, the threshold row and the rate row (§ 5).
4. § 1, "Prior work: the kernel at its centre", one clause; and the abstract's "the Matérn family
   extended to every γ > 0" can stand, since § 1 will name the Bessel kernels.

---

## 3. The heat-kernel sentences — CONFIRMED

The sentences: "the literature on ℝ^d does not study one law" (`03-isotropic.tex:816–817`, p. 22);
"In ℝ^d the neighbouring results are not about one kernel … a limit τ → 0 says nothing about one
kernel" (`01-introduction.tex:288–293`, p. 4; `03-isotropic.tex:822–823`). The sibling record
(`VERIFY-round1-claims-and-trust-base.md` § 3) confirms the finding on the paper's own evidence;
here it is checked at the sources.

- **Grzywny–Ryznar–Trojan, Example 3** (pp. 63–64 of the published text, read again at the image).
  p. 63: *"there is t_1 > d/α such that for all t ≥ t_1 and x ∈ ℝ^d,*
  p(t,x) ≍ min{t^{−d/α}, t|x|^{−d−α}}"; p. 64: *"Hence, for t < t_1,"* the three-case display, with
  p(t,x) ≍ t(log(2|x|^{−α}) + |x|^{αt−d}) for |x| < 1 and t ∈ (0, d/α], and
  *"p(t,0) ≍ t^{1−d/α}/(t − d/α) for t > d/α; ∞ for t ∈ (0, d/α]"*. Both regimes of time are
  covered: **an estimate at every t, hence for each law of the family.** The referee is right. Their
  Proposition 5.3 and Theorem 5.4 (all t > 0) are also statements about each law
  (`READING-grzywny2019asymptotic.md` § 4).
- **Cho–Kang–Kim** (`READING-cho2021estimates.md`, arXiv v2): Proposition 2.3 (p. 10), two times
  T_1 ≤ T_2 with p(t,0) = ∞ for t ≤ T_1 and finite for t > T_2; Corollary 2.13 (p. 16), two-sided
  bounds on (0,T] for every T, with unidentified exponents. Bounded-time comparison, as the referee
  says: about each law, without the sharp power.
- **Cygan–Grzywny–Trojan** (`READING-cygan2017asymptotic.md`): every theorem on the density assumes
  ψ regularly varying with index α ∈ (0,2) (Theorems 4–7) and is a joint limit with
  tψ(1/|x|) → 0; p. 3: *"The corresponding results for the case α = 0 is the subject of the
  forthcoming paper [13]"*. A law of the paper with finite c has an exponent of index 0. **Mimica**
  (`READING-mimica2016heat.md`): positive lower scaling in every theorem. The referee's sentence
  about both is right. (But see § 1.7: the same paper of Cygan, Grzywny and Trojan has the
  fixed-object asymptotics for the potential measure.)
- Also about one law: Knopova–Schilling's Lemma 2.6 (a single time), Mimica's remark at t = 1, and
  the sources the paper's own Table 3 cites "at every τ".

**Verdict.** "The literature does not study one law" is **false**, and contradicted by Table 3
itself. "A limit τ → 0 says nothing about one kernel" is true of a limit taken alone and
**misleading as a summary**: the theorem in question (Grzywny–Ryznar–Trojan, Theorem 3.9) is the
linearization in τ of the proposition along the semigroup (the memo, § 6.3), and the same paper has
the small-time two-sided bound.

**An accurate wording** (proposed, not applied), for both places:

```latex
In $\RR^d$ most of the neighbouring results are organized by time. With a law of exponent $F$ the
literature studies the laws with the transforms $e^{-\tau F}$, $\tau > 0$, the laws at the times
$\tau$ of a \Levy{} process. The kernel is the law at $\tau = 1$, and the law at time $\tau$ has
the power $\tau c$ in place of $c$. A result for all $\tau$ is a result for every kernel, a result
for small $\tau$ is one for the kernels with a small $c$, and an asymptotic formula in the limit
$\tau \to 0$ does not give the asymptotic at $\tau = 1$.
```

---

## 4. Strictness of the filtration and the map φ ↦ F — CONFIRMED, and stronger than the referee states

The referee (§ 6, "Dimension dependence"; required change 13): *"the fact that Gneiting's witnesses
vanish does not make the classical dimension literature irrelevant: characteristic functions can
generate self-decomposable exponents through* F(r) = ∫_0^r[1 − φ(u)]du/u", without claiming that
the strict chain is in print.

### 4.1 The map is right, and it is a bijection onto the exponents with finite c

Let Φ_d be the class of radial characteristic functions on ℝ^d (Schoenberg's 𝔓(E_d), Gneiting's
Φ_d): φ(r) = ∫_{[0,∞)}Ω_d(ru)σ(du) for a probability measure σ, the law of the radius. Write Φ_d°
for those whose σ has no atom at 0 and a finite logarithmic moment ∫log⁺u σ(du) < ∞.

**Claim.** For c ∈ (0,∞) and φ ∈ Φ_d°, F(r) := c∫_0^r[1 − φ(u)]du/u is in 𝒜_d, with Gaussian
coefficient 0 and polar profile k_d(r) = cσ((r,∞)), so k_d(0+) = c. Conversely every F ∈ 𝒜_d with
Gaussian coefficient 0 and 0 < k_d(0+) = c < ∞ is of this form, with φ(r) = 1 − rF′(r)/c.

*Proof.* § 1.3(v), read with ϖ = cσ: the identity tF′(t) = ∫(1 − Ω_d(ts))ϖ(ds) is
tF′(t) = c[1 − φ(t)]. The conditions on σ are those on the profile: no atom at 0 is
ϖ((0,∞)) = k_d(0+); the logarithmic moment is ∫_1^∞ k_d(r)dr/r < ∞; and ∫_0^1 rk_d(r)dr ≤ c/2. ∎

**It is in print**, for every self-decomposable law, as the representation by the background
driving Lévy process: Sato, Theorem 17.5, pp. 108–109 (p. 109 at the image): a self-decomposable
μ has μ̂(z) = exp∫_0^∞ ψ(e^{−cs}z)ds (17.12) for a unique Lévy exponent ψ with the logarithmic
moment (17.11), and the Lévy measure ρ of ψ is ρ(B) = −c∫_Sλ(dξ)∫_0^∞1_B(rξ)dk_ξ(r) (17.16):
minus the differential of the profile along each ray. A finite profile is a compound Poisson
driver, whose exponent is (jump rate)·(1 − φ) with φ the characteristic function of the jump. So
the referee's "which φ, which class" is: **φ the characteristic function of the jump law of the
driving compound Poisson process, any rotation-invariant law on ℝ^d with no atom at the origin and
a finite logarithmic moment; the class reached is exactly the exponents in 𝒜_d with no Gaussian
part and a finite profile at the origin.**

### 4.2 The map carries the strict inclusions

**Claim.** For φ ∈ Φ_d° and c > 0: F_φ ∈ 𝒜_{d+1} if and only if φ ∈ Φ_{d+1}.

*Proof.* "If": the radius of the projection to ℝ^d of a rotation-invariant law on ℝ^{d+1} has an
atom at 0, or an infinite logarithmic moment, exactly when the radius in ℝ^{d+1} has; so φ is in
Φ_{d+1}°, and § 4.1 in dimension d+1 applies. "Only if": let F_φ ∈ 𝒜_{d+1} with datum (a′, k′).
Since rF_φ′(r) = c[1 − φ(r)] ≤ 2c, F_φ(r) = O(log r), so a′ = 0; and by § 1.3(v) in dimension
d+1, with ϖ′ the measure of k′, F_φ(r) ≥ H_{d+1}(rδ)ϖ′((δ,∞)) for every δ > 0 with
H_{d+1}(x) ∼ log x, so ϖ′ is finite. (Both are also the paper's Corollary 3.13: a and c are read
off the exponent and do not depend on the dimension.) Then c[1 − φ(r)] = rF_φ′(r) = c′[1 − φ′(r)]
with φ′ ∈ Φ_{d+1} the transform of ϖ′/c′. The Cesàro means R^{−1}∫_0^R of φ and of φ′ tend to 0
as R → ∞, because the radial laws σ and ϖ′/c′ have no atom at 0 (for d ≥ 2 the functions
themselves tend to 0). So c′ = c and φ = φ′ ∈ Φ_{d+1}. ∎

**Corollary.** Every φ ∈ Φ_d° ∖ Φ_{d+1} gives F_φ ∈ 𝒜_d ∖ 𝒜_{d+1}. Two classical witnesses:

- **Gneiting's Euclid's hat h_d** (`READING-gneiting1999radial.md` § 2, his p. 94 read there at the
  image: *"h_n(t) belongs to the class Φ_n, but not to Φ_{n+1} or any higher class"*). Its law has
  the density (15), proportional to J²_{d/2}(|x|/2)/|x|^d: no atom, and a radial density of order
  r^{−2} at infinity, so a finite logarithmic moment. Hence
  F(r) = ∫_0^r[1 − h_d(u)]du/u ∈ 𝒜_d ∖ 𝒜_{d+1} for every d ≥ 1. At d = 1, h_1(t) = (1−t)_+ and
  F(r) = r for r ≤ 1, 1 + log r for r ≥ 1 (block F: (1−t)_+ is in Φ_1 and its plane Hankel
  transform is negative at s = 6).
- **Schoenberg's Ω_d itself**, the transform of the uniform law on a sphere of ℝ^d (σ = δ_τ). By
  Schoenberg's Theorem 1 every member of Φ_{d+1} is a mixture of dilates of Ω_{d+1}, so it is
  bounded below by inf Ω_{d+1}, and inf Ω_d < inf Ω_{d+1} (−1, −0.4028, −0.2172, −0.1323, …;
  block F). So Ω_d ∈ Φ_d° ∖ Φ_{d+1}, and F(r) = c∫_0^r[1 − Ω_d(τu)]du/u, **the exponent with the
  step profile k_d = c·1_{(0,τ)}**, is in 𝒜_d ∖ 𝒜_{d+1}. This is the referee's short projection
  proof, read through the map. (Whether that proof is correct as the referee writes it is another
  agent's; the statement it proves is confirmed here by this second route.)

So: **the strict chain 𝒜_d ⊋ 𝒜_{d+1} at every d follows in a few lines from the strictness of
Schoenberg's chain, by a representation that is in Sato's book.** The answer to "does it carry
Gneiting's or Schoenberg's strict inclusions?" is yes.

### 4.3 What this does to the paper's sentences

- `01-introduction.tex:307–309` (p. 4): *"Neither author treats the self-decomposable laws in a
  fixed dimension, and Gneiting's separating functions cannot serve here: they vanish outside a
  ball, so none of them is of the form e^{−F}."* The premise is true and the conclusion is
  **wrong**: they serve as φ, not as e^{−F}. The earlier records made the same inference
  (`READING-gneiting1999radial.md` § 4: "strictness of the Φ_n chain does not pass to a subclass";
  `PRIOR-ART-novelty-claims.md`, first row). It does pass, through § 4.1.
- **"The steps from 𝒜_3 on are new"** (contributions, item 2; the abstract's "the strict decrease
  from dimension three on"; § 4). The statement 𝒜_d ⊋ 𝒜_{d+1} for the paper's classes was not
  found in print: the classes were introduced in the cone paper, and no source read names them. But
  it is a short corollary of a result of 1999 (or of Schoenberg's Theorem 1), by a standard
  representation. **A referee who knows § 4.1 will not accept "new" for it.** The claim is at risk
  in exactly the sense in which the rate is.
- What is the paper's own in Theorem 3.19 and Lemmas A.4, A.5: the one-parameter separating family
  taken from the cone paper, its critical values w_d, their strict decrease and exact order
  d^{−1/2} (and, by the referee's remark, √d·w_d → √π). None of that follows from the map.
- **Outside this shard, but a consequence of the same map and owed to the author:** a Cin ray on
  the line has the step profile, so φ = cos(τ·) = Ω_1(τ·), and by § 4.2 it lies in 𝒜_2 if and only
  if cos is a radial characteristic function on the plane, which it is not (−1 < inf J_0 = −0.4028;
  block F). So **Theorem 3.20, the third statement the paper lists as new, is the case d = 1 of the
  second witness above.** It should be re-tiered with the strictness, by whoever verifies that
  part of the review.

---

## 5. Table 3, row by row

| row (p. 21) | the referee | after §§ 1–4 |
|---|---|---|
| Theorem 3.12, the threshold | *"Broadly fair about known ingredients; incomplete without Bessel potentials, and the boundary needs the lower bound on the slowly varying factor."* | **Stands.** The Bessel kernels are a family with the threshold and its boundary case in print in every dimension, 58 years before the geometric stable example. The "here" cell names Feller's observation but not the lower bound on the transform (Lemma A.3(1)), on which the boundary case rests |
| Corollary 3.13 | *"Appropriately not counted as new …"* | **Stands.** No change. (For d ≥ 2 and finite c, clause (2) also follows from tF′(t) → c, § 1.3(v); not needed in the table) |
| Proposition 3.14, the shape | *"Correctly identified as known; distinguish Watanabe's characterization from this particular consequence and retain the no-atom argument."* | **Stands**, a matter of wording: Watanabe's proposition is an equivalence for a larger class; the cell may say "one direction of" |
| Proposition 3.15, the rate | *"Materially incomplete because it omits both exact Bessel-kernel asymptotics and the general Hankel antecedent."* | **Stands, and a third omission is added**: Cygan–Grzywny–Trojan's Theorems 8–9 and Corollaries 3–4. "New for d ≥ 2 as far as the author has found" must go. **[2nd pass] And a fourth, which decides the row:** Leonenko–Olenko's Theorems 3 and 4 state clause (1) for every rotation-invariant law, every d, every c < d (§ 1.9). The "here" cell can claim the boundary clause only |
| Proposition 3.16, from below | *"A useful explicit radius and constant may be an addition; I located no exact predecessor for these particular constants."* | **Stands.** Nothing read has an explicit radius or constant. The power c − d is now also a consequence of the rate, and so of the Hankel theorems for c > (d−3)/2, without radius or constant; for the Bessel kernels it is Aronszajn–Smith, p. 418 |
| Proposition 3.17, from above | *"Properly linked …; its status is principally an explicit consequence, and the full constant should be displayed."* | **Stands** (the constant is another agent's item) |

**The corrected cells** (proposed, not applied; the paper's macros; `bingham1997abel`,
`aronszajn1961theory`, `cygan2017asymptotic` are in the library and not yet in
`paper-iso/references.bib`).

Threshold row, the cell "in ℝ^d, in print": the last sentence becomes

```latex
  The threshold with its boundary case for two families: the Bessel kernels, which are the
  \Matern{} kernels of this paper (\sscite{aronszajn1961theory}, (4,2), p.~416), and the geometric
  stable laws, of exponents $\tau\log(1 + |\xi|^\alpha)$
  (\sscite{grzywny2019asymptotic}, Example~3). &
  For the class, with $c = d$ on the unbounded side, from these, an observation of Feller
  (Lemma~\ref{lem:positive-transform-origin}) and a lower bound on the transform
  (Lemma~\ref{lem:isotropic-exponent-log}(1)). Not found stated. \\
```

Rate row, in full. **[2nd pass] This is the row to use** (`leonenko2013tauberian` is in the library
and not yet in `paper-iso/references.bib`; its theorem numbers are those of the arXiv version):

```latex
Prop.~\ref{prop:origin-rate-d}, the rate &
  \sscite{sato1978distribution}, Thm.~1.7, p.~277; \sscite{sato1999levy}, Thm.~53.8,
  pp.~410--411. &
  Clause (1), for every rotation-invariant law whose transform varies regularly with index $-c$,
  $0 < c < d$: the mass of a ball, and the density when it is monotone near the centre, with these
  constants (Olenko and Leonenko, as stated in \sscite{leonenko2013tauberian}, Thms.~3 and~4; for
  $c > (d-3)/2$ also from the Abel--Tauber theorem for Hankel transforms,
  \sscite{bingham1997abel}, Thm.~1.2, as Thm.~2 there). For the Bessel kernels, which are the
  \Matern{} kernels, with the logarithm at $c = d$ (\sscite{aronszajn1961theory}, (4,2), p.~416).
  The same argument for the potential measure of a \Levy{} process
  (\sscite{cygan2017asymptotic}, Thms.~8, 9 of the arXiv version). For the laws at time $\tau$:
  in the limit $\tau \to 0$ and, up to constants, for small $\tau$
  (\sscite{grzywny2019asymptotic}, Thms.~3.9 and~5.7). &
  Clause (1) is known: the class satisfies its hypotheses (Lemma~\ref{lem:isotropic-exponent-log};
  Proposition~\ref{prop:isotropic-radial-monotone}). Clause (2), the case $c = d$ with its lower
  bound, follows from \sscite{bingham1997abel}, Thm.~1.1, and was not found stated. A proof of
  both is given. \\
```

The first-pass row, kept for the record and **superseded**:

```latex
Prop.~\ref{prop:origin-rate-d}, the rate &
  \sscite{sato1978distribution}, Thm.~1.7, p.~277; \sscite{sato1999levy}, Thm.~53.8,
  pp.~410--411. &
  For the Bessel kernels, with the constant, the logarithm at $c = d$ and the value at the centre
  for $c > d$ (\sscite{aronszajn1961theory}, (4,2), p.~416). For the mass of a ball when
  $c > (d-3)/2$, so for every $c$ when $d \le 3$: from the Abel--Tauber theorem for Hankel
  transforms of Bingham and of Ridenhour and Soni, and at $c = d$ from its boundary case
  (\sscite{bingham1997abel}, Thms.~1.2 and~1.1 of the preprint), applied to
  $t^{(d-3)/2}\,\widehat\mu(te)$; the density then follows from its monotonicity. The same
  asymptotics and constants for the potential measure of a \Levy{} process
  (\sscite{cygan2017asymptotic}, Thms.~8, 9, Cor.~3, 4 of the arXiv version). For the laws at time
  $\tau$: in the limit $\tau \to 0$ (\sscite{grzywny2019asymptotic}, Thm.~3.9), and up to
  constants for small $\tau$ (Thm.~5.7 there) and, for the geometric stable laws, at every $\tau$
  (Example~3 there). &
  For the class, the ball and the density, every $d$ and every $c \le d$ by one proof, with an
  explicit lower bound at $c = d$. Not found stated for the class. Not covered by the Hankel
  theorem: $d \ge 4$, $c \le (d-3)/2$. \\
```

Lower-bound row, the cell "in ℝ^d, in print", one sentence added at the end:

```latex
  For the Bessel kernels, two-sided at the power $c - d$ (\sscite{aronszajn1961theory}, p.~418).
```

The caption's "``Not found'' refers to the sources cited in this paper" stays true.

The table gains about ten lines of small type, on a float page that is full; the sibling record's
balance (`VERIFY-round1-claims-and-trust-base.md` § 8) has to carry it.

---

## 6. What the paper can still claim

For each of the four, the strongest claim the sources read now support.

### 6.1 The rate (Proposition 3.15)

**[2nd pass] This subsection is rewritten at its head; the first-pass text follows it and is
superseded where the two differ.**

**Supported now.** Clause (1): "known". It is a theorem about rotation-invariant laws with a
regularly varying transform (Leonenko–Olenko 2013, Theorems 3 and 4, from Olenko 1991, Leonenko
1999 and Olenko 2005), for the ball and for the density, in every dimension and for every
0 < c < d, with the paper's constants; the paper's laws satisfy its hypotheses by results that are
also known. Not even "not found stated for the class" is a claim worth printing for it: the class
enters through two citations. Clause (2), the boundary c = d: "follows from Bingham and Inoue's
theorem; not found stated; with an explicit logarithmic lower bound", second tier. The proof:
"self-contained and machine-checked". **Is anything of Proposition 3.15 left that is not in
print?** The density form: no (Theorem 4). d ≥ 4 with small c: no (Theorem 3). The boundary
asymptotic: as a statement yes, as mathematics it is a corollary. The boundary lower bound: yes,
the paper's. "For the class", i.e. Lemma A.3: clause (2) of the lemma is Grzywny–Ryznar–Trojan's
Theorem 3.5, as the paper already says; clause (1), the explicit lower bound on the transform, is
the paper's in ℝ^d.

*The abstract*, now. The rate drops out of the list of new results and needs no sentence of its
own beyond the one the abstract already has ("Otherwise a point source is recorded as a spike,
whose rate is given with its constant"), which stays true. Proposed, 60 words for the present 60,
so the abstract keeps its length:

```latex
The threshold and the rate are classical on the line. In $\RR^d$ the rate below the threshold is
a known Tauberian theorem, and the threshold follows from known results; it was not found stated
for the class. New, as far as the author has found, are the critical values of a family that
separates the dimensions, of exact order $d^{-1/2}$.
```

(The strict decrease and the Cin statement stay in the abstract as results, in its earlier
sentences, and leave the list of new ones: § 4.)

*The contributions.* The rate is no longer an item of either list. It goes to the sentence that
says what is not counted (`01-introduction.tex:384–387`), and the boundary clause to the second
list:

```latex
\item[5.] \emph{The rate at the threshold} (Proposition~\ref{prop:origin-rate-d}(2)). When
$c = d$ the density at distance $s$ from the centre is asymptotic to $(2\pi)^{-d}$ times the
integral of the transform over the frequencies up to $1/s$, which is at least an explicit
constant times $\log(1/s)$. The asymptotic follows from the boundary case of the Abel--Tauber
theorem for Hankel transforms \sscite{bingham1997abel}; for the \Matern{} kernels it is classical
\sscite{aronszajn1961theory}.
```

and, in the paragraph of what is not counted:

```latex
Not counted are the classification, which derives a known class of laws, the radially
nonincreasing density (Proposition~\ref{prop:isotropic-radial-monotone}), which is a result of
Watanabe, and the rate below the threshold (Proposition~\ref{prop:origin-rate-d}(1)). The last is
a Tauberian theorem for rotation-invariant laws whose transform varies regularly, known from the
theory of random fields, where the law is a spectral measure and its transform a covariance
function (\sscite{leonenko2013tauberian}, Thms.~3 and~4, after Olenko and Leonenko); on the line
it is Sato and Yamazato's \sscite{sato1978distribution}, and for the mass of a ball with
$c > (d-3)/2$ it goes back to Bingham and to Ridenhour and Soni \sscite{bingham1997abel}. The
kernels of this paper satisfy its hypotheses, and Appendix~\ref{app:isotropic-proofs} proves it
again, by the argument of Sato and Yamazato.
```

*§ 3.3* (`03-isotropic.tex:808–812`): "Of these statements the rate is new for d ≥ 2, as far as the
author has found: …" becomes "None of these statements is new in kind. The rate below the
threshold is a known theorem. The threshold with its boundary case, the rate at the threshold and
the two bounds with their constants are stated here for the class, from known results, and the
author has not found them stated." The paragraph after the proposition
(`03-isotropic.tex:1082–1092`) should lead with the attribution (Leonenko–Olenko's Theorems 3 and
4; the Hankel theorem; Aronszajn–Smith for the example, which is also their Example 3) and then
say whose argument the proof follows (Sato–Yamazato; Cygan–Grzywny–Trojan). The sentence there on
Bogdan–Grzywny–Ryznar's open case should go or be confined to *estimates of the semigroup*: with
the rate in print for one law, "the proposition treats that case at one kernel" reads as a claim.
*§ 4* (`04-conclusion.tex:114–118`): the list of new statements loses its first item.

**The first-pass text of this subsection** (before Leonenko–Olenko was read; superseded above in
its claim that the rate "moves to the second tier", in its abstract sentence and in its
contributions item):

**Supported:** "stated here for the class, for the ball and the density, in every dimension and for
every 0 < c ≤ d, with an explicit logarithmic lower bound at c = d; the author has not found it
stated for the class." **Not supported:** "new", in any dimension. In d = 2 and 3 it is a corollary
of printed theorems; in d ≥ 4 the uncovered cases c ≤ (d−3)/2 are a consequence of a method that is
in print in ℝ^d for another measure, and they are not a contribution to announce. The rate moves
from the first tier of the contributions to the second.

*The abstract* (`main.tex`; now: "The threshold is classical on the line. In ℝ^d its ingredients
are known, and it was not found stated for the class. Three results are new as far as the author
has found: the rate for d ≥ 2, the strict decrease from dimension three on, and that of the line's
building blocks only the Gaussian remains in the plane."). Proposed, 63 words for 60:

```latex
The threshold and the rate are classical on the line. In $\RR^d$ both follow from known theorems,
the rate for $c > (d-3)/2$ from Abel--Tauber theorems for Hankel transforms, and were not found
stated for the class. The strict decrease is inherited from Schoenberg's chain; new, as far as the
author has found, are the critical values of a separating family, of exact order $d^{-1/2}$.
```

(If the statement on the Cin rays is to stay in the abstract it stays as a result, not in a list of
new ones: § 4.3, last item. The abstract is at its limit of 250 words; three words are owed.)

*The contributions item* (`01-introduction.tex:353–360`), moved to the second list, which then has
three items:

```latex
\item[3.] \emph{The rate of a kernel at its centre} (Proposition~\ref{prop:origin-rate-d}). When
$c < d$ the density at distance $s$ from the centre is asymptotic to an explicit constant times
$s^{-d}$ times the transform at the frequency $1/s$, and when $c = d$ to a truncated integral of
the transform, which grows at least like $\log(1/s)$. On the line this is a theorem of Sato and
Yamazato \sscite{sato1978distribution}. For the \Matern{} kernels it is the classical behaviour of
the Bessel kernels \sscite{aronszajn1961theory}. For the mass of a ball it follows, when
$c > (d-3)/2$ and so for every $c$ in the plane and in space, from the Abel--Tauber theorem for
Hankel transforms of Bingham and of Ridenhour and Soni, with its boundary case
\sscite{bingham1997abel}, and the density follows since it is radially nonincreasing. The proof
given here is the Tauberian argument of Sato and Yamazato, which Cygan, Grzywny and Trojan use in
$\RR^d$ for the potential measure \sscite{cygan2017asymptotic}; it needs no condition on $c$.
```

*§ 3.3* (`03-isotropic.tex:808–812`): "Of these statements the rate is new for d ≥ 2, as far as the
author has found: an asymptotic equivalence with its constant, at one kernel, for the whole class."
becomes "None of these statements is new in kind. The threshold with its boundary case, the rate
and the two bounds with their constants are stated here for the class, from known theorems, and the
author has not found them stated." *§ 4* (`04-conclusion.tex:114–118`) likewise. The paragraph after
the proposition (`03-isotropic.tex:1082–1092`) gains the Hankel theorem and Cygan–Grzywny–Trojan
beside Sato–Yamazato, and loses nothing.

### 6.2 The threshold (Theorem 3.12)

**Supported, unchanged in tier:** "for the class, with the boundary c = d on the unbounded side,
from known ingredients; not found stated." To add: the Bessel kernels as a second family, and the
older one, for which the threshold with its boundary is in print (Aronszajn–Smith, (4,2)); and the
lower bound on the transform among the ingredients. Nothing read states the threshold for the
class. The referee's caution stands that "not found stated" reports a bounded search.

### 6.3 The bounds (Propositions 3.16, 3.17)

**Supported, unchanged:** an explicit radius and constant for the lower bound, the form for the
measure, and the upper bound at every radius with its constant; not found stated. No source read
here has a constant or a radius. The power c − d is no longer something the paper is first to have
at a fixed law in d = 2, 3: it follows from the Hankel theorems through the rate. So the bounds'
claim is the constants and the radius, as the paper already says.

### 6.4 The strict filtration (Theorem 3.19)

**Supported:** "the critical values of the separating family decrease strictly and are of exact
order d^{−1/2}" as the contribution, and "the chain 𝒜_d is strict at every step" as a statement
that follows from the classical chain. **Not supported:** "the steps from 𝒜_3 on are new", and the
sentence that Gneiting's functions cannot serve.

*§ 1, "Prior work: the dimension filtration"*, in place of the sentence at
`01-introduction.tex:307–309`:

```latex
Neither author treats the self-decomposable laws, but their chain reaches them. A rotation-invariant
law on $\RR^d$ with no atom at the origin and a finite logarithmic moment, of characteristic
function $\varphi(|\xi|)$, gives the exponent $F(r) = c\int_0^r (1 - \varphi(u))\,du/u$ in
$\mathcal{A}_d$, by the representation of a self-decomposable law through its driving \Levy{}
process (\sscite{sato1999levy}, Thm.~17.5, pp.~108--109), and every exponent of $\mathcal{A}_d$ with
no Gaussian part and a finite $c$ arises so. Since $c$ is read off $F$
(Corollary~\ref{cor:origin-profile-exponent}), $F$ lies in $\mathcal{A}_{d+1}$ only if $\varphi$
is a characteristic function on $\RR^{d+1}$. So Gneiting's separating functions give
$\mathcal{A}_d \ne \mathcal{A}_{d+1}$ for every $d$.
```

*The contributions item* (`01-introduction.tex:361–365`):

```latex
\item \emph{The critical values of the separating family}
(Lemmas~\ref{lem:threshold-monotone} and~\ref{lem:threshold-limit}). That the dimension filtration
is strict at every step (Theorem~\ref{thm:filtration-strict}) follows from the strictness of
Schoenberg's chain, as said above, and is not counted. What is added is quantitative: the
one-parameter family of the cone paper separates every pair of consecutive classes, at critical
values $w_d$ (Definition~\ref{def:filtration-thresholds}) that decrease strictly and are of exact
order $d^{-1/2}$.
```

(The limit √d·w_d → √π, the short projection proof and the place of the Cin theorem are the other
agent's items; the wording above leaves room for them.)

---

## 7. What could not be read

- **The published Bingham–Inoue** (*Trends in Probability and Related Analysis*, World Scientific
  1997, pp. 83–90). It would settle the theorem numbers and pages to print. The mathematics is in
  the preprint.
- **Bingham 1972** (J. London Math. Soc. (2) 5, 493–503), **Ridenhour–Soni 1974** (SIAM J. Math.
  Anal. 5, 809–821), **Soni–Soni 1975** (II and III, J. Math. Anal. Appl. 49). They would settle
  under which hypotheses Theorem 1.2 was first proved (is the monotonicity theirs, or a bounded
  variation condition; is the range of ρ the same), and so the exact attribution and date. *From a
  web search only, not a page citation:* SIAM's abstract of Ridenhour–Soni describes a Parseval
  relation for f with x^{ν+1/2}f locally integrable, of bounded variation on a tail and tending to
  zero, "applied to obtain Tauberian results for the Hankel transform"; a later paper of Soni and
  Soni describes Bingham 1972 as giving Abelian and Tauberian results for a transform of Hankel
  type with a slowly varying factor.
- **Bingham–Inoue, *The Drasin–Shea–Jordan theorem for Fourier and Hankel transforms*** (Quart. J.
  Math. 48 (1997)), whose § 2 discusses weakening the monotonicity; **Inoue 1995** (the sine and
  cosine cases of the boundary theorem); **Pitman 1968**. None would widen the range past ρ < 0.
- **[2nd pass] The random-field literature: read, in its survey; the primary sources are what is
  left.** Leonenko–Olenko 2013 is now held and read (§ 1.9; the item below is the first pass's and
  is kept for the record; its "recollection" is confirmed at the page: c_2(n,α) is the reciprocal
  of R(n,α), and c_1(n,α) of the ball constant). Still not held, and what each would settle:
  - **N. N. Leonenko, *Limit theorems for random fields with singular spectrum*** (Kluwer, 1999),
    and **A. Olenko's dissertation** (Kyiv, 1991): the survey's sources for Theorem 3. The book
    would give the statement with its exact hypotheses and a proof, and the section to cite. Also
    Leonenko–Olenko, Ukrainian Math. J. 43 (1991), 1652–1664, and Olenko, Ukrainian Math. J. 48
    (1996), 368–383.
  - **A. Olenko, *Tauberian theorems for random fields with the OR asymptotics I***, Theory Probab.
    Math. Statist. 73 (2005), 120–133: its Theorem 7, the source of the survey's Theorem 4 (the
    density). It would settle the exact monotonicity hypothesis ("decreasing" on (0, ε]).
  - **Inoue–Kikuchi**, *Abel–Tauber theorems for Hankel and Fourier transforms and a problem of
    Boas*, Hokkaido Math. J. 28 (1999), 577–596: named by the survey for α > n and, with Soni 1975
    and Bingham–Inoue, for "this case". It may state the boundary α = n for Hankel transforms in a
    form closer to clause (2) than Bingham–Inoue's Theorem 1.1; not known.
  - **The version of record** of the survey (Methodol. Comput. Appl. Probab. 15 (2013)): its
    theorem numbers and pages.
  - **Yadrenko, *Spectral theory of random fields*** (1983): cited by the survey for the averaged
    functionals and for special cases only; not needed for the rate.
  - The survey states Theorems 3 and 4 **without proof**. Their truth in the paper's direction is
    not in doubt here: the paper's own proof of Proposition 3.15(1) is a proof of both for a law
    with a monotone density, and the numerical checks agree. But a citation of a theorem "as
    stated in a survey" is weaker than a citation of its proof.
- **(First pass, superseded by the item above.) The random-field literature on Abelian and
  Tauberian theorems for isotropic spectral measures.** This was the lead most likely to change § 1
  again and it was not anticipated by the referee. A covariance function of a homogeneous isotropic random field on ℝ^n is the transform of
  its spectral measure, a finite rotation-invariant measure; theorems relating the covariance at
  infinity to the spectral measure of a small ball, or to a monotone spectral density, at zero are
  the statement of Proposition 3.15(1) with μ the normalized spectral measure. *From a web search
  only:* Leonenko and Olenko, *Tauberian and Abelian theorems for long-range dependent random
  fields* (Methodol. Comput. Appl. Probab. 15 (2013); arXiv:1307.1857), is described as a survey
  linking "the behaviour of covariance functions … at infinity to the behaviour of spectral
  densities at zero"; an earlier paper in Ukr. Math. J. with a similar title cites Bingham 1972.
  *From this reader's recollection, unverified:* that literature (Leonenko's book of 1999 among it)
  states the relation with the constant Γ((n−α)/2)/(2^απ^{n/2}Γ(α/2)), which is R(n,α), for
  0 < α < n. If so, clause (1) is in print for every dimension, as a theorem about isotropic
  spectral measures, and the sliver d ≥ 4, c ≤ (d−3)/2 of § 1.5 closes. **To be acquired through
  the librarian and read before the paper's wording on the rate is fixed.**
- **The version of record of Cygan–Grzywny–Trojan** (Trans. Amer. Math. Soc. 369 (2017)): the
  numbers of Theorems 8, 9 and Corollaries 3, 4.
- **Gneiting 1999, p. 94**, was not read again; § 4.2 rests on `READING-gneiting1999radial.md`,
  which read it at the image. Golubov's truncated powers are not held.
- **Aronszajn–Smith outside pp. 414–418**, and the standard later accounts of the Bessel kernels
  (Stein's *Singular Integrals*, Chapter V), which a referee might prefer as the citation.
- **The literatures the referee names and does not rule out** (generalized hyperbolic and type-G
  laws, Picard and Orey conditions, local Lévy densities): not read here either.
- Whether the short argument of § 4.2 is in print, in the literature on self-decomposable laws
  (Jurek–Vervaat 1983, Sato–Yamazato 1984, on the driving process) or on radial positive definite
  functions, was not searched. It is this record's derivation from two printed statements.

## 8. Confidence

- The transcriptions of §§ 1.1 and 2: high (page images; (1.4) and (4,2) also checked numerically).
- The reduction of § 1.2–1.4 and the range of § 1.5: high. Every step is elementary, the constants
  were checked symbolically and numerically, and the uncovered region was counter-checked.
- "Nothing read widens the range" (§ 1.6): high for what was read; the random-field literature of
  § 7 is the open flank.
- § 4.1–4.2: high for the map and for the step from Φ_d ∖ Φ_{d+1} to 𝒜_d ∖ 𝒜_{d+1}; it was derived
  here and not machine-checked. The witness h_d rests on the earlier reading of Gneiting's p. 94;
  the witness Ω_d rests on Schoenberg's Theorem 1 and a numerical comparison of infima for d ≤ 7
  (the strict increase for all d is the classical fact that Ω_{d+1} is a nondegenerate mixture of
  dilates of Ω_d).
- That the paper's lead claim on the rate must change: certain for d = 2, 3.

**[2nd pass]**

- The transcriptions of Leonenko–Olenko's Theorems 2, 3, 4 and of the dictionary: high (page
  images of pp. 3–10; the constants checked against the paper's on 27 pairs and at n = 1 against
  the two Remarks).
- That Theorem 3's first sentence carries no monotonicity hypothesis: high as a reading of the
  page (the sentence introducing it says so, and Theorem 2, which has the hypothesis, is stated
  separately for the equivalence). The primary sources were not read; if Leonenko's book states an
  extra condition that the survey dropped, § 1.9(v) changes for the cases c ≤ (d−3)/2 in d ≥ 4
  only, since the rest is covered by Theorem 2 and the Hankel theorem.
- "Nothing in clause (1) is new, in any dimension": high.
- "Clause (2) is not stated in a source read": high for the sources read; Inoue–Kikuchi 1999 is the
  place it might be.
- "Nothing read widens the range" (the first bullet list above) is superseded: Theorem 3 does, by
  another method than the Hankel theorem.
