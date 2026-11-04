# Verification of the external review, round 2: the mathematics (parts A to D)

**What this is.** Article-kit `PROCESS.md` § 9: every finding of an external review is verified
against the text, the blueprint, the Lean and the sources before anything changes. This record
verifies the findings of parts A (front), B (classification), C (centre) and D (dimension) of the
second round, `review-round2-iso-review-2-{A,B,C,D}-…-claude-fable.md`, that assert an error, a
gap or a mathematical improvement. The literature findings of parts A, C and E are another
record's. The tree is the tag `iso-review-2` with the reviews (branch `queue/q-0433`). Page
numbers are the printed pages of `paper-iso/main.pdf` (86 pages, byte-identical to
`review-build-iso-review-2.pdf`). Nothing but this file and the scripts named below was written:
no `.tex`, `.lean` or blueprint file was edited, no Lean was built, nothing was committed.

**Verdicts.** CONFIRMED: the referee is right. PARTLY: what holds is said. REFUTED: the paper is
right.

**Read for this record.** The four reports in full. The frozen PDF, rendered at pp. 37, 39 and 47
(image and text layer) and searched in its text layer for every quoted sentence. At the page
image, through the librarian (`library page <citekey> --printed N --format image`): the cone paper
(`fagerstrom2026cone`, v0.1) pp. 34, 38, 39, 61, 82; the time-causal paper
(`fagerstrom2026hemigroup`, v1.1.0) pp. 27, 28, 29, 33; Bondesson's monograph
(`bondesson1992generalized`) p. 30. In the text layer of a born-digital PDF: the cone paper
pp. 35–36 and 79, the time-causal paper pp. 42 and 63, the line paper (`fagerstrom2026spatial`)
for its trust base and its references. The
reading notes `READING-halgreen1979self.md`, `READING-bondesson1978infinite.md`,
`READING-cygan2017asymptotic.md`, `READING-daley2014dimension.md`,
`READING-sato1999levy-prop-15-5.md`. The Lean files named in the items, read and not built.

**Scripts** (`records/affine/reviews/verify-round2-scripts/`, each run, each passing its
assertions, output saved beside it as `<name>-output.txt`;
`uv run --no-project --with mpmath --with scipy python <file>`):

| script | items | what it checks |
|---|---|---|
| `item12_stage_compound_poisson.py` | 12 | the mass $c\log(\chi(t)/\chi(s))$ of a stage's Lévy measure ($d = 1, 2, 3$; Matérn, a logarithmic profile, a step); its exponent; the Matérn stage on the line as an explicit law (closed form at $\gamma = 1$, inverse transform at $\gamma = 3/4$, a simulation of the compound Poisson sum, the cascade identity at points); the transform of the smoothing part |
| `item13_step_exponent_dimensions.py` | 13 | $\Omega_d = \Omega_{d+2} + (t/d)\Omega_{d+2}'$ and the identity in dimension $d + 2$; the profile in dimension $d + 1$ (closed forms, positivity, its shadow, its exponent, its two derivations); the Mellin transform in dimension $D$; a certificate that the step exponent is not a Lévy exponent in dimension $d + 3$ ($d = 1, 2, 3$) |
| `items_11_14_constants.py` | 11, 14 | the two lower bounds on the transform; $B_c$ against the constant of Cygan, Grzywny and Trojan; the cone paper's inequality behind $4 \le w_2$ |

**Three things to know before the items.**

1. *Two of the "errors in a printed proof" are misreadings of the PDF.* B's R1 (item 1) and C's R1
   (item 10) quote words that the frozen PDF does not print: p. 37 has the factor
   $(1 \wedge x^2)$, and p. 47 says "the next paragraph". Both proofs stand as printed.
2. *D's two main findings hold, and both go further than D took them.* The stages (item 12): an
   atom exactly when there is no Gaussian part and $c$ is finite, a density in the two other
   cases, so "which stages have a density, and which an atom" is answered completely. The step
   witnesses (item 13): the exponent of the step datum of dimension $d$ is the exponent of an
   infinitely divisible law in dimension $D$ exactly for $D \le d + 2$. D called the last
   dimension "the genuinely open question". It is $d + 2$.
3. *A parenthesis of B is false and should not be carried into a response.* B writes that "a
   residual of the Matérn law is not even infinitely divisible in general". Every stage of an
   isotropic family is infinitely divisible: Sato's Prop. 15.5 (p. 93, read at the page,
   `READING-sato1999levy-prop-15-5.md`), the blueprint's `thm:cascade-infinitely-divisible`(4)
   (machine-checked, `AffineHemigroup.isotropic_family_infinitelyDivisible`), and item 12(1)
   below, which gives the triplet. What is true is that a stage is not self-decomposable when
   $a = 0$ and $c < \infty$.

---

## 1. B R1: the dominating function in the proof of Theorem 3.6 — REFUTED

**The paper.** `paper-iso/appendix-isotropic.tex:465–468`, p. 37, as printed (text layer of the
PDF, p. 37, and the page image): "on $0 \le r \le \Omega$ the integrand of (2.1) is at most
$\max\{2,\Omega^2/2\}\,(1 \wedge x^2)\,k(x)/x$, which is integrable by the two conditions on $k$".
The factor that B says is missing is there. The tag `iso-review-2` has the same line
(`git show iso-review-2:paper-iso/appendix-isotropic.tex`), and the phrase entered the file with
Q-0316 (`git log -S`).

**The mathematics.** $1 - \cos rx \le \min\{2, r^2x^2/2\} \le \max\{2,\Omega^2/2\}(1 \wedge x^2)$
for $0 \le r \le \Omega$, and $\int_0^\infty (1 \wedge x^2)k(x)\,dx/x = \int_0^1 xk + \int_1^\infty
k/x < \infty$. Correct as printed. B's own repair is the printed text.

**The blueprint.** `blueprint/src/parts/03-isotropic.tex:5936`, the same sentence, verbatim.

**The Lean.** `isotropic_classification` reads the continuity of the exponent from the shared
library: `P.continuous_exponent` (`Formalization/AffineHemigroup/IsotropicClassification.lean:115,
239–240`), which is `SpatialLine.SymLevyPair.continuous_exponent`
(`SpatialHemigroup/Formalization/SpatialLine/ExponentContinuity.lean:103`). Its dominating function
is `one_sub_cos_mul_le`: $1 - \cos(\omega x) \le 2\max(1, M^2)\min(1, x^2)$ for $|\omega| \le M$,
integrated against the Lévy measure by dominated convergence in $[0,\infty]$. The factor is there
too.

**Fix.** None. **Touches.** Nothing. **Disposition.** Decline: the finding quotes a text the paper
does not print.

## 2. B R2: "the definition of $\mathcal{A}_d$ in Definition 3.20" — CONFIRMED

**The paper.** `paper-iso/appendix-isotropic.tex:649–650`, p. 39, end of the proof of
Proposition 3.10(2): "With the definition of $\mathcal{A}_d$ in Definition 3.20 this is the
description of the class." In the paper $\mathcal{A}_d$ is defined in Proposition 2.6
(`02-line-papers.tex:303–306`, p. 10), and Definition 3.20 says "Let $\mathcal{S}$,
$\mathcal{A}_d$ and $\mathcal{A}_\infty$ be the subordinated slice and the classes of
Proposition 2.6" (`03-isotropic.tex:1403–1404`).

**Why it happened.** The sentence is the proof of record transcribed
(`blueprint/src/parts/03-isotropic.tex:6280–6281`). In the blueprint it is right: the blueprint
has no § 2, and its `def:filtration-thresholds` defines the classes (lines 2913–2918). The paper's
copy of that definition was edited to point to § 2 (Q-0428), and this reference was not.

**Fix.** In the paper's copy: "With the definition of $\mathcal{A}_d$ in
Proposition~\ref{prop:line-filtration} this is the description of the class."

**Touches.** Prose of the paper's copy of a shared proof: the marker of
`prop:isotropic-polar-reading` gains a proof pin (`linkage check --pin-shared`), as the other
deliberately edited copies have. No blueprint change (its sentence is correct there), no Lean.
**Disposition.** Fix.

## 3. B R3: the paragraph after Proposition 3.11 — (a) CONFIRMED, (b) PARTLY

**The paper.** `03-isotropic.tex:686–696`, p. 19: "The exponents $\gamma\log(1+\sigma)$ and
$\sigma^\alpha$ of clauses (2) and (3) are causally admissible, and the classification of the
time-causal paper supplies a family for every causally admissible exponent ([11], version 1.1.0,
Thm. 7.3 with Props. 8.8 and 8.5). The inverse-gamma laws of clause (4) are generalized gamma
convolutions (Bondesson [4], § 4, pp. 51–52), a class of self-decomposable laws on the half-line
(Halgreen [20], pp. 13–15), and so they are the delay laws of a time-causal family ([11],
Prop. 8.17, by its Thm. 7.3)."

**(a) The range of $\alpha$.** Read at the page images of the time-causal paper, v1.1.0.
Proposition 8.5 (p. 33): "For $0 < \alpha < 1$ the exponent $F(s) = s^\alpha$ is of the form
(7.1), with Lévy density factor $k(t) = \frac{\alpha}{\Gamma(1-\alpha)}t^{-\alpha}$, which is
nonincreasing." So it does not cover $\alpha = 1$, and clause (3) of Proposition 3.11 runs to
$\alpha = 1$. What covers $\alpha = 1$: the form (7.1) itself (p. 27),
$F(s) = b_0s + \int_0^\infty(1 - e^{-st})\frac{k(t)}{t}\,dt$, $b_0 \ge 0$, at $b_0 = 1$, $k = 0$,
so that Theorem 7.3 (p. 28) applies with no further proposition; and the paper says so in words,
Corollary 7.4 (p. 29): "$F(s) = s^\alpha$ for some $0 < \alpha \le 1$, i.e. the kernels are
exactly the extremal stable densities of [8], Thm. 2, together with the boundary case
$\alpha = 1$ — the pure delay $\mu_{0,x} = \delta_x$", with its proof ("The value $\alpha = 1$
gives $sF'(s) = s \in \mathrm{BF}$, so Lemma 7.1 admits it") and Remark 7.5 (p. 29): "Under
Definition 2.1 the delay family — and more generally the drift term $b_0s$ in (7.1), which shifts
every kernel by $b_0x$ — is admissible." In this paper's terms $\sigma$ is causally admissible by
Definition 2.4 at sight, and the family needs no theorem: $\mu^{\mathrm I}_{x,y} = \delta_{y-x}$.

**Fix (a).** "… (\[11\], version 1.1.0, Thm. 7.3 with Props. 8.8 and 8.5; at $\alpha = 1$ the
exponent $\sigma$ is the drift term of Definition 2.4, $b_0 = 1$ and $k_{\mathrm I} = 0$, and its
family is that of the pure delays $\delta_{y-x}$, Cor. 7.4 and Rem. 7.5 there)."

**(b) Who states what.** From the reading notes, each at the page image:

- Bondesson 1978, § 4, pp. 51–52: "In this section we shall show that the distribution of the
  inverse of a gamma variable is a generalized $\Gamma$-convolution", for every shape $\nu > 0$;
  the consequence drawn is infinite divisibility. "Self-decomposability is not stated in that
  paper; the words do not occur in it."
- Halgreen 1979, p. 13: "In this note it will, firstly, be shown that a GIGD is self-decomposable,
  or belongs to class L (Feller, 1971). In fact, any GIGD is a generalized $\Gamma$-convolution.
  This latter term was introduced by Thorin (1977) to denote the class of self-decomposable
  distributions F, concentrated on $[0,\infty)$, whose Laplace-transform … can be written as (2)".
  The proof (pp. 14–15) covers $\lambda < 0$ with $\psi \ge 0$, the inverse-gamma laws
  ($\psi = 0$) included; for that case p. 14 credits Bondesson (1977), a preprint.
- Read for this item, Bondesson's monograph, § 3.1, p. 30, at the page image: "Since the Gamma
  distribution is ID and self-decomposable (SD), so is every GGC."

So the paper's sentence is not false: Halgreen's p. 13 does state the class as one of
self-decomposable laws, and his theorem is the self-decomposability of every generalized inverse
Gaussian law. B is right that the inclusion "generalized gamma convolutions are self-decomposable"
is not Halgreen's result (it is Thorin's, which Halgreen recalls), and the printed sentence hangs
Halgreen's citation on the inclusion.

**Fix (b), the exact sentence.** "The inverse-gamma laws of clause (4) are generalized gamma
convolutions (Bondesson \[4\], § 4, pp. 51–52; Halgreen \[20\], pp. 13–15, for every generalized
inverse Gaussian law), and a generalized gamma convolution is self-decomposable (Bondesson's
monograph `bondesson1992generalized`, § 3.1, p. 30; the class and this property are Thorin's). So
they are the delay laws of a time-causal family (\[11\], Prop. 8.17, by its Thm. 7.3)."

**Touches.** Prose, and one new bibliography entry (`bondesson1992generalized`, held by the
librarian; the paper's `references.bib` has only the 1978 article). Thorin (1977) is not held and
is named, not cited. **Disposition.** Fix (a) and (b).

## 4. B R4: "their kernels are the rotation-invariant self-decomposable laws" — CONFIRMED

**The paper.** `04-conclusion.tex:36–37`, p. 29: "Its main result is that their kernels are the
rotation-invariant self-decomposable laws." The stages $\mu_{s,t}$, $s > 0$, are kernels of the
family and are not self-decomposable in general (item 12(2)).

**Every sentence that states the main result**, with its qualification:

| place | sentence | qualified |
|---|---|---|
| abstract, `main.tex:227–229`, p. 1 | "The kernels that take the signal to each scale are the dilations of one rotation-invariant self-decomposable law" | yes ("that take the signal to each scale" is $\mu_{0,t}$) |
| § 1, `01-introduction.tex:226–229`, p. 2 | "The axiom on dilations makes the kernels from scale zero the dilations of one law" | yes |
| § 1, `:235`, p. 2 | "Every symmetric self-decomposable law other than the point mass occurs." | yes, by the sentences before it (it occurs as that one law) |
| § 1, The answers, `:273–275`, p. 3 | "the kernels from scale zero of an isotropic family are, up to a relabelling of the scales, the dilations of one rotation-invariant self-decomposable law" | yes |
| § 1, `:281–282`, p. 3 | "So these laws are exactly the apertures that a designer may choose." | yes (an aperture is a kernel from scale zero, § 1, first paragraph) |
| § 1, Relation to scale-space theory, `:378–380`, p. 4 | "The kernels of a general family can be unbounded at their centre, in the dimensions $d \ge c$" | **no**; true as "can be", but it is about the kernels from scale zero |
| § 1, What the paper contributes, `:413–420`, p. 4 | "the rotation-invariant self-decomposable laws on $\mathbb{R}^d$ are exactly the kernels from scale zero of the isotropic scale spaces that the axioms define" | yes |
| § 4, `04-conclusion.tex:36–37`, p. 29 | "Its main result is that their kernels are the rotation-invariant self-decomposable laws." | **no** |
| § 4, `:37–39`, `:43–45`, p. 29 | "the kernels from scale zero of an isotropic family are …"; "A kernel from scale zero with no Gaussian part …" | yes |

**Fix.** p. 29: "Its main result is that their kernels from scale zero are the rotation-invariant
self-decomposable laws." p. 4: "The kernels from scale zero of a general family can be unbounded
at their centre".

**Touches.** Prose. **Disposition.** Fix. (With item 12 the following sentences of § 4 gain what
the stages are.)

## 5. B's suggestions S3, S1 — CONFIRMED (each is correct; none repairs an error)

**(a) The bijection as a statement.** What it would say: *a probability measure on $\mathbb{R}^d$
is a kernel $\mu_{0,t}$, $t > 0$, of an isotropic cascade family in dimension $d$ if and only if it
is rotation invariant, self-decomposable and not $\delta_0$.* From which statements:

- *Only if.* Theorem 3.6: $\widehat\mu_{0,t} = e^{-F(\chi(t)|\cdot|)}$ with $F \in \mathcal{A}_d$,
  $F \not\equiv 0$. By the definition of $\mathcal{A}_d$ (Proposition 2.6) there is a
  self-decomposable $\mu'$ with $\widehat{\mu'} = e^{-F(|\cdot|)}$, so
  $\mu_{0,t} = (\chi(t)I)_*\mu'$, self-decomposable with the residuals $(\chi(t)I)_*\rho_\lambda$
  (this computation is printed, in the proof of Proposition 3.15(1), p. 47). Rotation invariance
  is (I3), and $\mu_{0,t} \ne \delta_0$ is (ND).
- *If.* Let $\mu$ be rotation invariant, self-decomposable, not $\delta_0$. The unwritten step:
  $\widehat\mu$ is real and radial (Lemma 3.4(1)); $\mu$ is infinitely divisible (C4), so
  $\widehat\mu = e^{\psi}$ by the representation C3(i) and has no zero; a real continuous function
  on $\mathbb{R}^d$ with no zero and the value $1$ at $0$ is positive. So
  $F(r) := -\log\widehat\mu(re_1)$ maps $[0,\infty)$ to $[0,\infty)$ and
  $\widehat\mu = e^{-F(|\cdot|)}$. Proposition 3.10(1) and (2) make $F$ admissible, so
  $F \in \mathcal{A}_d$, and $F \not\equiv 0$. Lemma 3.8 gives, for any gauge, a family with (3.1),
  and $\mu_{0,t_1} = \mu$ at $\chi(t_1) = 1$.

B's parenthesis "$\widehat\mu > 0$ by C4 and Lemma 3.4(1)" is right with one fact added: that the
transform of an infinitely divisible law has no zero is read from C3(i) (C4 alone gives infinite
divisibility, not the exponential form).

*Cost of a numbered corollary.* A blueprint node (the paper prints no statement of § 3 without
one), `\uses{thm:isotropic-classification, lem:isotropic-realisation, prop:isotropic-polar-reading,
lem:radial-marginal, thm:cited-A3, thm:cited-A4}`. Lean, written beside the target type and not
compiled: the new obligation is "a rotation-invariant self-decomposable $\mu$ has
$\mathrm{charFun}\,\mu\,\xi = e^{-F\|\xi\|}$ for an $F \ge 0$", from `levy_khintchine_exists` and
`radial_marginal`, about 100–150 lines; the rest is `polar_reading_admissible` and
`isotropic_realisation`. Or the node is printed as proved in print, and the second list of § 1.1
grows to five (the abstract says "four").

*Smallest form.* Two sentences of prose after Proposition 3.10, where clause (2) is available:
"So a probability measure on $\mathbb{R}^d$ is a kernel $\mu_{0,t}$, $t > 0$, of an isotropic
family exactly when it is rotation invariant, self-decomposable and not the point mass. The
transform of such a law is real and radial (Lemma 3.4(1)) and has no zero, the law being
infinitely divisible (C4, C3(i)), so it is $e^{-F(|\cdot|)}$ with $F \ge 0$; clause (2) puts $F$
in $\mathcal{A}_d$, and Lemma 3.8 gives the family."

**Touches.** Prose (smallest form), or the blueprint and optionally the Lean. **Disposition.** The
author decides; recommended: the prose form.

**(b) Lemma 3.5's proof of (A7) in one line.** The printed proof
(`appendix-isotropic.tex:414–455`, pp. 36–37) is the line paper's collapsing-increment argument.
B's replacement: "for $(s_n,t_n) \to (s,t)$, (I2) at $\xi = \omega e$ gives
$\widehat\kappa_{s_n,t_n}(\omega) \to \widehat\kappa_{s,t}(\omega)$ for every $\omega$, so
Lemma 3.3(2) with $d = 1$ gives $\Phi_{s_n,t_n}f \to \Phi_{s,t}f$ in $L^1(\mathbb{R})$." It is
correct: Lemma 3.3(2) is stated for every $d \ge 1$ and for arbitrary probability measures, its
proof (pp. 34–35) uses nothing of § 3.2, and sequential continuity suffices on the metric space
$\{0 \le s \le t\}$. No circularity: in the blueprint `lem:kernels-to-operators` uses
`lem:operators-to-kernels(-families)` and no node of § 3.2.

**(c) Is Lemma 3.5 really Lemma 3.3(4) at $d = 1$.** Yes. $(\kappa_{s,t})$ satisfies (I1) by
Lemma 3.4(3), (I2) because $\widehat\kappa_{s,t}(\omega) = \widehat\mu_{s,t}(|\omega|e)$, (I3)
because $\mathrm{O}(1) = \{\pm1\}$ and $\kappa_{s,t}$ is symmetric (Lemma 3.4(1)), (I4) with the
same $S_\lambda$ by Lemma 3.4(3), and (ND) by Lemma 3.4(2). So it is an isotropic cascade family
in dimension $1$, Lemma 3.3(4) at $d = 1$ makes the operators an isotropic cascade measurement
family in dimension $1$ with the same $S_\lambda$, and that is Definition 2.1 (Remark 3.22). The
remaining assertion of the lemma, $\widehat\mu_{s,t}(\xi) = \widehat\kappa_{s,t}(|\xi|)$, is
Lemma 3.4(1).

*What the shorter proof touches.* The proof is a proof of record
(`lem:isotropic-marginal-family`), so the blueprint's proof changes with it (prose), with
`lem:kernels-to-operators` added to its `\uses`. The Lean need not change, and then no longer
follows the printed route: `isotropic_marginal_family` assembles the marginals into the shared
library's `ScaleSpace.CascadeData`, whose `continuousOn_mconvL1` is the collapsing-increment
argument (`Formalization/AffineHemigroup/MarginalFamily.lean:12–31`). It saves about
two-thirds of a page.

**Disposition.** The author decides (length against the correspondence of the printed proof with
the formal route). Mathematically nothing stands in the way.

## 6. A R1: Proposition 2.6 renumbers the clauses of its source — CONFIRMED

**The source.** Cone paper, Proposition 4.9, p. 34, at the page image, four clauses: "1. (The
bottom, and the nesting.) $\mathcal{A}_1$ is the whole admissible cone, and
$\mathcal{A}_{d+1} \subseteq \mathcal{A}_d$ for every $d \ge 1$. 2. (The slice sits in every
dimension.) … 3. (The top.) $\mathcal{A}_\infty \subseteq \mathcal{B}$. Consequently every
$F \in \mathcal{A}_\infty$ with $F \not\equiv 0$ has $F' > 0$ on $(0,\infty)$, and no admissible
$F \not\equiv 0$ with Gaussian coefficient $0$ whose profile is a step function with its jumps on a
lattice — in particular no Cin ray — lies in $\mathcal{A}_\infty$. 4. (The intersection is the
slice.) $\mathcal{A}_\infty = \mathcal{S}$".

**The paper.** `02-line-papers.tex:303–315`, p. 10, titled "\[10, Prop. 4.9\]": clauses (1), (2)
and "(3) $\mathcal{A}_\infty = \mathcal{S}$", the source's clause (4). The source's clause (3) and
the class $\mathcal{B}$ are dropped, and clause (2) is shortened to $\mathcal{S} \subseteq
\mathcal{A}_d$. The source comment on line 302 says "at its clauses (1), (2) and (4)"; the printed
text does not. The rule of p. 7 (`02-line-papers.tex:99–100`): "A restated statement carries its
released number in its title, and its proof is at that number."

**Where "Proposition 2.6(3)" is printed** (text layer of the PDF): five places, not nine.

| page | source line | text |
|---|---|---|
| 3 | `01-introduction.tex:318` | "no other exponents lie in every $\mathcal{A}_d$ (Proposition 2.6(3))" |
| 9 | `02-line-papers.tex:247` | "(Proposition 2.6(3) below)" |
| 25 | `03-isotropic.tex:1199` | "(Proposition 2.6(3))" |
| 70 | `appendix-isotropic.tex:3011` | "which the cone paper identified (Proposition 2.6(3))" |
| 71 | `appendix-isotropic.tex:3129` | "is Proposition 2.6(3)", written `\restatedc{B}{Prop.~4.9}{prop:line-filtration}{(4)}{(3)}` |

And once without a clause for the same fact: p. 30, `04-conclusion.tex:76`, "(Proposition 2.6)".
Clause (2) (pp. 2, 18, 22, 29) and clause (1) (pp. 22, 71) carry the source's numbers.

**The macro.** `paper-iso/macros.tex:93–94`: `\restatedc{B}{Prop.~4.9}{prop:line-filtration}{(4)}{(3)}`
prints "Proposition 2.6(3)" where the label exists (this paper) and "\[10, Prop. 4.9(4)\]" where it
does not (the blueprint). So the one shared sentence is already right on both sides. What is
missing is at the restatement itself.

**Fix.** Keep the numbering (a restatement with clauses (1), (2), (4) would be worse). Title:
"the dimension filtration, \[10, Prop. 4.9(1), (2) and (4)\]". After the statement, one sentence:
"Clause (3) is clause (4) of \[10, Prop. 4.9\]. Its clause (3), on a class that contains
$\mathcal{A}_\infty$, is not used here and not restated, and of its clause (2) only the inclusion
is."

**Touches.** Prose (the restatement has no blueprint node). **Disposition.** Fix.

## 7. A R8: "A kernel with a Gaussian part is bounded and smooth in every dimension" — CONFIRMED

**The paper.** `01-introduction.tex:286–287`, p. 3: "A kernel with a Gaussian part is bounded and
smooth in every dimension." `03-isotropic.tex:745–747`, p. 20: "A kernel with a Gaussian part has
a bounded smooth density in every dimension, since its transform is at most a Gaussian's." And the
first bullet of the list on p. 22 for the Gaussian itself.

**Is it a statement of the blueprint.** No. Theorem 3.12 (`thm:origin-boundedness-d`) supposes
Gaussian coefficient $0$, and the blueprint names a datum with a Gaussian part only as excluded
or not claimed (`blueprint/src/parts/03-isotropic.tex:2294`, `:2784`). **Is it machine-checked.**
No: `origin_density_smooth` and `origin_density_bounded_smooth` take `ha : D.a = 0`
(`Formalization/AffineHemigroup/OriginBoundedness.lean:661, 673`). **Is it true.** Yes:
$F_d(\xi) \ge \tfrac12 a|\xi|^2$, so $\int|\widehat\mu||\xi|^n\,d\xi < \infty$ for every $n$, and C1
gives a $C^n$ density with derivatives vanishing at infinity, for every $n$. **Where is it
listed.** Nowhere: the first list of § 1.1 is the numbered statements, the second names four, and
"Outside the formal verification" (`01-introduction.tex:584–600`) lists "what the text computes
from the statements" without it.

**Fix.** (i) p. 20, the argument in full: "A kernel with a Gaussian part has a bounded smooth
density in every dimension: the exponent of a datum $(a,k_d)$ is at least $\tfrac12 a|\xi|^2$, so
for $a > 0$ the transform is at most $e^{-a|\xi|^2/2}$, and C1 applies with every $n$." (ii) § 1.1,
"Outside the formal verification", in the sentence that lists what is computed in the text: add
"that a kernel with a Gaussian part has a bounded smooth density" at its head.

**The alternative A offers**, a clause of Theorem 3.12, changes a shared statement: the blueprint
node, its Lean (a statement with `0 < D.a`; the integrability of a Gaussian against powers and
`density_of_integrable_charFun`, perhaps 80–120 lines, nothing compiled) and the row of Table 3.

**Touches.** Prose (the fix above). **Disposition.** Fix as prose; the clause is the author's
decision and is not needed.

## 8. A R6: the witness and probe declarations are not in the axiom report — CONFIRMED

**What Appendix B claims.** `appendix-verification.tex:305–327`, p. 80: for the classification,
the threshold, the rate, the strict filtration and the Cin rays "the development holds a formal
example that rests on no cited fact", the six declarations `witness_isotropic_classification`,
`witness_origin_boundedness`, `witness_origin_rate`, `witness_origin_rate_critical`,
`witness_filtration`, `witness_no_cin_ray` of `Witnesses.lean`; `threshold_three_lt` "rests on no
cited fact"; `probe_witness_four` "rests on C2, C3 and C4".

**Where Lean's report for them is.**

| declaration | where a report is | pinned |
|---|---|---|
| `witness_origin_rate`, `witness_origin_rate_critical` | `Formalization/CIAxiomGuard.lean:1422–1427`, under `#guard_msgs` with "[propext, Classical.choice, Quot.sound]" | yes: the build fails if it changes |
| `witness_isotropic_classification`, `witness_origin_boundedness`, `witness_filtration`, `witness_no_cin_ray` | `CIAxiomGuard.lean:1372–1378`, plain `#print axioms` lines under the comment "every line is Lean core" | no: printed at each run of the guard, saved nowhere, and covered only by the repository-wide check that no axiom outside the twelve of `trust-boundary.txt` appears |
| `threshold_three_lt`, `probe_witness_four` | nowhere. The source comment (`appendix-verification.tex:315–321`) says the two guard files and the report do not have them and that Lean's report for the two was "printed for this item after the build" on a scratch file | no |

The file `records/affine/axioms-iso-all-declarations-output.txt` has the 195 declarations of the
inventory and none of these eight (grep). So for four witnesses "rests on no cited fact" is a
comment in the guard, and for the two probes it is a sentence in a source comment. Nothing
contradicts the claims; no deposited file supports six of the eight. No Lean was run for this
record.

**Fix.** Make the report cover them: `axioms-iso-all-declarations.py` emits a second block of
`#print axioms` requests, for the eight names, and the report file gains their lines (one run of
`lake env lean` after a build); the guard pins the six unpinned ones under `#guard_msgs` as it
does the other two. Then Appendix B: "Lean's report for these eight declarations is the second
part of the same file." If no build is run before the next review build, the sentence that is true
today is: "The report file covers the declarations of the list above. The eight declarations of
this paragraph are checked by the build; the guard holds Lean's report for
`witness_origin_rate` and `witness_origin_rate_critical`."

**Touches.** The guard file and a script (no library declaration, no blueprint node), the report
file, prose of Appendix B. **Disposition.** Fix, with the next Lean run.

## 9. A R9 and D R5: "An $F$ that grows like $c\log r$ determines a radial characteristic function" — CONFIRMED

**The paper.** `main.tex:236–238`, p. 1: "An $F$ that grows like $c\log r$ determines a radial
characteristic function, and is admitted one dimension up exactly when that function of the radius
is a characteristic function there." Proposition 3.18(2) starts "let $F \in \mathcal{A}_d$"
(`03-isotropic.tex:1266`). A function of logarithmic growth that is in no $\mathcal{A}_d$
determines no law.

**Fix.** The abstract is at its limit of 250 words (`records/affine/check-paper-iso-backmatter.py`),
so in the same number of words: "An admitted $F$ growing like $c\log r$ determines a radial
characteristic function, and is admitted one dimension up exactly when …".

**D's companion, p. 27** (`03-isotropic.tex:1294–1296`): "So an exponent of logarithmic growth is
in $\mathcal{A}_d$ exactly when $r \mapsto 1 - rF'(r)/c$ is a radial characteristic function on
$\mathbb{R}^d$, of a law with no atom at the origin and a finite logarithmic moment". PARTLY. The
"only if" is clause (2). The "if" holds for a function $F$ that is continuous on $[0,\infty)$ with
$F(0) = 0$ and continuously differentiable on $(0,\infty)$: then $F' = c(1-\phi)/r$,
$\int_0^1(1-\phi)\,du/u < \infty$ by clause (1), and $F = c\int_0^r(1-\phi)\,du/u$ is the function
of clause (1). The sentence states none of this and calls $F$ an exponent before it is one. The
proposition proves a bijection, and the sentence should say that: "So the members of
$\mathcal{A}_d$ of logarithmic growth are exactly the functions
$F(r) = c\int_0^r(1 - \phi(u))\,du/u$ with $0 < c < \infty$ and $\phi$ the radial characteristic
function of a law on $\mathbb{R}^d$ with no atom at the origin and a finite logarithmic moment.
Then $\phi(r) = 1 - rF'(r)/c$, and the polar profile is $c$ times the tail of $|X|$."

**Touches.** Prose. **Disposition.** Fix both.

## 10. C R1: "the last two sentences of the previous paragraph" — REFUTED

**The paper.** `appendix-isotropic.tex:1275–1276`, p. 47, as printed (text layer of the PDF,
p. 47, lines 16–17): "So the last two sentences of the **next** paragraph, at $d = 1$, give
$e^{-F(r)} \to 0$". The tag has the same words, and so has the blueprint
(`blueprint/src/parts/03-isotropic.tex:1299`). The reference is a forward one and is labelled as
one; the two sentences are the last two of "Clause (2): the four properties"
(`:1284–1288`), which use Theorem 3.12(1) and nothing of clause (1). No circularity.

**Fix.** None. **Disposition.** Decline: the finding quotes a word the paper does not print.

## 11. C's suggestions S6, S4, S3 — CONFIRMED (each is correct)

**(a) S6, the lower bound of Proposition 3.16(2) with $e^{-C_k}$.** Printed
(`03-isotropic.tex:982–985`, p. 23): "$I(s) \ge |S^{d-1}|\,e^{-13d/4 - 2C_k}\log(1/s)$ for
$0 < s \le 1$". The proof (`appendix-isotropic.tex:1789–1799`) uses Lemma A.3(1),
$e^{-F_d} \ge e^{-13c/4-2C_k}|\xi|^{-c}$, which bounds $1 - \cos$ by $2$ beyond radius $1$.
Proposition A.6(4) gives $e^{-F_d(\xi)} \ge e^{-13c/4 - C_k}K(1/|\xi|)\,|\xi|^{-c}$ for
$|\xi| \ge 1$, with $K \ge 1$: sharper by the factor $e^{C_k}K$. It is right: by the layer-cake
identity $\varphi(s) = T(s) + \int_0^c G(s\tau(y))\,dy$ with $T(s) = \int_{1/s}^\infty k\,dr/r$ and
$G \le 13/4$, the tail enters once. So
$I(s) \ge |S^{d-1}|e^{-13d/4-C_k}\mathcal{L}(s) \ge |S^{d-1}|e^{-13d/4-C_k}\log(1/s)$ is true
(script, block 11a: both bounds hold on four Matérn kernels; the gain is $e^{C_k}$, a factor
$1.1$ to $2.9$ there, while the transform exceeds either bound by a factor between $14$ and
$8 \times 10^{4}$; at $c = d$ in the plane the exact coefficient of $\log(1/s)$ is $0.32$, against
$9.2 \times 10^{-5}$ and $1.5 \times 10^{-4}$ for the two bounds).

It would change a machine-checked statement: the shared statement `prop:origin-rate-d` and its
proof, the constant $C_*$ in the prose, the Lean declarations `origin_transform_ball_log` and
`origin_density_log_lower` with a new dependence of the rate file on the profile file, and a new
edge `prop:origin-rate-d` $\to$ `prop:isotropic-exponent-profile` in the blueprint. And it buys
nothing the paper lacks: Proposition 3.17(3) already has the exact statement,
$q(s)/(B\mathcal{L}(s)) \to 1$ with $\log(1/s) \le \mathcal{L}(s)$, of which both bounds are crude
forms. **Disposition.** Decline: not cheap, and superseded by Proposition 3.17(3).

**(b) S4, "$c > 0$" in Theorem 3.12 is only nontriviality.** Right. $k_d \ge 0$ is nonincreasing,
so $c = k_d(0{+}) = \sup k_d$, and $c = 0$ exactly when $k_d \equiv 0$, the datum $(0,0)$, whose
law is $\delta_0$. The sentence after the theorem (`03-isotropic.tex:805–808`) says it implicitly
("other than the point mass"). **Fix**, in that paragraph, not in the shared statement: "The
hypothesis $c > 0$ only excludes the point mass: $k_d$ is nonincreasing, so $c$ is its supremum."
**Touches.** Prose. **Disposition.** Fix (one sentence), or leave.

**(c) S3, the constant $B_c$ of (A.9).** `appendix-isotropic.tex:1742–1746`:
$B_c = I_c/\Gamma(1+c/2)$ with $I_c = (4\pi)^{-d/2}|S^{d-1}|2^{d-c-1}\Gamma(\tfrac{d-c}2)$, so
$B_c = 2^{-c}\Gamma(\tfrac{d-c}{2})/(\Gamma(\tfrac d2)\Gamma(1+\tfrac c2))$. The reading note has
Theorems 8 and 9 of Cygan, Grzywny and Trojan at the page image (arXiv v2, p. 16), with
$\tilde{\mathcal{C}}_{d,\alpha} = 2^{-\alpha}\Gamma((d-\alpha)/2)/(\Gamma(d/2)\Gamma(1+\alpha/2))$.
They are equal at $\alpha = c$ (script, block 11c, five pairs $(d,c)$, to 20 digits). One
correction to C: Theorem 8 is the statement at infinity ($\psi \in R^0_\alpha$, $r \to +\infty$);
the one at the origin, which is this paper's case, is Theorem 9, with the same constant. The
Sources row (`sources.tex:146–152`) cites "Thm. 8 with its proof, and Thm. 9" for the method and
does not say that the constant coincides.

**Fix**, in that row: "… \[6\], Thm. 8 with its proof, and Thm. 9, whose constant is the $B_c$ of
(A.9) at $c = \alpha$." **Touches.** Prose. **Disposition.** Fix.

---

## 12. D R1: "The stages" is not an open problem — CONFIRMED, and answered completely

**The paper.** § 4.1, `04-conclusion.tex:102–106`, p. 30: "**The stages.** A stage $\mu_{s,t}$
with $s > 0$ is a residual of a kernel from scale zero (§ 2.2), not a dilation of it, and the
statements of § 3.3 do not apply to it. Which stages have a density, and which have an atom at the
centre? Where a stage has a density, is it bounded near the centre, and what number takes the
place of $c$?" With it: Scope, `01-introduction.tex:336–337`, p. 3, "The stages $\mu_{s,t}$ with
$s > 0$, which are what a cascade applies, are not examined at their centre", and the third
limitation, `04-conclusion.tex:85–87`, p. 30.

D's claim is right in every part: the direction of the difference of the profiles, the mass, the
atom, the Matérn numbers. Two additions. D leaves open "whether the stage has a density when
$c = \infty$ and $a = 0$": it has one, by four lines (clause (3) below). And "the number that
takes the place of $c$" is not $c\log(\chi(t)/\chi(s))$, which is the mass of the Lévy measure:
the transform of a stage with an atom does not fall off at all, and how its smoothing part behaves
at the centre is the question that stays open.

### The statement, as it would be printed

**Proposition (the stages).** Let $d \ge 1$, let $(\mu_{s,t})_{0 \le s \le t}$ be an isotropic
cascade family in dimension $d$ with gauge $\chi$ and exponent $F$
(Theorem 3.6), let $(a, k_d)$ be the isotropic origin datum of $F$ in dimension $d$
(Proposition 3.10(1)) and $c := k_d(0{+}) \in [0,\infty]$. Let $0 < s < t$ and put
$\ell := \chi(s)$, $L := \chi(t)$, $\lambda := \ell/L \in (0,1)$.

1. *(The stage is infinitely divisible, with an explicit Lévy measure.)* The function
   $\kappa_{s,t}(r) := k_d(r/L) - k_d(r/\ell)$, $r > 0$, is nonnegative. Let $\nu_{s,t}$ be the
   rotation-invariant measure on $\mathbb{R}^d \setminus \{0\}$ with the density
   $\kappa_{s,t}(|x|)/(|S^{d-1}||x|^d)$. Then $\int(|x|^2 \wedge 1)\,d\nu_{s,t} < \infty$,
   $$\widehat\mu_{s,t}(\xi) = \exp\Bigl[-\tfrac12 a(L^2 - \ell^2)|\xi|^2
     - \int_{\mathbb{R}^d}\bigl(1 - \cos\langle\xi,x\rangle\bigr)\,\nu_{s,t}(dx)\Bigr],$$
   and $\nu_{s,t}(\mathbb{R}^d \setminus \{0\}) = c\,\log(L/\ell)$, infinite exactly when
   $c = \infty$.
2. *(No Gaussian part, finite $c$: an atom at the centre.)* If $a = 0$ and $c < \infty$, then
   $$\mu_{s,t} = \lambda^c\,\delta_0 + p_{s,t}(x)\,dx, \qquad
     p_{s,t} = \lambda^c\sum_{n \ge 1}\frac{1}{n!}\,f_{s,t}^{*n}, \qquad
     f_{s,t}(x) := \frac{\kappa_{s,t}(|x|)}{|S^{d-1}||x|^d},$$
   with $p_{s,t} \ge 0$ rotation invariant and $\int p_{s,t} = 1 - \lambda^c$. So
   $\mu_{s,t}(\{0\}) = (\chi(s)/\chi(t))^c$, the stage has no density, it is not self-decomposable,
   and for $f \in L^1(\mathbb{R}^d)$
   $$\Phi_{s,t}f = \Bigl(\frac{\chi(s)}{\chi(t)}\Bigr)^{c} f + p_{s,t} * f .$$
3. *(No Gaussian part, $c = \infty$: a density.)* If $a = 0$ and $c = \infty$, then $\mu_{s,t}$ is
   absolutely continuous. In particular it has no atom.
4. *(A Gaussian part: a smooth density.)* If $a > 0$, then $\mu_{s,t}$ has a bounded density of
   class $C^\infty$, all of whose derivatives are bounded.

So a stage with $s > 0$ has an atom at the centre exactly when the kernels have no Gaussian part
and $c$ is finite, and a density in the two other cases.

*For the Matérn kernels of index $\gamma$* (Example 3.14; $a = 0$, $c = 2\gamma$, gauge
$\chi(t) = t$): the Lévy measure of the stage has the mass $2\gamma\log(t/s)$, and
$\mu_{s,t}(\{0\}) = (s/t)^{2\gamma}$. At $\gamma = 1$, in every dimension,
$\mu_{s,t} = (s/t)^2\delta_0 + (1 - (s/t)^2)\,\mu_{0,t}$. For every $\gamma$ the smoothing part
$p_{s,t}$ is bounded on the line and unbounded at the centre in every dimension $d \ge 2$.

### Proof (to the standard of a proof of record)

*Clause (1).* By Proposition 3.10(1),
$F(|\xi|) = \tfrac12 a|\xi|^2 + \int(1 - \cos\langle\xi,x\rangle)\,\nu_d(dx)$ with $\nu_d$ the
Lévy measure of the datum, of density $k_d(|x|)/(|S^{d-1}||x|^d)$. For $\beta > 0$ the
substitution $y = \beta x$ gives
$F(\beta|\xi|) = \tfrac12 a\beta^2|\xi|^2 + \int(1 - \cos\langle\xi,y\rangle)\,(\beta I)_*\nu_d(dy)$,
and by (3.2), for $g \ge 0$ Borel vanishing at the origin,
$\int g\,d(\beta I)_*\nu_d = |S^{d-1}|^{-1}\int_{S^{d-1}}\sigma_{d-1}(d\eta)\int_0^\infty
g(r\eta)\,k_d(r/\beta)\,dr/r$: the image has the polar profile $k_d(\cdot/\beta)$. Since
$\ell < L$ and $k_d$ is nonincreasing, $k_d(r/L) \ge k_d(r/\ell)$, so $\kappa_{s,t} \ge 0$ and
$\nu_{s,t} = (LI)_*\nu_d - (\ell I)_*\nu_d$ as measures with densities. Both integrals
$\int(1-\cos\langle\xi,\cdot\rangle)\,d(\beta I)_*\nu_d$, $\beta \in \{\ell, L\}$, are finite, so
they may be subtracted, and by (3.1)
$-\log\widehat\mu_{s,t}(\xi) = F(L|\xi|) - F(\ell|\xi|)
= \tfrac12 a(L^2-\ell^2)|\xi|^2 + \int(1-\cos\langle\xi,x\rangle)\,\nu_{s,t}(dx)$. Further
$\int(|x|^2 \wedge 1)\,d\nu_{s,t} \le \int(L^2|x|^2 \wedge 1)\,d\nu_d
\le \max\{1,L^2\}\int(|x|^2\wedge1)\,d\nu_d < \infty$. So $\nu_{s,t}$ is a symmetric Lévy
measure, and by C3(iii) the infinitely divisible law with the triplet
$(a(L^2-\ell^2)I, \nu_{s,t}, 0)$ has the displayed transform, the odd part of the integrand
integrating to $0$. It is therefore $\mu_{s,t}$.

The mass. In polar coordinates $\nu_{s,t}(\mathbb{R}^d\setminus\{0\}) =
\int_0^\infty\kappa_{s,t}(r)\,dr/r$. For $0 < \varepsilon < A$ with $\varepsilon/\ell \le A/L$,
substituting $u = r/L$ and $u = r/\ell$,
$$\int_\varepsilon^A\kappa_{s,t}(r)\,\frac{dr}{r}
 = \int_{\varepsilon/L}^{A/L}k_d(u)\,\frac{du}{u} - \int_{\varepsilon/\ell}^{A/\ell}k_d(u)\,\frac{du}{u}
 = \int_{\varepsilon/L}^{\varepsilon/\ell}k_d(u)\,\frac{du}{u}
   - \int_{A/L}^{A/\ell}k_d(u)\,\frac{du}{u},$$
every integral being finite because $k_d$ is finite and nonincreasing, hence bounded on
$[\varepsilon/L,\infty)$. The first term lies between $k_d(\varepsilon/\ell)\log(L/\ell)$ and
$k_d(\varepsilon/L)\log(L/\ell)$, and both tend to $c\log(L/\ell)$ as $\varepsilon \downarrow 0$,
also when $c = \infty$. The second is at most $\int_{A/L}^\infty k_d\,du/u$, which tends to $0$ as
$A \to \infty$ by the second condition of Definition 3.9. The integrand is nonnegative, so
monotone convergence gives $\int_0^\infty\kappa_{s,t}\,dr/r = c\log(L/\ell)$. (For a finite $c$
this is the computation of $\int h_a = c\log a$ in the proof of Lemma A.3(2), at $a = L/\ell$.)

*Clause (2).* Now $\nu := \nu_{s,t}$ is a finite measure of mass $m := c\log(L/\ell) > 0$
($c > 0$, because $a = 0$ and $F \not\equiv 0$), symmetric, with the density $f := f_{s,t}$. Put
$\pi := e^{-m}\sum_{n \ge 0}\nu^{*n}/n!$, with $\nu^{*0} = \delta_0$. It is a probability measure,
and $\widehat\pi = e^{-m}\sum_n\widehat\nu^{\,n}/n! = \exp(\widehat\nu - m)
= \exp[-\int(1-\cos\langle\xi,x\rangle)\,\nu(dx)]$, because $\widehat\nu$ is real, $\nu$ being
symmetric. By clause (1) with $a = 0$ this is $\widehat\mu_{s,t}$, and a probability measure is
determined by its transform, so $\mu_{s,t} = \pi$. For $n \ge 1$ the measure $\nu^{*n}$ has the
density $f^{*n}$, the convolution of an absolutely continuous finite measure with a finite measure
being absolutely continuous: $(\nu * M)(N) = \int\nu(N - y)\,M(dy) = 0$ for a Lebesgue-null $N$. So
$\pi = e^{-m}\delta_0 + p\,dx$ with $p = e^{-m}\sum_{n\ge1}f^{*n}/n!$, and
$e^{-m} = (\ell/L)^c = \lambda^c$. The mass of $p$ is $1 - \lambda^c$, and $p$ is rotation
invariant because $f$ is. The atom excludes a density. The operator: $\Phi_{s,t}f = \mu_{s,t} * f$
(Lemma 3.3).

Not self-decomposable. Suppose it were. Its transform is $e^{-G(|\xi|)}$ with
$G(r) = F(Lr) - F(\ell r) \ge 0$, so by Proposition 3.10(1) $G(|\cdot|)$ is the exponent of a
datum $(a', k')$. The law of that datum and $\pi$, which is the infinitely divisible law with the
triplet $(0, \nu, 0)$ (C3(iii)), have the same transform, so by the uniqueness of the triplet
(C3(ii)) $a' = 0$ and the Lévy measure of the datum is $\nu$. Its mass is $\int_0^\infty k'(r)\,dr/r$, which is infinite unless
$k' = 0$ almost everywhere, a nonincreasing $k' \ge 0$ that is not almost everywhere $0$ being
bounded below by a positive constant near $0$. So $\nu = 0$ and $\mu_{s,t} = \delta_0$, against
(ND).

*Clause (3).* Now $\nu := \nu_{s,t}$ has infinite mass. For $\varepsilon > 0$ let
$\nu^{>}_\varepsilon$ and $\nu^{\le}_\varepsilon$ be its restrictions to $\{|x| > \varepsilon\}$
and to $\{0 < |x| \le \varepsilon\}$. The first is finite, as every Lévy measure is off a ball
round the origin, of mass $m_\varepsilon \uparrow \infty$ as $\varepsilon \downarrow 0$, and
absolutely continuous. The second is a symmetric Lévy measure,
so by C3(iii) there is a law $\mu^\varepsilon$ with
$\widehat{\mu^\varepsilon} = \exp[-\int(1-\cos)\,d\nu^{\le}_\varepsilon]$. With
$\pi_\varepsilon := e^{-m_\varepsilon}\sum_n(\nu^>_\varepsilon)^{*n}/n!$, the transforms multiply
to $\widehat\mu_{s,t}$, so $\mu_{s,t} = \pi_\varepsilon * \mu^\varepsilon$. As in clause (2),
$\pi_\varepsilon = e^{-m_\varepsilon}\delta_0 + (\text{an absolutely continuous measure})$. For a
Lebesgue-null Borel set $N$,
$\mu_{s,t}(N) = \int\pi_\varepsilon(N - y)\,\mu^\varepsilon(dy)
= e^{-m_\varepsilon}\mu^\varepsilon(N) \le e^{-m_\varepsilon}$. Letting $\varepsilon \downarrow 0$,
$\mu_{s,t}(N) = 0$.

*Clause (4).* By C3(iii) there is a law $\pi$ with $\widehat\pi = \exp[-\int(1-\cos)\,d\nu_{s,t}]$,
and by clause (1) $\mu_{s,t} = g_v * \pi$ with $g_v$ the centred Gaussian of covariance $vI$,
$v := a(L^2 - \ell^2) > 0$, $\chi$ being increasing. Its density
$x \mapsto \int g_v(x - y)\,\pi(dy)$ is $C^\infty$, and each derivative is bounded by the supremum
of the same derivative of $g_v$.

*The Matérn kernels.* $c = 2\gamma$ and $\chi = \mathrm{id}$ (Proposition 3.11(2),
Example 3.14), so clause (2) gives the mass and the atom. At $\gamma = 1$, with $x = |\xi|^2/2$,
$(1 + s^2x)/(1 + t^2x) = s^2/t^2 + (1 - s^2/t^2)/(1 + t^2x)$, the transform of
$(s/t)^2\delta_0 + (1 - (s/t)^2)\mu_{0,t}$. For a general $\gamma$ the transform
$\phi(\rho) = ((1 + s^2\rho^2/2)/(1 + t^2\rho^2/2))^\gamma$ decreases from $1$ to
$\lambda^{2\gamma}$, so $(\phi - \lambda^{2\gamma})/(1 - \lambda^{2\gamma})$ is the nonnegative
transform of the probability density $p_{s,t}/(1 - \lambda^{2\gamma})$, and
$\rho^2(\phi(\rho) - \lambda^{2\gamma}) \to 2\gamma\lambda^{2\gamma}(s^{-2} - t^{-2})$. It is
integrable on $\mathbb{R}^d$ exactly for $d = 1$. For $d = 1$, C1 gives a bounded continuous
density. For $d \ge 2$, Lemma A.2(2) excludes a density bounded near the centre. $\qquad\square$

**What is machine-checked in this proof and what is cited.** Nothing of it is in Lean. Clause (1)
uses Proposition 3.10(1) (on C2, C3, C4) and C3(iii); clause (2) the uniqueness theorem for
characteristic functions, and C3(ii) and (iii) for "not self-decomposable"; clauses (3) and (4)
C3(iii); the Matérn remark C1 and Lemma A.2(2). No cited fact outside the seven. The atom and the
compound Poisson form of clause (2) use no cited fact once the transform of the stage is written
with the datum, which is how a formal statement would take it.

### Numerical check (script `item12_stage_compound_poisson.py`, output saved)

- (A) $\int_0^\infty(k_d(r/t) - k_d(r/s))\,dr/r = 2\gamma\log(t/s)$ for the Matérn profile in
  $d = 1, 2, 3$ and three $(\gamma, s, t)$, to the 15 digits printed; for a step profile exactly; for the
  logarithmic profile of § 3.3 the head $\int_{\varepsilon/L}^{\varepsilon/\ell}k\,dv/v$ is shown
  squeezed towards $c\log(L/\ell)$ (slowly, as $k(\varepsilon) \to c$ like $1/\log$), and the
  truncation identity of the proof holds to 14 digits.
- (B) the exponent of $\nu_{s,t}$ equals $\gamma\log\frac{1 + t^2\rho^2/2}{1 + s^2\rho^2/2}$ in
  $d = 1, 2, 3$ at three $\rho$, to the 14 digits printed.
- (C) the line, $\gamma = 1$, $s = 1$, $t = 2$: the inverse transform of (transform $-$ atom) is
  $(1 - (s/t)^2)$ times the Laplace density of range $t/\sqrt2$, to 12 digits; atom $1/4$.
- (D) the line, $\gamma = 3/4$, $s = 1$, $t = 2$: atom $2^{-3/2} = 0.35355339$; the density of
  the smoothing part by inverse transform is nonnegative on $[0,40]$, with
  $2\int_0^{40}p = 0.646456$ against $1 - \text{atom} = 0.646447$; the Gaussian average
  $(2\pi\tau)^{1/2}\int g_\tau\,d\mu$ tends to the atom ($0.41264$, $0.35980$, $0.35418$ at
  $\tau = 10^{-2}, 10^{-4}, 10^{-6}$).
- (E) the law simulated as the compound Poisson sum ($N$ Poisson of mean $2\gamma\log(t/s)$, jumps
  $\pm E/U$ with $U$ log-uniform on $(\sqrt2/t, \sqrt2/s)$ and $E$ standard exponential;
  $2 \times 10^6$ draws): $\Pr(X = 0) = 0.353791$ against $0.353553$ (standard error
  $3.4 \times 10^{-4}$); $\mathbb{E}\cos(\omega X)$ at four $\omega$ and $\Pr(|X| \le x)$ at three
  $x$ within $2.4$ standard errors of the transform and of atom $+$ density. Three further seeds
  at $4 \times 10^6$ draws each: every deviation of $\Pr(X = 0)$ and of $\mathbb{E}\cos(\omega X)$
  below $1.5$ standard errors, of both signs.
- (F) the cascade at three points: $p_{0,t}(x) = \lambda^c p_{0,s}(x) + (p_{s,t} * p_{0,s})(x)$ to
  $3 \times 10^{-6}$.
- (G) $\rho^2(\phi - \text{atom})$ tends to $2\gamma\lambda^{2\gamma}(s^{-2} - t^{-2})$ for
  $\gamma = 3/4, 3, 10$.

### In plain words, for a filter

A stage of a cascade whose kernels have no Gaussian part and a finite $c$ does not blur
everything. It passes the fraction $(\chi(s)/\chi(t))^c$ of the record at scale $s$ through
unchanged and adds to it a smoothed copy carrying the rest: the stage operator is
$(\chi(s)/\chi(t))^c$ times the identity plus a convolution with a nonnegative kernel of mass
$1 - (\chi(s)/\chi(t))^c$. For a Matérn cascade of index $\gamma$ a stage from $s$ to $t$ leaves
the fraction $(s/t)^{2\gamma}$ of the image untouched, a quarter for $\gamma = 1$ and one octave.
The kernels from scale zero have no such atom: the atom tends to $0$ as $s \downarrow 0$. A stage
is a smoothing with a density exactly when the kernels have a Gaussian part or $c = \infty$, as
for the Gaussian and the stable kernels.

### Do the earlier papers have it

Searched for "atom", "compound Poisson", "stage", "increment", "convex combination".

- The cone paper has the fact for the Matérn family of integer index on the line, as a
  realization and not as a statement about an atom. Proposition 7.2, p. 61, at the page image:
  "The section's kernel is the mixture $\frac{t_k}{t_{k+1}}\delta_0 +
  (1 - \frac{t_k}{t_{k+1}})\,\mathrm{Exp}_+(t_{k+1})$ of no displacement and a one-sided
  exponential displacement … so the two-sided increment for $\gamma = 1$ is the four-term mixture
  $r^2\delta_0 + r(1-r)(\mathrm{Exp}_+ + \mathrm{Exp}_-) + (1-r)^2\,\mathrm{Lap}_{t_{k+1}}$,
  $r := t_k/t_{k+1} \in (0,1)$ (7.2)". With $\mathrm{Exp}_+ + \mathrm{Exp}_- = 2\,\mathrm{Lap}$
  this is $r^2\delta_0 + (1 - r^2)\mathrm{Lap}$, clause (2) at $\gamma = 1$, $d = 1$. For integer
  $\gamma$ the $2\gamma$ sections give the atom $r^{2\gamma}$. Its Example 7.12 (p. 79, text
  layer) has one more instance of the same count: a recursive Gaussian design whose stage from
  $\sigma$ to $2\sigma$ "has an atom of mass 1/64"; the profile printed there for that design,
  $2e^{-1.1668x} + 4e^{-1.10783x}\cos(1.40586x)$, has the value $6$ at $0{+}$, and
  $(1/2)^6 = 1/64$. (That design is not a member of the class; the limit of the ratio of the
  transfer functions is the same computation.)
- The time-causal paper has the same for the gamma family (p. 63, text layer: the increment
  section "whose transfer is $(1 + x_ks)/(1 + x_{k+1}s)$. The output is a convex combination of
  input and state"), the dilation difference of the profile in the proof of its Lemma 7.1 (p. 27:
  $F(bs) - F(as) = b_0(b-a)s + \int_0^\infty(1 - e^{-su})(k(u/b) - k(u/a))\,du/u$), and for the
  kernels from scale zero its Lemma 9.2 (p. 42): "$F(\infty) = \infty$ if and only if the kernels
  have no atom at zero delay".
- Neither states the general fact: for every profile with a finite $c$, in every dimension, the
  atom $(\chi(s)/\chi(t))^c$. The line paper has nothing on it.

### What stating it would cost

*Blueprint.* One node, say `prop:isotropic-stage`, in § 3.3 or with the limitations, with
`\uses{thm:isotropic-classification, prop:isotropic-polar-reading, def:isotropic-origin-datum,
lem:polar-decomposition, lem:positive-transform-origin, thm:cited-A1, thm:cited-A3}`, and the
proof above, about a page in the appendix.

*Lean.* What exists: every stage is infinitely divisible
(`isotropic_family_infinitelyDivisible`, `CascadeDivisible.lean:285`); the compound Poisson law of
a finite measure with its transform, and the real transform of a symmetric finite measure
(`cpLaw`, `charFun_cpLaw`, `charFun_of_symm`, `OriginLowerBound.lean:61–135`);
$(c\,\cdot)_*\nu_d \le \nu_d$ and the exponent at $c\eta$ as a Lévy–Khintchine form
(`OriginDatum.map_smul_levyMeasure_le`, `exponent_smul_eq_lkForm`, `FiltrationTop.lean:120, 193`);
the mass $\int h_b = c\log b$ of the dilation difference for a finite $c$
(`OriginDatum.lintegral_hb`, `ExponentLog.lean:144`); the general converse
`levy_khintchine_converse` for a triplet. The target for clause (2), written and not compiled:

```lean
theorem isotropic_stage_atom (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) {χ : ℝ → ℝ} (hχ : IsGauge χ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
      ((Real.exp (-(D.exponent (χ t • ξ) - D.exponent (χ s • ξ))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ L : Measure (Rd d), IsFiniteMeasure L ∧ L ≪ volume ∧ μ s t = cpLaw L ∧
      L univ = D.profileAtOrigin * ENNReal.ofReal (Real.log (χ t / χ s)) ∧
      μ s t {0} = ENNReal.ofReal ((χ s / χ t) ^ D.profileAtOrigin.toReal)
```

Its obligations, counted on that type: the stage's Lévy measure as a `withDensity` (the difference
of two measures is avoided), its mass by polar coordinates for a radial density that is not a
datum's (`polar_decomposition` is stated for an `OriginDatum`; the general identity is in
`lintegral_shadow`'s proof and has to be separated), its transform as a difference of two finite
integrals, equality of laws by transforms, and $(\nu * M)(\{0\}) = 0$ for an absolutely continuous
$\nu$. Estimate: one file of 300 to 450 lines, on Lean's logical axioms alone (the statement
quantifies over a datum and a family with the given transforms, so no cited fact enters). Clause
(3) needs the same decomposition with `levy_khintchine_converse` for the small part, 200 to 300
lines more, and prints C3(iii). Clause (4) needs the smoothness of a Gaussian convolution or C1
with a Gaussian bound, about 150 lines. Nothing of this was compiled.

*Or in print only*, as the dictionary is: the second list of § 1.1 grows, and the abstract's "four
proved in print" changes.

### Which sentences change

- Scope, `01-introduction.tex:336–337`, p. 3: "Those on the centre concern the kernels from scale
  zero. The stages $\mu_{s,t}$ with $s > 0$, which are what a cascade applies, are not examined at
  their centre." $\to$ "Those on the centre concern the kernels from scale zero. A stage
  $\mu_{s,t}$ with $s > 0$, which is what a cascade applies, is of another kind: when the kernels
  have no Gaussian part and $c$ is finite it has no density, and leaves the fraction
  $(\chi(s)/\chi(t))^c$ of the record in place (Proposition X). The part of a stage that smooths
  is not examined at its centre."
- § 4, the third limitation, `04-conclusion.tex:85–87`, p. 30: "Its statements on the centre are
  about the kernels from scale zero, and the stages … are not examined." $\to$ "Its statements on
  the centre are about the kernels from scale zero. Of a stage $\mu_{s,t}$ with $s > 0$ it says
  whether it has an atom at the centre or a density (Proposition X), and no more."
- § 4, second paragraph, one sentence for the user after the spike: "A stage of such a cascade
  passes the fraction $(\chi(s)/\chi(t))^c$ of the finer record unchanged, $(s/t)^{2\gamma}$ for
  the Matérn kernels."
- § 4.1, "The stages", rewritten as what is left: "A stage $\mu_{s,t}$ with $s > 0$ of a family
  with no Gaussian part and a finite $c$ is an atom at the centre and an absolutely continuous
  part (Proposition X). Is that part bounded near the centre, and what number decides it? For the
  Matérn kernels it is bounded on the line and unbounded in every higher dimension, whatever the
  index. And when $c = \infty$ the stage has a density: is it bounded?"
- § 4, `04-conclusion.tex:36–37` (item 4), and § 2.2's sentence "the residuals are the stages"
  stand.

**Touches.** A new statement: the blueprint; the Lean if it is to be machine-checked; prose of
§ 1, § 4 and § 4.1; § 1.1 and the abstract's count if it is printed without Lean.
**Disposition.** Fix: state it. The form (machine-checked clause (2), or all four clauses in
print) is the author's decision.

---

## 13. D R2: "The step witnesses" is answered — CONFIRMED, and the last dimension is $d + 2$

**The paper.** § 4.1, `04-conclusion.tex:108–111`, p. 30: "**The step witnesses.** The exponent of
a step datum is not that of a self-decomposable law in the next dimension
(Proposition 3.19(2)). Is it still the exponent of an infinitely divisible law there? Those of the
separating family are, in every dimension (Proposition A.14)."

D's inversion is right: its two closed forms, their positivity, the integrability, the shadow, and
the identity in $\mathbb{R}^3$ for the Cin ray. The repository had the case $d = 1$ already, as a
numerical observation: `VERIFY-round1-filtration-map-blind-check.md`, § 5, "Cin($|\xi|$) is the
exponent of the Lévy measure with polar profile $(1-s^2)^{-1/2}$ on the unit disc of the plane,
and of the measure $1_{(0,1)}\,dr/r + \delta_1$ in radius on $\mathbb{R}^3$ (both reproduce Cin to
14 digits)". The comment at the head of `04-conclusion.tex` (lines 19–22) records it as "numerical
evidence only". It is a two-line proof. And the question D proposes in its place, "the last
dimension in which a step exponent is infinitely divisible", is well posed (the set of such
dimensions is closed downwards, by projection) and has the answer $d + 2$.

### The statement, as it would be printed

**Proposition (the step exponent in higher dimensions).** Let $d \ge 1$, $b > 0$, $\tau > 0$, and
let $G$ be the function of Proposition 3.19(2): $\xi \mapsto G(|\xi|)$ is the exponent of the
step datum $(0, b\,\mathbf 1_{(0,\tau)})$ in dimension $d$,
$G(\rho) = b\int_0^\tau(1 - \Omega_d(r\rho))\,dr/r$. Write $G_n$ for the same function with $n$ in
place of $d$, so that $G = G_d$. Let $D \ge 1$ be an integer.

1. $\zeta \mapsto G(|\zeta|)$, $\zeta \in \mathbb{R}^D$, is the exponent of a self-decomposable
   law on $\mathbb{R}^D$ if and only if $D \le d$.
2. It is the exponent of an infinitely divisible law on $\mathbb{R}^D$ if and only if
   $D \le d + 2$.
3. *(Dimension $d + 2$.)* For every $\rho \ge 0$,
   $$G_d(\rho) = G_{d+2}(\rho) + \frac{b}{d}\bigl(1 - \Omega_{d+2}(\tau\rho)\bigr).$$
   So on $\mathbb{R}^{d+2}$ the law is the convolution of the law of the step datum
   $(0, b\,\mathbf 1_{(0,\tau)})$ of dimension $d + 2$ with a compound Poisson law of rate $b/d$
   whose jumps are uniformly distributed on the sphere of radius $\tau$. Its Lévy measure is the
   step datum's plus $b/d$ times the uniform probability measure on that sphere.
4. *(Dimension $d + 1$.)* On $\mathbb{R}^{d+1}$ the Lévy measure is rotation invariant with the
   polar profile, for $0 < s < \tau$ and $0$ beyond,
   $$k'(s) = 2b\,C_{d+1}\Bigl[J_{d+2}\bigl(\tfrac{\tau}{s}\bigr)
       + \frac{1}{d}\Bigl(\frac{s}{\tau}\Bigr)^{d}\frac{s}{\sqrt{\tau^2 - s^2}}\Bigr]
     = \frac{b}{\pi C_d}\Bigl[(d-1)\,J_d\bigl(\tfrac{\tau}{s}\bigr)
       + \frac{\tau^{2-d}s^{d-1}}{\sqrt{\tau^2 - s^2}}\Bigr],
     \qquad J_n(x) := \int_1^x\frac{v^{1-n}\,dv}{\sqrt{v^2-1}},$$
   with $C_n = |S^{n-1}|/|S^n|$ as in Lemma A.8. It is positive, $k'(0{+}) = b$, and
   $k'(s) \to \infty$ as $s \uparrow \tau$, so it is not nonincreasing. For $d = 1$,
   $k'(s) = b\tau/\sqrt{\tau^2 - s^2}$; for $d = 2$,
   $k'(s) = (2b/\pi)[\arccos(s/\tau) + s/\sqrt{\tau^2 - s^2}]$.

In particular a Cin ray ($d = 1$) is the exponent of an infinitely divisible law in the plane and
in space, of a self-decomposable law in neither, and of no infinitely divisible law on
$\mathbb{R}^4$.

### Proof (to the standard of a proof of record)

*Three facts about $\Omega_n$.* (i) $\zeta \mapsto \Omega_n(\tau|\zeta|)$ is the characteristic
function of the uniform probability measure $\sigma^{(n)}_\tau$ on the sphere of radius $\tau$ of
$\mathbb{R}^n$: this is the definition of $\Omega_n$ in Proposition 3.18. (ii) By (3.2), the
exponent of the datum $(0, b\,\mathbf 1_{(0,\tau)})$ in dimension $n$ at a point of length $\rho$
is $b\int_0^\tau(1 - \Omega_n(r\rho))\,dr/r = G_n(\rho)$; the integral converges at $0$ because
$1 - \Omega_n(t) \le t^2/2$. (iii) For every $d \ge 1$ and $t \ge 0$,
$$\Omega_d(t) = \Omega_{d+2}(t) + \frac{t}{d}\,\Omega_{d+2}'(t).$$
For $d = 1$: $\Omega_3(t) = \sin t/t$, and $\sin t/t + t(\cos t/t - \sin t/t^2) = \cos t$. For
$d \ge 2$: the first coordinate of a uniform point of $S^{n-1}$, $n \ge 2$, has the density
$c_n(1-u^2)^{(n-3)/2}$ on $(-1,1)$, $c_n = \Gamma(\tfrac n2)/(\sqrt\pi\,\Gamma(\tfrac{n-1}2))$, so
$\Omega_n(t) = c_n\int_{-1}^1\cos(tu)(1-u^2)^{(n-3)/2}du$. Differentiating under the integral at
$n = d + 2$ and integrating by parts, the boundary terms vanishing because $d \ge 2$,
$$t\,\Omega_{d+2}'(t) = c_{d+2}\int_{-1}^1 u\,\frac{d}{du}\cos(tu)\,(1-u^2)^{(d-1)/2}du
  = -c_{d+2}\int_{-1}^1\cos(tu)\,(1-u^2)^{(d-3)/2}\bigl[d(1-u^2) - (d-1)\bigr]du ,$$
which is $-d\,\Omega_{d+2}(t) + (d-1)(c_{d+2}/c_d)\,\Omega_d(t) = -d\,\Omega_{d+2}(t) + d\,\Omega_d(t)$,
since $c_{d+2}/c_d = d/(d-1)$.

*Clause (3).* By (ii) and (iii),
$G_d(\rho) - G_{d+2}(\rho) = b\int_0^\tau\bigl(\Omega_{d+2}(r\rho) - \Omega_d(r\rho)\bigr)\frac{dr}{r}
= -\frac bd\int_0^\tau\rho\,\Omega_{d+2}'(r\rho)\,dr = \frac bd\bigl(1 - \Omega_{d+2}(\tau\rho)\bigr)$.
On $\mathbb{R}^{d+2}$, $e^{-G_{d+2}(|\zeta|)}$ is the transform of the law of the step datum of
dimension $d + 2$ (C3(iii)), and by (i) $\exp[-\tfrac bd(1 - \Omega_{d+2}(\tau|\zeta|))]$ is the
transform of the compound Poisson law
$e^{-b/d}\sum_n(b/d)^n(\sigma^{(d+2)}_\tau)^{*n}/n!$. Both are infinitely divisible, so their
convolution is, and its transform is $e^{-G_d(|\zeta|)}$. Its Lévy measure is the sum
$\nu^{(d+2)} := \nu^{\mathrm{step}}_{d+2} + \tfrac bd\,\sigma^{(d+2)}_\tau$, by C3(ii).

*Clause (4), and "if" in clause (2).* The image of an infinitely divisible law under a linear map
is infinitely divisible, so the law of clause (3) projects to infinitely divisible laws on
$\mathbb{R}^{D}$, $D \le d + 2$, with the transforms $e^{-G_d(|\cdot|)}$. On $\mathbb{R}^{d+1}$
its Lévy measure is the image of $\nu^{(d+2)}$ under the projection $\Pi$, off the origin (C3(ii),
as in Lemma A.8(3)). The image of $\nu^{\mathrm{step}}_{d+2}$ has, by Lemma A.8 with $d + 1$ in
place of $d$ and the substitution $v = \sqrt{1+u^2}$, the polar profile
$C_{d+1}\int_{\mathbb{R}}b\,\mathbf 1_{\{s\sqrt{1+u^2} < \tau\}}(1+u^2)^{-(d+2)/2}du
= 2bC_{d+1}\,J_{d+2}(\tau/s)$. The image of $\sigma^{(d+2)}_\tau$ has the density
$2\tau^{-d}/(|S^{d+1}|\sqrt{\tau^2 - |x|^2})$ on $\{|x| < \tau\}$ (each point of the ball has two
preimages, with surface element $\tau\,dx/\sqrt{\tau^2-|x|^2}$), so $\tfrac bd$ times it has the
polar profile $|S^d|s^{d+1}\cdot\tfrac bd\cdot 2\tau^{-d}/(|S^{d+1}|\sqrt{\tau^2-s^2})$. The sum is
the first form of $k'$. The second form follows from
$x^{-d}\sqrt{x^2-1} = (1-d)J_d(x) + d\,J_{d+2}(x)$, which is the integral over $[1,x]$ of
$\frac{d}{dv}[v^{-d}\sqrt{v^2-1}] = [(1-d)v^{1-d} + d\,v^{-d-1}]/\sqrt{v^2-1}$, and from
$C_dC_{d+1} = |S^{d-1}|/|S^{d+1}| = d/(2\pi)$. Both terms of the first form are positive;
$k'(0{+}) = b$ by Lemma A.8(2) for the first term, the second tending to $0$; and the second term
is unbounded at $\tau$. The closed forms: $J_3(x) = \sqrt{x^2-1}/x$ and
$J_4(x) = \tfrac12[\sqrt{x^2-1}/x^2 + \arccos(1/x)]$. The second form is the one that D obtains by
inverting the shadow formula: the two derivations agree.

*Clause (1).* $G \in \mathcal{A}_d \setminus \mathcal{A}_{d+1}$ by Proposition 3.19(2), and
$\mathcal{A}_D \subseteq \mathcal{A}_{d+1}$ for $D \ge d + 1$, $\mathcal{A}_d \subseteq
\mathcal{A}_D$ for $D \le d$ (Proposition 2.6(1)).

*"Only if" in clause (2).* By projection it is enough to exclude $D = d + 3$. Suppose $\mu'$ is
infinitely divisible on $\mathbb{R}^{d+3}$ with $\widehat{\mu'} = e^{-G_d(|\cdot|)}$. As in the
proof of Proposition 3.10(1), its triplet is $(\alpha I, \nu', \gamma)$ with $\nu'$ invariant
under $\mathrm{O}(d+3)$, and
$G_d(|\zeta|) = \tfrac12\alpha|\zeta|^2 + \int(1 - \cos\langle\zeta,z\rangle)\,\nu'(dz)$. Let
$\Pi$ be the projection on the first $d + 2$ coordinates. Reading the identity at $(\zeta, 0)$,
$G_d(|\zeta|) = \tfrac12\alpha|\zeta|^2 + \int(1 - \cos\langle\zeta,y\rangle)\,\bar\nu(dy)$ on
$\mathbb{R}^{d+2}$, with $\bar\nu$ the image of $\nu'$ under $\Pi$ off the origin, a symmetric
Lévy measure because $|\Pi z| \le |z|$. By C3(iii) and C3(ii) in dimension $d + 2$, and clause
(3), $\alpha = 0$ and $\bar\nu = \nu^{(d+2)}$. So
$\bar\nu(\{|y| = \tau\}) \ge \tfrac bd > 0$. But
$\bar\nu(\{|y| = \tau\}) = \nu'(\{z : |\Pi z| = \tau\})$, and this is $0$: the set lies in
$\{|z| \ge \tau\}$, where $\nu'$ is finite, and averaging over the Haar probability of
$\mathrm{O}(d+3)$, which leaves $\nu'$ invariant,
$\nu'(\{|\Pi z| = \tau\}) = \int\nu'(dz)\,\bar\sigma(\{u \in S^{d+2} : |\Pi u| = \tau/|z|\})$, and
for each radius the set $\{u : |\Pi u| = w\}$ is a null set of the sphere, $|\Pi u|^2$ having a
density on $(0,1)$. A contradiction. $\qquad\square$

**Remark (the filter, as distinct from the cascade).** That $G(|\cdot|)$ is not a Lévy exponent on
$\mathbb{R}^D$ says that $e^{-tG(|\cdot|)}$ fails to be a characteristic function for some
$t > 0$, and then for every small $t$. For if it were one along a sequence $t_n \downarrow 0$,
then for every integer $k \ge 1$ the function
$e^{-G/k} = \lim_n\,(e^{-t_nG})^{\lfloor 1/(kt_n)\rfloor}$ would be one, being a continuous
pointwise limit of characteristic functions (Lévy's continuity theorem, in $\mathbb{R}^D$), and
$e^{-G}$ would be the transform of an infinitely divisible law. Since $G$ is proportional to $b$: for
$D \ge d + 3$ and every sufficiently small height $b$, $e^{-G(|\zeta|)}$ is not the transform of a
probability law on $\mathbb{R}^D$. Whether it is one for some large $b$ is not settled here.

**What is cited.** C3(ii), C3(iii), Lemma A.8, Proposition 3.19(2), Proposition 2.6(1). Nothing
of it is in Lean; $\Omega_d$ is not in the formal development (the dictionary is proved in print).

### Numerical check (script `item13_step_exponent_dimensions.py`, output saved)

- (A) the identity (iii) for $d = 1, \dots, 5$ at three $t$ to 18 digits, and
  $G_d = G_{d+2} + \tfrac bd(1 - \Omega_{d+2}(\tau\rho))$ at $b = 0.8$, $\tau = 1.7$ and three
  $\rho$, to 14 digits.
- (B) the two closed forms of $k'$ ($d = 1, 2$) to 18 digits; $k' > 0$, nondecreasing on
  $(0,\tau)$, $k'(0{+}) = b$ for $d = 1, \dots, 5$; $\int_0^\tau k'(s)\,s\,ds$ finite
  ($1, \tfrac34, \tfrac23, \tfrac58, \tfrac35$ at $b = \tau = 1$); the shadow of $k'$ by the
  formula of Lemma A.8 equals the step at four radii for $d = 1, \dots, 4$, to 10 digits; the
  exponent $\int_0^\tau(1 - \Omega_{d+1}(s\rho))k'(s)\,ds/s$ equals $G_d(\rho)$ for $d = 1, 2, 3$
  at three $\rho$, to the 13 digits printed; and the two forms of $k'$ agree (shadow of the step of dimension
  $d + 2$ plus the profile of the projected sphere).
- (C) the Mellin transform that the radial part of a Lévy measure in dimension $D$ would have,
  $M_D(z) = b\tau^z\Gamma(\tfrac d2)\Gamma(\tfrac{D+z}2)/(z\,\Gamma(\tfrac D2)\Gamma(\tfrac{d+z}2))$:
  $|M_D(1 + iy)|/M_D(1) \le 1$ on $[0, 10^4]$ for $D = d + 1, d + 2$, and it grows like
  $|y|^{1/2}$ and $|y|$ for $D = d + 3, d + 4$, which no positive measure allows. A second view
  of "only if".
- (D), (E) a certificate that does not use the proof. For a Lévy exponent $G$ on $\mathbb{R}^D$
  with Lévy measure $\nu$ and a radial Schwartz $h \ge 0$ that vanishes with its Laplacian at
  $0$, $\int G(|\zeta|)\,\widehat h(\zeta)\,d\zeta = -(2\pi)^D\int h\,d\nu \le 0$. With
  $h(x) = |x|^{2p}e^{-a(|x|^2-1)}$ the left side, computed directly from $G_d$:

  | $d$ | $D = d+1$ | $D = d+2$ | $D = d+3$ | $(p, a)$ |
  |---|---|---|---|---|
  | 1 | $-78.85$ | $-462.26$ | $+1242.03$ | $(30, 40)$, 30 digits |
  | 1 | $-66.64$ | $-362.31$ | $+11794.3$ | $(361, 400)$, double precision |
  | 2 | $-277.82$ | $-1497.18$ | $+25857.3$ | $(361, 400)$ |
  | 3 | $-1425.56$ | $-7774.97$ | $+74195.8$ | $(361, 400)$ |

  Positive in dimension $d + 3$ in each row: not a Lévy exponent there. Each value agrees with
  $-(2\pi)^D$ times the functional read off $M_D$, to 12 digits (first row) and to $10^{-5}$
  (the others).

### What follows, and what stays open

- The step exponent of dimension $d$ is the exponent of an infinitely divisible law in dimensions
  $d + 1$ and $d + 2$, and of a self-decomposable law in neither. In those two dimensions
  $e^{-G(|\xi|)}$ is a probability kernel, and what is lost is the cascade. D's suggestion for
  p. 28, that a Cin transfer function is still a kernel in the plane and in space, is right and is
  the case $d = 1$.
- On what is known for $\Omega_d$: $\Omega_d(\tau|\cdot|)$ is a characteristic function in
  dimensions up to $d$ only (Daley and Porcu, Lemma 12, p. 1822, in the reading note; the paper's
  Corollary A.9(2)). The step exponent integrates $1 - \Omega_d(r\rho)$ against $dr/r$ up to
  $\tau$, and that gains exactly two dimensions: $D \le d + 2$.
- Open, and of another kind: for $D \ge d + 3$, is $e^{-G(|\zeta|)}$ a characteristic function
  for some height $b$ (the remark)?

### What stating it would cost, and which sentences change

*Blueprint.* One node, `\uses{prop:profile-one-dimension-down, prop:radial-dictionary,
lem:shadow-polar-profile, prop:isotropic-polar-reading, thm:cited-A3}`, proved in print (about a
page). *Lean.* Not cheap: $\Omega_d$ and the spherical integrals are not in the development, and
the integration by parts on the sphere, the projection of the sphere measure and the Haar average
would each be new; an estimate from the target type is 600 to 1000 lines. Recommended in print
only, as the dictionary is.

*Sentences.* § 4.1, "The step witnesses": removed, or replaced by the remark's question. § 3.4,
`03-isotropic.tex:1367–1369`, p. 28, after "What the clause excludes is a Cin ray taken alone,
which is the exponent of no isotropic family in the plane or in any higher dimension": add "It is
still the exponent of an infinitely divisible law in the plane and in space, so the filter
remains a probability kernel there and only the cascade is lost (Proposition Y)." § 4,
`04-conclusion.tex:77–78`: unchanged.

A form without a numbered statement is possible: clause (3) and its two-line proof as a paragraph
of § 3.4, listed in § 1.1 with what the text computes. It would not carry "only if".

**Touches.** A new statement: the blueprint (print only); prose of § 3.4 and § 4.1; § 1.1 and the
abstract's count. **Disposition.** Fix: the question leaves § 4.1. Stated as a proposition or as a
paragraph: the author decides.

---

## 14. D R4: "$4 \le w_2$" is proved in print in the cone paper — CONFIRMED

**The paper.** `01-introduction.tex:597–600`, p. 6: "Of that example Lean has only $w_3 < 4$, so
that $F^{(4)}$ is admitted in no dimension $D \ge 3$. That it is admitted on the line and in the
plane rests on the computed value $w_2 \approx 5.24$." `appendix-verification.tex:326–327`, p. 80:
"The other inequality of the example, $4 \le w_2$, is the computed one."
`03-isotropic.tex:1444–1446`, p. 28: "With the computed values $w_3 \approx 3.21 < 4 \le w_2
\approx 5.24$, so $F^{(4)}$ is admitted on the line and in the plane and not in space." Against:
the Sources row, `sources.tex:193–195`, p. 33, "The family, the members $w = 8$ and $w = 4$ as
witnesses in dimensions $1$ and $2$ … \[10, Lem. 4.12 and Rem. 4.10\]", and
`02-line-papers.tex:322–323`, p. 10, "The cone paper proves that the first two inclusions of the
chain are strict \[10, Lem. 4.12(3)\]".

**The source, at the page images.** Cone paper, Lemma 4.12, p. 38–39: the datum is the same
family, $k^{(c)}_{\mathrm I}(u) = u^{-1/2} + c\,\mathbf 1_{[1,2]}(u)$. Clause 2: "For $c = 4$ the
profiles $k^{(4)}_1$ and $k^{(4)}_2$ are nonincreasing on $(0,\infty)$ and $k^{(4)}_3$ is not".
Clause 3: "$F^{(8)} \in \mathcal{A}_1 \setminus \mathcal{A}_2$ and
$F^{(4)} \in \mathcal{A}_2 \setminus \mathcal{A}_3$". Its proof, p. 82: the derivative of the
polar profile is nonpositive at $r$ exactly when
$c\,z^m(e^{-z} - 2^{-d/2}e^{-z/2}) \le \tfrac12\Gamma(m)$, $z = \tfrac12r^2$ (A.2), which is this
paper's criterion (A.20); and "At $d = 2$, where $m = \tfrac32$, $\lambda = \tfrac12$ and
$\Gamma(m) = \sqrt\pi/2$, the right side is $3^{3/2}5^{-5/2}$ …, so at $c = 4$ the criterion holds
at every $z$ as soon as $4 \cdot 3^{3/2}5^{-5/2} \le \sqrt\pi/4$, that is … $6912/3125 \le \pi$,
which holds". With Definition 3.20 that is $4M_2 \le \tfrac12\Gamma(\tfrac32)$, that is
$4 \le w_2 = \Gamma(\tfrac32)/(2M_2)$. The script (block 14) reproduces it:
$M_2 = 0.08452693 \le 3^{3/2}5^{-5/2} = 0.09295160$, $4 \times 0.0929516 = 0.3718 \le 0.4431$, so
$w_2 \ge 4.767$ by the cone paper's elementary bound alone, and $w_2 = 5.2423$ computed.

So both halves of the example are proved: $w_3 < 4$ in Lean (`threshold_three_lt`), $4 \le w_2$
in print in the cone paper. Only the value $5.24$ is computed. The paper's own source comment
(`01-introduction.tex:601–606`) says "The other half, $4 \le w_2$, needs an upper bound of $M_2$,
which the development does not have": true of the Lean, and the cone paper has that bound.

**Fix.** p. 6: "Of that example Lean has $w_3 < 4$, so that $F^{(4)}$ is admitted in no dimension
$D \ge 3$. That it is admitted on the line and in the plane, which is $4 \le w_2$, is proved in
print in the cone paper (\[10, Lem. 4.12(2) and (3)\]); the value $w_2 \approx 5.24$ is
computed." p. 80: "The other inequality of the example, $4 \le w_2$, is proved in print in the
cone paper: the proof of \[10, Lem. 4.12(2)\] shows the criterion (A.20) at $w = 4$ and $d = 2$
for every $z$." p. 28: "With the computed values $w_3 \approx 3.21 < 4 \le w_2 \approx 5.24$" may
stand, with "(both inequalities are proved: the first in the formal development, the second in
\[10, Lem. 4.12(2)\])".

**Touches.** Prose (§ 1.1, Appendix B, § 3.4). **Disposition.** Fix.

## 15. D R6, R7: Theorem A.15 — CONFIRMED in its three parts

**The paper.** `appendix-isotropic.tex:3006–3037`, p. 70, the lead and the theorem; proof
pp. 70–73.

1. *Clause (1) duplicates Theorem 3.21(1)/(4).* Yes, and the lead says so (`:3006–3009`): "Its
   clause (1) is Theorem 3.21(1) at the dimensions $d$ and $d + 1$ … and the strict inclusions of
   its clause (3) are the last assertion of clause (4) of that theorem." The proofs are the same
   argument written twice: "Clause (1), membership" and "Clause (1), exclusion"
   (`:3058–3096`, pp. 70–71) against "Clause (1), $w \le w_D$ gives membership" and "Clause (1),
   $w > w_D$ excludes it" (`:3295–3333`, p. 74), with the same lemmas, the same use of C3(ii)
   and C3(iii), and the same argument on points $u_n \downarrow r$, $v_n \uparrow s$.
2. *Clause (2) is about a bound nothing uses.* Yes, in the paper's words (`:3012–3014`): "Its
   clause (2) concerns the bound $6 + 4\sqrt2$ under which the cone paper states that $F^{(w)}$ is
   admissible. No other statement of this paper uses that bound." (D asks which declaration
   carries the clause: `filtration_witness_exists`, whose first conjunct is
   `threshold 2 < 6 + 4 * Real.sqrt 2`, `FiltrationStrict.lean:421–426`. The clause is
   machine-checked.)
3. *The reproof of $\mathcal{A}_\infty = \mathcal{S}$ is the cone paper's route.* Yes. Cone paper,
   proof of Prop. 4.9(4), pp. 35–36 (text layer): the radial theorem makes $f(\sigma) = F(\sqrt{2\sigma})$ a
   Bernstein function; for $0 < c < 1$ the exponent $F(|\xi|) - F(c|\xi|)$ of the residual is
   negative definite on every $\mathbb{R}^d$, so "By the radial theorem, applied as in clause (3),
   $g_c$ is a Bernstein function"; then laws $T$ and $R_c$ on the half-line by complete
   monotonicity, $T$ self-decomposable, and "By the one-dimensional characterization of
   self-decomposable Lévy measures — \[50\], Corollary 15.11, p. 95 … its Lévy measure is
   $k_{\mathrm I}(u)\,du/u$ on $(0,\infty)$ with $k_{\mathrm I}$ nonincreasing". This paper's
   route (`:3142–3178`): the same $f$ and $g_c$, the same two applications of C6, then the
   measures directly, $m = D_{c^2}m + m_c$ by step (b), $D_\lambda m \le m$, and step (c). The
   three steps (a), (b), (c) replace what the cone paper cites: the infinite divisibility of the
   residual, Bernstein's theorem for $e^{-f}$, and Sato's Corollary 15.11. The blueprint says
   exactly this, in the annotation of `lem:filtration-top`
   (`blueprint/src/parts/03-isotropic.tex:3911–3918`, "What the route saves"). The paper's
   sentence (`:3128–3133`) says that "the formal proof does not use that proposition. It derives
   the identification from Schoenberg's radial theorem, C6, by the route that follows", and not
   whose route it is.

**What the paper can do without changing the node `thm:filtration-strict`.**

- *(i) Print the existing node `lem:filtration-top` in its place.* The blueprint already has the
  statement "$\mathcal{A}_\infty = \mathcal{S}$" as a node of its own
  (`blueprint/src/parts/03-isotropic.tex:3895–3900`,
  `\lean{classAInf_of_classS, classS_of_classAInf, filtration_top}\leanok`), with the three steps
  as its children. The paper prints that lemma with the route of pp. 71–73 as its proof, and
  `thm:filtration-strict` is no longer printed, as its children are not. One sentence under
  Theorem 3.21 says that the strictness is also in the development window by window. This removes
  the lead, the statement and the proofs of clauses (1) and (2) and of the strictness in clause
  (3), `:3006–3112`, about a page and a third, and with them the duplication. What moves with it:
  the inventory of Appendix B (one row out, one in, by `gen-verification-table.py`), the row of
  Table 3 (C6 on the lemma), the sentence and the two lines of the printed Lean block that name
  `filtration_strict`, the reference at the end of the proof of Theorem 3.21 ("part of
  Theorem A.15(3)", to be pointed at Proposition 3.19(1) in a pinned copy), and the references to
  Theorem A.15 on pp. 29 and 68. C6 keeps a printed statement that uses it.
- *(ii) Keep the theorem's number and print clause (3) only*, as a deliberately edited and pinned
  copy of the node, with the inventory row left over-inclusive. The paper has both devices: the
  pinned copy of `def:filtration-thresholds`, and the row of Lemma 3.3, which holds three
  declarations "for clauses that this paper does not print".

Either way, one sentence at `:3128–3133`: "The route is that of the cone paper's proof of
\[10, Prop. 4.9(4)\], which applies the same theorem to the same two functions; steps (a), (b) and
(c) take the place of three facts that proof cites, the last being the description of a
self-decomposable law on the half-line (\[38\], Cor. 15.11, p. 95)."

**What would need the blueprint.** Removing or splitting `thm:filtration-strict` itself: it is a
headline node of `linkage.toml` (`filtration_strict`, `filtration_witness`, `filtration_top` are
pinned in the guard), the hub may cite its label, and `thm:separating-family-critical-values`
cites it for the nesting. Neither option above needs it.

**Touches.** Prose and the appendix's generated list; the paper's copy of one shared proof (a
pin). No blueprint statement, no Lean. **Disposition.** The author decides between (i), (ii) and
leaving it; recommended (i), with the sentence on the route in any case.

## 16. D's count: strictness four times, the Cin exclusion twice — CONFIRMED

**The strictness of every inclusion $\mathcal{A}_{d+1} \subsetneq \mathcal{A}_d$.**

| statement | where | proof | by |
|---|---|---|---|
| Proposition 3.19(2) | `03-isotropic.tex:1343–1347`, p. 27 | `appendix-isotropic.tex:2526–2541`, p. 63 | the step datum |
| Theorem 3.21(4), last sentence | `03-isotropic.tex:1426–1431`, p. 28 | `appendix-isotropic.tex:3341–3350` with `:3295–3333`, p. 74 | the separating family |
| Theorem A.15(1), with (2) | `appendix-isotropic.tex:3025–3030`, p. 70 | `:3045–3096`, pp. 70–71 | the separating family, the same proof text |
| Theorem A.15(3) | `:3031–3035`, p. 70 | `:3098–3112`, p. 71 | from (1) and (2) |

So two independent proofs (the step datum; the family), the second printed twice, and a fourth
statement that collects. Corollary A.9(2) (`:2569–2579`, p. 64) is a fifth reading of the first,
as the non-membership of $\Omega_d(\tau|\cdot|)$.

**The Cin rays.** Proposition 3.19(3) (`03-isotropic.tex:1348–1349`, p. 27; proof
`appendix-isotropic.tex:2543–2557`, pp. 63–64, from clause (2) and the nesting), and Theorem A.16
(`:3448–3454`, p. 75; proof p. 76, by one projection to the line, without the nesting). The second
is declared as a second proof ("The last theorem is clause (3) of Proposition 3.19, stated by
itself", `:3441–3443`).

**And $\mathcal{A}_\infty = \mathcal{S}$** twice: Proposition 2.6(3), cited from the cone paper,
and Theorem A.15(3), reproved (item 15).

**Fix.** Item 15 removes one statement and one proof text. Theorem A.16 is a genuinely different
proof and is short; it can stay as it is or become "a second proof of Proposition 3.19(3)", which
would change a printed node's form. **Disposition.** With item 15; for Theorem A.16, the author
decides, and leaving it is the cheaper choice.

---

## 17. Other assertions of an error or a gap in A to D

| # | where | assertion | verdict | note |
|---|---|---|---|---|
| a | B § 2, on p. 29 | "a residual of the Matérn law is not even infinitely divisible in general" | REFUTED | every stage is infinitely divisible (the head of this record, item 12(1)); the stage is not self-decomposable |
| b | B S2 | the continuity of a gauge is "used without comment" on p. 37 | PARTLY | p. 37 gives the reason ("and so is $\chi$, an increasing bijection of $[0,\infty)$"); $\chi(0) = 0$ is used on p. 16 without one. A parenthesis at the definition, p. 8, "(hence continuous, with $\chi(0) = 0$)", is harmless. Prose |
| c | B S4 | the drift: "$Q\gamma = \gamma$ for all $Q$ forces $\gamma = 0$ when $d \ge 2$ (and at $d = 1$ the drift is removed by the moduli step)" | PARTLY | $Q = -I$ gives $\gamma = 0$ in every dimension, $d = 1$ included. The printed moduli step is correct and needs no change |
| d | B S7 | p. 18, "For $d \ge 2$ that exponent is not a member of a Cin ray" has no reference | CONFIRMED | `03-isotropic.tex:577–579`; it follows from $\mathcal{A}_d \subseteq \mathcal{A}_2$ and Proposition 3.19(3). Add "(Proposition 3.19(3))". Prose |
| e | C R2 | p. 24, "the peak of the opening" is undefined | CONFIRMED | `03-isotropic.tex:1114–1115`; "opening" occurs nowhere else in the prose. Fix: "The limits for the mass of a ball give the peak of the record of a point source, the mass of the recording cell divided by its volume." Prose |
| f | C S5 | p. 21, derivative filters "continuous functions" could be "bounded continuous" | CONFIRMED | Theorem 3.12(2) gives derivatives tending to $0$ at infinity. Optional. Prose |
| g | A § 2 | "The proofs given here are written out from the seven cited facts" (p. 4; `sources.tex:65–66`) while the printed proof of Theorem 3.6 cites Theorem 2.3 | PARTLY | true of the formal proofs; the printed proofs also use the statements restated in § 2, as § 2 says. Fix: "from the seven cited facts of § 2.6 and the statements restated in § 2". Prose |
| h | A S4 | § 1.1 does not say why the classification here rests on fewer cited facts than the line paper's | CONFIRMED | the line paper's rests on Bochner's theorem and the symmetric Lévy–Khintchine representation (its § 1.1, text layer); here $\mathcal{A}_d$ is defined through the existence of the law. One sentence. Prose; the author decides |
| i | A S2 | § 1.1 says a definition is "listed as machine-checked", Appendix B says "formalised in Lean" | CONFIRMED | `01-introduction.tex:519–520` against `appendix-verification.tex:102ff.`. Wording. Prose |
| j | A S1 | abstract, "ask only that the stages compose": the axioms ask more | CONFIRMED | wording; "ask of the cascade only that" costs words the abstract does not have. The author decides |
| k | A R1 | "Proposition 2.6(3) is cited at least nine times" | PARTLY | five times with the clause, once without (item 6) |
| l | A R7 | the repository is private, so a referee cannot run the verification | not mathematics | a release decision; the author's |
| m | A R2, R3, R4, R5; C R3 | the Bessel scale space, Alvarez et al., Felsberg and Sommer, Iijima, the time-causal literature are not cited | the literature record's | checked here only: the line paper cites the Bessel scale space, Alvarez et al. and the Poisson scale space (text layer), and `paper-iso/references.bib` has none of them |
| n | D R3 | "Table 2 cites Gneiting only for the strictness in general"; Corollary A.9(2) needs its classical source | PARTLY | the Sources row of Proposition 3.19 and Corollary A.9 cites Daley and Porcu, Lemma 12, p. 1822, "for the last assertion of Corollary A.9(2)" (`sources.tex:186–189`); the note has the lemma at the page image, "$\Omega_d \in \Phi_d \setminus \Phi_{d+1}$". Whether Schoenberg (1938) is added is the literature record's |
| o | D § 5 | which Lean declaration carries Theorem A.15(2) | REFUTED as a gap | `filtration_witness_exists` (item 15) |
| p | D § 2, p. 3 | "decrease like $d^{-1/2}$" cites Theorem 3.21(3), which gives the limit | REFUTED | the limit $\sqrt d\,w_d \to \sqrt\pi$ is the order |
| q | D S4, A § 2 | "cut off sharply" for a jump of the profile (pp. 3, 27) | PARTLY | a jump need not be a cut-off to zero. "has a jump at some radius". Prose |
| r | D S1 | p. 68, "This paper does not explain the coincidence" | CONFIRMED | `appendix-isotropic.tex:2854–2855`. Both constants are $(1 - 2^{-1/2})^2 = \tfrac32 - \sqrt2$: in the cone paper from $2^{-d/2}$ at $d = 1$ (p. 82, "$(1 - 2^{-1/2})^2/2$"), here from the ratio $2^{-(d+1)/2}/2^{-d/2}$ in $(1 - q/\sqrt2)^2 - (1-q)(1-q/2) = (\tfrac32 - \sqrt2)q$. Fix: that sentence, or drop the paragraph. Paper prose (not in the blueprint) |
| s | D, end of § 4.1 | p. 29, "The critical values have no closed form" is an assertion | CONFIRMED | `03-isotropic.tex:1449`; nothing proves it. Fix: "The critical values are not given in closed form: $M_d$ is the maximum of a function whose stationary point solves a transcendental equation." Prose |
| t | D § 3, "small points a reader must supply" (pp. 62, 63, 64, 71, 74) | steps left to the reader | REFUTED as gaps | D itself: "None that break a proof". Each was read: the a.e. uniqueness on p. 62, the finiteness of $k'$ on p. 63, $u_n < v_n$ for large $n$ on pp. 71 and 74 are as D says, immediate |

---

## Closing table

| item | finding | verdict | the fix touches | proposed disposition |
|---|---|---|---|---|
| 1 | B R1, dominating function, p. 37 | REFUTED | nothing | decline: the PDF prints the factor; blueprint and Lean have it |
| 2 | B R2, "Definition 3.20", p. 39 | CONFIRMED | prose of the paper's copy of a shared proof (a pin) | fix: "Proposition 2.6" |
| 3a | B R3, Prop. 8.5 covers $\alpha < 1$ only | CONFIRMED | prose | fix: the drift case, Cor. 7.4 and Rem. 7.5 |
| 3b | B R3, credit for "GGC are self-decomposable" | PARTLY | prose; one bibliography entry | fix: Bondesson's monograph, § 3.1, p. 30, for the inclusion; Halgreen and Bondesson 1978 for the membership |
| 4 | B R4, § 4 "their kernels" | CONFIRMED | prose (pp. 29 and 4) | fix |
| 5a | B S3, the bijection as a corollary | CONFIRMED (correct) | prose, or blueprint and Lean | the author decides; recommended: two sentences of prose |
| 5b, 5c | B S1, Lemma 3.5 from Lemma 3.3 | CONFIRMED (correct) | the blueprint's proof (prose, one `\uses` edge); not the Lean | the author decides |
| 6 | A R1, Proposition 2.6 renumbers | CONFIRMED | prose (title and one sentence) | fix |
| 7 | A R8, a Gaussian part gives a smooth density | CONFIRMED | prose (p. 20 and § 1.1) | fix as prose; a clause of Theorem 3.12 is not needed |
| 8 | A R6, witnesses and probes not in the report | CONFIRMED | the guard and a script, the report file, prose of Appendix B | fix, with the next Lean run |
| 9 | A R9, D R5, "admitted" in the abstract; the sentence on p. 27 | CONFIRMED; PARTLY | prose | fix both |
| 10 | C R1, "previous paragraph", p. 47 | REFUTED | nothing | decline: the PDF prints "next" |
| 11a | C S6, $e^{-C_k}$ for $e^{-2C_k}$ | CONFIRMED (correct) | a shared statement, the blueprint, the Lean | decline: not cheap, superseded by Proposition 3.17(3) |
| 11b | C S4, "$c > 0$" is nontriviality | CONFIRMED | prose | fix (one sentence), or leave |
| 11c | C S3, $B_c$ is the constant of Cygan et al. | CONFIRMED (Thm. 9 is the one at the origin) | prose (Sources row) | fix |
| 12 | D R1, the stages | CONFIRMED, and complete | a new statement: blueprint; Lean if machine-checked; prose of § 1, § 4, § 4.1 | fix: state it; the form is the author's decision |
| 13 | D R2, the step witnesses | CONFIRMED; the last dimension is $d + 2$ | a new statement in print: blueprint; prose of § 3.4 and § 4.1 | fix: the question leaves § 4.1; proposition or paragraph, the author decides |
| 14 | D R4, $4 \le w_2$ | CONFIRMED | prose (§ 1.1, Appendix B, § 3.4) | fix |
| 15 | D R6, R7, Theorem A.15 | CONFIRMED | prose, the generated list, one pinned proof copy | the author decides; recommended: print `lem:filtration-top` in its place, and name the route |
| 16 | D, the count of repetitions | CONFIRMED | as item 15 | with item 15 |
| 17 | twenty further assertions | 8 CONFIRMED, 6 PARTLY, 4 REFUTED, 1 not mathematics, 1 the literature record's | prose | as listed |

**For the hub.** Two findings are new to the programme and belong in its notes when the author
has decided their form: the atom $(\chi(s)/\chi(t))^c$ of a stage (item 12), and the dimensions
$D \le d + 2$ in which a step exponent stays infinitely divisible (item 13). The second closes the
entry that the comment of `04-conclusion.tex` and the round-1 record kept as numerical evidence.
