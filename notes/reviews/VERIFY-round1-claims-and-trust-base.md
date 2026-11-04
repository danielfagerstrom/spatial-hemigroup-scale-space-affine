# Verification of the external review, round 1: the claims as worded, the imaging reading, the trust base, the structure

**What this is.** Article-kit's `docs/PROCESS.md` § 9 asks that every finding of an external review
be verified against the text before anything changes. This record verifies one shard of
`review-content-iso-review-1-GPT-6.1-Sol-Ultra.md`: its § 1, its § 2 (but for the points listed
below), its § 5 and § 7, required changes 4, 12 and 13, and suggestions 3, 4, 6, 7 and 8. Nothing
in the paper, the Lean sources or the blueprint was edited, and nothing was committed.

**Against what.** The worktree `spatial-hemigroup-affine-q0417`, branch `queue/q-0423`, at
`8e63949` (2026-10-12). `paper-iso/` and `Formalization/` are identical there to the tag
`iso-review-1` (`1cbcee1`): `git diff iso-review-1 HEAD -- Formalization paper-iso` is empty. File
and line references are to that tree. Page numbers are the printed pages of
`review-build-iso-review-1.pdf` (61 pages), found by `pdftotext` page by page.

**Not verified here** (other agents of the round): the optimality sentence after Proposition 3.16,
the slopes of Figure 1, the stable endpoint, C6, the Schoenberg route, the Borel map and the
Gaussian case of C5, Proposition 2.7, the upper bound's constant, the short strictness proof, the
Student-t item, the two open problems, and the prior art (the Hankel theorems, the Bessel
potentials). Where an item below depends on one of them, it says so.

**Verdicts.** CONFIRMED, PARTLY or REFUTED for a factual claim about the text or about the
mathematics of an interpretation; JUDGEMENT for an editorial choice.

**Two constraints that every disposition meets.** The abstract is at its limit of 250 words. The
main text ends two lines short of the foot of p. 30 (29.96 pages against the author's budget of
30). A printed page of prose holds 46 to 48 lines, about 55 lines of the `.tex` source. So a
sentence added to the abstract or to §§ 1 to 4 has to be paid for; § 8 below gives a balance.

---

## 1. The abstract's sentence on the rate, against the boundary case c = d — PARTLY

**The referee** (review § 2, "Rate at the centre"): Proposition 3.15 proves what it states; at
`c = d` the result is an equivalence with a law-dependent truncated integral, with a logarithmic
lower bound, and not `q(s) ~ C log(1/s)`; the body keeps the distinction and the abstract does not.

**The statement.** Proposition 3.15 (`03-isotropic.tex:1025-1055`, p. 25). Clause (1), `c < d`:
`q(s) / (R(d,c) s^{-d} \widehat\mu(e/s)) -> 1`. Clause (2), `c = d`:
`q(s) / ((2\pi)^{-d} I(s)) -> 1` with `I(s) = \int_{|\xi| \le 1/s} \widehat\mu`, and
`I(s) \ge |S^{d-1}| e^{-13d/4 - 2C_k} \log(1/s)`.

**The referee's mathematics is right.** `I(s) = |S^{d-1}| \int_0^{1/s} L(\rho) d\rho/\rho` with
`L(\rho) = \rho^d \widehat\mu(\rho e)` slowly varying and bounded below on `[1,\infty)`. `L` need
not be bounded above. For the polar profile `k_d(r) = d - 1/\log(e/r)` on `(0,1)`, which is
nonincreasing with limit `d` at zero, `\int_r^1 (d - k_d(u)) du/u = \log\log(e/r)`, so `L(\rho)`
is of the order of `\log\rho` and `I(s)` of the order of `\log^2(1/s)` (a check of this
verification, from `F_d(\rho e) = c\log\rho - \int_{1/\rho}^1 (c - k_d(u)) du/u + O(1)` for a
bounded profile). The only law-free statement at `c = d` is the lower bound. (For `c < d` too the comparison function carries the law, through
the slowly varying factor of `\widehat\mu(e/s)`; the law-free part is the constant `R(d,c)`.)

**Every place where the claim is made.**

| place | text | reading |
|---|---|---|
| `main.tex:165`, p. 1 | "Otherwise a point source is recorded as a spike, whose rate is given with its constant." | compressed: one phrase for two forms |
| `01-introduction.tex:227-230`, p. 3 | "When $c \le d$ the spike has a rate, which Proposition 3.15 gives with its constant: for $c < d$ the density at distance $s$ from the centre is asymptotic to a constant times $s^{-d}$ times the transform at the frequency $1/s$." | announces `c \le d`, describes `c < d` only |
| `01-introduction.tex:353-356`, p. 4 | "When $c < d$ the density ... is asymptotic to an explicit constant times $s^{-d}$ times the transform at the frequency $1/s$, and when $c = d$ it grows at least like $\log(1/s)$." | keeps the distinction |
| `03-isotropic.tex:753-754`, Table 3, p. 21 | "The equivalence with its constant, at one kernel, for the class, $c \le d$." | compressed |
| `03-isotropic.tex:799-803`, p. 22 | "for $c < d$ the density at the point $x$ is asymptotic to an explicit constant times $|x|^{-d}\,\widehat\mu(e/|x|)$ ..., and at $c = d$ it grows at least like $\log(1/|x|)$." | keeps the distinction |
| `03-isotropic.tex:808-809`, p. 22 | "an asymptotic equivalence with its constant, at one kernel, for the whole class" | compressed |
| `03-isotropic.tex:1019-1020`, p. 24 | "At $c = d$ the transform is at the edge of integrability, and its integral over the frequencies up to $1/s$ takes the place of its value." | exact |
| `03-isotropic.tex:1065-1068`, p. 25 | "the density at distance $s$ is asymptotic to that integral cut at the frequency $1/s$, which grows at least like $\log(1/s)$." | exact |
| `04-conclusion.tex:114-116`, p. 29 | "the rate at which the density of such a kernel grows at its centre when $c \le d$, for $d \ge 2$, as an asymptotic equivalence with its constant" | compressed |

**Verdict.** The referee's description of the text is accurate. No sentence is false: at `c = d`
there is an equivalence, and its constant `(2\pi)^{-d}` is given. Four places (the abstract,
Table 3, the tier paragraph of § 3.3, the conclusion) fold the two forms into "with its constant",
which a reader takes for `C s^{c-d}` or `C \log(1/s)`. The presentation review makes the same
point (its item 3).

**Disposition proposed.**

- Abstract, same length (16 words for 16):
  `Otherwise a point source is recorded as a spike, at a rate given through the transform.`
- § 1, `01-introduction.tex:227-230`: after the sentence on `c < d` add
  `At $c = d$ it is asymptotic to $(2\pi)^{-d}$ times the integral of the transform over the frequencies up to $1/s$, which grows at least like $\log(1/s)$.`
- Table 3, `03-isotropic.tex:753`:
  `The equivalence at one kernel, for the class: with the constant $R(d,c)$ for $c < d$, with the truncated integral of the transform at $c = d$.`
- § 3.3, `03-isotropic.tex:808-809`:
  `an asymptotic equivalence at one kernel, for the whole class, with its constant for $c < d$.`
- § 4, `04-conclusion.tex:114-116`:
  `... when $c \le d$, for $d \ge 2$, as an asymptotic equivalence: with a power of the distance and an explicit constant for $c < d$, with a truncated integral of the transform at $c = d$.`

The wording of what is new about the rate is the prior-art agent's; these sentences change again
if the Hankel antecedents stand.

---

## 2. The imaging interpretation — (a) PARTLY, (b) CONFIRMED

### 2(a) What an unbounded kernel does to a sampled or filtered image — PARTLY

**The referee's four statements, checked.**

1. *An unbounded density is the ideal point response.* True by construction: the record of a point
   mass at the origin is `\mu_{0,t}` itself.
2. *`\|p * f\|_\infty \le \|f\|_\infty` for bounded `f`.* True for every probability measure:
   `|(\mu * f)(x)| \le \int |f(x-y)| \mu(dy) \le \sup|f|`. It is positivity with mass
   preservation, axioms (A4) and (A5), and does not see `c`.
3. *Pixel masses are finite.* True, and the paper has more: `\mu(\{|x| < r\}) \le A_\beta r^\beta`
   (Proposition 3.17(1)), so the mass of a cell tends to zero with the cell. What diverges is the
   average over the cell: for a radially nonincreasing `q` with `q(0+) = \infty`, the average of the
   density over the ball of radius `r` is at least `q(r)`, and for `c < d` it is asymptotic to
   `(d/c) R(d,c) r^{-d} \widehat\mu(e/r)` by Proposition 3.15(1).
4. *The value of a density at a point is not invariant; the invariant statement is that no
   representative is locally bounded.* True, and it is how the theorem is stated: clause (4) of
   Theorem 3.12 says that there are no `\delta` and `M` with `\mu(B) \le M|B|` for Borel
   `B \subseteq \{|x| < \delta\}`, clauses (3) and (4) say "no representative is bounded near the
   origin", and clause (5) says "has a density bounded near the origin ... exactly when `c > d`"
   (`03-isotropic.tex:863-881`). With Proposition 3.14 the invariant statement is also
   `q(s) \to \infty` as `s \downarrow 0` for the radially nonincreasing version.

**Every sentence of the kind**, with a reading. No sentence of the paper says that a bounded image
is given an infinite value. The sentences are about a point source. Two of them say "no finite
value to sample", which is true of the ideal point response read pointwise and says nothing of
what the referee's points 2 and 3 add.

| place | text | wrong, loose or fine |
|---|---|---|
| `main.tex:165`, p. 1 | "Otherwise a point source is recorded as a spike" | fine ("spike" is defined on p. 20) |
| `main.tex:166-167`, p. 1 | "a kernel bounded on the line can have a spike in the plane" | fine |
| `01-introduction.tex:181-184`, p. 2 | "The kernel from scale zero is the record of a point source. If it is unbounded at its centre, a point is recorded as a spike and not as a blob of finite height, and the record has no finite value to sample there." | loose: the last clause |
| `01-introduction.tex:224-226`, p. 3 | "kernels from scale zero that are bounded on the line and have a spike in the plane" | fine |
| `03-isotropic.tex:141-143`, p. 14 | "A kernel from scale zero with no Gaussian part is bounded at its centre exactly when the power $c$ ... exceeds $d$" | fine (shorthand for clause (5)) |
| `03-isotropic.tex:690-693`, p. 20 | "whether a point source is recorded as a blob of finite height or as a spike, a density that is unbounded at the centre. ... so a spike is there at every scale." | fine; the place for the missing qualification |
| `03-isotropic.tex:792-793`, p. 22 | "the value of a density at its centre is $(2\pi)^{-d}\int_{\RR^d}\widehat\mu(\xi)\,d\xi$ when the transform is integrable" | loose: "of the continuous density" |
| `03-isotropic.tex:798-799`, p. 22 | "When $c \le d$ the kernel has a spike. Its density is radially nonincreasing, so the spike is at the centre and nowhere else" | fine |
| `03-isotropic.tex:1004-1005`, p. 24 | "Since $q$ is finite at every positive radius, an unbounded density is unbounded at the centre only." | fine |
| `03-isotropic.tex:1065-1066`, p. 25 | "The value at the centre, $(2\pi)^{-d}\int\widehat\mu$ in the formula of the opening, is infinite" | loose |
| `04-conclusion.tex:139-144`, p. 30 | "Where $c \le d$ the kernel has no finite value to sample at its centre. Its density is largest there and unbounded (Proposition 3.14), and what is finite is the mass of a small ball round the centre, which Proposition 3.15 gives." | loose: the first sentence; the second already has the referee's point 3 |

**Verdict.** The referee's mathematics is confirmed. The charge that the paper "overstates" is
partly right: nothing printed is false, two sentences are loose, and the paper never says what
an unbounded kernel does *not* do to a bounded image.

**Disposition proposed** (about six lines added to the main text).

- `01-introduction.tex:182-184`:
  `The kernel from scale zero is the record of an ideal point source. If no version of its density is bounded near the centre, the point is recorded as a spike and not as a blob of finite height: the record has no peak value, and its average over a cell round the centre grows without bound as the cell shrinks.`
- `03-isotropic.tex:693`, after "so a spike is there at every scale.":
  `This is a statement about the response to an ideal point source. The record of a bounded image $f$ is bounded by $\sup|f|$ whatever the kernel is, since the kernel is a probability measure, and the mass that a kernel gives to a cell is finite. What a spike takes away is a peak value of the point response that does not depend on the size of the cell.`
- `03-isotropic.tex:792-793`: `the value at the centre of a continuous density is ...`.
- `04-conclusion.tex:141-144`:
  `Where $c \le d$ no version of the density is bounded near the centre: the density is largest there and tends to infinity (Proposition~\ref{prop:isotropic-radial-monotone}). What is finite is the mass of a small ball round the centre, which Proposition~\ref{prop:origin-rate-d} gives, so the point response sampled on cells has a peak that grows without bound as the cells shrink. The record of a bounded image stays bounded by the bound of the image.`

### 2(b) A derivative filter "needs" N continuous derivatives — CONFIRMED

**The two sentences.**

- `03-isotropic.tex:789-791`, p. 22: "The kernel has a bounded density exactly when $c > d$, and
  $N$ continuous derivatives when $c > d + N$, which is what a derivative filter of order $N$ built
  from the kernel needs (Theorem 3.12)."
- `04-conclusion.tex:144-146`, p. 30: "A derivative filter of order $N$ built from the kernel needs
  $N$ continuous derivatives of the density, which it has when $c > d + N$ (Theorem 3.12(2))."

The other sentences on derivatives state the sufficient condition and are fine:
`01-introduction.tex:221-222` (p. 3), `03-isotropic.tex:845-848` (the theorem's clause (2), "If
$c > d + N$ then ..."), `03-isotropic.tex:896-897`, `04-conclusion.tex:148-150` and `183-185`.

**The referee's mathematics is right, and the counterexample is in the paper's own class.**

- The Matern kernel of index 1 on the line has transform `(1 + \omega^2/2)^{-1}`. By the closed
  form (3.7) at `d = 1`, `\gamma = 1`, with `K_{1/2}(z) = \sqrt{\pi/(2z)} e^{-z}`, its density is
  `2^{-1/2} e^{-\sqrt2 |x|}`, the Laplace kernel. Here `c = 2 = d + 1`, so clause (2) of Theorem
  3.12 gives `N = 0` and no more, and the density is not `C^1`. Its weak derivative
  `-\mathrm{sgn}(x) e^{-\sqrt2|x|}` is integrable, of norm `\sqrt2`. So the derivative filter of
  order 1 is convolution by an integrable function, bounded on `L^1` and on `L^\infty`.
- More is true, by a computation of this verification from three statements of the paper. It is
  not in the paper and is not machine-checked; it is given to settle the verdict and is not
  proposed for print. On the line a symmetric density that is nonincreasing on `(0,\infty)` has
  total variation `2q(0+)`, so its distributional derivative is a finite measure exactly when the
  kernel is bounded, that is when `c > 1`, not when `c > 2`. For `d \ge 2`, with `p(x) = q(|x|)`
  and `q` nonincreasing (Proposition 3.14), integration by parts gives the total variation of the
  gradient as `(d-1)|S^{d-1}|\int_0^\infty q(r) r^{d-2} dr = (d-1)\int |x|^{-1}\mu(dx)`. By the
  lower bound `q(r) \ge c_1 r^{c-d}` (Propositions 3.16 and 3.17(3)) and the upper bound
  `q(r) \le A_\beta V_d^{-1} r^{\beta-d}` for `\beta < c` (Proposition 3.17(2)), this is finite
  exactly when `c > 1`. So the Matern kernel of index 3/4 in the plane, the paper's example of a
  spike (`c = 3/2`), has a gradient that is a finite measure, while the paper's sentence asks
  `c > 3` of it.
- Theorem 3.12(2) is a sufficient condition for a classical `C^N` density whose derivatives vanish
  at infinity. It does not give the integrability of those derivatives, so it does not by itself
  give an operator bound for the derivative filter either. The referee says this too.

**Verdict.** Both sentences are wrong as statements of necessity. The condition is sufficient.

**Disposition proposed.**

- `03-isotropic.tex:789-791`:
  `The kernel has a bounded density exactly when $c > d$, and a density with $N$ continuous derivatives when $c > d + N$, so that the derivative filters of order up to $N$ built from the kernel are then continuous functions that vanish at infinity (Theorem~\ref{thm:origin-boundedness-d}).`
- `04-conclusion.tex:144-146`:
  `When $c > d + N$ the density has $N$ continuous derivatives, so the derivative filters of order up to $N$ built from the kernel are continuous functions (Theorem~\ref{thm:origin-boundedness-d}(2)). The condition is sufficient: the paper does not determine when a derivative filter exists in a weaker sense.`

Whether the weak-derivative threshold `c > 1` should become a statement of the paper is a new
result and a blueprint question, for the author. It would make the open problem "The derivatives"
(`04-conclusion.tex:183-187`) sharper.

---

## 3. The categorical sentences on the heat-kernel literature — CONFIRMED on the paper's own evidence

**The sentences, with all their repetitions.**

- `01-introduction.tex:288-293`, pp. 3-4: "In $\RR^d$ the neighbouring results are not about one
  kernel. With a law of exponent $F$ the literature studies all the laws with the transforms
  $e^{-\tau F}$, $\tau > 0$, the laws at the times $\tau$ of a Levy process. The kernel is the law
  at $\tau = 1$, and the transform at time $\tau$ falls off at the power $\tau c$. So a result for
  small $\tau$ is about the kernels with a small $c$, and a limit $\tau \to 0$ says nothing about
  one kernel."
- `03-isotropic.tex:816-823`, p. 22: "Table 3 needs a dictionary, because the literature on $\RR^d$
  does not study one law. With a law of exponent $F_d$ it studies all the laws with the transforms
  $e^{-\tau F_d}$, $\tau > 0$. ... So a result for small $\tau$ is a result for the kernels with a
  small $c$, and a limit $\tau \to 0$ says nothing about one kernel."
- The caption of Table 3, `03-isotropic.tex:777-778`: "A law in print at time $\tau$ is a kernel
  with $\tau c$ in place of $c$." This one is a dictionary and is fine.

The referee quotes them accurately (pp. 4 and 22; the first begins at the foot of p. 3).

**"Does not study one law" is contradicted inside the paper.** The same paragraph of § 1 says that
Grzywny, Ryznar and Trojan have, "for one family, the geometric stable laws, the threshold and the
order of the spike at every $\tau$" (`01-introduction.tex:296-298`). Table 3 has "for the geometric
stable laws, at every $\tau$" and "at $\tau = 1$ also" Mimica (`03-isotropic.tex:751-752`,
`760-761`). A result at every `\tau` is a result about the one law at `\tau = 1`. So the sentence is
too categorical whatever the prior-art agent finds.

**"Says nothing about one kernel".** A limit theorem as `\tau \to 0` does not imply the asymptotics
in `x` at `\tau = 1`, and that is all the sentence needs. "Nothing" is more than that.

**"The kernels with a small c" is loose too.** The small-time results hold for `\tau < \tau_0`
with `\tau_0` depending on the process (the paper's own comment, `03-isotropic.tex:708-711`: "no
one number bounds $c$ for the class"). The kernels covered are those of each family
`\{\tau F : \tau < \tau_0(F)\}`, not those with `c` below a number.

**Disposition proposed**, the referee's neutral wording fitted to each place. If the prior-art
agent confirms the Hankel theorems and the Bessel potentials, both paragraphs must also name those
results, which *are* about one law, and this wording is then the frame for them.

- `01-introduction.tex:288-293`:
  `In $\RR^d$ most of the neighbouring results are stated for a family of laws indexed by a time. With a law of exponent $F$ this literature studies the laws with the transforms $e^{-\tau F}$, $\tau > 0$, the laws at the times $\tau$ of a \Levy{} process. The kernel is the law at $\tau = 1$, and the transform at time $\tau$ falls off at the power $\tau c$. So a result for small $\tau$ covers, in each family, the kernels with $\tau$ below a bound that depends on the family, and a limit $\tau \to 0$ does not directly establish the asymptotics in $x$ at $\tau = 1$.`
- `03-isotropic.tex:816-817`:
  `Table~\ref{tab:in-print} needs a dictionary, because most of the literature on $\RR^d$ states its results for a family of laws indexed by a time and not for one law.`
- `03-isotropic.tex:822-823`:
  `So a result for small $\tau$ covers, in each family, the kernels with $\tau$ below a bound that depends on the family, and a limit $\tau \to 0$ does not directly establish the asymptotics in $x$ at $\tau = 1$.`

The contribution sentence `01-introduction.tex:357-360` ("In $\RR^d$ the rate was in print in the
limit $\tau \to 0$ ... but not the asymptotic equivalence with its constant, at one kernel, for the
class") is exact as far as the sources of Table 3 go, and is the prior-art agent's to settle.

---

## 4. "Not found stated" and "with explicit constants" — CONFIRMED for the constants; JUDGEMENT for the threshold

### Where the paper says them

"Not found stated", "new as far as the author has found":

- `main.tex:170-173`, p. 1: "In $\RR^d$ its ingredients are known, and it was not found stated for
  the class. Three results are new as far as the author has found".
- `01-introduction.tex:349-350`, p. 4, and `370-371`, p. 5: "three statements are new as far as the
  author has found"; "Two statements are made here for the class from known ingredients, and the
  author has not found them stated."
- `01-introduction.tex:384-385`, p. 5: "The search looked for each of these five statements in the
  sources cited in this section and in Table 3, and was not exhaustive."
- Table 3, `03-isotropic.tex:730`, `754`, `762-763`, `772-773`, p. 21, with the caption's
  "``Not found'' refers to the sources cited in this paper."
- `03-isotropic.tex:808-812`, p. 22; `04-conclusion.tex:114`, `122-125`, p. 29.

Constants of the bounds:

- `01-introduction.tex:377`, p. 5: "\emph{Bounds at one kernel, with their constants}".
- `03-isotropic.tex:803-804`, p. 22: "Two bounds with explicit constants complement the rate
  (Propositions 3.16 and 3.17)."
- `03-isotropic.tex:809-811`, p. 22: "the two bounds with their constants".
- Table 3, `03-isotropic.tex:762` ("explicit radius and constant", the lower bound) and `772-773`
  ("One kernel, every $c \le d$, $\beta < c$ and radius, with its constant", the upper bound).
- `03-isotropic.tex:1098-1100`, p. 25: "The lower bound has both, displayed, and the upper bound
  holds at every radius."
- `03-isotropic.tex:1179`, p. 27: "Stating it adds the constant".
- `04-conclusion.tex:124`, p. 29: "the bounds on the spike with their constants".

### Is "explicit constants" accurate for Proposition 3.17 as stated? — No (CONFIRMED)

Proposition 3.16 displays its radius and its constant from the datum (`03-isotropic.tex:1119-1127`).
Proposition 3.17 states (`1157-1158`): "One may take $A_\beta = (2\pi)^{d/2}e^{1/2}\,C'_\beta$, for
every constant $C'_\beta$ with which the upper bound of Theorem 3.12(4) holds." Theorem 3.12(4)
states that such a constant exists (`876-877`: "there is $C'_\beta$ with ..."). So the statement
gives the constant in terms of a constant whose existence is asserted. The proofs make it
constructive: `C'_\beta = (2\pi)^{-d} C_\beta \int |y|^{-\beta} e^{-|y|^2/2} dy`
(`appendix-isotropic.tex:904-909`) with `C_\beta = 2^\beta(1 + e^{\beta L})`,
`L = 3 - \log(\varepsilon r_\beta)` (`798-819`), where `r_\beta` is a radius below which
`k_d \ge \beta_1` and `\varepsilon` is chosen so that a spherical cap has a given share of the
sphere. The referee's substitution is the right one. Two of the three choices are conditions and
not formulas. The sentence at `1098-1100` is the accurate one; "Two bounds with explicit
constants" (`803`) is not.

**Disposition proposed**, if the statement is left as it is (displaying the constant in the
statement is the other agent's item, and changes a shared statement):

- `03-isotropic.tex:803-804`:
  `Two bounds complement the rate: a lower bound with an explicit radius and constant, and an upper bound at every radius whose constant is given through that of Theorem~\ref{thm:origin-boundedness-d}(4) (Propositions~\ref{prop:origin-lower-bound-d} and~\ref{prop:origin-upper-bound-d}).`
- `01-introduction.tex:377`: `\emph{Bounds at one kernel}`, and at the end of the item:
  `The lower bound has an explicit radius and constant.`
- `03-isotropic.tex:810` and `04-conclusion.tex:124`: "the two bounds", without "with their
  constants".
- Table 3, `03-isotropic.tex:772-773`:
  `One kernel, every $c \le d$, $\beta < c$ and radius, its constant in terms of that of clause (4) of the theorem;`
- `03-isotropic.tex:1179`: `Stating it adds the form of the constant,`.

If the other agent's disposition displays the full constant in Proposition 3.17, "explicit" becomes
accurate and these sentences stay.

### The threshold as a short synthesis — JUDGEMENT

The referee's description is accurate: "not found stated" reports a bounded search. The paper says
so itself (`01-introduction.tex:384-385`, the caption of Table 3). It also already says that the
threshold is assembled "from known ingredients" in every place where it claims it. What it does
not do is say in one sentence what the assembly is. The decay is clause (1); the bounded side is
Fourier inversion, C1; the unbounded side is Feller's observation (Lemma A.2(2)) with the lower
bound `\widehat\mu(\xi) \ge e^{-13c/4-2C_k}|\xi|^{-c}` of Lemma A.3(1), which is what settles
`c = d`.

**Disposition proposed** (accept; three words saved in the abstract, three lines added in § 1):

- Abstract, `main.tex:170-171`:
  `The threshold is classical on the line, and in $\RR^d$ it is a short synthesis of known estimates.`
- `01-introduction.tex:373-376`, item 4:
  `\emph{The threshold} (Theorem~\ref{thm:origin-boundedness-d}). The density is bounded near the centre exactly when $c > d$, and the boundary $c = d$ is on the unbounded side. The proof is a short synthesis: the decay of the transform at the power $c$, Fourier inversion for the bounded side, and for the unbounded side Feller's observation that a density bounded near the origin and a nonnegative transform force the transform to be integrable, with a lower bound on the transform that settles $c = d$. In print were the bounded side, the unbounded side for $c \le d/2$ and for small $\tau$, and the threshold for the geometric stable laws.`

Whether Table 3's row keeps "Not found stated" depends on the prior-art agent (the Bessel
potentials are a fixed-law instance of the threshold with its boundary case).

---

## 5. "Readable on its own", "the dimension enters twice", the repetition — CONFIRMED as descriptions; JUDGEMENT on what to cut

### "Readable on its own" against the dependence on Theorem 2.3 — CONFIRMED

The sentence: `02-line-papers.tex:82`, p. 7: "This paper continues two earlier papers by the author,
and is written to be read on its own." It occurs once. Seven lines on, the same paragraph says that
the section "restates, without proof, the statements of the two papers that the later sections
use" (`88-90`). The necessity half of Theorem 3.6 cites Theorem 2.3
(`03-isotropic.tex:400-404`: "Theorem 2.3 gives a gauge $\chi$, an admissible $F \not\equiv 0$
..."), and Theorem 2.3 is restated without proof (`02-line-papers.tex:177-185`, p. 9). The
referee's description is accurate: in print the classification on the line is an external result.
§ 1.1 adds a fact the referee did not use: the *formal* proofs assume none of the restated
statements (`01-introduction.tex:441-443`). So the dependence is one of the printed text only.

The referee's § 7 names two more places where the printed text asks for trust: the existence of
the time-causal families behind the named kernels (said at `03-isotropic.tex:639-647`), and the
reading of C5 (said in § 1.1 and § 2.6). Both are said plainly where they occur. The third, the
alternative proof on p. 54, is another agent's.

The referee could not retrieve the line and cone papers (review § 1). The bibliography prints
their version DOIs (`main.bbl`: `10.5281/zenodo.22761632`, `10.5281/zenodo.22864170`), so nothing
is missing from the paper; a second round can attach the two PDFs.

**Disposition proposed.** `02-line-papers.tex:82`:
`This paper continues two earlier papers by the author. It restates what it uses from them, so that its statements can be read without them. The proofs of the restated statements are in those papers, and the classification here rests on that of the line paper (Theorem~\ref{thm:line-classification}).`

### "The dimension enters twice": the count — CONFIRMED (three times verbatim, three times in other words)

| place | text |
|---|---|
| `main.tex:163`, p. 1 | "The dimension enters twice." |
| `01-introduction.tex:209`, p. 2 | "The dimension enters twice. It enters through the exponent." |
| `01-introduction.tex:216`, p. 2 | "The dimension also enters as a threshold" (the second half of the same passage) |
| `03-isotropic.tex:140-141`, p. 14 | "What remains of the dimension is the class $\mathcal{A}_d$ of exponents and a threshold." |
| `03-isotropic.tex:783`, p. 20 | "One number decides, and the dimension is its threshold." |
| `04-conclusion.tex:107`, p. 29 | "The dimension enters twice." |

The referee finds the two effects correctly distinguished and the phrase defensible. Three
verbatim uses, in the abstract, the introduction and the conclusion, are the usual three. Whether
that is "excessive" is a judgement. No change is proposed, except that the abstract's copy is the
first candidate when the abstract needs four words.

### The repetition, measured — CONFIRMED

Line counts are lines of the `.tex` source, about 55 to a printed page. "Statement" is the numbered
statement itself and is not counted.

| headline result | restated at | places | lines |
|---|---|---:|---:|
| Classification (the dilations of one rotation-invariant self-decomposable law; every such law but the point mass occurs) | abstract `main.tex:160-162`; § 1 answers `01:191-204`; prior work `01:273-274`; neighbours `01:336-338`; contributions `01:385-386`; § 3 opening `03:137-140`; § 3.2 opening `03:312-318`; after Cor. 3.7 `03:453-457`; § 3.3 opening `03:692-693`; § 3.4 opening `03:1211-1213`, `1218-1221`; § 4 `04:102-107` | 11 | 55 |
| Threshold (bounded exactly when `c > d`) | abstract `main.tex:163-165`; question 2 `01:181-184`; answers `01:216-222`; contributions 4 `01:373-376`; § 2.4 `02:371-372`; § 3 opening `03:141-143`; § 3.3 opening `03:783-796`; tiers `03:809-811`; Table 3 `03:729-730`; after the theorem `03:890`; Remark 3.21 `03:1399-1400`; § 4 `04:109-112`, `123-124` | 12 | 49 |
| `c` does not depend on the dimension: bounded on the line, a spike in the plane; the Matern range | abstract `main.tex:166-169`; answers `01:222-227`; § 3.3 opening `03:787-789`, `804-806`; caption of Figure 1 `03:704-705`; after Cor. 3.13 `03:940-949`; the example `03:968-970`; § 4 `04:139-141`, `148-150` | 7 | 37 |
| Rate | abstract `main.tex:165`; answers `01:227-230`; prior work `01:295-298`; contributions 1 `01:353-360`; § 3.3 opening `03:799-803`; tiers `03:808-809`; Table 3 `03:753-754`; lead `03:1014-1022`; after the proposition `03:1062-1068`; § 4 `04:114-118`; § 4.1 `04:172-176` | 11 | 52 |
| Bounds | contributions 5 `01:377-382`; § 3.3 opening `03:803-804`; Table 3 `03:762-763`, `772-773`; leads `03:1098-1101`, `1142-1144`; after the proposition `03:1177-1182`; § 4 `04:124-125` | 7 | 27 |
| Strict filtration | abstract `main.tex:169-170`, `172`; question 3 `01:185-188`; answers `01:209-214`, `232-234`; prior work `01:310-318`; contributions 2 `01:361-365`; § 2.3 `02:307-312`; § 3 opening `03:143-144`; § 3.4 opening `03:1224-1226`, `1238-1239`, `1246-1258`; after the theorem `03:1306-1310`; § 4 `04:107-109`, `118-121` | 12 | 68 |
| `Cin` rays | abstract `main.tex:172-173`; answers `01:234-242`; prior work `01:316-318`; contributions 3 `01:366-368`; § 3.4 opening `03:1234-1241`; lead `03:1345-1347`; after the theorem `03:1358-1364`; § 4 `04:121-122`, `137-139` | 9 | 40 |
| The two tiers of what is claimed ("three new ..., two not found stated") | abstract `main.tex:170-173`; contributions `01:349-389`; § 3.3 `03:808-814`; the last column of Table 3; § 4 `04:114-125` | 5 | 64 and a column |
| What the cone paper had proved (two steps strict; no claim on the `Cin` rays) | `01:313-318`; `01:362-363`, `367-368`; `02:310-312`; `03:1238-1241`; `04:120-121` | 5 | 19 |

The summarising blocks together: the abstract (17 lines), "The questions" (`01:171-189`, 19), "The
answers" (`01:191-242`, 52), "Contributions" (`01:349-389`, 41), the opening of § 3 (`03:137-144`,
8), of § 3.3 (`03:689-693` and `783-814`, 37), of § 3.4 (`03:1211-1258`, 48) and § 4
(`04:100-150`, 51): 273 source lines, about five of the thirty pages.

The referee's description is accurate. Two facts bear on what to cut. The openings of § 3.3 and
§ 3.4 were written at the author's review ("a bit more guiding to the main results in the
beginning", Q-0408). And the scope audit of `WRITING.md` § 5 covers every one of these sentences,
so each restatement is also a place where a hypothesis can be lost. § 8 proposes the cuts.

---

## 6. The trust base — (a) PARTLY; (b) CONFIRMED, and the paper's claim holds for every declaration; (c) JUDGEMENT, the author's

### 6(a) Does "verified" or "machine-checked" read as more than it is? — PARTLY

What is verified is that the formal statements follow from the formal definitions, Lean's logical
axioms and the seven cited facts. No sentence of the paper claims the truth of the cited facts,
novelty, or a machine check of the agreement between formal and printed statements; § 1.1's "What
is neither" (`01-introduction.tex:543-563`, p. 7) says the last in so many words, and the referee
calls the account "substantially clear and candid". Four sentences use a shorthand that reads as
more until the reader reaches that paragraph.

1. `01-introduction.tex:429-433`, p. 5: "Every definition, lemma, proposition, theorem and
   corollary of § 3 is stated in the Lean 4 proof assistant, on its mathematical library Mathlib,
   and every proof is machine-checked. The same holds for the six lemmas stated in Appendix A. So
   the proof assistant has verified each of these statements from the definitions, its own logical
   foundations and the seven cited facts listed below." "Every proof" reads as the printed proofs,
   which are not what Lean checks (§ 1.1 itself says the printed and the formal proofs differ in
   two places, `443-447`). "These statements" reads as the printed statements. The qualification
   comes two pages later. The presentation review flags the same sentence (its item 4).
2. `main.tex:173-174`, p. 1: "The main statements are machine-checked in Lean 4, assuming seven
   theorems of the literature." It carries the condition the referee asks it to keep. It does not
   say that what is checked is a formal counterpart.
3. `ai-statement.tex:42-43`, p. 58: "the formal development in Lean that machine-checks its main
   statements".
4. `declarations.tex:21-23`, p. 58: "the formal development in Lean 4 that machine-checks the
   statements of § 3, with its ledger of the cited facts (§ 1.1 and Appendix B)".

**Disposition proposed.**

- `01-introduction.tex:429-433`:
  `Every definition, lemma, proposition, theorem and corollary of \S\ref{sec:isotropic}, and each of the six lemmas stated in Appendix~\ref{app:isotropic-proofs}, has a formal counterpart in the Lean~4 proof assistant, on its mathematical library Mathlib. Lean checks that each formal statement follows from the formal definitions, its own logical foundations and the seven cited facts listed below. The check covers neither the cited facts, nor the printed proofs, nor the agreement between a formal statement and the printed one, which was reviewed by AI agents only (``What is neither'' below).`
- Abstract, one word more (to be taken from elsewhere):
  `Formal counterparts of the main statements are machine-checked in Lean~4, assuming seven theorems of the literature.`
- The AI statement and the code availability statement point to § 1.1 already; "machine-checks
  formal counterparts of" in each is the consistent form.

### 6(b) Twelve axioms in the guard, nine in the paper, eight declarations printed — CONFIRMED; the complete report is made

**The text.** `appendix-verification.tex:127-134`, p. 56: "`lake env lean CIAxiomGuard.lean`, run
there, prints for every named declaration the assumptions it depends on, which Lean calls its
axioms. The check passes when every axiom printed is one of Lean's three logical axioms ... or one
of the twelve axioms listed in `blueprint/trust-boundary.txt`." And: "Nine of the twelve axioms of
that file are the seven cited facts of this paper, C3 being three. The other three are cited facts
of the companion paper". The block of p. 57 prints eight declarations. The referee's description is
accurate: the criterion that the paper prints admits three axioms that the paper does not claim,
and the printed evidence for the nine covers eight declarations.

**The complete paper-specific report.** Appendix B lists 144 names in 26 rows; 141 are distinct
(`polarProfileOf`, `measurable_gaussVar` and `OriginDatum.polar_decomposition` stand under two
statements each). The list is that of `records/affine/gen-verification-table.py`, which reads the
blueprint's `\lean` tags (`check`: "26 rows, 144 declarations: equal to the blueprint's lean
tags").

- Script: `records/affine/reviews/verify-round1-scripts/axioms_all_144.py` (`gen`, then `table`).
- Scratch file: `Formalization/scratch/verify_round1_axioms_all_144.lean` (git-ignored): the import
  and 141 `#print axioms` lines.
- Run once, from `Formalization/`, on the warm build: `lake env lean scratch/verify_round1_axioms_all_144.lean`.
  It took 45 seconds (09:51:29 to 09:52:14 on 2026-10-12) and exited 0. Lean 4.31.0. No `lake build`.
  The `.olean` of the library is dated 2026-10-12 07:57, after the last commit that touches
  `Formalization/` (`d3ddc15`, 02:16).
- Output, as Lean printed it: `records/affine/reviews/verify-round1-scripts/axioms-all-144-output.txt`
  (285 lines, SHA-256 `4069dfd6a027e17023d278e8f5e837cb8f2b07741a588ad36424e0a2617819b9`).
- Cross-check: the eight blocks of Appendix B (`records/affine/axioms-block-q0417-output.txt`) are
  in the new output byte for byte.

**Result.** All 141 declarations are reported. Every one depends on Lean's three logical axioms.
110 depend on nothing else; 31 name one or more of the nine. None names
`operatorSelfDecomposable_infinitelyDivisible`, `khintchine_null_array` or
`gelfand_naimark_logMajorized`, and none names any other axiom. Each of the nine is named by at
least one declaration. For every statement the union of the cited facts that its declarations name
is exactly the set of Table 1.

| statement | names | cited facts that Lean reports (union) | Table 1 | agrees |
|---|---:|---|---|---|
| Def. 3.1 `def:isotropic-operator-family` | 2 | none | none | yes |
| Def. 3.2 `def:isotropic-kernel-family` | 8 | none | none | yes |
| Lemma 3.3 `lem:operators-to-kernels` | 15 | none | none | yes |
| Lemma 3.4 `lem:radial-marginal` | 4 | none | none | yes |
| Lemma 3.5 `lem:isotropic-marginal-family` | 4 | none | none | yes |
| Thm. 3.6 `thm:isotropic-classification` | 3 | C3(ii), C3(iii) | C3(ii) and (iii) | yes |
| Cor. 3.7 `cor:isotropic-classification-operators` | 2 | C3(ii), C3(iii) | C3(ii) and (iii) | yes |
| Lemma 3.8 `lem:isotropic-realisation` | 1 | none | none | yes |
| Def. 3.9 `def:isotropic-origin-datum` | 12 | none | none | yes |
| Prop. 3.10 `prop:isotropic-polar-reading` | 5 | C2, C3(i), C3(ii), C3(iii), C4 | C2, C3, C4 | yes |
| Prop. 3.11 `prop:isotropic-bridge` | 9 | none | none | yes |
| Thm. 3.12 `thm:origin-boundedness-d` | 12 | C1 | C1, in clauses (2) and (5) | yes |
| Cor. 3.13 `cor:origin-profile-exponent` | 4 | none | none | yes |
| Prop. 3.14 `prop:isotropic-radial-monotone` | 2 | C2, C3(ii), C3(iii), C5 | C5; C3(ii), (iii) in (1); C2, C3(iii) in (2) | yes |
| Prop. 3.15 `prop:origin-rate-d` | 8 | C2, C3(iii), C5, C7 | C7; C2, C3(iii), C5 | yes |
| Prop. 3.16 `prop:origin-lower-bound-d` | 6 | C3(iii) | C3(iii) | yes |
| Prop. 3.17 `prop:origin-upper-bound-d` | 7 | C2, C3(iii), C5 | none in (1), (2); C3(iii) in (3); C2, C3(iii), C5 | yes |
| Def. 3.18 `def:filtration-thresholds` | 13 | none | none | yes |
| Thm. 3.19 `thm:filtration-strict` | 4 | C2, C3(i), C3(ii), C3(iii), C4, C6 | C2, C3, C4; C6 in (3) | yes |
| Thm. 3.20 `thm:no-cin-ray-in-the-plane` | 2 | C2, C3(i), C3(ii), C3(iii), C4 | C2, C3, C4 | yes |
| Lemma A.1 `lem:polar-decomposition` | 1 | none | none | yes |
| Lemma A.2 `lem:positive-transform-origin` | 4 | none | none | yes |
| Lemma A.3 `lem:isotropic-exponent-log` | 3 | none | none | yes |
| Lemma A.4 `lem:threshold-monotone` | 7 | none | none | yes |
| Lemma A.5 `lem:threshold-limit` | 4 | none | none | yes |
| Lemma A.6 `lem:delay-polar-profile` | 2 | none | none | yes |

The clause-level entries of Table 1 agree with the declarations too (`axioms_all_144.py table`
prints the 144 rows):

- Theorem 3.12: C1 is named by `origin_density_smooth`, `origin_density_bounded_smooth` (clause
  (2)) and `origin_dichotomy` (clause (5)), and by no other of its twelve.
- Proposition 3.14: `radial_monotone_family` names C3(ii), C3(iii), C5; `radial_monotone_law` names
  C2, C3(iii), C5.
- Proposition 3.15: the six declarations of the limits name C7 alone, or nothing
  (`origin_transform_ball_log`); `origin_rate` and `origin_rate_critical`, which include the
  existence of the density, name C2, C3(iii), C5, C7.
- Proposition 3.17: `origin_upper_bound` and `origin_upper_bound_of_heat` name nothing;
  `origin_density_lower`, `origin_density_log_order`, `origin_ball_log_order` name C3(iii);
  `origin_density_upper` and `origin_density_order` name C2, C3(iii), C5.
- Theorem 3.19: C6 is named by `filtration_top` alone.
- Proposition 3.10: `polar_reading_unique` names C2, C3(ii), C3(iii); the other four name C2, C3
  and C4.

So the paper's claim, seven cited facts and nothing of the companion paper's, holds for every
declaration that it lists.

**A second fault in the printed description, which the referee could not see.** The paper says
that the command "prints for every named declaration the assumptions it depends on"
(`appendix-verification.tex:127-128`), that the block "is a selection of what the command prints,
for eight declarations" (`165-166`) and that "The command prints the report for the other
declarations too" (`171-172`); the caption of Table 1 says that Appendix B "gives the command that
prints the others" (`01-introduction.tex:538-539`). The guard file does not do this. Of the 141
declarations, 99 have a `#print axioms` line in `Formalization/CIAxiomGuard.lean`. 31 of those 99
stand under `#guard_msgs in`, which prints nothing when the pin holds, and the eight of the block
are among the 31. The other 42 are definitions and have no line (the guard's header: "a tagged
definition is covered through the theorems stated in it"). A reader who runs the printed command
sees the report of 68 of the 141 and not one line of the printed block. The paper's own comment
knows it (`appendix-verification.tex:190-191`: "The guard file CIAxiomGuard.lean no longer prints
these lines itself: it pins them under #guard_msgs"), and the block was made from a scratch file
(`records/affine/edits_q0417_axioms_block.py`). The pins are a stronger check than a print. The
sentences describe a weaker and different one.

**A note on the list.** The row of Lemma 3.3 carries the `\lean` tags of two blueprint nodes of
chapter 4, and so it lists `operators_to_kernels_gw`, `operators_to_kernels_affine` and
`kernels_to_operators_gw`, which belong to clauses on the `(G, W)` families that the paper's lemma
does not print (`03-isotropic.tex:236-238`: "Not taken: ... the clauses on the (G, W) families,
which are the affine paper's"). They depend on the logical axioms only, so nothing is hidden; the
list says "the declarations ... that state and prove it" and for this row it says more.

**What a paper-specific guard would be, and where it would go.**

1. A boundary of this paper: the nine names, in a file of its own
   (`blueprint/trust-boundary-iso.txt`) or as a marked part of `blueprint/trust-boundary.txt`.
2. A guard of this paper: one `#print axioms` line for each of the 141 declarations, generated from
   the blueprint's `\lean` tags by the list of `gen-verification-table.py` (never typed), as
   `Formalization/CIAxiomGuardIso.lean`, with no `#guard_msgs` pin in it so that the output is the
   report.
3. A check that fails when a printed axiom is outside Lean's three and the nine, and when a
   statement's union differs from Table 1. `axioms_all_144.py table` is that check (exit 1 on
   either fault). Its home is the CI job of `.github/workflows/lean.yml` that runs the guard
   ("guard 3"), as a further step, and in the release export as the file `axioms.txt`. Promoting
   it into `linkage axioms` (a boundary per paper directory) is a framework item for article-kit's
   `WISHLIST.md`, since a repository with two papers and one boundary will meet this again.
4. Not checked here: whether `linkage release export` restricts the exported `trust-boundary.txt`
   to the axioms of the exported module. If it copies the twelve-name file, the referee's point
   survives the release.

**Disposition proposed** for Appendix B (`appendix-verification.tex:126-134`, `165-173`) and the
caption of Table 1:

- `\texttt{lake build} in \texttt{Formalization/} reproduces the verification. For the declarations of this paper the criterion is that every axiom Lean reports is one of its three logical axioms, \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}, or one of the nine names below. Lean's report for all the declarations of the list above is deposited with the paper, with the file that prints it and the script that compares it with Table~\ref{tab:trust-base}. The repository's guard, \texttt{CIAxiomGuard.lean}, serves the companion paper as well: it admits three further axioms, cited facts of that paper, on which no declaration of this paper depends, and it fails the build if a main declaration gains or loses an axiom.`
- `\paragraph{Lean's report.} The block below is Lean's report for eight of the declarations: ...` in place of "is a selection of what the command prints", and the sentence "The command prints the report for the other declarations too." deleted.
- Caption of Table 1: `Appendix~\ref{app:verification} prints the report for eight declarations; the report for all of them is deposited with the paper.`

The full report is 285 lines, about six printed pages. It belongs in the export, not in print.

### 6(c) Review access — JUDGEMENT, the author's decision

**The text.** `appendix-verification.tex:41-46`, p. 55: "The repository is private until the paper
is released, so its name identifies the revision and is not a link a reader can follow. With each
released version a public verification export, which holds the formal development, the ledger and
the blueprint sources, is deposited under the concept DOI of the paper." The code availability
statement says the same (`declarations.tex:24-28`, pp. 58-59). The referee's description is
accurate: a reader of the review build cannot repeat the check.

**What `docs/RELEASE.md` says.** The verification export is a step of the release, not of the
review: checklist item 5, "Where the repository stays private (it holds unreleased modules), the
release is a verification export: a separate public repository holding the Lean modules the
released statements rest on, the trust boundary and the ledger, the released blueprint chapters,
the paper and its PDF, the process account and the reviews. The export is built from scratch and
its guard must reproduce the paper's printed `#print axioms` block." The public repository "is
created at the author's word". Checklist item 1 puts the external rounds *before* the release
("The external rounds answered (PROCESS.md § 9)"). The first page of a released PDF carries "the
release date, the version and the version DOI" (rule 5). A release is `v0.x` "while a preprint,
`v1.0` at journal submission". `linkage release export --draft` writes an export with a `DRAFT`
file "that `linkage release zenodo` refuses outside the sandbox".

**What the cone paper did.** Its reviews were run on frozen builds named by commit
(`records/cone/reviews/cone-review-build-a76a323.pdf`), by systems that had the PDF only. Its first
review asked for the same thing, and the response plan declined it before release
(`records/cone/PLAN-review-response.md:170-171`: "A permanent URL for this paper's export (review
§ 5): supplied by the release checklist, not before."). The export was then cut at the release
from the tag `cone-v0.1` into the public repository `spatial-hemigroup-scale-space-cone`, built
from scratch with its guard, tagged `v0.1` and deposited with a version DOI
(`records/cone/RELEASE-procedure.md`; `adr/0005-first-release-is-a-verification-export.md` gives
the reason: a PDF alone "would leave the paper's machine-checking claim ... pointing at nothing a
reader can open"). The run took about three hours, most of it the Lean build.

**So, on the process as written,** a journal referee never sees this problem: the journal
submission follows a release, which has the public export and a version DOI. The reviewer of this
round is the § 9 round, which sees the PDF by design. What the round shows is what the review build
has to say, and one fault of wording that the release must not carry.

**The fault of wording — CONFIRMED.** "Deposited under the concept DOI" names the series. The
referee is right that a revision is identified by its version DOI. `RELEASE.md` rule 5 already asks
for the version DOI on the first page. Proposed for both places, at the release:
`With each released version a public verification export is deposited, with a version DOI of its own; the concept DOI names the series of versions.`

**The options.**

- **A. As the cone paper.** No export before the release. The response says where the export, its
  tag and its version DOI come from. Cost: nothing now. A reviewer of round 2 still cannot repeat
  the check.
- **B. A, and the complete axiom report now.** The round-2 prompt attaches
  `axioms-all-144-output.txt` and the table of 6(b). This answers "the complete paper-specific
  axiom report" of required change 12 at once and costs nothing. The corrected sentences of 6(b)
  go into the next freeze.
- **C. A frozen export for review.** What it would take here:
  1. a `[[modules]]` table for `iso` in `linkage.toml`, which has none: the chapters (blueprint
     chapter 3, the two nodes of chapter 4 behind Lemma 3.3, the interface nodes of the seven cited
     facts), the paper directory, the tag, the Lean roots, the headline declaration, the records;
  2. the closure, by `linkage release export --dry-run` first. The declarations of this paper and
     of the unreleased affine paper are in one Lean library, and the records of both are in
     `records/affine/`. The cone paper needed a mathematician's pass to move declarations so that
     its export "carries no proof of a later module" (ADR-0005); the same question arises here,
     and the affine paper is unpublished work, which stays private;
  3. `linkage release export --module iso --draft --build`, about three hours for the build from
     scratch, the guard run in the export, the printed block compared;
  4. the identifier: a tag (`iso-review-2`) here and in the export, the commit hash, and the
     SHA-256 of the zip of the tagged tree, printed in the response and in Appendix B. A DOI comes
     only with a release;
  5. the access: the zip as an attachment to the review, or a private repository to which a
     reviewer is invited. The scripts refuse a `DRAFT` export on zenodo.org, so a deposit is not a
     route without a change to them.
- **D. Release first.** `iso-v0.1` as a preprint release with the public export and its version
  DOI, then the next review round on the released PDF. `RELEASE.md` puts the external rounds
  before the release, so this departs from the checklist's order and is the author's call.

Not verified: what access forms Zenodo offers for an unpublished draft; whether a reviewing system
can use a repository at all.

---

## 7. The AI statement (p. 58) — JUDGEMENT, the author's decision

**The text** (`ai-statement.tex:38-57`). The two parts in question: "the agents' words outnumber
mine by between twenty-one and forty-five to one (computed 2026-10-11, a lower bound) over the
module's first fourteen archived days" (`51-53`), and "I would not, unaided and in spare time, have
written this." (`55`). The referee (§ 5, suggestion 8) asks to drop the ratio and "the personal
account"; the presentation review (item 20) asks to drop the ratio, "archived days", "the module"
and the sentence on spare time, and to keep "the extent of AI drafting and formalization, the
allocation of decisions, the AI-only review, the absence of human review of formal statements, and
the author's responsibility".

**What `WRITING.md` § 6 requires.**

- "Never claim less AI involvement than there was."
- "Numbers come from `chronicler`, carrying the date they were computed and their caveats: they
  are lower bounds ... Never restate a figure without re-deriving it."
- "Do not repeat the trust boundary. The machine-checked subsection owns it (§ 4); the disclosure
  cites it."
- "Anonymity outranks completeness", for a double-blind submission.
- The scoping rule for a submission: a disclosure "points rather than restates", and "No
  storytelling: where a monograph has room to say something interesting about the process, a
  submission needs transparency, and transparency is six lines."
- "When targeting a specific venue, read its current wording rather than inferring it from the
  shape of the clause."

**What it leaves free.** It does not require a number: rule 2 says where a number comes from and
what it carries when one is printed. It does not require or forbid the sentence on spare time; "no
storytelling" is the nearest rule, and it is said of a submission. It names Paper I's statement as
the statement of record and its form as the starting point; the file's header says the six-line
form is the author's decision of 2026-09-14 and that the two statements of this repository share
it.

**What the present text complies with.** The ratio carries its date and "a lower bound". The trust
base is cited, not repeated. Nothing understates.

**One point that is not a matter of taste.** "The module's first fourteen archived days" prints a
word of the programme, "module", that the paper nowhere explains. The paper's rule for the
programme's labels is that none reaches the reader (`main.tex:34`, a comment: "No internal label
reaches the reader (Q-0344, the author's review)"). "The paper's" is the fix, whatever is decided
about the rest.
The pointer `notes/PROCESS.md` is a path in a private repository until the export exists.

**The options.**

- **A. Keep the six-line form**, fix "module". For: it is the form of record of the programme's
  released papers, and the ratio is the only quantified statement of extent. Against: two reviews
  ask to drop it.
- **B. Drop the ratio from the print**, keep it in the process account that the export carries, and
  keep the last two lines. Rule 1 still holds, because the sentence "the prose, statements, proofs
  and code ... are the agents' work, mostly unattended" states the extent.
- **C. Drop the ratio and the sentence on spare time**: the contribution, the review paragraph, the
  pointer, the responsibility. This is what both reviews ask.
- **D. Two forms**: the preprint release keeps the form of record, the journal submission takes the
  short one after the venue's wording is read (the scoping rule distinguishes the two cases).

In B and C the pass 5 of `PROCESS.md` § 8 (the archivist's re-derivation) still runs for
`notes/PROCESS.md`, which keeps the figures.

---

## 8. Exposition and structure (review § 7; suggestions 4, 6, 7) — JUDGEMENT, proposal by proposal

"Shared" means that the text is under a `% shared with blueprint` marker, so that a change is made
at the blueprint and re-transcribed (and re-pinned where the paper's copy is a pinned edit). Costs
are in printed lines of the main text; a page is 46 to 48.

| proposal of the referee | what the text has now | cost in the main text | shared statement? | proposed |
|---|---|---|---|---|
| An outline of the proof of Proposition 3.15 in the main text (suggestion 4) | One sentence, `03-isotropic.tex:1082-1085`, p. 25: "Karamata's Tauberian theorem, C7, and then the monotonicity of the density, with a Gaussian average of the transform ... in place of the Laplace transform." The two indices and the normaliser at `c = d` are in Appendix A only (Steps 3, 3' and 4, pp. 47-48). | +6 to +7 lines (a ten-line outline for the four-line sentence) | no (prose; the proof of record stays in Appendix A) | **accept**: it is the paper's main analytical claim, and the outline is what a reader needs to judge the use of C7 |
| Theorem 3.12(3) to the examples | Clause (3), 17 source lines of the statement (`03-isotropic.tex:849-865`), used by the Matern example (`967-968`) | 0 (moved, +2 for a heading) | **yes**: `thm:origin-boundedness-d`; clauses (4) and (5) would be renumbered, and they are cited in Table 1, in Appendix B, by clause in at least ten places of the paper and inside the shared statement of `prop:origin-upper-bound-d` ("Theorem 3.12(4)") | **decline** in this round: three shared statements and the clause numbers through the paper, for no page; the author may take it up with the presentation review's item 12 (the dichotomy first) |
| Proposition 3.17's logarithmic limits: "retain them only if their explicit-radius aspect is explained" | Clause (3), `03-isotropic.tex:1165-1173`; the comment `1179-1182` says what stating it adds and does not say that the limits also follow from the rate | +2 lines | the clause is shared; the proposal needs no change to it | **accept as a sentence, keep the clause.** The limits do follow from Proposition 3.15, in every `d \ge 1`. Clause (3) gets them for `d \ge 2` without Karamata's theorem (Table 1: C3(iii), against C7 for the rate; 6(b) confirms it in Lean's report), and its first assertion holds at every radius below `\delta` with no exceptional set. Add after `1182`: `The two limits of clause (3) also follow from Proposition~\ref{prop:origin-rate-d}, in every dimension; clause (3) obtains them for $d \ge 2$ without Karamata's theorem, and its inequality holds at every radius below $\delta$.` |
| The bound `6 + 4\sqrt2` of Theorem 3.19(2) to a remark | Clause (2), three lines of the statement (`1295-1297`), and five lines of comment (`1321-1325`) | -2 to 0 | **yes**: `thm:filtration-strict`, and the Lean statement `filtration_witness_exists` carries the bound | **author decides; recommended: decline.** The clause is provenance from the cone paper, as the referee says, and the paper says so (`1321-1323`). It gains no page and costs a blueprint and a Lean change. A journal version can drop it |
| Definition 3.18 need not redefine `\mathcal{A}_d`, `\mathcal{A}_\infty`, `\mathcal{S}` | It does, `1262-1267` (six lines), after Proposition 2.6 (`02-line-papers.tex:292-294`) and § 2.3 (`286-287`). The file's header names it as the one deliberate repetition (`03-isotropic.tex:14-16`) | -4 to -5 | **yes**, but the paper's copy can drop what § 2 gives and be pinned, as was done for `lem:isotropic-marginal-family` and `prop:isotropic-bridge`; the blueprint keeps its text, since it has no § 2 | **accept**: a pinned copy that begins `In the notation of Proposition~\ref{prop:line-filtration} and \S\ref{sec:line-bridge}, for $w > 0$ let ...` |
| "Origin datum" adds a name for a standard isotropic Levy triplet | The term is defined in Definition 3.9 (shared) and used 13 times in § 3, 12 in Appendix A, 3 in § 2, 41 in the blueprint, 10 in the affine paper, which restates the definition; the Lean structure is `OriginDatum` | 0 to rename; +1 for a gloss | **yes** to rename: about ten shared statements of this paper and one of the affine paper | **decline the rename; accept a gloss.** After Definition 3.9 (`524`): `An origin datum $(a, k_d)$ is the generating triplet $(aI, \nu_d, 0)$ of C3 for a rotation-invariant self-decomposable law, written in polar coordinates.` The name is the author's to keep or change at a later version |
| Appendix B's inventory and selected output to a supplement (suggestion 7) | Appendix B, pp. 55-58, a little over three pages | 0 (outside the main text; the total of 61 pages falls by about three) | no | **author decides**, with the journal. `WRITING.md` § 4 puts the inventory in "a verification appendix that the subsection names"; a supplement that § 1.1 names keeps the rule's point if nothing honesty-critical leaves § 1.1. The complete axiom report of 6(b) belongs in the export in any case |
| The elementary Stirling estimates to a supplement (suggestion 7) | The proof of Lemma A.5, pp. 51-52 | 0 (appendix) | the statement is shared; its place is not | **author decides.** The proof of record is the blueprint's and Appendix A prints the proofs of record; another agent's finding (the limit of `\sqrt d\, w_d`) uses these bounds, so the decision waits for it |
| Shorten the repeated questions, answers, contributions and conclusion (suggestion 6) | § 5 above: 273 source lines of summary, about five pages; each headline result restated 7 to 12 times | see below | no | **accept in part**, below |

**The cuts proposed for suggestion 6** (source lines; about 0.85 printed line each):

- § 4, the second paragraph (`04-conclusion.tex:114-125`, 12 lines), which repeats "Contributions"
  item by item: one sentence, `What is new, and what is stated here from known ingredients, is listed in \S\ref{sec:introduction}.` Saves 10.
- § 3.3, the tier paragraph (`03-isotropic.tex:808-814`, 7 lines): keep
  `Table~\ref{tab:in-print} says what is in print about each statement and what is claimed here. The proofs not given here are in Appendix~\ref{app:isotropic-proofs}, which also states the two lemmas of the theorem's proof.` Saves 4.
- § 3.4, the sentence on what the cone paper had proved (`03-isotropic.tex:1238-1241`, 4 lines),
  which is in § 1 twice and in § 2.3. Saves 4.
- § 3.4, the paragraph on the family (`1246-1258`): the sentences from "The critical values
  decrease strictly" to "tolerates a smaller step" repeat the two lemmas and the theorem that
  follow within a page. Saves 4.
- Definition 3.18, above. Saves 4 to 5.

Kept: the abstract, "The questions", "The answers", "Contributions" (the claim of record) and the
openings that the author asked for.

**The balance.** Cuts: about 26 source lines, 22 printed lines. Additions proposed in this record:
item 1 (2 lines), 2(a) (6), 2(b) (1), item 3 (2), item 4 (4), item 5 (2), 6(a) (2), the outline of
the proof of Proposition 3.15 (7), the sentence on Proposition 3.17 (2), the gloss on the origin
datum (1): about 29 source lines, 25 printed lines. With two lines of slack on p. 30 the main text
stays within thirty pages only if the cuts are taken, and it leaves nothing for what the other
agents' findings add. The length is then the author's decision again.

---

## 9. The version-specific citation of Grzywny, Ryznar and Trojan — CONFIRMED: the citation is right, and the paper does not print which version it follows

**The referee** (§ 6): "The available GRT arXiv version has a Theorem 5.8 concerning a Green
function, whereas the manuscript cites the published Corollary 5.8. That is a reason to identify
the version precisely, not a demonstrated erroneous citation."

**The reading note agrees.** `records/affine/READING-grzywny2019asymptotic.md`, § 7, the table
"arXiv v1 against the published text": "— | Cor. 5.8, p. 47 | **new**" and "Thm. 5.8 (d ≥ 6) |
Thm. 5.9, p. 48 | renumbered, and so the rest of § 5". Corollary 5.8 of the published text
("Under the assumptions of Theorem 5.7 there is t* > 0 such that, for 0 < t < t*,
sup p(t,x) = ∞", read at the page image, note § 4) is not in arXiv v1, where Theorem 5.8 is the
Green function bound. The note's anchors are to the published text in its advance-access
pagination 1-66; the journal pages 7193-7258 "presumably 7192 + N; this was not verified".

**What the paper prints.** Ten citations of the source, all by statement number and none by page:
`01-introduction.tex:295`, `296`, `359` (no number); `03-isotropic.tex:724` ("Cor. 5.8"), `728`
("Example 3"), `736-737` ("Thm. 3.5"), `750-752` ("Thm. 3.9", "Thm. 5.7", "Example 3"), `759-760`
("Prop. 5.3", "Thm. 5.7", "Example 3"), `769-771` ("(5.3), (5.4)", "Thm. 5.4", "Prop. 5.6");
`appendix-isotropic.tex:680` ("Thm. 3.5"). The bibliography entry prints the journal reference,
the DOI and "arXiv: 1606.04178" (`main.bbl:107-115`). For two other sources the text says which
numbering it uses ("Prop. 2.3 of the arXiv version", "arXiv numbering"). For this one it says
nothing in print: the choice is in two comments (`01-introduction.tex:121-123`,
`03-isotropic.tex:686-688`, the `TODO(release)`).

**Which printed numbers differ between the versions**, by the note's table: only "Cor. 5.8" (absent
from v1, where the number 5.8 is another statement). Theorems 3.5, 3.9, 5.4 and 5.7, Propositions
5.3 and 5.6, (5.3), (5.4) and Example 3 keep their numbers. Two of them keep the number and change
the content: Theorem 3.5 is normalised in the published text (the constants `c_1, c_2, c_3`), and
Proposition 5.6 has its `t_0` corrected. Not verified: whether later arXiv versions carry the
published numbering (the note read v1 only).

**The `TODO(release)`.** It concerns the pagination, which the paper never prints for this source.
It can be closed without the journal folios, provided the paper says which numbering it uses.

**Disposition proposed.**

- Caption of Table 3, one sentence:
  `The statements of \sscite{grzywny2019asymptotic} are cited by the numbers of the published article; its Corollary~5.8 is not in the first arXiv version, where it follows from Theorem~5.7, and Theorem~5.8 there is another statement.`
- Table 3, `03-isotropic.tex:724`: `(\sscite{grzywny2019asymptotic}, Cor.~5.8 of the published article; ...`.
- The bibliography entry keeps the arXiv number, which is how most readers will reach the text.

A reader with either version then finds the statement: Corollary 5.8 in the journal, the lower
half of Theorem 5.7 in the arXiv copy.

---

## 10. The remaining points of the shard

**The qualifications "from scale zero" and "with no Gaussian part"** (review § 2, "Boundedness
threshold and bounds": "present in the abstract, contributions, theorem and conclusion ... should
remain") — CONFIRMED. `main.tex:163`; `01-introduction.tex:350-351`; `03-isotropic.tex:837-838`;
`04-conclusion.tex:109-110`. Every rewording proposed above keeps them.

**The "building blocks" language** (review § 2, "Cin rays": acceptable because p. 29 explains that
superpositions may survive) — CONFIRMED. The explanation is `03-isotropic.tex:1358-1360`, p. 29: "A
member of $\mathcal{A}_2$ is admissible on the line, so it is still a superposition of $\Cin$ rays
and a Gaussian term. The theorem says that none of those rays is itself in $\mathcal{A}_2$." It
stays. The abstract ("of the line's building blocks only the Gaussian remains in the plane",
`main.tex:173`) and § 1 (`01-introduction.tex:241-242`) use the phrase without it; the presentation
review (item 14) asks to bring the explanation forward. Proposed for `01-introduction.tex:242`:
`So of the building blocks of the line only the Gaussian gives a family in the plane; superpositions of the others may.`

**The Student-t clause is conditional wherever it appears** (review § 2, "Scope and Student-t") —
CONFIRMED for the scope sentences: `01-introduction.tex:254-257`, `436-439`;
`03-isotropic.tex:576-577`, `616-628`, `644-647`; `04-conclusion.tex:189-195`. The lists of the
families admitted in every dimension leave the Student-t kernels out (`03-isotropic.tex:1232-1233`,
`04-conclusion.tex:136-137`). The item on the "open problem" is another agent's.

**Required change 13, the positioning of the strictness** — depends on the agent who verifies the
short proof; JUDGEMENT on the wording, the author's. Where the paper claims the strictness as new:
`main.tex:172` ("the strict decrease from dimension three on"); `01-introduction.tex:361-365`;
`03-isotropic.tex:1224-1226`, `1238-1239`; `04-conclusion.tex:118-121`. The referee does not say
the claim is disproved ("I did not locate an earlier publication explicitly stating this
self-decomposable chain"); the request is that the qualitative strictness and the quantitative
family be separated. The paper already has the referee's witness in hand without drawing the conclusion: the
datum `(0, b\,\mathbf{1}_{(0,\tau)})` is named after Proposition 3.10 (`03-isotropic.tex:562-569`)
and again after Theorem 3.20 (`1362-1364`: "those are members of $\mathcal{A}_d$"), and neither
place says whether its exponent lies in `\mathcal{A}_{d+1}`. If the short proof is confirmed,
contribution 2 could read:
`\item \emph{The dimension filtration is strict at every step, with a quantitative separating family} (Theorem~\ref{thm:filtration-strict}). That each inclusion is strict has a short proof, by a datum whose polar profile is a step. The cone paper proved the first two steps. What is added here is quantitative: on the one-parameter family of the cone paper the critical values $w_d$ (Definition~\ref{def:filtration-thresholds}) decrease strictly and are of exact order $d^{-1/2}$ (Lemmas~\ref{lem:threshold-monotone} and~\ref{lem:threshold-limit}), so its members separate every two consecutive classes.`
Printing the short proof is a new statement or a remark, and a blueprint decision.

**Review § 1, the recommendation.** "Major revision" rests chiefly on the prior art and on the
statements called wrong, which are other agents'. Of this shard, what bears on it is 2(b) (two
sentences wrong), 6(b) (the printed criterion and the printed command), and the wording of items
1, 3 and 4. None touches a statement or a proof.

---

## Closing table

| item | verdict | disposition proposed | who decides |
|---|---|---|---|
| 1. The abstract's "rate ... with its constant" at `c = d` | PARTLY: nothing false, four places fold two forms into one | Reword the abstract (same length), § 1, Table 3, § 3.3, § 4 as given | the response plan; final wording after the prior-art agent |
| 2(a). Unbounded kernel and a sampled or filtered image | PARTLY: the referee's mathematics confirmed; two sentences loose ("no finite value to sample"), none false; the qualification is missing | Three rewordings and one added paragraph of three sentences (pp. 2, 20, 22, 30) | the response plan |
| 2(b). A derivative filter "needs" `N` continuous derivatives | CONFIRMED: wrong as a necessity (the Matern kernel of index 1 on the line is the Laplace kernel; the gradient is a finite measure exactly when `c > 1`) | Two sentences replaced (pp. 22, 30); whether the weak-derivative threshold becomes a statement | the response plan; the author for the new statement |
| 3. "The literature does not study one law", "says nothing about one kernel" | CONFIRMED: contradicted by the paper's own Table 3 | The neutral wording at pp. 3-4 and p. 22 | the response plan; the frame changes if the prior-art agent confirms the fixed-law results |
| 4. "Explicit constants" for Proposition 3.17 | CONFIRMED: the statement gives the constant through `C'_\beta`, whose existence is asserted | Reword five places, or display the constant (the other agent's item, a shared statement) | the response plan, after the agent on the upper bound's constant |
| 4. The threshold as a short synthesis; "not found stated" | JUDGEMENT; the paper already says "from known ingredients" | One sentence of synthesis in contribution 4; the abstract's sentence shortened | the author (it is a claim of the paper); Table 3's row after the prior-art agent |
| 5. "Readable on its own" | CONFIRMED: Theorem 2.3 is restated without proof and carries the classification in print | The sentence of p. 7 replaced | the response plan |
| 5. "The dimension enters twice" | CONFIRMED as a count: three times verbatim, three in other words | No change | the author |
| 5. The repetition | CONFIRMED: 273 source lines of summary, about five pages; each headline result restated 7 to 12 times | The cuts of § 8 (about 22 printed lines) | the author |
| 6(a). "Verified", "machine-checked" | PARTLY: no claim beyond the check, but § 1.1 opens with "every proof is machine-checked" two pages before its qualification | The opening of § 1.1 reworded; "formal counterparts" in the abstract | the response plan |
| 6(b). Twelve axioms admitted, nine claimed, eight declarations printed | CONFIRMED as a description. The paper's claim holds: all 141 distinct declarations (144 names) depend on Lean's three axioms and the nine only, none on the companion's three, and every statement's set agrees with Table 1. Also found: the printed command prints 68 of the 141 and none of the eight | Appendix B's criterion and its two sentences on the command corrected; the full report deposited; a guard of this paper (nine names, 141 lines, the check in CI) | the response plan for the text; the engineer or the dispatching session for the guard; article-kit's wishlist for `linkage` |
| 6(c). Review access; "concept DOI" | JUDGEMENT on access; CONFIRMED that a version is named by its version DOI | Options A to D; recommended B (the cone paper's practice, and the complete axiom report attached to round 2); "version DOI" in both places at the release | the author |
| 7. The AI statement | JUDGEMENT; "the module" is an internal label in print | Options A to D; "the paper's" for "the module's" in every case | the author |
| 8. Outline of the proof of Proposition 3.15 in the main text | JUDGEMENT | accept (+7 lines) | the response plan, within the page balance |
| 8. Theorem 3.12(3) to the examples | JUDGEMENT | decline in this round (three shared statements, clause numbers through the paper, no page) | the author |
| 8. Proposition 3.17's logarithmic limits | JUDGEMENT | keep the clause; one sentence saying that the limits follow from the rate and what the clause adds (no C7; every radius) | the response plan |
| 8. `6 + 4\sqrt2` to a remark | JUDGEMENT | decline (blueprint and Lean change, no page) | the author |
| 8. Definition 3.18 redefines the classes | JUDGEMENT | accept as a pinned copy of the paper (-4 lines; the blueprint keeps its text) | the response plan |
| 8. "Origin datum" | JUDGEMENT | decline the rename (ten shared statements, the affine paper, the Lean name); accept a one-sentence gloss | the author for the name |
| 8. Appendix B and the Stirling estimates to a supplement | JUDGEMENT | no page of the main text is gained; wait for the journal and for the agent on the limit of `\sqrt d\,w_d` | the author |
| 8. Shorten the repeated summaries | JUDGEMENT | accept in part: § 4's second paragraph, § 3.3's tier paragraph, two passages of § 3.4's opening | the author |
| 9. Grzywny, Ryznar and Trojan, "Corollary 5.8" | CONFIRMED: the number is the published article's and is right; arXiv v1 has no such corollary and another Theorem 5.8; the paper does not print which numbering it follows | One sentence in the caption of Table 3; "of the published article" at the citation; the `TODO(release)` closed | the response plan |
| 10. Required change 13, the positioning of the strictness | depends on the agent on the short strictness proof; JUDGEMENT on the wording | Contribution 2 separated into the qualitative strictness and the quantitative family, as given | the author |
| 10. The qualifications, the "building blocks", the Student-t condition | CONFIRMED as the referee describes them | Keep; one clause added on p. 3 for the building blocks | the response plan |
