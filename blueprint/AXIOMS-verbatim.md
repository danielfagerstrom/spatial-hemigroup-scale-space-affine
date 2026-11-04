# Citation audit -- blueprint/AXIOMS.md, spatial-hemigroup-affine (A1-A6; A8 added by Q-0316, audited 2026-10-05; A9 added 2026-10-05, Q-0281 wave 2, group F; A10 added 2026-10-07, Q-0281 wave N; A11 added 2026-10-11, Q-0416)

Librarian pass, 2026-10-04. Every anchor below was opened from the held copy and rendered as a
page image through `library page <citekey> --printed N --format image`, then transcribed
independently of the ledger's own paraphrase and compared with the ledger's "Statement as used".
Page images are in the librarian's scratch directory, named <citekey>_printed<N>.png; none was
written into the repository. Two housekeeping notes on the held copies. (1) `urbanik1972levy` is a
two-up scan of 16 PDF pages (PDF page k holds printed pp. 116+2k and 117+2k), so printed p. 134
was imaged with `--printed 9 --offset 0` (it shares the page with p. 135); `--printed 134` alone
fails on this copy. (2) Sato's "Remarks on notation" (PDF page 13, printed xi, imaged with
`--printed 13 --offset 0`) was read for the weak-sense convention on "increasing/decreasing"
(see A2). Formulas are in LaTeX-ish plain text; [?] would mark an uncertain glyph (none occurs).

Overall finding: of six entries, five are MATCH or NARROWER-OK with nothing claimed beyond the
page, and one (A2) is a MATCH on its statement with a quotation slip in its Cite line (the page
says "A and gamma", the Cite line said "lambda and gamma"; corrected in the ledger and in
`records/affine/READING-sato1999levy-dimension-d.md` on the same date). No entry claims more than
its page.

---

## A1 -- A probability measure on R^d with integrable |mu-hat(z)||z|^n has a C^n density vanishing at infinity

**Cite:** sato1999levy -- Proposition 28.1, printed p. 190 (condition (28.1) and its conclusion;
the proof on the same page).

**Source, verbatim (Sato, p. 190).**
> PROPOSITION 28.1. *If a probability measure $\mu$ on $\mathbb{R}^d$ satisfies*
> (28.1)  $\int_{\mathbb{R}^d} |\hat\mu(z)|\,|z|^n\,dz < \infty$
> *for some $n \in \mathbb{Z}_+$, then $\mu$ has a density $g(x)$ of class $C^n$ and the partial
> derivatives of $g(x)$ of orders $0,\dots,n$ tend to $0$ as $|x| \to \infty$.*
>
> *Proof.* By Proposition 2.5(xii), the function $g(x)$ defined by
> $g(x) = (2\pi)^{-d} \int_{\mathbb{R}^d} e^{-i\langle x,z\rangle}\,\hat\mu(z)\,dz$
> is the density of $\mu$. The right-hand side is $n$ times differentiable with respect to $x$ and
> differentiation under the integral sign is possible by virtue of (28.1). Thus $g$ is of class
> $C^n$ and the Riemann-Lebesgue theorem applies.  [end-of-proof box]

Context on the same page, the sentence ending the preceding paragraph: "(Proposition 2.5(xii) and
the Riemann-Lebesgue theorem). Rapid decrease of $\hat\mu(z)$ as $|z| \to \infty$ implies
smoothness of $g(x)$." Sato's "Remarks on notation" (p. xi): "$\mathbb{Z}_+$, $\mathbb{Q}_+$, and
$\mathbb{R}_+$ are the collections of nonnegative elements of $\mathbb{Z}$, $\mathbb{Q}$, and
$\mathbb{R}$", so $n \in \mathbb{Z}_+$ includes $n = 0$.

**Ledger, statement as used:** "If a probability measure $\mu$ on $\mathbb{R}^d$ satisfies
$\int_{\mathbb{R}^d}|\hat\mu(z)|\,|z|^n\,dz<\infty$ for some $n\in\mathbb{Z}_+$, then $\mu$ has a
density $g$ of class $C^n$ on $\mathbb{R}^d$ and the partial derivatives of $g$ of orders
$0,\dots,n$ tend to $0$ as $|x|\to\infty$. Read at $n=0$ it says: an integrable characteristic
function gives a bounded continuous density vanishing at infinity."

**Verdict: MATCH.** Hypothesis (28.1), the range $n \in \mathbb{Z}_+$, the class $C^n$ and "orders
$0,\dots,n$ tend to $0$ as $|x|\to\infty$" agree word for word. The ledger's proof description
(inversion by 2.5(xii), differentiation under the integral, Riemann-Lebesgue) is the page's.
One remark, not a difference: "bounded" in the $n=0$ reading is not printed in the proposition. It
follows from continuity plus vanishing at infinity, and also directly from the inversion formula
($|g| \le (2\pi)^{-d}\int|\hat\mu|$).

---

## A2 -- The polar criterion: an infinitely divisible law on R^d is selfdecomposable exactly when its Levy measure has a radially nonincreasing polar profile

**Cite:** sato1999levy -- Theorem 15.10, printed p. 95 (formula (15.8), both directions);
Corollary 15.11, same page, for d = 1.

**Source, verbatim (Sato, p. 95).**
> Now we discuss selfdecomposable distributions. Let $S = \{\xi \in \mathbb{R}^d : |\xi| = 1\}$, the
> unit sphere.
>
> THEOREM 15.10. *Let $\mu$ be an infinitely divisible distribution on $\mathbb{R}^d$ with
> generating triplet $(A, \nu, \gamma)$. Then, $\mu$ is selfdecomposable if and only if*
> (15.8)  $\nu(B) = \int_S \lambda(d\xi) \int_0^\infty 1_B(r\xi)\,k_\xi(r)\,\frac{dr}{r}$
> *with a finite measure $\lambda$ on $S$ and a nonnegative function $k_\xi(r)$ measurable in
> $\xi \in S$ and decreasing in $r > 0$.*
>
> Selfdecomposability imposes no restriction on $A$ and $\gamma$.
>
> COROLLARY 15.11. *A probability measure $\mu$ on $\mathbb{R}$ is selfdecomposable if and only if*
> (15.9)  $\hat\mu(z) = \exp\Big[-\tfrac12 A z^2 + i\gamma z + \int_{-\infty}^\infty (e^{izx} - 1 - izx\,1_{[-1,1]}(x))\,\frac{k(x)}{|x|}\,dx\Big]$,
> *where $A \ge 0$, $\gamma \in \mathbb{R}$, $k(x) \ge 0$, $\int_{-\infty}^\infty (|x|^2 \wedge 1)\frac{k(x)}{|x|}\,dx < \infty$, and $k(x)$ is increasing on $(-\infty, 0)$ and decreasing on $(0, \infty)$.*

Convention, Sato p. xi: "for a real function $f$, increasing means $f(s) \le f(t)$ for $s < t$, and
decreasing means $f(s) \ge f(t)$ for $s < t$. When the equality is not allowed, we say strictly
increasing or strictly decreasing." So the source's "decreasing in $r>0$" is "nonincreasing" in the
strict-inequality-free sense. The unnumbered "Notes" on p. 117 read: "Theorem 15.10 is by Levy in
one dimension and by Wolfe [509] and Sato [390] in many dimensions" (text layer; supports the
ledger's attribution sentence, which names Wolfe).

**Ledger, statement as used:** "An infinitely divisible $\mu$ on $\mathbb{R}^d$ with generating
triplet $(A,\nu,\gamma)$ is self-decomposable if and only if
$\nu(B)=\int_S\lambda(d\xi)\int_0^\infty\mathbf 1_B(r\xi)\,k_\xi(r)\,dr/r$ for a finite measure
$\lambda$ on the unit sphere $S=S^{d-1}$ and a nonnegative $k_\xi(r)$, measurable in $\xi$ and
nonincreasing in $r>0$. Both directions are used [...]"

**Verdict: MATCH on the statement; DIFFERENCE in the Cite line's quotation (corrected).** The
theorem, (15.8), "finite measure", "nonnegative", "measurable in $\xi$" and the two-way "if and
only if" are as stated. "Nonincreasing" is correct under Sato's p. xi convention for "decreasing".
Corollary 15.11 is the $d=1$ case as the ledger says. The difference: the entry's **Cite** line
(and `records/affine/READING-sato1999levy-dimension-d.md`) quoted the page as "Selfdecomposability
imposes no restriction on $\lambda$ and $\gamma$". The page prints "**A and $\gamma$**", the
Gaussian matrix and the drift. $\lambda$ is the spherical measure, which the theorem does
constrain. The Cite line now reads "no restriction on $A$ and $\gamma$" (`03-isotropic.tex`
already did). The "Statement as used" bullet itself does not carry the slip, but
`prop:isotropic-polar-reading` (a law with a Gaussian part) relies on exactly this sentence, so
the quotation must be exact.

---

## A3 -- The Levy-Khintchine representation on R^d exists and its generating triplet is unique

**Cite:** sato1999levy -- Theorem 8.1, printed pp. 37-38 (clause (i) with (8.1)-(8.2) on p. 37, the
uniqueness clause (ii) and the converse (iii) on p. 38); Definition 8.2, same page.

**Source, verbatim (Sato, p. 37, last paragraph and Theorem 8.1(i)).**
> The following theorem gives a representation of characteristic functions of all infinitely
> divisible distributions. It is called the *Levy-Khintchine representation* or the
> *Levy-Khintchine formula*. It was obtained on $\mathbb{R}$ around 1930 by de Finetti and
> Kolmogorov in special cases, and then by Levy in the general case. It was immediately extended to
> $\mathbb{R}^d$. An essentially simpler proof on $\mathbb{R}$ was given by Khintchine. This theorem
> is fundamental to the whole theory. Let $D = \{x : |x| \le 1\}$, the closed unit ball.
>
> THEOREM 8.1. (i) *If $\mu$ is an infinitely divisible distribution on $\mathbb{R}^d$, then*
> (8.1)  $\hat\mu(z) = \exp\Big[-\tfrac12\langle z, Az\rangle + i\langle\gamma, z\rangle + \int_{\mathbb{R}^d} (e^{i\langle z,x\rangle} - 1 - i\langle z,x\rangle 1_D(x))\,\nu(dx)\Big]$,  $z \in \mathbb{R}^d$,
> *where $A$ is a symmetric nonnegative-definite $d \times d$ matrix, $\nu$ is a measure on
> $\mathbb{R}^d$ satisfying*
> (8.2)  $\nu(\{0\}) = 0$ *and* $\int_{\mathbb{R}^d} (|x|^2 \wedge 1)\,\nu(dx) < \infty$,

**Source, verbatim (Sato, p. 38).**
> *and $\gamma \in \mathbb{R}^d$.*
> (ii) *The representation of $\hat\mu(z)$ in (i) by $A$, $\nu$, and $\gamma$ is unique.*
> (iii) *Conversely, if $A$ is a symmetric nonnegative-definite $d \times d$ matrix, $\nu$ is a
> measure satisfying (8.2), and $\gamma \in \mathbb{R}^d$, then there exists an infinitely divisible
> distribution $\mu$ whose characteristic function is given by (8.1).*
>
> DEFINITION 8.2. We call $(A, \nu, \gamma)$ in Theorem 8.1 the *generating triplet* of $\mu$. The
> $A$ and the $\nu$ are called, respectively, the *Gaussian covariance matrix* and the *Levy measure*
> of $\mu$. When $A = 0$, $\mu$ is called *purely non-Gaussian*.

**Ledger, statement as used:** "An infinitely divisible $\mu$ on $\mathbb{R}^d$ has
$\widehat\mu(z)=\exp[-\tfrac12\langle z,Az\rangle+i\langle\gamma,z\rangle+\int(e^{i\langle
z,x\rangle}-1-i\langle z,x\rangle\mathbf 1_D(x))\nu(dx)]$ for a symmetric nonnegative-definite $A$,
a $\gamma\in\mathbb{R}^d$ and a measure $\nu$ with $\nu(\{0\})=0$ and
$\int(|x|^2\wedge1)\nu(dx)<\infty$; the triplet $(A,\nu,\gamma)$ is **unique**; and conversely
every such triplet occurs." With the entry's own quotations of (iii) and of (ii): *"(iii)
Conversely, if $A$ is a symmetric nonnegative-definite $d \times d$ matrix, $\nu$ is a measure
satisfying (8.2), and $\gamma \in \mathbb{R}^d$, then there exists an infinitely divisible
distribution $\mu$ whose characteristic function is given by (8.1)."* and *"The representation of
$\hat\mu(z)$ in (i) by $A$, $\nu$, and $\gamma$ is unique"* (p. 38).

**Verdict: MATCH.** (8.1), (8.2), uniqueness (ii) and the converse (iii) are as stated, and both
quotations the entry gives are letter-exact against the image. The ledger's $D$ is the closed unit
ball, defined in the paragraph on p. 37 above the theorem. The vocabulary list of Definition 8.2
(generating triplet, Gaussian covariance matrix, Levy measure, purely non-Gaussian for $A=0$) is
exact. The entry's remark on attribution is a mild compression: the page credits de Finetti and
Kolmogorov in special cases on $\mathbb{R}$, Levy in the general case, and Khintchine with a simpler
proof on $\mathbb{R}$.

---

## A4 -- A selfdecomposable law on R^d is infinitely divisible

**Cite:** sato1999levy -- Proposition 15.5, printed p. 93 (first sentence; proof on the same page);
Definition 15.1, printed p. 90.

**Source, verbatim (Sato, p. 90).**
> DEFINITION 15.1. Let $\mu$ be a probability measure on $\mathbb{R}^d$. It is called
> *selfdecomposable*, or *of class L*, if, for any $b > 1$, there is a probability measure $\rho_b$
> on $\mathbb{R}^d$ such that
> (15.1)  $\hat\mu(z) = \hat\mu(b^{-1}z)\,\hat\rho_b(z)$.
> It is called *semi-selfdecomposable* if there are some $b > 1$ and some infinitely divisible
> probability measure $\rho_b$ satisfying (15.1). If $\mu$ is semi-selfdecomposable, then $b$ in the
> definition is called a *span* of $\mu$.

**Source, verbatim (Sato, p. 93).**
> PROPOSITION 15.5. *If $\mu$ is selfdecomposable, then $\mu$ is infinitely divisible and, for any
> $b > 1$, $\rho_b$ in (15.1) is uniquely determined and infinitely divisible. If $\mu$ is
> semi-selfdecomposable, then $\mu$ is infinitely divisible and $\rho_b$ is uniquely determined.*
>
> *Proof.* Let $\mu$ be selfdecomposable. Then Theorem 9.3 and the proof of Theorem 15.3 show the
> infinite divisibility of $\mu$ and $\rho_b$. The uniqueness of $\rho_b$ comes from the fact that
> $\hat\mu(z)$ has no zero by Lemma 7.5.

(The page also carries, above the proposition, the end of the proof of Theorem 15.3: the null array
$\{n^{-1}Z_k\}$ "by Exercise 12.12", with (15.2) and (15.3) holding with $b_n = n^{-1}$ and
$c_n = 0$.)

**Ledger, statement as used:** "If a probability measure $\mu$ on $\mathbb{R}^d$ is
self-decomposable, that is if for every $b > 1$ there is a probability measure $\rho_b$ on
$\mathbb{R}^d$ with $\widehat\mu(z) = \widehat\mu(b^{-1}z)\,\widehat\rho_b(z)$ for every $z$
(Definition 15.1, (15.1)), then $\mu$ is infinitely divisible." Primary, quoted: *"If $\mu$ is
selfdecomposable, then $\mu$ is infinitely divisible and, for any $b > 1$, $\rho_b$ in (15.1) is
uniquely determined and infinitely divisible."*

**Verdict: NARROWER-OK.** The quoted sentence is exact against the image, and the ledger's
Definition 15.1 reading is the page's (the "for every $z$" quantifier is implicit in (15.1)). The
entry uses only "$\mu$ is infinitely divisible", a strict part of the first sentence, and says so
in "What the entry does NOT carry" (uniqueness and infinite divisibility of $\rho_b$, and the
semi-selfdecomposable clause). The statement of how it is proved (Theorem 9.3 plus the proof of
Theorem 15.3, the null-array argument) is the page's. This shares its root with A6: the proof of
15.5 spends Theorem 9.3.

---

## A5 -- An operator-selfdecomposable law, with a contracting exponent, and its residuals are infinitely divisible

**Cite:** jurek1993operator -- Theorem 3.3.5, printed p. 83 (last sentence), with the opening of
§ 3.4, printed pp. 89-90; original urbanik1972levy Proposition 5.2, printed p. 134.

**Source, verbatim (Jurek-Mason, p. 83).**
> **Theorem 3.3.5.** *A full measure $\mu$ on $\mathbb{R}^d$ is operator-decomposable if and only if
> its Urbanik decomposability semigroup $\mathbf{D}(\mu)$ contains a one-parameter semigroup
> $\{\exp(-tQ): t \ge 0\}$ with $Q$ invertible and $\exp(-tQ) \to 0$ as $t \to \infty$.
> Furthermore, if $\mu = \exp(-tQ)\mu * \mu_t$, for $t \ge 0$, then each $\mu_t$ is infinitely
> divisible.*

**Source, verbatim (Jurek-Mason, p. 89, § 3.4 opening).**
> In this section, we specialize the concept of operator-selfdecomposable to a particular $Q$ with
> $\exp(-tQ) \to 0$ as $t \to \infty$. The assumption of fullness in Theorem 3.3.5 was used only in
> the proof of the necessity, so we may drop that assumption in this section. For $Q$ with
> $\exp(-tQ) \to 0$ as $t \to \infty$, we say that a measure $\mu$ is $\exp(-tQ)$-*decomposable* if
> for each $t \ge 0$, there is a measure $\nu_t$ such that
> (3.4.1)  $\mu = \exp(-tQ)\mu * \nu_t$.
> From the last part of Theorem 3.3.5, each $\nu_t$ is infinitely divisible. The

**Source, verbatim (Jurek-Mason, p. 90, continuation).**
> assumption on $Q$ implies $\nu_t \Rightarrow \mu$ as $t \to \infty$, so $\mu$ is also infinitely
> divisible [cf. Proposition 1.8.1(b)].

(Same page, for the "does NOT carry" bullet: "**Proposition 3.4.1.** *A measure $\mu = [a,R,M]$ is
$\exp(-tQ)$-decomposable if and only if (a) for each $t \ge 0$ and each $y \in \mathbb{R}^d$,
$\langle Ry,y\rangle \ge \langle\exp(-tQ)R\exp(-tQ^*)y,y\rangle$; (b) for each $t \ge 0$ and each
Borel subset $B$ of $\mathbb{R}^d \setminus \{0\}$, $M(B) \ge M(\exp(tQ)B)$.*" Printed p. 53,
for $\mathbf{D}(\mu)$: "$\mathbf{D}(\mu) := \{A \in \mathrm{End}: \mu = A\mu * \mu_A$ for some
$\mu_A \in \mathscr{P}\}$", $\mathscr{P}$ the probability measures.)

**Source, verbatim (Urbanik 1972, p. 134, bottom of the left page).**
> PROPOSITION 5.2. *Suppose that a one-parameter semigroup $\exp tQ$ ($t \ge 0$) fulfils the
> condition $\lim_{t\to\infty} \exp tQ = 0$. Then each $\exp tQ$-decomposable for $t \ge 0$
> probability measure $\mu$ is a Levy's measure. Moreover, for every $t \ge 0$
> $\mu = \exp tQ\,\mu * \lambda_t$, where $\lambda_t$ is an infinitely divisible measure.*

**Source, verbatim (Urbanik 1972, p. 136, § 6 first paragraph).**
> By Proposition 5.2 all such measures are Levy's measures and, consequently, are infinitely
> divisible.

(Same page: "Namely, $\lim_{t\to\infty}\exp tQ = 0$ if and only if all eigenvalues of $Q$ have
negative real part." The sentence introducing "Levy's measure" as a limit law, on p. 119, was not
re-imaged in this pass; the entry cites it only for the name.)

**Ledger, statement as used:** "Let $B$ be a real $d \times d$ matrix with $e^{-tB} \to 0$ as
$t \to \infty$, and let $\mu$ be a probability measure on $\mathbb{R}^d$ such that for every
$t \ge 0$ there is a probability measure $\rho_t$ with $\mu = (e^{-tB})_*\mu * \rho_t$. Then every
$\rho_t$ is infinitely divisible, and so is $\mu$."

**Verdict: MATCH** (the ledger's own quotations of all three passages are letter-exact against the
images). Reasoning, in three points.
- *The last sentence of Theorem 3.3.5* is stated for a full $\mu$. The ledger does not rest on it
  alone: it adds the § 3.4 opening, which states that fullness was used only for the necessity and
  is dropped, and then draws both conclusions (each $\nu_t$ infinitely divisible, and $\mu$ too, via
  $\nu_t \Rightarrow \mu$). The ledger's statement without fullness is therefore exactly § 3.4's.
  It is also Urbanik's Proposition 5.2, which is stated for every probability measure.
- *The sign and the hypotheses.* Jurek-Mason's $Q$ is the ledger's $B$, with the same sign
  ($\exp(-tQ)$). Urbanik's $Q$ is $-B$. "$Q$ invertible" in Theorem 3.3.5 is automatic from
  $\exp(-tQ) \to 0$ and is not needed as a separate hypothesis. That "measure" means probability
  measure in § 3.4 is not printed in the opening itself but is the book's convention
  ($\mathscr{P}$ on p. 53); Urbanik says "probability measure" explicitly.
- *The $\mu$-infinitely-divisible conclusion* rests on Proposition 1.8.1(b) of Jurek-Mason, which
  was not re-read. Urbanik's p. 136 sentence supplies the same conclusion independently ("all such
  measures are Levy's measures and, consequently, are infinitely divisible"). The ledger names both.

---

## A6 -- Khintchine's theorem: the limit of the row sums of a null array on R^d is infinitely divisible

**Cite:** sato1999levy -- Theorem 9.3, printed p. 47, with Definition 9.2 and (9.1) on the same
page; Definition 2.2, printed p. 7, for "converges"; the sentence after Definition 2.4, printed
p. 8, for the law of a sum of independent variables.

**Source, verbatim (Sato, p. 47).**
> DEFINITION 9.2. A double sequence of random variables $\{Z_{nk} : k = 1, 2, \dots, r_n;\ n = 1, 2, \dots\}$
> on $\mathbb{R}^d$ is called a *null array* if, for each fixed $n$, $Z_{n1}, Z_{n2}, \dots, Z_{nr_n}$
> are independent and if, for any $\varepsilon > 0$,
> (9.1)  $\lim_{n\to\infty} \max_{1\le k\le r_n} P[\,|Z_{nk}| > \varepsilon\,] = 0$.
> The sums $S_n = \sum_{k=1}^{r_n} Z_{nk}$, $n = 1, 2, \dots$, are called the *row sums*.
>
> THEOREM 9.3 (Khintchine [254]). *Let $\{Z_{nk}\}$ be a null array on $\mathbb{R}^d$ with row sums
> $S_n$. If, for some $b_n \in \mathbb{R}^d$, $n = 1, 2, \dots$, the distribution of $S_n - b_n$
> converges to a distribution $\mu$, then $\mu$ is infinitely divisible.*

**Source, verbatim (Sato, p. 7).**
> DEFINITION 2.2. A sequence of probability measures $\mu_n$, $n = 1, 2, \dots$, *converges* to a
> probability measure $\mu$, written as $\mu_n \to \mu$ as $n \to \infty$, if, for every bounded
> continuous function $f$,
> $\int_{\mathbb{R}^d} f(x)\mu_n(dx) \to \int_{\mathbb{R}^d} f(x)\mu(dx)$ as $n \to \infty$.

**Source, verbatim (Sato, p. 8).**
> DEFINITION 2.4. The *convolution* $\mu$ of two distributions $\mu_1$ and $\mu_2$ on
> $\mathbb{R}^d$, denoted by $\mu = \mu_1 * \mu_2$, is a distribution defined by
> (2.2)  $\mu(B) = \iint_{\mathbb{R}^d \times \mathbb{R}^d} 1_B(x+y)\,\mu_1(dx)\mu_2(dy)$,  $B \in \mathscr{B}(\mathbb{R}^d)$.
> The convolution of two finite measures on $\mathbb{R}^d$ is defined by the same formula.
>
> The convolution operation is commutative and associative. If $X_1$ and $X_2$ are independent
> random variables on $\mathbb{R}^d$ with distributions $\mu_1$ and $\mu_2$, respectively, then
> $X_1 + X_2$ has distribution $\mu_1 * \mu_2$.

For "distribution" = probability measure: p. 2 (text layer only, not imaged) reads "In general,
probability measures on $\mathscr{B}(\mathbb{R}^d)$ are called distributions on $\mathbb{R}^d$."

**Ledger, statement as used:** "Let $\mu_{n,k}$, $1 \le k \le r_n$, $n = 1, 2, \dots$, be
probability measures on $\mathbb{R}^d$ with $\lim_{n\to\infty}\max_{1\le k\le r_n}\mu_{n,k}(\{|x| >
\varepsilon\}) = 0$ for every $\varepsilon > 0$. If $\mu_{n,1} * \dots * \mu_{n,r_n} *
\delta_{-b_n}$ converges weakly to a probability measure $\mu$ for some $b_n \in \mathbb{R}^d$,
then $\mu$ is infinitely divisible." Primary: quotations of Theorem 9.3, Definition 9.2 and the
p. 8 sentence.

**Verdict: MATCH.** Definition 9.2 with (9.1) and Theorem 9.3 are as quoted in the entry, letter
for letter against the image. The measure form is the theorem read through a realization of the
rows by independent random variables with laws $\mu_{n,k}$: the null-array condition (9.1) becomes
$\mu_{n,k}(\{|x|>\varepsilon\}) \to 0$ uniformly in $k$, the law of $S_n - b_n$ is
$\mu_{n,1}*\dots*\mu_{n,r_n}*\delta_{-b_n}$ by the p. 8 sentence, and "converges" is Definition
2.2 (the ledger's "converges weakly"). The translation is disclosed in the entry. Note that
$*\delta_{-b_n}$ for the shift is not printed as such: it is the standard identification of the law
of $X - b$ and uses only (2.2). The page states the theorem on $\mathbb{R}^d$ for any array size
$r_n$ and any $b_n$, which is more than the single use ($r_n = n + 1$, $b_n = 0$) the entry makes, so
the use is within the source. [Q-0281 wave 2, blind review W2C-5: the audit wrote $r_n = n$; the use
as machine-checked, and as `AXIOMS.md` § A6 and the blueprint proof state it, has $r_n = n + 1$. The
verdict does not depend on it.]

---

## A8 -- Wolfe's theorem: a symmetric selfdecomposable law on R^d is symmetric unimodal in Kanter's sense

*Librarian pass, 2026-10-05, independent audit. Every anchor below was opened from the held copy and
rendered as a page image through `library page <citekey> --printed N --format image` (Wolfe pp. 141,
142, 143, 144; Kanter pp. 65, 66, 67, 69, 70, 72; Sato pp. 90, 91), then transcribed independently of
the earlier transcription (Q-0316, 2026-10-04) and of the ledger's own paraphrase. Page images are in
the librarian's scratch directory, named <citekey>_printed<N>.png; none was written into the
repository. Kanter's pp. 68, 71, 73-81 and Wolfe's p. 145 were read from the text layer for context
only, and nothing below rests on them except where said. Formulas are in LaTeX-ish plain text; [?]
would mark an uncertain glyph (none occurs).*

**Cite:** wolfe1978unimodality -- Theorem 2, printed p. 144, with the definition of U_n on the same
page, and the definition of class L, pp. 141-142; kanter1977unimodality -- Definition 1.2 (p. 66)
with Definition 1.1 (p. 66), and Definition 3.1 (p. 70) with the convention paragraph above it
(p. 70) and Corollary 3.1 (p. 72); sato1999levy -- Definition 15.1 (p. 90), Theorem 15.3(ii) (p. 91).

**Source, verbatim (Wolfe, p. 144).**
> Let $W_n$ stand for the set of all probability measures on $R_n$ and let $\lambda_k(A) =
> \mu(K \cap A)$ for all Borel measurable sets in $R_n$ where $\mathbf{u}$ denotes Lebesgue measure and
> $K$ is a compact, convex, symmetric subset of $R_n$. Let $U_n$ stand for all measures $\mathbf{u}$
> on $R_n$ that are of the form
> $\mu = \int_{W_n}\lambda_K\,d\eta(\lambda_K)$
> where $\eta$ is a measure on $W_n$. Kanter [3] defines an $n$-dimensional distribution function to be
> symmetric unimodal if it generates a measure that is contained in $U_n$. The class of $n$-dimensional
> symmetric unimodal distribution functions properly contains the class of $n$-dimensional, symmetric
> distribution functions that are $n$-unimodal in the sense of Olshen and Savage [5].
>
> THEOREM 2. *A symmetric $n$-dimensional distribution function of class $L$ is symmetric unimodal.*

Typography of the page, exactly:
- The first sentence prints "$\lambda_k(A)$" with a lower-case $k$, then "$\mu(K \cap A)$" with an
  italic $\mu$, and says "where **u** denotes Lebesgue measure" (bold $\mathbf{u}$). So the italic $\mu$
  in $\mu(K\cap A)$ and the bold $\mathbf{u}$ both stand for Lebesgue measure.
- The bold $\mathbf{u}$ also names the elements of $U_n$ ("all measures $\mathbf{u}$ on $R_n$"), while
  the displayed mixture is called $\mu$.
- The page does not normalise $\lambda_K$ and does not restrict $W_n$ to the $\lambda_K$.

Same paper, pp. 141–142: the definition of "symmetric" and of class L, which continues onto p. 142.

p. 141:
> Let $\mathscr{B}$ denote the Borel sets of $R_n$. Let $F(\mathbf{x})$ be an $n$-dimensional
> distribution function and let $P$ be the probability measure generated by $F(\mathbf{x})$. The
> distribution function $F(\mathbf{x})$ is said to be symmetric if $P(B) = P(-B)$ for every
> $B \in \mathscr{B}$. [...] A distribution function $F(\mathbf{x})$ defined on $R_n$ is said to be a
> distribution function of class $L$ if there exists a sequence of independent random variables
> $\mathbf{X}_1, \mathbf{X}_2, \dots$ such that for suitable vectors $\mathbf{A}_k$ and constants
> $B_k > 0$ the random variables
> $\mathbf{Y}_k = (\mathbf{X}_1 + \cdots + \mathbf{X}_k)/B_k - \mathbf{A}_k$

p. 142 (continuing the same sentence):
> have the property that $F_{\mathbf{Y}_k} \to_c F$ and in addition the random variables
> $\mathbf{X}_{k,j} = \mathbf{X}_j/B_k \quad (1 \le j \le k)$
> form an infinitesimal system.

(The arrow carries a subscript $c$; the page does not define it, nor "infinitesimal system".)

**Source, verbatim (Kanter, p. 66).**
> *Notation.* [...] We let $\mathrm{span}(U)$ be the affine subspace spanned by $U$ and
> $\mathrm{conv}(U)$ be the least convex set containing $U$.
> We let $\dim(U)$ = dimension of $\mathrm{span}(U)$.
> Finally if $U$ is a convex set and $L = \mathrm{span}(U)$, we let $U_L^\circ$ stand for the interior of
> $U$ when viewed as a subset of $L$.
>
> DEFINITION 1.1. If $L$ is a linear subspace of $R^N$ of dimension $k$, we let $\mathrm{Vol}_L$ stand
> for $k$-dimensional Lebesgue measure on $L$, with the normalizing condition that
> $\mathrm{Vol}_L(B(1)) = \pi^{k/2}/\Gamma(1 + \frac12 k)$.
>
> If $L'$ is an affine subspace of $R^N$ of the form $L' = L + x$ where $L$ is a linear subspace of
> $R^N$ we let $\mathrm{Vol}_{L'}(A') = \mathrm{Vol}_L(A)$ where $A' = A + x$ and $A$ is any Borel
> subset of $L$.
>
> DEFINITION 1.2. If $K$ is a compact, convex subset of $R^N$ we define the probability measure
> $\lambda_K$ on $R^N$ by
> (1.2)  $\lambda_K(A) = \mathrm{Vol}_L(A \cap K)/\mathrm{Vol}_L(K)$
> where $A$ is any Borel subset of $R^N$ and $L$ is the affine subspace spanned by $K$.
>
> *Measures and metric spaces.* Let $\mathfrak{M}$ be a metric space with metric $d$. A measure on
> $\mathfrak{M}$ is a countably additive $[0,\infty]$ valued set function on the $\sigma$-field of Borel
> subsets of $\mathfrak{M}$, i.e. those sets generated by the open subsets of $\mathfrak{M}$. A
> probability measure on $\mathfrak{M}$ is a measure on $\mathfrak{M}$ with $\mu(\mathfrak{M}) = 1$.
>
> DEFINITION 1.3. Let $\mathfrak{M}$ be a metric space. Let $\mu_n$ be a sequence of bounded measures
> on $\mathfrak{M}$ and let $\mu$ be a bounded measure on $\mathfrak{M}$. We write
> $\mu_n \to^w \mu$ (and say $\mu_n$ converges weakly to $\mu$) if
> (1.3)  $\int f\,d\mu_n \to \int f\,d\mu$
> for all bounded, continuous, real valued functions on $\mathfrak{M}$.

(Page 66 prints "$\mu_n \to^w \mu$ (and say u_n converges weakly to $\mu$)".)

**Source, verbatim (Kanter, p. 67).**
> It is well known (see Parthasarathy [9]) that if $\mathfrak{M}$ is separable then the set of
> probability measures on $\mathfrak{M}$ may be made into a separable metric space
> $(\mathfrak{M}^+, d^+)$ where $d^+(\mu_n, \mu) \to 0$ if and only if $\mu_n \to^w \mu$. If
> $\mathfrak{M}$ is complete then $\mathfrak{M}^+$ will also be complete. [...] If
> $\mathfrak{M} = R^N$ we shall use the notation $\mathfrak{M}^+ = \mathfrak{M}_N^+$ [...]. If
> $\mathfrak{M} = L$, a linear subspace of $R^N$, we shall write $\mathfrak{M}^+ = \mathfrak{M}_L^+$
> [...].

**Source, verbatim (Kanter, p. 69).**
> DEFINITION 2.2. Let $L$ be a linear subspace of $R^N$. We shall denote by $T_L$ the set of all
> log-concave, symmetric nonnegative functions $f$ on $L$ with $\int_L f\,d\mathrm{Vol}_L = 1$, and we
> shall denote by $T_L^*$ the set of all probability measures $\mu$ on $L$ of the form
> $d\mu = f\,d\mathrm{Vol}_L$ where $f \in T_L$.

**Source, verbatim (Kanter, p. 70).**
> 3. **Symmetric unimodal random vectors.** [...] We shall often be dealing with sets $\mathfrak{S}$
> which consist of a subset of the collection of all probability measures on some metric space
> $\mathfrak{M}$ and we shall need to have a uniform convention for the concept of Borel subsets of
> $\mathfrak{S}$. Our convention shall be to endow $\mathfrak{S}$ with the Borel structure consisting of
> the least $\sigma$-field containing all those subsets $U$ of $\mathfrak{S}$ which are open in the
> topology of weak convergence of probability measures.
>
> DEFINITION 3.1. Let $L$ be a linear subspace of $R^N$. We shall let $W_L$ stand for the set of all
> probability measures on $L$ of the form $\lambda_K$ where $K$ is a compact symmetric subset of $L$.
> We give $W_L$ the Borel structure mentioned above.
>
> We let $U_L$ stand for all the measures $\mu$ on $R^N$ which are of the form
> (3.1)  $\mu = \int_{W_L}\lambda_K\,d\nu(\lambda_K)$
> where $\nu$ is a measure on $W_L$. We call $\nu$ the mixing measure for $\mu$. (We shall later show
> that $W_L$ is a Borel measurable subset of $\mathfrak{M}_L^+$.) We note that $\mu$ in (3.1) is a
> probability measure if and only if $\nu$ is a probability measure.
>
> We shall use the notation $W_{R^N} = W_N$ and $U_{R^N} = U_N$. We shall call a random vector in
> $R^N$, symmetric unimodal if its distribution is in $U_N$. We note that if $\mu$ is a symmetric
> probability measure on $R$ which is unimodal in the standard 1-dimensional sense, then by Feller
> [4, p. 158] we have $\mu \in U_1$.

**Source, verbatim (Kanter, p. 72).**
> COROLLARY 3.1. *$W_L$ is a Borel subset of $\mathfrak{M}_L^+$.*
>
> PROOF. We have $W_L \subset T_L^* \subset \mathfrak{M}_L^+$. Using Corollary 2.3 we know that
> $T_L^*$ is a complete metric space under the total variation metric; also the imbedding
> $T_L^* \subset \mathfrak{M}_L^+$ is continuous where $T_L^*$ is given the topology determined by the
> total variation metric while $\mathfrak{M}_L^+$ is given the topology determined by weak convergence
> of probability measures. We conclude by a theorem of Kuratowski [7, p. 21] that $T_L^*$ is a Borel
> subset of $\mathfrak{M}_L^+$. [...] Noting $W_L = J^{-1}(H)$, by Lemma 3.2 we conclude that $W_L$ is
> a Borel subset of $T_L^*$. Since $T_L^*$ is a Borel subset of $\mathfrak{M}_L^+$, we are done.
> Q.E.D.

**Source, verbatim (Sato, p. 90).**
> DEFINITION 15.1. Let $\mu$ be a probability measure on $\mathbb{R}^d$. It is called
> *selfdecomposable, or of class L*, if, for any $b > 1$, there is a probability measure $\rho_b$ on
> $\mathbb{R}^d$ such that
> (15.1)  $\widehat\mu(z) = \widehat\mu(b^{-1}z)\widehat\rho_b(z)$.

**Source, verbatim (Sato, p. 91).**
> THEOREM 15.3. (i) *Let $\{Z_n : n = 1, 2, \dots\}$ be independent random variables on
> $\mathbb{R}^d$ and $S_n = \sum_{k=1}^n Z_k$. Let $\mu$ be a probability measure on $\mathbb{R}^d$.
> Suppose that there are $b_n > 0$ and $c_n \in \mathbb{R}^d$ for $n = 1, 2, \dots$ such that*
> (15.2)  $P_{b_nS_n + c_n} \to \mu$ as $n \to \infty$
> *and that*
> (15.3)  $\{b_nZ_k : k = 1, \dots, n;\ n = 1, 2, \dots\}$ *is a null array.*
> *Then, $\mu$ is selfdecomposable.*
> (ii) *For any selfdecomposable distribution $\mu$ on $\mathbb{R}^d$ we can find $\{Z_n\}$
> independent, $b_n > 0$, and $c_n \in \mathbb{R}^d$ satisfying (15.2) and (15.3).*

(Null array is Sato's Definition 9.2, p. 47, transcribed under A6. The proof of Lemma 15.4 on the same
page restates (15.3) as "for any $\varepsilon > 0$, $\max_{1\le k\le n} P[b_n|Z_k| > \varepsilon] \to 0$".)

**Comparison with the earlier transcription (2026-10-04).** Where the earlier transcription quotes, it
is accurate; no word inside a verbatim blockquote is wrong. The differences:
1. **Wolfe, p. 144.** The quotation is letter-exact up to where it stops, but it stops before the
   Olshen–Savage sentence. Its parenthetical on "u" and "μ" is imprecise (see the typography note
   above).
2. **The Primary bullet in `AXIOMS.md`** writes "$\lambda_K(A) = \mu(K\cap A)$"; the page has the
   lower-case $\lambda_k(A)$.
3. **Wolfe's definition of class L** runs over pp. 141–142, not p. 141 alone; the "infinitesimal
   system" clause is on p. 142.
4. **Kanter, p. 66.** The earlier transcription omits the affine clause of Definition 1.1, which is
   needed because $L$ in (1.2) is an affine subspace.
5. **Kanter, p. 70.** Its elision swallowed two passages: the Borel-structure convention paragraph, and
   the parenthesis promising that $W_L$ is Borel. That promise is kept by Corollary 3.1 on p. 72, which
   is now transcribed above.
6. **Sato, p. 91.** Theorem 15.3(i) is now transcribed in full.
7. **The earlier reading of Wolfe's $U_n$ in Kanter's sense is confirmed.**

**Verdict: MATCH**, read in Kanter's sense (not Wolfe's printed definition) and using only direction
(ii) of Sato's Theorem 15.3.
- **The conclusion.** The entry's $u_K$, $W_d$ and $\Lambda$ are Kanter's Definitions 1.2 and 3.1 under
  the module's names. For a symmetric nonempty $K$, $0 \in K$, so its affine span is linear.
- **The hypothesis.** "Symmetric" is Wolfe's p. 141 definition. "Self-decomposable implies class L" is
  Sato's Theorem 15.3(ii) with $B_k = 1/b_k$ and $A_k = -c_k$.
- **Not printed** (these are reading steps, not differences):
  - Wolfe does not define "infinitesimal system" or the arrow $\to_c$.
  - The case $k = 0$: Definition 1.1 at $k = 0$ gives $\lambda_{\{x\}} = \delta_x$.
  - $\mathrm{Vol}_L(K) > 0$ for a nonempty compact convex $K$ is used tacitly.
  - The entry names no $\sigma$-algebra on $W_d$; Kanter's is the weak-topology Borel structure.

**(a) Does Kanter's $\lambda_K$ presuppose $K$ nonempty?** Tacitly, yes; it is not stated. For the
empty set (1.2) is $0/0$, and Kanter's span/dim are not defined. The Lean interface should require
`K.Nonempty`; for a symmetric $K$ that is equivalent to $0 \in K$.

**(b) The $\sigma$-algebra on the mixing measures.**
- **Kanter states it (p. 70):** the least $\sigma$-field containing the weakly open subsets (weak
  convergence as in Def. 1.3; on a separable space it is metrisable, p. 67).
- **"$W_L$ is a Borel subset" is stated** as Corollary 3.1, p. 72.
- **Wolfe puts no topology or $\sigma$-algebra** on $W_n$.
- **Caveat on Kanter's printed proof of Corollary 3.1.** The proof starts from
  $W_L \subset T_L^*$ (densities w.r.t. $\mathrm{Vol}_L$), so at face value it covers only $K$ with
  nonempty interior in $L$. The lower-dimensional $\lambda_K$ have no such density.
- **Consequence for Lean:** do not make "$W_d$ is a measurable subset" a theorem of the interface. State
  $\Lambda$ as a measure on the ambient space of probability measures (the Giry $\sigma$-algebra on
  `Measure (Rd d)`), concentrated on $W_d$.

**Addendum, 2026-10-12 (Q-0424): the pages behind the Gaussian part.** Read for the response to
the external review of the isotropic paper (`records/affine/reviews/VERIFY-round1-mathematics.md`,
item 6(b)) by the session of Q-0424, each page rendered with `library page kanter1977unimodality
--printed N --format image` (N = 68, 69, 70, 71, 72, 74, 77, 78, 84) and transcribed from the
image. They back the entry for the laws with a Gaussian part (`AXIOMS.md`, A8, "The Gaussian
part"). The statement of the entry and the audit above are not changed by them.

**Source, verbatim (Kanter, p. 68).**
> DEFINITION 2.1. We say that a probability measure $\mu$ on $R^N$ is logarithmically concave if
> for all open, convex sets $C, D \subset R^N$ and $t \in (0, 1)$ we have
> (2.1)  $\mu(tC + (1 - t)D) \ge (\mu(C)^t)(\mu(D)^{1-t})$.
> [...] If we let $L = \mathrm{span}(\mathrm{supp}(\mu))$ it is natural to conjecture that
> $d\mu = f\,d\,\mathrm{Vol}_L$ for some logarithmically concave function $f$ on $L$. (A function
> $f$ is said to be log-concave if $\log f$ has values in $[-\infty, +\infty)$ and is concave.)
> This conjecture has recently been proved in [2, p. 123]. The converse to this conjecture was
> demonstrated by Prekopa [10]. We combine these results to get the following key lemma.
>
> LEMMA 2.1. *Let $\mu$ be a logarithmically concave measure on $R^N$. Then there exists a linear
> subspace $L$ of $R^N$ and a log-concave density function $f$ such that $d\mu = f\,d\,\mathrm{Vol}_L$.
> Conversely if $L$ and a log-concave density function $f$ are given, then the measure $\mu$
> defined by $d\mu = f\,d\,\mathrm{Vol}_L$ is logarithmically concave.*

**Source, verbatim (Kanter, p. 70).**
> LEMMA 3.1. *Let $L$ be a linear subspace of $R^N$ and let $\mu$ be a log-concave, symmetric,
> probability measure on $L$ with $d\mu/d\,\mathrm{Vol}_L = f$ where $f \in T_L$. Then
> $\mu \in U_L$.*
>
> PROOF. Let $D_s = \{y \mid f(y) \ge s\}$ for $s > 0$. We have $f(x) = \int_0^\infty I_{D_s}(x)\,ds$;
> hence it follows that for any Borel subset $A$ of $L$,

(The proof continues on p. 71: *"Now $D_s$ is a bounded convex subset of $L$ for $s > 0$"*,
$K_s = \mathrm{cl}(D_s)$, and (3.6),
$\int_A f(x)\,d\,\mathrm{Vol}_L(x) = \int_{W_L}\lambda_K(A)\,d\nu(\lambda_K)$, *"hence we conclude
that $\mu \in U_L$ with mixing measure $\nu$."* $T_L$ is Definition 2.2, p. 69, transcribed above.)

**Source, verbatim (Kanter, p. 74).**
> We now prove that symmetric unimodal probability measures on $R^N$ are closed under
> convolution. [...]
>
> THEOREM 3.2. *Let $\mu_1, \mu_2 \in U_N$. Then $\mu_1 * \mu_2 \in U_N$.*

**Source, verbatim (Kanter, p. 77).**
> It is well known that we can write the characteristic function $\phi_X(v) = E(e^{i(v\cdot X)})$ of
> the random vector $X$ in the form (due to Levy and Khinchine)
> (4.1)  $\log(\phi_X(v)) = \int_{R^N}(\cos(v\cdot y) - 1)\,dM_X(y) - q_X(v)$
> where $M_X$ is a symmetric measure on $R^N$ with $M_X(\{0\}) = 0$, $M_X(B(a)^c) < \infty$ and
> $\int_{B(a)}(\|y\|_2)^2\,dM_X(y) < \infty$ for all $a > 0$; while $q_X(y) = (B_Xy \cdot B_Xy)$ for
> some symmetric matrix $B_X$. [...] We shall assume $q_X \equiv 0$, unless otherwise stated (no
> Gaussian part).

**Source, verbatim (Kanter, p. 78).**
> THEOREM 4.1. *Let $X$ be a symmetric infinitely divisible random vector in $R^N$. Suppose the
> Levy-Khinchine measure $M_X$ is in $U_N$; then $X$ is a symmetric unimodal random vector in
> $R^N$.*

**Source, verbatim (Kanter, p. 84).**
> Comparing the above notions of unimodality to our own we see clearly that any symmetric random
> vector $X$ which is unimodal according to Anderson or Sherman is unimodal in our sense as well.

**Reading.** A centred Gaussian law on $R^N$ with covariance $A \ne 0$ has, on the range $L$ of
$A$, a density proportional to $\exp(-\tfrac12\langle x, (A|_L)^{-1}x\rangle)$: a symmetric
log-concave function of integral $1$, so it is in $T_L$, the law is log-concave by the second
half of Lemma 2.1, and Lemma 3.1 puts it in $U_L$. The inclusion $U_L \subseteq U_N$ is not
printed. It is immediate from Definition 3.1: $W_L \subseteq W_N$, with the relative weak
topology. Theorem 3.2 then gives the convolution of that law with a member of $U_N$.

---

## A9 -- Gel'fand-Naimark(-Lidskii) log-majorization of the spectrum of a product of positive matrices

Librarian pass, 2026-10-06 (supersedes the 2026-10-05 pass, which read PDM only). Anchors opened from the
held copies of bhatia2007positive (PDM, N = 228, 1, 5, 224, 253) and bhatia1997matrix (MA, GTM 169,
Springer 1997; N = 4, 28, 29, 30, 35, 50, 57, 58, 70, 71, 72, 73; printed = pdf - 12) and rendered as page
images (`library page <citekey> --printed N --format image`), transcribed independently of any ledger
paraphrase. **MA was read** at the page the PDM exercise points to ("MA p. 73") and in Chapters II and III
for the definitions. Formulas are in LaTeX-ish plain text; [?] would mark an uncertain glyph (none occurs).

**Cite:** bhatia1997matrix -- Corollary III.4.6 (Lidskii), relation (III.21), printed p. 73 (pdf 85); the
symbol $\prec$ on logarithms as in (III.15), printed p. 71, and (II.2)-(II.3), printed p. 28; the
Gel'fand-Naimark singular-value theorem it is derived from is Theorem III.4.5, (III.17), printed p. 71.
Parallel: bhatia2007positive -- Exercise 6.5.3, relation (6.47), printed p. 228, which is (III.21)
verbatim and points to "MA p. 73". The right half of (III.21) is the one the Paper VII entry uses.

**Source, verbatim (Bhatia MA, p. 73).**
> Corollary III.4.6 (Lidskii) Let $A, B$ be two positive matrices. Then all eigenvalues of $AB$ are
> nonnegative and
>
> $\log\lambda^{\downarrow}(A) + \log\lambda^{\uparrow}(B) \prec \log\lambda(AB) \prec \log\lambda^{\downarrow}(A) + \log\lambda^{\downarrow}(B).$   (III.21)
>
> Proof. It is enough to prove this when $B$ is invertible, since every positive matrix is a limit of
> such matrices. For invertible $B$ we can write
> $AB = B^{-1/2}(B^{1/2}AB^{1/2})B^{1/2}.$
> Now $B^{1/2}AB^{1/2}$ is positive; hence the matrix $AB$, which is similar to it, has nonnegative
> eigenvalues. Now, from (III.20) we obtain
> $\log\lambda^{\downarrow}(A^{1/2}) + \log\lambda^{\uparrow}(B^{1/2}) \prec \log s(A^{1/2}B^{1/2}) \prec \log\lambda^{\downarrow}(A^{1/2}) + \log\lambda^{\downarrow}(B^{1/2}).$   (III.22)
> But $s^2(A^{1/2}B^{1/2}) = \lambda^{\downarrow}(B^{1/2}AB^{1/2}) = \lambda^{\downarrow}(AB)$. So, the majorisations
> (III.21) follow from (III.22).

**Source, verbatim (MA p. 71: the notation for $\prec$ on logarithms, and the singular-value theorem).**
> It is convenient to adopt the following notational shorthand. If $x, y, z$ are $n$-vectors with
> nonnegative coordinates, we will write
>
> $\log x \prec_w \log y$ if $\prod_{j=1}^{k} x_j^{\downarrow} \le \prod_{j=1}^{k} y_j^{\downarrow}$, for $k = 1,\dots,n$;   (III.14)
>
> $\log x \prec \log y$ if $\log x \prec_w \log y$ and $\prod_{j=1}^{n} x_j^{\downarrow} = \prod_{j=1}^{n} y_j^{\downarrow}$;   (III.15)
>
> $\log x - \log z \prec_w \log y$ if $\prod_{j=1}^{k} x_{i_j} \le \prod_{j=1}^{k} y_j \prod_{j=1}^{k} z_{i_j}$,   (III.16)
>
> for all indices $1 \le i_1 < \dots < i_k \le n$. Note that we are allowing the possibility of zero
> coordinates in this notation.
>
> Theorem III.4.5 (Gel'fand-Naimark) Let $A, B$ be any two operators on $\mathcal{H}$. Then the singular
> values of $A, B$ and $AB$ satisfy the majorisation
> $\log s(AB) - \log s(B) \prec \log s(A).$   (III.17)

(Its proof runs to p. 72, ending "This, by definition, is what (III.17) says.")

**Source, verbatim (MA p. 72: the singular-value form, (III.20)).**
> If we temporarily introduce the notation $s^{\downarrow}(A)$ and $s^{\uparrow}(A)$ for the vectors whose
> coordinates are the singular values of $A$ arranged in decreasing order and in increasing order,
> respectively, then the inequalities (III.18) and (III.19) can be combined to yield
> $\log s^{\downarrow}(A) + \log s^{\uparrow}(B) \prec \log s(AB) \prec \log s^{\downarrow}(A) + \log s^{\downarrow}(B)$   (III.20)
> for any two matrices $A, B$.

**Definitions read in MA.**
- **$\prec$ (majorised), p. 28.** Section II.1, "Basic Notions". The definition is in the running text,
  unnumbered.
  > "Let $x = (x_1,\dots,x_n)$ be an element of $\mathbb{R}^n$. Let $x^{\downarrow}$ and $x^{\uparrow}$ be the
  > vectors obtained by rearranging the coordinates of $x$ in the decreasing and the increasing orders,
  > respectively. Thus, if $x^{\downarrow} = (x_1^{\downarrow},\dots,x_n^{\downarrow})$, then
  > $x_1^{\downarrow} \ge \cdots \ge x_n^{\downarrow}$. Similarly, if $x^{\uparrow} = (x_1^{\uparrow},\dots,x_n^{\uparrow})$,
  > then $x_1^{\uparrow} \le \cdots \le x_n^{\uparrow}$. Note that $x_j^{\uparrow} = x_{n-j+1}^{\downarrow}$, $1 \le j \le n$. (II.1)
  >
  > Let $x, y \in \mathbb{R}^n$. We say that $x$ is **majorised** by $y$, in symbols $x \prec y$, if
  > $\sum_{j=1}^{k} x_j^{\downarrow} \le \sum_{j=1}^{k} y_j^{\downarrow}$, $1 \le k \le n$, (II.2)
  > and
  > $\sum_{j=1}^{n} x_j^{\downarrow} = \sum_{j=1}^{n} y_j^{\downarrow}$. (II.3)"
- **$\prec_w$ and $\prec^w$, p. 30.**
  > "We say that $x$ is (weakly) **submajorised** by $y$, in symbols $x \prec_w y$, if condition (II.2) is
  > fulfilled. Note that in the absence of (II.3), the conditions (II.2) and (II.4) are not equivalent. We
  > say that $x$ is (weakly) **supermajorised** by $y$, in symbols $x \prec^w y$, if condition (II.4) is
  > fulfilled."

  Condition (II.4), on p. 29, is $\sum_{j=1}^{k} x_j^{\uparrow} \ge \sum_{j=1}^{k} y_j^{\uparrow}$ for
  $1 \le k \le n$. Together with (II.5), equal totals of the increasing arrangements, it is equivalent
  to $x \prec y$.
- **$\lambda^{\downarrow}$ and $\lambda^{\uparrow}$, pp. 57-58** (Section III.1). For Hermitian $A$ with
  $Au_j = \alpha_j u_j$ and $\alpha_1 \ge \cdots \ge \alpha_n$:
  > "When the dependence of the eigenvalues on the operator is to be emphasized, we will write
  > $\lambda^{\downarrow}(A)$ for the vector with components $\lambda_1^{\downarrow}(A),\dots,\lambda_n^{\downarrow}(A)$,
  > where $\lambda_j^{\downarrow}(A)$ are arranged in decreasing order; i.e., $\lambda_j^{\downarrow}(A) = \alpha_j$.
  > Similarly, $\lambda^{\uparrow}(A)$ will denote the vector with components $\lambda_j^{\uparrow}(A)$ where
  > $\lambda_j^{\uparrow}(A) = \alpha_{n-j+1}$, $1 \le j \le n$."
- **$\lambda(\cdot)$, p. 35 (Exercise II.1.12) and p. 50 (Problem II.5.4).** On p. 35: "$\lambda(A)$ the
  vector whose coordinates are the eigenvalues of $A$ specified in any order" (for Hermitian $A$). On
  p. 50: "Let $\lambda(A)$ and $s(A)$ denote the $n$-vectors whose coordinates are the eigenvalues and the
  singular values of $A$, respectively."
- **"positive", p. 4** (Section I.2).
  > "A Hermitian operator $A$ is said to be **positive** or **positive semidefinite** if
  > $\langle x, Ax\rangle \ge 0$ for all $x \in \mathcal{H}$. ... If $\langle x, Ax\rangle > 0$ for all
  > nonzero $x$, we will say $A$ is **positive definite**, or **strictly positive**."

  $\mathcal{H}$ is a complex Hilbert space.

**Source, verbatim (PDM, p. 228).** This is the 2026-10-05 reading, unchanged.
> 6.5.3 Exercise
>
> An inequality due to Gel'fand, Naimark, and Lidskii gives relations between eigenvalues of two
> positive matrices $A$ and $B$ and their product $AB$. This says
>
> $\log\lambda^{\downarrow}(A) + \log\lambda^{\uparrow}(B) \prec \log\lambda(AB) \prec \log\lambda^{\downarrow}(A) + \log\lambda^{\downarrow}(B).$   (6.47)
>
> See MA p. 73. [...]

The PDM definitions read on 2026-10-05 are unchanged. PDM itself does not define $\prec$; it defers to
MA, Chapters II and IV.

**Notes for the ledger.**
1. **The page states the equal totals.** (III.21) uses $\prec$, not $\prec_w$. By (III.15), it contains
   the partial-product inequalities (III.14), which are the partial sums of the logarithms. It also
   contains $\log\det(AB) = \log\det A + \log\det B$, in the positive definite case. The weak form A9
   was admitted in is therefore a strict consequence of the page. The full form with equal totals is
   available too, without a second source.
2. **The weak form is exactly the right half of the page.** For positive definite $A, B$ and
   $k = 1,\dots,d$:
   $\sum_{i \le k}\log\lambda_i^{\downarrow}(AB) \le \sum_{i \le k}\big(\log\lambda_i^{\downarrow}(A) + \log\lambda_i^{\downarrow}(B)\big)$.
   - The right-hand vector is already in decreasing order, so it is its own $y^{\downarrow}$ in (II.2).
   - $\log\lambda(AB)$ enters through $x^{\downarrow}$.
3. **Hypotheses.**
   - MA's $A, B$ are complex Hermitian positive semidefinite matrices of any size.
   - The conclusion concerns the eigenvalues of $AB$, not its singular values.
   - Zero coordinates are allowed, so a logarithm may be $-\infty$. For positive definite $A, B$ every term
     is finite.
   - Real symmetric positive definite matrices are a special case, so the ledger's narrowing stands.
4. **Attribution.** MA names Corollary III.4.6 "(Lidskii)". It is derived from the Gel'fand-Naimark
   singular-value theorem III.4.5 via (III.20). MA's $\prec$ is the unnumbered definition on p. 28,
   (II.2)-(II.3).
5. **Only the right half of (III.21) is used.**

---

## A10 -- Schoenberg's radial theorem (Bernstein function iff radial extension is continuous negative definite in every dimension), with the representation of a Bernstein function

Librarian pass, 2026-10-07. Anchors opened from the held copy of schilling2012bernstein (Schilling, Song,
Vondracek, *Bernstein Functions: Theory and Applications*, 2nd ed., de Gruyter Studies in Mathematics 37,
2012; printed = pdf - 14 in the body) and rendered as page images
(`library page schilling2012bernstein --printed N --format image`): printed pp. 2, 3, 15, 21, 22, 27, 35,
36, 45, 46, 55, 57, 58, 59, 121, 212, 213, 214 and the Index of notation (pdf p. 13, front matter, rendered
with `--offset 0`). Transcribed from the images, independently of Paper V's ledger A23 and of the cone
module's reading; the comparison with A23 is in the notes at the end. Formulas are in LaTeX-ish plain text.
No glyph was uncertain.

**Cite:** schilling2012bernstein --
- Thm. 13.14 (Schoenberg; Bochner), printed p. 212 (proof pp. 212-214, Lemma 13.15 on p. 214); Example
  13.13, p. 212 (the sufficiency direction);
- Def. 4.3 and Prop. 4.4 (Schoenberg), printed p. 36 (Def. 4.1 and the setting, p. 35); (4.7)-(4.8), pp.
  45-46; Thm. 4.14 (Bochner) and Thm. 4.15 (Levy; Khintchine), printed p. 46;
- Def. 3.1, Thm. 3.2, printed p. 21 (proof p. 22) and Remark 3.3, p. 22; Thm. 3.7 (i)<=>(iii), printed p. 27;
- Def. 1.3 (completely monotone), printed p. 2; Thm. 1.4 (Bernstein), printed p. 3;
- Def. 5.14 and Prop. 5.17 (self-decomposable subordinators), printed pp. 55 and 57-59; Remark 5.18, p. 59.

---

### 1. Thm. 13.14, the radial theorem (printed p. 212)

**Source, verbatim (p. 212).** Preceded by Example 13.13 (below) and by "There is an interesting converse to
the last remark of Example 13.13. This is due to Schoenberg [325]; we follow Bochner's presentation [63, p. 99]."

> **Theorem 13.14** (Schoenberg; Bochner). *A function $f : (0,\infty) \to [0,\infty)$ is a Bernstein
> function if, and only if, for all $d \in \mathbb{N}$ the function $\xi \mapsto f(|\xi|^2)$,
> $\xi \in \mathbb{R}^d$, is continuous and negative definite.*

**Source, verbatim (p. 212, the proof opens).**
> *Proof.* Since $\xi \mapsto |\xi|^2$ is continuous and negative definite in all dimensions, sufficiency
> follows from Example 13.13.
>
> Conversely, fix $d \in \mathbb{N}$ and assume that $f(|\xi|^2)$ is continuous and negative definite. By
> Proposition 4.4 this is equivalent to saying that
> $F_t(|\xi|^2) := \exp(-t f(|\xi|^2))$
> is continuous and positive definite for all $t > 0$, and by Bochner's theorem, Theorem 4.14, we know that
> $F_t(|\xi|^2)$ is for fixed $t > 0$ a Fourier transform. This means that
> $F_t(|\xi|^2) = \int_{\mathbb{R}^d} e^{i\xi\cdot y}\, \nu_d^t(dy), \quad t > 0,$   (13.21)
> with a measure $\nu_d^t$ on $\mathbb{R}^d$ which is invariant under rotations and whose total mass
> $\nu_d^t(\mathbb{R}^d) = F_t(0) = \exp(-t f(0))$ does not depend on the dimension $d$.

**Source (p. 213, the proof continues; summary of the route, formulas as printed).** Radialisation of (13.21),
with $G_t(\xi) := F_t(|\xi|^2)$, gives $F_t(|\xi|^2) = \int_{\mathbb{R}^d} H_{\frac12(d-2)}(|\xi|\cdot|y|)\,\nu_d^t(dy)$,
where $H_\kappa(x) = c_\kappa J_\kappa(x)\,x^{-\kappa}$ (13.22) is a normalised Bessel function with
$H_\kappa(0) = 1$. With $\kappa = \kappa(d) = (d-2)/2$ and $\mu_d^t$ the image of $\nu_d^t$ under
$\Phi_d : y \mapsto |y|^2/(4\kappa)$: $\int H_{\frac12(d-2)}(|\xi|\cdot|y|)\,\nu_d^t(dy) = \int_{[0,\infty)} H_\kappa(2\sqrt{\kappa}\,|\xi|\sqrt{r})\,\mu_d^t(dr)$
and "$\mu_d^t[0,\infty) = \nu_d^t(\mathbb{R}^d) = F_t(0)$ is independent of $d$. This shows that for fixed
$t > 0$ the measures $(\mu_d^t)_{d\in\mathbb{N}}$ are vaguely bounded and by Theorem A.5 vaguely compact."
A subsequence $d_k$ gives weak convergence to a measure $\mu^t$ with $\mu^t[0,\infty) = F_t(0)$ (Theorem A.4).

**Source, verbatim (p. 214, the conclusion of the proof).**
> From Lemma 13.15 below we see that the integrand of the second integral converges uniformly to 0 as
> $d \to \infty$, hence $\kappa \to \infty$, while $\mu_d^t(0,\infty)$ is independent of $d$. Since
> $\mu_d^t$ converges weakly to $\mu^t$ we get
> $\lim_{d\to\infty} \int_{[0,\infty)} H_\kappa(2\sqrt{\kappa}\,|\xi|\sqrt{r})\,\mu_d^t(dr) = \int_{[0,\infty)} e^{-|\xi|^2 r}\,\mu^t(dr)$
> which shows that $F_t(\lambda) = \int_{(0,\infty)} e^{-\lambda r}\,\mu^t(dr)$, i.e. $F_t(\lambda)$ is completely
> monotone for all $t > 0$. Since by our construction $F_t(\lambda) = e^{-t f(\lambda)}$, we can use
> Theorem 3.7 to conclude that $f$ is a Bernstein function.

(Lemma 13.15, p. 214, the Bessel estimates: (i) $|H_\kappa(2\sqrt{2\kappa}\,r)| \le C/r$ for $\kappa > 1$,
$r > 0$; (ii), (iii) local-uniform and uniform convergence $H_\kappa(2\sqrt{\kappa}\,r) \to e^{-r^2}$ as $\kappa \to \infty$.)

**Source, verbatim (p. 212, Example 13.13: the sufficiency direction).**
> **Example 13.13.** A stochastic process $(X_t)_{t\ge0}$ with values in $\mathbb{R}^d$ is called a *Levy
> process* if it has independent and stationary increments and if almost all sample paths
> $t \mapsto X_t(\omega)$ are right-continuous and have left limits. It is well known that the transition
> function of a Levy process is characterized by its Fourier transform which is of the form
> $\mathbb{E}^0 e^{i\xi X_t} = e^{-t\psi(\xi)}, \quad \xi \in \mathbb{R}^d.$
> The characteristic exponent $\psi : \mathbb{R}^d \to \mathbb{C}$ is continuous and *negative definite* in the
> sense of Schoenberg, cf. Chapter 4, in particular (4.8). Every continuous and negative definite function
> is uniquely determined by its *Levy-Khintchine formula*, see (4.9) in Theorem 4.15
>
> Denote by $\widehat{S} = (\widehat{S}_t)_{t\ge0}$ and $(\mu_t)_{t\ge0}$ the (killed) subordinator and the
> convolution semigroup given by the Bernstein function $f$. Because of independence, we see
> $\mathbb{E}e^{i\xi X_t^f} = \int_{[0,\infty)} \mathbb{E}e^{i\xi X_s}\,\mu_t(ds) = \int_{[0,\infty)} e^{-s\psi(\xi)}\,\mu_t(ds) = e^{-t f(\psi(\xi))}.$
>
> A calculation similar to the one in the proof of Theorem 5.27 shows that $f \circ \psi$ is again given by
> a Levy-Khintchine formula. This means that $f \circ \psi$ is a continuous and negative definite function
> and that a subordinate Levy process is still a Levy process.

(Compare p. 15, Comments to Chapter 1, verbatim: "The basic result is due to Schoenberg [325]: a function $f$
on $[0,\infty)$ with $f(0) = f(0+)$ is completely monotone if, and only if, $\xi \mapsto f(|\xi|^2)$,
$\xi \in \mathbb{R}^d$, is positive definite for all dimensions $d \ge 0$, cf. Theorem 13.14." Printed as
"$d \ge 0$", although the book's $\mathbb{N}$ starts at 1.)

### 2. Negative definite and positive definite, as the book defines them

**Source, verbatim (p. 35, Chapter 4 opening; the setting of Def. 4.1 and Def. 4.3).**
> An *Abelian semigroup with involution* $(S, +, *)$ is a nonempty set equipped with a *commutative and
> associative addition* $+$, a *zero element* 0 and a mapping $* : S \to S$ called *involution*, satisfying
> (a) $(s+t)^* = s^* + t^*$ for all $s, t \in S$;
> (b) $(s^*)^* = s$ for all $s \in S$.
>
> We are mainly interested in the semigroups $([0,\infty), +)$ and $(\mathbb{R}^d, +)$ where "+" is the usual
> addition; the respective involutions are the identity mapping $s \mapsto s$ in $[0,\infty)$ and the
> reflection at the origin $\xi \mapsto -\xi$ in $\mathbb{R}^d$.
>
> **Definition 4.1.** A function $f : S \to \mathbb{C}$ is *positive definite* if
> $\sum_{j,k=1}^{n} f(s_j + s_k^*)\, c_j \bar{c}_k \ge 0$   (4.1)
> holds for all $n \in \mathbb{N}$, all $s_1,\dots,s_n \in S$ and all $c_1,\dots,c_n \in \mathbb{C}$.

**Source, verbatim (p. 36, Def. 4.3 and Prop. 4.4).**
> **Definition 4.3.** A function $f : S \to \mathbb{C}$ is *negative definite* if it is hermitian, i.e.
> $f(s^*) = \overline{f(s)}$, and if
> $\sum_{j,k=1}^{n} \big( f(s_j) + \overline{f(s_k)} - f(s_j + s_k^*) \big)\, c_j \bar{c}_k \ge 0$   (4.2)
> holds for all $n \in \mathbb{N}$, all $s_1,\dots,s_n \in S$ and all $c_1,\dots,c_n \in \mathbb{C}$.
>
> Note that "$f$ is negative definite" does *not* mean that "$-f$ is positive definite". The connection
> between those two concepts is given in the following proposition.
>
> **Proposition 4.4** (Schoenberg). *For a function $f : S \to \mathbb{C}$ the following assertions are
> equivalent.*
> *(i) $f$ is negative definite.*
> *(ii) $f(0) \ge 0$, $f(s^*) = \overline{f(s)}$ and $-f$ is conditionally positive definite, i.e. for all
> $n \in \mathbb{N}$, all $s_1,\dots,s_n \in S$ and all $c_1,\dots,c_n \in \mathbb{C}$ satisfying
> $\sum_{j=1}^{n} c_j = 0$ one has*
> $\sum_{j,k=1}^{n} f(s_j + s_k^*)\, c_j \bar{c}_k \le 0.$   (4.3)
> *(iii) $f(0) \ge 0$ and $s \mapsto e^{-tf(s)}$ is positive definite for all $t > 0$.*

**The book gives no separate definition of "continuous negative definite".** The phrase is the conjunction of
Def. 4.3 with ordinary continuity of $f$ on $S$ ($\mathbb{R}^d$ with its usual topology); the book uses it in
that sense in Thm. 4.14/4.15 (p. 46: "continuous and positive definite", "continuous and negative definite")
and in Thm. 13.14. Continuity enters Def. 4.3 nowhere.

**Source, verbatim (p. 45 end / p. 46 start, the $\mathbb{R}^d$ instance of Def. 4.1 and 4.3).**
> On $\mathbb{R}^d$ the involution is given by $\xi^* = -\xi$, $\xi \in \mathbb{R}^d$. This means that $f$ is
> positive definite (in the sense of Bochner) if
> $\sum_{j,k=1}^{n} f(\xi_j - \xi_k)\, c_j \bar{c}_k \ge 0,$   (4.7)
> and negative definite (in the sense of Schoenberg) if
> $\sum_{j,k=1}^{n} \big( f(\xi_j) + \overline{f(\xi_k)} - f(\xi_j - \xi_k) \big)\, c_j \bar{c}_k \ge 0$   (4.8)
> hold for all $n \in \mathbb{N}$, $\xi_1,\dots,\xi_n \in \mathbb{R}^d$ and $c_1,\dots,c_n \in \mathbb{C}$.

(The sentence straddles pp. 45/46: (4.7) is on p. 45, "and negative definite (in the sense of Schoenberg) if"
and (4.8) on p. 46. Hermitian symmetry, $f(-\xi) = \overline{f(\xi)}$, is part of Def. 4.3 and is not
repeated in the $\mathbb{R}^d$ paragraph.)

**Source, verbatim (p. 46, Bochner's theorem and the Levy-Khintchine theorem).**
> **Theorem 4.14** (Bochner). *A function $\phi : \mathbb{R}^d \to \mathbb{C}$ is continuous and positive
> definite if, and only if, it is the Fourier transform of a finite measure $\mu$ on $\mathbb{R}^d$,*
> $\phi(\xi) = \widehat{\mu}(\xi) = \int_{\mathbb{R}^d} e^{ix\xi}\,\mu(dx), \quad \xi \in \mathbb{R}^d.$
> *The measure $\mu$ is uniquely determined by $\phi$, and vice versa.*
>
> **Theorem 4.15** (Levy; Khintchine). *A function $\psi : \mathbb{R}^d \to \mathbb{C}$ is continuous and
> negative definite if, and only if, there exist a number $\alpha \ge 0$, a vector $\beta \in \mathbb{R}^d$, a
> symmetric and positive semi-definite matrix $Q \in \mathbb{R}^{d\times d}$ and a measure $\nu$ on
> $\mathbb{R}^d \setminus \{0\}$ satisfying $\int_{y\neq0} (1 \wedge |y|^2)\,\nu(dy) < \infty$ such that*
> $\psi(\xi) = \alpha + i\beta\cdot\xi + \tfrac12\,\xi\cdot Q\xi + \int_{y\neq0}\Big(1 - e^{i\xi\cdot y} + \frac{i\xi\cdot y}{1+|y|^2}\Big)\nu(dy).$   (4.9)
> *The quadruple $(\alpha, \beta, Q, \nu)$ is uniquely determined by $\psi$, and vice versa.*

### 3. Bernstein function, Def. 3.1 and Thm. 3.2 (printed p. 21)

**Source, verbatim (p. 21; the first page of Chapter 3).**
> **Definition 3.1.** A function $f : (0,\infty) \to \mathbb{R}$ is a *Bernstein function* if $f$ is of class
> $C^\infty$, $f(\lambda) \ge 0$ for all $\lambda > 0$ and
> $(-1)^{n-1} f^{(n)}(\lambda) \ge 0 \quad$ for all $n \in \mathbb{N}$ and $\lambda > 0.$   (3.1)
> The set of all Bernstein functions will be denoted by $\mathcal{BF}$.
>
> [...] The key to the next theorem is the observation that a non-negative $C^\infty$-function
> $f : (0,\infty) \to \mathbb{R}$ is a Bernstein function if, and only if, $f^\prime$ is a completely monotone
> function.
>
> **Theorem 3.2.** *A function $f : (0,\infty) \to \mathbb{R}$ is a Bernstein function if, and only if, it
> admits the representation*
> $f(\lambda) = a + b\lambda + \int_{(0,\infty)} (1 - e^{-\lambda t})\,\mu(dt),$   (3.2)
> *where $a, b \ge 0$ and $\mu$ is a measure on $(0,\infty)$ satisfying $\int_{(0,\infty)} (1 \wedge t)\,\mu(dt) < \infty$.*
> *In particular, the triplet $(a, b, \mu)$ determines $f$ uniquely and vice versa.*

**Source, verbatim (p. 22, the end of the proof of Thm. 3.2, and Remark 3.3(i)).** The proof, which starts at
the foot of p. 21 ("Assume that $f$ is a Bernstein function. Then $f^\prime$ is completely monotone. According
to Theorem 1.4, there exists a measure $\nu$ on $[0,\infty)$ such that for all $\lambda > 0$
$f^\prime(\lambda) = \int_{[0,\infty)} e^{-\lambda t}\,\nu(dt)$"), continues on p. 22:
> Let $b := \nu\{0\}$. Then [...] Write $a := f(0+)$ and define $\mu(dt) := t^{-1}\nu|_{(0,\infty)}(dt)$. Then the
> calculation from above shows that (3.2) is true. That $a, b \ge 0$ is obvious, and from the elementary
> (convexity) estimate $(1 - e^{-1})(1 \wedge t) \le 1 - e^{-t}$, $t \ge 0$, we infer
> $\int_{(0,\infty)} (1 \wedge t)\,\mu(dt) \le \frac{e}{e-1}\int_{(0,\infty)} (1 - e^{-t})\,\mu(dt) = \frac{e}{e-1} f(1) < \infty.$
> [...] Because $f(0+) = a$ and because of the uniqueness assertion of Theorem 1.4 it is clear that
> $(a, b, \mu)$ and $f \in \mathcal{BF}$ are in one-to-one correspondence.
>
> **Remark 3.3.** (i) The representing measure $\mu$ and the characteristic triplet $(a, b, \mu)$ from (3.2)
> are often called the *Levy measure* and the *Levy triplet* of the Bernstein function $f$. The formula (3.2)
> is called the *Levy-Khintchine representation* of $f$.

### 4. Characterisation by complete monotonicity of $e^{-uf}$, Thm. 3.7 (printed p. 27)

**Source, verbatim (p. 27).** Introduced by "The following structural characterization comes from Bochner
[63, pp. 83-84] where Bernstein functions are called completely monotone mappings."
> **Theorem 3.7.** *Let $f$ be a positive function on $(0,\infty)$. Then the following assertions are
> equivalent.*
> *(i) $f \in \mathcal{BF}$.*
> *(ii) $g \circ f \in \mathcal{CM}$ for every $g \in \mathcal{CM}$.*
> *(iii) $e^{-uf} \in \mathcal{CM}$ for every $u > 0$.*

(Proof pp. 27-28: the Faa di Bruno formula (3.9) for the $n$-th derivative of $g\circ f$ gives (i)=>(ii);
(ii)=>(iii) because $\lambda \mapsto e^{-\lambda u}$ is completely monotone; (iii)=>(i) by expanding
$e^{-uf} = \sum_j (-1)^j u^j [f]^j/j!$ and differentiating termwise.)
In the book "positive" is *always in the sense $> 0$* (Index of notation, pdf p. 13: "positive: always in
the sense $> 0$; negative: always in the sense $< 0$"). So the hypothesis of Thm. 3.7 literally reads
$f > 0$, while Thm. 13.14 has codomain $[0,\infty)$ and its proof (p. 214) applies Thm. 3.7 to $f \ge 0$ with
$F_t = e^{-tf}$. The literal gap ($f \equiv 0$ is excluded by "positive" but allowed by Def. 3.1) is the
book's and harmless: $f\equiv0$ is in $\mathcal{BF}$ with triplet $(0,0,0)$ and $e^{-uf} \equiv 1 \in \mathcal{CM}$.

**Definition 1.3 and Thm. 1.4 (the terms Thm. 3.7 uses).**
> **Definition 1.3** (p. 2). A function $f : (0,\infty) \to \mathbb{R}$ is a *completely monotone function* if
> $f$ is of class $C^\infty$ and
> $(-1)^n f^{(n)}(\lambda) \ge 0 \quad$ for all $n \in \mathbb{N}\cup\{0\}$ and $\lambda > 0.$   (1.4)
> The family of all completely monotone functions will be denoted by $\mathcal{CM}$.
>
> **Theorem 1.4** (Bernstein) (p. 3). *Let $f : (0,\infty) \to \mathbb{R}$ be a completely monotone function.
> Then it is the Laplace transform of a unique measure $\mu$ on $[0,\infty)$, i.e. for all $\lambda > 0$,*
> $f(\lambda) = \mathcal{L}(\mu;\lambda) = \int_{[0,\infty)} e^{-\lambda t}\,\mu(dt).$
> *Conversely, whenever $\mathcal{L}(\mu;\lambda) < \infty$ for every $\lambda > 0$, $\lambda \mapsto \mathcal{L}(\mu;\lambda)$ is a completely monotone function.*

### 5. Self-decomposable subordinators (printed pp. 55, 57-59): the book has it

The theorem exists: **Prop. 5.17, printed p. 57** (proof pp. 57-59), with **Remark 5.18, p. 59**. The
definition of self-decomposable is **Def. 5.14, p. 55**.

**Source, verbatim (p. 55).**
> **Definition 5.14.** A completely monotone function $g \in \mathcal{CM}$ with $g(0+) \le 1$ is said to be
> *self-decomposable*, if
> $\lambda \mapsto \dfrac{g(\lambda)}{g(c\lambda)} = g_c(\lambda)$ is completely monotone for all $c \in (0,1).$   (5.8)
>
> We will see in Proposition 5.17 that the Laplace exponent $f$ of a $\pi \in \mathsf{SD}$, i.e.
> $\mathcal{L}\pi = e^{-f}$, is a Bernstein function with a Levy triplet of the form $(a, b, m(t)\,dt)$ such
> that $t \mapsto t\,m(t)$ is non-increasing.

Context on the same page: $\mathsf{SD}$ is "the set of all self-decomposable distributions on $[0,\infty)$"
(Index of notation: SD, 55; $\mathsf{SD}_\infty$, 59), the $\pi$ being sub-probability measures on $[0,\infty)$
with Laplace transform $\mathcal{L}\pi$; and "{stable laws} $\subset$ SD $\subset$ ID."

**Source, verbatim (p. 57).**
> **Proposition 5.17.** *Let $f \in \mathcal{BF}$ satisfy $\mathcal{L}\pi = e^{-f}$ and let $\mu$ be the Levy
> measure of $f$. Then the following assertions are equivalent.*
> *(i) $\mu$ has a density $m(t)$ such that $t \mapsto t\cdot m(t)$ is non-increasing;*
> *(ii) $\pi \in \mathsf{SD}$.*

**Source, verbatim (pp. 58-59, the proof).** For (ii)=>(i), with $g = \mathcal{L}\pi$ and
$g_c(\lambda) = g(\lambda)/g(c\lambda) = \exp(-(f(\lambda) - f(c\lambda)))$, the proof (p. 57-58) shows $g_c$ is
logarithmically completely monotone, defines $f_c(\lambda) := f(\lambda) - f(c\lambda) \in \mathcal{BF}$ (by
Theorem 5.11), derives $\mu_c = \mu - \mu^{(c)}$ with $\mu^{(c)}(\cdot) := \mu(c^{-1}\,\cdot)$ (5.11)-(5.12), so
$\mu(B) \ge \mu(c^{-1}B)$ for Borel $B \subset (0,\infty)$; then with $M(t) = \mu(t,\infty)$ and
$h(s) := M(e^{-s})$ (non-negative, non-decreasing, convex) it writes $h(s) = \int_{-\infty}^{s}\ell(u)\,du$ with
$\ell$ non-negative and non-decreasing. The proof of (ii)=>(i) closes (p. 59):
> Define a function $k : (0,\infty) \to \mathbb{R}$ by $k(v) := \ell(e^{-v})$. Then $k$ is non-negative and
> non-increasing. For $t > 0$ a change of variables shows
> $M(t) = h(-\log t) = \int_{-\infty}^{-\log t}\ell(u)\,du = \int_t^\infty \frac{\ell(e^{-v})}{v}\,dv = \int_t^\infty \frac{k(v)}{v}\,dv,$
> and the proof is finished by defining $m(t) := k(t)/t$.
>
> (i)=>(ii) To prove the converse, let $c \in (0,1)$ and define $f_c(\lambda) := f(\lambda) - f(c\lambda)$.
> Then
> $f_c(\lambda) = \Big(a + b\lambda + \int_0^\infty (1-e^{-\lambda t})\,m(t)\,dt\Big) - \Big(a + bc\lambda + \int_0^\infty (1-e^{-c\lambda t})\,m(t)\,dt\Big)$
> $= b(1-c)\lambda + \int_0^\infty (1-e^{-\lambda t})\big(m(t) - c^{-1}m(t/c)\big)\,dt.$
> Since $t \mapsto t\cdot m(t)$ is non-increasing, $n_c(t) := m(t) - c^{-1}m(t/c) \ge 0$ is non-negative for
> all $t \ge 0$. Hence, $f_c \in \mathcal{BF}$. Let $g := \mathcal{L}\pi = e^{-f}$. Then
> $g_c(\lambda) = \dfrac{g(\lambda)}{g(c\lambda)} = \dfrac{e^{-f(\lambda)}}{e^{-f(c\lambda)}} = e^{-f_c(\lambda)},$
> proving that $g$ is completely monotone. Since $g(0+) \le 1$, we see that $g$ is self-decomposable, i.e.
> $\pi \in \mathsf{SD}$.
>
> **Remark 5.18.** In the proof one can choose $m(t)$ so that $t\cdot m(t)$ is right-continuous. Hence,
> Proposition 5.17 can be stated as $\pi \in \mathsf{SD}$ if, and only if, $t\cdot m(t)$ is 1-monotone.
> Alternatively, $\pi \in \mathsf{SD}$ if, and only if, $t\cdot m(t) = n(\log t)$ where $n$ is 1-monotone on
> $\mathbb{R}$.

So, in the book's terms: with $k(u) := u\,m(u)$, the Levy measure of a self-decomposable subordinator is
$\mu(du) = (k(u)/u)\,du$ with $k \ge 0$ non-increasing (the proof builds exactly this $k$); conversely every such
$\mu$ that is the Levy measure of a Bernstein function gives a self-decomposable $\pi$. The statement is for
$f \in \mathcal{BF}$ with $e^{-f} = \mathcal{L}\pi$, $\pi$ a sub-probability measure on $[0,\infty)$, so
$a = f(0+) \ge 0$ (killing) and $b \ge 0$ (drift) are unrestricted by self-decomposability. Prop. 5.20 (p. 60)
is the $p$-times / completely self-decomposable analogue ($t\,m(t) = n(\log t)$ with $n$ $p$-monotone, resp.
completely monotone). The integrability condition $\int(1\wedge t)\mu(dt) < \infty$ on $\mu = (k(t)/t)\,dt$
reads $\int_0^1 k(t)\,dt + \int_1^\infty k(t)\,t^{-1}\,dt < \infty$; it is *not* printed in Prop. 5.17, it comes
from $\mu$ being the Levy measure of a Bernstein function (Thm. 3.2). Related, not transcribed: Prop. 9.11
and p. 123 (Ch. 9) say GGC (Thorin-Bernstein) distributions are self-decomposable; the Comments (p. 67) credit
Prop. 5.17 to Levy [243, Sect. VII.55], adapted from Sato [314, p. 95].

### 6. Answers to the coordinator's questions

1. **$f$ at 0 in Thm. 13.14.** The theorem is stated for $f : (0,\infty) \to [0,\infty)$, a function on the open
   half-line. Its conclusion concerns $\xi \mapsto f(|\xi|^2)$ on $\mathbb{R}^d$, which includes $\xi = 0$, so a
   value $f(0)$ is needed. **The book does not say how it is fixed in Thm. 13.14 or in its proof.** The proof
   writes $F_t(0) = \exp(-t f(0))$ and $\nu_d^t(\mathbb{R}^d) = F_t(0)$ (p. 212) and $\mu^t[0,\infty) = F_t(0)$
   (p. 213) without comment. What the book does say all points one way:
   - Thm. 3.2 and its proof give $a = f(0+)$ (p. 22);
   - the Comments on p. 15 require, for the CM analogue, "$f$ on $[0,\infty)$ with $f(0) = f(0+)$";
   - for complete Bernstein functions it fixes "$f(0) := f(0+) \in [0,\infty)$" (p. 211, before Thm. 13.11);
   - the hypothesis "continuous" in Thm. 13.14 forces $f(0) = f(0+)$ whenever $f(0+)$ exists (it does:
     a Bernstein function is non-negative and non-decreasing);
   - the Index of notation (pdf p. 13) lists the subscript 0 as "$f(0) = 0$, resp. $f(0+) = 0$", one notion.
   So $f(0) := f(0+)$ is the book's convention in effect, but it is **not stated at Thm. 13.14**. A statement
   quoting the theorem should say "with $f(0) := f(0+)$" as its own reading. In Example 13.13 (sufficiency)
   the Bernstein function belongs to a "(killed) subordinator", so $f(0+) = a$ is the killing rate. The theorem
   asks no continuity of $f$ on $(0,\infty)$ itself (Bernstein functions are $C^\infty$ there).
2. **Does the book's $\mathbb{N}$ include 0?** No. Index of notation (pdf p. 13, printed as "Index of notation",
   front matter): "$\mathbb{N}$: natural numbers: 1, 2, 3, ...". The book writes $\mathbb{N}\cup\{0\}$ when it
   wants 0 (Def. 1.3, (1.4), p. 2). Hence "for all $d \in \mathbb{N}$" in Thm. 13.14 means
   $d = 1, 2, 3, \dots$; in Def. 3.1 "$n \in \mathbb{N}$" in (3.1) means $n \ge 1$, with $n = 0$ carried by
   "$f(\lambda) \ge 0$"; in Def. 4.1 and 4.3 "$n \in \mathbb{N}$" is the number of points. The one place that
   reads "$d \ge 0$" is the Comments on p. 15 (the CM analogue), where it can only be a slip ($\mathbb{R}^0$ is a
   point). The index also fixes "positive: always in the sense $> 0$".
3. **Thm. 3.2's exact conditions.** $f : (0,\infty) \to \mathbb{R}$ (the non-negativity is part of Def. 3.1,
   not of the theorem's domain); representation (3.2); **$a, b \ge 0$**; **$\mu$ "a measure on $(0,\infty)$"**
   (no finiteness or absolute continuity, no mass at 0, which is carried by $a$ and $b$); the integrability
   condition **$\int_{(0,\infty)} (1 \wedge t)\,\mu(dt) < \infty$**, which is
   $\int_{(0,1]} t\,\mu(dt) + \mu(1,\infty) < \infty$. **Uniqueness is part of the printed statement**, as its
   last sentence: "In particular, the triplet $(a, b, \mu)$ determines $f$ uniquely and vice versa." It is
   proved at the end of the proof on p. 22 ($a = f(0+)$; $\nu = b\delta_0 + t\mu(dt)$ is the unique measure of
   Thm. 1.4 representing $f^\prime$). The theorem does not state $a = f(0+)$ or $b = \lim f(\lambda)/\lambda$;
   $a = f(0+)$ is in the proof.
4. **"Continuous negative definite".** Def. 4.3 (p. 36) plus continuity; see section 2. The $\mathbb{R}^d$ form
   is (4.8), p. 46. The book states the equivalent characterisation (Prop. 4.4(iii)): negative definite iff
   $f(0) \ge 0$ and $e^{-tf}$ positive definite for all $t > 0$ (hermitian symmetry is a separate clause in (ii) and
   in Def. 4.3, and is not repeated in (iii) as printed).

---

**Notes for the ledger.**
1. **Hypotheses and domain.** Thm. 13.14: $f : (0,\infty) \to [0,\infty)$; for every $d \in \{1,2,3,\dots\}$ the
   function $\xi \mapsto f(|\xi|^2)$ on $\mathbb{R}^d$ is continuous and negative definite (Def. 4.3, hermitian
   included, plus continuity). The value $f(0)$ is not fixed in the statement; $f(0) := f(0+)$ is the book's
   convention in effect (p. 15, p. 211, the proof). The theorem is a two-sided "if and only if". The
   necessity direction ("Bernstein from the radial extensions") uses all $d$ through a limit $d \to \infty$
   (pp. 213-214, vague compactness of the $\mu_d^t$ and Lemma 13.15); the book does not assert the conclusion
   from one fixed $d$.
2. **Which direction A10 would spend.** "All radial extensions continuous negative definite => Bernstein" is
   the direction proved on pp. 212-214; it ends with Thm. 3.7 (iii)=>(i). The converse is Example 13.13
   (composition of a Levy exponent with the subordinator's Bernstein function, using Thm. 4.15).
3. **Comparison with Paper V's A23 (cone module, ledger entry read 2026-09-17).** No discrepancy. A23 states
   Thm. 13.14 as printed (domain $(0,\infty) \to [0,\infty)$, "for all $d \in \mathbb{N}$", no continuity of $f$
   itself, vague compactness on p. 213, sufficiency by Example 13.13) and Def. 3.1/Thm. 3.2 as printed on
   p. 21 (including $(-1)^{n-1}f^{(n)} \ge 0$ for $n \ge 1$, $a, b \ge 0$, $\int(1\wedge t)\mu(dt) < \infty$,
   uniqueness of the triplet). What this reading adds, and A23 does not carry: Def. 4.3 itself; the book's
   silence on $f(0)$ at Thm. 13.14 and its conventions elsewhere; $\mathbb{N}$ starts at 1; Thm. 3.7 is
   stated for "positive" $f$ ($> 0$); Prop. 5.17 / Def. 5.14 / Remark 5.18.
4. **Item 3 of the brief (Thm. 3.7).** Present: Thm. 3.7, printed p. 27: (i) $f \in \mathcal{BF}$ iff (iii)
   $e^{-uf} \in \mathcal{CM}$ for every $u > 0$ (with (ii), $g \circ f \in \mathcal{CM}$ for all $g \in \mathcal{CM}$),
   hypothesis "$f$ a positive function on $(0,\infty)$".
5. **Item 4 of the brief (self-decomposable).** Present: Prop. 5.17, printed p. 57 (statement), proof pp. 57-59,
   Remark 5.18 p. 59; Def. 5.14 p. 55. The density is $m(t) = k(t)/t$, $k \ge 0$ non-increasing; the Levy
   measure is of $f \in \mathcal{BF}$ with $e^{-f} = \mathcal{L}\pi$.
6. **Not read.** Prop. 9.11 beyond the p. 121 statement of (i) (its proof, pp. 121-122, and the clause that
   GGC laws are self-decomposable were seen only as text or not at all); the Remark after Thm. 3.2 on p. 23.

---

## A11 -- Karamata's Tauberian theorem at the origin (the Laplace-Stieltjes transform at infinity gives the distribution function at 0+)

Pass of 2026-10-11 (Q-0416), by the mathematician's office through the librarian's CLI. Anchors opened
from the held copy of bingham1987regular (Bingham, Goldie, Teugels, *Regular Variation*, Encyclopedia of
Mathematics and its Applications 27, Cambridge University Press, 1987; body folio = pdf - 24) and rendered
as page images (`library page bingham1987regular --printed N --format image`, with `--offset -24` for
folios below 37, where the label mapping of the held copy returns a front-matter page): printed pp. 6, 18,
25, 26, 37, 38, 39, 40. Each folio was checked on its image. Transcribed from the images. The same pages
were read at the image twice before, independently: by Q-0414's reading
(`records/affine/READING-bingham1987regular.md`, on that item's branch) and by the blind referee of the
derivation (`records/affine/REFEREE-rate-at-the-centre.md`, sections 2.3-2.5 and 3); the three readings
agree on every statement below. Formulas are in LaTeX-ish plain text. No glyph was uncertain; the
inequalities ($\ge$ in "$c \ge 0$, $\rho \ge 0$", $<$ in "$x < 0$" and "$\hat U(s) < \infty$") were settled on
the image.

**Cite:** bingham1987regular --
- Thm. 1.7.1' (Feller (1971), XIII, section 5), printed p. 38;
- the Laplace-Stieltjes transform (1.7.0a) and Thm. 1.7.1 (Karamata Tauberian Theorem), printed p. 37;
- the definition of a slowly varying function, (1.2.1), printed p. 6; the classes $R_\rho$, $R_0$ and
  $R_\rho(0+)$, printed p. 18;
- read and NOT cited: Thm. 1.5.6 (Potter's Theorem), printed p. 25; Prop. 1.5.8, (1.5.8) and Prop. 1.5.9a,
  printed p. 26; Thm. 1.7.2 (Monotone Density Theorem) with its proof and (1.7.5), printed p. 39; Thm. 1.7.2b,
  printed pp. 39-40.

---

### 1. Thm. 1.7.1', the theorem at the origin (printed p. 38)

**Source, verbatim (p. 38).** After the proof of Theorem 1.7.1 and the remarks on it:

> We point out that the same method of proof yields a version of Theorem 1.7.1 with
> $x \to 0+$, $s \to \infty$:
>
> **Theorem 1.7.1'** (Feller (1971), XIII, § 5). *Let $U$ be non-decreasing on $\mathbb{R}$, $U(x) = 0$ for all
> $x < 0$, and such that $\hat U(s) < \infty$ for all large $s$. Let $\ell \in R_0$, $c \ge 0$, $\rho \ge 0$. The
> following are equivalent:*
> $U(x) \sim c x^{\rho} \ell(1/x)/\Gamma(1+\rho) \quad (x \to 0+)$,   (1.7.1')
> $\hat U(s) \sim c s^{-\rho} \ell(s) \quad (s \to \infty)$.   (1.7.2')
>
> Monotonicity of $U$ plays the rôle of a Tauberian condition in Theorem 1.7.1. It may be weakened
> considerably; see Theorems 1.7.6 and 4.8.7 below.

No proof of 1.7.1' is printed beyond the sentence "the same method of proof yields".

### 2. The transform and Thm. 1.7.1 (printed p. 37)

**Source, verbatim (p. 37, "1. LS transforms").**
> If $U : \mathbb{R} \to \mathbb{R}$ has locally bounded variation (see Appendix 6), is right-continuous, and
> vanishes on $(-\infty, 0)$, we define its *Laplace-Stieltjes transform* (*LS transform*)
> $\hat U(s) := \int_{-\infty}^{\infty} e^{-sx}\,dU(x) = \int_{[0,\infty)} e^{-sx}\,dU(x)$,   (1.7.0a)
> where the integral converges absolutely for $s > \sigma$ (where $\sigma$ may be $+\infty$) or more generally
> for all complex $s$ with $\mathrm{Re}\,s > \sigma$ (see e.g. Widder (1941)). The most important case is when
> $U$ is non-decreasing on $\mathbb{R}$, with $U \equiv 0$ on $(-\infty, 0)$. For such $U$, statements about
> $\hat U$ below are to be considered to include the assertion that it is finite for the arguments in
> question.

**Source, verbatim (p. 37, "2. Karamata's Tauberian Theorem").**
> **Theorem 1.7.1** (Karamata Tauberian Theorem). *Let $U$ be a non-decreasing right-continuous function on
> $\mathbb{R}$ with $U(x) = 0$ for all $x < 0$. If $\ell$ varies slowly and $c \ge 0$, $\rho \ge 0$, the following
> are equivalent:*
> $U(x) \sim c x^{\rho} \ell(x)/\Gamma(1+\rho) \quad (x \to \infty)$,   (1.7.1)
> $\hat U(s) \sim c s^{-\rho} \ell(1/s) \quad (s \to 0+)$.   (1.7.2)
>
> When $c = 0$, (1.7.1) is to be interpreted as $U(x) = o(x^{\rho}\ell(x))$; similarly for (1.7.2).

The proof (pp. 37-38) bounds $\hat U(1/x)/\{x^{\rho}\ell(x)\}$ by Potter's Theorem, (iii), and then applies "the
continuity theorem for LS transforms of (not necessarily bounded) positive measures ... (see e.g. Feller
(1971), XIII 1, Theorem 2a)", in both directions. P. 38: "The passage from (1.7.1) to (1.7.2) is *Abelian*
... the converse is *Tauberian*."

### 3. Slowly varying, $R_0$ (printed pp. 6 and 18)

**Source, verbatim (p. 6, "1.2 The Uniform Convergence Theorem").**
> **Definition.** *Let $\ell$ be a positive measurable function, defined on some neighbourhood $[X, \infty)$ of
> infinity, and satisfying*
> $\ell(\lambda x)/\ell(x) \to 1 \quad (x \to \infty) \quad \forall\lambda > 0$;   (1.2.1)
> *then $\ell$ is said to be* **slowly varying** *(in Karamata's sense).*
>
> [...] The neighbourhood $[X, \infty)$ is of little importance; we may (and often shall) suppose $\ell$
> defined on $(0, \infty)$ -- for instance, by taking $\ell(x) \equiv \ell(X)$ on $(0, X)$.

**Source, verbatim (p. 18).**
> $f(\lambda x)/f(x) \to \lambda^{\rho} \quad (x \to \infty) \quad \forall\lambda > 0$.   (1.4.3)
>
> **Definition.** *A measurable [Baire] function $f > 0$ satisfying (1.4.3) is called* **regularly varying**
> *[*Baire regularly varying*] of* **index** *$\rho$; we write $f \in R_\rho$ [$f \in BR_\rho$].* [...]
> *$R_0$ [$BR_0$] is the class of slowly varying [Baire slowly varying] functions considered earlier.*
>
> It is sometimes convenient to transfer attention from infinity to the origin; thus if $f$ is positive,
> $f(\lambda x)/f(x) \to \lambda^{\rho} \quad (x \downarrow 0) \quad \forall\lambda > 0$
> and, for instance, $f$ is measurable, we say $f$ is *regularly varying* (*on the right*) *at the origin*
> with index $\rho$, $f \in R_\rho(0+)$. This is equivalent to saying $f(1/x) \in R_{-\rho}$.

### 4. Read and not cited (printed pp. 25, 26, 39, 40)

**Thm. 1.5.6 (Potter's Theorem), p. 25, verbatim.** *(i) If $\ell$ is slowly varying then for any chosen
constants $A > 1$, $\delta > 0$ there exists $X = X(A, \delta)$ such that*
$\ell(y)/\ell(x) \le A \max\{(y/x)^{\delta}, (y/x)^{-\delta}\}$ $(x \ge X, y \ge X)$. [...] *(iii) If $f$ is regularly
varying of index $\rho$ then for any chosen $A > 1$, $\delta > 0$ there exists $X = X(A, \delta)$ such that*
$f(y)/f(x) \le A \max\{(y/x)^{\rho+\delta}, (y/x)^{\rho-\delta}\}$ $(x \ge X, y \ge X)$.

**Prop. 1.5.9a, p. 26, verbatim.** *Let $\ell$ be slowly varying and choose $X$ so that
$\ell \in L^1_{loc}[X, \infty)$. Then $\int_X^x \ell(t)\,dt/t$ is slowly varying and (1.5.8) holds*, where (1.5.8)
is $\frac{1}{\ell(x)}\int_X^x \ell(t)\,dt/t \to \infty$.

**Thm. 1.7.2 (Monotone Density Theorem), p. 39, verbatim.** *Let $U(x) = \int_0^x u(y)\,dy$. If
$U(x) \sim c x^{\rho}\ell(x)$ $(x \to \infty)$, where $c \in \mathbb{R}$, $\rho \in \mathbb{R}$, $\ell \in R_0$, and if
$u$ is ultimately monotone, then* $u(x) \sim c\rho x^{\rho-1}\ell(x)$ $(x \to \infty)$. (1.7.4) Its proof, for
$u$ eventually non-decreasing and $0 < a < b < \infty$: "$U(bx) - U(ax) = \int_{ax}^{bx} u(y)\,dy$ so, for $x$
large enough, $\frac{(b-a)x\,u(ax)}{x^{\rho}\ell(x)} \le \frac{U(bx) - U(ax)}{x^{\rho}\ell(x)} \le
\frac{(b-a)x\,u(bx)}{x^{\rho}\ell(x)}$. (1.7.5)" The centre member tends to $c(b^{\rho} - a^{\rho})$; "taking
$a := 1$ and letting $b \downarrow 1$" gives the upper limit, "a similar treatment of the right inequality
with $b := 1$ and $a \uparrow 1$" the lower.

**Thm. 1.7.2b, pp. 39-40, verbatim.** *Let $U$ be given on $(0, X]$ by $U(x) = \int_0^x u(y)\,dy$ for some
$u \in L^1[0, X]$. If $U(x) \sim c x^{\rho}\ell(x)$ $(x \downarrow 0)$, where $c \in \mathbb{R}$, $\rho \ge 0$,
$\ell \in R_0(0+)$, and if $u$ is monotone in some right neighbourhood of $0$, then*
$u(x) \sim c\rho x^{\rho-1}\ell(x)$ $(x \downarrow 0)$. (1.7.4b) Introduced on p. 39 by "Variants of the Monotone
Density Theorem involving integrals $\int_x^\infty u(y)\,dy$ as $x \to \infty$, or $\int_0^x u(y)$ as
$x \downarrow 0$, have almost exactly the same proof."

---

**Notes for the ledger.**
1. **Hypotheses and domain of Thm. 1.7.1'.** $U$ non-decreasing on $\mathbb{R}$, $U = 0$ on $(-\infty,0)$,
   $\hat U(s) < \infty$ for all large $s$; $\ell \in R_0$; $c \ge 0$, $\rho \ge 0$. Right-continuity is not in
   the statement of 1.7.1' but is in the definition (1.7.0a) of $\hat U$ and in Thm. 1.7.1. The conclusion is
   an equivalence. For $c = 0$ the relation is read as $o(\cdot)$ (the sentence after Thm. 1.7.1, which
   1.7.1' is "a version" of). The symbol $\sim$ is used without a displayed definition at these pages; for
   $c > 0$ it is the quotient tending to $1$ (the $c = 0$ convention shows that this is the reading meant).
2. **What A11 takes.** The implication (1.7.2') => (1.7.1') for $U(x) = \nu((-\infty, x])$ with $\nu$ a finite
   measure on $[0,\infty)$, $\ell$ positive on $(0,\infty)$ and measurable, $c > 0$, $\rho > 0$. Every change
   from the page is a restriction: a finite measure gives a non-decreasing right-continuous $U$ vanishing on
   $(-\infty,0)$ with $\hat U$ finite for every $s \ge 0$; a function positive and measurable on $(0,\infty)$
   is in $R_0$ once (1.2.1) holds; $c > 0$ and $\rho > 0$ are inside $c \ge 0$, $\rho \ge 0$. Verdict:
   NARROWER-OK, nothing claimed beyond the page.
3. **The primary source of 1.7.1'** is Feller, *An Introduction to Probability Theory and Its Applications*,
   vol. II (1971), XIII, section 5, which the book names. It was not opened for this entry; Q-0414's reading
   note `READING-feller2009introduction.md` covers XV.3, not XIII.5. The entry cites the book that states the
   theorem.
4. **Why the three statements of section 4 are not entries.** Each is used by the refereed derivation and
   replaced in `prop:origin-rate-d` by a proof for the functions at hand: Potter's bound by a dyadic
   iteration (the transform is monotone along rays), Prop. 1.5.9a by a direct argument for the truncated
   integral of the transform, and Thm. 1.7.2b by the inequality (1.7.5) written on spherical shells.
