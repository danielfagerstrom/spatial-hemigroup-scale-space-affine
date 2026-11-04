# Verification of the external review, round 1: the mathematics

**What this is.** Article-kit `PROCESS.md` § 9 asks that every finding of an external review is
verified against the text, the blueprint and the sources before anything changes. This record
verifies the findings of `review-content-iso-review-1-GPT-6.1-Sol-Ultra.md` that call a statement
of the isotropic paper wrong or incomplete in the mathematics. The tree is the tag `iso-review-1`
with the reviews (branch `queue/q-0423`). Page numbers are the printed pages of
`review-build-iso-review-1.pdf`, which are its PDF pages. Nothing but this file and the scripts
named below was written: no `.tex`, `.lean` or blueprint file was edited.

**Verdicts.** CONFIRMED: the referee is right. PARTLY: what holds is said. REFUTED: the paper is
right.

**Sources read for this record, at the page image** (`library page <citekey> --printed N --format
image`): Schilling, Song and Vondraček pp. 21 and 212; Kanter pp. 69, 70, 72, 74, 77, 78, 83 and 84;
Wolfe p. 144; Halgreen pp. 13, 14 and 15. Read in the text layer of a born-digital PDF: the
time-causal paper, version 1.1.0, p. 38, and the cone paper, pp. 13 and 14.

**Scripts** (`records/affine/reviews/verify-round1-scripts/`, each run, each passing its
assertions; `uv run --no-project --with mpmath --with sympy python <file>`):

| script | items | what it checks |
|---|---|---|
| `item01_02_matern_centre.py` | 1, 2 | the Matérn density at its centre for $c > d$ and $c \le d$; the slopes of Figure 1 |
| `item03_04_05_symbolic.py` | 3, 4, 5 | $a$ and $c$ of the stable exponents; the form of C6 at $d = 0$ and $d = 1$; the identity behind the uniqueness of a Bernstein triplet |
| `item06_gaussian_part.py` | 6 | the Gaussian as a mixture of uniform laws on balls; the intersection of two balls; a Matérn kernel convolved with a Gaussian |
| `item08_upper_bound_constant.py` | 8 | the referee's formula for $C'_\beta$; a constant explicit in the datum, on five Matérn kernels |
| `item09_projection_of_polar_profile.py` | 9 | the polar profile of the shadow in $\mathbb{R}^d$ of a measure on $\mathbb{R}^{d+1}$ |

A pattern is worth stating before the items. In items 1, 2, 4 and 7 the project's own records
already have the correct statement, and the paper's prose lost a qualifier: the blueprint
annotation of `prop:origin-lower-bound-d` says "for $c \le d$ ... the exponent is sharp there" and
"for $c > d$ the bound is true but weak"; the deposited script of Figure 1 expects the slope $0$ on
the line; the ledger entry A10 says that the hypothesis at $d = 0$ is one "which continuity and
$f \ge 0$ on $(0,\infty)$ already give"; and the cone paper states the tail identity "for almost
every $x > 0$". Each of these four fixes restores what the record says.

---

## 1. "The power cannot be improved" after Proposition 3.16 — CONFIRMED

**The paper.** `paper-iso/03-isotropic.tex:1130–1132`, p. 26: "The power cannot be improved. A
bound $c_1|x|^{\beta-d}$ with $\beta < c$ would give $\int g_t\,d\mu \ge C\,t^{-(d-\beta)/2}$,
against the upper bound of clause (4) of the theorem at a power between $\beta$ and $c$."
Proposition 3.16 (`prop:origin-lower-bound-d`) admits every finite $c > 0$.

**What settles it.** Clause (4) of Theorem 3.12 supposes $c \le d$, so the argument of the second
sentence is available only there, and there it is correct: a bound at a power $\beta < c \le d$
gives $\int g_t\,d\mu \ge C\,t^{-(d-\beta)/2}$, and the upper bound at $\beta' \in (\beta, c)$ is
$C'_{\beta'}\,t^{-(d-\beta')/2}$, of smaller order as $t \downarrow 0$. For $c > d$ the sentence is
false. The law then has a continuous density $p$ (Theorem 3.12(2)), and by Lemma A.2(1)
$p(0) = \lim_{t \downarrow 0}\int g_t\,d\mu = (2\pi)^{-d}\int\widehat\mu > 0$. So $p \ge p(0)/2$
near the centre, which is a bound $c_1|x|^{\beta-d}$ with $\beta = d < c$, while the bound of the
proposition, $c_1|x|^{c-d}$, tends to $0$. On the Matérn kernel with $d = 2$, $\gamma = 3/2$
($c = 3$): $p(0) = 1/\pi$ and $p(r)/r^{c-d}$ is unbounded (script, item 1(a)). The project knew
this: the blueprint annotation of `prop:origin-lower-bound-d`
(`blueprint/src/parts/03-isotropic.tex:998–1005`) restricts the sharpness to $c \le d$ and says
"For $c > d$ the bound is true but weak", and `Formalization/Adversarial.lean:132–144` holds the
false goal `origin_density_log_order_above_threshold` for the same reason.

**Fix.** Replace lines 1130–1133 up to "Proposition~\ref{prop:origin-rate-d}." by:

> For $c \le d$ the power cannot be improved. A bound $c_1|x|^{\beta-d}$ with $\beta < c$ would
> give $\int g_t\,d\mu \ge C\,t^{-(d-\beta)/2}$, against the upper bound of clause (4) of the
> theorem at a power between $\beta$ and $c$. At $c = d$ the bound is a positive constant, and the
> growth there is clause (2) of Proposition~\ref{prop:origin-rate-d}. For $c > d$ the bound holds
> and says little: the density is then continuous and positive at the centre
> (Theorem~\ref{thm:origin-boundedness-d}(2) and Lemma~\ref{lem:positive-transform-origin}(1)),
> and $c_1|x|^{c-d}$ tends to $0$.

**Touches.** Prose only. The statement, the blueprint and the Lean are right as they stand.

---

## 2. The slopes of Figure 1 — CONFIRMED

**The paper.** `paper-iso/03-isotropic.tex:1078–1079`, p. 25: "In Figure 1 the slopes at the centre
are $2\gamma - d$." The caption, lines 702–705, p. 21: "Here $c = 3/2$: the density is bounded on
the line and unbounded in the plane and in space, with slope $c - d$ at the centre."

**What settles it.** The figure is drawn at $\gamma = 3/4$. On the line $2\gamma - d = +\tfrac12$,
and the curve is bounded with
$p_1(0) = (2\pi)^{-1/2}\,\Gamma(1/4)/\Gamma(3/4) = 1.18034\ldots$ (Theorem 3.12(3) with the gamma
delay: $p(0) = (2\pi)^{-d/2}\,\Gamma(\gamma - d/2)/\Gamma(\gamma)$ for $\gamma > d/2$). Its slope on
logarithmic axes tends to $0$. What has the exponent $2\gamma - d = \tfrac12$ on the line is the
approach to the limit, $p_1(0) - p_1(r) \sim 1.3419\,r^{1/2}$, which the figure does not show. In
the plane and in space the slopes are $-\tfrac12$ and $-\tfrac32$, as stated (script, item 2). The
deposited script says the same: `records/affine/fig-matern-centre.py` prints the slope "$2\gamma -
d$ where $d > 2\gamma$" and expects $0$ at $d = 1$
(`fig-matern-centre-output.txt`: slope $-0.0011$, expected $+0.0000$). The sentence of p. 25 is
wrong for the curve on the line. The caption can be read correctly, the slope clause attached to
the two unbounded curves, and can be read wrongly.

**Fix.** Line 1078–1079:

> In Figure~\ref{fig:matern-centre} the two unbounded curves have the slope $2\gamma - d$ at the
> centre, $-\tfrac12$ in the plane and $-\tfrac32$ in space. The curve on the line is bounded and
> levels off at $(2\pi)^{-1/2}\,\Gamma(1/4)/\Gamma(3/4) \approx 1.18$.

Caption, lines 704–705:

> Here $c = 3/2$: the density is bounded on the line, where the curve levels off, and unbounded in
> the plane and in space, where its slope at the centre is $c - d$.

**Touches.** Prose only (one sentence and one caption). The figure and its script are right.

---

## 3. "The stable kernels have $c = \infty$" — CONFIRMED

**The paper.** `paper-iso/04-conclusion.tex:146–148`, p. 30: "Of the named families, the stable
kernels have $c = \infty$ and are smooth in every dimension." Clause (3) of Proposition 3.11
(`03-isotropic.tex:612–615`, p. 20) admits $0 < \alpha \le 1$, and says: "At $\alpha = 1$,
$\mu_{s,t} = g^{(d)}_{t^2-s^2}$, the Gaussian."

**What settles it.** The exponent is $F(r) = 2^{-\alpha}r^{2\alpha}$. By Corollary 3.13 the datum
has $a = \lim 2F(r)/r^2$ and $c = \lim (F(r) - \tfrac12 a r^2)/\log r$. For $\alpha < 1$: $a = 0$
and $c = \infty$. For $\alpha = 1$: $a = 1$, the remainder is $0$, the polar profile vanishes and
$c = 0$ (script, item 3). So the sentence is false at the Gaussian endpoint. The Gaussian is
smooth because it has a Gaussian part, and it is outside Theorem 3.12, which supposes Gaussian
coefficient $0$ and $c > 0$.

**Fix.**

> Of the named families, the stable kernels of index $2\alpha < 2$ have $c = \infty$ and are
> smooth in every dimension. So is the Gaussian, their member of index $2$, which has a Gaussian
> part and $c = 0$.

**Touches.** Prose only.

---

## 4. C6 "assumes more than its source" — CONFIRMED

**The paper.** `paper-iso/01-introduction.tex:480–482`, p. 6: "C6 composes two theorems of one
book, and asks its hypothesis in one dimension more than the book does, so that it assumes more
than its source." `paper-iso/02-line-papers.tex:504–505`, p. 13: "The book states the hypothesis
for every $d \ge 1$; C6 asks it also at $d = 0$, where it says only $f(0) \ge 0$, so C6 assumes
more than its source."

**The axiom.** `Formalization/AffineHemigroup/Interfaces.lean:320–329`: for `f : ℝ → ℝ` with
`0 ≤ f σ` for `0 < σ`, the hypothesis `hnd` asks, for every `d : ℕ`, that `ξ ↦ f (‖ξ‖^2)` is
continuous on `Rd d` and that the quadratic form
$\sum_{j,k}\bigl(f(|\xi_j|^2) + f(|\xi_k|^2) - f(|\xi_j - \xi_k|^2)\bigr)c_j\overline{c_k}$ is
$\ge 0$ for every $n$, all points and all complex coefficients. The conclusion is the
representation $f(\sigma) = a + b\sigma + \int(1 - e^{-\sigma t})\,m(dt)$ at every $\sigma > 0$.

**The source, at the page image.** Theorem 13.14, p. 212: "A function
$f : (0,\infty) \to [0,\infty)$ is a Bernstein function if, and only if, for all
$d \in \mathbb{N}$ the function $\xi \mapsto f(|\xi|^2)$, $\xi \in \mathbb{R}^d$, is continuous and
negative definite." Theorem 3.2, p. 21: "A function $f : (0,\infty) \to \mathbb{R}$ is a Bernstein
function if, and only if, it admits the representation [...] where $a, b \ge 0$ and $\mu$ is a
measure on $(0,\infty)$ satisfying $\int_{(0,\infty)}(1 \wedge t)\,\mu(dt) < \infty$. In
particular, the triplet $(a, b, \mu)$ determines $f$ uniquely and vice versa." The book's
$\mathbb{N}$ starts at $1$ (`READING-schilling2012bernstein-schoenberg.md`, § 1).

**What settles it.** $\mathbb{R}^0$ is one point, so at $d = 0$ continuity is empty and the form is
$f(0)\,|\sum_j c_j|^2$: the hypothesis there is $f(0) \ge 0$. The hypothesis at $d = 1$ with
$n = 1$, $\xi_1 = 0$, $c_1 = 1$ is $f(0) + f(0) - f(0) = f(0) \ge 0$ (script, item 4). It also
follows from the continuity at $\xi = 0$ and $f \ge 0$ on $(0,\infty)$. So the hypothesis for
$d \ge 0$ and the hypothesis for $d \ge 1$ are equivalent, and C6 assumes exactly what the book
assumes. The referee is right. The ledger entry (`blueprint/AXIOMS.md`, A10, "at least as strong
as the page: there it says $f(0) \ge 0$, which continuity and $f \ge 0$ on $(0,\infty)$ already
give"), the docstring of the axiom and the fidelity card F6.11 ("including $d = 0$, at least the
page's"; "≤ source. Faithful.") are all correct. Only the two sentences of the paper turn "at
least as strong" into "more".

**What the departure is.** Three things, none a strengthening. (i) C6 is a composite: the
direction "radially negative definite in every dimension implies Bernstein" of Theorem 13.14,
followed by the direction "Bernstein implies the representation" of Theorem 3.2. (ii) It concludes
less than the two theorems: neither converse, and not the uniqueness of $(a, b, \mu)$, which
Theorem 3.2 prints. (iii) It writes two readings out: $f$ is taken on $[0,\infty)$ with the value
$f(0)$ that the continuity hypothesis forces, the book's $f(0{+})$; and $d$ ranges over
$d \ge 0$, a redundancy.

**Fix.** § 1.1, lines 480–482:

> C6 composes two theorems of one book, one direction of each, and concludes less than they do:
> it leaves out the uniqueness of the representation.

§ 2.6, lines 504–505:

> The book states the hypothesis for every $d \ge 1$. C6 writes it for $d \ge 0$, which adds
> nothing: at $d = 0$ it says only $f(0) \ge 0$, and that is the hypothesis at $d = 1$ with
> $n = 1$, $\xi_1 = 0$ and $c_1 = 1$. C6 takes one direction of each of the two theorems and
> leaves out the uniqueness of $(a, b, m)$, which Theorem~3.2 also states.

The sentence of § 1.1 before it, "Three depart from the letter of one page", stands.

**Touches.** Prose, in § 1.1 and § 2.6. Optional, for the same wording everywhere: one clause in
the annotation of `thm:cited-A10` (`blueprint/src/parts/02-cited-facts.tex:262–263`), "equivalent
to the book's, the hypothesis at $d = 1$ giving the one at $d = 0$". The ledger entry, the
fidelity card and the Lean need nothing.

---

## 5. The alternative derivation of $\mathcal{A}_\infty = \mathcal{S}$, p. 54 — CONFIRMED

**The paper.** `paper-iso/appendix-isotropic.tex:1849–1871`, p. 54: "It also follows from
Schoenberg's radial theorem, C6 (Theorem 2.14), by the following route, which is the one the
formal proof takes (§ 1.1). [...] Hence $\eta \mapsto F(|\eta|)$ and
$\eta \mapsto F(|\eta|) - F(c|\eta|)$ are continuous and negative definite on $\mathbb{R}^d$ for
every $d$, and C6 represents $f$ and each residual [...]. Comparing the representation of $f$ with
the sum of those of $f(c^2\,\cdot)$ and of the residual, the uniqueness of such a representation
shows that the image of the measure $m$ of $f$ under every dilation $t \mapsto \lambda t$,
$0 < \lambda \le 1$, is at most $m$. So $m(dt) = k(t)\,t^{-1}dt$ with $k$ nonincreasing [...]."

**What settles it.** The paragraph is not a complete derivation from the printed cited facts.
Three steps are used and not printed, the two the referee names and one more.

1. *Negative definiteness.* "Hence [...] negative definite" is not a cited fact and is not proved
   in the paper. The residual is a difference of two Lévy–Khintchine forms, and C6 also needs
   $f \ge 0$ and the residual $\ge 0$ on $(0,\infty)$.
2. *Uniqueness.* Printed C6 gives existence only. The ledger deliberately leaves the uniqueness
   out of A10.
3. *From the dilation inequality to the profile.* No proof and no reference.

**What the Lean uses.** `filtration_top` (`Formalization/AffineHemigroup/FiltrationTop.lean:423`)
is `classAInf_of_classS` with `classS_of_classAInf`. The second spends the axiom twice (lines 327
and 345) and proves the three steps: `radial_negDef_of_lk` on `lkForm_sub_negDef`
(`LevyKhintchineNegDef.lean`), `bernstein_triplet_unique` (`BernsteinUnique.lean:92`, line 367 of
the proof, on the shared library's `ScaleSpace.laplace_uniqueness_locally_finite`), and
`ScaleSpace.exists_profile_of_dilate_le` (line 380). None of the three is an axiom. So the claim
of § 1.1, that the formal proof derives the identification "from C6 with C2, C3 and C4", is true
of the formal proof. The blueprint is complete as well: its proof of `thm:filtration-strict`
introduces the same paragraph by "is `lem:filtration-top`", and that lemma has a six-step proof of
record on three children, `lem:lk-negative-definite`, `lem:bernstein-triplet-unique` and
`lem:dilation-decreasing-profile` (`blueprint/src/parts/03-isotropic.tex:2646–2938`). The paper's
pinned copy dropped the pointer to the lemma (the comment at `appendix-isotropic.tex:1839–1842`),
and with it the three proofs.

**The missing steps, in full.** They are the blueprint's, read and checked here.

*(a) A Lévy–Khintchine form, and a difference of two, is negative definite.* Let
$\alpha' \le \alpha$ and $L' \le L$ be measures on $\mathbb{R}^d$ with
$\int(1 - \cos\langle\eta,x\rangle)\,L(dx) < \infty$ for every $\eta$, and put
$\psi(\eta) = \alpha|\eta|^2 + \int(1 - \cos\langle\eta,x\rangle)\,L(dx)$, $\psi'$ likewise, and
$\phi = \psi - \psi'$. For real $a_1, \dots, a_n$, by
$\cos(\theta_j - \theta_k) = \cos\theta_j\cos\theta_k + \sin\theta_j\sin\theta_k$,
$$\sum_{j,k} a_ja_k\bigl(\psi(\eta_j) + \psi(\eta_k) - \psi(\eta_j - \eta_k)\bigr)
 = 2\alpha\Bigl|\sum_j a_j\eta_j\Bigr|^2 + \int P_a\,dL, \qquad
 P_a(x) = \Bigl(\sum_j a_j(1 - \cos\langle\eta_j,x\rangle)\Bigr)^2
        + \Bigl(\sum_j a_j\sin\langle\eta_j,x\rangle\Bigr)^2 \ge 0 .$$
The same holds for $\psi'$, and $\int P_a\,dL' \le \int P_a\,dL$, so the form of $\phi$ is
$2(\alpha - \alpha')|\sum a_j\eta_j|^2 + \int P_a\,dL - \int P_a\,dL' \ge 0$. For complex
coefficients the matrix of the form is real and symmetric, so the form is the sum of the real
forms of the real and the imaginary parts. In the paragraph: $(\alpha, L) = (\tfrac12 a_d, \nu_d)$
with $(\alpha', L') = (0, 0)$ for $F(|\eta|)$, and with
$(\alpha', L') = (\tfrac12 a_d c^2, (c\,\cdot)_*\nu_d)$ for the residual, where
$(c\,\cdot)_*\nu_d \le \nu_d$ because the image has the density
$k_d(|x|/c)/(|S^{d-1}||x|^d)$ and $k_d$ is nonincreasing. The form of a function $g$ with
$g(0) = 0$ at one point with coefficient $1$ is $2g(\sigma) - g(0)$, which gives $g_c \ge 0$.

*(b) The uniqueness of the representation.* Let
$G(\sigma) = a + b\sigma + \int(1 - e^{-\sigma t})\,m(dt) = a' + b'\sigma + \int(1 - e^{-\sigma
t})\,m'(dt) < \infty$ for every $\sigma > 0$. Since
$(1 - e^{-\sigma t}) + (1 - e^{-(\sigma+2)t}) + e^{-\sigma t}(1 - e^{-t})^2 = 2(1 - e^{-(\sigma+1)t})$
(script, item 5),
$$\int e^{-\sigma t}(1 - e^{-t})^2\,m(dt) = 2G(\sigma+1) - G(\sigma) - G(\sigma+2),$$
and the same for $m'$. So the measures $(1 - e^{-t})^2\,m(dt)$ and $(1 - e^{-t})^2\,m'(dt)$ have the
same finite Laplace transform on $(0,\infty)$, hence are equal, and $m = m'$. Then
$a + b\sigma = a' + b'\sigma$ for every $\sigma > 0$. This is the last sentence of the book's
Theorem 3.2 (p. 21, read at the page image for item 4), which A10 does not carry. In the paragraph
it is applied to $f = f(c^2\,\cdot) + g_c$: the right side has the measure $D_{c^2}m + m_c$, with
$D_\lambda m$ the image of $m$ under $t \mapsto \lambda t$, so $m = D_{c^2}m + m_c \ge D_{c^2}m$.

*(c) A measure that decreases under every dilation has a nonincreasing profile.* Let $m$ be a
measure on $(0,\infty)$ with $\int(1 \wedge t^2)\,m(dt) < \infty$ and $D_\lambda m \le m$ for
$0 < \lambda \le 1$. Let $\tilde m$ be the image of $m$ under $\log$. Its right rays are finite,
and $\tilde m(A + h) \le \tilde m(A)$ for every Borel $A$ and $h > 0$. Put
$\varphi(\theta) = \sup_n 2^n\,\tilde m((\theta, \theta + 2^{-n}])$. Each term is nonincreasing in
$\theta$, and the terms increase with $n$, because the right half of an interval, shifted, has at
most the mass of the left half. By monotone convergence and Tonelli,
$\int_a^b\varphi$ is the limit of quantities between $\tilde m((a + 2^{-n}, b])$ and
$\tilde m((a, b + 2^{-n}])$, so $\tilde m = \varphi(\theta)\,d\theta$, and $\varphi$ is finite
because the rays are. Then $m(dt) = k(t)\,t^{-1}dt$ with $k = \varphi \circ \log$, nonincreasing.
This is the step from the dilation inequality to the profile in the proof of Lemma 7.1 of the line
paper, where it is not a numbered statement.

**Fix.** Two ways, both in the paper only. *The complete one:* print `lem:filtration-top` with its
three children in Appendix A, verbatim from the blueprint (about 120 lines of proofs of record),
and let the proof of Theorem 3.19(3) say "is Lemma A.x", as the blueprint does. *The small one:*
keep the paragraph, call it what it is, and name the three steps. Replace "It also follows from
Schoenberg's radial theorem, C6 (Theorem 2.14), by the following route, which is the one the
formal proof takes (§ 1.1)." by

> The formal proof does not use that proposition. It derives the identification from Schoenberg's
> radial theorem, C6 (Theorem~\ref{thm:cited-A10}), and what follows is an outline of its route.
> Three of its steps are lemmas of the formal development that are not printed here, and each is
> named where it is used.

after "negative definite on $\mathbb{R}^d$ for every $d$" add

> (a computation with the \Levy--Khintchine form, which gives the nonnegativity of the form for
> the difference of two such forms with ordered data)

and replace "the uniqueness of such a representation shows that [...] is at most $m$. So
$m(dt) = k(t)\,t^{-1}dt$ with $k$ nonincreasing," by

> the uniqueness of such a representation shows that the image of the measure $m$ of $f$ under
> every dilation $t \mapsto \lambda t$, $0 < \lambda \le 1$, is at most $m$. The uniqueness is not
> part of C6. It is the last sentence of Theorem~3.2 of the book (p.~21), and the formal
> development proves it from the uniqueness of the Laplace transform of a measure. A measure on
> $(0,\infty)$ that every such dilation decreases has the form $k(t)\,t^{-1}dt$ with $k$
> nonincreasing: this is the step from the dilation inequality to the profile in the proof of
> \prog{V}{Lem.~7.1}. So $m(dt) = k(t)\,t^{-1}dt$,

**Not the fix:** adding the uniqueness to C6, as the referee's table suggests. That widens a cited
fact where the development has a proof.

**Touches.** The paper's pinned copy of the proof of `thm:filtration-strict` (re-pin), or a new
transcription of four blueprint nodes into Appendix A. No blueprint statement or proof changes, no
ledger entry, no Lean.

---

## 6. The proof of Proposition 3.14

### 6(a) The Borel measurability of $K \mapsto u_K$ — CONFIRMED (asserted, not proved; true)

**The paper.** `paper-iso/appendix-isotropic.tex:1174–1177`, p. 44: "The source puts its mixing
measure on $W_d$ itself; reading it as almost every measure being a $u_K$ uses only that $W_d$ is
universally measurable, which it is, being analytic: the image of the Polish space of the nonempty
compact convex symmetric sets under the Borel map $K \mapsto u_K$." The same sentence is in the
blueprint proof (`blueprint/src/parts/03-isotropic.tex:1304–1306`), in ledger A8 and in the docstring of the axiom
(`Interfaces.lean:226–231`).

**What settles it.** The sentence is not used by the derivation of the density, which starts from
C5 as printed: $\Lambda$ on the measures with the evaluation $\sigma$-algebra, almost every measure
a $u_K$. It justifies reading Kanter's mixing measure, which lives on $W_d$, in that form. The map
is not continuous (Kanter's Example 3.1: flattening rhombi), so "Borel" needs an argument, and none
is given. Kanter's own Corollary 3.1, p. 72, "$W_L$ is a Borel subset", does not supply it: its
proof begins "$W_L \subset T^*_L$", and $T^*_L$ is the set of laws with a density on $L$
(Definition 2.2, p. 69), so it covers only the sets that span $L$; the project's audit had found
this. The following argument is complete, proves more than the paper asserts, and uses no
descriptive set theory.

**The argument.** Let $\mathcal{K}$ be the nonempty compact convex sets $K = -K$ of
$\mathbb{R}^d$ with the Hausdorff metric, and for $k \ge 1$ and $n \ge 1$ let $\mathcal{K}_{k,n}$
be the $K \in \mathcal{K}$ with $\dim\operatorname{span}K = k$, $K \subseteq n\bar B$ and
$K \supseteq \tfrac1n\bar B \cap \operatorname{span}K$, $\bar B$ the closed unit ball.

1. *Every $K$ of dimension $k \ge 1$ is in some $\mathcal{K}_{k,n}$.* $K$ is bounded, and it
   contains a basis $y_1, \dots, y_k$ of its span $V$, hence the convex hull of the $\pm y_i$,
   which contains a ball of $V$ round $0$.
2. *$\mathcal{K}_{k,n}$ is compact.* Let $K_j \in \mathcal{K}_{k,n}$ with spans $V_j$. By
   Blaschke's selection theorem and the compactness of the Grassmannian, along a subsequence
   $K_j \to K \in \mathcal{K}$ and $V_j \to V'$ of dimension $k$. Then $K \subseteq V' \cap n\bar
   B$, since a limit of points of $V_j$ is in $V'$, and $K \supseteq \tfrac1n\bar B \cap V'$,
   since every point of the right side is a limit of points of $\tfrac1n\bar B \cap V_j \subseteq
   K_j$. So $\operatorname{span}K = V'$ and $K \in \mathcal{K}_{k,n}$.
3. *$K \mapsto u_K$ is continuous on $\mathcal{K}_k = \bigcup_n\mathcal{K}_{k,n}$, for weak
   convergence.* Let $K_j \to K$ in $\mathcal{K}_k$, with spans $V_j$ and $V$, let $y_1, \dots,
   y_k \in K$ be a basis of $V$ and $y_i^j \in K_j$ with $y_i^j \to y_i$. For large $j$ the $y_i^j$
   are independent (their Gram determinant converges to a positive number), hence a basis of
   $V_j$. Let $T_j : V \to V_j$ be linear with $T_jy_i = y_i^j$, so that
   $\varepsilon_j := \|T_j - \mathrm{id}\| \to 0$. A linear bijection carries the uniform law on a
   set to the uniform law on its image, so $u_{K_j} = (T_j)_*u_{K'_j}$ with
   $K'_j := T_j^{-1}K_j \subseteq V$, and $K'_j \to K$, because
   $|T_j^{-1}z - z| \le \varepsilon_j|z|/(1 - \varepsilon_j)$. Inside $V$, $K \supseteq rB_V$ for
   an $r > 0$. If the Hausdorff distance $\delta_j$ of $K'_j$ and $K$ is below $r$, then
   $K'_j \subseteq K + \delta_jB_V \subseteq (1 + \delta_j/r)K$, and by support functions,
   $h_{K'_j} \ge h_K - \delta_j \ge (1 - \delta_j/r)h_K$, so $(1 - \delta_j/r)K \subseteq K'_j$.
   Hence $\mathrm{Vol}_V(K'_j \,\triangle\, K) \to 0$, and $u_{K'_j} \to u_K$ in total variation.
   For bounded continuous $\varphi$, $\int\varphi\,du_{K_j} = \int\varphi \circ T_j\,du_{K'_j}$,
   and $\varphi \circ T_j \to \varphi$ uniformly on the bounded set $2K$. So
   $\int\varphi\,du_{K_j} \to \int\varphi\,du_K$.
4. *$W_d$ is a countable union of compact sets.* By 2 and 3 each
   $\{u_K : K \in \mathcal{K}_{k,n}\}$ is compact in the weak topology, and with $\{\delta_0\}$,
   the case $k = 0$, these sets exhaust $W_d$ by 1. So $W_d$ is an $F_\sigma$, hence a Borel set of
   the space of probability measures, whose Borel $\sigma$-algebra is the one generated by the
   evaluations.

So $W_d$ is Borel, which is Kanter's Corollary 3.1 for sets of every dimension, and is more than
"universally measurable". A reference could carry step 2 (Blaschke's selection theorem) and the
volume convergence in step 3; the library holds no source for either under a citekey this record
could find, and a reference is read at the page before it is cited. The descriptive route (the
map is Borel, being continuous on each piece of a finite Borel partition; an analytic set is
universally measurable) is also correct and needs two cited theorems that the argument above
avoids.

**Fix.** In the proof of record, replace the sentence quoted above by

> The source puts its mixing measure on $W_d$ itself. Reading it as almost every measure being a
> $u_K$ uses only that $W_d$ is a Borel set of the probability measures, and it is one, being a
> countable union of compact sets: for $k \ge 1$ the map $K \mapsto u_K$ is continuous on the sets
> $K$ of dimension $k$, for the Hausdorff metric and weak convergence, these sets are a countable
> union of compact families, those with $K \subseteq n\bar B$ and
> $K \supseteq \tfrac1n\bar B \cap \operatorname{span}K$, and $k = 0$ gives $\delta_0$ alone.

with steps 1–3 as a short lemma of Appendix A, or as a footnote-length paragraph.

**Touches.** A shared proof of record (`prop:isotropic-radial-monotone`, at the blueprint, then
mirrored), the text of ledger A8 ("$W_d$ is analytic [...] hence universally measurable"), and the
docstring of `wolfe_symmetric_unimodal`. No declaration changes: the axiom's statement does not
mention the measurability of $W_d$.

### 6(b) The Gaussian case of C5 — PARTLY

**The paper.** `paper-iso/01-introduction.tex:494–498`, p. 6: "The source of C5 has a gap for one
case. Wolfe states his theorem for every symmetric law of class L, and his proof ends with a
theorem of Kanter that is stated for laws with no Gaussian part [...]. So for a law with a Gaussian
part C5 rests on Wolfe's statement and not on a printed proof." The same in
`02-line-papers.tex:474–478`, p. 12, in the annotation of `thm:cited-A8`, and in ledger A8, which
adds: "Whether Kanter shows that a centred Gaussian law is symmetric unimodal in his sense was not
found."

**What holds.** The paper's description of the two printed proofs is accurate, and the referee
could not check it. Wolfe, p. 144, last line: "Theorem 2 now follows from Theorem 4.1 of Kanter."
Kanter, p. 77: "We shall assume $q_X \equiv 0$, unless otherwise stated (no Gaussian part)", and
Theorem 4.1, p. 78, is stated under it. The referee's conclusion is also right: the extension is
routine, and both of its ingredients are printed in Kanter's paper. What the referee cites for it,
the abstract, is not the anchor. The anchors, read at the page image:

- **Kanter, Lemma 3.1, p. 70:** "Let $L$ be a linear subspace of $R^N$ and let $\mu$ be a
  log-concave, symmetric, probability measure on $L$ with $d\mu/d\,\mathrm{Vol}_L = f$ where
  $f \in T_L$. Then $\mu \in U_L$." ($T_L$, Definition 2.2, p. 69: the log-concave symmetric
  nonnegative functions on $L$ of integral $1$.) A centred Gaussian law has such a density on the
  range of its covariance, so it is symmetric unimodal in Kanter's sense. This answers the
  question the ledger left open. P. 84 has the same in words: "any symmetric random vector $X$
  which is unimodal according to Anderson or Sherman is unimodal in our sense as well", Anderson's
  sense being a symmetric density with convex level sets (p. 83).
- **Kanter, Theorem 3.2, p. 74:** "Let $\mu_1, \mu_2 \in U_N$. Then $\mu_1 * \mu_2 \in U_N$."

**The extension.** Let $\mu$ be symmetric and self-decomposable on $\mathbb{R}^d$, with triplet
$(A, \nu, \gamma)$ (C4, C3(i)). Its transform is real, so by C3(ii) $\nu$ is symmetric and
$\gamma = 0$. Let $\mu_0$ be the law with triplet $(0, \nu, 0)$ (C3(iii)). It is symmetric, and
self-decomposable by C2, which puts no condition on $A$. So $\mu = N(0, A) * \mu_0$, where
$\mu_0 \in U_d$ by Wolfe's theorem in the case his printed proof covers, $N(0, A) \in U_d$ by
Lemma 3.1, and $\mu \in U_d$ by Theorem 3.2. So C5 is carried by printed proofs for every
symmetric self-decomposable law, and the paper's sentence "rests on Wolfe's statement and not on a
printed proof" can be withdrawn.

**The direct repair is a complete proof of Proposition 3.14 for a datum with a Gaussian part.**
Suppose the proposition known for data with Gaussian coefficient $0$, where C5 is used inside the
range of Wolfe's printed proof.

*Clause (2), $a > 0$.* Let $\mu_0$ be the law of the datum $(0, k_d)$, which satisfies
Definition 3.9 with the same $k_d$. The transform of the law $\mu$ of $(a, k_d)$ is
$e^{-a|\xi|^2/2}\,\widehat{\mu_0}(\xi)$, so $\mu = \gamma_a * \mu_0$ with $\gamma_a = N(0, aI)$, of
density $g_a(x) = (2\pi a)^{-d/2}e^{-|x|^2/2a}$. Two cases, and no third.
(i) $k_d = 0$ almost everywhere. Then $\nu_d = 0$, $\mu_0 = \delta_0$, and $\mu = \gamma_a$ has the
density $g_a$, which is radial and decreasing.
(ii) Otherwise $(0, k_d)$ is not trivial, and by the case $a = 0$ the law $\mu_0$ has a density
$p_0(x) = q_0(|x|)$ with $q_0$ nonincreasing; in particular it has no atom. Then $\mu$ has the
density $p = g_a * p_0$ (Tonelli), bounded by $(2\pi a)^{-d/2}$, and radial, both factors being
rotation invariant. It is radially nonincreasing by the lemma below, and $q(r) := p(re_1)$ is the
function of the statement.

*Lemma (two radially nonincreasing functions).* Let $f(x) = \varphi(|x|)$ and $g(x) = \psi(|x|)$
with $\varphi, \psi : (0,\infty) \to [0,\infty]$ nonincreasing. Then $(f * g)(x) \le (f * g)(x')$
whenever $|x| \ge |x'|$. *Proof.* For $s > 0$ the set $\{f > s\}$ is, up to a null set, a ball
$B_{\rho(s)}$ round $0$, of radius in $[0,\infty]$, and $f = \int_0^\infty 1_{\{f > s\}}\,ds$;
likewise $g$. By Tonelli
$(f * g)(x) = \int_0^\infty\!\!\int_0^\infty |B_{\rho(s)} \cap (x + B_{\rho'(u)})|\,ds\,du$. So it
is enough that $V(x) := |B(0, R) \cap B(x, R')|$ is a nonincreasing function of $|x|$. It depends
on $|x|$ only, by rotation, and is constant if a radius is infinite. Let $x_i = t_ie$ with
$0 \le t_1 < t_2$, put $A_i = B(0, R) \cap B(x_i, R')$, and let $\sigma$ be the reflection in the
hyperplane $H = \{\langle y, e\rangle = (t_1 + t_2)/2\}$, which exchanges $x_1$ and $x_2$. A point
$y \in A_2 \setminus A_1$ is in $B(x_2, R')$ and not in $B(x_1, R')$, so it is nearer to $x_2$ than
to $x_1$ and lies on the far side of $H$ from $0$. Then $|\sigma y| \le |y|$, so
$\sigma y \in B(0, R)$; $\sigma y \in B(x_1, R')$; and $\sigma y \notin B(x_2, R')$. So $\sigma$
maps $A_2 \setminus A_1$ into $A_1 \setminus A_2$, and
$|A_2| = |A_2 \cap A_1| + |A_2 \setminus A_1| \le |A_1|$. $\square$

*Clause (1).* $\widehat{\mu_{0,t}}(\xi) = e^{-F(s|\xi|)}$ with $s = \chi(t) > 0$ and
$F \in \mathcal{A}_d$, $F \not\equiv 0$ (Theorem 3.6). By Proposition 3.10(1), in its forward
direction, $F(|\cdot|)$ is the exponent of a datum $(a, k_d)$, not trivial, with law $\mu'$, and
$\mu_{0,t}$ is the image of $\mu'$ under $x \mapsto sx$. If $\mu'$ has the density $q'(|x|)$, then
$\mu_{0,t}$ has the density $s^{-d}q'(|x|/s)$, and clause (2) gives $q'$.

The script checks the lemma's ball statement on closed forms in dimensions 1 to 3, and the
conclusion on the Matérn kernel of index $3/4$ convolved with $N(0, 0.3\,I)$ in the plane and in
space. For the isotropic Gaussian, Lemma 3.1 is explicit:
$g_a = \int_0^\infty u_{B_\rho}\,w(\rho)\,d\rho$ with $w(\rho) = V_d\,\rho^{d+1}g_a(\rho)/a$, of
integral $1$ (script).

**What each route changes.**

- *Route A, the citation completed.* § 1.1 (lines 494–501) and § 2.6 (lines 474–478) say that
  Wolfe's printed proof covers the laws with no Gaussian part and that Kanter's Lemma 3.1 and
  Theorem 3.2 give the others, by the three-line extension above. The annotation of
  `thm:cited-A8` and the paragraph "The Gaussian part" of ledger A8 are rewritten to match, and
  `READING-kanter1977unimodality.md` gains the two anchors (pp. 69–70 and 74 at the page image,
  and p. 84). The statement of C5, the proof of record of Proposition 3.14, the axiom and the Lean
  proof are unchanged: the axiom is Wolfe's statement, and it is now backed by printed proofs in
  both cases. Proposed wording for § 1.1:

  > Wolfe's printed proof of C5 covers the laws with no Gaussian part: it ends with a theorem of
  > Kanter that is stated for them (\sscite{kanter1977unimodality}, Thm.~4.1, p.~78, with the
  > convention of p.~77). A symmetric self-decomposable law with a Gaussian part is the
  > convolution of a centred Gaussian law and a symmetric self-decomposable law with none (C2 and
  > C3), and two results of the same paper finish the proof for it: a symmetric law with a
  > log-concave density, such as a centred Gaussian law, is symmetric unimodal (Lemma~3.1,
  > p.~70), and the convolution of two symmetric unimodal laws is symmetric unimodal (Thm.~3.2,
  > p.~74). One statement uses C5 for a law with a Gaussian part:
  > Proposition~\ref{prop:isotropic-radial-monotone}, when the kernel has one.

- *Route B, the direct repair.* The proof of record of `prop:isotropic-radial-monotone` gains the
  reduction and the lemma above, and C5 can be **narrowed** to laws with no Gaussian part, so that
  the paragraph on the gap disappears from § 1.1 and § 2.6 instead of being rewritten. The row of
  Table 1 changes: clause (1) then goes through Proposition 3.10(1) and rests on C2, C3 and C4 as
  well. The Lean needs work to match: a narrowed axiom (a new statement of the hypothesis "no
  Gaussian part", and a new fidelity card), the splitting $\mu = \gamma_a * \mu_0$, the lemma on
  radially nonincreasing functions, and `radial_monotone_family` rerouted through the polar
  reading. That is several hundred lines, not priced here; the estimate belongs beside the Lean
  statement. If the proof of record changed and the Lean did not, the printed proof would use less
  of C5 than the formal one, and § 1.1 would have to say so.

Route A is the smaller change and removes the "impression of unresolved mathematical doubt" the
referee objects to. Route B is the narrower trust base.

**Touches.** Route A: prose of § 1.1 and § 2.6, the annotation of a cited-fact node, ledger A8, a
reading note. No shared statement, no proof, no Lean. Route B: a shared proof of record, the
statement and annotation of `thm:cited-A8`, ledger A8, Table 1, and the Lean.

---

## 7. Proposition 2.7: $k(x) = \varpi((x,\infty))$ — CONFIRMED

**The paper.** `paper-iso/02-line-papers.tex:326`, p. 10: "with $\varpi = -dk$ the measure on
$(0,\infty)$ given by the folded profile, $k(x) = \varpi((x,\infty))$." A folded profile is any
nonincreasing $k : (0,\infty) \to [0,\infty)$ with the two integrability conditions (line 167).

**What settles it.** $\varpi((x,\infty)) = k(x{+})$, since $k(\infty) = 0$ is forced. So the
identity holds at the continuity points of $k$ and fails at a jump of a profile that is not
right-continuous: $\mathbf{1}_{(0,\tau]}$ is a folded profile with the same exponent and the same
$\varpi = \delta_\tau$ as $\mathbf{1}_{(0,\tau)}$, and $k(\tau) = 1 \ne 0 = \varpi((\tau,\infty))$.
The statement being restated has the qualifier. Cone paper, Lemma 3.1(2), p. 13: "$\varpi$ is any
positive measure on $(0,\infty)$ with $\varpi((x,\infty)) = k(x)$ for almost every $x > 0$", and
its p. 14 says why: "that is why the tail identity is asserted almost everywhere and not
everywhere, and a right-continuous version of $k$ is neither available nor needed." The
restatement dropped "for almost every $x$". The uniqueness of the superposition is unaffected.

**Fix.** Of the referee's two alternatives, the source's:

> with $\varpi = -dk$ the measure on $(0,\infty)$ given by the folded profile,
> $\varpi((x,\infty)) = k(x)$ for almost every $x > 0$.

**Touches.** Prose only: the restated statement has no blueprint node (the comment at line 316).

---

## 8. Proposition 3.17 and the constant $C'_\beta$ — CONFIRMED

**The paper.** `paper-iso/03-isotropic.tex:1157–1158`, p. 26: "One may take
$A_\beta = (2\pi)^{d/2}e^{1/2}\,C'_\beta$, for every constant $C'_\beta$ with which the upper bound
of Theorem 3.12(4) holds." Theorem 3.12(4), lines 876–877, p. 23: "for every $\beta$ with
$0 < \beta < c$ there is $C'_\beta$ with $\int g_t\,d\mu \le C'_\beta\,t^{-(d-\beta)/2}$ for all
$t > 0$." The opening of § 3.3, lines 803–804, p. 22: "Two bounds with explicit constants
complement the rate."

**Is the referee's formula what the proofs give?** Yes. The proof of clause (4)
(`appendix-isotropic.tex:904–910`, p. 41) gives
$\int g_t\,d\mu \le (2\pi)^{-d}C_\beta\,t^{-(d-\beta)/2}\int_{\mathbb{R}^d}|y|^{-\beta}
e^{-|y|^2/2}\,dy$, and
$\int_{\mathbb{R}^d}|y|^{-\beta}e^{-|y|^2/2}\,dy = |S^{d-1}|\,2^{(d-\beta)/2-1}\,
\Gamma\bigl(\tfrac{d-\beta}2\bigr)$ (script, part (1)). So
$$C'_\beta = (2\pi)^{-d}\,C_\beta\,|S^{d-1}|\,2^{(d-\beta)/2-1}\,\Gamma\bigl(\tfrac{d-\beta}2\bigr),$$
the referee's formula, with $C_\beta = 2^\beta(1 + e^{\beta L})$ of the proof of clause (1)
(line 819, p. 40). The referee is also right that the statement displays no constant: $C_\beta$
depends on three choices of that proof, $\beta_1 \in (\beta, c)$, a radius $r_\beta \in (0,1]$
with $k_d \ge \beta_1$ on $(0, r_\beta)$, and an $\varepsilon \in (0,1]$ for which the cap
$\{|\langle e_1,\eta\rangle| \ge \varepsilon\}$ has normalized measure at least $\beta/\beta_1$,
and $\varepsilon$ is obtained there by a limit, not by a formula.

**A constant explicit in the datum.** Take $\beta_1 = (\beta + c)/2$, which is finite because
$c \le d$, and $\varepsilon = (c - \beta)/((c + \beta)\sqrt d)$. The cap condition holds: the band
$\{|\eta_1| < \varepsilon\}$ has normalized measure at most $\varepsilon\sqrt d$, so the cap has
at least $1 - (c - \beta)/(c + \beta) = \beta/\beta_1$. (For $d \ge 3$ the density of $\eta_1$ is
at most $\Gamma(d/2)/(\sqrt\pi\,\Gamma((d-1)/2)) \le \sqrt{(d-1)/(2\pi)}$, by the log-convexity of
$\Gamma$; for $d = 2$ the band has measure $(2/\pi)\arcsin\varepsilon \le \varepsilon$; for
$d = 1$ it is empty. Script, part (2): the quotient of the band by $\varepsilon\sqrt d$ is at most
$0.75$ for $d \le 12$.) With $L = 3 - \log(\varepsilon r_\beta)$ this gives:

> Let $r_\beta \in (0,1]$ satisfy $k_d(r_\beta) \ge (\beta + c)/2$. Then one may take
> $$A_\beta = \sqrt e\;2^{\beta/2}\;\frac{\Gamma\bigl(\tfrac{d-\beta}{2}\bigr)}{\Gamma\bigl(\tfrac d2\bigr)}
>   \Bigl(1 + \Bigl(\frac{e^3\sqrt d\,(c + \beta)}{(c - \beta)\,r_\beta}\Bigr)^{\beta}\Bigr),$$
> which is $(2\pi)^{d/2}e^{1/2}\,C'_\beta$ for
> $C'_\beta = (2\pi)^{-d}\,C_\beta\,|S^{d-1}|\,2^{(d-\beta)/2-1}\,\Gamma\bigl(\tfrac{d-\beta}2\bigr)$
> and $C_\beta = 2^\beta\bigl(1 + (e^3\sqrt d\,(c+\beta)/((c-\beta)\,r_\beta))^\beta\bigr)$.

It has the form of the lower bound's constants, which depend on an $\varepsilon_0$ with
$k_d(\varepsilon_0) \ge c/2$. The script checks the closed form against the chain, and each
inequality of the chain with these constants on five Matérn kernels with $c \le d$ in dimensions
1 to 3 (the transform, the blurred centre, the ball, the density); the constants are far from
sharp, as the proof makes them. A smaller one is available: the proof has
$|\widehat\mu(\xi)| \le e^{\beta L}|\xi|^{-\beta}$ before it passes to $(1 + |\xi|)^{-\beta}$, and
clause (4) uses only that, so $C_\beta$ may be replaced by $e^{\beta L}$ in $C'_\beta$.

**Fix.** The display above with its one sentence on $r_\beta$, as prose after Proposition 3.17,
marked as a computation of the prose (§ 1.1, "What is neither"). Then "two bounds with explicit
constants" is true of both. Putting the formula into the statement is a different change: the
statement is shared and machine-checked, and the Lean proof of clause (1) of the theorem obtains
$\varepsilon$ by a limit, so a formal constant needs the cap estimate in Lean, which is new work
and not priced here.

**Touches.** As prose: prose only. In the statement: a shared statement (blueprint
`prop:origin-upper-bound-d`, and `thm:origin-boundedness-d`(1) and (4) for $C_\beta$ and
$C'_\beta$), and the Lean.

---

## 9. The referee's short proof that the filtration is strict — CONFIRMED (correct; it proves the strictness of every inclusion, not clause (1) of Theorem 3.19)

**The review**, § 6, "Dimension dependence": in dimension $d$ take $k_d = b\,\mathbf{1}_{(0,\tau)}$;
if its exponent were in $\mathcal{A}_{d+1}$, the projected Lévy measure would be the prescribed
one, its support would force the support in $\mathbb{R}^{d+1}$ into the ball of radius $\tau$, the
density there is bounded near the edge, so the projected density tends to $0$ as $r \uparrow \tau$,
and the prescribed one tends to $b/(|S^{d-1}|\tau^d) > 0$.

**Line by line.**

1. *The datum and its exponent.* $(0, b\,\mathbf{1}_{(0,\tau)})$ is an isotropic origin datum in
   dimension $d$, with Lévy measure $\nu_d$ of density $b\,\mathbf{1}_{\{|x|<\tau\}}/(|S^{d-1}||x|^d)$.
   Its exponent is radial, $F_d(\xi) = F(|\xi|)$ with $F(r) := F_d(re_1)$, and $F \in \mathcal{A}_d$
   by Proposition 3.10(1) and (2). The paper says so itself, `03-isotropic.tex:562–564`, p. 19.
   So "$F \in \mathcal{A}_{d+1}$" is a meaningful question about the function $F$.
2. *The lift.* Suppose $F \in \mathcal{A}_{d+1}$. By Proposition 3.10(1), forward, $F(|\zeta|)$ on
   $\mathbb{R}^{d+1}$ is the exponent of a datum $(a', k')$ with Lévy measure $\nu'$, of density
   $k'(|z|)/(|S^d||z|^{d+1})$, $k'$ nonincreasing and finite at every $r > 0$.
3. *The shadow is the prescribed measure.* Let $\Pi$ be the projection on the first $d$
   coordinates and $\bar\nu$ the image of $\nu'$, restricted to $\mathbb{R}^d \setminus \{0\}$.
   It is a Lévy measure, as $|\Pi z| \le |z|$, and it is symmetric. At $\zeta = (\xi, 0)$,
   $F(|\xi|) = \tfrac12 a'|\xi|^2 + \int(1 - \cos\langle\xi,x\rangle)\,\bar\nu(dx)$. By C3(iii) and
   C3(ii), as in the proof of Theorem 3.20, $a' = 0$ and $\bar\nu = \nu_d$.
4. *The support.* $\nu'(\{|\Pi z| > \tau\}) = \nu_d(\{|x| > \tau\}) = 0$. If $k'(r) > 0$ for some
   $r > \tau$, then $k' > 0$ on $(0, r]$, and $\nu'$ has a positive density on the open set
   $\{|\Pi z| > \tau,\ |z| < r\}$, which is not empty. So $k' = 0$ on $(\tau,\infty)$.
5. *The edge.* For $\tau/2 \le |x| = r < \tau$ the density of $\bar\nu$ at $x$ is
   $\int_{|h| < \sqrt{\tau^2 - r^2}} k'(\sqrt{r^2 + h^2})\,(|S^d|(r^2 + h^2)^{(d+1)/2})^{-1}dh
   \le 2M\sqrt{\tau^2 - r^2}$, with $M := k'(\tau/2)/(|S^d|(\tau/2)^{d+1})$, finite: "its density is
   bounded near that edge" is the monotonicity and finiteness of $k'$. So
   $\bar\nu(\{\tau(1 - \varepsilon) < |x| < \tau\}) = O(\varepsilon^{3/2})$, while
   $\nu_d$ gives that shell the mass $b\log\frac{1}{1 - \varepsilon} \ge b\,\varepsilon$. A
   contradiction for small $\varepsilon$.

Every line is correct. The argument uses C2, C3 and C4, the cited facts of Theorem 3.20.

**Is it the argument of Theorem 3.20?** Yes, the same three steps (the shadow by C3(iii) and
C3(ii), the support, the edge), with the projection $\mathbb{R}^{d+1} \to \mathbb{R}^d$ in place of
$\mathbb{R}^d \to \mathbb{R}$, and the length of a chord in place of the measure of a cap. At
$d = 1$ it is Theorem 3.20 at $d = 2$: the datum $(0, b\,\mathbf{1}_{(0,\tau)})$ in dimension $1$
is the $\Cin$ ray. The paper's last sentences after Theorem 3.20 name these data ("those are
members of $\mathcal{A}_d$") and do not ask where they sit in $\mathcal{A}_{d+1}$.

**What it proves.** For every $d \ge 1$, the exponent of $(0, b\,\mathbf{1}_{(0,\tau)})$ in
dimension $d$ is in $\mathcal{A}_d \setminus \mathcal{A}_{d+1}$. That is the strictness of every
inclusion, the part of clause (3) of Theorem 3.19 that does not identify $\mathcal{A}_\infty$. It
does **not** prove clause (1), which is a statement about the family $F^{(w)}$, or clause (2).
The separating family is needed for the quantitative statements only: the criterion $w \le w_d$,
the strict decrease and the exact order of the critical values (Lemmas A.4 and A.5), and that
witnesses exist with smooth profiles and of the form $F_{\mathrm I}(r^2/2)$ of the bridge.

**A general form** (found while checking; not in the review). The polar profile of the shadow is
$$\bar k(r) = C_d\int_{\mathbb{R}} k'\bigl(r\sqrt{1 + u^2}\bigr)\,(1 + u^2)^{-(d+1)/2}\,du, \qquad
  C_d = \frac{|S^{d-1}|}{|S^d|} = \frac{\Gamma(\tfrac{d+1}2)}{\sqrt\pi\,\Gamma(\tfrac d2)}, \qquad
  C_d\int_{\mathbb{R}}(1 + u^2)^{-(d+1)/2}du = 1 .$$
It is continuous on $(0,\infty)$, by dominated convergence, $k'$ having countably many
discontinuities. So: *if $F \in \mathcal{A}_{d+1}$, the polar profile of $F$ in dimension $d$ has a
continuous version, given by this formula from the profile in dimension $d + 1$.* Every datum in
dimension $d$ whose profile has a jump is then a witness, the step and, at $d = 1$, the $\Cin$ ray
among them, and the formula also gives $\bar k(0{+}) = k'(0{+})$, the dimension independence of
$c$. The script checks the normalization, the formula on the Matérn exponent for $d = 1, \dots, 4$,
and that the shadow of a step vanishes at the edge like $2\sqrt2\,C_d\sqrt{1 - r/\tau}$.

**Fix.** A matter of what the paper claims and how it is built, so not a prose fix. The claim that
every step is strict stands. What changes is its weight: the strictness has a ten-line proof by
the method of Theorem 3.20, and the paper's contribution in § 3.4 beyond it is the quantitative
family. Two ways to say so. *Smaller:* one paragraph after Theorem 3.20 stating that its proof,
with the projection $\mathbb{R}^{d+1} \to \mathbb{R}^d$, shows that the step datum of dimension
$d$ is outside $\mathcal{A}_{d+1}$, so that the strictness alone does not need the family; as
prose it is a claim that is neither machine-checked nor cited, and § 1.1 would have to list it.
*Larger:* a lemma (the shadow has a continuous profile) with Theorem 3.20 and the strictness as
corollaries, the referee's suggestion 5.

**Touches.** The prose of §§ 1, 3.4 and 4 (the second of the three "new" statements), and, for
either form with a statement, a new blueprint node and its Lean: `NoCinRay.lean` is the model,
with one projected coordinate instead of $d - 1$. Not priced.

---

## 10. The Student-t item of § 4.1 and Proposition 3.11(4) — CONFIRMED

**The paper.** Proposition 3.11(4), `03-isotropic.tex:616–628`, p. 20, is conditional: "*If*
$\mu^{\mathrm I}_{0,1}$ is the law of $T_1$ (that is, if the inverse-gamma laws are the delay
kernels of a time-causal family as above, whose existence [B, Prop. 4.5(3)] leaves as a
hypothesis)". After it, lines 644–647: "which by the same classification means that it is
self-decomposable. The time-causal paper takes that from the literature (its Prop. 8.17), and the
cone paper and this one leave it as a hypothesis." § 4.1, `04-conclusion.tex:169–170` and
189–195, p. 30, under "Open problems": "The paper leaves four questions. [...] Can clause (4) of
Proposition 3.11 be made unconditional? [...] The time-causal paper has this from a theorem of the
literature that it cites [...]. That theorem was not read for this paper and is not among its cited
facts".

**What the time-causal paper takes from Halgreen.** Version 1.1.0, proof of Proposition 8.17,
p. 38: "Self-decomposability of $T_1$ is a theorem of Halgreen ([12], for the generalized inverse
Gaussian laws, of which this is a limiting case); by Lemma 7.1 its exponent is of the form (7.1)
[...] and Theorem 7.3 makes the family admissible."

**Halgreen, at the page image** (`halgreen1979self`, held by the library). P. 13: the density of
$\mathrm{GIGD}(\lambda, \chi, \psi)$ is proportional to
$x^{\lambda-1}e^{-\frac12(\chi x^{-1} + \psi x)}$, and "In fact, any GIGD is a generalized
$\Gamma$-convolution", a class of self-decomposable laws on $[0,\infty)$. P. 14: the parameter
domain is "$\chi > 0$, $\psi \ge 0$ for $\lambda < 0$; $\chi > 0$, $\psi > 0$ for $\lambda = 0$;
$\chi \ge 0$, $\psi > 0$ for $\lambda > 0$", and "For $\lambda < 0$ and $\psi = 0$, where we get the
distribution of the inverse of a gamma variate, the statement was proved by Bondesson (1977) by
use of the same technique as is employed below." The proof (pp. 14–15) supposes "$\chi > 0$,
$\psi \ge 0$ and $-\lambda = \nu \ge 0$" and concludes "for $\nu > 0$ [...] $U$ fulfills the
conditions (3) [...] the GIGDs with $\lambda \le 0$ are generalized $\Gamma$-convolutions." The
law $T_1$ of the paper, of density $u^{-\vartheta-1}e^{-1/(2u)}/(2^\vartheta\Gamma(\vartheta))$, is
$\mathrm{GIGD}(-\vartheta, 1, 0)$: a member of Halgreen's parameter domain, on its boundary
$\psi = 0$, covered by his proof and credited by him to Bondesson. The same page states the
self-decomposability of the Student distribution as a consequence. Bondesson (1977) was not read.

**What settles it.** The referee is right. The question has an answer in print, which the paper
itself points to, so it is not open: it is a hypothesis that this paper does not discharge. The
two conditional sentences on p. 20 are accurate and stay. The time-causal paper's "a limiting
case" understates its source, where the law is a member.

**Fix.** Remove the item from § 4.1, change "four questions" to "three" (or to the number the
other shard leaves), and say the status once, after the proposition. Replace
`03-isotropic.tex:644–647`, from "The time-causal paper takes" to "as a hypothesis.", by

> That is in print. The inverse-gamma laws are the generalized inverse Gaussian laws with
> $\lambda < 0$ and $\psi = 0$, and these are generalized gamma convolutions, hence
> self-decomposable (\sscite{halgreen1979self}, pp.~13--15, where this member is credited to
> Bondesson). The time-causal paper cites this theorem (its Prop.~8.17). It is not among the cited
> facts of this paper, whose formal statement keeps the hypothesis, as the cone paper's does.

and, if a pointer is wanted in § 4.1, under "Not treated":

> Clause (4) of Proposition~\ref{prop:isotropic-bridge} is stated under a hypothesis that is a
> theorem of the literature (\S\ref{sec:isotropic-reduction}); it is not discharged here.

The citation needs `halgreen1979self` in the paper's bibliography and a reading note
(`READING-halgreen1979self.md`), which this record is not.

**Touches.** Prose (§ 4.1 and the paragraph after Proposition 3.11), the bibliography, a reading
note. Making the clause unconditional is a different change and the author's: a new cited fact
(Halgreen's theorem, with the classification of the time-causal paper, which the proofs of this
paper do not use), a shared statement, and the Lean hypothesis of the clause.

---

## 11. Everything else in § 3 of the review that asserts an error or a gap

Items not in the list above and not in the other shards.

| the review, § 3 | verdict | note |
|---|---|---|
| "For $c > d$, Fourier integrability [...] proves existence of that representative, not continuity of every density modified on a null set." | No defect asserted, and none found | Theorem 3.12(2) says "$\mu$ has a density of class $C^N$", clause (5) "has a density bounded near the origin", Corollary 2.8 "has a representative continuous on the whole line". Every statement is an existence statement. No change. |
| "I could not independently confirm the exact historical allegation about Wolfe's use of Kanter on pp. 77–78." | The paper is right | Confirmed at the page image: Wolfe p. 144, last line; Kanter p. 77, "We shall assume $q_X \equiv 0$, unless otherwise stated (no Gaussian part)"; Theorem 4.1, p. 78. See item 6(b). |
| Table of cited facts, C5: sound "subject to the measurability justification and source-page qualification". | See 6(a), 6(b) | |
| Table of cited facts, C6: "add uniqueness if the p. 54 argument is retained." | REFUTED as a remedy | The gap is real (item 5). The remedy is to cite or print the proved lemma, not to widen C6. |
| "C7's stated departure [...] is sound." | Agreed | "C7 assumes more than its source and concludes less" (`02-line-papers.tex:540–541`) is correct: its hypotheses are narrower. Unlike C6's sentence, this one is right. |
| "At $c = d$ [...] regular variation of index $-d$ alone would not suffice." | No defect | The paper's opening of § 3.3 (p. 22) uses the lower bound of Lemma A.3(1), not regular variation, for "integrable exactly when $c > d$". |

One remark of § 2 of the review falls between the shards and is mathematical. "It is not a
universal equivalence $q(s) \sim C\log(1/s)$ [...] the abstract's compressed description of a
spike whose rate is given with its constant should preserve it." **No error.** The abstract says
"a spike, whose rate is given with its constant" (`main.tex:165`). At $c < d$ that is
$R(d,c)\,s^{-d}\widehat\mu(e/s)$, and at $c = d$ it is $(2\pi)^{-d}I(s)$, an equivalence with
constant $1$ and a law-dependent comparison function, with a logarithmic lower bound. The body
(p. 22, "at $c = d$ it grows at least like $\log(1/|x|)$"; Proposition 3.15(2)) keeps the
distinction. Whether the abstract should spell it out is a wording choice.

**Found while verifying, not raised by the referee.**

- The paragraph of p. 54 has a third unprinted step, the negative definiteness of the
  Lévy–Khintchine forms (item 5, step (a)).
- Kanter prints that a centred Gaussian law is symmetric unimodal (Lemma 3.1, p. 70). Ledger A8
  and `READING-kanter1977unimodality.md` record this as "not found" (item 6(b)).
- $W_d$ is a Borel set, a countable union of compact sets, in every dimension of $K$ (item 6(a)).
  The paper, the ledger and the docstring claim less, and prove nothing.
- The time-causal paper, version 1.1.0, p. 38, calls the inverse-gamma law "a limiting case" of
  Halgreen's family; it is a member of his parameter domain (item 10). That paper is another
  repository's.
- The projection formula for polar profiles, and its corollary that a member of
  $\mathcal{A}_{d+1}$ has a continuous profile in dimension $d$ (item 9).

---

## Closing table

| item | verdict | the fix touches | proposed disposition |
|---|---|---|---|
| 1. "The power cannot be improved" (p. 26) | CONFIRMED | prose only | fix: restrict to $c \le d$, say what holds for $c > d$ (the blueprint annotation already does) |
| 2. The slopes of Figure 1 (pp. 21, 25) | CONFIRMED | prose only (a sentence, a caption) | fix |
| 3. "The stable kernels have $c = \infty$" (p. 30) | CONFIRMED | prose only | fix: index below $2$; the Gaussian has $c = 0$ and a Gaussian part |
| 4. C6 "assumes more than its source" (pp. 6, 13) | CONFIRMED | prose of § 1.1 and § 2.6; optionally one clause in the annotation of `thm:cited-A10`; ledger, fidelity card and Lean are right | fix |
| 5. The alternative derivation of $\mathcal{A}_\infty = \mathcal{S}$ (p. 54) | CONFIRMED, with a third missing step | the paper's pinned copy of one proof, or four blueprint nodes transcribed into Appendix A; no blueprint, ledger or Lean change | fix differently: name the three steps with their sources, or print the lemmas; do not add uniqueness to C6 |
| 6(a). $K \mapsto u_K$ Borel (p. 44) | CONFIRMED: asserted only; true, and $W_d$ is Borel | a shared proof of record, the text of ledger A8, the axiom's docstring | fix: the $\sigma$-compactness argument of this record |
| 6(b). The Gaussian case of C5 (pp. 6, 12) | PARTLY: the paper describes the printed proofs correctly; the extension is routine, by Kanter's Lemma 3.1 (p. 70) and Theorem 3.2 (p. 74); the direct repair is a complete proof | route A: prose of § 1.1 and § 2.6, the annotation of `thm:cited-A8`, ledger A8, a reading note; route B: also the proof of record, the statement of C5, Table 1 and the Lean | fix by route A; route B the author decides |
| 7. $k(x) = \varpi((x,\infty))$ (p. 10) | CONFIRMED | prose only (a restated statement with no blueprint node) | fix: "for almost every $x$", as the cone paper's Lemma 3.1(2) |
| 8. The constant of Proposition 3.17 (pp. 26, 40–41) | CONFIRMED: the formula is the proofs'; the statement displays no constant | as prose: prose only; in the statement: shared statements and the Lean | fix as prose, with the explicit $A_\beta$ of this record; the statement the author decides |
| 9. The short proof of strictness (review § 6) | CONFIRMED: correct, the method of Theorem 3.20, proves every strict inclusion and not clause (1) | the claims of §§ 1, 3.4 and 4; a new node and its Lean if it becomes a statement | the author decides |
| 10. The Student-t "open problem" (pp. 20, 30) | CONFIRMED | prose of § 4.1 and after Proposition 3.11, the bibliography, a reading note | fix: not an open problem; cite Halgreen as read; unconditional clause the author decides |
| 11. § 3, "every density" for $c > d$ | no defect | none | decline: every statement is of existence |
| 11. § 3, "add uniqueness to C6" | REFUTED as a remedy | none | decline: item 5's fix instead |
| 11. § 3, Wolfe's use of Kanter unconfirmed | the paper is right | none | decline: confirmed at the page |
| 11. § 2, the abstract's "rate with its constant" at $c = d$ | no error | the abstract, if reworded | the author decides |
