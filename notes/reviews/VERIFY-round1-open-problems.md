# Verification, review round 1 of the isotropic paper: the two open problems the referee says are settled

**Item.** Q-0423, on the branch `queue/q-0423`. The paper is frozen at `iso-review-1`; nothing in
`paper-iso/`, `blueprint/` or `Formalization/` was edited, and no Lean was built.

**What is verified.** The subsection "Two supposed open problems that the manuscript already
settles" of § 3 of `review-content-iso-review-1-GPT-6.1-Sol-Ultra.md`, and its required changes 6
and 7. Both concern § 4.1 of the paper (p. 30): the question whether $\sqrt d\,w_d$ has a limit, and
the question whether the slowly varying factor of Proposition 3.15 is given by the polar profile.

**Read for it.** The blueprint nodes `def:isotropic-origin-datum`, `lem:polar-decomposition`,
`lem:isotropic-exponent-log`, `prop:origin-rate-d`, `def:filtration-thresholds`,
`lem:threshold-monotone`, `lem:threshold-limit` with their proofs
(`blueprint/src/parts/03-isotropic.tex`); § 4.1 (`paper-iso/04-conclusion.tex`); the Lean statements
of `Formalization/AffineHemigroup/ThresholdLimit.lean` and the declaration lists of
`ExponentLog.lean`, `RegularVariation.lean` and `OriginRate.lean`; the reading notes
`READING-sato1978distribution.md`, `READING-sato1999levy-dimension-d.md` and
`READING-sato1999levy-prior-art.md`; two page images, read on 2026-10-12 for the constants:
Sato–Yamazato p. 277 (`library page sato1978distribution --printed 277 --format image`) and Sato
p. 411 (`library page sato1999levy --printed 411 --format image`).

**Scripts.** `verify-round1-scripts/a_critical_values.py`, `b_slowly_varying_factor.py`,
`c_critical_case.py`, each with its output beside it (`…-output.txt`); run with
`uv run --no-project --with mpmath python …`.

| | Claim of the review | Verdict |
|---|---|---|
| A | $\sqrt d\,w_d \to \sqrt\pi$ | **Correct.** The bounds of Lemma A.5 on $M_d$ and Stirling's formula give it. The paper's proof has Stirling's two-sided bounds, not the formula; six lines of dominated convergence on the integral already in that proof supply it. |
| B | $L(\rho) \sim \exp\bigl(-C_k - c\gamma_E - \tfrac c2[\psi(\tfrac12) - \psi(\tfrac d2)]\bigr)\,K(1/\rho)$ | **Correct as stated, with the referee's constant.** Derived below from the paper's definitions; it needs $k_d$ nonincreasing, $0 < c = k_d(0+) < \infty$ and $C_k < \infty$, which is the datum of Lemma A.3 and nothing more. It holds for every $d \ge 1$ and does not need $c \le d$. |

---

## A. The critical values: $\sqrt d\,w_d \to \sqrt\pi$. The referee is right.

### A.1 The objects

From `def:filtration-thresholds` and `lem:threshold-monotone`, for a real $d \ge 1$:
$$m = \frac{d+1}{2},\qquad h_d(z) = z^m\bigl(e^{-z} - 2^{-d/2}e^{-z/2}\bigr),\qquad
M_d = \sup_{z>0}h_d(z),\qquad w_d = \frac{\Gamma(m)}{2M_d}.$$
From the proof of `lem:threshold-limit` (Lemma A.5, pp. 51–52 of the review build), with
$\varphi(u) = u - \log(1+u)$ on $(-1,\infty)$:
$$\Gamma(m) = m^m e^{-m}\,I_m,\qquad I_m = \int_{-1}^{\infty}e^{-m\varphi(u)}\,du,\qquad
m^m e^{-m}(1-\varepsilon_d) \le M_d \le m^m e^{-m},\qquad
\varepsilon_d = 2^{-d/2}e^{m/2} = e^{1/4}\Bigl(\frac e4\Bigr)^{d/4}.$$
The proof also has four comparisons for $\varphi$: $\varphi(u) \ge u^2/2$ on $(-1,0]$;
$\varphi(u) \ge u^2/4$ on $[0,1]$; $\varphi(u) \ge u/4$ on $[1,\infty)$; $\varphi(u) \le u^2/2$ on
$[0,\infty)$. From them it gets $e^{-1/2} \le \sqrt m\,I_m \le K$ with
$K = \sqrt{\pi/2} + \sqrt\pi + 4 \approx 7.03$, and so
$e^{-1/2}/2 \le \sqrt m\,w_d \le K/(2(1-\varepsilon_d))$.

### A.2 The statement, as it would be printed

> **Lemma A.5, added clause.** Moreover $\sqrt m\,I_m \to \sqrt{2\pi}$ as $m \to \infty$ (Stirling's
> formula), and therefore
> $$\sqrt m\,w_d \to \sqrt{\pi/2}\qquad\text{and}\qquad \sqrt d\,w_d \to \sqrt\pi
> \qquad(d \to \infty),$$
> that is, $w_d \sim \sqrt{\pi/d}$. The limit is taken along the real parameter $d$, so in
> particular along the integers.

### A.3 The proof

*Stirling's formula.* Substitute $u = v/\sqrt m$ in $I_m$:
$$\sqrt m\,I_m = \int_{-\sqrt m}^{\infty}e^{-m\varphi(v/\sqrt m)}\,dv .$$
*Pointwise limit.* $\varphi(u) = \int_0^u \frac{s}{1+s}\,ds$, so
$\varphi(u) - \tfrac12u^2 = -\int_0^u\frac{s^2}{1+s}\,ds$ and
$|\varphi(u) - \tfrac12u^2| \le \frac{|u|^3}{3(1-|u|)}$ for $|u| < 1$. For a fixed real $v$ and
$m > v^2$ this gives
$|m\varphi(v/\sqrt m) - \tfrac12v^2| \le \frac{|v|^3}{3\sqrt m\,(1 - |v|/\sqrt m)} \to 0$, and
$v > -\sqrt m$ eventually. So the integrand, extended by $0$ to $v \le -\sqrt m$, tends to
$e^{-v^2/2}$ at every $v$.
*Domination.* Let $m \ge 1$. By the first three comparisons at $u = v/\sqrt m$:
$m\varphi \ge v^2/2$ for $-\sqrt m < v \le 0$; $m\varphi \ge v^2/4$ for $0 \le v \le \sqrt m$;
$m\varphi \ge \sqrt m\,v/4 \ge v/4$ for $v \ge \sqrt m$. So the integrand is at most
$g(v) := e^{-v^2/4} + e^{-|v|/4}$ for every $v$ and every $m \ge 1$, and $g$ is integrable.
By dominated convergence $\sqrt m\,I_m \to \int_{\mathbb R}e^{-v^2/2}\,dv = \sqrt{2\pi}$.

*The limit of $\sqrt m\,w_d$.* Since $w_d = m^me^{-m}I_m/(2M_d)$, the two bounds on $M_d$ give, for
every $d$ with $\varepsilon_d < 1$,
$$\frac{\sqrt m\,I_m}{2} \;\le\; \sqrt m\,w_d \;\le\; \frac{\sqrt m\,I_m}{2(1-\varepsilon_d)} .$$
As $d \to \infty$, $m \to \infty$ and $\varepsilon_d \to 0$, so both sides tend to
$\sqrt{2\pi}/2 = \sqrt{\pi/2}$. Finally $\sqrt d\,w_d = \sqrt{d/m}\,\sqrt m\,w_d$ and
$d/m = 2d/(d+1) \to 2$, so $\sqrt d\,w_d \to \sqrt2\,\sqrt{\pi/2} = \sqrt\pi$. $\qquad\blacksquare$

The proof reads the lemma's own substitution, its own comparisons and its own two bounds on $M_d$;
the only new ingredient is the pointwise limit. It cites nothing.

### A.4 Where the referee's sentence is exact and where it is short

The referee writes that the limit "follows immediately from the displayed bounds and Stirling's
formula". That is exact. What the paper prints, and what the Lean proves, is weaker than Stirling's
formula: the two-sided bound $e^{-1/2} \le \sqrt m\,I_m \le K$. With that bound alone the displayed
bounds give only $0.303 \le \liminf\sqrt m\,w_d$ and $\limsup\sqrt m\,w_d \le K/2 \approx 3.51$,
which is what the lemma states ("of exact order $d^{-1/2}$") and why § 4.1 asks the question. The
derivation does not fail anywhere; it needs the constant $\sqrt{2\pi}$, which A.3 supplies from the
material already in the proof.

The lemma's annotation says "**Not claimed**: sharp constants … and nothing here says that limit
exists". With the clause that sentence goes.

### A.5 Numbers (`a_critical_values.py`, 40 digits)

$M_d$ is computed from the first-order condition $m(1-q) = z(1 - q/2)$, $q = 2^{-d/2}e^{z/2}$, of the
proof of `lem:threshold-monotone`; the first-order function changes sign once on $(0, d\log 2)$ at
every $d$ of the table. The referee's values $w_1 \approx 12.606252$, $w_2 \approx 5.242276$,
$w_3 \approx 3.205618$ are reproduced. $\sqrt\pi = 1.772453851$.

| $d$ | $\varepsilon_d$ | $w_d$ | $\sqrt d\,w_d$ | $\sqrt d\,w_d/\sqrt\pi - 1$ | $d\,(\sqrt d\,w_d/\sqrt\pi - 1)$ | squeeze, lower | squeeze, upper |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1.166 | 12.60625198 | 12.60625198 | 6.112 | 6.112 | 1.35914 | — |
| 2 | 1.059 | 5.242275736 | 7.413697443 | 3.183 | 6.366 | 1.52874 | — |
| 3 | 0.9611 | 3.205617664 | 5.552292664 | 2.133 | 6.398 | 1.59978 | 41.08 |
| 5 | 0.7923 | 1.776978174 | 3.973443992 | 1.242 | 6.209 | 1.66343 | 8.007 |
| 10 | 0.4888 | 0.8553538379 | 2.704866333 | 0.5261 | 5.261 | 1.71574 | 3.357 |
| 20 | 0.1861 | 0.4597766494 | 2.056183685 | 0.1601 | 3.202 | 1.74352 | 2.142 |
| 30 | 0.07085 | 0.3415181813 | 1.870572117 | 0.05536 | 1.661 | 1.75303 | 1.887 |
| 50 | 0.01027 | 0.2515082248 | 1.778431713 | 0.003373 | 0.169 | 1.76074 | 1.77900 |
| 60 | 0.003909 | 0.2284404051 | 1.769491769 | −0.001671 | −0.100 | 1.76267 | 1.76959 |
| 100 | 8.2e−5 | 0.1766715193 | 1.766715193 | −0.003238 | −0.3238 | 1.766570 | 1.766715 |
| 200 | 5.3e−9 | 0.125122963 | 1.769505912 | −0.001663 | −0.3326 | 1.7695059 | 1.7695059 |
| 500 | 1.4e−21 | 0.07921374559 | 1.771273199 | −0.0006661 | −0.3331 | 1.7712732 | 1.7712732 |
| 1000 | 1.5e−42 | 0.05603123664 | 1.771863279 | −0.0003332 | −0.3332 | 1.7718633 | 1.7718633 |
| 2000 | 1.7e−84 | 0.03962666881 | 1.772158503 | −0.0001666 | −0.3333 | 1.7721585 | 1.7721585 |
| 5000 | 2.5e−210 | 0.0250646118 | 1.772335697 | −0.00006666 | −0.3333 | 1.7723357 | 1.7723357 |

"Squeeze" is the pair $\sqrt{d/m}\,\sqrt m\,I_m/2$ and the same over $1 - \varepsilon_d$, the two
sides of the display of A.3 multiplied by $\sqrt{d/m}$; $\sqrt d\,w_d$ lies between them at every
row. Three observations, none of which the clause claims.

- The convergence is slow at small $d$, because $\varepsilon_d$ decays like $(e/4)^{d/4}$: at
  $d = 20$ the product is still 16 % above its limit. A table to $d = 12$ or $d = 20$ does not show
  a limit, which is consistent with the question having been left open on numerical evidence.
- $\sqrt d\,w_d$ is not monotone. It decreases from $12.6$, passes below $\sqrt\pi$ between
  $d = 55$ and $d = 56$, has its least value over the integers at $d = 81$ ($1.76610$), and
  returns to $\sqrt\pi$ from below.
- The last column tends to $-\tfrac13$: $\sqrt d\,w_d = \sqrt\pi\,(1 - \tfrac{1}{3d} + O(d^{-2}))$
  up to a term of order $\varepsilon_d$, from $\Gamma(m) = \sqrt{2\pi}\,m^{m-1/2}e^{-m}(1 +
  \tfrac{1}{12m} + \dots)$ and $\sqrt{d/m} = \sqrt2\,(1 - \tfrac{1}{4m} + \dots)$. In the
  normalisation by $m$ the correction is the Stirling one alone:
  $\sqrt m\,w_d/\sqrt{\pi/2} = 1.0001665$ at $d = 1000$, and $1/(12m) = 0.0001665$.

### A.6 The Lean, and what the statement costs

**What the Lean has** (`ThresholdLimit.lean`, 506 lines, Lean core only).
`threshold_limit_bounds (d : ℝ) (hd : 1 ≤ d)` states the formula for $\varepsilon_d$, the lower bound
$e^{-1/2}/(2\sqrt m) \le w_d$, and the upper bound $w_d \le K/(2(1-\varepsilon_d)\sqrt m)$ under
$\varepsilon_d < 1$. `threshold_limit` states that $\varepsilon_d$ is strictly decreasing and tends to
$0$, that $w_d \to 0$, the two bounds on $\sqrt m\,w_d$, and that every $w > 0$ exceeds $w_d$ from
some $D$ on. Neither states a limit of $\sqrt m\,w_d$, and neither implies one: the constants are
$e^{-1/2}/2$ and $K$. So the limit can be *typed* today,
`Tendsto (fun d : ℝ => Real.sqrt d * threshold d) atTop (𝓝 (Real.sqrt π))`, since
`threshold : ℝ → ℝ` exists; it cannot be *proved* from the two declarations of the tag.

What carries over unchanged: the squeeze of $M_d$ (`thresholdSup_le`, `le_thresholdSup`), which is
exact and is all the limit needs of $M_d$; the three pointwise dominations
`gamma_integrand_le_one`, `gamma_integrand_le_two`, `gamma_integrand_le_three`, which are the
dominating function of A.3 in the variable $t = m(1+u)$; `gamma_integrand_eq`; the shifted Gaussian
integrals. What is missing is Stirling's formula for the real Gamma function. Mathlib at the pinned
revision (v4.31.0) has it for factorials only (`Stirling.tendsto_stirlingSeq_sqrt_pi`,
`Stirling.factorial_isEquivalent_stirling`); it has the log-convexity of $\Gamma$
(`Real.convexOn_log_Gamma`) and the duplication formula, so the half-integers could be reached
from the factorials, but the lemma is stated for a real $d$ and A.3 is the shorter route.

**Options.**

1. **A clause of Lemma A.5 at the blueprint, with a Lean proof (recommended).** Blueprint: the clause
   of A.2 in `lem:threshold-limit`, the paragraph of A.3 appended to its proof, the title and the
   "Not claimed" sentence of the annotation revised. Lean, priced beside the type above: (i) the
   limit $\sqrt m\,\Gamma(m)/(m^me^{-m}) \to \sqrt{2\pi}$ along real $m$, by dominated convergence
   along the filter `atTop` on the existing integrand, with one new elementary inequality for the
   pointwise limit (an upper bound $\log(1+u) \le u - u^2/2 + u^3/3$ beside the four the file has)
   and one change of variables: 200 to 300 lines; (ii) the squeeze and $\sqrt{d/m} \to \sqrt2$: 60
   to 100 lines. About 300 to 400 lines in `ThresholdLimit.lean`, Lean core only, no ledger entry,
   no interface. Paper: the clause and the paragraph mirrored into Appendix A; the paragraph "The
   critical values" of § 4.1 removed and "four questions" made three; the two sentences "of exact
   order $d^{-1/2}$" (§ 1, line 365 of `01-introduction.tex`, and § 3.4, line 1254 of
   `03-isotropic.tex`) may then say $w_d \sim \sqrt{\pi/d}$. The bounds $e^{-1/2}/2$ and $K$ stay:
   they hold at every $d$, which the limit does not give.
2. **A remark after Lemma A.5**, with the proof of A.3 printed and not machine-checked. No Lean. It
   answers the referee at the cost of one statement outside the checked part, which § 1.1 of the
   paper would have to name.
3. **Citing Stirling's formula** instead of proving it. A new cited fact for six lines of proof;
   not recommended.

A widening of a lemma's statement is the author's decision; option 1 changes what Lemma A.5 claims
and removes a question from § 4.1.

---

## B. The slowly varying factor: the referee's formula is correct as stated

### B.1 The conventions, each checked against the source file

- **The datum** (`def:isotropic-origin-datum`). $(0,k_d)$ with $k_d : (0,\infty) \to [0,\infty)$
  nonincreasing, $\int_0^1 k_d(r)\,r\,dr < \infty$, $\int_1^\infty k_d(r)\,dr/r < \infty$,
  $c := k_d(0+)$. The Lévy measure has the radial density $k_d(r)/(|S^{d-1}|r^d)$, so by
  `eq:polar-decomposition` the profile is integrated against $dr/r$ and the sphere measure is
  **normalised**: with $\bar\sigma := \sigma_{d-1}/|S^{d-1}|$,
  $$F_d(\xi) = \int_{S^{d-1}}\varphi(\langle\xi,\eta\rangle)\,\bar\sigma(d\eta),\qquad
  \varphi(s) = \int_0^\infty(1-\cos rs)\,k_d(r)\,\frac{dr}{r} .$$
  This is the first display of the proof of `lem:isotropic-exponent-log` (Lemma A.3, p. 38), and
  $\varphi$ is the referee's "one-variable cosine exponent". At $d = 1$, $S^0 = \{\pm1\}$,
  $|S^0| = 2$, $F_1 = \varphi$, and $k_1$ is the **folded** profile $k(r) + k(-r)$ of Sato's
  notation.
- **$C_k = \int_1^\infty k_d(r)\,dr/r$**, as in Lemma A.3.
- **$L$.** $\widehat\mu(\rho e) = e^{-F_d(\rho e)} = \rho^{-c}L(\rho)$ (§ 4.1; the "What it is worth"
  of `prop:origin-rate-d`).
- **$K$.** $K(x) = \exp\int_x^1(c - k_d(u))\,du/u$ for $0 < x \le 1$: lower limit $x$, upper limit
  $1$, integrand $c - k_d \ge 0$. It is evaluated at $x = 1/\rho$ and enters $F_d$ with a minus
  sign. With $k_d$ the folded profile this is Sato's (53.25) and Sato–Yamazato's (1.9), both
  compared at the page image.
- **The brief's test profile** $k_d = c(1 + 1/\log(e/r))\mathbf 1_{(0,1)}$ is increasing and exceeds
  $c$, so it is not a datum. The nonincreasing profile with a logarithmic approach to $c$,
  $k_d = c(1 - 1/\log(e/r))\mathbf 1_{(0,1)}$, is used below.

### B.2 The statement, as it would be printed

Write $\gamma_E$ for Euler's constant and $\psi = \Gamma'/\Gamma$ for the digamma function.

> **Proposition (the transform at infinity through the polar profile).** Let $d \ge 1$, let
> $(0,k_d)$ be an isotropic origin datum in dimension $d$ with Gaussian coefficient $0$ and
> $c := k_d(0+) \in (0,\infty)$, let $F_d$ be its exponent, $C_k := \int_1^\infty k_d(r)\,dr/r$, and
> $e$ a unit vector. Put
> $$K(x) := \exp\Bigl[\int_x^1\bigl(c - k_d(u)\bigr)\frac{du}{u}\Bigr]\quad(0 < x \le 1),\qquad
> \varkappa_d := \gamma_E + \tfrac12\bigl[\psi(\tfrac12) - \psi(\tfrac d2)\bigr],$$
> $$A(d,c,C_k) := \exp\bigl(-C_k - c\,\varkappa_d\bigr)
>   = 2^{c}\exp\Bigl(-C_k - \tfrac c2\bigl(\gamma_E - \psi(\tfrac d2)\bigr)\Bigr) .$$
> 1. *(The factor.)* $K$ is nonincreasing on $(0,1]$, $K \ge 1 = K(1)$, and $K(ax)/K(x) \to 1$ as
>    $x \downarrow 0$ for every $a > 0$. It is bounded if and only if
>    $\int_0^1(c - k_d(u))\,du/u < \infty$.
> 2. *(The transform.)* As $\rho \to \infty$,
>    $$F_d(\rho e) = c\log\rho - \log K(1/\rho) + C_k + c\,\varkappa_d + o(1),
>    \qquad\text{that is}\qquad
>    \frac{e^{-F_d(\rho e)}}{A(d,c,C_k)\,\rho^{-c}\,K(1/\rho)} \to 1 .$$
>    Moreover, for every $\rho \ge 1$,
>    $$-c\bigl(3 + \tfrac12[\psi(\tfrac d2) - \psi(\tfrac12)]\bigr)
>      \;\le\; F_d(\rho e) - \bigl(c\log\rho - \log K(1/\rho) + C_k\bigr) \;\le\; \tfrac{13}{4}\,c .$$
> 3. *(The rate, below the threshold.)* Let $c < d$, let $\mu$ be the datum's law and $q$ a
>    nonincreasing function on $(0,\infty)$ with $\mu = q(|x|)\,dx$, as in
>    Proposition 3.15. Then, as $s \downarrow 0$,
>    $$\frac{q(s)}{Q(d,c,C_k)\,s^{c-d}\,K(s)} \to 1
>    \qquad\text{and}\qquad
>    \frac{\mu(\{|x| \le s\})}{Q(d,c,C_k)\,|S^{d-1}|\,c^{-1}\,s^{c}\,K(s)} \to 1,$$
>    $$Q(d,c,C_k) := R(d,c)\,A(d,c,C_k)
>      = \frac{\Gamma\bigl(\tfrac{d-c}{2}\bigr)}{\pi^{d/2}\,\Gamma\bigl(\tfrac c2\bigr)}\,
>        \exp\Bigl(-C_k - \tfrac c2\bigl(\gamma_E - \psi(\tfrac d2)\bigr)\Bigr) .$$
> 4. *(The rate, at the threshold.)* Let $c = d$ and $\mathcal L(s) := \int_s^1 K(y)\,dy/y$. Then
>    $$\frac{q(s)}{B(d,C_k)\,\mathcal L(s)} \to 1,\qquad
>    B(d,C_k) := (2\pi)^{-d}\,|S^{d-1}|\,A(d,d,C_k)
>      = \frac{2}{\pi^{d/2}\,\Gamma(\tfrac d2)}\exp\Bigl(-C_k - \tfrac d2\bigl(\gamma_E - \psi(\tfrac d2)\bigr)\Bigr).$$

In the notation of § 4.1, clause 2 is $L(\rho) \sim A(d,c,C_k)\,K(1/\rho)$, and
$A(d,c,C_k) = \exp\bigl(-C_k - c\gamma_E - \tfrac c2[\psi(\tfrac12) - \psi(\tfrac d2)]\bigr)$ is the
referee's constant, letter for letter. The second form uses $\psi(\tfrac12) = -\gamma_E - 2\log 2$.
So the answer to the question of § 4.1 is yes: $L$ is given in $\mathbb R^d$ by the expression of
the line in the polar profile $k_d$, up to a constant that depends on the dimension through
$\psi(d/2)$ alone. Clause 2 holds for every finite $c > 0$; only clauses 3 and 4 use $c \le d$.

Values: $\tfrac12[\psi(\tfrac12) - \psi(\tfrac d2)]$ is $0$, $-\log 2$, $-1$, $-\log 2 - \tfrac12$,
$-\tfrac43$ at $d = 1,\dots,5$, and decreases by $1/d$ from $d$ to $d + 2$. So
$\varkappa_1 = \gamma_E$, $\varkappa_2 = \gamma_E - \log 2$, $\varkappa_3 = \gamma_E - 1$.

### B.3 The proof

Throughout $k := k_d$. Three facts are in the proof of Lemma A.3: $k \le c$ on $(0,\infty)$;
$k(r) \to 0$ as $r \to \infty$; and, with $\operatorname{Cin}(X) := \int_0^X(1-\cos u)\,du/u$,
$$\log X - 3 \le \operatorname{Cin}(X)\ (X > 0),\qquad \operatorname{Cin}(X) \le \log X + \tfrac{13}{4}\ (X \ge 1),
\qquad 0 \le \operatorname{Cin}(X) \le \tfrac14\ (0 \le X \le 1)$$
(`eq:cin-log` and the line before it). Write $\log^+ X := \max\{\log X, 0\}$ and
$$G(X) := \operatorname{Cin}(X) - \log^+X \quad (X \ge 0),\qquad
I(s) := \int_{1/s}^{\infty}k(r)\,\frac{dr}{r}\quad(s > 0).$$
So $-3 \le G \le \tfrac{13}{4}$ on $[0,\infty)$. For $X \ge 1$,
$G(X) = \operatorname{Cin}(1) - \int_1^X\cos u\,du/u$, and the integral converges as $X \to \infty$
(integrate by parts as in the proof of Lemma A.3: $\int_1^X u^{-1}\cos u\,du = [u^{-1}\sin u]_1^X +
\int_1^Xu^{-2}\sin u\,du$, and the last integrand is absolutely integrable). So
$g := \lim_{X\to\infty}G(X)$ exists. And for $s \ge 1$,
$$I(s) = \int_{1/s}^1 k(r)\frac{dr}{r} + C_k = c\log s - \log K(1/s) + C_k . \tag{B.1}$$

**Step 0: clause 1.** For $0 < x \le 1$ the integrand $(c - k(u))/u$ lies in $[0, c/u]$, so $K(x)$
is finite, $K(1) = 1$, $K \ge 1$ and $K$ is nonincreasing. For $a > 0$,
$|\log K(ax) - \log K(x)| = \bigl|\int_{ax}^{x}(c - k(u))\,du/u\bigr| \le
\bigl(c - k(\max\{a,1\}x)\bigr)|\log a| \to 0$ as $x \downarrow 0$, because $k(0+) = c$. By monotone
convergence $K(0+) = \exp\int_0^1(c-k(u))\,du/u \in [1,\infty]$.

**Step 1: the layer-cake form of $\varphi$.** For $0 < y < c$ put
$\tau(y) := \sup\{r > 0 : k(r) > y\}$. The set is nonempty because $\sup k = c > y$, and bounded
because $k \to 0$ at infinity; so $0 < \tau(y) < \infty$. As $k$ is nonincreasing, the set is
$(0,\tau(y))$ or $(0,\tau(y)]$. Since $0 \le k \le c$, $k(r) = \int_0^c\mathbf 1\{y < k(r)\}\,dy$ for
every $r > 0$. For a measurable $w \ge 0$ on $(0,\infty)$, Tonelli's theorem gives
$$\int_0^\infty w(r)\,k(r)\,dr = \int_0^c\Bigl(\int_0^{\tau(y)}w(r)\,dr\Bigr)dy .$$
With $w(r) = (1-\cos rs)/r$ and with $w(r) = \mathbf 1\{r > 1/s\}/r$, for $s > 0$:
$$\varphi(s) = \int_0^c\operatorname{Cin}\bigl(s\,\tau(y)\bigr)\,dy,\qquad
I(s) = \int_0^c\log^+\bigl(s\,\tau(y)\bigr)\,dy .$$
Both are finite ($I(s) \le c\log^+s + C_k$), so
$$\varphi(s) = I(s) + \int_0^c G\bigl(s\,\tau(y)\bigr)\,dy \qquad (s > 0). \tag{B.2}$$
This is an identity, with no remainder. The monotonicity of $k$ is used here and nowhere else.

**Step 2: $g = \gamma_E$.** Take $\gamma_E = -\Gamma'(1) = -\int_0^\infty e^{-v}\log v\,dv$. For
$0 < \varepsilon < 1$ put $J(\varepsilon) := \int_0^\infty(1-\cos u)\,e^{-\varepsilon u}\,du/u$.
(a) $(1-\cos u)/u = \int_0^1\sin(tu)\,dt$ and
$\int_0^\infty\sin(tu)e^{-\varepsilon u}du = t/(\varepsilon^2+t^2)$; the integrand
$|\sin(tu)|e^{-\varepsilon u}$ is integrable on $(0,1)\times(0,\infty)$, so by Fubini
$J(\varepsilon) = \int_0^1\frac{t\,dt}{\varepsilon^2+t^2} = \tfrac12\log(1+\varepsilon^{-2})
 = \log(1/\varepsilon) + \tfrac12\log(1+\varepsilon^2)$.
(b) $e^{-\varepsilon u} = \int_u^\infty\varepsilon e^{-\varepsilon x}dx$ and Tonelli give
$J(\varepsilon) = \int_0^\infty\varepsilon e^{-\varepsilon x}\operatorname{Cin}(x)\,dx
 = \int_0^\infty e^{-v}\operatorname{Cin}(v/\varepsilon)\,dv$.
(c) $\operatorname{Cin}(v/\varepsilon) - \log(1/\varepsilon) = G(v/\varepsilon) +
\bigl[\log^+(v/\varepsilon) - \log(1/\varepsilon)\bigr]$. The bracket equals $\log v$ when
$v \ge \varepsilon$ and $\log\varepsilon \in (\log v, 0)$ when $v < \varepsilon$; so it is bounded by
$|\log v|$ and tends to $\log v$ as $\varepsilon \downarrow 0$. As $|G| \le \tfrac{13}{4}$ and
$G(v/\varepsilon) \to g$, dominated convergence with $e^{-v}(\tfrac{13}{4} + |\log v|)$ gives
$J(\varepsilon) - \log(1/\varepsilon) \to g + \int_0^\infty e^{-v}\log v\,dv = g - \gamma_E$.
(d) By (a) the left side is $\tfrac12\log(1+\varepsilon^2) \to 0$. Hence $g = \gamma_E$. (This is
the classical $\operatorname{Cin}(X) = \gamma_E + \log X - \operatorname{Ci}(X)$,
$\operatorname{Ci}(X) = -\int_X^\infty\cos u\,du/u \to 0$, proved rather than cited.)

**Step 3: the mean of $\log|\eta_1|$ over the sphere.** Let $\eta$ be distributed by $\bar\sigma$
and $\eta_1 := \langle e,\eta\rangle$. Claim: $\log|\eta_1|$ is $\bar\sigma$-integrable and
$$\lambda_d := \int_{S^{d-1}}\log|\langle e,\eta\rangle|\,\bar\sigma(d\eta)
 = \tfrac12\bigl[\psi(\tfrac12) - \psi(\tfrac d2)\bigr] \le 0 .$$
Let $Z$ be a standard Gaussian vector of $\mathbb R^d$. In polar coordinates $Z = |Z|\,\eta$ with
$\eta$ distributed by $\bar\sigma$ and independent of $|Z|$, and
$\log|\langle e,Z\rangle| = \log|Z| + \log|\eta_1|$. $|Z|^2/2$ has the gamma law of shape $d/2$ and
$\langle e,Z\rangle^2/2$ the gamma law of shape $\tfrac12$; for the gamma law of shape $a$,
$\int_0^\infty\log t\;t^{a-1}e^{-t}dt/\Gamma(a) = \Gamma'(a)/\Gamma(a) = \psi(a)$, the integral
converging absolutely. So $\log|Z|$ and $\log|\langle e,Z\rangle|$ are integrable, hence so is
their difference $\log|\eta_1|$, and
$\mathbb E\log|\eta_1| = \tfrac12[\log 2 + \psi(\tfrac12)] - \tfrac12[\log 2 + \psi(\tfrac d2)]$.
It is $\le 0$ because $|\eta_1| \le 1$. At $d = 1$, $|\eta_1| = 1$ and $\lambda_1 = 0$.

**Step 4: the sphere average; clause 2.** As $\varphi$ is even, $F_d(\rho e) = \int\varphi(\rho|\eta_1|)\,
\bar\sigma(d\eta)$, and $\eta_1 \ne 0$ off a $\bar\sigma$-null set (a great subsphere for $d \ge 2$,
empty for $d = 1$). By (B.2),
$$F_d(\rho e) - I(\rho) = \int\bigl[I(\rho|\eta_1|) - I(\rho)\bigr]\bar\sigma(d\eta)
  + \int\!\!\int_0^c G\bigl(\rho|\eta_1|\tau(y)\bigr)\,dy\,\bar\sigma(d\eta) . \tag{B.3}$$
*First term.* For $0 < t \le 1$ and $\rho > 0$,
$I(\rho) - I(\rho t) = \int_{1/\rho}^{1/(\rho t)}k(r)\,dr/r$ lies between
$k(1/(\rho t))\log(1/t)$ and $c\log(1/t)$. So $I(\rho t) - I(\rho) \to c\log t$ as
$\rho \to \infty$, because $k(0+) = c$, and $|I(\rho t) - I(\rho)| \le c|\log t|$ for every
$\rho > 0$. By Step 3 the bound is integrable at $t = |\eta_1|$, and dominated convergence gives
that the first term tends to $c\lambda_d$; for every $\rho > 0$ it lies in $[c\lambda_d, 0]$.
*Second term.* The integrand lies in $[-3, \tfrac{13}{4}]$, and for every $y \in (0,c)$ and every
$\eta$ with $\eta_1 \ne 0$, $\rho|\eta_1|\tau(y) \to \infty$, so the integrand tends to
$g = \gamma_E$ (Step 2). By bounded convergence on $S^{d-1}\times(0,c)$ the second term tends to
$c\gamma_E$; for every $\rho > 0$ it lies in $[-3c, \tfrac{13}{4}c]$.
Hence $F_d(\rho e) - I(\rho) \to c(\gamma_E + \lambda_d) = c\varkappa_d$, and
$c\lambda_d - 3c \le F_d(\rho e) - I(\rho) \le \tfrac{13}{4}c$ for every $\rho > 0$. With (B.1) for
$\rho \ge 1$ this is clause 2. The last equivalence of clause 1 for $L$ follows: by the two-sided
bound, $L(\rho) = \rho^{c}e^{-F_d(\rho e)}$ lies between two positive multiples of $K(1/\rho)$ on
$[1,\infty)$, so $L$ is bounded exactly when $K$ is.

**Step 5: clause 3.** Let $c < d$. Proposition 3.15(1) gives
$q(s)/\bigl(R(d,c)\,s^{-d}\,\widehat\mu(e/s)\bigr) \to 1$ and
$\mu(\{|x| \le s\})/\bigl(R(d,c)|S^{d-1}|c^{-1}\widehat\mu(e/s)\bigr) \to 1$ as $s \downarrow 0$.
Clause 2 at $\rho = 1/s$ gives $\widehat\mu(e/s)/\bigl(A\,s^{c}K(s)\bigr) \to 1$. Multiply. The
closed form of $Q$ is $R(d,c) = \Gamma(\tfrac{d-c}{2})/(2^c\pi^{d/2}\Gamma(\tfrac c2))$ times the
second form of $A$.

**Step 6: clause 4.** Let $c = d$ and $P(R) := \int_0^R e^{-F_d(\rho e)}\rho^{d-1}d\rho$, so that
$I_{3.15}(s) := \int_{\{|\xi| \le 1/s\}}\widehat\mu = |S^{d-1}|P(1/s)$ in the notation of
Proposition 3.15(2), which gives $q(s)/\bigl((2\pi)^{-d}|S^{d-1}|P(1/s)\bigr) \to 1$. By clause 2,
$e^{-F_d(\rho e)}\rho^{d-1} = L(\rho)/\rho$ with $L(\rho)/(A\,K(1/\rho)) \to 1$. As $K \ge 1$,
$\int_1^R K(1/\rho)\,d\rho/\rho \ge \log R \to \infty$; for positive functions $f \sim h$ at
infinity with $\int^\infty h = \infty$ one has $\int_1^Rf \sim \int_1^Rh$, and the bounded
contribution of $(0,1)$ does not matter. So
$P(R) \sim A\int_1^RK(1/\rho)\,d\rho/\rho = A\int_{1/R}^1K(y)\,dy/y = A\,\mathcal L(1/R)$. With
$|S^{d-1}| = 2\pi^{d/2}/\Gamma(\tfrac d2)$,
$(2\pi)^{-d}|S^{d-1}|\cdot 2^{d} = 2/(\pi^{d/2}\Gamma(\tfrac d2))$, which gives $B$. $\qquad\blacksquare$

*What the proof uses.* The definition of the datum (monotone $k_d$, finite positive $c$, $C_k <
\infty$), the three inequalities for $\operatorname{Cin}$ of Lemma A.3, Tonelli, dominated
convergence, the Gaussian in polar coordinates, and $\Gamma'$. It cites nothing for clauses 1 and
2. Clauses 3 and 4 read Proposition 3.15 and inherit its cited facts (C7 for the limits; C5, C2 and
C3 for the existence of $q$). Lemma A.3(2) is not used; it follows from clause 2 and clause 1.

### B.4 The referee's route, and the points the brief asked to check

The referee's argument has two steps, and both are right.

1. *One variable:* $\varphi(\rho) = c\log\rho - \log K(1/\rho) + c\gamma_E + C_k + o(1)$. This is
   (B.2) with (B.1) and Step 2, at $d = 1$. The usual derivation splits $\varphi$ at $r = 1/\rho$
   and $r = 1$:
   $\varphi(\rho) = \int_0^1(1-\cos u)k(u/\rho)\,du/u + I(\rho) - \int_1^\infty\cos u\;k(u/\rho)\,du/u$;
   the first integral tends to $c\operatorname{Cin}(1)$ by dominated convergence, and the last to
   $c\int_1^\infty\cos u\,du/u = -c\operatorname{Ci}(1)$. The last limit is of a conditionally
   convergent integral and is **not** a dominated convergence: it needs the monotonicity of $k$
   (the second mean value theorem, which bounds $\bigl|\int_N^\infty\cos u\;k(u/\rho)\,du/u\bigr|$
   by $2c/N$ uniformly in $\rho$; or the signed-measure argument of Sato's proof of Lemma 53.9,
   p. 411). The layer-cake identity (B.2) replaces that step by Tonelli and bounded convergence,
   which is why B.3 takes it.
2. *The sphere:* $F_d(\rho e) - \varphi(\rho) = \int[\varphi(\rho|\eta_1|) - \varphi(\rho)]\,d\bar\sigma
   \to c\lambda_d$, by the pointwise limit $\varphi(\rho t) - \varphi(\rho) \to c\log t$ and the
   bound $|\varphi(\rho t) - \varphi(\rho)| \le 2c|\log t|$, both proved in Lemma A.3 for every
   $\rho > 0$ and $t > 0$ ("Clause (2), one variable"), and the integrability of $\log|\eta_1|$.
   This is a correct dominated convergence, and it needs no separate treatment of the set
   $\rho|\eta_1| < 1$: the bound holds at every $\rho$.

So, item by item:

| Point | Finding |
|---|---|
| Normalisation of $k_d$ against the sphere measure | As in B.1: normalised sphere average of $\varphi$, profile against $dr/r$. Checked numerically against the definition (B.6, part 1 and part 3(a)). |
| The definition of $\varphi$ | The first display of the proof of Lemma A.3. |
| The sphere average of $\log|\eta_1|$ | $\tfrac12[\psi(\tfrac12) - \psi(\tfrac d2)]$, Step 3; numerically for $d = 2,\dots,7$ (B.6, part 0). |
| Sign and limits of the integral in $K$ | $K(x) = \exp\int_x^1(c - k_d)\,du/u$ at $x = 1/\rho$, entering $F_d$ as $-\log K(1/\rho)$; so $L \propto K(1/\rho) \ge 1$, nondecreasing in $\rho$. |
| Whether the $o(1)$ needs more than $k_d(0+) = c$ and integrability at infinity | It needs the monotonicity of $k_d$ as well, which the datum has by definition. Nothing else: no rate of approach to $c$, no regularity. $0 < c < \infty$. |
| Whether dominated convergence on the sphere is justified by the bound quoted | Yes (point 2 above). |

The paper's own records already had the formula: `PRIOR-ART-origin-threshold-reading.md` § 6.4
sketches it with $C_d = c(\gamma_E + \mathbb E\log|\eta_1|) + C_k$, and
`REFEREE-rate-at-the-centre.md` § 5 found the sketch "right in substance" and short of two
justifications, the conditional convergence and a domination on the sphere. B.3 supplies both.
The value of $\mathbb E\log|\eta_1|$ in terms of $\psi$ is the external referee's.

### B.5 The line, $d = 1$: the constants agree with Sato–Yamazato and with Sato

Read at the page images on 2026-10-12.

- **Sato–Yamazato p. 277.** (1.8): $c = \exp\bigl\{\lambda\int_0^1(e^{-u}-1)u^{-1}du +
  \lambda\int_1^\infty e^{-u}u^{-1}du - \int_1^\infty(k(u)-k(-u))u^{-1}du\bigr\}$. (1.9):
  $K(x) = \exp\int_{|x|}^1(\lambda - k(u) + k(-u))u^{-1}du$. (1.10): $L(x) = \int_{|x|}^1K(u)u^{-1}du$.
  Their $k$ is negative on the negative half-line (`READING-sato1978distribution.md` § 1), so
  $k(u) - k(-u)$, $u > 0$, is the folded profile.
- **Sato p. 411.** (53.25): $K(x) = \exp\bigl[\int_{|x|}^1(c - k(y) - k(-y))\,dy/y\bigr]$. (53.27):
  $\kappa = \exp\bigl[c\int_0^1(e^{-x}-1)\,dx/x + c\int_1^\infty e^{-x}dx/x -
  \int_1^\infty(k(x)+k(-x))\,dx/x\bigr]$. Here $k \ge 0$ on both sides, and $k(y) + k(-y)$ is the
  folded profile.

In both, the bracket is $-\lambda\gamma_E - C_k$ with $C_k$ formed from the folded profile, since
$\int_0^1(1-e^{-u})\,du/u - \int_1^\infty e^{-u}du/u = \gamma_E$. So
$$c_{\mathrm{SY}} = \kappa_{\mathrm{Sato}} = e^{-c\gamma_E - C_k} = A(1,c,C_k),$$
because $\varkappa_1 = \gamma_E$, and $K$ is the $K$ of B.2 at $k_1$ = the folded profile. Then:

- Clause 2 at $d = 1$ is Sato–Yamazato's Lemma 5.1, (5.9), in the symmetric case
  ($\mu = \lambda_+ - \lambda_- = 0$): $\varphi(x^{-1}s)\,x^{-\lambda}K(x)^{-1} \to c|s|^{-\lambda}$;
  it is Sato's (53.33) with $c' = 0$.
- Clause 3 at $d = 1$: $Q(1,c,C_k) = R(1,c)\,e^{-c\gamma_E - C_k}$ and
  $R(1,c) = 1/(2\Gamma(c)\cos(c\pi/2)) = \sin(c\pi/2)/(\Gamma(c)\sin c\pi)$, which is the constant
  $c_{\mathrm{SY}}\sin(\lambda_+\pi)/(\Gamma(\lambda)\sin\lambda\pi)$ of Theorem 1.7(i), (1.12), at
  $N = 0$ and $\lambda_+ = \lambda/2$, and that of Sato's (53.28) at $k(0+) = c/2$.
- Clause 4 at $d = 1$: $B(1,C_k) = e^{-\gamma_E - C_k}/\pi$, the constant
  $(c_{\mathrm{SY}}/\pi)\cos 0$ of (1.14) and $(\kappa/\pi)\cos(c'\pi/2)$ of (53.30) at $c' = 0$,
  with the same $\mathcal L$.

The convention that matters is the one the paper already fixes: at $d = 1$ the polar profile is
the folded profile, and the sources' $K$, $c$ and $\kappa$ are written in the folded profile too.
Nothing has to be converted.

### B.6 Numbers (`b_slowly_varying_factor.py`, `c_critical_case.py`)

**Part 0, the constants** (30 digits; differences below $10^{-29}$).
$\mathbb E\log|\eta_1|$ by quadrature against $\tfrac12[\psi(\tfrac12) - \psi(\tfrac d2)]$ for
$d = 2,\dots,7$: $-0.693147180559945$, $-1$, $-1.19314718055995$, $-1.33333333333333$,
$-1.44314718055995$, $-1.53333333333333$. $\operatorname{Cin}(1) + \operatorname{Ci}(1) =
0.57721566490153286061 = \gamma_E$. With $\Omega_d(s) := \int\cos(s\eta_1)\,d\bar\sigma =
\Gamma(\tfrac d2)(2/s)^{d/2-1}J_{d/2-1}(s)$, the constant
$\int_0^1(1-\Omega_d)\,du/u - \int_1^\infty\Omega_d\,du/u$ equals $\varkappa_d$ for $d = 1,\dots,7$
($0.577215664901533$, $-0.115931515658412$, $-0.422784335098467$, $-0.615931515658412$, …).

**Part 1, the definition against the single integral.** $F_d(\rho e)/c$ computed (A) literally, by
the cosine integral and a second quadrature over the sphere, and (B) as
$\int_0^\infty(1-\Omega_d(r\rho))k_d(r)\,dr/r$, for the three profiles below, $d = 1,2,3$ and
$\rho = 3, 12, 30$: the 27 pairs agree to $3\cdot10^{-19}$ (A is run at 18 digits). Method B is
what reaches large $\rho$.

**Part 2, three profiles supported in $(0,1)$** ($C_k = 0$). Since $F_d$ is linear in $k_d$,
$\delta(\rho) := [F_d(\rho e) - c\log\rho + \log K(1/\rho)]/c - \varkappa_d$ does not depend on
$c$, and the ratio of the claim is $L(\rho)/(A\,K(1/\rho)) = e^{-c\,\delta(\rho)}$. The table is
that ratio at $c = 1$.

*Step, $k_d = c\,\mathbf 1_{(0,1)}$, $K \equiv 1$:* $L(\rho) \to e^{-c\varkappa_d}$, which at
$c = 1$ is $0.5614594836$, $1.122918967$, $1.526205112$ for $d = 1, 2, 3$.

| $\rho$ | $d = 1$ | $d = 2$ | $d = 3$ |
|---:|---:|---:|---:|
| $10$ | 0.955561232597 | 1.00882587764 | 1.00898581024 |
| $10^2$ | 0.994864407337 | 0.999225160932 | 0.999914834895 |
| $10^3$ | 1.000826657 | 1.00000467873 | 0.999999435971 |
| $10^4$ | 0.99996944855 | 1.00000036489 | 1.00000000952 |
| $10^6$ | 0.999999650006 | 0.999999999274 | 0.999999999999 |
| $10^8$ | 1.00000000932 | 1.0 | 1.0 |

*Power, $k_d = c(1 - r^{1/2})\mathbf 1_{(0,1)}$, $K(x) = \exp(2c(1 - x^{1/2}))$, non-constant and
bounded:*

| $\rho$ | $d = 1$ | $d = 2$ | $d = 3$ |
|---:|---:|---:|---:|
| $10$ | 1.27205393614 | 0.972272498116 | 0.852028351048 |
| $10^2$ | 1.07748124617 | 0.9908315024 | 0.950599390973 |
| $10^4$ | 1.00749480993 | 0.999079431618 | 0.994946529219 |
| $10^8$ | 1.00007467137 | 0.999990790118 | 0.999949338456 |
| $10^{16}$ | 1.00000000747 | 0.999999999079 | 0.999999994934 |
| $10^{32}$ | 1.0 | 1.0 | 1.0 |

*Logarithmic, $k_d = c(1 - 1/\log(e/r))\mathbf 1_{(0,1)}$, $K(x) = (1 + \log(1/x))^c$, unbounded.*
Here $c - k_d(u/\rho)$ is of order $1/\log\rho$, so the ratio converges at that rate, and the
first-order term is computable: $\delta(\rho)(1+\log\rho) \to -\varkappa_d$. Both columns are shown.

| $\rho$ | $d=1$: ratio | $\delta(1+\log\rho)$ | $d=2$: ratio | $\delta(1+\log\rho)$ | $d=3$: ratio | $\delta(1+\log\rho)$ |
|---:|---:|---:|---:|---:|---:|---:|
| $10$ | 1.24021 | −0.71099 | 0.97354 | 0.08858 | 0.86735 | 0.47000 |
| $10^2$ | 1.11941 | −0.63228 | 0.98055 | 0.11011 | 0.92234 | 0.45313 |
| $10^4$ | 1.06103 | −0.60485 | 0.98884 | 0.11458 | 0.95783 | 0.43987 |
| $10^8$ | 1.03089 | −0.59084 | 0.99406 | 0.11574 | 0.97801 | 0.43186 |
| $10^{16}$ | 1.01555 | −0.58395 | 0.99694 | 0.11597 | 0.98877 | 0.42747 |
| $10^{32}$ | 1.00780 | −0.58056 | 0.99845 | 0.11599 | 0.99432 | 0.42516 |
| $10^{60}$ | 1.00417 | −0.57899 | 0.99917 | 0.11597 | 0.99696 | 0.42406 |
| limit | 1 | −0.57722 | 1 | 0.11593 | 1 | 0.42278 |

For comparison, without the factor $K$ the quantity $L(\rho)/A$ at $\rho = 10^{60}$ and $c = 1$ is
$K(1/\rho) = 139.2$ times the ratio: the factor is what is being tested.

**Part 3, the Matérn datum of the paper** (Proposition 3.11(2)): $\widehat\mu(\rho e) =
(1+\rho^2/2)^{-\gamma}$, $c = 2\gamma$, delay profile $k_{\mathrm I}(u) = \gamma e^{-u}$, and by
`eq:polar-profile-d`
$$k_d(r) = \frac{4\gamma}{\Gamma(d/2)}\Bigl(\frac{r}{\sqrt2}\Bigr)^{d/2}K_{d/2}(\sqrt2\,r)$$
($K_\nu$ the modified Bessel function). Here $C_k \ne 0$, $K$ is non-constant, and $L$ is known
exactly, $L(\rho) = \rho^{2\gamma}(1+\rho^2/2)^{-\gamma} \to 2^\gamma$. (a) This $k_d$ reproduces the
exponent $\gamma\log(1+\rho^2/2)$ through the definition, at $\rho = 3$, to 30 digits in each case.
(b) The proposition predicts $A(d,c,C_k)\,K(0+) = 2^\gamma$:

| $d$ | $\gamma$ | $C_k$ | $\log K(0+)$ | $A$ | $A\,K(0+)$ | $2^\gamma$ |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0.3 | 0.068247563393 | 0.622521116502 | 0.660619688612 | 1.231144413344916 | 1.231144413344916 |
| 2 | 0.75 | 0.358713316089 | 0.704676428021 | 0.831257185697 | 1.681792830507429 | 1.681792830507429 |
| 3 | 0.75 | 0.535294010135 | 0.420977892907 | 1.103936571125 | 1.681792830507429 | 1.681792830507429 |
| 3 | 1.25 | 0.892156683558 | 0.701629821511 | 1.179162162126 | 2.378414230005442 | 2.378414230005442 |
| 5 | 1.0 | 1.105015825187 | 0.285927668883 | 1.502633915152 | 2.0 | 2.0 |
| 2 | 2.0 | 0.956568842904 | 1.879137141391 | 0.610887305053 | 4.0 | 4.0 |

The last row has $c = 4 > d = 2$: clause 2 does not need $c \le d$. The identity of this table is
exact and can be checked by hand: the Mellin transform of $k_d$ is
$\int_0^\infty k_d(r)r^{s-1}dr = \frac{4\gamma}{\Gamma(d/2)}\,2^{-s/2}\,2^{s-2}\,
\Gamma(\tfrac s2)\Gamma(\tfrac{s+d}{2})$, whose expansion at $s = 0$ is
$\frac cs + c\bigl[\tfrac12\log 2 - \tfrac12\gamma_E + \tfrac12\psi(\tfrac d2)\bigr] + O(s)$, and
the constant term is $C_k - \log K(0+)$; so $A\,K(0+) = \exp\bigl(c[\log 2 - \tfrac12\log 2]\bigr)
= 2^{\gamma}$. This checks the dependence of the constant on $d$, $\psi(d/2)$ included, in every
dimension. (c) The ratio $L(\rho)/(A\,K(1/\rho))$:

| $d$ | $\gamma$ | $\rho = 1$ | $10$ | $10^2$ | $10^4$ | $10^8$ |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0.3 | 1.34035892142 | 1.07896674105 | 1.00843072145 | 1.00008484741 | 1.00000000849 |
| 2 | 0.75 | 0.887556774439 | 1.0082549956 | 1.00025314215 | 1.00000005985 | 1.0 |
| 3 | 0.75 | 0.668324581108 | 0.992225204226 | 0.999924548309 | 0.9999999925 | 1.0 |
| 5 | 1.0 | 0.44366539311 | 0.983657863112 | 0.999833366387 | 0.999999983333 | 1.0 |

(d) Clause 3, end to end: the closed-form density (3.7) of the paper over $Q\,s^{c-d}K(s)$:

| $d$ | $\gamma$ | $Q$ | $s = 10^{-1}$ | $10^{-2}$ | $10^{-4}$ | $10^{-6}$ | $10^{-8}$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0.3 | 0.377356699633 | 0.613221283476 | 0.832112895454 | 0.972355041106 | 0.995606337641 | 0.999303526031 |
| 2 | 0.75 | 0.276781988993 | 0.660803570293 | 0.886733950468 | 0.988631527041 | 0.998863144654 | 0.999886314464 |
| 3 | 0.75 | 0.0700929467415 | 0.952339234691 | 0.997928658628 | 0.999997681848 | 0.999999997657 | 0.999999999998 |
| 3 | 1.25 | 0.149738586059 | 0.653359948935 | 0.886486694645 | 0.988631465401 | 0.998863144644 | 0.999886314464 |
| 5 | 1.0 | 0.019031080858 | 0.994195330659 | 0.999934267586 | 0.999999993334 | 0.999999999999 | 1.0 |

The convergence is of order $s^{d-c}$ (the next term of the density), slow where $c$ is close to
$d$.

**Part 4, the line.** $\int_0^1(e^{-u}-1)\,du/u + \int_1^\infty e^{-u}du/u = -\gamma_E$ to 20
digits; $\sin(c\pi/2)/(\Gamma(c)\sin c\pi) = R(1,c)$ at $c = 0.2, 0.5, 0.8, 0.95$ to 29 digits.

**Clause 4** (`c_critical_case.py`): the Matérn kernel of index $\gamma = d/2$, whose density is
$2K_0(\sqrt2|x|)/((2\pi)^{d/2}\Gamma(\tfrac d2))$. The quotient $p/(B\,\mathcal L)$ tends to $1$ at
the rate $1/\log(1/s)$, so the sharper check is that the difference $p - B\,\mathcal L$ tends to a
constant, and that $B\,K(0+) = 2(2\pi)^{-d/2}/\Gamma(\tfrac d2)$, the coefficient of
$\log(1/|x|)$ that the paper prints after Proposition 3.15.

| $d$ | $B$ | $B\,K(0+)$ | $2(2\pi)^{-d/2}/\Gamma(\tfrac d2)$ | $s$ | $p(s)$ | $B\,\mathcal L(s)$ | quotient | difference |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0.159503168821 | 0.450158158079 | 0.450158158079 | $10^{-2}$ | 1.969350488 | 1.654924076 | 1.1899945 | 0.31442641 |
| | | | | $10^{-4}$ | 4.042284468 | 3.721710028 | 1.0861363 | 0.32057444 |
| | | | | $10^{-6}$ | 6.115339374 | 5.794701935 | 1.0553329 | 0.32063744 |
| | | | | $10^{-10}$ | 10.26144923 | 9.940811155 | 1.0322547 | 0.32063808 |
| 2 | 0.124394357609 | 0.318309886184 | 0.318309886184 | $10^{-2}$ | 1.392541085 | 1.292429132 | 1.0774603 | 0.10011195 |
| | | | | $10^{-4}$ | 2.858326759 | 2.758206862 | 1.0362989 | 0.1001199 |
| | | | | $10^{-6}$ | 4.324197941 | 4.224078044 | 1.0237022 | 0.1001199 |
| | | | | $10^{-10}$ | 7.255940336 | 7.155820439 | 1.0139914 | 0.1001199 |
| 3 | 0.0617388450206 | 0.143289792063 | 0.143289792063 | $10^{-2}$ | 0.6268637297 | 0.6001283697 | 1.0445494 | 0.02673536 |
| | | | | $10^{-4}$ | 1.286699109 | 1.259991548 | 1.0211966 | 0.026707561 |
| | | | | $10^{-6}$ | 1.94657298 | 1.919865425 | 1.0139112 | 0.026707555 |
| | | | | $10^{-10}$ | 3.266320737 | 3.239613182 | 1.0082441 | 0.026707555 |

### B.7 Is it in print for $d \ge 2$? What the notes on the line theory imply

The reading notes are on the line theory, and what they establish is this.

- On the line the statement is in print in full: the transform (Sato–Yamazato Lemma 5.1; Sato's
  (53.33)), the upper bound (their Lemma 2.4; Sato's Lemma 53.9) and the density (their Theorems
  1.6 and 1.7; Sato's Theorems 53.6 and 53.8), with the constant $e^{-c\gamma_E - C_k}$.
- `READING-sato1978distribution.md` § 6: "Everything in this paper is on the line."
  `READING-sato1999levy-dimension-d.md` § 7: the asymptotic (53.28)/(53.30) "still has no
  $\mathbb R^d$ counterpart in the book"; Theorem 53.8 is "on $\mathbb R$" and the whole apparatus
  of § 53, the $k$-function, $K$, $L$, $\kappa$, is one-dimensional.
- The $\mathbb R^d$ source the notes record for the rate, Grzywny–Ryznar–Trojan, normalises by
  the exponent $\psi$ and by the slowly varying function $\ell$ of the Lévy density, in the limit
  $t \to 0$; the notes record no statement there that expresses $e^{-\psi}$ through
  $\exp\int(c - k_d)\,du/u$ with its constant.

So as far as these notes show, the profile form with its constant is in print for $d = 1$ only,
and the $d$-dimensional constant, with $\psi(d/2)$, is not in what was read. That is a statement
about the notes; the prior-art search is another agent's. One thing that search should be told:
clause 2 is equivalent to $\psi(\rho e) - \int_{1/\rho}^\infty k_d(r)\,dr/r \to c\,\varkappa_d$ for
the exponent $\psi = F_d$, a comparison of the exponent with the tail integral of the Lévy measure
to within an additive constant. Comparisons up to a multiplicative constant are standard for
unimodal Lévy processes; the additive form is what a logarithmic exponent needs, and it is the
place to look.

### B.8 Options and cost

**What the Lean has.** `ExponentLog.lean` (644 lines): the cosine profile `cosProfileL` as a lower
integral, `OriginDatum.cosProfile_limit` (the one-variable limit and the bound $2c|\log b|$),
`OriginDatum.exponent_eq_integral_sphere`, `OriginDatum.tendsto_exponent_dilate` (the dominated
convergence on the sphere, for differences), a Riemann–Lebesgue lemma on $(0,\infty)$,
`OriginDatum.tailConst` for $C_k$. `OriginRate.lean` (1109 lines): `origin_ball_rate` and
`origin_density_rate`, normalised by the transform. `RegularVariation.lean` (533 lines):
Mathlib-only steps for a function nonincreasing along rays. None of them names $K$, the
logarithm on the sphere, Euler's constant or the digamma function. Mathlib at the pinned revision
has the layer-cake formula (`MeasureTheory.lintegral_eq_lintegral_meas_lt`),
`Real.eulerMascheroniConstant` with `eulerMascheroniConstant_eq_neg_deriv` and
`Complex.hasDerivAt_GammaIntegral`, `digamma` with `digamma_one_half`, and
`integral_log_sin_zero_pi_div_two`; it does not have the cosine integral or its constant.

**The Lean statement, and its price written beside it.** Clause 2 as a limit of a quotient of real
numbers along `atTop`, with `D.slowFactor x := Real.exp (∫ u in x..1, (c - D.k u) / u)`:

| Piece | Content | Lines (estimate) |
|---|---|---:|
| (a) | `slowFactor`: $K \ge 1$, monotone, slowly varying, and (B.1) | 120 |
| (b) | Step 1, the layer-cake identity (B.2) for `cosProfileL` and for $I$; the superlevel sets of an antitone $k$ | 200 |
| (c) | $\operatorname{Cin}$: the limit of $\operatorname{Cin}(X) - \log X$ exists, and the bound on $G$ (the bounds are in the file) | 150 |
| (d) | the one-variable limit, by bounded convergence in $y$ | 80 |
| (e) | Step 4: the integrability of $\log|\langle e,\eta\rangle|$ on the sphere (new), and the dominated convergence, modelled on `tendsto_exponent_dilate` | 320 |
| (f) | clause 2 as a quotient; clause 3 by multiplying with `origin_density_rate` and `origin_ball_rate` | 100 |
| | **Clauses 1 to 3, the constant written as $g + \lambda_d$ with $g$ and $\lambda_d$ defined as a limit and an integral** | **about 950** |
| (g) | Step 2: $g$ is Mathlib's Euler constant | 250 |
| (h) | Step 3: $\lambda_d = \tfrac12[\psi(\tfrac12) - \psi(\tfrac d2)]$, by the Gaussian in polar coordinates and the derivative of the Gamma integral | 300 |
| (i) | clause 4: integrals of equivalent divergent functions, and the constant | 150 |
| | **Everything** | **about 1650** |

These are estimates made while writing the type, not from an attempted proof; nothing was
compiled. The total is the size of Proposition 3.15 itself (1640 lines in two modules). Axioms, by
the shape of the statement and to be confirmed by `#print axioms` when it exists: clauses 1 and 2
are about the exponent alone and should print Lean core; clauses 3 and 4 inherit entry A11 from
`origin_density_rate` (and A8, A2, A3(iii) in the form that asserts $q$ exists). No new ledger
entry, no new interface.

**Options.**

1. **A new proposition** (blueprint node after `prop:origin-rate-d`, the proof of B.3 as the proof
   of record, Lean as priced). It replaces the first question of § 4.1 by a result, lets the
   paper state the rate as $q(s) \sim Q\,s^{c-d}K(s)$ in the profile, and makes the comparison
   with Sato–Yamazato complete at $d = 1$. Cost: one blueprint node with its blind referee, about
   950 Lean lines for clauses 1 to 3 with the constant as $g + \lambda_d$, about 1650 with the
   closed form and clause 4; the mirror into § 3.3 and Appendix A. It changes what the paper
   claims; the prior-art row for it in Table 3 depends on the other agent's search.
2. **The proposition at the blueprint with clause 2 in Lean and the two closed forms of the
   constant as computations of the prose.** The machine-checked statement is
   $L(\rho)/K(1/\rho) \to e^{-C_k - c(g + \lambda_d)}$; that $g = \gamma_E$ and
   $\lambda_d = \tfrac12[\psi(\tfrac12) - \psi(\tfrac d2)]$ is printed with Steps 2 and 3 and named
   in § 1.1 beside the Matérn readings, which have that status now. About 950 lines.
3. **A remark after Proposition 3.15**, with the statement of clauses 2 and 3 and the proof of
   B.3 printed (about one page), outside the machine-checked part. No Lean. § 4.1's first
   question is replaced by a pointer to it. This is what the referee asks for at the least cost
   ("Replace the purported open problem by this consequence, with its short proof").
4. **Leave the question, reworded.** Not tenable: the answer is in the paper's own records
   (`PRIOR-ART-origin-threshold-reading.md` § 6.4) and now in a referee's report.

Each of 1 to 3 changes what the article claims, and 1 and 2 add a node: the author's decision.
Whichever is taken, the first paragraph of § 4.1 goes, and with required change 6 the subsection
keeps two questions (the derivatives; the Student-t kernels).

### B.9 What else the statement touches

- `lem:isotropic-exponent-log`, annotation: "**Not claimed**: … an explicit form of $L$; nor that
  $L$ is bounded above". Clause 2 gives the form, and its two-sided bound decides the second: $L$
  is bounded exactly when $\int_0^1(c - k_d(u))\,du/u < \infty$, as on the line.
- `prop:origin-rate-d`, annotation: "**Not claimed**: … an explicit form of the slowly varying
  factor $L$, such as the $d$-dimensional analogue of the factor $K$ of (53.25) (the memo's § 6.4
  sketches one …)". Same.
- Proposition 3.17 (the upper bound with a loss $\beta < c$): for $c < d$, clause 3 gives
  $q(s)\,s^{d-c} \to Q\,K(0+) \in (0,\infty]$, finite exactly when
  $\int_0^1(c - k_d(u))\,du/u < \infty$. So an upper bound by the pure power $s^{c-d}$ holds for
  exactly those profiles, and the loss in the exponent cannot be removed in general. This bears
  on the review's remark on the optimality sentence beside Proposition 3.17, which is another
  part of the response.
- Lemma A.3(1) has the constant $\tfrac{13}{4}c + 2C_k$; the upper bound of clause 2 is
  $F_d(\rho e) \le c\log\rho - \log K(1/\rho) + C_k + \tfrac{13}{4}c$, which is smaller by
  $C_k + \log K(1/\rho)$. Nothing needs the sharper form; it is recorded because the Lean of A.3
  and of Proposition 3.15(2) pins the constant $e^{-13d/4 - 2C_k}$.

---

## Scripts and outputs

| File | What it computes |
|---|---|
| `verify-round1-scripts/a_critical_values.py`, `a_critical_values-output.txt` | $w_d$ for $d \le 5000$, $\sqrt d\,w_d$, the squeeze of A.3, Stirling's ratio, the crossing of $\sqrt\pi$ |
| `verify-round1-scripts/b_slowly_varying_factor.py`, `b_slowly_varying_factor-output.txt` | parts 0 to 4 of B.6 (about 17 minutes) |
| `verify-round1-scripts/c_critical_case.py`, `c_critical_case-output.txt` | clause 4 on the Matérn kernel of index $d/2$ (nested quadratures) |

Not done: no Lean was built and no statement was typed in Lean; the line counts of A.6 and B.8 are
estimates. No density was inverted numerically for a profile with unbounded $K$; for that profile
the check is of clause 2, and clause 3 is clause 2 composed with Proposition 3.15(1), whose own
numerical checks are in `REFEREE-rate-at-the-centre.md` § 4.
