# Verification of the external review, round 3: reports C (§§ 4.1–4.5, App. B) and D (§§ 4.6–4.8, Apps. C, E)

**What this is.** Article-kit `PROCESS.md` § 9 asks that every finding of an external review be
checked against the text, the blueprint and the sources before anything changes. This record checks
every required change, every suggestion, and every claim of an error, gap, missing qualification,
overclaim, attribution or numerical disagreement in sections 2–7 of reports C and D of round 3
(`review-content-review-3-C-sections-4.1-4.5-appendix-B-claude-fable-5.1.md`,
`review-content-review-3-D-sections-4.6-4.8-appendices-C-E-claude-fable-5.1.md`). Reports A, B and E
were skimmed only for repeats, which are named where they occur; their own findings are not verified
here. Nothing but this file and the scripts under `verify-round3-paper-scripts/` was written; no
`.tex`, `.lean` or blueprint file changed, and nothing was committed.

## Inputs and conventions

**Inputs.** The frozen build `review-build-review-3.pdf` (110 pages, revision `59c56bd`; since then
only `paper/references.bib` changed, `git diff --stat 59c56bd HEAD -- paper blueprint`). Printed page
numbers equal PDF page numbers; each page was read with `pdftotext -f N -l N -layout`, and where the
text layer was ambiguous (stacked fractions, superscripts) the page was rendered with `pdftoppm` and
read as an image (pp. 12, 67). Also read: `paper/*.tex`; `blueprint/src/parts/03-isotropic.tex`,
`05-orbits.tex`, `05-wedges.tex`; `paper-iso/*.tex` and the release tag `iso-v0.1`
(`git show iso-v0.1:paper-iso/appendix-isotropic.tex`); the decisions
`records/affine/PLAN-review-response-paper.md` §§ 0 and R2.0 (D1–D9) and `adr/0003`–`adr/0006`.
Sources read through the librarian CLI: `fagerstrom2026isotropic` p. 38 (`library search`);
`jurek1993operator` p. 88 (`library page`); `hilgert1989lie` p. 440 (`library page`);
`mikolajczyk2004scale` p. 72, `lindeberg1997shape` p. 17, `horn2012matrix` p. 494 (`library search`,
`library page`); `library search --corpus` for Lawson, Kostant, Neeb, Hilgert, "semigroup",
"convexity", "symmetric space", "majorization". Reading notes consulted:
`READING-lindeberg1994shape.md`, `READING-lindeberg1997shape.md`, `READING-mikolajczyk2004scale.md`,
`READING-horn2012matrix.md`, `READING-hilgert1997causal.md`, `READING-cuppens1975decomposition.md`,
`READING-linnik1977decomposition.md`.

**Scripts** (in `verify-round3-paper-scripts/`, each with its saved `-output.txt`):
`e5_index2_coefficient.py` (the continuum log-rate at indices 1 and 2, the grid of Remark E.5 over two
ranges of $t$, a direct check of the angular factor), `e5_rotated_step.py` (Remark E.5 at a step
rotated by $45^\circ$), `orders_checks.py` (the union of the $\mathfrak k_\alpha$; the ordered-density
step set of the dyadic profile under square roots; the atom of a Matérn ray increment). numpy only.

**Verdicts.** CONFIRMED: the defect is real as stated. PARTLY: what holds is said, and what does not.
REFUTED: the paper is right, and the reason is given.

**Classes.** *safe*: a wording, qualification, attribution or slip a session may fix under `adr/0003`;
where it touches a `% shared with blueprint` statement or a `% proof of` proof it is made in the
blueprint first and re-transcribed (`adr/0004`). *author*: it changes what the paper claims or its
structure, reverses one of D1–D9, or chooses between routes. *decline*: wrong, or against a rule or a
decision.

Items are cited as C-R*n* / D-R*n* (required change *n*), C-S*n* / D-S*n* (suggestion *n*), and by
report section otherwise.

---

## 1. Lemma 2.9(2), the factor four (D § 3.2 item 1, D-R1, D-S5; C § 3 in passing) — REFUTED; decline

**Quote.** In the build at p. 12, clause (2) of Lemma 2.9 (`02-line-papers.tex:362–365`).

**The defect is an extraction artefact.** `pdftotext` prints the stacked fraction $\tfrac c2$ as
"2c" (the 2 of the denominator lands before the c on the line). The page rendered at 150 dpi reads
$g(au) - g(u) \to \tfrac c2 \log a$, and the source is `\tfrac c2\log a` (`02-line-papers.tex:364`).
Report C already says so ("the rendered page reads ½ c log a"); report A agrees (A § 3, "clause (2)'s
'c/2 log a' … is right").

**Derivation.** $g(au) = F_d(\sqrt a\,\sqrt u\,e)$, so $g(au) - g(u) \to c\log\sqrt a = \tfrac c2\log a$.
Matérn check: $c = k_d(0{+}) = 2\gamma$ and $g(u) = \gamma\log(1+u)$ give $\gamma\log a = \tfrac c2\log a$.

**Every copy is right.** Blueprint `lem:isotropic-exponent-log`, `03-isotropic.tex:329–330`, with
its proof deriving $\tfrac c2$ at line 432; the paper's restatement (above); `paper-iso/appendix-isotropic.tex:510`
and `supp-proofs.tex:485`; the release `iso-v0.1`, same file and line; the held release PDF
`fagerstrom2026isotropic`, printed p. 38 (`library search … "Equivalently, for a unit vector"`, the
text layer splitting "c" and "2 log a" over two lines). Proposition 4.19's proof (p. 69) uses the
same value. **No erratum, in this paper or in the released isotropic paper.**

**Response: decline.** D-S5 (display $k = k_d/|S^{d-1}|$, $\kappa = c/2$ near 4.19) rests on this
"slip"; the dictionary is already printed on p. 13 and p. 42 ("$k = k_d/|S^{d-1}|$") and in 4.19's
statement ($\kappa = \tfrac12|S^{d-1}|k(0{+})$). Decline it too.

## 2. The transposed product in the proof of Proposition 4.10 (C § 3, C-R1; D § 3.1, D § 3.2 item 6(a), D-S1 first half) — REFUTED; decline

**Quote.** p. 67, "Here $M_t = \ldots$". The text layer shows "etB etB" with a stray "T" on the line
above, which both referees read as $e^{tB}e^{tB^{\mathsf T}}$.

**The build prints the right product.** Rendered at 150 dpi, p. 67 reads
$M_t = e^{tB^{\mathsf T}}e^{tB}$, and the source is `$M_t = e^{tB^{\tp}}e^{tB}$`
(`appendix-proofs.tex:148`; blueprint `05-orbits.tex:753`, "$M_t = \Sigma_t^{-1} = e^{tB^{\tp}}e^{tB}$").
With $\Sigma_t = e^{-tB}e^{-tB^{\mathsf T}}$ the relative step of $(\Sigma_t, I)$ is
$\Sigma_t^{-1} = e^{tB^{\mathsf T}}e^{tB}$, whose least eigenvalue is $\min_{|x|=1}|e^{tB}x|^2$: exactly
what is printed. The referees' "correction" is the text already there.

**Response: decline.**

## 3. Proposition 4.12(2) and the two products (D § 3.1, D § 3.2 item 6(b), D-S1 second half) — REFUTED; decline

**Quote.** p. 42, 4.12(2): $\mathfrak k_\alpha = \{B : e^{tB}e^{tB^{\mathsf T}} \in \exp C_\alpha\ \forall t \ge 0\}$.

**Why no clause is needed.** The proof of 4.12(2) (p. 76, `appendix-wedge-axis.tex:389–400`) does not
pass through Proposition 4.10's product. It applies $\psi_\alpha$ to $e^{tB}(e^{tB})^{\mathsf T}$, gets
$e^{tB'}e^{tB'^{\mathsf T}} \ge I$ with $B' = B - \tfrac{\tr B}{d+\alpha}I$, and derives
$(d+\alpha)\lambda_{\min}(\mathrm{sym}\,B) \ge \tr B$, which *is* (4.4), directly. Both sets are
defined by (4.4), so they agree without isospectrality. The reader who compares 4.10's proof with
4.12(2) sees two products, but each proof is complete for its own.

**Response: decline** (an optional half-clause "which is (4.4)" already ends the proof).

## 4. The union of the exponent cones (D § 3.2 item 2, D-R2) — CONFIRMED; safe

**Quotes.** Both on p. 41: "The cone grows with $\alpha$, and its union over $\alpha < \infty$ is the
Gaussian's cone $\{\mathrm{sym}\,B \ge 0\}$" (`05-orbits.tex:362–363`, prose after the shared statement),
and in "Prior art", "for the standard Gaussian it is $\{\mathrm{sym}\,B \ge 0\}$, the union of the
$\mathfrak k_\alpha$" (`05-orbits.tex:398`). The blueprint annotation of `prop:stable-exponent-cone`
(not printed) says the same and attributes it to Jurek–Mason Prop. 3.3.10(a), p. 88
(`blueprint/src/parts/05-orbits.tex:735–737`).

**The defect.** $B \in \bigcup_\alpha \mathfrak k_\alpha$ iff $\lambda_{\min}(\mathrm{sym}\,B) > 0$ or
$B$ is skew: if $\lambda := \lambda_{\min}(\mathrm{sym}\,B) = 0$, (4.4) needs $\tr B \le 0$, while
$\mathrm{sym}\,B \ge 0$ gives $\tr B \ge 0$, so $\mathrm{sym}\,B = 0$. This is the paper's own last
sentence of Proposition 4.10. $B = \mathrm{diag}(1, 0)$ has $\mathrm{sym}\,B \ge 0$, lies in no
$\mathfrak k_\alpha$, and is an exponent of $N(0, I)$, with residual $N(0, \mathrm{diag}(1 - e^{-2t}, 0))$
(`orders_checks.py` (a)). The union is dense in $\{\mathrm{sym}\,B \ge 0\}$ ($B + \eta I \in \mathfrak
k_\alpha$ for $\alpha \ge 1/\eta - 2$ at $d = 2$), so its closure is the Gaussian's cone. Jurek–Mason
Prop. 3.3.10(a), p. 88 (read at the page) states only the Gaussian's exponent set
$\{Q : QS + SQ^* \ge 0\}$; it says nothing about a union, so the attribution covers the cone, not the
union. The same boundary phenomenon is stated correctly for the $C_\alpha$ in Theorem 4.21(1) (p. 48).

**Response: safe** (paper prose, and a blueprint annotation that is not printed). p. 41:
"The cone grows with $\alpha$, and the closure of its union over $\alpha < \infty$ is the Gaussian's
cone $\{\mathrm{sym}\,B \ge 0\}$." Prior art: "…for the standard Gaussian it is
$\{\mathrm{sym}\,B \ge 0\}$, the closure of the union of the $\mathfrak k_\alpha$." Blueprint line
736: the same "closure of", keeping the Jurek–Mason citation for the Gaussian's cone.

## 5. Remark E.5 and open problem 6 at index 2 (D § 3.2 item 3, D § 4, D-R3) — CONFIRMED; safe (wording), author only for a new clause

**Quotes.** p. 88, Remark E.5: "At $\gamma = 2$ the slopes are $0.0060$, $0.0544$ and $0.1768$, against
$0.0063$, $0.0579$ and $0.2122$, which are $\gamma$ times the index-1 values, the first-order term in
$P$; they follow it only for small $\varepsilon$" (`appendix-orbits.tex:273–276`). pp. 55–56, open
problem 6: "At index 2 … the grid follows the first-order term in the step only for small steps, and
the coefficient beyond first order is not known" (`06-open-problems.tex:158–161`). The blueprint
annotation of `prop:matern-negative-mass` has the same comparison (`05-orbits.tex:1873–1877`).

**The computation.** The increment's transform tends along rays to the degree-0 function
$h(\omega) = (\langle\omega,\Sigma\omega\rangle/\langle\omega,\Sigma'\omega\rangle)^\gamma$ (the $h$ of
Proposition 4.15's proof), and $\hat\rho - h = O(|\omega|^{-2})$, whose inverse transform is less
singular than $|x|^{-d}$. So the $|x|^{-2}$ term of the increment in the plane is the inverse transform
of $h - \bar h$. With $h = a_0 + \sum_m a_m\cos 2m\varphi$ and the inverse transform of
$\cos 2m\varphi$ equal to $(-1)^m (m/\pi)\cos 2m\theta/|x|^2$ (Stein's formula for spherical harmonics,
$\gamma_k = i^{-k}\pi^{d/2}\Gamma(k/2)/\Gamma((k+d)/2)$, at $d = 2$, $k = 2m$), the negative mass on a
shell grows like $\log(1/a)\int_0^{2\pi}A_-\,d\theta$. `e5_index2_coefficient.py`:

| $\gamma$ | $\varepsilon$ | $\int A_-$ | $\varepsilon/(\pi(1+\varepsilon))$ | grid slope $t \in 4..32$ | grid slope $t \in 8..64$ |
|---|---|---|---|---|---|
| 1 | 0.01 | 0.00315 | 0.00315 | 0.0030 | 0.0031 |
| 1 | 0.1 | 0.02894 | 0.02894 | 0.0283 | 0.0289 |
| 1 | 0.5 | 0.10610 | 0.10610 | 0.1064 | 0.1062 |
| 2 | 0.01 | 0.00627 | (×2: 0.00630) | 0.0060 | 0.0062 |
| 2 | 0.1 | 0.05526 | (×2: 0.05787) | 0.0544 | 0.0554 |
| 2 | 0.5 | 0.17771 | (×2: 0.21221) | 0.1768 | 0.1772 |

At $\gamma = 1$ the method reproduces Proposition E.4(4) exactly, which checks the constant and the sign
independently. At $\gamma = 2$ it gives D's three values, and the grid is within 1–4 % of them on
$t \in \{4, \ldots, 32\}$ and within 0.3–1 % on $t \in \{8, \ldots, 64\}$, the same agreement as at
index 1. The angular factor itself checks: at $t = 64$, $r^2\rho$ on circles of radius 4–16 grid units
is $+0.12, +0.055, -0.022, -0.057, -0.064$ at $\theta = 0, \pi/8, \ldots, \pi/2$, against $A(\theta) =
+0.119, +0.057, -0.025, -0.058, -0.065$. The printed grid slopes reproduce to four decimals.

**What holds and what does not.** The remark's sentence "they follow it only for small $\varepsilon$" is
literally true of the first-order proxy, but the comparison is the wrong one, and the reader is led to
the false conclusion of problem 6. "The coefficient beyond first order is not known" is false as a
statement of knowledge: the coefficient is computable at every index. It is *not proved*: Proposition
E.4 covers index 1 only, and the leading-singularity step above is the same heuristic the remark already
uses at index 1 (shells cut at $a \approx 1/t$). Report E (§ 4) reproduced the same slopes and judged
the remark "the right strength"; it did not compute the index-2 rate, so it does not contradict D.

**Response: safe** for the wording, since a false clause is removed and the comparison corrected; no
statement changes. Remark E.5 (paper prose): "At $\gamma = 2$ the slopes are $0.0060$, $0.0544$ and
$0.1768$, against $0.0063$, $0.0553$ and $0.1777$, the rate that the same heuristic gives for the
$|x|^{-2}$ term of the increment, read off the degree-0 limit $h$ of its transform (proof of
Proposition 4.15); the first-order term in $P$, $\gamma$ times the index-1 values, is not the right
comparison at $\varepsilon = 0.5$." The deposited script `check-grid-matern-cross-shape.py` should print
that rate (its last block compares with `gamma/pi*eps/(1+eps)`), so that every number names what is
computed. Problem 6, last sentence: "At index 2, the other index computed, the grid follows the rate
read off the degree-0 limit of the increment's transform, within 1–4 %, as at index 1; that rate is
computed, not proved." The blueprint annotation's "Not claimed: the coefficient at index $\gamma \ne 1$"
stays true (not proved) and needs only the same correction of its comparison. **Author**, only if the
index-2 rate is to become a statement (an extension of Proposition E.4 to every index: a blueprint
clause and a proof). *Recommended: no*; the remark is numerical and the paper's lead (`adr/0006`) does
not need it.

## 6. Remark E.5: base of the logarithm and the fit (D-R4) — PARTLY; safe

**Quote.** p. 88, "the slopes fitted over $t \in \{4, 8, 16, 32\}$". **What holds:** the fit method is not
named. **What does not:** "the numbers cannot be matched" — the paper's $\log$ is natural throughout,
and reports D and E both matched them. **Response: safe:** "the least-squares slopes against $\log t$
over $t \in \{4, 8, 16, 32\}$".

## 7. Remark E.5: a rotated step (D § 4, D-S7) — CONFIRMED; safe (optional)

A step rotated by $45^\circ$ ($b_+ > 0$, the diagonal neighbours used) gives slope $0.1092$ against
$0.1061$ at $\gamma = 1$, $\varepsilon = 0.5$; the diagonal step gives $0.1064$ (`e5_rotated_step.py`).
D's numbers reproduce. "The five-point stencil treats [the diagonal steps] isotropically" is loose: the
diagonal steps are the ones that use only the axis neighbours. **Response: safe, optional:** "For a step
rotated by $45^\circ$, which uses the diagonal neighbours, the slope is $0.1092$: the stencil's
anisotropy at the grid scale, about 3 %." Needs the deposited script to compute it.

## 8. Proposition 4.19's class: subordinated data with a Gaussian part (D § 3.2 item 4, D-R5) — CONFIRMED; safe

**Quote.** p. 46, "every subordinated isotropic datum (Definition 2.8) whose delay profile is nonzero
and bounded at the origin" (`05-orbits.tex:737–739`, prose). A subordinated datum $(a, k_d)$ takes
$a = b_0$, the drift of the delay datum (p. 11, "in Definition 2.8 the drift $b_0$ is written $a$"), and
Proposition 4.19 is about the orbit of Proposition 4.13(1), which has no Gaussian part. **Response:
safe:** "every subordinated isotropic datum with $a = 0$ (Definition 2.8) whose delay profile …".

## 9. "The ordered-density cone" (D § 3.2 item 5, D-R6) — CONFIRMED, and stronger; safe (rename), author (a counterexample)

**Quotes.** Proposition 4.13's title "the ordered-density cone of an affine orbit" and clause label
"(The cone.)" (p. 43, shared, `05-orbits.tex:511, 524`; blueprint `05-orbits.tex:786, 805`); "gives a
cone of steps" (p. 38, `05-orbits.tex:154`); "the ordered-density cone of $k$" (p. 44,
`05-orbits.tex:592`; blueprint 942); Table 3 "at least the cone read off $R$" (p. 51,
`05-shape-adapted.tex:159`); open problem 1's title (p. 55); `appendix-orbits.tex:54, 58`.

**The defect.** The step set $K_R = \{M : \lambda_{\min}(M) \ge 1,\ \det M \le \lambda_{\min}(M)^d
R(\lambda_{\min}(M)^{1/2})^2\}$ is a step set and its relation a partial order (4.13(3)), but it is
not $\exp C$ for a cone in general. Closure under $M \mapsto M^\tau$ needs $R(\mu)^\tau \le R(\mu^\tau)$,
and supermultiplicativity (Lemma 4.14(1)) gives the reverse. A counterexample, with the paper's own
dyadic profile of Lemma 4.14(5) ($R = 1$ on $[1, 2)$, $R(2) = 2$) and $d \ge 2$:
$M = \mathrm{diag}(4, \ldots, 4, 16) \in K_R$ (on the boundary: $\det M = 4^d\cdot 4 = 4^d R(2)^2$), while
$M^{1/2} = \mathrm{diag}(2, \ldots, 2, 4)$ has $\det = 2^d\cdot 2 > 2^d R(\sqrt2)^2 = 2^d$
(`orders_checks.py` (b), $d = 2, 3$). A set $\exp C$ contains $e^{\tau X}$ with $e^X$, so $K_R$ is
$\exp C$ for no cone. The uses at the stable profile ("is the stable cone of index $\alpha$") and at
$R \equiv 1$ ("the rays") are cones, and they are right. Open problem 2 is unaffected: it concerns the
orbit's true step set, of which $K_R$ is a lower bound.

**Response: safe** for the name (a narrowing of a word, no change of mathematics): "the
ordered-density step set" in 4.13's title and "(The steps.)" for its clause (2), made in the blueprint
and re-transcribed (`prop:orbit-step-cone` is shared; the label may stay); "a set of steps" on p. 38;
"the ordered-density step set of $k$" on p. 44 and in `appendix-orbits.tex`; Table 3 "at least the
steps read off $R$"; problem 1 "The converse of the ordered-density steps". **Author**, whether to add
one sentence (or a clause of Lemma 4.14(5)) that for the dyadic profile the set is not closed under
square roots, so no cone generates it: a new claim, with a two-line proof. *Recommended: yes*, after
4.13; it shows why "cone" is not claimed and links Lemma 4.14(5) to Theorem 4.3(2).

## 10. "These are the kernels computed by finitely many elliptic solves" (D § 2, D-R8) — REFUTED; decline

**Quote.** p. 4 (`01-introduction.tex:272–273`). "These" refers to the preceding sentence, the orbits
of a law whose transform is a decaying rational function of $\langle\omega,\Sigma\omega\rangle$ without
zeros (Proposition 4.18), not to the orbits that cascade along rays only. p. 45 shows that this class
is exactly what finitely many solves compute (a rational function by $\deg P$ shifted solves and one
application of $Q(L_\Sigma)$, and conversely). The sentence characterizes the class it names. The
converse that fails (p. 45) is "rays only ⇒ rational", which p. 4 does not assert. **Response:
decline.**

## 11. Theorem 4.3's "Prior art": Lawson's Ol'shanskiĭ semigroups, Kostant, and "not connected" (C § 6, C-R4; D § 1(iv), D § 6, D-R7) — PARTLY (not verifiable at the page); author

**Quote.** p. 36, "New against the sources read are the reading on PD(d) through step sets and their
spectra, the proof by majorization, the equality of the order with $\exp C$ without a closure, and
cones that are not pointed. … Their theorem is for a connected group. The semigroup $S_K$ lies in
$GL(d)$, which is not connected, and the powers in (c) are those of the positive definite steps, so the
proof here is by majorization" (`05-wedges.tex:236–245`).

**What the library holds.** Not held: Lawson, *Polar and Ol'shanskiĭ decompositions* (J. reine angew.
Math. 448, 1994); Hilgert–Neeb, *Lie semigroups and their applications* (LNM 1552, 1993); Neeb,
*Holomorphy and convexity in Lie theory* (2000); Kostant's convexity theorem (Ann. Sci. ENS 1973)
(`library search --corpus`: no hit for Lawson beyond `lawson1989ordered` and `hilgert1989lie`, none for
Kostant or Neeb). `paper/references.bib` and `PRIOR-ART-positioning.md` (row C) cite only
`lawson1989ordered`, `hilgert1989lie`, `hilgert1997causal`. So neither referee's claim can be checked at
the page, and neither referee read those pages either (D says so).

**What the held sources say.** HHL Cor. V.4.58 (p. 440, read): for a pointed cone $C$ in the
$-1$-eigenspace with conditions (a)–(d), $S = (\exp C)H_0$ is a semigroup with tangent wedge
$C \oplus L(H)$ "**provided $S$ is closed**". Hilgert–Ólafsson Thm. 2.3.3 (p. 44, from Hilgert–Neeb;
`READING-hilgert1997causal.md`): the causal semigroup is $\overline{S_W H}$, a closure. So against the
sources read, "without a closure" is accurate. What C and D assert is that Lawson 1994 proves the
closedness of $H\exp C$ for a group with a polar decomposition (as $GL(d) = O(d)\exp\mathrm{Sym}(d)$),
which would make the equality, for pointed cones, that theorem read on $PD(d)$. That is plausible from
the literature as recalled, but unverified. Kostant's convexity theorem bears on the log-majorization
(C4, which the paper cites and does not claim); whether it also gives "the proof by majorization" of
Theorem 4.3 depends on Lawson's proof, also unread.

**"Not connected".** PARTLY. The connectedness half is a weak reason: $S_K \cap GL^+(d)$ is a closed
subsemigroup of a connected group, and Proposition D.1 already reads every order on $GL^+(d)$. The
second half stands: HHL Thm. V.6.5's divisibility is about roots of elements $A \in S_K$, and the
condition (c) of Theorem 4.3(2) is about powers $M^\tau$ of positive definite steps; the two agree on
symmetric $A$ only, so the translation is not immediate.

**A tension the referees did not name.** `adr/0006` item 6 says the paper claims no novelty in Lie
semigroups and item 1 that such novelty is no criterion of value; a list "New against the sources read"
of Lie-semigroup points sits uneasily with it whatever Lawson 1994 says.

**Response: author.** (a) Have the librarian acquire Lawson 1994 (and Neeb 2000, Thm. XI.1.7, and
Hilgert–Neeb 1993, Prop. 4.16 and Thm. 4.21) and read them at the page; then cite Lawson for the
closed Ol'shanskiĭ semigroup if it is there and narrow the list. (b) Narrow now without the sources:
replace the "New …" sentence by what the paper does with the theory ("Here the correspondence is read
on PD(d) through step sets and their spectra and proved by majorization, without a closure, for cones
that need not be pointed"), with no priority claim, and drop "which is not connected" while keeping the
powers-versus-roots reason. *Recommended: (b) now, which is safe in direction and fits `adr/0006`
item 6, and (a) as a request to the librarian*, so that the citation follows a reading note
(`CLAUDE.md`, "A source is read at the page").

## 12. Table 2's (GL(d), stable) cell and laws with a Gaussian part (C § 2, C-R3) — PARTLY; author, with report E's item 1

**Quotes.** p. 32, cell: "contains the orbit of every profile with $R(\lambda) \ge \lambda^\alpha$ …; among
the stable orbits, exactly those of index $\gamma \ge \alpha$"; p. 48 after Theorem 4.21: "For general
profiles the row is known to be at least the one stated: that $\mu_I \in F_\alpha$ forces
$R(\lambda) \ge \lambda^\alpha$ is the open converse of Proposition 4.13"; p. 55, problem 1: "The
converse would complete the profile clause of Theorem 4.21(3) and of Proposition 4.20(2)".

**What holds.** Laws with a Gaussian part are in $F_\alpha$ and the paper never says so. C's family
checks: for $\Sigma \le_\alpha \Sigma'$ in PD(d), $\Sigma' - \Sigma \ge 0$ (Proposition 4.20(1)), so
$N(0, 2b\Sigma) * S_\gamma(\Sigma)$, $\gamma \ge \alpha$, has the increment
$N(0, 2b(\Sigma' - \Sigma)) * \rho_{\Sigma,\Sigma'}$, a probability measure, and is $GL(d)$-covariant.
**What does not.** The cell does not "describe only laws without a Gaussian part" as a wrong claim: it
says "contains", Theorem 4.21(3)(c) says "contains", and the glossary of § 4.3 says the profile entries
concern "a rotation-invariant law with no Gaussian part" (p. 31). Problem 1's "would complete the
profile clause" is right for that clause, which is about the laws of 4.13(1). Report D (§ 2) read the
same cell and found no overstatement.

**Overlap.** Report E § 3.1 and E-R1 (not verified here) claim more: that Theorem 3.5(2) with the path
condition of Proposition 4.20(1) makes every increment of a $(GL(d), \le_\alpha)$-family infinitely
divisible, so the Lévy densities are ordered along every step and $F_\alpha = \{N(0, aI) * \nu_k :
k = 0 \text{ or } \beta_-(k) \ge \alpha\}$. If E is right, C's open question ("whether a positive
increment of an orbit with a Gaussian part forces ordered Lévy measures") is answered for families,
and the cell becomes complete.

**Response: author**, decided together with E-R1. If E-R1 is rejected, the safe minimum is one sentence
after Theorem 4.21 (paper prose): "Laws with a Gaussian part are not described here; the convolution
of $N(0, 2bI)$ with a law of $F_\alpha$ is in $F_\alpha$" (the second clause is a new, easy claim, so it
is the author's; the first is safe on its own).

## 13. Which cells are complete, at the table (C § 2, C-R2; repeats A-R1, E § 2) — CONFIRMED as presentation; safe (caption), author (abstract)

**Quotes.** Abstract p. 1 "completely in some cases, by bounds or examples in others"; p. 3 "a complete
description in some cases and bounds or examples in the others"; the only cell-by-cell account is § 5,
p. 54 ("four cells … stop short …; three more are classified on part of their parameters"). Table 2's
caption (p. 32) marks nothing. The count (two complete) was verified in round 1
(`VERIFY-round1-claims-paper.md`; the plan's "two are complete on PSD(d) and three more in a stated
restricted sense"). It changes if E-R1 holds (§ 12).

**Response: safe** for the caption (one sentence, paper prose): "The cells (GL(d), rays) and (GL(d),
Loewner) are complete descriptions; § 5 says which of the others are bounds, examples or partial."
The abstract's wording was decided in D6 (its words on $\alpha$ and on re-measurement, its 250-word
budget); naming the cells there is **author**. *Recommended:* the caption only, after § 12 is decided.

## 14. "Re-measurement of the original image" as a reading (C § 2, C-R5; overlaps A-R4) — PARTLY; safe

**Quotes.** p. 28, "Off the order, a change of aperture is a re-measurement of the original image"
(`05-landscape.tex:131`); p. 2 (`01-introduction.tex:155–156`, the term in emphasis); p. 37
(`05-orbits.tex:129`); abstract `main.tex:143` ("measures the image afresh").

**What holds.** The term is introduced as a definition (emphasized, § 1 and § 4.1), and § 4.8 states the
mathematics beside it ("related to the first stage by no increment that is a probability measure",
`05-shape-adapted.tex:60`). The scope paragraph (§ 5, p. 54) disclaims statements about computation.
**What does not.** As written, "Off the order, a change of aperture *is* a re-measurement" reads as a
fact, and report A adds the reason it is not one: a step off a chosen order $W$ may still have a
probability increment (every Loewner step of the Gaussian, off the ray order; the stable orbit's
full-rank steps, off the rays). On p. 37 the sentence is correct ("along every other step", the steps
with no positive increment).

**Response: safe** (paper prose, `05-landscape.tex:131` and `01-introduction.tex:155–156`): "Off the
order the axioms ask for no increment, and a change of aperture with no increment that is a probability
measure is called a *re-measurement* of the original image: the coarser record is then not a further
smoothing of the finer one." The abstract is D6's and stays.

## 15. Shape selection "needs" a transitive group (C § 2, C-R6; repeats E-R7) — PARTLY; safe

**Quote.** p. 27, "Shape selection transports a shape with the image, so it needs a group that carries
every shape to every other, as GL(d) does on PD(d)" (`05-landscape.tex:125–127`); p. 51, "neither
supports shape selection in the sense of § 4.1". **What holds:** § 4.9 relies on it as a definition, and
p. 27's use 1 says "The selected shape must transform with the image". **What does not:** a
similarity-covariant family can select shapes; what it loses is the covariance of the selection under
shears. **Response: safe:** "Shape selection, in the sense used here, transports a shape with the image
under every linear map, so it needs …".

## 16. The page anchors of § 4.1 (C § 2, C-R8) — REFUTED; decline

All three were read at the page before this round, and spot-checked now. Lindeberg–Gårding 1994, p. 396,
step 2, $M_I^{(k)} = M^{(k)}/\lambda_{\min}(M^{(k)})$ (`READING-lindeberg1994shape.md`, from the page
image). Lindeberg–Gårding 1997, p. 17: the fixed-volume alternative "would … lead to systematic
over-estimates of the anisotropy", and the choice to keep $\lambda_{\min}(\Sigma_t)$ constant, "the
smallest amount of smoothing", "noise suppression" (`READING-lindeberg1997shape.md`; `library page
lindeberg1997shape --printed 17`, broken text layer, words found). Mikolajczyk–Schmid, p. 72: "setting
the larger eigenvalue $\lambda_{\max}(U) = 1$, which implies that the image patch is enlarged in the
direction of $\lambda_{\min}(U)$" (`library search`). **Response: decline**; a quotation in § 4.1 is a
matter of style, not of grounding.

## 17. Proposition 4.24(1)'s sketch is a pointer (C § 3, C § 5, C-R7) — PARTLY; safe

**Quote.** p. 69, "By Proposition 4.20(1) and Theorem 3.5(2) every increment and kernel is infinitely
divisible, and the rest is the proof of Proposition H.9(1). The last sentence is Proposition F.3(4)"
(`appendix-proofs.tex:326–328`). **What holds:** the sketch delegates. **What does not:** "not proved
at all": H.9(1)'s proof is printed (p. 103, four lines: $-I$ fixes every $\Sigma$, (K3) gives symmetry,
C2(ii) the triplet, (K3) at $\sqrt c\,Q$ the covariance, (K1) the increment), and it transfers word for
word with $\le_\alpha$ for the Loewner order. Report E (§ 3) checked 4.24(1) correct. D2 keeps the
sketches. **Response: safe** (a sketch is paper-side under D2): "…and the rest is the proof of
Proposition H.9(1), with $\le_\alpha$ and Proposition 4.20(1) in place of the Loewner order and Theorem
3.5(3)(a)."

## 18. A shorter proof of Proposition 4.15, and the atom (C § 3, C-S1) — CONFIRMED (mathematics); author

**Quote.** pp. 68–69, the paragraphs "$\Lambda$ vanishes on test functions vanishing near 0" and
"$\Lambda$ is a multiple of the point mass" (`appendix-proofs.tex:244–262`, proof of record of
`prop:log-orbit-rays`, blueprint `05-orbits.tex:1322ff`).

**Check.** $\Lambda(\phi) = \lim_{R\downarrow0}\int\phi(x/R)\,\rho(dx)$ with $\rho$ a probability measure
(shown in the proof) and $\phi$ bounded with compact support: for $x \ne 0$, $\phi(x/R) = 0$ once $R$
is small, and at $0$ it is $\phi(0)$; dominated convergence gives $\Lambda(\phi) = \rho(\{0\})\phi(0)$.
The two paragraphs (about 12 lines) prove this by dilation invariance. Then the paragraph "h is
constant" gives $h \equiv \rho(\{0\})$, and the ray $\Sigma' = c\Sigma$ has $\rho(\{0\}) = c^{-\kappa}$.
For the Matérn orbit ($\kappa = \gamma$, $c = \lambda^2$) this is $\lambda^{-2\gamma}$, the no-jump
probability of Proposition 4.4(4)'s compound Poisson residual of mass $2\gamma\log\lambda$
(`orders_checks.py` (c), two parameter pairs, six digits).

**Response: author.** The proof printed is the blueprint's proof of record (D1), the author accepted its
Fourier convention on 2026-11-03 (`CHANGELOG.md`), and its route is the Lean's
(`AffineHemigroup.log_orbit_rays`); replacing it changes a proof of record and, under `adr/0004`, the
blueprint and the paper together, with the Lean either following or diverging. Options: (a) keep;
(b) shorten blueprint and paper to the dominated-convergence line, and the Lean after it; (c) keep the
proof and add the one-line observation and the atom as a remark. *Recommended: (b)*: the shorter
argument is elementary and complete, and it also makes Remark 4.16's second route less needed; the
atom remark is a new claim and optional.

## 19. Proposition 4.4(3): "g is not linear" (C § 3, C-S2) — REFUTED; decline

$g : [0, \infty) \to [0, \infty)$ with $g(0) = 0$ (p. 36): a linear $g$ is $bu$, and $g \ge 0$ forces
$b \ge 0$. "Not linear" already means "not of the form $bu$, $b \ge 0$". **Decline.**

## 20. "The source of C4 states its inequality in this form" (C-S3) — CONFIRMED (minor); safe

p. 35 defines majorization by the $k$ *smallest* entries and says the source of C4 states it "in this
form" (`05-wedges.tex:210`); § 2.4 (p. 13) says Bhatia states (III.21) through the $k$ largest, with
equal totals. Equivalent, but not "this form". **Safe:** "states its inequality in the equivalent form
of partial sums of the largest entries (§ 2.4)".

## 21. Proposition 4.2(4): $C(K)$ empty unless $I \in K$ (C § 3, C-S4) — REFUTED; decline

Invariance under $X \mapsto cX$ of the empty set holds vacuously, and closedness too; nothing in the
clause is false at $c = 0$. **Decline.**

## 22. Table 2's long cells (C § 7, C-S5) — decline

Round 2 tried a condensed (similarities, Loewner) cell: it was no shorter and dropped a hypothesis of
H.1(3) (`VERIFY-round2-structure-paper.md`; the plan's R2 list). Completeness marks are § 13.
**Decline**; restructuring the table is the author's and was not taken in D3.

## 23. Table 2's footer, "One linear flow $\{e^{sB}\}$, with rotations" (C-S6) — PARTLY; safe

"With rotations" means a skew part of $B$ is allowed. Unclear on its own.
**Safe** (`05-table.tex:121`): "One linear flow $\{e^{sB}\}$, $B$ with a skew part allowed, along …".

## 24. Figure 2(b): which apertures the crosses are (C § 4, C-S7) — CONFIRMED; safe

The caption (p. 30, `05-landscape.tex:244`) does not say. The figure script plots
$tI \to t\,\mathrm{diag}(1, m)$ for $m = 2, 4, 8, 16$ (`fig-shape-plane.py`, `ms = [2.0, 4.0, 8.0, 16.0]`).
**Safe:** "The crosses are the apertures of shape-adapted smoothing at anisotropy $n_2/n_1 = 2, 4, 8,
16$, reached from …".

## 25. § 4.2's one-parameter and orientation paragraphs (C § 7, C-S8) — decline

Each is five to six lines and already ends in a pointer (Appendices G and D). `adr/0006` item 7 sets no
page budget. **Decline.**

## 26. Lemma C.1 into § 4.4; Theorem 4.3(3) to the appendix (C § 7, C-S9) — decline (author if wanted)

p. 35 already states both inequalities of Lemma C.1 in prose and why majorization is the tool. Moving
clause (3) out splits the shared node `thm:cone-orders`. **Decline**; a structural change is the
author's.

## 27. § 4.5's restatement of § 3.4 (C § 7, C-S10) — decline

The two paragraphs serve the subsection's opening map (`WRITING.md`, "each section opens with its aim").
**Decline** (minor; the author's in a later pass).

## 28. The Horn–Johnson anchors (C-S11) — REFUTED; decline

Second edition (2013), printed = pdf − 20: Thm. 7.7.3(a) p. 494, Cor. 7.7.4(c), (e) p. 495, read on
page images (`READING-horn2012matrix.md`); `library search horn2012matrix "7.7.3"` finds the theorem on
p. 494. **Decline.**

## 29. The decomposability semigroup in § 4.4's "Prior art" (C-S12) — PARTLY; decline

The reading (step set = Urbanik's decomposability semigroup transported) is cited in § 4.6's "Prior
art" (p. 41, Jurek–Mason Lemma 2.3.3, p. 54). Theorem 4.3(2)'s tangent cone is Jurek's Lie wedge only
when $K$ is an orbit's step set; Theorem 4.3 is for a general $K$. **Decline** (an optional
cross-reference, the author's taste).

## 30. Terms used before they are defined in § 4.3 (C § 7) — PARTLY; safe

"Step set" on p. 29 ("the order of the step set of the stable orbit", `05-table.tex:28`) precedes
Proposition 4.2: CONFIRMED; **safe:** add "(Proposition 4.2, § 4.6)". ecc and es are defined in the
glossary (p. 30, "Both are defined again where they are used"): REFUTED. Proposition 4.20(1) cited in
§ 4.2 is a forward reference that carries no proof (C agrees); no change.

## 31. Lemma 4.8's proof: the sign of $C$ and $|e^{-s} - 1 + s|$ (D § 3.1, D § 3.2 item 6(c), D-S2) — REFUTED; decline

The bound $R^\alpha E(\zeta/R) \le \|C\||\zeta|^2 + |D(\zeta)|$ (p. 78) holds for every real $C$:
$R^{\alpha-2}\langle\zeta, C\zeta\rangle \le |\langle\zeta, C\zeta\rangle| \le \|C\||\zeta|^2$ for $R \ge 1$,
whatever the sign. No sign of $\mathrm{sym}\,C$ is used. $|e^{-s} - 1 + s| \le s^2$ for $|s| \le 1$ is
true and applied to $s = E(\zeta/R) \to 0$. **Decline.**

## 32. Remark 4.9 as the proof of 4.7(1)(a)⇒(b) (D § 7, D-S3) — decline (author if wanted)

The printed proof is the blueprint's proof of record and the Lean's route; changing it is a route
choice under `adr/0004`, and D3 settled the layout of the Lemma 4.8 material. **Decline.**

## 33. A map at the head of § 4.6; "rung" (D § 7, D-S4) — REFUTED in part; decline

p. 38's second paragraph is that map (the stable orbit, the dilation ratio, index 0, what § 4.7 takes).
"Rung" is defined on p. 38 and used on p. 43, twice on p. 44 (Lemma 4.14(4), "rung 0") and in § 4.8's
title. **Decline.**

## 34. "The orders" of Theorem 4.21's proof as a lemma (D § 7, D-S6) — author; recommend decline

A new statement node (with a Lean tag) for a paragraph whose independence from C4 Appendix I already
prints (p. 105). **Author**; *recommended: no*.

## 35. Proposition E.2 folded into a remark (D § 7, D-S8) — decline

D3: "No merging of propositions"; folding E.2's formula into 4.17 was among the options declined.
**Decline.**

## 36. The Cuppens and Linnik–Ostrovskii sentence (D § 6, D-S9) — REFUTED (premise); decline

Both anchors are page-checked: Cuppens Thm. 7.2.1, p. 157, and Linnik–Ostrovskii Thm. 6.7.2 and Ex. 1,
p. 218, on page images (`READING-cuppens1975decomposition.md`, `READING-linnik1977decomposition.md`).
The sentence explains why the class $I_0$ does not close the open converse of 4.13. **Decline.**

## 37. Proposition 4.18's sketch: $Q$ has no zero on $[0, \infty)$ (D § 5, D-S10) — PARTLY; safe

The sketch (p. 69) says "the coefficient of $u^{n-1}$ in the mixture's $Q$ is positive"; that
$Q = \sum_i w_i\prod_{j\ne i}(1 + a_j u) > 0$ on $[0, \infty)$ and $Q(0) = P(0) = 1$ is left implicit.
**Safe** (sketch, paper side): "…is positive, and $Q > 0$ on $[0, \infty)$ with $Q(0) = \sum_i w_i = 1 =
P(0)$."

## 38. Appendix I: "by definition" for $\preceq_{C_\alpha} = \preceq_\alpha$ (D § 5, D-S11) — PARTLY; decline

Proposition 4.7(2) defines $\preceq_\alpha$ by condition (c) ("Write $\Sigma \preceq_\alpha \Sigma'$ when (c)
holds", p. 39), and 4.12(1) proves $\preceq_{C_\alpha}$ is that condition; the identification is visible
at the statements, and Appendix I lists cited facts per statement. **Decline** (optional).

## 39. Moves for a journal version (C § 7; D § 7, D-S12) — decline

`adr/0006` item 7 (no page budget) and D3 (the measured moves taken; no supplement, no merging).
**Decline.**

## 40. Claims checked and found right, no change asked

C § 2: the introduction's "containing no line" (C itself asks no change); Figure 3's regimes; the ray
base; "costs nothing beyond what the isotropic theory requires". D § 2: the speed limit, Table 3's
bounds, the numbers $2^{2/3}$, 4, 2.52, 2.07, the "price" sentences, Figures 2–3. Agreed; nothing to
do.

---

## Closing table

| Report and item | Verdict | Class | Response |
|---|---|---|---|
| D 3.2(1), D-R1, D-S5; C § 3 (Lemma 2.9(2)) | REFUTED | decline | Rendered page, source, blueprint, `iso-v0.1` and held release all read $\tfrac c2\log a$; text-layer artefact. No erratum. |
| C-R1; D 3.2(6a), D-S1 (4.10 product) | REFUTED | decline | Build prints $e^{tB^{\mathsf T}}e^{tB}$ (p. 67 rendered; `appendix-proofs.tex:148`). |
| D 3.2(6b), D-S1 (4.12(2)) | REFUTED | decline | Proof derives (4.4) directly; no isospectrality used. |
| D 3.2(2), D-R2 (union of $\mathfrak k_\alpha$) | CONFIRMED | safe | "the closure of its union" on p. 41 (twice) and in the blueprint annotation. |
| D 3.2(3), D-R3 (E.5, problem 6) | CONFIRMED | safe; author for a new clause | Compare with 0.0063, 0.0553, 0.1777; drop "not known"; script prints the rate. |
| D-R4 (E.5 fit) | PARTLY | safe | "least-squares slopes against $\log t$". |
| D-S7 (E.5 rotated step) | CONFIRMED | safe (optional) | Slope 0.1092 at $45^\circ$, about 3 %. |
| D 3.2(4), D-R5 (4.19 class) | CONFIRMED | safe | "subordinated isotropic datum with $a = 0$". |
| D 3.2(5), D-R6 ("cone" of 4.13) | CONFIRMED, stronger | safe (rename via blueprint); author (counterexample) | Dyadic profile: $K_R$ not closed under square roots; "ordered-density step set". |
| D-R8 (elliptic solves, p. 4) | REFUTED | decline | "These" names the rational orbits, which p. 45 shows are exactly those. |
| C-R4; D-R7, D § 6 (Prior art, Lawson, Kostant, connectedness) | PARTLY | author | Sources not held; narrow now (also `adr/0006` item 6), acquire and read Lawson 1994. |
| C-R3 (GL stable cell, Gaussian part) | PARTLY | author (with E-R1) | Cell says "contains"; Gaussian-part laws unmentioned; E claims a full characterization. |
| C-R2; A-R1, E § 2 (complete cells) | CONFIRMED | safe (caption); author (abstract) | One caption sentence after § 12; abstract is D6's. |
| C-R5; A-R4 (re-measurement) | PARTLY | safe | Say it is the name for "no probability increment"; abstract untouched. |
| C-R6; E-R7 (shape selection) | PARTLY | safe | "in the sense used here … under every linear map". |
| C-R8 (§ 4.1 anchors) | REFUTED | decline | All three page-checked. |
| C-R7 (4.24(1) sketch) | PARTLY | safe | Add "with $\le_\alpha$ and 4.20(1) in place of …". |
| C-S1 (4.15 proof, atom) | CONFIRMED | author | Dominated convergence gives $\rho(\{0\})\phi(0)$; proof of record and Lean route; recommend (b). |
| C-S2 ("g not linear") | REFUTED | decline | Already exact under $g \ge 0$, $g(0) = 0$. |
| C-S3 (C4 "in this form") | CONFIRMED | safe | "in the equivalent form of partial sums of the largest entries". |
| C-S4 ($C(K)$ empty) | REFUTED | decline | Vacuous. |
| C-S5 (cell lengths) | — | decline | Round 2: condensation dropped a hypothesis. |
| C-S6 (table footer) | PARTLY | safe | "$B$ with a skew part allowed". |
| C-S7 (Fig. 2(b) crosses) | CONFIRMED | safe | "at $n_2/n_1 = 2, 4, 8, 16$". |
| C-S8, C-S10, C § 7 (§§ 4.2, 4.5 paragraphs) | — | decline | No page budget (`adr/0006` 7). |
| C-S9 (Lemma C.1, Thm 4.3(3) moves) | — | decline | Prose already on p. 35; splits a shared node. |
| C-S11 (Horn–Johnson) | REFUTED | decline | Page-checked, 2nd ed. |
| C-S12 (decomposability semigroup) | PARTLY | decline | Cited in § 4.6; Thm 4.3 is for general $K$. |
| C § 7 (forward references) | PARTLY | safe | Pointer for "step set" on p. 29; ecc, es defined in the glossary. |
| D 3.1, 3.2(6c), D-S2 (Lemma 4.8) | REFUTED | decline | Bound holds for every real $C$. |
| D-S3 (Remark 4.9 as proof) | — | decline | Proof of record and Lean route; D3. |
| D-S4 (§ 4.6 map, "rung") | REFUTED in part | decline | Map on p. 38; "rung" used on pp. 43, 44, 48. |
| D-S6 (orders lemma) | — | author; recommend no | New node. |
| D-S8 (fold E.2) | — | decline | D3. |
| D-S9 (Cuppens) | REFUTED | decline | Page-checked. |
| D-S10 (4.18 sketch) | PARTLY | safe | "$Q > 0$ on $[0, \infty)$, $Q(0) = P(0) = 1$". |
| D-S11 (App. I "by definition") | PARTLY | decline | Visible at 4.7(2). |
| C § 7, D-S12 (journal moves) | — | decline | `adr/0006` 7, D3. |
