# Verification of the external review, round 1: the mathematics of the affine paper

**What this is.** Article-kit `PROCESS.md` § 9 asks that every finding of an external review be
checked against the text, the blueprint and the sources before anything changes. This record checks
the mathematical findings of `review-content-review-1-Gemini-4.0-Argon-High.md`: its § 3 (items 1–9),
§ 5 item 5 (sketched proofs whose complete proofs are only in the deposited sources), the last item of
§ 7's first bullet (the forward reference in the proof of Theorem 3.5(3)(c)), and § 8 required changes
6, 7 and 9 and suggestion 6. The headline claims, the numbers, the references and the exposition are
checked in other records and are not repeated here.

**Inputs.** The build the referee read, `review-build-review-1.pdf` (108 pages). Its page numbers
are its PDF pages and the report's. Each page was read with `pdftotext -f N -l N -layout`. Also read:
`paper/*.tex`; `blueprint/src/parts/*.tex`, the text of record; the Lean sources under
`Formalization/` (read only, not built); `paper/main.aux`, for statement numbers and pages. The tree
is at the revision of the build for `paper/` and `blueprint/`. No source was read through the
librarian: no finding in scope turns on a cited page. Nothing but this file was written.

**Verdicts.** CONFIRMED: the referee is right. For a finding that calls a proof correct, it means the
referee's account of that proof is accurate. PARTLY: what holds is said, and what does not. REFUTED:
the paper is right, and the reason is given.

**Fix classes.** *safe*: a typo, a notation slip, a missing step written out or a pointer, which
`adr/0003` lets a session do. *author*: it changes what is claimed, the structure, or which proofs
are printed. *Where*: paper prose; a shared statement or proof, which is changed in the blueprint
and re-transcribed (`adr/0004`, `linkage check --pin-shared`); a Lean docstring.

**Lengths.** Proof lengths are counted in the source (lines and words of the `proof` environment,
comment lines excluded). The page estimates use the density of the paper's own appendices: App. H,
5,360 words over about 8.3 pages, and App. C, 9,924 words over about 13 pages, so about 700 source
words per printed page.

---

## 1. § 3 item 1: Theorems 3.6, 3.7 and 3.12, Lemmas 3.8–3.10, Lemmas A.1–A.2 — CONFIRMED

**The report.** It calls these proofs "complete and rigorous" and describes them: Lemma 3.8 by "a
clean connectedness and separability argument on $U \subset H$"; Lemma 3.9 by "$O(d)$-invariance at
$I$, $\mathrm{GL}(d)$-transport on $\mathrm{PD}(d)$, density of $\mathrm{PD}(d)$ in $\mathrm{PSD}(d)$
with (K2), and a first-zero argument along the ray $tI$"; Lemma 3.10 "deduces additivity of $g$ …
using only continuity at $0$, and then uses $g \ge 0$ to get monotonicity and linearity"; Theorem 3.7
reduces to Lemma 3.8 on $H = \ker(Q^T\Sigma^{-1/2}P\Sigma^{-1/2}Q)$.

**Against the PDF.** Each description matches what is printed:
- Lemma 3.8, p. 65, takes a countable dense $D \subseteq U$ and a null set $N := \bigcup_{\eta\in D}N_\eta$.
  It then argues that "$\ell_x(U)$ is a connected subset of $2\pi\mathbb Z$, a single point".
- Lemma 3.9, pp. 65–66, has the steps "Every kernel from scale zero" (with $A = \Sigma^{1/2}$, then
  $\Sigma_n := \Sigma + n^{-1}I$ and (K2)) and "No zeros", which uses the infimum $t_*$ of the zeros
  of $f(0,\cdot)$ along $sI, tI$.
- Lemma 3.10, p. 66: the step "Additivity, from continuity at 0 alone" gives
  $h(\delta) = g(\delta2^{-n}) - 2^{-n}K(\delta) \to 0$. Then "As $g \ge 0$, $g(y+\delta) \ge g(y)$: $g$ is
  nondecreasing".
- Theorem 3.7, p. 22, uses $H := \{\zeta : \zeta_1 = \dots = \zeta_r = 0\}$ with
  $Q^TP'Q = \operatorname{diag}(p_1,\dots,p_r,0,\dots,0)$ and $P' = \Sigma^{-1/2}P\Sigma^{-1/2}$. That
  $H$ is the kernel the referee names.
- Lemma A.1, pp. 57–58, uses the "Bochner integral" and "Prokhorov's theorem". Lemma A.2, p. 59,
  smooths "with a Gaussian".

**Action.** None.

## 2. § 3 item 2: Theorem 3.5 — CONFIRMED

**The report.** It describes the proof as uniform continuity on the triangle, Lévy's continuity
theorem and the portmanteau theorem making equal subdivisions a null array, then C1 with $b_n = 0$.
For (3)(c), the polar factor $Q = \zeta(s)^{-1/2}\Sigma^{1/2}M^{s/2}$ gives
$\zeta(s)^{-1/2}\zeta(t)\zeta(s)^{-1/2} = QM^{t-s}Q^T \in \mathcal K$.

**Against the PDF.** The steps match pp. 64–65:
- "Small increments … uniformly continuous on the compact triangle … Lévy's continuity theorem …
  the portmanteau inequality". Then "(1) … $t_{n,k} := s + k(t-s)/(n+1)$ … C1 with $b_n = 0$".
- (3)(c): "put $B := \Sigma^{1/2}M^{s/2}$, so that $\zeta(s) = BB^T$ and $\zeta(t) = BM^{t-s}B^T$. Then
  $Q := \zeta(s)^{-1/2}B$ is orthogonal". This is the referee's $Q$.
- The hypotheses of C1 (Theorem 2.10, p. 12) hold: $r_n = n+1$, every row product equals
  $\mu_{s,t}$, and $b_n = 0$.

The forward reference the report notes in parentheses is item 11 below.

**Action.** None.

## 3. § 3 item 3: Proposition 4.2, Lemma C.1, Theorem 4.3, Proposition 4.12 — CONFIRMED

**The report.** The proof uses Ky Fan's extremal principle and the log-majorization C4 to show that
$F_w(\Sigma,\Sigma') = \sum_i w_i^\downarrow\ell_i(\Sigma^{-1/2}\Sigma'\Sigma^{-1/2})$, $w \in D^\#$,
is "superadditive along any three points and nondecreasing along any $C$-causal curve". This "proves
$\preceq_C = \le_{\exp C}$ directly without needing a closure or connectedness of $\mathrm{GL}(d)$ or
pointedness of $C$".

**Against the PDF.** Each part matches:
- Lemma C.1(1), p. 71, is the minimum principle $s_k(\lambda^\uparrow(X)) = \min\operatorname{tr}(U^TXU)$.
  C.1(2), pp. 71–72, gets $\ell(M^{1/2}NM^{1/2}) \prec \ell(M) + \ell(N)$ from C4.
- The proof of Theorem 4.3, pp. 72–73, defines $F_w$ exactly as quoted. Its paragraph
  "Superadditivity" gives $F_w(\Sigma,\Sigma'') \ge F_w(\Sigma,\Sigma') + F_w(\Sigma',\Sigma'')$. Its
  paragraph "(1), causal curves end in the order" gives $g'(t) \ge \sum_i w_i^\downarrow\lambda_i^\uparrow(Y) \ge 0$.
- Theorem 4.3(1), p. 34, gives "a closed $\mathrm{GL}(d)$-invariant preorder, which is a partial order
  if and only if $C \cap (-C) = \{0\}$", so pointedness is not assumed. The prior-art paragraph,
  p. 35, says the proof is by majorization because "$S_K$ lies in $\mathrm{GL}(d)$, which is not
  connected". The referee's account is the paper's own.

**Action.** None.

## 4. § 3 item 4: Proposition 4.7, Lemma 4.8, Proposition 4.13 — CONFIRMED

**The report.** It calls the proofs complete and says the open converse (do ordered densities follow
from a positive increment for a general profile?) is stated accurately on pp. 43, 49 and 55.

**Against the PDF.**
- Proposition 4.7 is proved where it stands (p. 39).
- Lemma 4.8 (sketch p. 39) and Proposition 4.13 (sketch p. 43) both say "The complete proof is in
  Appendix C". `records/affine/PROOF-DRIFT.md` records that the Appendix C copies are the blueprint's
  proofs of record.
- The open converse is stated on p. 43 ("For a general profile it is open"), p. 46 ("for the others
  it is open whether (1) implies (2)"), p. 49 ("the open converse of Proposition 4.13") and p. 55
  (problem 1).

**Action.** None.

## 5. § 3 item 5: Propositions 4.10 and 4.11 — CONFIRMED

**The report.** It describes the proof of 4.11(1): C3 for infinite divisibility and
$(e^{-tB})_*\nu \le \nu$; radial smoothing by a compactly supported bump $\eta$, "so that no Haar
measure on $O(d)$ or radial density assumption on $\nu$ is needed"; differentiation along a least
eigenvector of $\operatorname{sym}B$, giving $\operatorname{tr}B\,M(r) + \lambda rM'(r) \le 0$; and
$\int_{|x|\le1}|x|^2\nu_\eta < \infty$, which forces $\operatorname{tr}B/\lambda < d+2$.

**Against the PDF.** Each step is on pp. 79–80:
- "By C3, $\mu$ and every $\rho_t$ are infinitely divisible … hence $(L_t)_*\nu \le \nu$".
- "Radial smoothing. Fix a smooth $\eta$ on $\mathbb R$ with … $\eta = 0$ off $(1/2,3/2)$". The page
  ends with "no Haar measure on $O(d)$ is needed".
- "tr $B\,M(r) + \lambda rM'(r) \le 0$ ($r > 0$)".
- "which is infinite if $\kappa \ge d+2$".

One detail the referee leaves out: the proof also excludes $\lambda < 0$, through the integrability of
$|x|^2 \wedge 1$ at large $|x|$. The statement (p. 40) has the constant $d+2$ and the strict
inequality, as quoted.

**Action.** None.

## 6. § 3 item 6: Theorem 4.21, Appendix C.4 — CONFIRMED

The report says only "thorough and correct". The complete proof (pp. 80–82) was read through. It is
the blueprint's proof of `thm:wedge-axis` (`blueprint/src/parts/05-table.tex`, lines 126–307), as
`records/affine/PROOF-DRIFT.md` records. Its first paragraph re-derives the order properties; that
is suggestion 6, item 13 below. **Action.** None.

## 7. § 3 item 7 and required change 6: Proposition 4.15 has only a sketch — CONFIRMED; Remark 4.16 answers part (ii)

**The report.** "On p. 44, Proposition 4.15 only has a 'Sketch', and … it has no complete proof in
Appendix B or Appendix C." It makes two points. (i) The sketch "abruptly switches Fourier transform
conventions to $\Phi(\xi) = \int e^{-2\pi i\langle x,\xi\rangle}\phi(x)dx$". (ii) It "asserts in one
phrase (*Testing with $\chi_0(x/N)\cos(2\pi\langle a,x\rangle)$ … gives $h(a) = c_0$*) the
approximate-identity step … without writing out why $\int\Phi_N(\xi)h(\xi)d\xi \to h(a)$". Required
change 6 asks that the complete proof be printed in the article.

**What the PDF prints.** On p. 44, Proposition 4.15, then "Sketch. The transform of the increment is
…", about 22 printed lines, ending "For the Matérn orbit, $g(cu)-g(u) = \gamma\log((1+cu)/(1+u)) \to
\gamma\log c$." No appendix proves 4.15. Appendix B (pp. 66–69) has no entry for it, and Appendix C
lists the statements it proves (pp. 69–70) without it. §1.1 (p. 6) and App. I (pp. 102–103) send the
reader to "the LaTeX sources deposited with this version".

**The blueprint.** `prop:log-orbit-rays` (`blueprint/src/parts/05-orbits.tex`) has a complete proof
of record, lines 1286–1350: 65 lines and about 630 words, in six labelled steps:
1. the increment's transform;
2. the blow-up, with the bound $h \le (\lambda_{\max}(\Sigma)/\lambda_{\min}(\Sigma'))^\kappa$;
3. "$\Lambda$ vanishes on test functions vanishing near 0", including the general-sign case by
   $(\phi + M\chi') - M\chi'$;
4. "$\Lambda$ is a multiple of the point mass", by $\psi := \phi - \phi(0)\chi_0$ and a cut-off $b$;
5. "$h$ is constant", which is the computation the referee asks for;
6. "The step is a ray".

It is `\leanok` and its route is the Lean's (`AffineHemigroup.LogOrbitRays`).

**(i) The $2\pi$ convention: CONFIRMED.** The convention appears only here in the paper:
`paper/05-orbits.tex`, lines 680 and 686. Everywhere else the paper uses $e^{i\langle\omega,x\rangle}$
with $(2\pi)^{-d}$ in the inversion:
- §2 (`02-line-papers.tex`, lines 58 and 187);
- the sketch of Lemma 4.8 on p. 39 itself;
- App. C (`appendix-wedge-axis.tex`, lines 522–523);
- App. E (`appendix-orbits.tex`, line 210).

The blueprint has the same convention at lines 1289–1334: it is Mathlib's normalization, which the
Lean proof uses. It is a test-function transform, not the characteristic function, so nothing is
wrong. But the sketch does not say why the convention changes. Nothing depends on it: with
$\Phi(\xi) := \int e^{-i\langle x,\xi\rangle}\phi$ and $\phi = (2\pi)^{-d}\int\Phi e^{i\langle\xi,\cdot\rangle}$
one gets $\int\phi(x/R)\rho(dx) = (2\pi)^{-d}\int\Phi(\xi)\widehat\rho(\xi/R)d\xi$, and the test
function becomes $\chi_0(x/N)\cos\langle a,x\rangle$.

**(ii) The approximate-identity step: CONFIRMED that it is compressed; the sketch is correct.** The
blueprint's step 5 computes the transform of $\phi_N$ as
$\frac{N^d}2(\Phi_0(N(\xi-a)) + \Phi_0(N(\xi+a)))$ and substitutes $\xi = \pm a + \eta/N$. Dominated
convergence then applies: $h$ is bounded and continuous at $\pm a \ne 0$, and $\Phi_0$ is integrable.
The limit is $\frac12(h(a)+h(-a))\int\Phi_0 = h(a)\chi_0(0) = h(a)$, using that $h$ is even. This
checks, and the sketch's one-line assertion is true. The sketch compresses one more step, "By
positivity, $\Lambda(\phi) = c_0\phi(0)$", which is the blueprint's step 4. "Positivity" alone does
not give it: it needs the $\psi = \phi - \phi(0)\chi_0$ cut-off argument.

**Remark 4.16 (`rem:log-orbit-crum`).** It is in this build, on p. 45, and it answers (ii) in
substance. It replaces the whole functional argument (steps 3–5) with a published one:
1. $h$ is a pointwise limit of characteristic functions, so it is measurable and positive definite
   ([51], Thm. 1.4.10).
2. A measurable positive-definite function equals a continuous one $f_c$ almost everywhere (Crum
   [10]; [51], Thm. 2.11.7).
3. $h$ is continuous off $0$, so $h = f_c$ off $0$; two continuous functions equal almost everywhere
   on an open set agree there.
4. $f_c$ is homogeneous of degree 0 off 0 and continuous at 0, hence constant.

The argument is correct and needs neither the $2\pi$ convention nor the approximate identity. Both
sources have reading notes (`records/affine/READING-crum1956positive.md`,
`READING-sasvari2013multivariate.md`). It does not by itself meet required change 6, for three
reasons:
- the remark is framed as "a second, published route", not as the proof;
- the steps before it in the sketch stay compressed;
- it rests on literature outside C1–C4, so a proof through it is not the proof of record that the
  Lean checks.

**Fix.** Three options:
- **(a)** Print the blueprint's proof verbatim in Appendix B, under "Proof of Proposition 4.15". This
  costs about 630 source words, about 0.9 printed page. The main-text sketch stays as is, with
  "The complete proof is in Appendix B" added, as for Lemma 4.8; or it is replaced by a pointer,
  and the net cost is about +0.6 page. With the conversion of (i), the blueprint and paper copies
  stay verbatim.
- **(b)** Print a complete proof by the route of Remark 4.16. Write the blow-up (sketch lines 1–4)
  in full, about 4 lines, then cite the remark's argument for "$h$ is constant". This costs nothing
  net (the remark is absorbed), but the printed route then differs from the proof of record.
- **(c), alone and in any case.** Convert the sketch's transform to the paper's convention, or add
  "(the normalization of the formal proof; used only here)".

(c) is **safe**: a notation fix in paper prose. Done in the blueprint too, it is also safe: notation
only, and the route is unchanged. Choosing between (a) and (b), and whether to print at all, is
**author**: which proofs are printed, and the choice between two routes. (a) keeps the printed proof
and the checked proof the same.

## 8. § 3 item 8, first bullet, and required change 9: the $Q$/$R$/$Q'$ mix-up in Proposition H.5 — CONFIRMED (and it is in the blueprint and in a Lean docstring)

**The report.** Proposition H.5(1) (p. 97) "quantifies *For $c > 0$ and $Q \in O(d)$*, but then
writes $\operatorname{rs}((cR)_*L) = \operatorname{rs}(L)$, $\operatorname{es}(\psi(cR\,\cdot)) =
\operatorname{es}(\psi)$ and $\mathcal M_s((cR)_*L) = c^2Q\,\mathcal M_{s/c}(L)\,Q^T$". The sketch
(p. 98) repeats it: "$x \mapsto cRx$; … $Q'_*L_\Sigma \le L_I \le \theta^{-1}L_\Sigma$ with $Q'$
undefined; … *its invariance under the $Q'$ with $Re_1 = \pm e_1$*".

**What the PDF prints.**
- p. 97, clause (1): "For $c > 0$ and $Q \in O(d)$, $\operatorname{rs}((cR)_*L) = \operatorname{rs}(L)$,
  $\operatorname{es}(\psi(cR\,\cdot)) = \operatorname{es}(\psi)$ and $\mathcal M_s((cR)_*L) = c^2Q\,\mathcal M_{s/c}(L)\,Q^T$."
  These are lines 1–2 of the clause, not of the page, but they are as quoted.
- p. 98, the sketch: "(1) … $\mathcal M_s((cR)_*L) = c^2Q\mathcal M_{s/c}(L)Q^T$ by the substitution
  $x \mapsto cRx$"; "(2), (3). … $Q'_*L_\Sigma \le L_I \le \theta^{-1}L_\Sigma$"; "(4). … its
  invariance under the $Q'$ with $Re_1 = \pm e_1$".

**Diagnosis.** The slip comes from an incomplete rename. The blueprint's comment above the node
(`05-smaller-groups.tex`, lines 1494–1495) reads: "CHANGED Q-0327: notation only …: the rotation is
$Q$ (and $Q'$ for a second one), no longer $R$, which is the dilation ratio of prop:orbit-step-cone".
The rename left $R$ in four places:

| Where | Lines | What is printed or written |
|---|---|---|
| blueprint, shared statement | 1522–1523 | `\operatorname{rs}((cR)_*L)`, `\psi(cR\,\cdot)`, `\mathcal M_s((cR)_*L)` |
| blueprint, proof of record, clause (1) | 1586, 1589 | "Conjugation $Q \mapsto Q'^{-1}RR'$" (garbled: it should be $Q'^{-1}QQ'$) and $\frac{Rxx^{T}Q^{T}}{\lvert x\rvert^2}$ |
| blueprint, proof of record, clause (4) | 1622–1623 | "$Q'\mathcal M_s(\cdot)Q'^{T} = \mathcal M_s(\cdot)$ whenever $Re_1 = \pm e_1$" |
| paper, shared statement (re-transcribed) | `appendix-similarity-loewner.tex` 278–279 | as in the blueprint |
| paper, sketch (a deliberately edited copy) | 319, 327, 331 | "$x \mapsto cRx$"; "$Q'_*L_\Sigma \le \dots$" without "for every $Q' \in O(d)$"; "the $Q'$ with $Re_1 = \pm e_1$" |
| Lean docstring of `anisotropy_functionals` | `Formalization/AffineHemigroup/SimilarityBounded.lean` 556–557 | "`Q ∈ O(d)`, `rs((cQ)_*L) = rs(L)`, `es(ψ(cQ·)) = es(ψ)` … and `𝓜_s((cR)_*L) = c²R𝓜_{s/c}(L)Rᵀ`": the docstring mixes $Q$ and $R$; the Lean statement binds `R` throughout and is consistent |

Read with $R = Q$, every identity is true. With $(c^2|x|^2)\wedge s^2 = c^2(|x|^2 \wedge (s/c)^2)$,
$\mathcal M_s((cQ)_*L) = \int(c^2|x|^2\wedge s^2)\,\frac{Qxx^TQ^T}{|x|^2}L(dx) = c^2Q\,\mathcal M_{s/c}(L)\,Q^T$.
The $R$ of Proposition H.4(4) (p. 97, statement and sketch) is bound by its own quantifier ("every
$R \in O(d)$ with $Re_1 = \pm e_1$") and is not a slip. It does reuse the letter that H.2 gives the
dilation ratio, which is what Q-0327 meant to remove.

**Fix.**
1. Blueprint statement, clause (1): $(cR) \to (cQ)$ three times.
2. Blueprint proof: "For $Q' \in O(d)$, conjugation $Q \mapsto Q'^{-1}QQ'$"; $(cR)_*L \to (cQ)_*L$
   and $Rxx^{T}Q^{T} \to Qxx^{T}Q^{T}$; "whenever $Q'e_1 = \pm e_1$".
3. Paper: re-transcribe the statement and re-pin; in the sketch, $x \mapsto cQx$, "and, for every
   $Q' \in O(d)$, $Q'_*L_\Sigma \le \dots$", and "the $Q'$ with $Q'e_1 = \pm e_1$".
4. Lean docstring (line 557): `𝓜_s((cQ)_*L) = c²Q𝓜_{s/c}(L)Qᵀ`, or `R` throughout to match the binder.
5. Optionally, in H.4(4) and its sketch: $R \to Q'$.

**safe**: a notation slip, no claim changes. **Where**: a shared statement and a proof of record, so
blueprint first, then re-transcribe (`adr/0004`); paper sketch; Lean docstring.

## 9. § 3 item 8, second bullet: Appendix H is sketches only; the Bernoulli step of H.1(3); the countable additivity in H.4(4) — PARTLY

**The report.** "Propositions H.1, H.2, H.4, H.5, H.6, H.7, and H.8 (pp. 94–101) are all printed with
*Sketch* proofs only." It names two routine verifications that are "compressed":
- the Bernoulli step of H.1(3), "showing that $\frac{1+d\kappa}{\kappa(1+\kappa)} \le
  \frac{d+\alpha}{d}\frac{\kappa}{1+\kappa}$ is equivalent to $\alpha\kappa^2 - (d+1)\kappa - 1 \ge 0$";
- "the countable additivity of the rank-one limit $L_*$ in Proposition H.4(4)".

**Sketches only: CONFIRMED.** H.1 (p. 94), H.2 (p. 95), H.4 (p. 97), H.5 (p. 98), H.6 (p. 99), H.7
(p. 100) and H.8 (p. 101) are headed "Sketch". H.9 has a complete proof (`appendix-similarity-loewner.tex`,
line 612). The blueprint lengths are in the table of item 10.

**The Bernoulli step: the compression is CONFIRMED; the referee's inequality is wrong.** The paper's
sketch (p. 95; `appendix-similarity-loewner.tex`, lines 87–97) reads: "$\lambda_{\min}(M) \ge
1 + \kappa u/(1+\kappa)$ and $\operatorname{tr}M \le d + (1+d\kappa)u/\kappa$ … give $\det M \le
(\operatorname{tr}M/d)^d \le (1 + \frac{d+\alpha}d\frac{\kappa u}{1+\kappa})^d \le
\lambda_{\min}(M)^{d+\alpha}$ under the condition on $\kappa$". The middle inequality needs
$$\frac{1+d\kappa}{d\kappa} \le \frac{d+\alpha}{d}\,\frac{\kappa}{1+\kappa}
\iff (1+d\kappa)(1+\kappa) \le (d+\alpha)\kappa^2 \iff \alpha\kappa^2 - (d+1)\kappa - 1 \ge 0 ,$$
which is the paper's condition exactly. The last inequality is Bernoulli,
$(1+x)^{(d+\alpha)/d} \ge 1 + \frac{d+\alpha}d x$ for $x = \kappa u/(1+\kappa) \ge 0$. The two bounds
on $M$ check:
- $\operatorname{tr}(H^{-1}P) \le \operatorname{tr}P/(\kappa\tau) = u/\kappa$ and
  $\kappa\operatorname{tr}(P)\operatorname{tr}H^{-1} \le du$;
- $\lambda_{\min}(M) \ge 1 + \kappa\operatorname{tr}P/\lambda_{\max}(H) \ge 1 + \kappa u/(1+\kappa)$.

The referee's left-hand side, $\frac{1+d\kappa}{\kappa(1+\kappa)}$, is not the paper's. Multiplied
through, the referee's inequality is $(d+\alpha)\kappa^2 - d^2\kappa - d \ge 0$, which is **not**
equivalent to the paper's condition. At $d = 2$, $\alpha = 1$, $\kappa = 2$ the referee's inequality
holds ($12 - 8 - 2 = 2 \ge 0$), while $\alpha\kappa^2 - (d+1)\kappa - 1 = -3 < 0$ (checked with
sympy). The paper is right. Its sketch skips the intermediate bound $(1 + Au/d)^d$, with
$A := (1+d\kappa)/\kappa$, and does not say that the condition is $A \le (d+\alpha)B$, with
$B := \kappa/(1+\kappa)$. The blueprint's proof of record (`05-smaller-groups.tex`, lines 1197–1208)
writes both out.

**The countable additivity in H.4(4): CONFIRMED that it is compressed; the sketch is correct.** The
sketch reads "it converges, countably additively, and the limit extends to a Lévy measure below every
$L_{\Sigma_\varepsilon}$". The blueprint (lines 1450–1460) gives the argument:
- on $\{|x| \ge \delta\}$, $\sum_nL_{\Sigma_\varepsilon}(B_n)$ has terms dominated by $L_I(B_n)$, with
  $\sum_nL_I(B_n) < \infty$, so the limit of the sum is the sum of the limits;
- $L_*(B) := \lim_{\delta\downarrow0}L_*(B_\delta)$, an increasing limit of measures;
- $\int(|x|^2\wedge1)dL_* \le \int(|x|^2\wedge1)dL_I$.

This is correct.

**Fix.**
- **Safe**, paper prose, in the sketch of H.1(3): add "The condition on $\kappa$ is
  $(d+\alpha)\kappa^2 \ge (1+d\kappa)(1+\kappa)$, that is
  $(1+d\kappa)/\kappa \le (d+\alpha)\kappa/(1+\kappa)$, so
  $\operatorname{tr}M/d \le 1 + \frac{d+\alpha}d\frac{\kappa u}{1+\kappa}$", about one line, before
  the display.
- **Safe**, paper prose, in the sketch of H.4(4): "on a shell $\{|x| \ge \delta\}$ the terms are
  dominated by the summable $L_I(B_n)$", half a line.

The sketches are deliberately edited copies, so `linkage check --pin-shared` re-pins them. Printing
the complete Appendix H proofs is item 10, and **author**.

## 10. § 5 item 5: proofs that the PDF prints only as sketches — CONFIRMED

**The report.** It says that §1.1 (p. 6) and App. I (p. 103) "state that for propositions printed with
a *Sketch* and no appendix proof, the complete prose proof is in the deposited LaTeX sources", and
that "a journal paper must stand on its own".

**What the PDF prints.**
- p. 6: "A proof headed 'Sketch' shows the decisive steps, and its complete proof is in an appendix or
  in the LaTeX sources deposited with this version."
- pp. 102–103: "Where an appendix gives the complete proof, the sketch says so; for the others it is
  in the LaTeX sources deposited with this version".
- The data and code availability statement (`paper/declarations.tex`, lines 17–23) says the
  deposited sources "hold the complete proofs of the statements whose proofs are sketched here".

The fact is as the referee states it.

**Sketched, with a complete proof elsewhere in the PDF.** These are not part of the finding:
- Lemma 4.8 (sketch p. 39) and Proposition 4.13 (sketch pp. 42–43), complete in App. C.3;
- Theorem 4.21 (sketch §4.7, pp. 49–50), complete in App. C.4;
- Proposition 4.20(1)–(2), complete in App. C.3, and 4.11(1), in App. C.3;
- Proposition E.1(1), whose sketch is its complete proof (p. 70: "whose short proof is in Appendix E").

**Sketched, with no complete proof anywhere in the PDF.** 22 statements. The complete proof of each
is in the blueprint:

| # | Statement | Label | Sketch on p. | Paper sketch (words) | Blueprint proof of record | Lines / words | ≈ printed pages |
|---|---|---|---|---|---|---|---|
| 1 | Prop. 4.15 | `prop:log-orbit-rays` | 44 | 198 | `05-orbits.tex` 1286–1350 | 65 / 630 | 0.9 |
| 2 | Prop. 4.19 | `prop:bounded-profile-rays` | 46 | 63 | `05-orbits.tex` 1523–1550 | 28 / 252 | 0.35 |
| 3 | Prop. A.3 | `prop:isotropic-corner` | 62 | 641 | `04-classical.tex` 945–1052 | 108 / 1316 | 1.9 |
| 4 | Lemma A.5 | `lem:parameter-space` | 64 | 541 | `04-classical.tex` 1166–1259 | 94 / 1162 | 1.7 |
| 5 | Prop. 4.4 | `prop:affine-orbits` | 67 (App. B) | 197 | `05-orbits.tex` 97–165 (+ `prop:affine-orbits-matern`, 193–196) | 64 / 474 | 0.7 |
| 6 | Lemma 4.14 | `lem:dilation-ratio` | 68 (App. B) | 316 | `05-orbits.tex` 955–1021 | 65 / 730 | 1.0 |
| 7 | Prop. 4.18 | `prop:rational-symbols` | 69 (App. B) | 117 | `05-orbits.tex` 1451–1477 | 27 / 293 | 0.4 |
| 8 | Prop. 4.20(3)–(5) | `prop:similarity-stable-order-families` | 69 (App. B) | 341 | `05-smaller-groups.tex` 2393–2547, clauses (3)–(5) from about 2474 | ~73 / ~720 | 1.0 |
| 9 | Prop. D.1 | `prop:glplus-families` | 83 | 375 | `05-landscape.tex` 144–224 | 81 / 964 | 1.4 |
| 10 | Prop. E.1 (2)–(4) | `prop:tempered-step-cone` | 85 | 231 | `05-orbits.tex` 1116–1209 | 93 / 751 | 1.1 |
| 11 | Prop. E.4 | `prop:matern-negative-mass` | 87 | 121 | `05-orbits.tex` 1875–2001 (+ `lem:matern-kernel-hessian`, 1665–1724) | 127 / 1214 | 1.7 (+0.6) |
| 12 | Prop. F.2 | `prop:fixed-frame-families` | 88 | 203 | `05-smaller-groups.tex` 247–295 | 49 / 472 | 0.7 |
| 13 | Prop. F.3 | `prop:similarity-ray-families` | 90 | 244 | `05-smaller-groups.tex` 565–625 | 61 / 755 | 1.1 |
| 14 | Prop. F.4 | `prop:diagonal-ray-families` | 91 | 192 | `05-smaller-groups.tex` 703–762 | 60 / 681 | 1.0 |
| 15 | Prop. F.5 | `prop:diagonal-stable-order-families` | 92 | 199 | `05-smaller-groups.tex` 2721–2800 | 78 / 850 | 1.2 |
| 16 | Prop. H.1 | `prop:similarity-stable-family` | 94 | 272 | `05-smaller-groups.tex` 1164–1223 | 59 / 570 | 0.8 |
| 17 | Prop. H.2 | `prop:similarity-orbit-family` | 95 | 179 | `05-smaller-groups.tex` 1300–1340 | 40 / 429 | 0.6 |
| 18 | Prop. H.4 | `prop:similarity-general-sandwich` | 97 | 152 | `05-smaller-groups.tex` 1422–1477 | 56 / 568 | 0.8 |
| 19 | Prop. H.5 | `prop:similarity-general-bounded-shape` | 98 | 176 | `05-smaller-groups.tex` 1584–1633 | 50 / 526 | 0.75 |
| 20 | Prop. H.6 | `prop:similarity-degenerate-family` | 99 | 296 | `05-smaller-groups.tex` 1723–1826 | 100 / 930 | 1.3 |
| 21 | Prop. H.7 | `prop:similarity-line-family` | 100 | 408 | `05-smaller-groups.tex` 1898–2035 | 131 / 1540 | 2.2 |
| 22 | Prop. H.8 | `prop:similarity-general-index-zero` | 101 | 126 | `05-smaller-groups.tex` 2095–2147 | 50 / 505 | 0.7 |

Totals: the blueprint proofs come to about 16,300 words, the paper's sketches of the same statements
to about 5,600. Printing every complete proof in place of its sketch would add about 10,700 words,
about **15 pages**, to a paper the same report asks to cut from 108 pages to 45–55. Only two of the
22 are in the main text (4.15 and 4.19), and five more are main-text statements proved in App. B
(4.4, 4.14, 4.18, 4.20(3)–(5)). The other 15 are in the supplementary appendices D–H, which the report
itself suggests moving to Electronic Supplementary Material. Proposition 4.19's sketch is short
because it is assembled from 4.13(2)–(3), 4.15 and Lemma 2.9(2). Once 4.15 is complete, it
lacks only the line "$c \ge 1$ as in the proof of Proposition 4.18".

**Fix.**
- **Safe**, paper prose: name where the complete proofs are, by citable reference. Give the deposit's
  DOI and the blueprint file and node label, or a published blueprint web page per node, so that "the
  LaTeX sources" becomes an addressable place. Also confirm at release that the public verification
  export contains `blueprint/src/`, which the comment in `paper/appendix-verification.tex` does not
  say.
- **Author**: which complete proofs to print. A defensible line is the main-text statements (4.15,
  then 4.19, 4.4, 4.14, 4.18, 4.20(3)–(5)), about 5 pages, with Appendices D–H staying sketched if
  they move to supplementary material. That is a decision about the structure.

## 11. § 7: the proof of Theorem 3.5(3)(c) refers forward to Proposition 4.7(2) — PARTLY (forward in numbering only; not circular, and harmless)

**The report.** The proof of Theorem 3.5(3)(c) (p. 65) "Relies on a forward reference to Proposition
4.7(2) (p. 38) for the fact that $\le_{\mathcal K_\alpha}$ is a partial order". It lists this among
the "load-bearing forward references".

**What the PDF prints.** The proof is on p. 65 (Appendix A.5), and Proposition 4.7 is on p. 38, so in
the order of reading the reference points *back*. Only the numbering, 3.5 before 4.7, makes it look
forward. The sentence (p. 65) is: "That the relation of $\mathcal K_\alpha$ is one is Proposition
4.7(2), proved without this theorem." The text already says the point that matters.

**Circularity.** There is none:
- In the blueprint, `thm:cascade-infinitely-divisible` `\uses` `lem:stable-step-order`
  (`04-classical.tex`, line 1355). That node is the matrix-analysis part of `prop:stable-step-cone`
  (clause (2)'s order, read from the pointwise order of densities), and it `\uses` only
  `lem:elliptical-stable-density` and `lem:loewner-scale-shape` (`05-orbits.tex`, line 668). Neither
  uses Theorem 3.5.
- In the PDF, the proof of Prop. 4.7(2) (p. 39) reads "Transitivity is that of (b), antisymmetry that
  of the Loewner order", with no appeal to Theorem 3.5.

**Fix.** None needed. Optionally, as **safe** paper prose, make it self-contained in one line:
"$\le_{\mathcal K_\alpha}$ is transitive because the stable densities of (4.1) are ordered pointwise
along it, and antisymmetric because it lies in the Loewner order (Proposition 4.7(1)–(2))". The
pointer stays.

## 12. § 7 and required change 7: Proposition 4.20's statement depends on Appendix H's definitions — CONFIRMED (mitigated in the prose before it); cheap to fix

**The report.** The preamble of Proposition 4.20 says "use the functionals $\operatorname{es}$,
$\mathcal M_s$, $T_s$ and $\operatorname{cond}$ of Proposition H.5"; clause (3) says the family "is a
family as in Proposition H.4"; clause (4) says "with $\psi_\Sigma$ as in Proposition H.4". "A formal
proposition in the main text should be self-contained".

**What the PDF prints.** pp. 46–47, as quoted (`paper/05-orbits.tex`, lines 834–835, 865, and the
$\psi_\Sigma$ of clause (4)). Mitigations:
- The paragraph before the statement (p. 46) defines $\operatorname{es}$ in words ("the least
  $K \ge 1$ with $\psi(Q\omega) \le K\psi(\omega)$ for every $Q \in O(d)$ and every $\omega$").
- The statement itself defines $\operatorname{ecc}$.
- The paragraph says the others "are defined with Proposition H.5 in Appendix H".

**Against the statement.** The dependence is real. Clause (4)'s $\operatorname{cond}\mathcal M_s(L_\Sigma)$
and $\psi_\Sigma$, and clause (3)'s "family as in Proposition H.4", which packs the triplet
$(C(\Sigma),L_\Sigma,0)$, the symmetric infinitely divisible laws and similarity covariance, are
defined only on pp. 96–97. One item is even free: $T_s$ is named in the preamble but used nowhere in
the statement; only the proof (p. 69) uses it.

**Cost of making it self-contained.** About six printed lines:
- $\psi_\Sigma(\omega) := \int(1-\cos\langle\omega,x\rangle)L_\Sigma(dx)$, half a line;
- $\mathcal M_s(L) := \int(|x|^2\wedge s^2)\frac{xx^T}{|x|^2}L(dx)$, one inline or displayed line;
- $\operatorname{cond}M := \lambda_{\max}(M)/\lambda_{\min}(M)$, half a line;
- $\operatorname{es}$, one line, moved from the prose into the preamble;
- in clause (3), "(a family as in Proposition H.4)" becomes "with $(\sqrt c\,Q)_*\mu_\Sigma =
  \mu_{cQ\Sigma Q^T}$ for $c > 0$ and $Q \in O(d)$"; the triplet is already in the clause;
- $T_s$ is dropped.

The pointer "(these are the functionals of Proposition H.5)" can stay, for the reader who goes on.

**Fix.** Restating definitions changes nothing claimed, so the fix is **safe**. **Where**: the
statement is shared (`% shared with blueprint prop:similarity-stable-order-families`; blueprint
`05-smaller-groups.tex`, lines 2291–2330). It is changed in the blueprint and re-transcribed, and the
prose before it (paper only) loses the definition that moves.

## 13. Suggestion 6: Appendix C.4 re-proves parts of Theorem 4.3(4) and Proposition 4.12(1) — PARTLY (one repetition, deliberate, and load-bearing for the trust base)

**The report.** "Shorten the proof of Theorem 4.21 in Appendix C.4 by citing Theorem 4.3(4) and
Proposition 4.12(1) … rather than re-proving from scratch that $\preceq_C^+$ is a
$\mathrm{GL}(d)$-invariant partial order."

**What the PDF prints.** The paragraph "The orders." of the proof (pp. 80–81) opens: "The proof reads
of $\preceq_C$ and $\preceq_C^+$ only what the causal curves give directly." It then proves:
- reflexivity, and transitivity by concatenating causal curves;
- $\mathrm{GL}(d)$-invariance;
- antisymmetry ("Its antisymmetry is that of Theorem 4.3(4), and the causal curves give it
  directly"), through the monotonicity of $\det\gamma$ and the last sentence of Lemma C.1(4).

This is about 40 printed lines.

**Theorem 4.3(4): the repetition is CONFIRMED, and it is deliberate.** The conclusion is that of
Theorem 4.3(4) (p. 34), reached by another route. Theorem 4.3 runs through the functionals $F_w$ and
Lemma C.1(2), which spends **C4**. Appendix I says so (p. 103): "C4: … Lemma C.1, for its clause (2)
… and through it Theorem 4.3, for its clauses (1), (2) and (4)". It does not list C4 for
Theorem 4.21. The blueprint records the decision above `thm:wedge-axis` (`05-table.tex`, lines 30–33):
"CHANGED Q-0281 wave 2: entry-free route (the author's decision on W2F-1). … the orders are read
through prop:stable-order-generated and the causal curves, without ledger A9", A9 being C4. Citing
Theorem 4.3(4), as suggested, would put C4 into the trust base of the paper's main theorem, and the
Lean (`wedge_axis_*`) would no longer match the printed route.

**Proposition 4.12(1): REFUTED.** C.4 does not re-prove it. It cites it ("By Proposition 4.12(1),
$\preceq^+_{C_\gamma}$ is the order $\le_\gamma$", "by Proposition 4.12(1), $I \preceq_{C_0} e^X$
would make …", in (1), (2)(c) and (3)), and it cites facts (a)–(c) of its proof. Clause (1) of the
theorem (the strict chain $C_\alpha \subsetneq C_\beta$) is the theorem's own clause, not
Proposition 4.12's.

**Fix.** Do not shorten by citation. Two **safe** options:
- add to "The orders." the reason, in paper prose that also goes into the blueprint proof, which is
  shared (`% proof of thm:wedge-axis`): "so that the theorem does not rest on C4, which Theorem 4.3
  spends through Lemma C.1(2)";
- say it in App. I.

Shortening at the cost of adding C4 to Theorem 4.21's trust base would reverse an author's decision
(W2F-1), so it is **author**.

## 14. § 3 item 9: the cited facts C1–C4 are used within their hypotheses — CONFIRMED (spot-checked)

The report asserts this without detail. Spot checks:
- **C1** in Theorem 3.5(1) (p. 65): a null array, all row products equal to $\mu_{s,t}$, $b_n = 0$.
  Within the hypotheses of Theorem 2.10.
- **C3** in Proposition 4.11(1) (p. 79): $e^{-tB} \to 0$ is the clause's hypothesis. In Theorem
  4.21(2)(c) (p. 82), C3 is reached through 4.11(1) with $B = X/2$ positive definite, so
  $e^{-tB} \to 0$.
- **C2**(ii)–(iii) in Lemma 4.8 and Proposition 4.7 (b)$\Rightarrow$(a) (p. 39), and in H.4(1).
- **C4** in Lemma C.1(2) (p. 71), in its weak, partial-sum form, as §2.4 states it (p. 13).

No invocation outside a hypothesis was found. Not every invocation was checked; the trust-base
verifier covers the ledger.

---

## Summary

| # | Finding | Verdict | Fix | Class | Where |
|---|---|---|---|---|---|
| 1 | § 3.1 Thms 3.6/3.7/3.12, Lemmas 3.8–3.10, A.1–A.2: descriptions | CONFIRMED | none | — | — |
| 2 | § 3.2 Thm 3.5: description | CONFIRMED | none | — | — |
| 3 | § 3.3 Prop 4.2, Lemma C.1, Thm 4.3, Prop 4.12: description | CONFIRMED | none | — | — |
| 4 | § 3.4 Prop 4.7, Lemma 4.8, Prop 4.13; the open converse | CONFIRMED | none | — | — |
| 5 | § 3.5 Props 4.10, 4.11: description (constant $d+2$) | CONFIRMED | none | — | — |
| 6 | § 3.6 Thm 4.21, App. C.4 | CONFIRMED | none (see 13) | — | — |
| 7 | § 3.7 / RC 6: Prop 4.15 has only a sketch; $2\pi$ convention; approximate identity | CONFIRMED (sketch correct; Remark 4.16 gives a complete published route for "$h$ constant", but not the proof of record) | (c) convert the transform to the paper's convention, or flag it; (a) print the blueprint proof (~0.9 p) in App. B, or (b) a complete proof through Remark 4.16 (~0 p net) | (c) safe; (a)/(b) author | paper sketch (`05-orbits.tex` 680, 686), optionally the blueprint proof; App. B |
| 8 | § 3.8 / RC 9: $Q$/$R$/$Q'$ in Prop H.5(1) and its sketch | CONFIRMED; also in the blueprint statement and proof of record (incl. "$Q'^{-1}RR'$") and the Lean docstring | $R \to Q$; "for every $Q' \in O(d)$"; "$Q'e_1 = \pm e_1$"; docstring made consistent | safe | blueprint `05-smaller-groups.tex` 1522–1523, 1586, 1589, 1622–1623, re-transcribed; paper sketch 319, 327, 331; `SimilarityBounded.lean` 557 |
| 9 | § 3.8: App. H sketches only; H.1(3) Bernoulli step; H.4(4) countable additivity | PARTLY: sketches only, CONFIRMED; the paper's condition is right and the referee's stated equivalence is wrong (not equivalent: $d=2$, $\alpha=1$, $\kappa=2$); both steps correct but compressed | one line in the H.1(3) sketch ($A \le (d+\alpha)B$); half a line in H.4(4) | safe | paper sketches (`appendix-similarity-loewner.tex` ~90–96, 243–245), re-pinned |
| 10 | § 5.5: sketched statements with no complete proof in the PDF | CONFIRMED: 22 statements (2 in the main text, 5 in App. B, 15 in Apps. D–H); the blueprint has every complete proof, ~16,300 words, ~+15 pages net | address the deposited proofs citably (DOI plus node labels); choose which complete proofs to print (main-text ones ≈ 5 pages) | addressing: safe; printing: author | §1.1, App. I, declarations; App. B |
| 11 | § 7: Thm 3.5(3)(c) refers forward to Prop 4.7(2) | PARTLY: forward only in numbering (proof on p. 65, after p. 38); not circular (`lem:stable-step-order` uses neither 3.5 nor its consequences); the text already says "proved without this theorem" | none; optionally a one-line self-contained reason | safe (optional) | paper App. A.5 (`appendix-classical.tex` 658) |
| 12 | § 7 / RC 7: Prop 4.20 uses Appendix H's definitions | CONFIRMED, mitigated by the prose definition of es; $T_s$ is named and unused | define $\psi_\Sigma$, $\mathcal M_s$, cond, es in the preamble; restate H.4's covariance in clause (3); drop $T_s$ (~6 lines) | safe | shared statement: blueprint `05-smaller-groups.tex` 2291–2330, re-transcribed (`05-orbits.tex` 834–865) |
| 13 | Suggestion 6: C.4 re-proves Thm 4.3(4) and Prop 4.12(1) | PARTLY: Thm 4.3(4)'s conclusion is re-derived, deliberately, to keep C4 out of Thm 4.21 (W2F-1); Prop 4.12(1) is cited, not re-proved | do not shorten by citation; state the reason in one sentence | sentence: safe; shortening: author | blueprint proof of `thm:wedge-axis` (`05-table.tex` 147), re-transcribed (`appendix-wedge-axis.tex` 779); or App. I |
| 14 | § 3.9: C1–C4 used within their hypotheses | CONFIRMED (spot-checked C1, C2, C3, C4) | none | — | — |
