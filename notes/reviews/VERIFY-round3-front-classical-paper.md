# Verification of the content review, round 3 (the affine paper, `review-3`): reports A (§§ 1–2) and B (§ 3 and Appendix A)

*2026-11-03. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is checked
against the text, the blueprint and the sources before anything changes. This record verifies
reports A and B of the five blind Claude Fable 5.1 referees of round 3:
`review-content-review-3-A-sections-1-2-claude-fable-5.1.md` (10 required changes, 15 suggestions)
and `review-content-review-3-B-section-3-appendix-A-claude-fable-5.1.md` (6 required changes, 12
suggestions), with every claim of their sections 2–7 that asserts an error, a gap, a missing
qualification, an overclaim or a wrong or missing attribution. Reports C, D and E are verified
elsewhere; where they repeat a finding of A or B, that is noted (§ C below) and their own findings are
not verified here. This record changes no `.tex`, `.lean` or blueprint file.*

## Inputs and conventions

- **The build.** `review-build-review-3.pdf`, 110 pages, the revision `59c56bd`;
  `git diff 59c56bd HEAD -- paper blueprint` changes only `paper/references.bib` (two `publisher`
  fields), so the sources read at `HEAD` are the build's. `paper/main.pdf` is no longer the frozen
  build (`cmp` differs, the bibliography); the frozen PDF was read. Page numbers are printed = PDF
  (p. 1 prints 1, p. 104 prints 104). Text: `pdftotext -layout`; pp. 16–17 also rendered.
- **Scripts**, in `verify-round3-paper-scripts/` (the directory is shared with the verifiers of C–E;
  mine are these four), each with its `-output.txt`:
  `front_classical_phrases.py` (where each quoted phrase is in the build), `k2_boundary_family.py`
  (B's family showing (K2) is needed only at the boundary), `delta_at_pd_family.py` (B's similarity
  family with $\delta_0$ at a positive definite aperture), `singular_base_step.py` (a rank-deficient
  step from a singular base). Read but not mine: `sketched_statements-output.txt` (lengths of the
  twenty sketches against their blueprint proofs).
- **Sources** (librarian CLI, `library resolve | search | page | get`, read-only role): Lindeberg–Gårding
  1997 [37] (`lindeberg1997shape`; the held copy is the 33-page KTH report, printed = PDF), Weickert–
  Ishikawa–Imiya [59] p. 241, Weickert 1998 [58] pp. 13–14, Lindeberg 2011 [34] p. 45, Bhatia [4]
  p. 73, Kelker [30] p. 423, Wendel 1952 p. 252, Larsen 1971 Thm. 0.1.1, Meerschaert–Scheffler
  pp. 33–34, Jurek–Mason pp. 59–60. Not held: Billingsley 1966, Nitzberg–Shiota 1992 (`library search
  --corpus` finds neither). Existing reading notes consulted: `READING-wendel1952left.md`,
  `READING-larsen1971introduction.md`, `READING-lindeberg1997shape*.md`, `READING-hudson1981operator.md`,
  `READING-holmes1982operator.md`, `READING-meerschaert2001limit.md`.
- **Lean and trust base read**: `Formalization/AffineHemigroup/IsotropicCorner.lean`, `Upstream.lean`,
  `Interfaces.lean`, `IsoAxiomGuard.lean`, `CIAxiomGuard.lean`, the ScaleSpaceCore package
  (`Gauge.lean`, `AxiomCheck.lean`), `blueprint/trust-boundary.txt`, `Formalization/README.md`. No Lean
  toolchain is installed in this session: axiom statuses are the guard files' recorded expectations,
  not a fresh run.
- **Rules read.** `CLAUDE.md`; `.claude/rules/article-kit/core.md`, `writing.md`, `blueprint.md`,
  `ledger.md`, `lean.md`; `adr/0003`–`0006`; `records/affine/PLAN-review-response-paper.md` §§ 0 and
  R2.0 (D1–D9); `records/affine/PRIOR-ART-positioning.md` row A and § 7; `records/affine/NODES-q0457.md`.
- **Verdicts.** **CONFIRMED**: holds as stated. **PARTLY**: part holds, part not (both said).
  **REFUTED**: the paper is right, and why.
- **Classes.** **safe**: a change a session may make under `adr/0003` (narrowing, a missing
  qualification, an attribution, a slip), given exactly; "shared" says whether it touches a statement
  or proof of record (then it goes through the blueprint, `adr/0004`). **author**: changes what the
  paper claims or its structure, reverses D1–D9, or chooses between routes. **decline**: wrong, or
  against a rule or a decision.
- **Quotations.** Every phrase quoted by A or B and listed in `front_classical_phrases-output.txt` is
  in the build at the page given (one, "which carry the name of the Matérn covariances", p. 3, is
  missed by the script on the accented letter and was read on the page). A gives "p. 61" for the
  shape-blind family and B "p. 61" for F.3(3)(ii); both are at p. 61 (A.3's remark) and p. 90 (F.3).

---

# Report A (§§ 1–2)

## A.R1 "The main result … the classification" overstates Table 2; say which cells are complete (pp. 1, 3, 32, 54)

**Claim.** PARTLY. The abstract's "completely in some cases, by bounds or examples in others" (p. 1,
`main.tex:138`) and p. 3's "a complete description in some cases and bounds or examples in the
others" (`01-introduction.tex:215`) are accurate; round 1 narrowed both (B1, `VERIFY-round1-claims-paper.md`
F1a). What is true is that only § 5 (p. 54) says cell by cell which are complete: two, (GL(d), rays)
and (GL(d), Loewner); four stop short; three are classified on part of their parameters. Table 2
(p. 32) marks nothing. B (part 2 (f)) reads the (S(d), rays) cell as a complete characterization;
§ 5 counts it as partial ("up to which kernels extend to a continuous field over the shapes"), and
§ 5 is right: Proposition 3.4(2) characterizes the fields, but which fields exist is problem 4. E
(its § 2) argues that (GL(d), stable) is complete too, which would make three; that is E's finding,
not verified here, and the count below depends on it.

**"Name Theorems 3.6/3.7 and 4.21 as the main results, the table as the map."** Against `adr/0006`
item 3 ("The main result is the $(G, W)$ classification (`tab:landscape`)").

**Response: safe** for the count, **decline** for the renaming.
- `01-introduction.tex:215`: "a complete description in some cases and bounds or examples in the
  others" → "a complete description for the general linear group along the rays and along the
  Loewner order, and bounds, examples or partial descriptions in the others (\S\ref{…conclusion})".
- Table 2's caption (`05-table.tex`): add "The cells (GL(d), rays) and (GL(d), Loewner) are complete
  descriptions; § 5 says how far each other cell goes." Prose, no shared marker. Both wait for the
  verdict on E's (GL(d), stable) finding, which may add a third cell.
- The abstract stays: it is accurate and at 277 words by round 2's convention
  (`verify-round2-paper-scripts/abstract_words.py`), already above D6's "near 250".

## A.R2 The abstract's "Shape-adapted apertures are such steps from the first stage" drops the normalization (p. 1)

**Claim.** CONFIRMED. `main.tex:141`. The step is rank-deficient only under Lindeberg–Gårding's
normalization (least eigenvalue fixed); at fixed volume no Loewner step leaves the first stage
(§ 4.1 item 1, p. 27; Lemma 4.1(2)); § 1 (p. 4) and § 5 (p. 54) carry the qualification.
**The source**, which A could not reach: [37] § 6.1, report p. 17: normalizing to $\det\Sigma_0 = 1$
"would, however, also lead to systematic over-estimates of the anisotropy … we propose to keep the
smallest eigenvalue $\lambda_{\min}(\Sigma_t)$ of $\Sigma_t$ constant during the iterations". So p. 27's
description is right; A's request to quote it in the paper is optional (C asks the same, its required
change 8).

**Response: safe** (a missing qualification): "Shape-adapted apertures are such steps from the first
stage." → "Shape-adapted apertures at fixed least smoothing are such steps from the first stage."
(+4 words, § 4.1's own phrase). Not shared. The word budget is the author's (D6): with the abstract
at 277 words, the author may want a cut elsewhere.

## A.R3 p. 4, "a non-Gaussian kernel loses only the cascade … which the iteration does not use (§ 5)"

**Claim.** PARTLY. `01-introduction.tex:250-253` says "for the apertures of the practice", which is
§ 5's "as far as the apertures are concerned" in other words; so the scope is stated. What p. 4 lacks
is § 5's limitation that the selection and its iteration under a non-Gaussian kernel are not treated
(p. 54), and "loses only" reads as a claim about the whole procedure.

**Response: safe.** "So for the apertures of the practice a non-Gaussian kernel loses only the
cascade between the stages of the iteration, which the iteration does not use (§5)." → "So, as far as
the apertures of the practice are concerned, a non-Gaussian kernel loses only the cascade between the
stages of the iteration, which the iteration does not use. How the selection of the shape behaves
under such a kernel is not treated (§5)." Not shared.

## A.R4 p. 2, "Off W a change of aperture is a re-measurement of the original image"

**Claim.** PARTLY. `01-introduction.tex:155`. As a description of the family it is right: off $W$
the family has no stage, so the record at the new aperture is computed from the original image. As
read beside "further smoothing" it says more than the axioms: a step off $W$ can still have a
probability increment (the stable orbit's full-rank steps, Proposition 4.7, p. 39, are off the ray
order). C raises the same sentence form (its required change 5, pp. 28, 37, 54).

**Response: safe.** "Off $W$ a change of aperture is a re-measurement of the original image." →
"Off $W$ the family has no stage, so a change of aperture need not be a further smoothing, and the
record there is measured from the original image." Not shared.

## A.R5 (with B.R4) The line paper in the trust base; Proposition A.3 "on Lean's logical axioms alone"

**Claim 1: § 1.1 and Appendix I cannot all be read the same way.** CONFIRMED as an omission; nothing
claimed is false. The printed proof of A.3(2) restates [15, Prop. 6.6] (p. 62); § 1.1 says the line
paper's statements are "proved in its released version" and the development requires "no formal
development of the line paper" (p. 7, `01-introduction.tex:452-458`); Appendix I lists A.3 as
"machine-checked on Lean's logical axioms alone" (p. 104). What the Lean does
(`IsotropicCorner.lean:294-310`): `isotropic_corner_gauge` takes the gauge from
`ScaleSpace.canonical_gauge` in the shared library ScaleSpaceCore (`Gauge.lean`, node
`line:prop:canonical-gauge`, i.e. [15, Prop. 6.6] moved there on second demand); the guard records
A.3's seven declarations as Lean core "(the shared library's `canonical_gauge` is)"
(`CIAxiomGuard.lean:1251-1261`). [15, Lem. 6.3]'s fact is proved inline (`eq_dirac_of_push_smul_eq`,
same block). Theorem 2.5's formal proof reads ScaleSpaceCore's `ScaleSpace.main_analysis`
([15, Thm. 7.3], necessity), whose cited clause is a hypothesis discharged from C2(ii) by
`line_levy_unique` (`Upstream.lean`, `trust-boundary.txt:80-90`; `IsoAxiomGuard.lean`:
`isotropic_classification` expects C2(ii), C2(iii)). So every sentence printed is true, and the
reader cannot see why: the line paper's statements that the formal proofs use are proved in the shared
library, not assumed. E raises the same (its required change 4).

**Claim 2: the two scopes of "what is checked" differ.** CONFIRMED. § 1.1: "Every definition,
lemma, proposition and theorem of §§ 3–4 and of the appendices" (p. 6); Appendix I: the theorems,
"every proposition and lemma their proofs spend, and every further result of the appendices"
(p. 103, `appendix-verification.tex:47`). The second leaves out main-text results no theorem spends,
which are formalized: `prop:matern-steps` (4.17), `prop:rational-symbols` (4.18),
`prop:shape-adapted-apertures` (4.22) and `lem:loewner-scale-shape` (4.1) are all `\leanok`. Appendix I
understates.

**Response: safe** (prose, no shared marker; the session first runs the guard on
`ScaleSpace.canonical_gauge` and `ScaleSpace.main_analysis`, `lean.md`, since this record read the
guard's comments and could not run Lean).
- `01-introduction.tex:458`, after "… and no formal development of the line paper.": "The formal
  proofs take two statements of the line paper from ScaleSpaceCore, where they are proved: the gauge of
  \prog{V}{Prop.~6.6}, in the proof of Proposition~\ref{prop:isotropic-corner}, and the necessity half
  of Theorem~\ref{thm:line-classification}, whose uniqueness clause of C2 is a hypothesis this
  development discharges. The fact of \prog{V}{Lem.~6.3} is proved inside the proof of
  Proposition~\ref{prop:isotropic-corner}."
- `appendix-verification.tex:47`: "So is every proposition and lemma their proofs spend, and every
  further result of the appendices." → "So is every other definition, lemma and proposition of
  §§ 3–4 and of the appendices." In the A.3 bullet (after line 96): "(Proposition A.3), whose gauge
  of [15, Prop. 6.6] is proved in ScaleSpaceCore (§ 1.1)".
- Not raised by A or B, read on the way: `blueprint/trust-boundary.txt:75-76` opens "This development
  still requires Paper V's Lean package", which its own next paragraph (lines 85–90) and
  `lakefile.toml` contradict. A stale comment, outside this verification; flagged for the trust-base
  session.

## A.R6 Print the complete proofs of the sketched 4.24, A.3 and 4.4

**Claim.** CONFIRMED as a fact (the three are sketched, p. 104), and the request reverses **D2**
(print 4.15 and 4.19 only; the rest keep their sketches, the deposit gets a citable address). E asks
the same for the Table 2 cells (its required change 5). Cost, from `sketched_statements-output.txt`
(another verifier's): the blueprint proofs of 4.4, 4.24 and A.3 are 3974 + 6741 + 8922 characters
against sketches of 1848 + 3272 + 4392, net ≈ 10 100 characters ≈ 1.8 pages; all twenty ≈ 13.6 pages.

**Response: author.** Options: (a) keep D2 (recommended: the author decided it after the same request
in round 1, and the deposit's address is the remedy); (b) print these three (+1.8 pages); (c) print
all twenty (+13.6). The reason to reopen would be A.3, which carries the isotropic corner, and E's
finding that one sketch (H.8(3)) does not prove its statement, which is E's to verify.

## A.R7 Iijima's matrix scale "as Weickert, Ishikawa and Imiya report" (p. 5; Remark 3.14, p. 26)

**Claim.** REFUTED. [59] p. 241 (held, `weickert1999linear`), § 3 "Iijima's Two-Dimensional Axiomatic
(1962)": "$\Sigma$ is a symmetric positive definite 2 × 2 matrix"; (I) linearity, (II) translation
invariance, (III) "closedness under affine transformations: If the pattern is transformed by an
(invertible) matrix … there exists a $\Sigma' = \Sigma'(\Sigma, \Lambda)$"; (IV) "(Generalized)
semigroup property: For every $\Sigma_1$ and $\Sigma_2$ there exists a $\Sigma_3$"; "These four axioms
in combination with the requirement of positivity preservation are sufficient to derive … the affine
Gaussian scale-space." The paper's description (pp. 5, 26) is this page. The published abstract A
read describes § 2 of the article (the 1959 one-dimensional work). The library's acquisition note on
the record ("The JMIV version has not been found") is stale: the JMIV copy is held and paginated
237–252.

**Response: decline.** A quotation in the paper is not needed; the reading notes
(`READING-weickert1999linear*.md`) hold it.

## A.R8 C3's justification "applied to a family completed around that measure" (p. 13)

**Claim.** PARTLY. `02-line-papers.tex:446-449`, prose after the shared C3. The paper's argument is
valid and checkable: given $\rho$ a residual at $t_0$, choose residuals at the other $t$ by the
hypothesis; Jurek–Mason's sentence applied to that family makes $\rho$ infinitely divisible. A's
route (apply the theorem once, so $\mu$ is infinitely divisible, $\widehat\mu$ has no zero, and the
residual at each $t$ is unique) is shorter and also valid. A's remark on $t = 0$: once $\mu$ is
infinitely divisible, $\widehat\rho_0 = 1$, so $\rho_0 = \delta_0$; harmless.

**Response: safe, optional.** Replace "this is their sentence applied to a family completed around that
measure, the hypothesis supplying the residuals at the other $t$" by "their sentence makes $\mu$
infinitely divisible, so $\widehat\mu$ has no zero and the residual at each $t$ is the unique law with
transform $\widehat\mu/\widehat\mu(e^{-tB^{\mathsf T}}\cdot)$". Prose; the ledger entry's wording
(`blueprint/AXIOMS.md`, A5) should be compared before changing it, since the paragraph reports what C3
reads beyond its sources.

## A.R9 Table 2's (similarities, Loewner) cell lacks Proposition F.3(4) (p. 5, p. 32)

**Claim.** CONFIRMED. p. 5 says the similarity row "keeps every rotation-invariant one in every
column, the Loewner column included (Proposition F.3(4))"; F.3(4) (p. 90) states it; the (S(d),
Loewner) cell (p. 32, `05-table.tex:96-106`) does not. The witness is F.3(3)(ii),
$\Sigma \mapsto ((\det\Sigma)^{1/(2d)}I)_*m$, with kernels $\delta_0$ at every singular $\Sigma$ (p. 61,
p. 91). B makes the same point from the other side (its part 2 (l), suggestion 8). E asks to shorten
the same cell (its exposition list), which pulls the other way.

**Response: safe.** At the head of the cell: "the isotropic members are the rotation-invariant
self-decomposable laws $\ne \delta_0$, the shape-blind family $((\det\Sigma)^{1/(2d)}I)_*\mu_I$ among
the families (Proposition~\ref{prop:similarity-ray-families}(3)–(4));". `01-introduction.tex:290-291`,
after "(Proposition F.3(4))": ", by a family that sees only the volume of the aperture". Not shared.

## A.R10 "[37], § 4 and § 4.1, eqs. (24)–(30), p. 10" is not a page of IVC 15:415–434 (p. 24)

**Claim.** CONFIRMED. `04-classical.tex:707`. The held copy is the KTH report (33 pp., "March 13,
2001"; `library get lindeberg1997shape --pages 10`: § 4 and eqs. (24)–(25) on its p. 10), and the
bibliography entry is the journal article. `READING-lindeberg1997shape.md:8-9` already says the
journal pagination was not checked. The paper's other three citations of [37] give sections only.

**Response: safe.** `(\sscite{lindeberg1997shape}, \S4 and \S4.1, eqs.~(24)--(30), p.~10)` →
`(\sscite{lindeberg1997shape}, \S\S4 and 4.1)`. The equation numbers are the report's and are
dropped with the page; with the journal copy acquired, both could be restored. Not shared.

## A.S Suggestions

| # | Claim checked | Verdict | Class and response |
|---|---|---|---|
| S1 | § 1's two "Relation to" paragraphs duplicate § 3.5 and § 4; cut § 1 to 3 pp. | PARTLY (overlap real; § 1's are the positioning of `adr/0006`) | decline: `adr/0006` item 7 (no page budget), D3, D6 (§ 1 restructured by the author) |
| S2 | Cite Nitzberg–Shiota (1992), whom Weickert § 1.2.6 names | CONFIRMED at [58] p. 13: "In 1992 Nitzberg and Shiota [310] proposed to adapt the Gaussian kernel shape to the structure of the original image" (shape-adapted smoothing, not the covariance-indexed family) | author: a new prior-art citation of a source not held (acquire, reading note first); it would sit with p. 1's "Its use is shape adaptation" |
| S3 | Move the subordination paragraph and (2.6) to Appendix E | — | decline: structure; `adr/0006` item 7 |
| S4 | Define the variance gauge before p. 19 | REFUTED: p. 19 defines it at first use ("the coordinate in which the scale of the Gaussian member is proportional to its variance") | decline |
| S5 | "six statements restated in § 2.3" undercounts: four more of [16] cited | CONFIRMED: `\prog{Iso}{Prop.~3.11}` (`02-line-papers.tex:344`), `{Prop.~3.12(2)}` (`:287`), `{Thm.~3.13}` (`05-orbits.tex:741`), `{Rem.~3.26}` (`04-classical.tex:835`); the numbers are the released `iso-v0.1`'s (`paper-iso/main.aux`: 3.11 polar form, 3.12 bridge; `NODES-q0457.md` for 3.13, 3.26) | safe: `01-introduction.tex:307-308` "used through the six statements restated in §2.3" → "used through the six statements restated in §2.3, and four more cited where they are used" |
| S6 | Matérn laws are Matérn covariances only for $\gamma > d/2$ (p. 3) | PARTLY: p. 3 already writes "carry the name of the Matérn covariances", not "are"; p. 37 states $\gamma > d/2$ | decline (optional safe: "for $\gamma > 1/2$" on the line) |
| S7 | Cite Proposition 3.4(3) beside 4.5 on p. 4 | CONFIRMED (Table 2 cites both) | safe, optional |
| S8 | Fold the list of letters into Table 1 | — | decline: layout, round 2 notation verification |
| S9 | One frequency letter | — | decline: § 2.1 follows the sources' letters, decided in rounds 1–2 |
| S10 | "Every definition, lemma, …" → "every numbered statement"; abstract "The results" → "The theorems of §§ 3–4" | REFUTED for § 1.1: remarks are numbered too, so the proposed wording would wrongly include them; the present list excludes them. Abstract: true of the paper's results, § 2's restatements being cited | decline |
| S11 | `gelfand_naimark_logMajorized` may state the full majorization | REFUTED: `Interfaces.lean:273-277` states the partial-sum inequalities for $1 \le k \le d$ only, the weak form § 2.4 calls C4 | decline |
| S12 | Lindeberg 2011 [34] may already state the order over covariance matrices | REFUTED at the page: [34] § 4.1.2, p. 45, states the family over covariance matrices and its closure under affine maps; its semigroup is in the scalar $s$ (searches for a matrix sum or difference find nothing). Remark 3.14 cites that page already | decline |
| S13 | Define self-decomposability on p. 2 | REFUTED: p. 3 ("For every $0 < c < 1$ such a law is the convolution of its own image under $x \mapsto cx$ with another law") defines it one page after "in the sense defined below" | decline |
| S14 | "Table 3 gives the limit kernel by kernel" oversells | CONFIRMED (Table 3 has "at least" and "not known in general" rows) | safe: `01-introduction.tex:266-267` → "Table 3 gives the limit for each family it lists". The other two "kernel by kernel" (pp. 3–4) are `adr/0006` item 4's phrase for the reading and stay |
| S15 | Give the reason the uniqueness clause of Theorem 2.5 needs no hypothesis on $F'$ | The reason is right (an exponent of a self-decomposable law is nondecreasing) | safe, optional, as prose after the shared statement |

## A.x Other claims of A's sections 2–7

- **"exponent" on p. 5 lacks a forward reference** (§ 7). CONFIRMED (`01-introduction.tex:292`).
  Safe: "(§2.2)" after "exponent".
- **p. 6, "Through the singular matrix …" cannot be followed until Remark 3.13.** REFUTED: the next
  sentence ends "(Remark 3.13)" (round 2's fix 18.3).
- **Lemma 2.9(2)'s constant.** A is right that pdftotext prints "2c"; the source is
  `\tfrac c2\log a` (`02-line-papers.tex:364`). No change.
- **Lemma 2.9(1)'s 13c/4 is "generous".** Not an error; no change.
- **C4 at Bhatia Cor. III.4.6, p. 73** (unverified by A). CONFIRMED at the page: "Corollary III.4.6
  (Lidskii) … (III.21)".
- **Kelker, Lemma 5, p. 423** (unverified by A). CONFIRMED at the page (OCR "Lemma ?": "If $\Sigma$
  is a diagonal matrix, then the components of $X$ are independent only if $X$ has a normal
  distribution").
- **"χ(0) = 0 is automatic"** (§ 3). True and harmless; decline.
- **Pedersen–Sato and Hazod–Siebert page numbers** (§ 6, "unverified"). No error asserted; not checked
  here.

---

# Report B (§ 3 and Appendix A)

## B.R1 p. 4, "The base must be positive definite: from Σ = 0 every step 0 → P has the increment µ_P"

**Claim.** CONFIRMED: the sentence asserts a necessity that is false beyond $\Sigma = 0$. For an orbit
$\widehat\mu_\Sigma = e^{-g(\langle\omega,\Sigma\omega\rangle)}$ and the step $e_1e_1^{\mathsf T} \to I$
($P = I - e_1e_1^{\mathsf T}$, singular base), the increment's transform is 1 on $\ker P = \RR e_1$, so by
Lemma 3.8 it is invariant along $e_1$, which is $g(u + v) = g(u) + g(v)$ for $u, v \ge 0$: Cauchy's
equation, $g$ linear. `singular_base_step-output.txt`: for the stable $g(u) = u^{\alpha/2}$, $\alpha = 1,
1.5$, the candidate transform varies along $e_1$ (spread 0.54, 0.35), so no probability increment;
at $\alpha = 2$ it is constant. Remark 3.13 (p. 25) uses a step from the singular base
$I - e_1e_1^{\mathsf T}$. B is also right on why Theorem 3.7 takes a definite base: from
$e_1e_1^{\mathsf T}$ the ray step $P = e_1e_1^{\mathsf T}$ has $0 < \operatorname{rank}P < d$ and an
increment for every self-decomposable law (the same output, case 2).

**Response: safe** (narrowing a false necessity). `01-introduction.tex:237-238`: "The base must be
positive definite: from $\Sigma = 0$ every step $0 \to P$ has the increment $\mu_P$." → "The theorem
takes a positive definite base, where a rank-deficient step is one with $P$ singular. The base must not
be $0$: from $\Sigma = 0$ every step $0 \to P$ has the increment $\mu_P$." Not shared.

## B.R2 Lemma A.1(1) is Wendel's theorem, uncredited (pp. 56–58)

**Claim.** CONFIRMED. Wendel 1952, Theorem 1, p. 252 (held): a left centralizer of real or complex
$L^1(G)$ "is given by $Ax = x * \mu$" for a unique regular measure of bounded variation. For
$G = \RR^d$, Larsen 1971, Theorem 0.1.1, (i) ⇔ (v), p. 2 (held), gives it for operators commuting with
translations. Lemma A.1(1) is that statement plus positivity and mass; its proof's interchange identity
($\Phi(f*g) = f*\Phi g$) is the centralizer condition. Reading notes exist since 2026-10-15
(`READING-wendel1952left.md`, `READING-larsen1971introduction.md`), and the prior-art record lists both
in row A ("Wendel and Larsen leave positivity, mass and continuity"); the paper cites neither and
`paper/references.bib` has no entry. `adr/0006` item 1: "A published theorem reused in the scale-space
setting is cited with its page." The proof stays: it is the proof of record on the Lean route.

**Response: safe** (an attribution). Prose before Lemma A.1 (`appendix-classical.tex`, the opening of
§ A.1, before the shared marker at line 40): "Clause (1) is, on the real space $L^1(\RR^d)$, Wendel's
theorem on left centralizers (\sscite{wendel1952left}, Thm.~1, p.~252; for operators commuting with
the translations, \sscite{larsen1971introduction}, Thm.~0.1.1, p.~2), with positivity and mass making
the measure a probability measure." Two `references.bib` entries. Not shared.

## B.R3 Lemma A.5(1) and (3) are classical, uncredited (pp. 63–64)

**Claim.** CONFIRMED, and the source is already in the bibliography. Meerschaert–Scheffler [42],
Theorem 2.3.10, p. 33: "If $\mu \in M_1$ is full, then $S(\mu)$ is a compact subgroup of
$\mathrm{GL}(\RR^d)$" ($S(\mu)$ allows a shift, so it contains Stab$(\mu)$ as a closed subgroup);
Theorem 2.3.11, p. 34: every compact subgroup of GL is $L\mathcal K L^{-1}$ with $\mathcal K \subseteq
O$, which is A.5(3)(b)'s form. Hudson–Mason (p. 482) and Holmes–Hudson–Mason state the compactness for
full laws "(Billingsley)" (`READING-hudson1981operator.md:24-25`, `READING-holmes1982operator.md:21-23`).
Jurek–Mason pp. 59–60 recall it at the opening of § 2.4. Billingsley 1966 is not held.

**Response: safe** (an attribution). Prose before Lemma A.5 (`appendix-classical.tex`, before the
shared marker at line 515): "Clause (1) is a classical consequence of the convergence of types
(\sscite{meerschaert2001limit}, Thm.~2.3.10, p.~33, where the symmetries may carry a shift), and
(3)(b) has the form of their Thm.~2.3.11, p.~34." Before citing, the librarian adds the two theorems,
read at the page image, to `READING-meerschaert2001limit.md` (it records pp. 257–262 only). Not shared.

## B.R4 Proposition A.3 in the trust base

Same finding as A.R5; verdict and response there.

## B.R5 p. 17, "the last clause of the definition lists them as the corners" — "Definition 3.1 has no such clause"

**Claim.** REFUTED in substance, PARTLY in wording. The corners are inside Definition 3.1: the
`definition` environment ends after the corners list (`04-classical.tex:160-173`, `\end{definition}` at
173). The definition is typeset upright with no end mark (rendered p. 17), so the reader cannot see
that, and "clause" collides with the numbered clauses (1) and (2).

**Response: safe.** `04-classical.tex:175`: "the last clause of the definition lists them as the
corners of the scheme" → "the definition ends by listing them as the corners of the scheme". Prose,
outside the shared block.

## B.R6 Figure 1's caption omits the direction of $u$ (p. 22)

**Claim.** CONFIRMED. `records/affine/fig-rank-deficient-step.py:32-33` draws $u$ at 30°, as B
estimated.

**Response: safe.** `04-classical.tex:485`: after "$P = \tfrac32\,uu^{\tp}$" insert ", $u = (\cos
30^\circ, \sin 30^\circ)$". Caption, not shared.

## B.S Suggestions, and the claims of B's sections 2–7 behind them

**B.S1 / part 3 (ii) first half: every family of the scheme has zero-free kernels from scale zero, so
Lemma 3.3(2)'s conditional always holds.** CONFIRMED, and already in the blueprint:
`lem:gw-kernels-self-decomposable` (`blueprint/src/parts/05-smaller-groups.tex:455-463`, `\leanok`, Lean core:
`gw_family_determined_by_kernels`) states it, and its annotation says "The hypothesis of the last
sentence of \ref{lem:gw-kernels-from-origin}(2) always holds". The paper replaces the node by one
sentence in the proof of Proposition 3.4(2) (p. 76, `appendix-wedge-axis.tex:460`), so the text on
pp. 17–18 ("once their transforms have no zeros") reads conditional. **Response: safe**: after
Proposition 3.4 in § 3.1, "By the proof of Proposition 3.4(2) the kernels from scale zero of every
family of the scheme are self-decomposable, so their transforms have no zeros, and a family is
determined by them (Lemma 3.3(2))." Lemma 3.3 keeps its hypothesis (the `adr/0003` direction: the
corollary discharges it). Removing Lemma 3.9's first-zero argument: **decline**: it is the proof of
record on the Lean route of the (GL(d), Loewner) chain.

**B.S2 / part 3 (ii) second half: (K2) enters Theorem 3.6 only at the boundary; on PD(d) the Gaussian
form follows from (K1), (K3), (K4).** CONFIRMED. The argument: $\mu_I$ is rotation invariant (K3) and
self-decomposable (K1 on the ray, K3 at the dilations: the necessity argument of Proposition 3.4(2),
which uses no continuity), so $\widehat\mu_I = \vartheta(|\omega|^2)$ has no zero (Proposition 3.4(1));
$g = -\log\vartheta$ is continuous, $\ge 0$, $g(0) = 0$; (K3) gives $e^{-g(\langle\omega,\Sigma\omega\rangle)}$
on PD(d); (K1) at $I \le I + e_1e_1^{\mathsf T}$ is (3.2); Theorem 3.7 gives $g = bu$, $b > 0$ by (K4);
increments between definite apertures are quotients. B's family
$N(0, 2b(\theta(\Sigma')\Sigma' - \theta(\Sigma)\Sigma))$, $\theta = 1$ on PD(d), $\theta_0 \in [0,1)$ on
the singular matrices: `k2_boundary_family-output.txt`, $d = 2, 3$, 12 000 Loewner pairs each (≈ 2/3
with a singular end): every increment covariance PSD (least eigenvalue $\ge -4\cdot10^{-15}$), (K1)
additivity and (K3) covariance to $10^{-14}$, (K4), agreement with (3.1) on PD pairs, and (K2) fails at
$(0, \operatorname{diag}(1, \varepsilon, \dots)) \to (0, \operatorname{diag}(1, 0, \dots))$
($0.4966$ against $0.8106$ at the limit). The printed hypotheses are not wrong, and Remark 3.14's "It
adds continuity in the pair" (`04-classical.tex:825`) is a true statement of the hypothesis sets.
**Response: author** (a new statement: a weakening of Theorem 3.6's hypotheses on PD(d), with an
example). Options: (a) a blueprint remark with B's proof and the family, and one sentence in Remark
3.14 (on PD(d) the scheme needs no continuity, as Iijima's axioms have none, [59] p. 241); (b) leave
it. *Recommended: (a)*: it sharpens the one comparison § 1 and Remark 3.14 draw, at the cost of one
remark, refereed blind; no Lean is required for a remark.

**B.S3 / part 3 (iii): Theorem 3.5(2) puts the kernels from scale zero under (P) needlessly.**
CONFIRMED: $\zeta(s) = s\Sigma$ is a $W$-chain from 0 for every order containing the rays (Definition 3.1
takes $0 \le c \le c'$), and clause (2)'s first sentence applies. **Response: safe** as prose (the
statement keeps its form): `04-classical.tex:440`, the sentence "With the ray chains from $0$ …" is
generalized: "The ray chain $\zeta(s) = s\Sigma$ joins $0$ to $\Sigma$ for every order of the scheme,
so every kernel from scale zero is infinitely divisible, with or without (P)."

**B.S4 / part 3 (viii) and part 2 (f): for the similarities the scheme admits kernels $\delta_0$ at a
positive definite aperture.** CONFIRMED. $\nu_\Sigma = N(0, \phi(\sigma(\Sigma))\operatorname{tr}(\Sigma)I)$,
$\nu_0 = \delta_0$, with $\phi$ continuous on $\Delta_d$, 1 at the centre and 0 at an interior
$\sigma_0$: `delta_at_pd_family-output.txt` ($d = 2, 3$): (a) holds, covariance under random
similarities to $10^{-12}$, continuity at 0 and along a path through an eigenvalue crossing and a
singular matrix, and $\nu = \delta_0$ at the positive definite $\operatorname{diag}(\sigma_0)$. Every
$\nu_\Sigma$ is Gaussian or $\delta_0$, so Proposition 3.4(2) makes it an (S(d), rays) family. p. 17's
defence of (K4) at one pair ("whose kernels at the singular matrices are trivial") is true and covers
less. **Response: author.** Options: (a) one sentence in § 3.1 after p. 17's defence, with the family,
and the same in the annotation of `def:gw-cascade-family` (recommended: it changes no statement);
(b) require $\mu_\Sigma \ne \delta_0$ on PD(d), which changes Definition 3.1, its Lean structure and
every cell's statement (not recommended).

**B.S5 / part 3 (i): rename "wedge datum".** Decline: **D7** keeps the name with a clause saying
Definition 3.1 needs no cone, which p. 16 has ("although Definition 3.1 does not require one"). B's
support, "Theorem 4.3(3) exhibits an order of the scheme that comes from no cone", is wrong as stated:
its $K = \{I\} \cup \{\lambda_{\min}(M) \ge 2\}$ lacks the rays ($cI$, $1 < c < 2$), as round 2 found;
adding the rays would give such an order, but the paper does not state one. "$G$ closed is unused in
this block": true and harmless.

**B.S6 / part 3 (xiv): Remark 3.13's step to mutual independence.** CONFIRMED (one-against-the-rest for
every coordinate factors the transform coordinate by coordinate). **Response: safe**:
`04-classical.tex:754-755`, "So the first coordinate of $\mu_I$ is independent of the others, by
rotation invariance every coordinate is, and Kelker's lemma makes $\mu_I$ normal." → "… by rotation
invariance every coordinate is, so the transform factors over the coordinates and they are
independent, and Kelker's lemma makes $\mu_I$ normal. The step used has a singular base, outside
Theorem 3.7 and inside Definition 3.2." Remark, not shared.

**B.S7 / part 3 (iv), part 5 (b): Theorem 3.5(3)(c) takes the order from Proposition 4.7(2), which
Appendix I lists under C2 whole.** CONFIRMED. The order clause is the blueprint's split node
`lem:stable-step-order` ((1) (b) ⇔ (c), (2)'s first sentence, (3); "matrix analysis and spend nothing",
`blueprint/src/parts/05-orbits.tex:661-665`), which `thm:cascade-infinitely-divisible` uses; C2 enters only (1)(a) and the
increments; `gw_family_infinitelyDivisible` prints C1 only (p. 105). **Response: safe**:
`appendix-classical.tex:659`, "is one is Proposition~\ref{prop:stable-step-cone}(2), proved without
this theorem" → "is one is the first sentence of Proposition~\ref{prop:stable-step-cone}(2), which
rests on no cited fact"; `appendix-verification.tex:77`, "Propositions~\ref{prop:stable-step-cone}"
→ "Proposition~\ref{prop:stable-step-cone}, for the increments of its clauses (1) and (2),". Not
shared.

**B.S8 / part 2 (l): the abstract's "With the similarities, non-Gaussian families cascade along the
Loewner order" is shown by the shape-blind family.** CONFIRMED (F.3(3)(ii) along the Loewner order).
The sentence is true; § 1 already cites F.3(4) before H.1(3) (p. 5). **Response:** safe in § 1 and
Table 2 as A.R9; **decline** in the abstract (true; the budget).

**B.S9, S10, S11 and part 7 (cut § 3.5 by a page; § 3.2 to a remark and p. 19's paragraph to four
lines; reduce Lemmas A.1–A.2's proofs; drop Figure 1; one derivation four times).** The repetition is
real (Lemma 3.9, Proposition 3.4(3), Proposition 4.5, D.1(2)). **Decline**: `adr/0006` item 7 (no page
budget), D3 (the measured cuts chosen), and the proofs of record follow the Lean route (`lean.md`); a
shortened proof of Lemma A.1 would leave it.

**B.S12 / part 3 (xv): Remark 3.15 leans on [16, Rem. 3.26] without restating it.** CONFIRMED as a
fact; § 2's rule binds statements and proofs, and this is a remark. **Response: safe, optional**:
`04-classical.tex:835`, after `\prog{Iso}{Rem.~3.26}`: ", which says that at $d = 1$ the isotropic
paper's definition is the line's Definition~\ref{def:line-family}" (`NODES-q0457.md`).

## B.x Other claims of B's sections 2–7

- **Part 2 (a): the headline omits "order of the scheme" and what "Gaussian families" means.** PARTLY:
  the abstract defines the order as the family's $W$ two sentences earlier; that it contains the rays is
  not said there. **Decline** (round 1 narrowed this sentence, D5; the budget).
- **Part 3 (vii): Lemma 3.3(3)'s proof does not say $(A\cdot\Sigma, A\cdot\Sigma') \in P_W$ for (K3).**
  CONFIRMED (p. 60; clause (1) of the same proof says it). **Response: safe**, a slip in a proof of
  record: in the blueprint proof of `lem:gw-kernels-from-origin`, clause (3), insert "the pair
  $(A\cdot\Sigma, A\cdot\Sigma')$ lies in $P_W$ because $W$ is $G$-invariant, and" before "by (b)";
  mirror into `appendix-classical.tex:318-335` in the same pull request (`adr/0004`).
- **Part 5 (c): "A sketched statement is machine-checked like every other" (p. 104).** PARTLY: true of
  the formal proofs; B's point is that the printed sketch of A.3 rests on a restatement. With A.R5's
  sentence in § 1.1 the point is answered; optional safe precision: "… machine-checked like every
  other; its formal proof rests on nothing more."
- **Part 6: Lemma 3.10 could cite Aczél for monotone solutions of Cauchy's equation.** The paper
  claims no novelty there (Remark 3.11 says what the sign replaces). Decline.
- **Part 6: Iijima as reported is "consistent with what is generally reported".** CONFIRMED at [59]
  p. 241 (A.R7).
- **Parts 1, 3 (v), (vi), (ix)–(xiii): no error found by B.** No finding to verify.

---

# C. Where reports C, D and E repeat a finding of A or B

- **Table 2 does not mark complete cells** (A.R1): C (§ 2, required change 2, suggestion 5), E (§ 2,
  with its own claim that (GL(d), stable) is complete).
- **"Re-measurement of the original image"** (A.R4): C (required change 5, pp. 28, 37, 54, abstract).
- **Lindeberg–Gårding's normalization and the practice's pages** (A.R2): C (required change 8); D
  (§ 2) finds the abstract's two shape-adaptation sentences consistent with Proposition 4.22.
- **The line paper in the trust base; A.3** (A.R5, B.R4): E (§ 5 point 1, required change 4, which
  also names Lemma 2.2 and [15, Rem. 6.7]).
- **Print the sketched proofs** (A.R6): E (§ 5 point 2, required change 5).
- **"A sketched statement is machine-checked like every other"** (B part 5 (c)): E (§ 5 point 2).
- **The shape-blind family of F.3(3)(ii), $\delta_0$ at the singular matrices** (A.R9, B.S8): E (§ 3.5,
  F.3); E's suggestion to shorten the (S(d), Loewner) cell conflicts with A.R9's addition.
- **Lemma 2.9(2) printed "2c" in the text layer**: C (§ 3), as A.

---

## Summary

| Report, item | Finding | Verdict | Class | Response |
|---|---|---|---|---|
| A R1 | "classification"; which cells are complete | PARTLY (claims accurate; only § 5 counts; renaming against `adr/0006`) | safe + decline | p. 3 and Table 2's caption name the complete cells (count pending E's (GL, stable) finding); abstract stays; "main result" stays |
| A R2 | abstract drops the normalization | CONFIRMED ([37] § 6.1, report p. 17, supports p. 27) | safe | "at fixed least smoothing" (+4 words; budget the author's) |
| A R3 | p. 4 "loses only" | PARTLY ("for the apertures" present) | safe | add § 5's limitation sentence |
| A R4 | "Off W … is a re-measurement" | PARTLY | safe | "need not be a further smoothing … measured from the original image" |
| A R5 / B R4 | line paper and A.3 in the trust base; two scopes of "checked" | CONFIRMED as omissions (all printed sentences true: [15, Prop. 6.6] and Thm. 7.3's necessity are proved in ScaleSpaceCore) | safe | one sentence in § 1.1; App. I's scope aligned; run the guard first |
| A R6 | print sketches of 4.24, A.3, 4.4 | CONFIRMED as fact; reverses D2 | author | keep D2 (recommended); or +1.8 pp. for the three |
| A R7 | Iijima's matrix scale unverified | REFUTED ([59] p. 241, § 3) | decline | — |
| A R8 | C3's justification uncheckable | PARTLY (valid; A's is shorter) | safe, optional | the uniqueness route, after comparing ledger A5 |
| A R9 | (S, Loewner) cell lacks F.3(4) | CONFIRMED | safe | add to the cell and "a family that sees only the volume" on p. 5 |
| A R10 | [37] "p. 10" | CONFIRMED (a report page) | safe | cite §§ 4 and 4.1 only |
| A S1, S3, S8, S9 | cuts and layout | — | decline | `adr/0006` item 7, D3, D6 |
| A S2 | Nitzberg–Shiota | CONFIRMED at [58] p. 13 | author | new prior-art citation, not held |
| A S4, S10, S11, S12, S13 | variance gauge; "numbered statement"; C4 axiom; Lindeberg 2011; self-decomposability | REFUTED | decline | — |
| A S5 | four more [16] statements cited | CONFIRMED | safe | "and four more cited where they are used" |
| A S6 | Matérn $\gamma > d/2$ | PARTLY | decline (optional) | — |
| A S7, S14, S15 | cite 3.4(3); "kernel by kernel" (Table 3); Thm 2.5's $F'$ | CONFIRMED | safe | as given |
| B R1 | "The base must be positive definite" | CONFIRMED (false necessity; Remark 3.13 forces from a singular base) | safe | "must not be 0"; definite base is where "P singular" is the right condition |
| B R2 | Lemma A.1(1) is Wendel's | CONFIRMED (Wendel Thm 1, p. 252; Larsen Thm 0.1.1, p. 2; notes exist) | safe | cite in prose before A.1; two bib entries |
| B R3 | Lemma A.5(1), (3) classical | CONFIRMED (Meerschaert–Scheffler Thms 2.3.10–2.3.11, pp. 33–34; Hudson–Mason p. 482) | safe | cite; reading note amended first; Billingsley not held |
| B R5 | "last clause of the definition" | REFUTED in substance (corners inside Def. 3.1), wording ambiguous | safe | "the definition ends by listing them" |
| B R6 | Figure 1's $u$ | CONFIRMED (30°) | safe | add $u$ to the caption |
| B S1 | no zeros for every family | CONFIRMED (blueprint already has `lem:gw-kernels-self-decomposable`) | safe | one sentence in § 3.1; Lemma 3.9 unchanged |
| B S2 | (K2) only at the boundary | CONFIRMED (proof and family checked) | author | a remark with proof and the family (recommended) |
| B S3 | Thm 3.5(2): kernels from 0 need no (P) | CONFIRMED | safe | prose sentence at p. 20 |
| B S4 | $\delta_0$ at a PD aperture (similarities) | CONFIRMED (family checked) | author | a sentence in § 3.1 (recommended), not a new (K4) |
| B S5 | rename "wedge datum" | Theorem 4.3(3) support REFUTED (no rays) | decline | D7 |
| B S6 | Remark 3.13 mutual independence | CONFIRMED | safe | one clause, and the singular base noted |
| B S7 | Prop. 4.7(2) under C2 | CONFIRMED | safe | App. I and p. 65 say which clauses spend C2 |
| B S8 | shape-blind family makes the abstract's similarity claim easy | CONFIRMED | safe (§ 1, Table 2) / decline (abstract) | as A R9 |
| B S9–S11 | cuts, shorter proofs | — | decline | `adr/0006` item 7, D3, Lean route |
| B S12 | Remark 3.15 and [16, Rem. 3.26] | CONFIRMED | safe, optional | one clause |
| B x (vii) | Lemma 3.3(3)'s proof omits $G$-invariance | CONFIRMED | safe (shared proof) | blueprint proof, mirrored (`adr/0004`) |
| B x (a), 5 (c), Aczél | headline wording; sketches; Aczél | PARTLY / — | decline (optional precision for 5 (c)) | — |

**For the author.** (1) A R6: reopen D2 or not (recommended: not). (2) B S2: add the remark that (K2)
is needed only at the boundary (recommended: yes). (3) B S4: say in § 3.1 that the similarity cells
contain fields with $\delta_0$ at a positive definite aperture (recommended), not strengthen (K4).
(4) A S2: acquire and cite Nitzberg–Shiota. (5) A R2: four words in an abstract already at 277 by round
2's count; whether to cut elsewhere. (6) A R1's count of complete cells waits for the verdict on E's
(GL(d), stable) finding.

**Errors in the paper** (none in a theorem or proof): the false necessity on p. 4 (B R1); a report
page cited for a journal article (A R10); two uncredited classical results (B R2, B R3); a missing step
in Lemma 3.3(3)'s proof of record (B x (vii)); and the trust-base account that is true but leaves the
line paper's role unreadable (A R5).
