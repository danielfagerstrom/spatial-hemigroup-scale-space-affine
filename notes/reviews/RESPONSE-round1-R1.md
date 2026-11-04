# Response to the external review of the isotropic paper, round 1: batch R1 (Q-0424)

**What this is.** Article-kit `PROCESS.md` § 9. Batch R1 of
`records/affine/PLAN-review-response-paper-iso.md` (§ 1.2 and § 3): the statements of the prose
that the review showed wrong or too strong, the two printed proofs, the cited facts C5 and C6,
Appendix B's account of the check. The sources of truth are the two verification records,
`VERIFY-round1-mathematics.md` (cited below as M, with its item) and
`VERIFY-round1-claims-and-trust-base.md` (cited as C). Branch `queue/q-0424`, from `queue/q-0423`
(`fd307e5`), 2026-10-12. Line numbers are those of the branch at its last commit.

**Not in this batch**: the abstract, "The answers", the prior-work paragraphs and the
contributions of § 1, Table 3's last column and caption, the tier paragraph and the dictionary of
§ 3.3, the opening of § 3.4, the second paragraph of § 4 (the framing batch, R4, written once
after the new statements are in); the new statements (Q-0425); the paper-specific guard (R2); the
presentation items (R5); the second freeze (R6). § 3 below lists every place left, with the
wording proposed for it.

**No statement is changed.** No `.lean` file, no shared statement, no ledger entry's statement,
no line of `blueprint/trust-boundary.txt`, and nothing in `paper/`. One proof of record is
changed at the blueprint and mirrored (`prop:isotropic-radial-monotone`), and its marker is
re-pinned, alone (`python records/formalization/pin-one-marker.py prop:isotropic-radial-monotone`:
`+cbc4e8881b03` became `+41f64e7002fa`).

## 1. The sixteen items of the brief

| # | item | what was done | where |
|---|---|---|---|
| 1 | "The power cannot be improved" (M 1) | Restricted to $c \le d$, with the record's argument. For $c > d$ one sentence: the bound tends to $0$ and says little, the density being continuous and positive at the centre (Theorem 3.12(2), Lemma A.2(1)). | `paper-iso/03-isotropic.tex:1168–1173` |
| 2 | The slopes of Figure 1 (M 2) | The sentence: the two unbounded curves have the slope $2\gamma - d$, the bounded curve on the line levels off. The caption: bounded on the line, where the curve levels off, unbounded in the plane and in space, where its slope at the centre is $c - d$. The figure is not redrawn. | `03-isotropic.tex:1114–1118`; caption `:737–740` |
| 3 | "The stable kernels have $c = \infty$" (M 3) | "the stable kernels of index below 2 have $c = \infty$"; the Gaussian, their member of index 2, is smooth because it has a Gaussian part, and its polar profile is zero. | `04-conclusion.tex:156–159` |
| 4 | C6 "assumes more than its source" (M 4) | § 1.1: C6 composes two theorems of one book, one direction of each, and concludes less (no uniqueness). § 2.6: the hypothesis for $d \ge 0$ adds nothing, the one at $d = 0$ being the one at $d = 1$ with $n = 1$, $\xi_1 = 0$, $c_1 = 1$; C6 leaves out the uniqueness, cited at the page. Ledger A10: "at least as strong as the page" sharpened to "equivalent", with the reason. The annotation of `thm:cited-A10`: the same clause. Card F6.11 is not touched (M 4: it is right). The axiom is not touched. | `01-introduction.tex:510–512`; `02-line-papers.tex:531–536`; `blueprint/AXIOMS.md:559–569`; `blueprint/src/parts/02-cited-facts.tex:276–278` |
| 5 | Proposition 2.7 (M 7) | "$\varpi((x,\infty)) = k(x)$ for almost every $x > 0$", as the cone paper prints it: Lemma 3.1(2), p. 13, "ϖ is any positive measure on (0, ∞) with ϖ((x, ∞)) = k(x) for almost every x > 0; such a ϖ exists", read through the librarian for this item (`library page fagerstrom2026cone --printed 13`; pp. 14 and 15 for the proof and Proposition 3.3). | `02-line-papers.tex:333–334` |
| 6 | Derivative filters and sampling (C 2(a), 2(b)) | *Derivatives*: "which is enough for the derivative filters of order up to $N$ built from the kernel to be continuous functions", in the opening of § 3.3 and in § 4; "needs" is gone from both. The weak-derivative threshold is not stated. *Sampling*: question 2 of § 1 (an ideal point source; no version of the density bounded near the centre; no peak value; the average over a cell grows without bound); the opening of § 3.3 (a spike concerns the response to an ideal point source, which then has no peak value; the record of a bounded image $f$ is bounded by $\sup|f|$ for every kernel; the mass of a cell is finite); "the value at the centre of a continuous density" and "the integral of the opening diverges" for the two loose sentences of p. 22 and p. 25; § 4 (no version of the density bounded near the centre; the point response has no peak value; the record of a bounded image stays bounded). | `01-introduction.tex:196–199`; `03-isotropic.tex:724–727`, `:824–829`, `:1101–1104`; `04-conclusion.tex:149–153`, `:154–156` |
| 7 | "Rate with its constant" at $c = d$, body only (C 1) | The tier sentence of § 3.3: "an asymptotic equivalence at one kernel, for the whole class, with its constant when $c < d$" (the rest of that paragraph is the framing batch's). The reading after Proposition 3.15: the cut integral "depends on the law and grows at least like $\log(1/s)$". The Matérn example at $\gamma = d/2$: "A logarithm with a constant appears here because this limit exists." The places left are in § 3. | `03-isotropic.tex:844–845`, `:1101–1104`, `:1114–1115` |
| 8 | "Explicit constants" for Proposition 3.17 (M 8; C 4) | The closed form of $A_\beta$ after the proposition, with its $r_\beta$ ($k_d(r_\beta) \ge (\beta + c)/2$), as prose and not in the statement. The derivation is a paragraph of Appendix A after the proof of the proposition, outside the proof of record: the choices $\beta_1 = (\beta+c)/2$, $\varepsilon = (c-\beta)/((c+\beta)\sqrt d)$, the bound on the band, the Gaussian integral, the two closed forms. § 1.1, "What is neither", names it as computed from the printed proofs. With it, "two bounds with explicit constants" and "with their constants" are true in every place (C 4's list), so those sentences stand. Checked again by the record's script (`verify-round1-scripts/item08_upper_bound_constant.py`, exit 0) and by hand at one kernel ($d = 2$, $c = 3/2$, $\beta = 1$: $A_\beta = 1701.9$). | `03-isotropic.tex:1234–1240`; `appendix-isotropic.tex:1399–1434`; `01-introduction.tex:581–582` |
| 9 | "Readable on its own" (C 5) | The clause is gone from the first sentence of § 2. The sentence that says what § 2 restates is followed by: the statements can be read without the two papers, and the proofs rest on theirs, the classification on that of the line paper (Theorem 2.3). | `02-line-papers.tex:87`, `:95–97` |
| 10 | The alternative derivation of $\mathcal{A}_\infty = \mathcal{S}$ (M 5) | **The paper's copy is corrected; the blueprint's proof is not transcribed and not changed.** The route is said to be the formal proof's and is completed in print: what C6 needs is checked (the two radial functions are negative definite by step (a), continuous, zero in dimension 0, and $f \ge 0$, $g_c \ge 0$), $a = 0$, the comparison of the two representations by step (b), the profile by step (c), the causal admissibility. The three steps are stated and proved after the route, in the words of the proofs of record of `lem:lk-negative-definite`, `lem:bernstein-triplet-unique` and `lem:dilation-decreasing-profile`, with the letters of this proof; (b) also names the book's Theorem 3.2, last sentence, p. 21, and (c) the proof of Lemma 7.1 of the line paper. No Lean name is printed. They are steps of this proof, not numbered statements, so Appendix B's list and the 141 declarations are unchanged. The marker `thm:filtration-strict+30dbefb688b7` stands: the pin records the version of the blueprint's proof that was read, and `linkage check` reports no drift. | `appendix-isotropic.tex:1961–2139` |
| 11 | The measurability of $K \mapsto u_K$ (M 6(a)) | Changed at the blueprint and mirrored verbatim (`mirror` checked by `linkage check`: the proof is "tracked by sha" at the new pin). The three sentences on the source's mixing measure now say that $W_d$ is a Borel set, being a countable union of weakly compact sets, and a new paragraph at the end of the proof, "The set $W_d$ is a Borel set", proves it: the families $\mathcal{K}_{k,n}$, their compactness by Blaschke's selection theorem, the weak continuity of $K \mapsto u_K$ on each, the union. The sentence on analytic sets is gone. Blaschke's theorem is stated by name as a classical theorem, with a `% TODO(librarian)` naming Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, at the blueprint and in the paper. The blueprint's closing paragraph "What is machine-checked" (not printed in the paper) now excepts this paragraph, which is prose and not formalized. | `blueprint/src/parts/03-isotropic.tex:1303–1308`, `:1392–1459`, `:1460–1466`; `paper-iso/appendix-isotropic.tex:1174–1179`, `:1249–1313`; ledger A8, "Statement as used", `blueprint/AXIOMS.md:338–356`; marker `03-isotropic.tex:1023` |
| 12 | C5 and the Gaussian part, route A (M 6(b); D5) | Kanter's pp. 68, 69, 70, 71, 72, 74, 77, 78 and 84 read at the page image for this item. § 1.1: Wolfe's printed proof covers the laws with no Gaussian part, two further results of Kanter's paper cover the others, so C5 is carried by printed proofs for every symmetric self-decomposable law; the sentence on the one statement that uses C5 for a law with a Gaussian part is kept. § 2.6: the same with the anchors (Thm. 4.1, p. 78, with p. 77; Lemma 3.1, p. 70; Thm. 3.2, p. 74) and the splitting by C2 to C4. The annotation of `thm:cited-A8`, ledger A8 (the bullet of 2026-10-11 rewritten, "was not found" withdrawn, the argument in full with its use of A2, A3 and A4; the Cite line gains the anchors), `AXIOMS-verbatim.md` § A8 (an addendum with the transcriptions), card F6.9, `READING-kanter1977unimodality.md` (an addendum). The axiom, the statement of C5, the Lean and Table 1 are not touched. | `01-introduction.tex:532–535`; `02-line-papers.tex:493–503`; `blueprint/src/parts/02-cited-facts.tex:198–200`, `:205–221`; `blueprint/AXIOMS.md:325`, `:338–356`, `:406–472`; `blueprint/AXIOMS-verbatim.md:534–598`; `blueprint/REVIEW-fidelity.md:946–961`; `records/affine/READING-kanter1977unimodality.md:136–198` |
| 13 | The Student-t hypothesis (M 10; D6 (i)) | `records/affine/READING-halgreen1979self.md` written from pp. 13–17 at the page image (the whole article). After Proposition 3.11: the hypothesis is a theorem of Halgreen, the inverse-gamma laws being generalized gamma convolutions, a class of self-decomposable laws on the half-line (pp. 13–15, the case credited there to Bondesson); the proposition keeps it as a hypothesis because the theorem is not among the cited facts of the formal development. § 4.1: the item is gone, "three questions", and "Not treated" says that the clause is not discharged. § 1.1: the paragraph after the proposition "says ... where the second is proved in print". The clause is not touched. `\sscite{halgreen1979self}` is new: `references.bib` is not edited. | `03-isotropic.tex:655–659`; `04-conclusion.tex:187–188`, `:218–220`; `01-introduction.tex:461–463` |
| 14 | Appendix B and the caption of Table 1 (C 6(a), 6(b)) | § 1.1 opens with what is checked (the formal counterparts, from the formal definitions, the logical foundations and the seven cited facts) and, in the next sentence, what is not (the cited facts, the printed proofs, the agreement of formal and printed statements). Appendix B: the criterion of this paper (the three logical axioms and the nine names); a paragraph "The report for every declaration" naming `records/affine/axioms-iso-all-declarations-output.txt` (144 names, 141 distinct; all depend on the three logical axioms, 110 on nothing else, 31 also on one or more of the nine, none on any other axiom; each statement's cited facts are those of Table 1) and the script beside it; a paragraph "The guard of the repository" (it serves both papers, admits twelve axioms, three of them the companion paper's, on which no declaration of this paper depends; it pins the main declarations and prints nothing for them, has no request for a definition, and so does not print that report); "is Lean's report for eight of the declarations, as it stands in that file" for "a selection of what the command prints", and "The command prints the report for the other declarations too" deleted. The row of Lemma 3.3 is said to hold three declarations for clauses the paper does not print; it is not filtered (C 6(b) notes it and does not ask for a fix). Caption of Table 1: "names the file that holds it for all of them". The report and its script are copied to the stable place, the report byte for byte, the script with its paths and names changed (`table`: exit 0, "ALL CHECKS PASS"). | `01-introduction.tex:450–457`, `:571–573`; `appendix-verification.tex:61–65`, `:132–136`, `:150–152`, `:163–181`, `:199–206`; `records/affine/axioms-iso-all-declarations.py`, `-output.txt` |
| 15 | The Grzywny–Ryznar–Trojan numbering (C 9) | "Cor. 5.8 of the published article" at the one citation whose number collides with the first arXiv version (Table 3, first row). The part of the `TODO(release)` on this source is closed in both comments: the paper cites it by statement number only, never by page. The parts on the three sources held as arXiv versions stay. | `03-isotropic.tex:759–760`; comments `:698–705`, `01-introduction.tex:124–128` |
| 16 | The two settled questions of § 4.1 | Not answered. Both paragraphs stand, each under a `% TODO(Q-0425)`. | `04-conclusion.tex:190–192`, `:210–212` |

## 2. The findings of the two verification records

### 2.1 `VERIFY-round1-mathematics.md`

| item | verdict there | disposition here |
|---|---|---|
| 1 "The power cannot be improved" | CONFIRMED | Fixed (row 1). |
| 2 The slopes of Figure 1 | CONFIRMED | Fixed (row 2). |
| 3 "The stable kernels have $c = \infty$" | CONFIRMED | Fixed (row 3). |
| 4 C6 "assumes more than its source" | CONFIRMED | Fixed (row 4). |
| 5 The alternative derivation, p. 54 | CONFIRMED, with a third missing step | Fixed, more fully than the record's small form (row 10). C6 is not widened. |
| 6(a) $K \mapsto u_K$ Borel | CONFIRMED: asserted only | Fixed at the blueprint and mirrored (row 11). The docstring of `wolfe_symmetric_unimodal` still words the reading by analytic sets: no Lean file changes in this item, and ledger A8 says so. |
| 6(b) The Gaussian case of C5 | PARTLY | Route A (row 12). Route B, narrowing the cited fact and proving the Gaussian case directly, is not taken (D5) and is recorded in ledger A8 as the alternative. |
| 7 $k(x) = \varpi((x,\infty))$ | CONFIRMED | Fixed (row 5). |
| 8 The constant of Proposition 3.17 | CONFIRMED | Fixed as prose (row 8). The statement is not changed. |
| 9 The short proof of strictness | CONFIRMED | Not this batch: the author's decisions D1 and D2, the new statements (Q-0425) and the framing batch. |
| 10 The Student-t "open problem" | CONFIRMED | Fixed (row 13). |
| 11 "every density" for $c > d$ | no defect | None. |
| 11 "add uniqueness to C6" | REFUTED as a remedy | Not done; the uniqueness is step (b) of the printed proof (row 10). |
| 11 Wolfe's use of Kanter unconfirmed | the paper is right | Kept, and completed (row 12). |
| 11 The abstract's "rate with its constant" | no error | Left to the framing batch (§ 3). |
| "Found while verifying": the time-causal paper's "a limiting case" | — | Another repository's. Recorded in `READING-halgreen1979self.md` § 4. |

### 2.2 `VERIFY-round1-claims-and-trust-base.md`

| item | verdict there | disposition here |
|---|---|---|
| 1 "Rate ... with its constant" at $c = d$ | PARTLY | The body places (row 7). The abstract, § 1, Table 3 and § 4: § 3. |
| 2(a) Unbounded kernel and a sampled image | PARTLY | Fixed at the four places (row 6). |
| 2(b) A derivative filter "needs" | CONFIRMED | Fixed at both places (row 6). The weak-derivative threshold is not stated (the author's, a new result). |
| 3 "Does not study one law", "says nothing about one kernel" | CONFIRMED | Not this batch: the dictionary and the prior-work paragraph are the framing batch's (§ 3). |
| 4 "Explicit constants" | CONFIRMED | Made true by the closed form (row 8). |
| 4 The threshold as a short synthesis | JUDGEMENT | Not this batch (contribution 4, the abstract). |
| 5 "Readable on its own" | CONFIRMED | Fixed (row 9). |
| 5 "The dimension enters twice"; the repetition | CONFIRMED as counts | Not this batch (the cuts are D9's and the framing batch's). |
| 6(a) "Verified", "machine-checked" | PARTLY | The opening of § 1.1 (row 14). The abstract, the AI statement and the code availability statement: § 3. |
| 6(b) Twelve, nine, eight | CONFIRMED | Appendix B and the caption (row 14). The guard of this paper in CI is batch R2. |
| 6(c) Review access; "concept DOI" | JUDGEMENT; CONFIRMED for the DOI | Not this batch (D7; the wording at the release). § 3. |
| 7 The AI statement | JUDGEMENT | The author's (D8). Not touched. |
| 8 Exposition and structure | JUDGEMENT | Not this batch (R4, R5). |
| 9 Grzywny–Ryznar–Trojan, "Corollary 5.8" | CONFIRMED | Fixed at the citation (row 15). The caption sentence is not added: § 4, point 9. |
| 10 The qualifications, the "building blocks", the Student-t condition | CONFIRMED | Kept. The clause on the building blocks is the framing batch's. |
| 10 Required change 13 | depends | Not this batch. |

## 3. Left for the framing batch (R4) and for others, with the wording proposed

The rate at $c = d$ (C 1):

- **Abstract**, `main.tex:165`, same length: `Otherwise a point source is recorded as a spike, at a rate given through the transform.`
- **§ 1, "The answers"**, `01-introduction.tex:242–245`: "gives with its constant" becomes "gives", and after the sentence on $c < d$: `At $c = d$ it is asymptotic to $(2\pi)^{-d}$ times the integral of the transform over the frequencies up to $1/s$, which grows at least like $\log(1/s)$.`
- **§ 1, contribution 1**, `01-introduction.tex:374–375`: "but not the asymptotic equivalence with its constant, at one kernel, for the class" goes with the claim of novelty (D1). If a sentence on the form survives: `the asymptotic equivalence at one kernel, for the class, with the constant $R(d,c)$ for $c < d$ and with the truncated integral of the transform at $c = d$`.
- **Table 3, the row of the rate**, `03-isotropic.tex:788–789`: `The equivalence at one kernel, for the class: with the constant $R(d,c)$ for $c < d$, with the truncated integral of the transform at $c = d$.`
- **§ 3.3, the tier paragraph**, `03-isotropic.tex:844–850`: the one clause is corrected (row 7); the paragraph still says that the rate is new, which D1 withdraws.
- **§ 4, second paragraph**, `04-conclusion.tex:114–116`: `as an asymptotic equivalence: with a power of the distance and an explicit constant for $c < d$, with a truncated integral of the transform at $c = d$`.
- **`notes/HANDOFF.md` and `paper-iso/README.md`, "What it claims"**: they repeat the frozen claims and are rewritten with the framing.

"Machine-checked" (C 6(a)):

- **Abstract**, `main.tex:173–174`, one word more: `Formal counterparts of the main statements are machine-checked in Lean~4, assuming seven theorems of the literature.`
- **`ai-statement.tex:42–43`** and **`declarations.tex:21–23`**: "machine-checks formal counterparts of". The AI statement is the author's (D8).

The literature (C 3), with the frame of the prior-art record:

- **§ 1**, `01-introduction.tex`, "Prior work: the kernel at its centre": `In $\RR^d$ most of the neighbouring results are stated for a family of laws indexed by a time. [...] So a result for small $\tau$ covers, in each family, the kernels with $\tau$ below a bound that depends on the family, and a limit $\tau \to 0$ does not directly establish the asymptotics in $x$ at $\tau = 1$.`
- **§ 3.3, the dictionary**, `03-isotropic.tex:852–859`: `Table~\ref{tab:in-print} needs a dictionary, because most of the literature on $\RR^d$ states its results for a family of laws indexed by a time and not for one law.` and the same last sentence.

The Student-t hypothesis, outside the two places of row 13:

- **§ 1, "Families in every dimension at once"**: "which the cone paper leaves as a hypothesis and this paper does too" is true and stands. If the framing batch wants the pointer: `which is a theorem of the literature (\S\ref{sec:isotropic-reduction}) and stays a hypothesis of the statement here, as in the cone paper`.

The Grzywny–Ryznar–Trojan numbering, if the float page is rebuilt (R5 redraws the figures):

- **Caption of Table 3**: `The statements of \sscite{grzywny2019asymptotic} are cited by the numbers of the published article; its Corollary~5.8 is not in the first arXiv version.`

The two questions of § 4.1 that the review settled wait for Q-0425 (`% TODO(Q-0425)` on each).

For the second freeze (R6): Appendix B still says "The text of this review build is the revision
tagged `iso-review-1`", and so do `\date` and the code availability statement. The text is no
longer that revision; the three places take the new tag at the freeze. "Deposited under the
concept DOI" becomes "with a version DOI of its own" at the release (C 6(c)).

## 4. Judged differently from the verification records

1. **M 5, the derivation of p. 54.** The record offers a complete form (four blueprint nodes
   printed as lemmas) and a small one (the paragraph called an outline, the three steps named).
   The brief asks that a reader be given the three facts with a proof or a reference that can be
   followed. So the route is completed and the three steps are proved in the text, as steps of
   the proof. Printing them as numbered lemmas would add four rows and at least six declarations
   to Appendix B, and the report of the 141 declarations would have to be made again, which needs
   the Lean build. The record's "re-pin" is not needed: the pin is over the blueprint's proof.
2. **M 6(a), the Borel argument.** Three changes to the record's argument, none to its idea.
   The subspaces converge through their orthogonal projections ($P_j^2 = P_j = P_j^{\mathsf T}$,
   $\operatorname{tr}P_j = k$ pass to the limit), so the Grassmannian is not named. The continuity
   of $K \mapsto u_K$ is proved on each compact family $\mathcal{K}_{k,n}$, which is all the last
   step uses, with $r = 1/n$. The inclusion $(1 - \eta/r)K \subseteq K'$ is said to rest on the
   fact that a compact convex set contains every compact convex set with a smaller support
   function, which goes to the same reference as Blaschke's theorem. The identification of the
   Borel sets of weak convergence with the sets of the evaluation $\sigma$-algebra is used and
   said (it is in the annotation of `thm:cited-A8` as Kanter's convention); no reference is held
   for it either.
3. **M 6(a), where it is disclosed.** The paragraph is not formalized: the formal proof takes C5
   in the form with $\Lambda$-almost every measure a $u_K$. The record does not say where the
   paper should say so. It is now a departure of C5 in § 1.1 (one clause) and in § 2.6 (two
   sentences), since § 1.1 owns every step that is neither machine-checked nor cited.
4. **M 6(b).** Two reading steps that the record does not mention are written into the ledger:
   Lemma 3.1 supposes a log-concave *measure*, which a law with a log-concave density is by the
   converse half of Kanter's Lemma 2.1 (p. 68); and for a singular covariance $U_L \subseteq U_N$
   is needed, which is immediate from Definition 3.1 and is not printed. Where the module spends
   the entry, $A = aI$ and the second is not needed.
5. **M 8.** The record puts the display with one sentence in the prose after the proposition and
   says "the constants are far from sharp". The display is in § 3.3 and the derivation in
   Appendix A, to pay for it in the main text; nothing is said about sharpness, which the paper
   has no statement for.
6. **M 2.** The value at which the curve on the line levels off, $(2\pi)^{-1/2}\Gamma(1/4)/
   \Gamma(3/4) \approx 1.18$, is not printed. It is correct (Theorem 3.12(3) with the gamma
   delay), and it costs two lines for a number the figure shows.
7. **M 3.** "Its polar profile is zero" for "$c = 0$": in § 4, $c$ is introduced as the power at
   which the transform of a kernel with no Gaussian part falls off, which is not what $c$ is for
   the Gaussian.
8. **C 2(b).** The record's second sentence for § 4, "The condition is sufficient: the paper does
   not determine when a derivative filter exists in a weaker sense", is not added. "Is enough
   for" says that the condition is sufficient, and § 4.1 has the question of the derivatives.
9. **C 9.** The record's sentence for the caption of Table 3 is not added. The float page of
   Figure 1 and Table 3 fits by about four points: with "of the published article" in the cell
   the first row gained a line and the page was too large by 5.3 pt. The cell is kept to its
   length by writing "arXiv Prop. 2.3" for "Prop. 2.3 of the arXiv version" at the citation
   beside it. The sentence is in § 3 for the batch that rebuilds the page.
10. **C 6(b), the row of Lemma 3.3.** Said in one sentence of Appendix B, not filtered: the list
    stays the blueprint's `\lean` tags, and the report covers the three declarations.
11. **C 5.** The record's replacement is three sentences at the head of § 2. The dependence is
    said once, at the sentence that says what the section restates.

## 5. Sources read for this batch

At the page image, through `library page <citekey> --printed N --format image`:
`kanter1977unimodality`, pp. 68, 69, 70, 71, 72, 74, 77, 78, 84; `halgreen1979self`, pp. 13, 14,
15, 16, 17. In the text layer of a born-digital PDF: `fagerstrom2026cone`, pp. 13, 14, 15.

**For the librarian.**

- **To acquire**: Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, for Blaschke's
  selection theorem and the comparison of compact convex sets by support functions (the
  `% TODO(librarian)` at `blueprint/src/parts/03-isotropic.tex:1394–1401` and
  `paper-iso/appendix-isotropic.tex:1254–1256`). A reference for "the Borel sets of weak
  convergence on the probability measures of $\RR^d$ are the sets of the $\sigma$-algebra
  generated by the evaluations" is not held either.
- **The bibliography**: `halgreen1979self` is cited by the paper and is not in
  `paper-iso/references.bib`, which is not edited by hand. Until the file is regenerated the
  build has one undefined citation and `linkage paper` fails on it, and on nothing else.
- **Not held and not read**: Bondesson (1977), the preprint to which Halgreen credits the
  inverse-gamma case; Thorin (1977).

**For the hub.** `READING-halgreen1979self.md` obliges a source page
`wiki/sources/@halgreen1979self.md`.

## 6. Pages

`python records/affine/measure-section-pages.py paper-iso`
(`records/affine/measure-section-pages-q0424-iso-output.txt`).

| | before (`iso-review-1`) | after |
|---|---:|---:|
| main text | 29.96 | **30.43** |
| Appendix A | 24.36 | 27.47 |
| Appendix B | 3.14 | 3.50 |
| the PDF | 61 pages | 65 pages |

**The main text is over the limit of 30 pages by 0.43 page, about twenty printed lines.** The
additions could not be paid for inside the passages touched, and framing text was not cut. By
passage, in printed lines: the opening of § 3.3 on sampling and derivatives +4; the closed form
of $A_\beta$ with its display +6; the Matérn reading and the figure +2; "for $c \le d$" and
$c > d$ +2; Halgreen after Proposition 3.11 +2; § 2.6 after C5 +5 and after C6 +2; the head of
§ 2 +2; Proposition 2.7 +1; § 1 question 2 +1; § 1.1 +1 (its opening +2, the departures +1, the
paragraph on C5 −3, $A_\beta$ +1); § 4 −1 (the practice paragraph +2, § 4.1 −3). The plan's D9
expects about 25 lines from § 1.2 and § 1.3 and names the cuts that recover about 35 (the second
paragraph of § 4, the tier paragraph of § 3.3, two passages of the opening of § 3.4, Table 3's
anchors, Definition 3.18), all of them the framing batch's. The appendices grew by 3.5 pages:
the paragraph on $W_d$ (0.9), the derivation of $A_\beta$ (0.5), the three steps of the route
(1.9), Appendix B (0.4).

## 7. Gates

Run in the worktree `spatial-hemigroup-affine-q0424`, which has no Lean build.

| gate | result |
|---|---|
| `linkage check` (`WIKI_VAULT` set) | OK, exit 0: 98 shared statements, 88 verbatim, 10 tracked by sha, 0 needing attention; shared proofs 19 verbatim, 39 tracked by sha, 17 to re-read, as before the item. Two advisories of the trust-base regions changed their wording and not their content (the status sentence of § 1.1 now reads `\ref{app:isotropic-proofs}` first; the order of the list of Appendix B). |
| `linkage paper` | exit 1 on one problem, the expected one: `\cite{halgreen1979self}` resolves in no `references.bib`. Abstract 249 words, 4/4 declarations. One advisory more of the standing kind (a `\prog` pointer in step (c)). |
| `linkage axioms --check` | OK, exit 0 (twelve names, each backed by a ledger entry). |
| `python records/affine/check-paper-iso-backmatter.py` | exit 0. |
| `python records/affine/check-restated-labels.py` | exit 0. |
| `uv run --no-project --with mpmath python records/affine/check-matern-rate-constants.py` | exit 0. |
| `python scripts/check-control-chars.py` | OK (9718 files). |
| `python records/affine/gen-verification-table.py check` | "26 rows, 144 declarations: equal to the blueprint's lean tags". |
| `python records/affine/axioms-iso-all-declarations.py table` | exit 0, "ALL CHECKS PASS" (141 reported; 110 on the logical axioms only, 31 naming a cited fact; every statement's set equal to Table 1). |
| `paper-iso`, `latexmk -g -pdf` | 65 pages; no overfull box; no float too large; undefined: the citation `halgreen1979self`, once, and nothing else. |
| `paper`, `latexmk -g -pdf` | 101 pages; not touched by this item. |
| `bash scripts/build-blueprint.sh` | exit 0: control characters, `linkage check`, `print.pdf` (167 pages), the web build, the manifest with every node rendered (131 labels, 114 proofs). |

**Not run here, for the dispatching session, on the worktree with the build**: `linkage check
--fresh-axioms`, `python records/affine/check-axiom-guard.py` (the axiom guard), `linkage
boundary`, and `python records/affine/run-freeze-gates.py` at the second freeze. No Lean file
changed, so the stamped block of Appendix B and the report of the 141 declarations stand.
