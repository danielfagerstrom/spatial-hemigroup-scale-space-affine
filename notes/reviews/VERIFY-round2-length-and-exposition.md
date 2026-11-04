# VERIFY, round 2: the paper's length and its exposition

Assessment for the author's decision on length and format (Q-0433). Read-only: no `.tex`, no
blueprint and no Lean was touched. Measured at `ef3570b` (`iso-review-2` plus one commit of
records), 2026-10-13. Sources: the five reviews of round 2 (A to E, this directory), the paper's
sources, `measure-section-pages.py`, article-kit's `LINKAGE.md` and `PROCESS.md` § 7, and the
journals' own pages.

How the numbers were made. The parts are `python records/affine/measure-section-pages.py
paper-iso`, run today. The proof lengths are from a second scratch build with a position marker
at the start and end of every statement and proof; the markers shift the whole document by 0.2
page, so a single length is good to about 0.05 page.

## 1. The paper as it is

86 pages; 85.15 to the end of the text.

| Part | Pages | | Part | Pages |
|---|---|---|---|---|
| Title and abstract | 0.56 | | § 3 opening | 0.14 |
| § 1 before § 1.1 | 3.70 | | § 3.1 The axioms | 1.66 |
| § 1.1 What is machine-checked | 2.01 | | § 3.2 Reduction to the line | 4.27 |
| § 2 opening, § 2.1 | 0.46 | | § 3.3 The kernel at its centre | 5.88 |
| § 2.2 Axioms and classification on the line | 1.27 | | § 3.4 The dimension filtration | 4.18 |
| § 2.3 Subordination, the filtration | 1.63 | | § 4 Conclusion (§ 4.1: 0.35) | 1.15 |
| § 2.4, § 2.5 | 0.71 | | **Main text** | **29.99** |
| § 2.6 The cited facts | 2.23 | | Appendix A | 46.08 |
| § 2.7 Notation note | 0.13 | | Appendix B Verification | 4.75 |
| | | | AI statement, declarations | 0.70 |
| | | | References | 3.63 |

Appendix A by subsection: opening and Table 1 (notation) 1.14; A.1 Sources with Table 2, 1.72;
A.2 The axioms 2.15; A.3 Reduction to the line 4.32; A.4 The kernel at its centre 20.04; A.5 The
dimension filtration 16.72.

Appendix A, proof by proof. "MC" is machine-checked by § 1.1's lists. The last column says where
a proof repeats an earlier paper of the series or another proof of this paper.

| Statement | Proof, pages | MC | Repeats |
|---|---|---|---|
| Lemma 3.3 (operators and kernels) | 2.1 | yes | standard (Wendel), by review B |
| Lemma 3.4 | 0.3 | yes | no |
| Lemma 3.5 | 1.0 | yes | 0.6 page is the line paper's continuity argument (B) |
| Theorem 3.6, sufficiency and uniqueness | 0.4 | yes | no |
| Corollary 3.7 | 0.2 | yes | no |
| Lemma 3.8 | 0.3 | yes | no |
| Lemma A.1 | 0.1 | yes | no |
| Proposition 3.10 | 1.3 | yes | no |
| Proposition 3.11 | 0.5 | yes | cites the cone paper |
| Lemma A.2 | 0.4 | yes | no |
| Lemma A.3 | 1.0 | yes | no |
| Theorem 3.12 (the threshold) | 1.8 | yes | no |
| Corollary 3.13 | 0.7 | yes | no |
| Proposition A.4 (lower bound) | 1.6 | yes | no |
| Proposition 3.15 | 2.9 | yes | no; the Borel-set paragraph is 0.9 |
| Proposition A.5 (upper bound) | 0.9 | yes | no |
| Proposition 3.16 (rate, transform) | 2.5 | yes | no |
| Proposition A.6 | 2.1 | yes | no |
| **Lemma A.7** (the constant) | 1.3 | **no** | no |
| Proposition 3.17 (rate, profile) | 1.0 | yes | no |
| **Proposition 3.18** (the dictionary) | 2.1 | **no** | no |
| Lemma A.8 (the shadow) | 1.1 | yes | no |
| Proposition 3.19 (the test) | 0.5 | yes | no |
| **Corollary A.9** | 0.2 | **no** | no |
| Lemma A.10 | 1.2 | yes | opens with the cone paper's App. A, restated |
| Lemma A.11 | 0.9 | yes | no |
| Lemma A.12 | 0.7 | yes | no |
| Lemma A.13 | 0.6 | yes | extends the cone paper's Prop. 4.9(2) |
| **Proposition A.14** (the family as laws) | 1.2 | **no** | no |
| Theorem A.15 (strictness) | 3.2 | yes | (1) is Theorem 3.21(1),(4) again, 0.5; (3) is the cone paper's route, 2.5 |
| Theorem 3.21 | 0.8 | yes | no |
| Theorem A.16 | 0.9 | yes | second proof of Proposition 3.19(3) |

Totals: printed proofs 35.8 pages, of which 31.0 machine-checked and 4.75 not. The sixteen
appendix statements take 5.4 pages; a paragraph computing a constant 0.5; connecting prose 1.5.

Two numbers of the reviews do not hold. Review E's own list of cuts sums to 41 pages, which gives
45 pages, not "about 40". Review D's "about five pages" in A.5 measures 2.5 (3.6 if Theorem A.16
goes too). The "three-page" Borel-set proof (A, C) is 0.9 page.

## 2. What a journal expects

| Journal | Length of a regular paper | Supplementary material |
|---|---|---|
| J. Math. Imaging and Vision ([guidelines](https://link.springer.com/journal/10851/submission-guidelines)) | No limit stated. Only short papers have one: "10 double-spaced manuscript pages or less". | Accepted, PDF preferred; published as received, without editing or reformatting. Whether it is refereed is not said. |
| SIAM J. Imaging Sciences ([editorial policy](https://epubs.siam.org/journal/siims/editorial-policy)) | No formal limit; a paper over 30 journal pages, not counting supplementary material, is reviewed more closely to see that the length is justified. | Encouraged, and outside the count. Sister SIAM journals tell referees it is generally not refereed. |
| Int. J. Computer Vision ([guidelines](https://link.springer.com/journal/11263/submission-guidelines)) | No limit stated. | Same Springer rules as JMIV. |

Not confirmed. The SIAM pages refused a direct read; the sentence on 30 pages is from the search
engine's extract of the editorial-policy page, and SIIMS's own supplementary-materials policy was
not read. A figure of 20 to 30 pages for IJCV is from a commercial blog only. An old page of the
Kluwer period gave 36 double-spaced pages for JMIV; the current page does not.

What JMIV has printed: Lindeberg's axiomatics of 2011 is 46 journal pages (vol. 40, pp. 36–81),
cut from a technical report of 76. In Springer's two-column class a page of this manuscript is
roughly 0.6 to 0.7 journal page (my estimate from the word counts, not measured): 86 pages are
about 50 to 60 journal pages, 48 about 30 to 35.

The earlier papers. The line paper (`fagerstrom2026spatial`) is 49 pages, the cone paper
(`fagerstrom2026cone`) 89 pages. Both are Zenodo preprints, version 0.1, one document each, with
their own § 1.1 "What is machine-checked"; neither was a journal submission. article-kit's
template says "preprint first", built for a journal of JMIV's kind. The 30-page limit on the main
text is the project's own (the plan's D9), not a journal's.

## 3. Three options

### (a) As it is: 86 pages, one document

| | Pages |
|---|---|
| Main text | 30.0 |
| Appendix A | 46.1 |
| Appendix B, back matter, references | 9.1 |
| **Total** | **86** |

A referee: all five reviews ask for cuts; E gives major revision partly on length, A calls it far
too long for a journal. No guideline forbids it, but it is some 50 to 60 journal pages, above the
longest comparable JMIV paper found. The reader pays twice: five pages of trust-base and cited
facts before Theorem 3.6, and 31 pages of proofs that Lean has already checked. Nothing is lost.
Work: none. It is the format of the line and cone preprints.

### (b) A journal paper with a supplement: 48 pages and a supplement of about 40

| Stays in print | Pages |
|---|---|
| Main text, with § 1.1 as one paragraph and the two lists (0.4) and § 2.6 as one paragraph naming C1 to C7 with source and page (0.4) | 26.6 |
| Notation table; Sources (A.1, Table 2) | 2.8 |
| Proofs of the classification: Lemma 3.4, Theorem 3.6, Corollary 3.7, Lemma 3.8, Lemma A.1, Proposition 3.10; Lemma 3.5 as a pointer | 2.9 |
| The four statements that are not machine-checked, with proofs: Proposition 3.18, Corollary A.9, Proposition A.14, Lemma A.7 | 6.0 |
| Statements those proofs and the main text use, without proofs: A.3, A.4, A.5, A.6, A.8, A.13 | 2.6 |
| Proof of Proposition 3.19 (the test; short) | 0.5 |
| Connecting prose | 0.6 |
| Appendix B: where the development is, versions, the nine names, Table 3, the restated statements | 1.7 |
| AI statement, declarations, references | 4.3 |
| **Total** | **48** |

| Moves to the supplement | Pages |
|---|---|
| Proofs of machine-checked statements: A.2 whole; from A.3 the proofs of 3.5 and 3.11; A.4 whole except Lemma A.7; A.5 except the four items above | 27.9 |
| Statements used only there: A.2, A.10, A.11, A.12, A.15, A.16; the constant's paragraph; prose | 3.0 |
| § 2.6 in full (the seven cited facts with their departures) | 2.2 |
| § 1.1's three long paragraphs | 1.4 |
| Appendix B's list of 198 declarations, Lean's report, the guard, the formal examples | 3.1 |
| Title, opening, its references | 2.0 |
| **Total** | **about 40** |

Why the classification proofs stay: the classification is the result the author names as the
paper's point, the chain is three pages, and a reader in scale-space theory can follow it. The
threshold's proof (1.8 pages, and 1.4 of lemmas) is the next candidate to keep; I leave it out.
48 becomes 44 with E's rewrites of the main text (the rate stated once, Example 3.14 in one
place, § 4 without the repeat); 40 is reached only if the classification proofs leave print as
well, which I advise against.

What the supplement is: a second PDF from the same directory, `paper-iso/supplement.tex` beside
`main.tex`, with numbers S.1, S.2, … and cross-references through `xr-hyper`. A third root can
still build the one document of 86 pages for the preprint, so (b) does not close (a).

The mirror rule. `linkage check` reads every `.tex` file of `paper-iso/`, whichever root includes
it (`linkage/artifacts.py`, `sorted(d.glob("*.tex"))`), and matches a moved proof to its statement
by the `\ref` in its heading. So every shared statement and every proof stays compared with the
blueprint, verbatim, for both PDFs. A proof may also simply be absent: an unmatched proof is an
advisory that never changes the exit code, and `% proof omitted` after the marker silences it
(`LINKAGE.md`, "A proof moved off its statement"). No shared statement changes; no blueprint
change; no Lean.

Lost in print: 31 pages of proofs, each still deposited and each machine-checked. A referee:
this is what E asks for and what SIIMS's rule on length assumes; the cut follows one rule
(checked by Lean goes to the supplement, proved only in print stays), which is easy to defend
since a supplement is usually not refereed. One risk: a referee who wants the seven cited facts
in print; keeping § 2.6 in Appendix B gives 50 pages. PROCESS.md § 7 asks that each cited fact be
stated before its first use, so the paragraph in § 2 is a departure the author allows or not.

Work: one session. Files: `01-introduction.tex`, `02-line-papers.tex` (the seven blocks move with
their markers), `appendix-isotropic.tex` and `appendix-verification.tex` (each split in two), a
new `supplement.tex`. Three gate scripts follow the files (the two Appendix B checks, the page
measure). About one page of new prose for the author to read. A new freeze.

### (c) The paper with the agreed cuts, no supplement: 79 pages

| Cut | Pages | Touches |
|---|---|---|
| A.5 (D): Theorem A.15(3)'s three steps cut to one, clause (1)'s proof replaced by a pointer | −2.0 | proof only, re-pinned |
| A.2, A.3 (B): Lemma 3.5 by Lemma 3.3(2); Lemma 3.3's standard parts cited | −1.9 | proofs only, re-pinned |
| A.4 (C): the Borel-set paragraph cut to a citation | −0.8 | proof only |
| Appendix B (A): Lean's eight reports, three short paragraphs | −1.4 | one gate retired |
| § 1.1's list of C1 to C7, which § 2.6 repeats | −0.4 | prose |
| § 1 and § 4 say the answers three times (E, A) | −1.0 | prose |
| **Total** | **−7.5 → 79** | |

Deleting Theorem A.15(1),(2), as D asks, saves 0.7 more (78) but changes a shared statement: the
blueprint node, its four Lean tags, Appendix B's row and Table 3. Moving § 1.1's three paragraphs
and § 2.6's statements to Appendix B takes the main text to about 25 pages without changing the
total.

Lost: nothing of substance. A referee: the complaint about length stands at 79 pages. Work: as
much as (b) for a fifth of the gain. Four proofs are rewritten, so the paper's proofs are no
longer verbatim with the proofs of record but pinned to them (`--pin-shared`), or the blueprint's
proofs are shortened too; the new proof of Lemma 3.5 needs a blind check.

## 4. Exposition items worth doing under any option

For a reader in scale-space theory. None changes a shared statement.

| # | Page | What is wrong | Fix |
|---|---|---|---|
| 1 | 1 | The abstract uses "admits" unexplained, "self-decomposable" unglossed, and "this correspondence … that family" point back three sentences (E, A). | Say that an F of the line need not be one in the plane; gloss the term in a clause; end with "except four, listed in § 1.1". |
| 2 | 2, 17–18 | "Profile" is the folded profile on p. 2 and the polar profile from p. 17 (E). | "On the line" on p. 2, and announce the profile of § 3.2. |
| 3 | 3, 9, 24, 29 | Terms before or without definition: "slowly varying" (p. 3, defined p. 13), "Lévy process" (p. 9, defined p. 32), "radial characteristic function" (p. 3, p. 26), "the peak of the opening" (p. 24, never), "window by window" (p. 29) (E, A, C). | A clause at first use; "the peak of the record of a point source"; "between consecutive dimensions". |
| 4 | 3–5, 29–30 | The answers are given three times (E, A). | Merge "The answers" with "What the paper contributes"; § 4 keeps the limits and open problems. |
| 5 | 17 | The main result is assembled by the reader from Theorem 3.6, Lemma 3.8 and Proposition 3.10(2) (B). | One corollary after Lemma 3.8: a law is a kernel from scale zero of such a family exactly when it is rotation invariant, self-decomposable and not a point mass. |
| 6 | 16, 23–25 | One letter, two roles: c in the uniqueness clause of Theorem 3.6; K beside the Bessel K_ν; Q, A, R (E). | Rename the gauge ratio and three constants in the prose; Table 1 shrinks. |
| 7 | 20–21 | Theorem 3.12 is a page of five clauses, and (4) uses a g_t defined in an appendix lemma (E). | Before it, say which clauses carry the result, (1), (2), (5), and give g_t's formula. |
| 8 | 24 | Proposition 3.17 takes C_k, K and ϰ_d "as in Proposition A.6" (A, C, E). | Print the statements of A.6 and A.7 in § 3.3 before it; the text is unchanged. |
| 9 | 22, 23, 25, 27 | Example 3.14 comes in four pieces (E). | One example after Proposition 3.17, with a small table of the Matérn numbers. |
| 10 | 20, 29 | The captions leave out what a reader checks (E, D). | Figure 1: the slopes −1/2 and −3/2; Figure 2: the bound is drawn for d ≥ 3, and the interval (1.20, 1.74). |

## 5. Recommendation

Take (b) at 48 pages: it is what the journals provide for, its dividing line is the paper's own
(what Lean checked goes to the supplement, what is proved only in print stays), and it touches
no shared statement, no blueprint node and no Lean. Do the ten items of § 4 in the same pass, and
leave (c)'s rewrites of proofs undone, since under (b) those proofs are out of print anyway. The
86-page document stays buildable from the same sources for the preprint, so nothing is decided
that a journal's answer could not undo.
