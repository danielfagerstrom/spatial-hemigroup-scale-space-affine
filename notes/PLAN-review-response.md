# PLAN — response to the external review of the affine paper, rounds 1 and 2 (2026-11-03)

Article-kit `PROCESS.md` § 9. The build reviewed is `07a131d` (`review-1`, 108 pages). The review
is Gemini 4.0 Argon at its high setting, run by the author, archived as returned:
`records/affine/reviews/review-content-review-1-Gemini-4.0-Argon-High.md`. **Rounds run in
sequence** (the author's decision of 2026-11-03): this round's changes are applied and frozen as
`review-2` before round 2 (the presentation review) is run.

**The review.** *Minor-to-major revision.* It finds the mathematics sound ("free of fatal flaws"),
the trust base exemplary, and the positioning accurate. It asks for: the headline claims narrowed
to what is proved; Proposition 4.15's complete proof in print; Proposition 4.20 made
self-contained; the numerical remarks made reproducible from the page; identifiers for the
companion papers; a notation slip fixed; and a much shorter paper. Eleven required changes, six
suggestions.

**The verification.** Every finding was checked against the build, the paper, the blueprint, the
Lean and the sources by three verifiers that did not write the paper:
`records/affine/reviews/VERIFY-round1-claims-paper.md` (12 findings: 8 confirmed, 3 partly, 1
refuted), `VERIFY-round1-mathematics-paper.md` (14: no error in the mathematics; 3 confirmed
defects of presentation, 1 referee step refuted) and `VERIFY-round1-exposition-paper.md` (14; both
deposited scripts re-run and reproduced), with scripts in `verify-round1-paper-scripts/`. Where
the referee was wrong: the count "7 of 9 cells incomplete" (two are complete on PSD(d) and three
more in a stated restricted sense); "§ 1 does not say where Theorem 3.7's orbit form comes from"
(it cites Lemma 3.9); the inequality given for Proposition H.1(3) (the paper's is right, the
referee's fails at $d = 2$, $\alpha = 1$, $\kappa = 2$); "80 % identical" sketches (18–22 %
verbatim, a third of the length); the saving of "8–10 pages" from repetition (about 1–2.5); and
"45–50 pages" (all the proposed moves together reach about 83–86).

**Nothing in the paper, the blueprint or the Lean has changed yet.**

## 0. Decided (the author, 2026-11-03)

- **D1 and D2:** the complete proofs of Propositions 4.15 and 4.19 are printed in Appendix B in
  place of their sketches (the blueprint's proofs of record); the other twenty sketched statements
  keep their sketches, and the deposited sources get a citable address in § 1.1 and Appendix I.
- **D3:** fold § 4.3's prose after the legend into § 1 and shorten § 5's summary; replace the body
  sketches of Theorem 4.21, Lemma 4.8 and Proposition 4.13, which Appendix C proves in full, by
  short pointers. No merging of propositions, no supplement.
- **D4 (a):** credit Felsberg and Sommer 2004 (Thm. 1, p. 7) in § 3.5 and cite Felsberg and
  Sommer 2001, p. 130, after a reading note; amend the prior-art record's row C. The dissertation
  is not requested.
- **D5:** no new clause; the abstract is narrowed only (B1).

## 1. Decisions for the author (as put on 2026-11-03)

- **D1. Proposition 4.15's complete proof.** The paper prints a sketch only; the blueprint's
  complete proof is about 0.9 page. (a) Print the blueprint's proof in Appendix B in place of the
  sketch (+0.6 page net). (b) Write a complete proof through Remark 4.16's published route (Crum,
  Sasvári; about 0 pages net, but not the Lean's route, so a proof of record would diverge from the
  formal one). (c) Keep the sketch and point to the deposited proof by a citable address.
  *Recommended: (a).*
- **D2. The other sketched statements.** 22 statements have no complete proof in print (the list
  is in `VERIFY-round1-mathematics-paper.md`); each has a complete blueprint proof. (a) Print the
  two of the main text (4.15, 4.19) and point to the deposit for the rest. (b) Print all (+15
  pages). (c) Print none, point to the deposit. Either way the deposit gets a citable address (the
  DOI of the release and the node labels) in § 1.1 and Appendix I. *Recommended: (a).*
- **D3. Length.** The author's `adr/0006` keeps the smaller groups and sets no page budget. The
  measured options: fold § 4.3's prose after the legend into § 1 and shorten § 5's summary (−1 to
  −2.5 pages); replace the body sketches that Appendix C proves in full by pointers (−0.5 to −1.5);
  prove Proposition 3.4(3) from 4.5 and fold Proposition E.2's formula into 4.17 (small; touches
  four blueprint nodes); move Appendices D and E to a supplement (−4.8). Moving F–H would reverse
  `adr/0006` item 5. *Recommended: the first two only; the rest no.*
- **D4. Felsberg.** The paper credits the Poisson scale space to Duits et al. alone and cites
  neither Felsberg–Sommer paper. The held `felsberg2001scale`, p. 130, proposes "a 2 × 2 scaling
  matrix instead of the real scale parameter s", with no analysis; the 2002 dissertation the
  referee names is not held. (a) Credit `felsberg2004monogenic` (Thm. 1, p. 7) in § 3.5 and cite
  `felsberg2001scale`, p. 130, as an earlier proposal of a matrix-scale Poisson space, after a
  reading note; amend the prior-art record's row C. (b) Also request the dissertation.
  (c) Neither. *Recommended: (a).*
- **D5. The dichotomy in Proposition 4.22(3).** The abstract's "admits the Gaussian alone" is
  narrowed to "admits only Gaussian families" (batch B1). Stating that such an order admits the
  Gaussian exactly when it lies in the Loewner order would be a new claim: a blueprint clause, a
  proof and Lean. *Recommended: no.*

## 2. Batches of safe fixes (`adr/0003`: narrowing, wording, a slip, a missing parameter)

- **B1. Claims** (`VERIFY-round1-claims-paper.md`): the abstract ("describes … completely in some
  cases and by bounds or examples in the others"; "admits only Gaussian families"; the rational
  symbols as linear images of one law; what $\alpha$ indexes; "shape change" for "turning"; within
  250 words); § 1 ("needs both": neither the Loewner order alone nor the group alone forces the
  Gaussian; "turning"); § 5 (every cell accounted for; the rational symbols); Table 2's cells
  $(D_+, \le_\alpha)$ and $(D_+, \text{Loewner})$; § 4.8 "scale parameters in the variance gauge";
  § 4.9 $b \ge 0$; "turn" kept for rotation of the axes only throughout.
- **B2. Mathematics** (`VERIFY-round1-mathematics-paper.md`): Proposition H.5's $Q/R/Q'$ slip, at
  the blueprint node, its proof, the paper's copy and the Lean docstring of
  `anisotropy_functionals`; Proposition 4.20 made self-contained (cond, $\mathcal M_s$, $\psi_\Sigma$
  and es defined in its preamble, H.4's covariance restated, $T_s$ dropped), at the blueprint and
  re-transcribed (`adr/0004`); Proposition 4.15's Fourier convention brought to the paper's; one
  line each in the sketches of H.1(3) and H.4(4); one sentence in Appendix C.4 saying why it
  re-derives the order (to keep C4 out of Theorem 4.21's trust base).
- **B3. Numbers, references, exposition** (`VERIFY-round1-exposition-paper.md`): Remark E.5 states
  the operator, its five-point form for the diagonal steps computed (the printed "nine-point" is
  corrected), the symbol and the torus size; Remark H.3 states the box and the two grids; Table 2's
  legend gets one-line formulas for $C_\alpha$, the Lévy profile, $R(\lambda)$ and $\beta_-(k)$;
  the bibliography style `plainurl`, as the isotropic paper's, so every DOI prints (the companion
  papers' included; about +0.9 page).
- **Librarian.** The programme's papers' records hold version DOIs; `CLAUDE.md` cites an earlier
  module by its concept DOI. A desktop librarian aligns the records; not the paper's change.

## 3. Then

Apply B1–B3 and the decided items, each refereed blind where it adds or changes mathematics; build,
`linkage check`, `linkage paper`; freeze `review-2`; run round 2 (part B, the presentation review).

---

# Round 2 — the presentation review of `review-2` (2026-11-03)

The build reviewed is `5f6f72c` (`review-2`, 108 pages), round 1's response refereed blind. The
review is part B of `reviews/PROMPT-round2-paper.md`, Gemini 4.0 Argon at its high setting, run by
the author, archived as returned: `reviews/review-presentation-review-2-Gemini-4.0-Argon-High.md`
(twenty changes, ranked).

**The verification.** Every item, and every claim inside its proposed fix, was checked against the
build, the blueprint, the Lean and the sources by three verifiers that did not write the paper:
`reviews/VERIFY-round2-front-paper.md` (items 1–3, 16–18), `VERIFY-round2-notation-paper.md` (5,
6, 11–15, 19) and `VERIFY-round2-structure-paper.md` (4, 7–10, 20), with scripts in
`reviews/verify-round2-paper-scripts/`. Nearly every item is *partly* right: the defect it names is
often real, and the paper often already says much of what it calls missing. Of the proposed texts,
many carry a wrong detail, and the records give a corrected wording for each one taken. Where the
reviewer was wrong:
- the twenty sketches are not complete proofs (10–48 % of the blueprint proofs; E.4 omits steps);
- the line results are not machine-checked "from first principles" in this development: it no
  longer requires the line paper's package, which § 1.1 and Appendix I still say it does (a defect
  the review did not name);
- Theorem 4.3(3)'s order is not a counterexample to "wedge datum" (it is on PD(d) and lacks the
  rays);
- Figure 3(a) has no axis arrow to collide (the real collision is "rays" in Figure 2(a));
- the condensed Table 2 cell is no shorter and drops a hypothesis of H.1(3);
- $\le_\alpha$ is not defined for $2 \le \alpha < \infty$, so Theorem 4.21(3) cannot use it;
- "or increase its minimum scale" is false for the Matérn, logarithmic and rational-symbol orbits;
- the programme's paper names and the version sentence are rules (`WRITING.md` § 1, `adr/0005`),
  and the dates are past.

## R2.0. Decided (the author, 2026-11-03)

- **D6** (items 1, 2.2, 2.3): **both changes.** In § 1, "What is an affine scale space?" and "The two
  choices" move before the earlier papers, rewritten so that no term is used before it is taught.
  The abstract gains about 9–15 words on what $\alpha$ measures and on re-measurement against
  cascade, with a cut elsewhere so that it stays near 250 words. Gemini's false clause ("or increase
  its minimum scale") stays out.
- **D7** (items 7, 12): the exponent cone $K_\alpha \to \mathfrak k_\alpha$, in the blueprint and
  the paper. "Wedge datum" is kept, with one clause saying Definition 3.1 needs no cone.
- **D8** (item 9): **split Proposition 4.20.** Clauses (1)–(2) stay in § 4.6. Clauses (3)–(5)
  become a node of their own, printed in § 4.9 as Proposition 4.24.
- **D9** (item 8): **neither move.** The proof of 4.22 stays in the body, with its tautological first
  sentence fixed. F.2 and H.1 stay in the appendices.

## R2.1. Decisions for the author (as put on 2026-11-03)

1. **§ 1's order and the abstract** (items 1, 2.2, 2.3). Keep § 1's order from pass 6 and
   `adr/0006`, and keep the abstract at its 250-word budget (recommended). Or move "What is an
   affine scale space?" and "The two choices" before the earlier papers, done correctly. Or add
   about 9–15 words on $\alpha$'s meaning, with a cut elsewhere.
2. **Two names** (items 7, 12). "Wedge datum" is decided in `GATE-affine.md` rows 17 and 132 and
   is a Lean structure. Renaming it touches 99 lines and `WedgeDatum`, so keep it (recommended),
   with one clause saying Definition 3.1 needs no cone. The exponent cone $K_\alpha \subseteq
   \mathfrak{gl}(d)$ against the step cone $\mathcal K_\alpha \subseteq \mathrm{PD}(d)$ is owed since
   `GATE-affine.md:94`. Rename the exponent cone to $\mathfrak k_\alpha$ (recommended: about 20
   paper and 26 blueprint lines, re-pins). The alternatives are renaming the step cone or keeping
   both.
3. **Proposition 4.20** (item 9). Split the blueprint node into clauses (1)–(2) and (3)–(5); its
   `\lean` tags are already per clause. Print (3)–(5) in § 4.9 as Proposition 4.24 (recommended:
   nothing else renumbers; ten clause citations re-typed). Or split and keep both in § 4.6, or leave
   it.
4. **§§ 4.8–4.9** (item 8). Moving 4.22's proof to an appendix reverses Q-0290 and recreates the
   double printing D3 removed; decline it and fix the tautological first sentence (recommended).
   Moving the statements of F.2 and H.1 into § 4.9 reverses Q-0312 and Q-0290 and renumbers F.3–F.5
   and H.2–H.9 (not recommended). Shortening 4.22(1)'s proof would take it off the Lean route (not
   recommended).

Taken without asking (the recommendation stands unless vetoed): item 5's link is one sentence citing
[16, Prop. 3.11], not a restated statement. Item 17.3 (the private path `notes/PROCESS.md` and the
ratio's wording in the AI statement) goes to pass 5.

## R2.2. Batches of safe fixes (`adr/0003`)

- **B4, the blueprint (shared statements and proofs of record, re-transcribed under `adr/0004`).**
  - $k_I \to k_d$ in Proposition H.8, its proof, and H.9(2) (item 6).
  - "null space $\ker P$" for "kernel" in Proposition 4.22 (three occurrences), and the tautological
    first sentence of its proof (items 15, 8).
  - $\omega$ for $\xi$ in Lemma 3.8 and the two proofs of record that break p. 7's rule (item 15).
  - The decided renames and the split of 4.20, if taken.
- **B5, the paper's prose.**
  - De-duplicate § 2.1 and § 2's opening against § 1 (item 1).
  - "on covariance matrices" → "on scale matrices" in the abstract (2.1).
  - § 1's shape-adaptation paragraph, with the verifier's rewrite (3).
  - Table 2's legend: $D_s$, $\Delta(\Sigma)$, $\mathrm{sym}\,B$, "$B$-self-decomposable"; the gloss
    "$r^\alpha k(r)$ nonincreasing"; and "not beyond it" → "need not be beyond it", false as a
    universal (4).
  - One sentence after Definition 2.8 citing [16, Prop. 3.11] (5).
  - § 4.6's "size of the failure" with the mechanism, hypotheses $d \ge 2$, $P \ne 0$ (11).
  - One sentence relating the two scale conventions, with $t(vI) = \sqrt v$ (13).
  - § 3.2's "itself an axiom" replaced (14).
  - $\omega$ on pp. 22, 60, 64, 75, 79, and p. 7's wording (15).
  - "A proof marked as a sketch" in § 1.1 and Appendix I (16.1).
  - **§ 1.1 and Appendix I corrected: the development requires ScaleSpaceCore and Mathlib, not the
    line paper's package** (16.2).
  - The three logical axioms named (16.3).
  - "in preparation" for "a further paper, not yet released" on pp. 5 and 53 (17.1).
  - Remarks 3.13 and 3.11 said in place (18.3, 18.4).
  - § 4.4's motivation of curves and majorization (19).
  - Table 1: rows for $N(0,C)$, $\mathrm{sym}\,B$, $D_s$, $\Delta(\Sigma)$ (20).
- **B6, the figures** (item 10).
  - Figures 1 and 3 drawn at their printed size with 8–9 pt labels.
  - "rays" moved clear in Figure 2(a), and $v$ unrotated in Figure 3(b).
  - "unit direction $w$" in Figure 1's caption.
  - Figure 2's caption clause on the doubled angle, and the arrow at $\alpha = 1$, with the x-range
    widened.
  - Each script re-run with its output.
- **Outside the review.** `Formalization/README.md` gives ScaleSpaceCore v0.4.0 where the lakefile
  pins v0.5.0. The comment at `paper/02-line-papers.tex:212-219` describes an include Q-0365 removed.

**Declined**, with the reasons in the records:
- the reviewer's sentences for items 1, 2.3, 3, 7, 16.1, 16.2 and 17.3;
- $k_{\mathrm V}$ (item 6);
- the move of 4.22's proof (8.1);
- $\le_\alpha$ in Theorem 4.21(3) (12);
- "aperture kernel", and $\omega$ in § 2.3 and C2 (15);
- the condensed Table 2 cell (4.3);
- "Working draft", which the release replaces (17.1);
- the paper names and the version sentence (17.2);
- items 18.1 and 18.2.

## R2.3. Then

Apply B4–B6 and the decided items; referee blind; build, `linkage check`, `linkage paper`; freeze
`review-3`. The second content review, in another vendor's system when one is available, reads it.

---

# Round 3 — the second content review of `review-3` (2026-11-03)

The build reviewed is `59c56bd` (`review-3`, 110 pages). No system of another vendor was available,
so the author chose Claude Fable 5.1. Five blind referees each took one block of
`reviews/PROMPT-round3-paper.md`; the prompt's "How this round was run" records the procedure and
the caveat that Fable shares a vendor with the model that wrote the text. The reports are
`reviews/review-content-review-3-{A,B,C,D,E}-*-claude-fable-5.1.md`. Blocks A–D recommend minor
revision; block E recommends major revision.

**The verification.** Every finding was checked, by three verifiers, against the build, the
blueprint, the Lean and the sources: `reviews/VERIFY-round3-front-classical-paper.md` (A, B),
`VERIFY-round3-landscape-orbits-paper.md` (C, D) and `VERIFY-round3-smaller-groups-paper.md` (E),
with scripts in `reviews/verify-round3-paper-scripts/`.
- **No theorem and no proof's logic is wrong.** Lemma 2.9(2)'s "factor of four" was `pdftotext`
  setting $c/2$ as "2c", so neither this paper nor the released isotropic paper needs an erratum.
  The "transposed product" in 4.10's proof is a stray glyph of the text layer.
- **Real errors, all safe to fix:**
  - the union of the exponent cones called the Gaussian's cone (p. 41, and a blueprint annotation):
    it is only dense in that cone;
  - "the coefficient beyond first order is not known" (Remark E.5, problem 6): it is computable, and
    the grid agrees with it within 1–4 % at index 2;
  - Proposition 4.19's commentary, which lacks $a = 0$;
  - "the ordered-density cone" (4.13): a dyadic profile gives a step whose square root is not a
    step, so no cone generates the set;
  - "the base must be positive definite" (p. 4), a false necessity;
  - a report page cited for [37];
  - Wendel's theorem and the compactness of a full law's symmetry group, used without credit;
  - a missing $G$-invariance step in Lemma 3.3(3)'s proof;
  - the sketches of H.7(2) and H.8(3), each short of a clause (the proofs of record are right);
  - the line-paper results that the formal development uses, proved in ScaleSpaceCore, which § 1.1
    does not say;
  - `blueprint/trust-boundary.txt`'s opening comment, which still names Paper V's package.
- **A new result, confirmed (block E, item i).** The increments of a $(\GL(d),\le_\alpha)$-family are
  infinitely divisible (4.24(1), from Theorem 3.5). With H.2(1) and Lemma 4.14(4) this makes
  $R(\lambda) \ge \lambda^\alpha$ *necessary*: for a right-continuous profile and any Gaussian part,
  $N(0,aI) * \mu_I$ is in $\mathfrak F_\alpha$ if and only if $\beta_-(k) \ge \alpha$, and along a cone
  with $\beta(C) < 2$ the families depend on $\beta(C)$ alone. Calling the cell complete also needs the
  polar criterion (ledger A2, not among C1–C4). The single-step converse stays open.

## R3.0. Decided (the author, 2026-11-03)

- **D10** (E i): **state the new result, and add A2.** For the general linear group along the stable
  orders and the cone orders with $\beta(C) < 2$, membership becomes "if and only if" for
  right-continuous profiles with any Gaussian part. The polar criterion (ledger A2) joins the paper's
  cited facts, so that the (GL, stable) cell is a complete description. The Lean is assembled in a
  desktop session; until then the new statement is proved in print only, and § 1.1 says so.
- **D11** (E iii): **keep D2.** The twenty sketches stay, with the deposit address. The sketches of
  H.7(2) and H.8(3) are repaired.
- **D12** (B): **both.** A remark that (K2) enters Theorem 3.6 only at the boundary of $\PSD(d)$, with
  the family that shows it is needed there. A sentence in § 3.1 on the $\delta_0$ kernels that (K4)
  at the one pair $(0, I)$ allows.
- **D13** (sources): narrow the novelty paragraph after Theorem 4.3 to no priority claim, and ask the
  librarian for Lawson 1994. Cite Sato–Yamazato 1984 (p. 73) and Jurek 1982 (p. 385) in Appendix G.
  Ask the librarian for Nitzberg–Shiota, and cite it once read.

- **D14** (2026-11-04; the round-3 referee's finding 1): **drop "right-continuous" from 4.22(1).**
  $\beta_-(k)$ is unchanged when $k$ is replaced by its right-continuous modification, so (1) holds
  for every profile. (2) keeps the hypothesis where the description of the cell needs it.
- **D15** (2026-11-04): **no fourth review round.** Next comes the Lean of 4.22 and 3.11 in a desktop
  session, then pass 5 (the AI statement) and the release `v0.1`.
- **D16** (2026-11-04; the round-3 Lean's finding, `records/affine/REFEREE-lean-round3.md`, "For the author"):
  **drop $\alpha < 2$ and $\beta(C) < 2$ from 4.22(2).** Neither proof read them. The cell runs over
  $0 < \alpha < \infty$, and from $\alpha = 2$ on it is the Gaussian laws, as $\beta_-(k) < 2$. So the sets of laws of
  4.21(2)(c) and (3)(d) for finite $\alpha$ also hold on C1, C2 and C5, without C3, and the end of 4.21(2)(b), which spends
  nothing, then gives the families. 4.21's own proof stays on C3: the anisotropy budget's clause (1) spends C3 in any
  case, so C3 stays in the paper, and C1 with C5 is no lighter a route.

## R3.1. Decisions for the author (as put on 2026-11-03)

1. **The new result** (E i): (a) state it as "if and only if" in 4.20(2), 4.21(3)(c) and (2)(c). That
   is a proof of about six lines from 4.24(1), H.2(1) and 4.14(4), plus a Lean assembly in a desktop
   session (no Lean toolchain in the cloud). It brings rewrites of p. 48, open problems 1 and 3,
   Table 2 and § 5's count, and a blind referee. (b) As (a), with A2 added to the cited facts so that
   the cell is complete. (c) Leave it unstated.
2. **D2** (the twenty sketch-only statements; all have complete, `\leanok` blueprint proofs). Keep it
   and repair the two weak sketches (recommended). Or print the eleven that Table 2 cites in the
   smaller-group rows (+7.4 pp.), all twenty (+13.6 pp.), or the three that A asks for (4.4, 4.24,
   A.3; +1.8 pp.).
3. **Two remarks on the axioms** (B). A remark that (K2) enters Theorem 3.6 only at the boundary of
   $\PSD(d)$: between positive definite apertures (K1), (K3) and (K4) alone give the Gaussian form, and
   a $\theta$-family shows the boundary is needed (recommended). A sentence in § 3.1 that (K4) at the
   single pair $(0,I)$ allows similarity families whose kernel at a positive definite aperture is
   $\delta_0$ (recommended, in place of strengthening (K4)).
4. **Sources.**
   - Narrow the novelty paragraph after Theorem 4.3 to no priority claim, and ask the librarian to
     acquire Lawson 1994 (recommended). The paragraph's sources (Lawson, Hilgert–Neeb, Neeb 2000,
     Kostant) are not held.
   - In Appendix G, cite Sato–Yamazato 1984 (p. 73) and Jurek 1982 (p. 385), both held and read
     (recommended).
   - Whether to acquire and cite Nitzberg–Shiota on shape adaptation.

Taken unless vetoed:
- the dyadic counterexample is printed, and "the ordered-density cone" becomes "the step set" through
  the blueprint;
- the index-2 rate stays a numerical finding, with its coefficient named;
- Proposition 4.15's proof of record stays on the Lean route;
- the complete cells are named on p. 3 and in Table 2's caption, not in the abstract (D6's budget);
- the structural moves are declined (`adr/0006`, D3, D9), as are renaming "the main result" and the
  condensed cells.

## R3.2. Then

The safe fixes in batches, as in rounds 1 and 2 (blueprint first, then the prose); the decided items;
a blind referee; the build, `linkage check`, `linkage paper`; freeze `review-4` if another round is
wanted, or go to pass 5 and the release.
