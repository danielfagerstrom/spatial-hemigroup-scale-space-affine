# Verification of the presentation review, round 2 (the affine paper, `review-2`): Table 2 and § 4.3, "wedge datum", the placement of statements and proofs in §§ 4.6–4.9, the figures, Table 1

*2026-11-03. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is checked
against the text, the blueprint and the sources before anything changes. This record verifies items
4, 7, 8, 9, 10 and 20 of `review-presentation-review-2-Gemini-4.0-Argon-High.md` (twenty ranked
changes); the other items are verified elsewhere. This record changes no `.tex`, `.lean`, blueprint
or figure-script file.*

## Inputs and conventions

- **The build.** `review-build-review-2.pdf`, 108 pages, byte-identical to `paper/main.pdf` (`cmp`).
  The build was frozen at `5f6f72c` (commit `4a7a462`), and `git diff 5f6f72c HEAD -- paper
  blueprint` is empty: the sources are those of the build. Page numbers are the PDF's, which are
  the printed ones and the report's. Text was read with `pdftotext -layout`; pages 21, 29 and 33 were
  rendered with `pdftoppm -r 150` (and crops at 300 dpi) and looked at. Numbers and pages of labels
  are from `paper/main.aux`. Sources are cited as file:line.
- **Scripts** (`verify-round2-paper-scripts/`, each with its `-output.txt`): `typeset_lines.py`
  (typeset lines and vertical extent of a passage, from `pdftotext -bbox-layout`; output
  `typeset_lines-prop-4.22-output.txt`, `typeset_lines-F2-H1-output.txt`), `cell_length.py` (Table 2's (similarities, Loewner) cell
  against the review's condensed cell), `figure_fonts.py` (printed size of figure labels: font size
  in the script × printed width / figsize width, the printed width from `pdfimages -list`).
  Section lengths: `python3 records/affine/measure-section-pages.py paper`, in
  `measure-section-pages-review-2-output.txt`. A body line is 13.55 pt; a page holds about 51.
- **Earlier decisions that bear on these items.** Q-0290 (`paper/appendix-proofs.tex:1-12`, the
  author's decision of 2026-10-04): the main text keeps the proofs that carry its argument, among
  them `prop:shape-adapted-apertures`; Appendix H moved out of § 4.9 whole
  (`paper/appendix-similarity-loewner.tex:1-12`); the table moved forward with its forward
  references (`paper/05-table.tex:1-13`). Q-0312 (`paper/05-smaller-groups.tex:1-10`,
  `paper/appendix-smaller-groups.tex:1-7`): § 4.9 became a one-page summary, its statements moved to
  Appendix F, and `prop:similarity-stable-order-families` to the end of § 4.6 because
  `thm:wedge-axis` spends its clauses (1)–(2). Q-0281 (`blueprint/src/parts/05-shape-adapted.tex:68-72`):
  the proof of 4.22(1) was rewritten to the Lean route. `records/affine/GATE-affine.md` rows 17 and
  132: "wedge datum" kept, "wedge axis" being the axis of the wedge datum. Round 1
  (`records/affine/PLAN-review-response-paper.md` § 0): D1–D2 print complete proofs for the main
  text's sketched statements; D3 folded § 4.3's prose after the legend into § 1 and replaced body
  sketches of statements Appendix C proves in full by pointers. `adr/0006` item 5: § 4.9 and
  Appendices F–H keep their place; item 7: no page budget.
- **Verdicts.** **CONFIRMED**: the finding holds as stated. **PARTLY**: part holds, part not (both
  are said). **REFUTED**: the paper is right, and why.
- **Classes of response.** **safe**: a presentation change a session may make under `adr/0003`,
  stated as the exact change. **author**: changes structure, numbering, a name used across the
  paper, or chooses between routes. **decline**: wrong, or against a rule or an earlier decision.

---

## 4. Table 2 and § 4.3 forward-reference later notation (report pp. 30–31)

**Quotes.** Both are in the build: the "frame" bullet on p. 30 (`paper/05-table.tex:36-39`) and the
two phrases of Table 2 on p. 31 (`paper/05-table.tex:95, 104`). "The similarities S(d) Loewner
cell is a 19-line wall": the build sets it in **18** lines (p. 31; `paper/05-table.tex:84-92`). The
quoted "for a profile bounded at the origin, shape-blind at the origin (Proposition H.8) and not
beyond it" is there.

**4.1. Symbols undefined before Appendix F.**
- $D_s$: used in Table 2 (`05-table.tex:95, 98`), defined first in Proposition F.2
  (`appendix-smaller-groups.tex:55`, p. 87) and again in F.4 (`:187`, p. 89). **Confirmed.**
- $\Delta(\Sigma)$: used in Table 2 (`05-table.tex:104`), defined in Proposition F.4
  (`appendix-smaller-groups.tex:186-187`, p. 89). **Confirmed.**
- $\mathrm{Corr}(d)$: **not used in Table 2** nor anywhere in § 4; the table says "orbits in PD(d)
  indexed by the correlation matrices" in words (`05-table.tex:96`). **Refuted.**
- $\nu_1 \otimes \dots \otimes \nu_d$: defined in the same cell, "the products
  $(s_1)_*\nu_1 \otimes \dots \otimes (s_d)_*\nu_d$ of self-decomposable laws on the line"
  (`05-table.tex:102-103`), before the off-frame extension uses it. **Refuted.**
- Missed by the review: $\mathrm{sym}\,B$ in the one-parameter row (`05-table.tex:110`), defined in
  Proposition 4.10 (`05-orbits.tex:349`, after the table); and "operator-self-decomposable for every
  diagonal exponent in $K_\alpha$" (`05-table.tex:98`), whose term "$B$-self-decomposable" is also
  defined in Proposition 4.10 (`05-orbits.tex:350`). The legend's $K_\alpha$ bullet describes that
  property without naming it (`05-table.tex:40-42`).

The fix's definitions are right: $D_s = \mathrm{diag}(s_1,\dots,s_d)$, $\Delta(\Sigma) =
\mathrm{diag}(\Sigma_{11},\dots,\Sigma_{dd})$ and $\mathrm{Corr}(d) = \{\Theta \in \mathrm{PD}(d) :
\Theta_{ii} = 1\}$ are F.2's and F.4's (`appendix-smaller-groups.tex:55, 186-188`). Defining
$\mathrm{Corr}(d)$ in the legend defines a symbol the table does not print.

**4.2. The gloss of $R(\lambda) \ge \lambda^\alpha$.** The equivalence with $\beta_-(k) \ge \alpha$ is
right (Lemma 4.14(3), `05-orbits.tex:578-579`). The rest is loose. $k$ is the profile, not a "radial
jump rate": the Lévy density is $k(|x|)\,|x|^{-d}$ (`05-table.tex:50-51`). "Grows at least as fast as
$r^{-\alpha}$ under any contraction of scale" is vague. The exact reading is that
$k(r/\lambda) \ge \lambda^\alpha k(r)$ for all $r$ and $\lambda \ge 1$ (with $s = r/\lambda$), which is
that $r^\alpha k(r)$ is nonincreasing. The legend already has the formulas for $R$ and $\beta_-$
(`05-table.tex:51-54`, round 1 B3); the gloss is optional.

**4.3. The condensed cell.** Checked against Propositions 4.20, H.1 and H.5–H.9
(`05-orbits.tex:770-873`, `appendix-similarity-loewner.tex:31-62, 263-312, 347-385, 440-470,
524-545, 580-606`) and `cell_length-output.txt`:
- It is not shorter: 388 characters against the current 391, about 18 lines in the same column.
- It prints seven symbols the current cell avoids and § 4.3 does not define: $N(0,\cdot)$,
  $S_\alpha(\cdot)$ with a matrix argument, $\kappa$, $b$, $L_\Sigma$, $L_I$, $k_d(0{+})$. That works
  against the item's own aim.
- It drops a hypothesis. H.1(3) needs $\alpha\kappa^2 - (d+1)\kappa - 1 \ge 0$
  (`appendix-similarity-loewner.tex:47-48`); "e.g., $\mu_\Sigma = N(0,2b\Sigma) * S_\alpha(\Sigma +
  \kappa\,\mathrm{tr}(\Sigma)I)$" states the family for every $\kappa$.
- It replaces H.1(3)'s content with a weaker one. The current cell says "not every family is a
  Gaussian convolved with a shape-blind part". "Non-Gaussian families survive" is already true of
  shape-blind parts, such as $((\det\Sigma)^{1/(2d)})_*\nu_I$ (the remark after H.5,
  `appendix-similarity-loewner.tex:320-321`). The point of H.1(3) is that the non-Gaussian part
  can carry the shape.
- It drops H.9, the statement that makes H.5–H.8's standing hypothesis (infinitely divisible Loewner
  increments) a theorem for every family of the cell (`appendix-similarity-loewner.tex:580-606`).
- "Asymptotically isotropic at the origin" says more than H.8(1) proves. H.8(1) proves equal
  logarithmic rates in every direction, which is the legend's "shape-blind at the origin"
  (`05-table.tex:47-49`). H.8's hypothesis is on $k_I(0{+})$ of the isotropic member's origin datum.

The current cell has one defect of its own that the review did not name. "Shape-blind at the origin
(Proposition H.8) and **not beyond it** (Proposition H.7(3))" reads as a universal. It is backed by
one example family (H.7), and it is false as a universal: the shape-blind family
$((\det\Sigma)^{1/(2d)})_*\nu_I$ is in the cell for every rotation-invariant self-decomposable $\nu_I$,
including those with a profile bounded at the origin, and it is rotation invariant at every $\Sigma$.
§ 4.9 already says "need not" (`05-smaller-groups.tex:69-70`).

**Verdict: PARTLY.** $D_s$, $\Delta(\Sigma)$ (and $\mathrm{sym}\,B$, unnamed) are undefined at the
table; $\mathrm{Corr}(d)$ and the $\nu_i$ are not defects; the gloss is loose; the condensed cell is
no shorter, adds undefined symbols, drops a hypothesis and a citation, and weakens H.1(3).

**Response.**
- **safe** (4.1). In the frame bullet (`05-table.tex:36-39`), after "under $\mathrm D_+(d)$": "For
  $s \in (0,\infty)^d$ write $D_s := \mathrm{diag}(s_1,\dots,s_d)$, so that the frame's shapes are the
  $D_s^2$, and write $\Delta(\Sigma) := \mathrm{diag}(\Sigma_{11},\dots,\Sigma_{dd})$ for the diagonal
  of $\Sigma$." In the $K_\alpha$ bullet (`:40-42`): "… for every $t$, that is, $S_\alpha(I)$ is
  *$B$-self-decomposable* (Proposition 4.10); $\mathrm{sym}\,B := \tfrac12(B + B^{\tp})$." Leave out
  $\mathrm{Corr}(d)$.
- **safe, optional** (4.2). Append to the profile bullet (`:54`): "$R(\lambda) \ge \lambda^\alpha$
  for every $\lambda \ge 1$ says that $r^\alpha k(r)$ is nonincreasing: towards the origin the
  profile grows at least like $r^{-\alpha}$." Do not use the review's sentence ("radial jump rate").
- **decline** (4.3), for the reasons above. **safe** instead: narrow the current cell,
  `05-table.tex:90`, "and not beyond it" → "and need not be beyond it" (`adr/0003`: a universal
  backed by one example becomes "need not").

---

## 7. The name "wedge datum" (report p. 15)

**Quote.** It is in the build, p. 15 (`paper/04-classical.tex:100-104`), outside the shared
definition, which follows at `:106`.

**Claims.**
- "$W$ is a partial order, not a wedge." True, and the paper does not call $W$ a wedge: it names the
  pair "after its order", whose steps "for the orders of this paper" are generated by a cone
  (`04-classical.tex:102-104`). That sentence is true of every order the paper studies: the rays
  ($C_0$), the stable orders ($C_\alpha$), the Loewner order ($\mathrm{PSD}(d)$) and every
  $\preceq^+_C$ (Theorem 4.3(4), Proposition 4.12).
- "Theorem 4.3(3) explicitly exhibits a closed $\mathrm{GL}(d)$-invariant partial order $W$ that is
  generated by no wedge." **Refuted as stated.** 4.3(3) (`05-wedges.tex:174-177`, p. 34) gives
  $\mathcal K = \{I\} \cup \{M : \lambda_{\min}(M) \ge 2\}$. Its relation is on $\mathrm{PD}(d)$ and
  does not contain the rays: $\Sigma \le_{\mathcal K} c\Sigma$ only for $c = 1$ or $c \ge 2$. It is the
  order of no wedge datum. The underlying point stands by a variant (checked here, not in the paper):
  $\mathcal K' := \{cI : c \ge 1\} \cup \{M : \lambda_{\min}(M) \ge 2\}$ is a closed step set and
  $\le_{\mathcal K'}$ is a partial order. Transitivity holds since $M^{1/2}NM^{1/2} \ge 2M$ when
  $\lambda_{\min}(N) \ge 2$ (Proposition 4.2(3)). The relation contains the rays and lies inside the
  Loewner order, and $C(\mathcal K') = \{cI : c \ge 0\}$. So its extension to $\mathrm{PSD}(d)$ as in
  4.3(4) gives a wedge datum $(G, W)$ whose order is generated by no cone (Theorem 4.3(2), (b)
  fails). Definition 3.1 does not require a cone, and the paper's sentence does not say it does.
- "Eighteen pages before tangent cones appear in § 4.4." § 4.4 starts on p. 30 (15 pages after p. 15);
  the cone fields of Theorem 4.3 are on p. 33 (18 pages). Roughly right.
- "§ 4.4 itself calls the tangent object an 'invariant cone C'." Its statements say "closed convex
  cone" (`05-wedges.tex:150`), and Table 1 says "invariant cone" (p. 14). But the subsection is
  titled "Invariant wedges" (`05-wedges.tex:15`). The source the gloss cites uses "cone" and "wedge"
  as synonyms (`records/affine/READING-hilgert1989lie.md` § 7, p. 3). **Partly.**

**The proposed sentence is wrong.** "The smooth $G$-invariant partial orders $W$ between the ray
order and the Loewner order will be generated by closed convex cones": the paper defines no
smoothness, and $\le_{\mathcal K'}$ above lies between the rays and the Loewner order and is
generated by no cone. Theorem 4.3(2)(c) is the condition, roots of the steps, under which an order
is cone-generated. The proposed definition of a "cascade datum", "a $G$-invariant partial order
$W$ on $\mathrm{PSD}(d)$", drops "contains the rays" (Definition 3.1, p. 15), and the scheme needs
that condition (`04-classical.tex:85-87`).

**The cost of a rename.** "wedge datum" is on 34 lines of `paper/`, 65 of the blueprint (in
shared statements: Definition 3.1, Lemma 3.3, Proposition 3.4, Theorem 3.5, Theorem 4.3(4),
Propositions 4.20(1) and 4.22(3), and statements of Appendices A, D and F; and in proofs of record
in Appendices A, C, D, F and H; so a blueprint change re-transcribed under `adr/0004`), in Table 1, and in 30 Lean files (structure
`WedgeDatum`, 131 identifiers; renaming them is optional, since no Lean name is printed). It is tied
to "wedge axis" (Theorem 4.21's title and `thm:wedge-axis`), to § 4.4's title, and to Figure 2(b)'s
"the orders as wedges". GATE-affine rows 17 and 132 decided to keep the name. "Cascade datum" would
sit beside "cascade family" and "the $(G, W)$ cascade scheme" (Definition 3.1's own title).

**Verdict: PARTLY.** The name is a label, introduced with a gloss that is correct and restricted to
"the orders of this paper". The review's evidence, Theorem 4.3(3), does not show what it claims,
though the conclusion that Definition 3.1 admits orders with no cone is true. The replacement
sentence is false.

**Response: author** (a name used across the paper, blueprint and Lean, kept by an earlier
decision). Options: (a) keep the name (cost 0); (b) rename to "cascade datum" (99 lines of text,
statements re-transcribed, titles of § 4.4 and Theorem 4.21 reconsidered); (c) keep the name and
add, **safe**, one clause at `04-classical.tex:103`: "… generated by such a cone of symmetric
matrices (§ 4.4), although Definition 3.1 does not require one". *Recommended: (a), or (c) if the
reviewer's reading should be forestalled.* **Decline** the review's replacement sentences in any
case.

---

## 8. Rebalance §§ 4.8–4.9: Proposition 4.22's proof to Appendix B; Propositions F.2 and H.1 into § 4.9 (report pp. 49–52)

**Quotes.** Both are in the build: the proof on pp. 49–50 (`paper/05-shape-adapted.tex:65-107`,
`% proof of prop:shape-adapted-apertures`, the blueprint's proof of record), and "The statements
behind the rows of the two smaller groups are in Appendices F–H" (p. 51,
`05-smaller-groups.tex:30-31`).

**Claims.**
- "The 45-line proof." **About 31 typeset lines** (0.6 page), from the middle of p. 49 to the third line
  of p. 50 (`typeset_lines-prop-4.22-output.txt`: vertical extent 30.9 body lines).
- "Whose first sentence is tautological." **Confirmed**: "The least eigenvalue
  $\lambda_{\min}(M) = \min_{|x|=1}\langle x, Mx\rangle$ is the least eigenvalue of $M$ and is attained
  at a unit eigenvector $v$" (p. 49; `05-shape-adapted.tex:67-68`, blueprint
  `05-shape-adapted.tex:75`).
- "Whose first 18 lines prove the elementary fact …" Clause (1)'s proof is **12** lines, and it
  identifies the kernel and the range of $P$, not only the rank. It was written to the Lean route
  on purpose (Q-0281, blueprint `05-shape-adapted.tex:68-70`).
- "Interrupts the climax … separating Proposition 4.22 from the worked numerical example of a slanted
  planar surface on p. 50." The proof does sit between the statement with its commentary (p. 49) and
  the slant example (p. 50). The example is not an instance of 4.22, though: it computes how far a
  *stable* orbit must move up the scale axis, from Proposition 4.7(1) (`05-shape-adapted.tex:113-128`).
  The order is the one the writing standard prescribes: statement, comments, proof. **Partly.**
- "§ 4.9 contains no formal statements at all." **Confirmed**: `05-smaller-groups.tex` has no
  theorem environment (Q-0312 made it a one-page summary, 1.20 pages).
- "Forcing the reader to turn to Appendices F and H for the two flagship results." **Partly.**
  § 4.9 states both in prose. It gives H.1(3)'s family displayed, with its hypothesis on $\kappa$
  and its conclusion (p. 51, `05-smaller-groups.tex:20-30`), and F.2's conclusion in a sentence
  (p. 51, `:35-37`). H.1(3) is in the abstract ("With the similarities, non-Gaussian families
  cascade along the Loewner order") and § 1 (`01-introduction.tex:279`). F.2 is in § 1 only
  (`:285`).

**The proposed sketch** is correct as far as it goes. $\lambda_{\min}(M) = 1$ makes $P$ positive
semidefinite with kernel the 1-eigenspace, so $0 < \mathrm{rank}\,P < d$ for $M \ne I$; and (2)
follows from Theorem 3.7 at $\Sigma = wI$, with Proposition 4.4(1) for the orbit's transform. For
(3) it omits Lemma 3.3(1) (restriction to the rays), Proposition 3.4(1) (no zero, so
$g = -\log F$ exists), and (K1)/(K4) for $b > 0$ and the Gaussian increments on every pair.
"Appendix B.2" is the wrong place: B.2 is "The base, and the step set of an orbit"
(`appendix-proofs.tex:75`), so the proof would need a new B.3.

**What the moves would undo.**
- Moving the proof reverses Q-0290, which names `shape-adapted-apertures` among the proofs the main
  text keeps (`appendix-proofs.tex:3-5`).
- A body sketch with the full proof in an appendix is the double printing that D3 removed for
  Theorem 4.21, Lemma 4.8 and Proposition 4.13. D3 left pointers, not sketches.
- Moving F.2 and H.1 into § 4.9 reverses Q-0312 (`05-smaller-groups.tex:1-10`) and Q-0290's move of
  Appendix H (`appendix-similarity-loewner.tex:1-12`). Both were decisions on this exact
  arrangement.

**Renumbering** if the statements moved, with § 4.9 after Remark 4.23:
- F.2 and H.1 become Propositions 4.24 and 4.25, in § 4.9's order: H.1 first, then F.2.
- F.3–F.5 become F.2–F.4.
- H.2, Remark H.3 and H.4–H.9 become H.1, Remark H.2 and H.3–H.8. Table 2 alone cites eight of these.
- Every printed number and every record's number of those statements changes.

The body grows by about 0.8 page (the two statements, 21 and about 18 typeset lines,
`typeset_lines-F2-H1-output.txt`), and the total length is unchanged.

**Verdict: PARTLY.**
- Confirmed: the tautology, and that § 4.9 holds no statement.
- Wrong: the lengths (31 and 12 lines, not 45 and 18) and the target appendix.
- Partly right: the "interruption", and that the reader is "forced" to the appendices, since the
  statements are given in prose.

**Response.**
- **decline** (8.1, the move of the proof): it reverses Q-0290, and the sketch recreates the
  duplication D3 removed. **safe** instead: fix the tautology at the blueprint
  (`blueprint/src/parts/05-shape-adapted.tex:75`) and re-transcribe it
  (`paper/05-shape-adapted.tex:67-68`; `adr/0004`; `linkage check` verbatim): "The least eigenvalue
  of $M$ is $1 = \min_{|x|=1}\langle x, Mx\rangle$, and it is attained at a unit eigenvector $v$."
  Shortening clause (1) further would take it off the Lean route (Q-0281). That choice is the
  author's, and it is not recommended.
- **author** (8.2, the statements into § 4.9). Options: (a) keep § 4.9 as it is; (b) move F.2 and
  H.1, with the renumbering above, reversing Q-0312 and Q-0290; (c) give § 4.9 one formal
  statement without moving any appendix statement, by item 9 (b) below.
  *Recommended: (c), else (a).* The flagship results are already stated in § 4.9 in prose.

---

## 9. Proposition 4.20 mixes two subjects (report pp. 45–46)

**Quotes.** All three are in the build: the title (p. 45), "(so it satisfies the hypotheses of
Proposition H.4)" and "These are the functionals of Proposition H.5." (pp. 45–46;
`paper/05-orbits.tex:770, 817, 784-785`).

**Claims.** Clauses (1)–(2) give $\le_\alpha$ on $\mathrm{PSD}(d)$ and the $\mathrm{GL}(d)$ cell
along it. Theorem 4.21 spends them (`appendix-wedge-axis.tex:889, 925`). Clauses (3)–(5) are about
groups containing $\mathrm S(d)$. The preamble's $\psi_L$, $\mathcal M_s$, es and cond serve only (4).
The paper's lead paragraph says the same: "Its clauses (3)–(5) treat the same order for the
similarities" (p. 45, `05-orbits.tex:755-760`). The references to H.4 and H.5 are parenthetic since
round 1 (B2), not load-bearing. § 4.9's paragraph "The stable order" points back to it: "(Proposition
4.20(3)–(5), § 4.6)" (p. 52, `05-smaller-groups.tex:73-76`). **Confirmed.**

**The fix.** It is one blueprint node, `prop:similarity-stable-order-families`
(`blueprint/src/parts/05-smaller-groups.tex:2296`). Its `\lean` tags are already per clause:
`stablePlusLE_order` for (1); `stable_order_gl_row`, `…_examples` for (2); `…_sim_kernels`,
`…_sim_isotropic` for (3); `stable_order_sandwich`, `loewner_order_sandwich` for (4); and
`…_cell_strict` for (5). A split therefore keeps ADR-0025 with no Lean work, and splitting a clause
into its own node is within `adr/0003`. What is the author's is where the new statement is printed:

- (a) Keep the node. Cost 0, and the lead paragraph already says the node has two subjects.
- (b) Split. Clauses (1)–(2) stay Proposition 4.20 at the end of § 4.6. Clauses (3)–(5) become a
  new proposition printed in § 4.9 under "The stable order", as Proposition **4.24**; nothing else
  renumbers. The cost:
  - The hand-typed clause numbers change, (3)→(1), (4)→(2), (5)→(3), at ten sites:
    `01-introduction.tex:281`, `05-orbits.tex:281`, `05-smaller-groups.tex:63, 76`,
    `05-table.tex:83, 86, 128`, `06-open-problems.tex:48, 140`, `appendix-verification.tex:50`.
  - The preamble's $\mathrm S(d)$, $\psi_L$, $\mathcal M_s$, es and cond go to the new statement;
    ecc stays with (1).
  - Appendix B's proof of (3)–(5) (`appendix-proofs.tex:318`) gets the new heading.
  - The split is refereed blind and mirrored (`adr/0004`).
- (c) Split and keep both parts in § 4.6. This renumbers Theorem 4.21, Proposition 4.22 and Remark
  4.23, the paper's headline numbers.

*Recommended: (b).* It is the only similarity statement printed in the body, and both of § 4.9's
similarity paragraphs cite it. It gives § 4.9 a formal statement (item 8) without moving any
appendix statement, so `adr/0006` item 5 and Q-0312 stand. Q-0312's reason for the position, that
Theorem 4.21 spends (1)–(2), stays met.

**Verdict: CONFIRMED.** **Response: author** (placement and numbering), options above.

---

## 10. Figures: an arrow collision in Figure 3(a), small labels, Figure 1's unit vector, Figure 2 (report pp. 21, 29, 33)

**Quotes.** Both captions are in the build: Figure 1, p. 21 (`paper/04-classical.tex:462-469`), and
Figure 2, p. 29 (`paper/05-landscape.tex:231-241`). The captions are paper-only; the blueprint has
no figures.

**10.1. "The bottom arrowhead of the vertical axis collides with 'u, change of shape'" (Figure 3(a),
p. 33).** **Refuted.** Panel (a) has no axis line and no arrow. It is a framed box without ticks,
whose y-range starts at $-0.05$ (`records/affine/fig-cones-plane.py:105-110, 134-136`), and the
label sits clear below the frame (rendered p. 33 at 300 dpi). The review's fix ("truncate the
negative vertical axis at $a = -0.1$") has nothing to act on. Defects seen in the renders that the
review did not name:
- Figure 2(a), p. 29: the label "rays" is printed across the $\alpha = 1$ and $\alpha = 0.5$
  circles. It is placed inside the discs, at `xytext=(-0.55, 0.35)` (`fig-shape-plane.py:149`).
  This is the actual label collision.
- Figure 3(b), p. 33: the y-label "$v$", rotated 90°, reads as "$>$".
- Figure 3(a): a white band under the grey fill, from `ylim(-0.05, …)` (cosmetic).

**10.2. Label sizes** (`figure_fonts-output.txt`; body 11 pt, `\scriptsize` 8 pt, `\footnotesize`
9 pt). Figure 1 is printed at scale 0.680 (4.6 in drawn, 3.13 in printed): legend 5.4 pt, "$w$" 6.8 pt.
Figure 3 at 0.763 (8.2 in, 6.26 in): titles and axis labels 7.6 pt, legend and annotations 6.1 pt,
"rays" 5.7 pt. Figure 2 at 0.995: every label 8.0 pt. **Partly**: 5–6 pt holds for Figure 1's legend
and Figure 3's legend and annotations; Figure 2's labels (the review's "$\alpha = 1.5$" is Figure
2's; Figure 3 has no $\alpha$) are 8 pt.

**10.3. Figure 1's caption without a unit vector.** **Confirmed.** The extent in direction $w$ (the
support function $\langle w, \Sigma w\rangle^{1/2}$) is unchanged for every $w \in \ker P$. But "both
ellipses touch the lines $\langle x, w\rangle = \pm 1$" needs $\langle w, \Sigma w\rangle = 1$, that is
$|w| = 1$ at $\Sigma = I$. The script uses a unit $w$ (`fig-rank-deficient-step.py:30-32`).

**10.4. Figure 2.**
- (a) The doubled angle: the review's reason is right. In the plane, conjugation by a rotation
  through $\theta$ turns the trace-free part of $\log S$ through $2\theta$. Orientations $\theta$ and
  $\theta + \pi$ are the same ellipse, and $\theta + \pi/2$ gives $S^{-1}$, the antipodal point.
- (b) The proposed arrow: the coordinates are right. For the 60° slant (§ 4.8, p. 50,
  `05-shape-adapted.tex:121-126`) $n_2/n_1 = 4$, so the anisotropy coordinate is
  $\log\sqrt{4} = \log 2 = 0.693$. The practice's aperture $2w\,S$ (here $M = \mathrm{diag}(1, 4)$)
  has $\log(t_2/t_1) = \tfrac12\log 2 = 0.347$. It is the plotted cross $m = 4$
  (`fig-shape-plane.py:99-109, 125`). The stable orbit of index 1 needs $s = w\,n_1^{-(d+\alpha)/\alpha}
  = 8w$, so $\log(t_2/t_1) = \tfrac12\log 8 = 1.040$, on the line of slope $2/3$. The arrow's length
  is $\log 2$: a volume scale twice the practice's. But panel (b) is drawn for
  $\log(t_2/t_1) \in [0, 1]$ (`fig-shape-plane.py:185`), so the arrow's end is off the plot.

**Verdict: PARTLY.** The collision claimed is refuted, though one exists elsewhere (Figure 2(a)).
The sizes hold for Figures 1 and 3, not for Figure 2. The unit vector is confirmed. The Figure 2
suggestions are mathematically right.

**Response: safe** (figure presentation; no statement changes; each script re-run with its output
saved, `adr/0003`):
- Figures 1 and 3: draw at the printed size, so that script points are printed points.
  `figsize=(3.13, 2.86)` for Figure 1 (`fig-rank-deficient-step.py:59`) and `(6.27, 3.06)` for
  Figure 3 (`fig-cones-plane.py:95`). Then set every label to 8–9 pt, with layout adjusted. The
  alternative is to keep the figsize and scale the fonts by 1/0.680 and 1/0.763; 9 pt printed needs
  13.2 pt and 11.8 pt in the scripts.
- Figure 2 (optional): raise `font.size` 8 → 9 (`fig-shape-plane.py:131`), for uniformity.
- Figure 2(a): move "rays" outside the Loewner disc, with its leader line to the centre
  (`fig-shape-plane.py:149`).
- Figure 3(b): `ax2.set_ylabel(r"$v$", rotation=0)` (`fig-cones-plane.py:132`).
- Decline the "truncate the vertical axis" fix: there is no such axis.
- Figure 1's caption (`04-classical.tex:464`): "Its extent in a direction $w$ of the null space
  $\ker P$" → "Its extent in a unit direction $w$ of the null space $\ker P$".
- Figure 2's caption, optional (`05-landscape.tex:233`): after "twice the orientation of the major
  axis" insert ", so that orthogonal orientations lie at opposite points".
- Figure 2(b), optional: the horizontal arrow at height $\log 2$ from $x = 0.347$ to $x = 1.040$,
  with `set_xlim(0, 1.1)` and the $\alpha$ labels moved to match. Label it "60° slant, $\alpha = 1$:
  volume scale $\times 2$" and add one caption sentence citing § 4.8.

---

## 20. Table 1 omits symbols (report p. 14)

**Quote.** "Table 1: Notation of §§3–4." is in the build, p. 14. Its scope, as § 2.1 states it, is
"the symbols of §§ 3–4, each with the statement that defines it" (`02-line-papers.tex:73-75`).
Table 2 is in § 4.

**Claims, symbol by symbol** (grep of `paper/*.tex`, comments excluded):

| symbol | used in §§ 3–4 or Table 2 | defined | in scope, missing? |
|---|---|---|---|
| $\mathcal A_d$ | no; § 2 only, twice (`02-line-papers.tex:208, 273`) | before Thm 2.5 (`:204-208`) | no |
| $\chi$ | § 3 prose twice, each naming it (`04-classical.tex:318-319, 817`) | § 2.2 (`02-line-papers.tex:124-127`) | marginal |
| $\varphi = \chi^2$ | § 3 once, defined there (`04-classical.tex:317-318`) | there; Prop. A.3 | no; $\varphi$ also names a Gaussian density and a transform in appendix proofs |
| $N(0, C)$ | Prop. 4.20(5), p. 45 (`05-orbits.tex:838`); § 4.9 | § 4.9, p. 51 (`05-smaller-groups.tex:28`), after its first use | **yes** |
| $\mathrm{sym}\,B$ | Table 2 (`05-table.tex:110`), Prop. 4.10, 4.11, Table 3, § 4.9 | Prop. 4.10 (`05-orbits.tex:349`) | **yes** (the table precedes 4.10) |
| $\sigma(\Sigma)$, $\Delta_d$ | no (Table 2 and § 4.9 say "normalized spectrum", "simplex" in words) | Prop. F.3 (`appendix-smaller-groups.tex:139-141`) | no; $\sigma(\Sigma)$ is already in § 2.1's list of second meanings (p. 13) |
| $D_s$ | Table 2 | Props. F.2, F.4 | **yes** |
| $\Delta(\Sigma)$ | Table 2 | Prop. F.4 | **yes** |
| $\mathrm{Corr}(d)$ | no | Prop. F.4 | no |

"Appear repeatedly in … § 4.9": of these, § 4.9 prints only $N(0, C)$, where it defines it, and
$\mathrm{sym}\,B$. The proposed rows' pointers are right except "$N(0,C)$ … Prop. 4.20", which
uses the symbol but does not define it. Putting $\Delta_d$ beside $\Delta(\Sigma)$ would print two
$\Delta$s that are both local to Appendix F; Proposition H.8(3) has a third, $\Delta_\Sigma(u)$.

**Verdict: PARTLY.** Four of the ten are in Table 1's scope and missing ($N(0,C)$,
$\mathrm{sym}\,B$, $D_s$, $\Delta(\Sigma)$). Six are § 2 or appendix symbols, outside the table's
stated scope.

**Response: safe.** Add three rows to `02-line-papers.tex:494-534`, in the table's order:
- "$\mathrm{sym}\,B$ & $\tfrac12(B + B^{\tp})$ & Prop. 4.10";
- "$N(0, C)$ & centred Gaussian law of covariance $C$ & § 4.9";
- "$D_s$; $\Delta(\Sigma)$ & $\mathrm{diag}(s_1,\dots,s_d)$; the diagonal of $\Sigma$ & Props. F.2,
  F.4". If item 4.1's legend lands, the last row reads "§ 4.3".

Do not add $\mathcal A_d$, $\chi$, $\varphi$, $\sigma(\Sigma)$, $\Delta_d$ or $\mathrm{Corr}(d)$.
Optionally, also define $N(0, C)$ at its first use, Proposition 4.20(5). That is a shared
statement: a blueprint wording change, mirrored under `adr/0004`, or under item 9 (b) in the new
node.

---

## Summary

| # | Item (report) | Verdict | Class | Response |
|---|---|---|---|---|
| 4.1 | Table 2 symbols undefined before App. F | PARTLY: $D_s$, $\Delta(\Sigma)$ yes (and $\mathrm{sym}\,B$, "$B$-self-decomposable", unnamed); $\mathrm{Corr}(d)$ not in the table; $\nu_i$ defined in the cell | safe | define $D_s$ (frame's shapes $D_s^2$), $\Delta(\Sigma)$ in the frame bullet; name $B$-self-decomposable and $\mathrm{sym}\,B$ in the $K_\alpha$ bullet; omit $\mathrm{Corr}(d)$ |
| 4.2 | gloss of $R(\lambda) \ge \lambda^\alpha$ | PARTLY: equivalence right; "radial jump rate" misnames $k$ | safe, optional | "$r^\alpha k(r)$ is nonincreasing" |
| 4.3 | condense the (S(d), Loewner) cell | REFUTED as a fix: same length, 7 new undefined symbols, drops H.1(3)'s $\kappa$ condition and H.9, weakens H.1(3) | decline; safe instead | "and not beyond it" → "and need not be beyond it" (false as a universal) |
| 7 | rename "wedge datum" | PARTLY: Thm 4.3(3)'s order contains no rays, so is no $W$; the point holds by a variant; replacement sentence false and drops "contains the rays" | author | keep (recommended), rename (99 lines + Lean names, titles), or keep + one clause; decline the review's text |
| 8.1 | 4.22's proof to App. B, sketch in body | PARTLY: ~31 lines, not 45; clause (1) 12, not 18; tautology confirmed; target B.2 wrong | decline; safe instead | fix the tautological first sentence at the blueprint, mirrored; keep the proof (Q-0290, D3) |
| 8.2 | F.2 and H.1 statements into § 4.9 | PARTLY: no statements in § 4.9, but both results are stated there in prose | author | recommend item 9 (b) instead; moving renumbers F.3–F.5, H.2–H.9 and reverses Q-0312/Q-0290 |
| 9 | split Prop. 4.20, (3)–(5) to § 4.9 | CONFIRMED | author | split the node (per-clause `\lean` tags; `adr/0003`); print (3)–(5) in § 4.9 as Prop. 4.24; ten clause citations re-typed |
| 10 | figures | PARTLY: Fig. 3(a) collision refuted (no axis arrow; the real collision is "rays" in Fig. 2(a)); 5.4–7.6 pt in Figs 1, 3, 8 pt in Fig. 2; unit vector confirmed | safe | figsize = printed size, labels 8–9 pt; move "rays" in Fig. 2(a); unrotate "$v$" in Fig. 3(b); "unit direction $w$"; optional Fig. 2 caption clause and arrow (with xlim 1.1) |
| 20 | Table 1 incomplete | PARTLY: 4 of 10 in scope and missing | safe | rows for $\mathrm{sym}\,B$, $N(0,C)$, $D_s$/$\Delta(\Sigma)$; not the § 2 or appendix symbols |
