# Verification of the presentation review, round 2 (the affine paper, `review-2`): the abstract, § 1, § 1.1 and Appendix I, the back matter, the announcements

*2026-11-03. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is checked
against the text, the blueprint and the sources before anything changes. This record verifies items
1, 2, 3, 16, 17 and 18 of `review-presentation-review-2-Gemini-4.0-Argon-High.md` (twenty ranked
changes): the abstract and § 1, § 1.1 and Appendix I, the declarations and the AI statement, and the
metatextual announcements. The other fourteen items are verified elsewhere. This record changes no
`.tex`, `.lean` or blueprint file.*

## Inputs and conventions

- **The build.** `review-build-review-2.pdf`, 108 pages, byte-identical to `paper/main.pdf` (`cmp`),
  and `git diff 5f6f72c HEAD -- paper blueprint` is empty (the tag `review-2` is not in this clone;
  the frozen commit is `5f6f72c`, `notes/HANDOFF.md`). Page numbers are the PDF's, which are the
  printed ones (p. 1 prints 1) and the report's. Text was read with `pdftotext -layout`; sources are
  cited as file:line.
- **Scripts**, in `verify-round2-paper-scripts/`, each with its `-output.txt`:
  `front_phrases.py` (where each quoted phrase is in the build, whitespace and hyphenation
  normalized), `sketch_headings.py` (for the twenty statements Appendix I lists as sketched: the
  heading of the printed proof, its length, and the length of the blueprint's proof of the node),
  `abstract_words.py` (the abstract's word count, by the convention of the comment in
  `paper/main.tex`: a math span is one word, and the cost of each candidate rewording).
- **Sources.** `library resolve lindeberg1994shape --json`, `library search lindeberg1994shape
  "eigenvalue"`, `library get lindeberg1994shape --pages 8-8` (the held copy is paginated 1–12,
  so `--printed 396` fails; pdf p. 8 is the paper's p. 396).
- **Rules read.** `CLAUDE.md`; `.claude/rules/article-kit/core.md` and `writing.md`; `adr/0003`
  (safe direction), `0004` (proofs of record mirrored), `0005` (no internal label; prose names the
  papers), `0006` (positioning; § 1 and the abstract rewritten by the author in pass 6); article-kit
  `WRITING.md` §§ 0–4 and § 6; hub `RELEASES.md`; `records/affine/PLAN-review-response-paper.md`
  § 0 (the author's round-1 decisions D1–D5, 2026-11-03); `Formalization/lakefile.toml`,
  `lake-manifest.json`, `README.md`; `blueprint/trust-boundary.txt`; `CHANGELOG.md`.
- **Verdicts.** **CONFIRMED**: the finding holds as stated. **PARTLY**: part holds, part not (both
  are said). **REFUTED**: the paper is right, and why.
- **Classes.** **safe**: a wording or presentation change a session may make under `adr/0003`,
  given as the exact change. **author**: changes what the paper claims, its structure, a convention,
  or chooses between routes. **decline**: wrong, or against a rule or a decision.

---

## 1. Reorder § 1 so that $(G, W)$ comes before the earlier papers and the vocabulary (pp. 1–2, p. 7)

**Claim 1a: the quoted passage is at pp. 1–2.** CONFIRMED. `paper/01-introduction.tex:95-121`; the
build prints it as quoted (pp. 1–2), with the "..." eliding "They require positive, mass-preserving
stages … relabel the scales."

**Claim 1b: the reader meets the earlier papers and the vocabulary before the organizing idea.**
PARTLY. The order is: the reader's starting point (¶ 1), the hemigroup axioms and the three earlier
papers (¶ 2), the vocabulary and the line's classification (¶ 3), then "What is an affine scale
space?" and "The two choices" (p. 2, about two thirds down, to p. 3). The $(G, W)$ idea is the
abstract's second and third sentences, so the reader has it before § 1; in § 1 it comes after about
1.2 pages. The order is not an accident: it is the structure of the writing-rules pass, "the reader's
starting point, the axioms, the change to the vocabulary of probability, the (G, W) pair, …"
(`01-introduction.tex:64-71`), and the author's pass-6 rewrite under `adr/0006`
(`01-introduction.tex:123-137`).

**Claim 1c: the vocabulary paragraph of p. 2 is repeated almost word for word on p. 7 (§ 2.1).**
CONFIRMED. Three of its sentences recur in § 2.1 (`02-line-papers.tex:54-60` against
`01-introduction.tex:104-109`): "A kernel is a probability measure … in that theory", "a kernel is a
law, and its Fourier transform, the transfer function of the smoothing, is the characteristic
function", and "Scale, stage and cascade keep their meaning, and “kernel” stays in use for a law in
its role as an aperture" (the last verbatim; `front_phrases-output.txt`: "keep their meaning" on pp. 2
and 7). Not raised by the report, the same holds of the earlier papers: § 2's opening (p. 7,
`02-line-papers.tex:43-46`) repeats ¶ 2's "the cone paper … studies the set of
the line's exponents, and the isotropic paper … carries the theory to $\mathbb R^d$ for apertures that
have a size and no shape" nearly verbatim.

**The proposed fix.**
- *Move "What is an affine scale space?" and "The two choices" after ¶ 2, and delete ¶ 3.* Wrong as
  it stands. "What is an affine scale space?" uses "rotation-invariant self-decomposable law",
  "transforms", the stable and the Matérn laws (`01-introduction.tex:143-149`), all taught in ¶ 3.
  Self-decomposability and the stable and Matérn families are on the default list of `WRITING.md`
  § 0 ("taught when first used"); the reviewer's replacement sentence names self-decomposability but
  drops its definition and its reading in a cascade (`01-introduction.tex:111-115`). And § 1 uses
  "law" and "transform" throughout (p. 4: "rotation-invariant laws with a positive transform"), so
  the convention must be set in § 1, at first use; deleting the § 1 copy and keeping § 2.1's puts
  first use before definition.
- *The replacement sentence.* Three errors. (i) "In one dimension and for isotropic apertures in
  $\mathbb R^d$, the hemigroup axioms admit every symmetric self-decomposable probability measure":
  in $\mathbb R^d$ the class is the rotation-invariant self-decomposable laws (Theorem 2.5, $F \in
  \mathcal A_d$; Proposition 4.5), and "symmetric" is weaker than rotation-invariant for $d \ge 2$;
  the point mass is excluded by (ND), which § 1 says ("Every such law other than the point mass
  occurs", `01-introduction.tex:115`). (ii) It cites [17], the cone paper, for a classification it
  does not state (it studies the set of exponents). (iii) It writes the stable index $\alpha$, the
  letter of the order index throughout the abstract and § 1 (the abstract writes the stable index
  $\gamma$; ¶ 3 writes $p$ on the line), and the Matérn exponent $\gamma$, the abstract's stable index.

**Response: author** (the order of § 1 is the author's structure, pass 6 and `adr/0006`), with a
**safe** part.
- *Safe now:* remove the duplicates on the § 2 side, where the reader has already read them.
  § 2.1 (`02-line-papers.tex:54-60`): replace the three sentences through "role as an aperture." by
  "As in \S\ref{sec:introduction}, a probability measure is a \emph{law}, and its transform is its
  characteristic function, $\widehat\mu(\xi) = \int e^{i\langle\xi,x\rangle}\,\mu(dx)$ for a law $\mu$
  on $\RR^d$." § 2's opening: drop the sentence that re-describes the three papers, keeping the
  sentence on the released version 0.1 (item 17). § 2.1 is paper prose, not under a marker.
- *Author's options for the order:* (a) keep it (the reader has $(G, W)$ from the abstract; § 1 sets
  the vocabulary before using it); (b) the reviewer's move, done correctly: carry ¶ 3's definition of
  self-decomposability, its reading in a cascade and the stable and Matérn transforms into "What is an
  affine scale space?", and move ¶ 3's vocabulary sentence before it; (c) one sentence at the end of
  ¶ 1 announcing the two choices ("Under them an affine scale space is fixed by two choices, a group of
  linear maps and an order on the aperture matrices, made below"). *Recommended: (a) with the safe
  de-duplication.* The gain of (b) is about one page earlier sight of $(G, W)$ for a reader who skipped
  the abstract, at the cost of the author's pass-6 structure and a rewrite of the paragraph that
  teaches self-decomposability.

---

## 2. The abstract: "covariance matrices", the index $\alpha$, the shape-adaptation sentence (p. 1)

**Quotation.** CONFIRMED at p. 1 (`paper/main.tex:133-163`).

**The abstract's budget.** The comment above it says it is held within 250 words
(`main.tex:103`, `:129`, `:158`). By `abstract_words.py` the built abstract has 257 words (the
comment's count, 249–250, differs by the counting of hyphenated words and "Lean~4"); it is at its
budget by either count. The reviewer's replacement of the three passages takes 87 words to 171 (+84):
the abstract would be about 341 words. Every addition below therefore needs a cut elsewhere.

**Claim 2.1: "covariance matrices" is wrong for laws without a covariance.** CONFIRMED. The isotropic
$\gamma$-stable laws, $\gamma < 2$, which the abstract names, have infinite variance; § 1 says the
indexing matrix is "proportional to its covariance in the Gaussian case" (p. 2,
`01-introduction.tex:163-164`). (For an affine orbit of a rotation-invariant law with finite second
moments the covariance is a multiple of $\Sigma$ too, so the Matérn orbits are fine; the stable ones
are not.)
*The fix* ("a partial order $W$ on positive semidefinite scale–shape matrices $\Sigma$ (proportional
to the covariance in the Gaussian case)") is correct but costs about 12 words and coins
"scale–shape matrices", a term the paper does not use. **Response: safe**, at no cost in words:
`main.tex:136`, "an order $W$ on covariance matrices" → "an order $W$ on scale matrices", Lindeberg's
term for the same object, which the paper uses for it (`05-landscape.tex:98`,
`05-shape-adapted.tex:29`, "local scale matrix").

**Claim 2.2: $\alpha$ is introduced without what it controls.** PARTLY. Since round 1 the abstract says
what $\alpha$ indexes, "a chain of orders from the rays ($\alpha = 0$) to the Loewner order
($\alpha = \infty$)", and what it costs, "a non-Gaussian kernel pays in speed of shape change"
(`main.tex:143-144`; the round-1 comment `main.tex:150-153`). What the abstract does not say is the
geometric content of the index. The reviewer's gloss, "$\alpha$ bounds how fast the aperture's
anisotropy may grow relative to its volume scale", is right for $0 < \alpha < 2$: the stages of
$\le_\alpha$ between positive definite matrices are the step set of the $\alpha$-stable orbit
(Proposition 4.7), whose anisotropy per step is at most $(t_2/t_1)^{d\alpha/(d+\alpha)}$ with
$t_1 < t_2$ the volume scales (Table 3, Proposition 4.7(3)), increasing in $\alpha$ to the Gaussian's
$(t_2/t_1)^d$. That bound is stated for the stable orders only, not for the cones $C_\alpha$,
$\alpha \ge 2$, of the chain. "A continuous chain" is not a property the paper states (the chain is
nested, Proposition 4.12, Theorem 4.21); "GL(d)-invariant" is right.
**Response: author** (the budget). Options: (a) keep (the cost is named; Table 3 has the rates);
(b) "… pays in speed of shape change, the anisotropy a step gains for its growth in volume" (+9 words,
needs a cut). *Recommended: (a).*

**Claim 2.3: the shape-adaptation sentence leaves open whether a non-Gaussian kernel fails or
re-measures.** PARTLY. "Only the Gaussian reaches them by further smoothing" says what fails (the
cascade), not what the practice does instead; § 1 (p. 4) and § 4.8 say it: the adapted record is a
re-measurement, which the iteration makes in any case.
*The fix* overclaims. "Every other kernel must either convolve the original image afresh … or
increase its minimum scale" is false for a large part of the class the sentence quantifies over: the
Matérn orbits, every orbit of logarithmic exponent and the rational symbols keep at most the rays
(Propositions 4.15, 4.17, 4.18), so no increase of the minimum scale makes a change of shape a
further smoothing; § 4.8 says so: "An orbit whose transform decays like a power of the frequency,
such as a Matérn orbit, cannot follow them at all" (`05-shape-adapted.tex:112-115`, p. 50). Only the
stable orbits can follow the practice's shapes, by growing the minor axis
(`05-shape-adapted.tex:111-126`). "Preserves the minimum directional scale" is right
(Proposition 4.22(1); Lindeberg and Gårding keep "the smallest eigenvalue … constant during the
iterations", `lindeberg1994shape`, p. 396, held copy pdf p. 8).
**Response: author** (the budget). Options: (a) keep; (b) "…, and for every other kernel the adapted
record is a new measurement of the image" (+15 words, needs a cut; it adds nothing false, since a
record off the cascade is a convolution of the original image). *Recommended: (a)*: the abstract's
sentence is exact, and the next three sentences already say which kernels can change shape at all.

---

## 3. The shape-adaptation paragraph of § 1 (p. 4)

**Quotation.** CONFIRMED (`01-introduction.tex:231-239`, p. 4, the second paragraph under "The
general linear group with the Loewner order").

**Claim: the last two sentences are elliptical, and the iteration and the alternative are not
recalled.** PARTLY. "Which the iteration makes in any case" relies on a fact § 1 has stated only as
"the iteration … fits the shape of the aperture" (p. 1), not that each round convolves the original
image; that is § 4.1, p. 26 ("Each round convolves the original image", `05-landscape.tex:94-96`).
The normalization ($M$ divided by its least eigenvalue, the scale $w$) is named here only in words.

**The proposed fix, checked.**
- "an isotropic first stage at scale matrix $wI$ selects a local shape matrix $M$ with
  $\lambda_{\min}(M) = 1$, and the next stage measures the image at $\Sigma_w = wM$": right; it is the
  setting of Proposition 4.22 (`05-shape-adapted.tex:35-36`) and the source's step 2 (p. 396: the shape
  matrix divided by its least eigenvalue, "keep the smallest eigenvalue of $\Sigma_0$ constant").
  "[36, 37]" without the page anchors is below the paper's citation standard; § 1 cites p. 396, step 2
  and § 6.2 (`05-shape-adapted.tex:56`).
- "the increment $\Sigma_w - wI = w(M - I)$ is singular (Proposition 4.22(1))": right, and it should
  keep "for $M \ne I$" (clause (1): rank 0 exactly when $M = I$; clause (2) assumes $M \ne I$).
- "only the Gaussian can compute the record at $\Sigma_w$ by a further convolution of the first-stage
  record": right for the affine orbits of rotation-invariant laws with a positive transform
  (Proposition 4.22(2), with Proposition 4.4's hypotheses); the fix keeps that hypothesis.
- "For every non-Gaussian kernel, obtaining the record at $\Sigma_w$ requires either convolving the
  original image afresh … or else enlarging the minor-axis scale … so that the step lies inside the
  kernel's cascade cone (§4.8)": wrong twice. Enlarging the minor axis changes the aperture, so it
  does not obtain the record at $\Sigma_w$; and kernels that keep only the rays (Matérn, logarithmic
  exponent, rational symbols) have no cascade cone across shapes (item 2.3).

**Response: safe**, as a § 1 summary compared with Proposition 4.22 and § 4.8. Replace
`01-introduction.tex:231-239` by:

> Shape adaptation takes such a step. In the iteration of Lindeberg and Gårding the first stage is
> isotropic, at $wI$, and the adapted aperture is $\Sigma_w = wM$, with $M$ the shape matrix of the
> round divided by its least eigenvalue (\sscite{lindeberg1994shape}, p.~396, step~2;
> \sscite{lindeberg1997shape}, \S6.2). So $\Sigma_w$ keeps the least eigenvalue $w$, and for $M \ne I$
> the step $\Sigma_w - wI = w(M - I)$ is rank-deficient (Proposition 4.22(1)). Among the affine orbits
> of the rotation-invariant laws with a positive transform only the Gaussian reaches $\Sigma_w$ by a
> further smoothing of the first stage (Proposition 4.22(2)). For every other kernel the record at
> $\Sigma_w$ is a new convolution of the original image, which each round of the iteration computes in
> any case (\S\ref{sec:landscape-uses}). A stable orbit reaches the adapted shape by a further smoothing
> only with a wider minor axis, and a Matérn orbit not at all (\S\ref{sec:shape-adapted}). So for the
> apertures of the practice a non-Gaussian kernel loses only the cascade between the stages of the
> iteration, which the iteration does not use (\S\ref{sec:conclusion}).

(The sentence on the stable and Matérn orbits restates `05-shape-adapted.tex:111-115`; "a Matérn
orbit" may read "an orbit whose transform decays like a power of the frequency, such as a Matérn
orbit" if the author wants the whole class.)

---

## 16. § 1.1 and Appendix I: the sketches, the line paper's formal development, Lean's axioms (pp. 6–7, 102–103)

**Quotations.** CONFIRMED at pp. 6, 7, 102 and 103 (`01-introduction.tex:406-408`, `:439-440`;
`appendix-verification.tex:48-58`, `:156-158`). The p. 102 list names twenty statements
(eighteen propositions, two lemmas), as quoted.

**Claim 16.1a: the twenty proofs are complete, journal-level proofs that omit only line-by-line
algebra.** REFUTED. `sketch_headings-output.txt`: each printed proof is 10–48 % of the length of the
blueprint's proof of the node (Proposition E.4: 119 words against 1,212; Lemma 4.14: 311 against 728;
Proposition 4.20(3)–(5): 343 against 1,528). Read against the blueprint, Proposition E.4's sketch
(`appendix-orbits.tex:246-258`) leaves out the identification of the would-be increment with $q$ off
the origin (the blueprint's clause (1), a distributional argument with a cut-off), the proof that
$\Theta > 0$ exactly off the rays, and the argument that a finite signed measure would have to agree
with $q$, which is what makes "its total variation would be at least $\int_{E_a} q_-$" true
(`blueprint/src/parts/05-orbits.tex`, the proof of `prop:matern-negative-mass`). These are steps of
the proof, not algebra.

**Claim 16.1b: the disclaimer makes the article sound incomplete.** PARTLY: twenty statements are
proved completely only in the deposit, and that is what the paper is; saying so is required
("Where a step is only sketched, say so and point to the formal proof", `WRITING.md` § 3), and the
author decided it on 2026-11-03 (D1–D2: the two main-text sketches printed in full, "the other twenty
sketched statements keep their sketches, and the deposited sources get a citable address",
`PLAN-review-response-paper.md` § 0). Not raised by the report: § 1.1 says "A proof headed
“Sketch”", but ten of the twenty are headed "Proof of … (sketch)" (`appendix-proofs.tex:77, 173, 278,
318`; `appendix-classical.tex:430, 570`; `appendix-smaller-groups.tex:102, 229, 255, 333`), and only
ten "Sketch".

**The fix 16.1** (head them "Proof"; "complete at standard journal level; … routine algebraic
verifications are condensed") **decline**: it states something false (16.1a), contradicts `WRITING.md`
§ 3 and reverses the author's D2. **Safe instead:** `01-introduction.tex:406`, "A proof headed
``Sketch'' shows" → "A proof marked as a sketch shows"; `appendix-verification.tex:47-48`, the same
change. Printing the twenty in full (+about 15 pages, round 1's D2 option (b)) is the author's, and
was declined.

**Claim 16.2: a reader cannot tell whether Lemma 2.2 and Theorem 2.3 are machine-checked.** PARTLY. The
paper says they are proved in the line paper's released version, "which … says what of it is
machine-checked" (p. 7); a reader must go there.
*The fix's statement* ("all one-dimensional results imported from [15] (Lemma 2.2, Theorem 2.3, and
the gauge construction of [15, Prop. 6.6]) are machine-checked from first principles in Lean 4 without
assuming any of C1–C4 or any other external theorem") is **false**: this development formalizes no
§ 2.2 statement (no marker, no `\lean`; `main.tex:20`, "no blueprint nodes for [V]"), and the line
paper's own development rests on cited facts of its own and leaves one step unchecked (the hub's
source page `wiki/sources/@fagerstrom2026spatial.md`, "Machine-checking": Bochner's theorem, the
symmetric Lévy–Khintchine representation and two facts for regularity; "One step in the development is
not machine-checked"). **Decline.**

**Found in checking 16.2: the p. 7 and p. 103 sentences on the line paper's formal development are
false at this build.** § 1.1: "The formal development builds on the line paper's own, at its released
version, and uses only parts of it that rest on no cited fact" (`01-introduction.tex:439-440`).
Appendix I: "The toolchain is pinned in-tree: … the shared library ScaleSpaceCore at its tag v0.5.0,
and the line paper's formal development at its released tag" (`appendix-verification.tex:142-144`,
p. 103). `Formalization/lakefile.toml` requires ScaleSpaceCore `v0.5.0` and Mathlib `v4.31.0` only;
`lake-manifest.json` has no entry for the line paper's package; the `require` was dropped on
2026-10-18 (`CHANGELOG.md`, hub Q-0460, the author's decision of 2026-10-17; `adr/0002`), and since
Q-0365 no guarded declaration prints one of its interfaces (`Formalization/README.md`, "Trust"). The
isotropic paper's identical sentence was corrected on that ground ("'Builds on the line paper's own'
formal development was stale and is replaced by what is true: the shared library, which has no
assumption of its own", `CHANGELOG.md`; `paper-iso/appendix-verification.tex:89-93`, "The build
configuration requires these two packages and no other"). **Response: safe** (a correction that
narrows a stated dependency to the build, on the isotropic paper's precedent; both passages are
inside the `% trust base` regions, which `linkage check` reads):
- `01-introduction.tex:439-440`: "The formal development builds on the line paper's own, at its
  released version, and uses only parts of it that rest on no cited fact." → "The formal development
  requires no formal development of the line paper: it requires Mathlib and the shared library
  ScaleSpaceCore, which makes no assumption of its own, and proves what it uses of the line paper's
  results from the cited facts above."
- `appendix-verification.tex:142-144`: drop ", and the line paper's formal development at its released
  tag" and add "The build configuration requires these two packages and no other."
- In passing (not printed): `Formalization/README.md`'s table gives ScaleSpaceCore `v0.4.0`
  (`f81a3032`); the lakefile and the manifest pin `v0.5.0` (`aabf4f4`). The comment at
  `02-line-papers.tex:212-219` still says the isotropic classification prints Paper V's interface
  through the include line, which Q-0365 removed.

**Claim 16.3: `[propext, Classical.choice, Quot.sound]` is unexplained.** CONFIRMED (p. 103: "Lean's
three logical axioms", unnamed). The gloss is correct: propositional extensionality, the axiom of
choice (Lean's global choice), soundness of quotients. **Response: safe**:
`appendix-verification.tex:157`, after "Lean's three logical axioms" insert "(propositional
extensionality, \texttt{propext}; the axiom of choice, \texttt{Classical.choice}; and the soundness of
quotient types, \texttt{Quot.sound})".

---

## 17. Programme names, "version 0.1", "not yet released", the process note (pp. 1, 5, 7, 53, 104)

**Quotations.** CONFIRMED: "Working draft — not yet released" (p. 1, `main.tex:93`); "left to a
further paper, not yet released" (p. 5, `01-introduction.tex:298`) and "left to a further paper by the
author, on scale-space pyramids, not yet released" (p. 53, `06-open-problems.tex:82`); the version-0.1
sentence (p. 7); the process sentence (p. 104, in "Author contribution and use of AI",
`ai-statement.tex:55-57`, not in "Declarations"). "The line/cone/isotropic paper": 39 printed
occurrences (10, 6, 23; `front_phrases-output.txt`): "over thirty" is right.

**17.1a "Working draft".** CONFIRMED as text, not a defect of the review build: it is the pre-release
date line, replaced at the release by the release date (`notes/HANDOFF.md`; the isotropic paper's
`\date` returned to the working-draft line after its release, Q-0470). **Decline now**; the release
handles it.

**17.1b "a further paper, not yet released" → "future work".** PARTLY. Both are prose, as the rule for
an unreleased module asks (`WRITING.md` § 3, with `% TODO(module VI)` beside each); "not yet released"
is programme vocabulary, while "future work" drops that the paper exists (Paper VI is an active module,
hub `constellation.json`). **Response: safe**: "left to a further paper, not yet released" → "left to a
paper in preparation" (p. 5); "left to a further paper by the author, on scale-space pyramids, not yet
released" → "left to a paper by the author on scale-space pyramids, in preparation" (p. 53). Keep both
`% TODO(module VI)` comments.

**17.2a "the line paper", "the cone paper", "the isotropic paper" → "[15]", "[17]", "[16]".** REFUTED.
They are not internal labels: each is introduced with its citation and a word of what it is (p. 1,
"the author's paper on the line [15], the line paper below"; p. 2), which is how `WRITING.md` § 1 asks a
paper to be named ("the bibliography number with a word of what it is — never the programme's
internal paper letters"), and `adr/0005` decides that the paper's prose names them so (no `[V]`,
`[B]`, `[Iso]`). The internal labels the reviewer would rightly object to do not reach the reader.
**Decline** (against `adr/0005`).

**17.2b Delete "in their released version 0.1, by the statement numbers of that version".** REFUTED.
The sentence is load-bearing: every `\prog` citation is to a statement number of v0.1, and the
isotropic paper's next version renumbers the statements this paper cites (`notes/HANDOFF.md`, "Open"
item 2: Remark 3.26 becomes 3.30). `CLAUDE.md` ("An earlier module is cited as its released version
… statement numbers as of that version") and the hub's rule for citable numbers ("named with its
version") require it. **Decline.**

**17.2c "Future-dated timestamps".** REFUTED. 2026-10-13, September 2026 and October 2026 precede the
build (frozen at `5f6f72c`, 2026-11-03); the reviewer's clock is earlier than the paper's.

**17.3 The process sentence of p. 104.** PARTLY. `notes/PROCESS.md` is a path in a private repository,
which a reader cannot open unless the release deposits it; that is a real defect for the release. The
reviewer's replacement restates the ratio without its date and without "a lower bound", against
`WRITING.md` § 6 rule 2 ("Numbers come from `chronicler`, carrying the date they were computed and
their caveats … Never restate a figure without re-deriving it"). The AI statement is rewritten by the
archivist in pass 5, after the external reviews (`notes/HANDOFF.md` items 1 and 6; the
`% TODO(release)` at `ai-statement.tex:36`). **Decline now**; carry to pass 5 as an input: the
private path must become a deposited file or go.

---

## 18. Metatextual announcements (pp. 1, 5, 21)

**Quotations.** CONFIRMED at pp. 1, 5, 5 and 21 (`01-introduction.tex:85-87`, `:316-317`, `:337-338`;
`04-classical.tex:456-457`).

**18.1 "incomparable with the classical ones (Remark 3.14)" (p. 1).** PARTLY. The pointer is a forward
reference, but § 1 itself explains it at p. 5 ("Neither earlier result implies it, and it implies
neither of them (Remark 3.14)"), and ¶ 2 states the axioms in the next paragraph. The fix's
content is accurate as far as it goes against Remark 3.14 (Lindeberg assumes a semigroup in a scalar
scale and non-enhancement; this paper assumes positivity and a cascade along an order on matrices), but
it lists two of the axioms out of five (covariance, continuity and nondegeneracy are left out), drops
the claim the word carries (neither set implies the other), anticipates ¶ 2, and adds an em-dash pair.
**Decline the fix.** Optional **safe** alternative, in plain words: "under other axioms, which neither
imply the classical ones nor follow from them (Remark~\ref{rem:lindeberg})".

**18.2 "§3.5 sets the axiomatics side by side." (p. 5).** PARTLY. It is a pointer after the paragraph
has stated the comparison; `WRITING.md` § 2 allows light signposting ("Light explicit signposting is
fine"). **Decline**; deleting it is harmless and optional.

**18.3 "Remark 3.13 shows how, and what the single step of Theorem 3.7 adds." (p. 5).** CONFIRMED: it
announces where both answers are. *The fix* drops a hypothesis: "a single rank-deficient step from a
positive definite matrix already forces a quadratic exponent" omits that the step's increment is a
probability measure, the hypothesis that does the work (Theorem 3.7; Remark 3.11: "The classification
theorems of this paper use positivity"). "A rank-one step splits the aperture into independent
orthogonal subspaces" is loose: Remark 3.13 goes through the singular matrix $I - e_1e_1^{\mathsf T}$,
whose factors are carried by $e_1^\perp$ and by the $e_1$-axis, so the first coordinate of $\mu_I$ is
independent of the others. "Without even assuming that $e^{-g(\langle\omega,\Sigma\omega\rangle)}$ is a
characteristic function" is right (`04-classical.tex:502-504`, `:735-736`). **Response: safe**,
compared with Remark 3.13 and Theorem 3.7: `01-introduction.tex:337-338`, replace the sentence by
"Through the singular matrix $I - e_1e_1^{\tp}$ the cascade makes the first coordinate of $\mu_I$
independent of the others, and Kelker's lemma then makes $\mu_I$ normal (Remark~\ref{rem:kelker}).
Theorem~\ref{thm:rank-deficient-step} needs one rank-deficient step from a positive definite matrix,
with a probability measure as its increment, and a function $g$ for which
$e^{-g(\langle\omega,\Sigma\omega\rangle)}$ need not be a characteristic function."

**18.4 "Where positivity enters is Remark 3.11." (p. 21).** CONFIRMED (an announcement in the
roadmap paragraph of § 3.4). *The fix* is right in substance against Remark 3.11
(`04-classical.tex:627-637`: it enters through Lemma 3.8 and through the sign of $g$), but
"confining a measure with a degenerate transform to a subspace" is vague, and $g$ is Lemma 3.9's.
**Response: safe**: `04-classical.tex:456-457`, "Where positivity enters is
Remark~\ref{rem:positivity}." → "Positivity enters twice: a probability measure whose transform is $1$
on a subspace is carried by its orthogonal complement (Lemma~\ref{lem:charfn-one-on-subspace}), and the
function $g$ of Lemma~\ref{lem:affine-reduction} is nonnegative because a transform has modulus at most
$1$ (Remark~\ref{rem:positivity})." Paper prose: the first shared marker of § 3.4 is at
`04-classical.tex:473`.

---

## Summary

| Item | Finding (report) | Verdict | Class | Response |
|---|---|---|---|---|
| 1 | $(G, W)$ after the earlier papers and the vocabulary; vocabulary repeated in § 2.1 | PARTLY (order deliberate; $(G, W)$ in the abstract); repetition CONFIRMED, and § 2's opening repeats the three papers too | author + safe | keep the order (recommended); de-duplicate on the § 2 side (§ 2.1 to one sentence and the formula; drop § 2's re-description of the papers). Reviewer's sentence declined: "symmetric" for rotation-invariant, point mass, [17], letter clash |
| 2.1 | "covariance matrices" for infinite-variance laws | CONFIRMED | safe | "on covariance matrices" → "on scale matrices" (0 words) |
| 2.2 | $\alpha$'s meaning | PARTLY (indexed and costed since round 1) | author | keep (recommended) or +9 words with a cut; reviewer's gloss right for $0<\alpha<2$, "continuous" unsupported |
| 2.3 | non-Gaussian: fail or re-measure? | PARTLY | author | keep (recommended); fix's "or increase its minimum scale" false for Matérn, logarithmic and rational orbits; abstract at its 250-word budget (+84 words proposed) |
| 3 | § 1 shape-adaptation paragraph elliptical | PARTLY | safe | rewrite given above: $\Sigma_w = wM$ with anchors, $M \ne I$, re-measurement each round (§ 4.1), stable orbits only with a wider minor axis, Matérn not at all |
| 16.1 | "Sketch" proofs are complete; rename to "Proof" | REFUTED (10–48 % of the blueprint proofs; E.4 omits steps) | decline | against `WRITING.md` § 3 and the author's D2; safe precision: "A proof marked as a sketch" (ten are headed "(sketch)") |
| 16.2 | line results machine-checked "from first principles" | PARTLY (defect); fix FALSE | decline + safe | new finding: § 1.1 p. 7 and App. I p. 103 name the line paper's formal development as built on / pinned; the lakefile requires only ScaleSpaceCore and Mathlib (Q-0460): correct both, on the isotropic paper's precedent |
| 16.3 | Lean's three axioms unexplained | CONFIRMED | safe | gloss propext, Classical.choice, Quot.sound |
| 17.1 | "Working draft"; "not yet released" | CONFIRMED as text | decline (release) / safe | date line is the release's; "in preparation" on pp. 5 and 53, TODO(module VI) kept |
| 17.2 | programme names; "version 0.1"; future dates | REFUTED | decline | names per `WRITING.md` § 1 and `adr/0005`; the version sentence is load-bearing (iso renumbering); the dates are past |
| 17.3 | `notes/PROCESS.md` and the ratio | PARTLY | decline now | pass 5 (archivist): a private path must be deposited or go; the reviewer's text drops the date and "lower bound" (`WRITING.md` § 6) |
| 18.1 | "incomparable … (Remark 3.14)" | PARTLY | decline (optional safe) | "which neither imply the classical ones nor follow from them" |
| 18.2 | "§3.5 sets the axiomatics side by side." | PARTLY | decline | light signposting allowed |
| 18.3 | "Remark 3.13 shows how …" | CONFIRMED | safe | content sentence given above; fix dropped the probability-measure hypothesis |
| 18.4 | "Where positivity enters is Remark 3.11." | CONFIRMED | safe | "Positivity enters twice: … (Lemma 3.8) … (Remark 3.11)" |
