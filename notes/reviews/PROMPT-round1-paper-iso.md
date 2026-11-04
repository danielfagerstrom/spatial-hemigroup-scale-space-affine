# Prompt for the external review of the isotropic paper, round 1

From article-kit's `docs/templates/external-review-prompt.md`; the procedure is its `docs/PROCESS.md` § 9.

## For the author

Attach the PDF of the frozen build (the repository revision tagged `iso-review-1`, 61 pages;
`review-build-iso-review-1.pdf` in this directory, untracked). Run part A in a system of another vendor
than the one that wrote the text, set to its highest reasoning effort; part B may be run in the same
or another system. Save each output verbatim here as
`review-content-iso-review-1-<system>-<setting>.md` and
`review-presentation-iso-review-1-<system>-<setting>.md`. Nothing else is attached: no earlier review,
no record of this repository.

If a system stops before the end of part A, run it once per block (§§ 1–2; §§ 3.1–3.2 with their
proofs in Appendix A; § 3.3 with its proofs; § 3.4 with its proofs, § 4 and Appendix B) with the
sentence "Review sections N to M in detail and the rest for consistency with them" added at its
head, and save each output.

---

## Part A, a content review

You are a referee for a mathematical-imaging journal (JMIV class), reviewing the attached
manuscript, *Spatial scale space from hemigroup axioms: rotation-invariant self-decomposable
kernels in dimension d*. It belongs to a series by the same author. Two earlier papers, cited as
the line paper and the cone paper, classify the admissible smoothing kernels on the real line and
describe the class; this one carries the theory to rotation-invariant kernels on $\mathbb{R}^d$.
Section 2 restates what it uses of the earlier papers, and the manuscript is meant to be readable
on its own: say where it is not. Write a detailed referee report. Be specific, cite pages of the
PDF, and separate what is wrong from what is merely improvable.

1. **Overall assessment and recommendation** (accept, minor revision, major revision, reject), with
   the reasons in a paragraph.

2. **The headline claims against what is proved.** The abstract, the questions, answers and
   contributions of section 1, Table 3 ("What is in print") and section 4 make claims; check each
   against the statements and proofs that are supposed to carry it. Say where a claim is stronger
   than its result, where a qualification made in the body is missing from the headline, and where
   a scope statement leaves a wrong impression. The claims most at risk:
   - that the rate of the kernel at its centre (Proposition 3.15), an asymptotic equivalence
     with an explicit constant for $0 < c < d$ and a logarithmic form at $c = d$, is new in
     dimension $d \ge 2$ "as far as the author has found";
   - that the threshold $c > d$ for a bounded kernel, its boundary case included
     (Theorem 3.12), and the two-sided bounds with explicit constants
     (Propositions 3.16 and 3.17) are "not found stated" for this class although their
     ingredients are known, and whether the paper says clearly enough which ingredients are whose;
   - that the dimension filtration is strict at every step, the steps from $\mathcal{A}_3$ on being
     new (Theorem 3.19), with critical values of exact order $d^{-1/2}$;
   - that no member of a Cin ray lies in $\mathcal{A}_2$ (Theorem 3.20);
   - every sentence that reads a statement for imaging: what "bounded at the centre" and the
     dimension dependence are said to mean for a filter, and the sentences of sections 1 and 4 that
     say the dimension "enters twice";
   - the scope sentences: that the statements about the centre concern a kernel "from scale zero"
     with no Gaussian part, and that the Student-t clause of Proposition 3.11 is conditional.

3. **Mathematical correctness.** Read the statements and their proofs (most proofs are in
   Appendix A). Report every gap, error or unjustified step, with the page. Section 1.1 says that
   every statement of section 3 and the six lemmas of Appendix A are machine-checked in Lean, on
   seven cited theorems (C1 to C7, section 2.6). The printed proofs were written separately from
   the formal ones and are what a reader has, so read them as if nothing were machine-checked, and
   say where a printed proof does not prove the printed statement. Pay particular attention to:
   - Proposition 3.15 (the rate) and its proof: the passage from the Fourier transform of a
     radial law to a Laplace-type transform; the use of Karamata's Tauberian theorem (C7) and
     whether its hypotheses hold as used (regular variation of the normaliser, the range of the
     index, the direction of the theorem); the monotone density step that passes from the mass of
     a ball to the density; the constant $R(d,c)$; the boundary case $c = d$, where the normaliser
     is the integral of the transform over a ball and the lower bound is logarithmic;
   - Theorem 3.12 (the threshold), especially the boundary case $c = d$ and the clause
     that a bounded kernel is continuous, and Corollary 3.13;
   - Proposition 3.14 (the radially nonincreasing density), which the paper attributes to
     Watanabe (1983) and proves from Wolfe's theorem (C5): the averaging of a mixture of uniform
     laws on convex sets over the rotations, the measurability step (an analytic set is universally
     measurable), and the absence of an atom; and the gap that section 1.1 reports in the source of
     C5 for a law with a Gaussian part: is the account of that gap, and of which statements it
     touches, correct and sufficient?
   - Propositions 3.16 and 3.17 (the bounds) and Lemmas A.1 to A.6, with their explicit
     constants;
   - Theorem 3.6 and Corollary 3.7 (the classification on kernels and on
     operators): the reduction to the line through a one-dimensional marginal, Lemma 3.3
     (operators to kernels) and its regularity hypotheses, and whether the axioms of
     Definitions 3.1 and 3.2 are the ones the proofs use;
   - Propositions 3.10 and 3.11 (the polar form of $\mathcal{A}_d$; the bridge from
     time-causal families), and the conditional Student-t clause: does every later use respect the
     condition?
   - Theorems 3.19 and 3.20: the separating family, the monotonicity and the limit of
     its critical values, the use of Schoenberg's theorem (C6) for
     $\mathcal{A}_\infty = \mathcal{S}$;
   - the seven cited facts of section 2.6: is each stated as its source states it, at the page
     given, and used within its hypotheses? Section 1.1 says three of them depart from the letter
     of their source (C5, C6, C7); are the departures sound?
   - the statements restated in section 2 from the line and cone papers: are they used as
     restated?

4. **The numerical examples.** The paper works the Matérn (symmetric variance-gamma) kernel at both
   cases of the rate, from the closed form of its density, and has two figures drawn by scripts
   (the Matérn kernel near its centre; the critical values of the separating family against the
   dimension). Do the worked constants agree with the closed form (reproduce them if you can: the
   limit of the density against the normaliser for $0 < c < d$, and the logarithmic case $c = d$)?
   Do the figures show what their captions say, and is anything concluded that a figure or a
   computation cannot show?

5. **The trust base.** Section 1.1, its table, section 2.6 and Appendix B state what the
   machine-checked development assumes, what is not formalized, and how the agreement between the
   formal and the printed statements was reviewed (by AI agents only; no human, the author
   included, has reviewed the formal statements). Is the account clear, complete and honest as a
   reader would judge it? Is anything claimed as verified that the text elsewhere qualifies? Does
   Appendix B give a reader what is needed to repeat the check, and what should a reader be told
   that is not there?

6. **Novelty and relation to prior work.** The paper positions itself against: Sato's book (the
   classification of self-decomposable laws on $\mathbb{R}^d$, Theorems 16.1, 28.4, 53.8) and
   Hazod–Siebert; Sato–Yamazato (1978), Zolotarev (1963) and Wolfe (1971) for the density of a
   self-decomposable law on the line at its mode; Watanabe (1983) for the radially nonincreasing
   density; the heat-kernel literature on isotropic unimodal Lévy processes
   (Bogdan–Grzywny–Ryznar 2014; Grzywny–Ryznar–Trojan 2019; Cho–Kang–Kim 2021; Knopova–Schilling
   2013; Mimica 2016), which estimates the transition density for small times, including for
   exponents that vary slowly; Trabs (2014); Hartman–Wintner (1942); Feller's corollary on positive
   transforms; Karamata theory in Bingham–Goldie–Teugels; Schoenberg (1938) and Gneiting (1999) on
   radial positive-definite functions and their dimension dependence; the Matérn family in spatial
   statistics (Matérn, Stein, Guttorp–Gneiting) and its identification with the variance-gamma
   law; Pauwels et al. (1995), the alpha scale spaces of Duits et al. (2004), and the scale-space
   axiomatics of Koenderink, Florack and Lindeberg. Is the positioning accurate, and is Table 3 right row by row? In particular:
   is the rate at a fixed law (Proposition 3.15), or the threshold with its boundary case, in
   print for isotropic self-decomposable or unimodal laws on $\mathbb{R}^d$, for instance as a
   consequence of a small-time estimate by a scaling or subordination argument the paper has
   missed, or in the literature on variance-gamma, generalized hyperbolic or type G laws, on
   Bessel potentials and their kernels, or on local properties of Lévy densities
   (Kim–Mimica, Cygan–Grzywny–Trojan, Kaleta–Sztonyk, Kulczycki–Ryznar, Picard, Orey)? Is the
   strictness of the dimension filtration known from the literature on radial positive-definite
   or self-decomposable laws in several dimensions? Is anything attributed wrongly, or relevant
   work missing?

7. **Exposition and structure.** Where does the argument become hard to follow, where is a
   definition used before it is given, where is a forward reference load-bearing, where does the
   paper lean on the line or cone paper in spite of section 2, and which remarks, paragraphs,
   table rows or figures could go without loss? The main text is 30 pages and the manuscript
   61 with its appendices; say what a journal version should lose and whether the division
   between section 3 and Appendix A is right.

8. **A numbered list of required changes** (what must change for acceptance) and a separate
   **numbered list of suggestions**, each item with a page reference and one sentence of reason.

Do not summarize the paper back to the author beyond what the assessment needs. Do not soften
findings; a wrong claim should be called wrong. If you are unsure whether something is an error,
say so and say what would settle it.

---

## Part B, a presentation review (optional, a second run)

You are an experienced editor of a mathematical-imaging journal. Read the attached manuscript as
its intended reader would: a researcher in scale-space theory or image analysis who knows Fourier
analysis and basic probability, has not read the earlier papers of the series, and does not know
the theory of Lévy processes or of regular variation. Mathematical correctness is out of scope.
Rank the twenty changes that would most improve its readability, each with a page reference, the
phrase quoted, what is wrong, and a concrete fix. Consider:

- the abstract and section 1: does that reader know after three pages what the paper shows, why it
  matters to someone who designs or uses a scale space, and what it does not claim?
- the register: sentences that are hard to parse, coined terms a reader would not follow (the paper
  uses "from scale zero", "origin datum", "polar profile", "delay", "bridge", "separating family",
  "critical value", "Cin ray", "cited fact"), places where the text announces instead of stating,
  and any passage that reads as written for the author's own project and not for the field;
- the opening of each subsection of section 3: does it say what is coming and why it is of
  interest before the statements start?
- Table 3, the trust-base table, the notation table and the two figures: is each earning its
  place, is any hard to read at print size, and is a figure missing?
- the notation: collisions, symbols used before they are introduced, letters that change meaning
  between the paper and the literature it cites (the paper says how its $c$ relates to the
  literature's process time);
- section 1.1 and Appendix B: can a reader who has never used a proof assistant tell what was
  checked and what was not?
