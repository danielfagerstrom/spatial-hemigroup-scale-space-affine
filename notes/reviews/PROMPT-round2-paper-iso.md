# Prompt for the external review of the isotropic paper, round 2

From article-kit's `docs/templates/external-review-prompt.md`; the procedure is its `docs/PROCESS.md` § 9.

## How this round is run

The frozen build is the repository revision tagged `iso-review-2` (86 pages; `review-build-iso-review-2.pdf`
in `records/affine/reviews/`, untracked). The author chose Claude Fable for this round (2026-10-12): a
model that has done none of the paper's authoring. It is run by the dispatching session as five fresh
agents, one per part, each of which is given only: the manuscript, the three earlier papers of the
series that the manuscript cites (the first-round referee could not retrieve them), and Lean's axiom
report for the paper's formal statements. No file of the repository, no earlier review, no record. Each
output is saved verbatim as `review-round2-iso-review-2-<part>-claude-fable.md`.

For the record of independence: Fable has twice read pieces of this work as a blind referee of
statements, not of the paper: the derivation of the rate at the centre (2026-10-11) and four structural
statements of § 3.4 (2026-10-12). The first round was run in another vendor's system (GPT-6.1 Sol, Ultra).

The parts: A, the front (abstract, § 1, § 1.1, § 2, Appendix B, the declarations); B, § 3.1–3.2 with
their proofs in Appendix A; C, § 3.3 with its proofs; D, § 3.4 with its proofs, and § 4; E, the paper as
a whole against the literature, and its exposition.

---

## The prompt (each part receives this, with its own part named in the last section)

You are a referee for a mathematical-imaging journal (JMIV class), reviewing the manuscript
`manuscript.pdf`, *Spatial scale space from hemigroup axioms: rotation-invariant self-decomposable
kernels in dimension d*. It belongs to a series by the same author: `line-paper.pdf` and
`cone-paper.pdf` classify and describe the admissible smoothing kernels on the real line, and
`time-causal-paper.pdf` is the earlier paper on time-causal families; this manuscript carries the theory
to rotation-invariant kernels on $\mathbb{R}^d$. Its section 2 restates what it uses of the earlier
papers, and it is meant to be readable on its own: say where it is not. The manuscript has been revised
after a referee report; you have not seen that report, and you should not assume that anything has
already been checked. `lean-axiom-report.txt` is the proof assistant's report of which assumptions each
formal declaration depends on. Read only these five files; you may search the literature and compute.

The manuscript presents itself as a paper in scale-space theory: it derives the rotation-invariant
scale spaces that its axioms allow and describes them, it says that it claims no new result for
probability theory, and it attributes the statements it uses or reproves to their sources in one
place (the subsection "Sources" at the head of Appendix A). Hold it to that.

Write a detailed referee report. Be specific, cite pages of the PDF, and separate what is wrong from
what is merely improvable.

1. **Overall assessment and recommendation** (accept, minor revision, major revision, reject), with the
   reasons in a paragraph.
2. **The headline claims against what is proved.** The abstract, the questions, answers and
   contributions of section 1, and section 4 make claims; check each against the statements and proofs
   that carry it. Say where a claim is stronger than its result, where a qualification made in the body
   is missing from the headline, and where a scope statement leaves a wrong impression. In particular:
   the main result as section 1 states it (the rotation-invariant self-decomposable laws are exactly
   the kernels from scale zero of the isotropic scale spaces the axioms define: is that what
   Theorem 3.6, Corollary 3.7 and Lemma 3.8 prove, with which qualifications); every sentence that
   reads a statement for imaging (what an unbounded kernel means for a recorded image; derivative
   filters; what "admitted in a dimension" means for a filter given by one radial transfer function);
   every sentence comparing the hemigroup axioms with the semigroup axioms of the scale-space
   literature; and the sentence that the paper claims no new result for probability theory: is anything
   nevertheless presented as if it were the paper's own that is known, or attributed wrongly?
3. **Mathematical correctness.** Read the statements and their proofs (most proofs are in Appendix A).
   Report every gap, error or unjustified step, with the page. The printed proofs are what a reader
   has: read them as if nothing were machine-checked, and say where a printed proof does not prove the
   printed statement. Section 1.1 lists four statements that are proved in print only: give those the
   closest reading. Check the cited facts C1 to C7 of section 2.6 against how they are used, and the
   statements restated in section 2 against `line-paper.pdf` and `cone-paper.pdf` (same hypotheses,
   same conclusions, right statement numbers).
4. **The worked examples and figures.** Reproduce what you can: the constants of the Matérn example
   (Example 3.14 and its continuations: the threshold, the two limits of the rate, the profile, $C_k$,
   $K(0+)$, $Q$, the coefficient), the logarithmic profile, the dependence on scale, the functions
   $\Omega_1, \Omega_2, \Omega_3$ and the Matérn exponent put through the dictionary, the shadow of the
   step profile, the critical values $w_1, w_2, w_3$, the case $w = 4$, and the limit
   $\sqrt d\,w_d \to \sqrt\pi$ with what the text says about how it is approached. Do the figures show
   what their captions say?
5. **The trust base.** Section 1.1, section 2.6, Appendix B and the statement on the use of AI say what
   is machine-checked, what is proved in print, what is assumed and what is computed. Is the account
   clear, complete and honest as a reader would judge it? Compare it with `lean-axiom-report.txt`:
   does each statement's row agree with the table of cited facts per statement in Appendix B; does any
   declaration depend on an assumption outside the nine named in Appendix B; is anything said or
   implied to be verified that is not?
6. **Sources and relation to prior work.** Check the Sources subsection row by row against the
   literature you can reach: is each statement attributed to where it is stated, with the right
   hypotheses and credit; is a closer or earlier source missing; is any source cited for more than it
   says? And the relation to scale-space theory in section 1: is it accurate about Koenderink,
   Florack et al., Lindeberg, Pauwels et al., Duits et al., and is scale-space work missing that a
   referee of this field would expect (non-Gaussian and Matérn or Bessel-type kernels in scale space,
   the Poisson and alpha scale spaces, recursive and first-order smoothing filters, temporal and
   time-causal scale spaces, scale-space axiomatics without a semigroup)?
7. **Exposition and structure.** Where does the argument become hard to follow for a reader in
   scale-space theory or image analysis who knows Fourier analysis and basic probability and does not
   know Lévy processes or regular variation; where is a term used before it is defined; what in the
   30 pages of main text could go and what is missing from them; is the division between main text
   and appendices right (two bounds, the notation table, the table of cited facts and the sources are
   in the appendices); the manuscript is 86 pages: what should a journal version lose?
8. **A numbered list of required changes** and a separate **numbered list of suggestions**, each with a
   page reference and one sentence of reason.

Do not summarize the paper back to the author beyond what the assessment needs. Do not soften findings;
a wrong claim should be called wrong. If you are unsure whether something is an error, say so and say
what would settle it.

**Your part.** The paper is long, so five referees each take one part in detail and read the rest for
consistency with it. Yours is named below. For your part do everything above that applies to it, at
the level of every statement, proof step and constant; for the rest of the paper, report only what you
notice.
