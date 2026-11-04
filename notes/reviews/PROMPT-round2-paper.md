# Prompt for the external review of the affine paper, round 2

From article-kit's `docs/templates/external-review-prompt.md`; the procedure is its `docs/PROCESS.md` § 9.

## For the author

**The rounds run in sequence, each on its own frozen build** (the author's decision of 2026-11-03).
Round 1, the content review (part A, Gemini 4.0 Argon, High), read the build at `07a131d`; its
findings were verified (`VERIFY-round1-{claims,mathematics,exposition}-paper.md`), decided
(`../PLAN-review-response-paper.md`, § 0) and applied. The revised build is frozen at the repository
revision `5f6f72c` (the head of danielfagerstrom/spatial-hemigroup-affine#174, 108 pages;
`review-build-review-2.pdf` in this directory, untracked), to be tagged `review-2`. The cloud
session that froze it can push only its branch, so both tags are pushed from a desktop:

```bash
git tag -a review-1 07a131d -m "Frozen for the external review, round 1" && git tag -a review-2 5f6f72c -m "Frozen for the external review, round 2" && git push origin review-1 review-2
```

Round 2 is the presentation review, part B below. It may run in the same system as round 1 or in
another, at its highest reasoning effort; save the output verbatim here as
`review-presentation-review-2-<system>-<setting>.md`, naming the model and the setting. Nothing else
is attached: no earlier review, no record of this repository. A second content review, when another
vendor's system is available again, reads the build frozen after round 2's response (`review-3`),
so that its page references are those of the text it is answered in.

---

## Part B, a presentation review

You are an experienced editor of a mathematical-imaging journal (JMIV class). Read the attached
manuscript, *Spatial scale space from hemigroup axioms: affine covariance and shape adaptation*, as
its intended reader would: a researcher in scale-space theory or image analysis who knows linear
algebra, Fourier analysis and basic probability, has not read the earlier papers of the series (the
line paper, the cone paper and the isotropic paper, which section 2 restates), and does not know the
theory of Lévy processes, of operator-self-decomposable laws or of Lie semigroups. The manuscript
has been revised after a referee report; you have not seen that report. Mathematical correctness is
out of scope. Rank the twenty changes that would most improve its readability, each with a page
reference, the phrase quoted, what is wrong, and a concrete fix. Consider:

- the abstract and section 1: does that reader know after four pages what the paper shows, why it
  matters to someone who designs or uses an anisotropic or shape-adapted scale space, and what it
  does not claim? Is the choice of a group and an order, the organizing idea of the paper,
  understood before it is used?
- the register: sentences that are hard to parse, coined terms a reader would not follow (the paper
  uses "cascade family", "from scale zero", "aperture", "volume scale", "variance gauge", "step
  set", "rank-deficient step", "profile", "dilation ratio", "anisotropy budget", "wedge", "the
  chain", "stable order", "the frame's shapes", "the landscape", "rungs", "the speed limit"),
  places where the text announces instead of stating, and any passage that reads as written for the
  author's own project and not for the field;
- the opening of each section and subsection of sections 3 and 4: does it say what is coming and why
  it is of interest before the statements start? Section 4 is long (pp. 25–52): does its map
  (section 4.1 to 4.3) let a reader find the result they came for?
- Table 1 (notation), Table 2 (the landscape), Table 3 (the speed limit) and Figures 1 to 3: is each
  earning its place, is any hard to read at print size, are the legends enough to read them without
  the text, and is a figure missing (for instance, of the chain of cones or of a shape-adapted
  cascade)?
- the notation: collisions, symbols used before they are introduced, letters that change meaning
  between sections or between the paper and the literature it cites (the scale parameter against
  the variance, $t$ against $\Sigma$, the three uses of a letter for a radius or a ratio);
- the balance between body and appendices (about 54 pages of text, 48 of appendices): which proofs
  or remarks would a reader rather meet in an appendix, and which appendix material is needed to
  follow the body?
- section 1.1 and Appendix I: can a reader who has never used a proof assistant tell what was
  checked, what is proved in print only, and what is assumed?
- the references: is a source cited where the reader needs it, by page or statement, and is any
  citation load-bearing that the reader cannot follow without the earlier papers?

Do not summarize the paper back to the author. Quote the phrase each change concerns, and give a fix
that could be applied as written.
