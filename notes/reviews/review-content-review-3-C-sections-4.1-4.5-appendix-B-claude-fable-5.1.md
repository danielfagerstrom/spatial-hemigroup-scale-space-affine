# Referee report C: §§ 4.1–4.5 and Appendix B (the rest read for consistency)

**Manuscript:** *Spatial scale space from hemigroup axioms: affine covariance and shape adaptation* (working draft, 111 pp.).

**Scope of this report.** I reviewed §§ 4.1–4.5 (pp. 27–37) and Appendix B (pp. 66–70) in detail, with the proofs of the statements of that block that the paper defers to Appendix C (Propositions 3.4, 4.2 and 4.12, Lemma C.1, Theorem 4.3, pp. 70–77), and I read the rest of the manuscript for consistency with the block. Page numbers are those of the PDF. I had no access to the deposited scripts, the LaTeX sources or the Lean development, and read every proof as if nothing were machine-checked. Three hosts needed for page checks of the imaging sources (link.springer.com, www.kth.se, www.ece.lsu.edu) are not reachable from this session, so the page anchors into Lindeberg–Gårding and Mikolajczyk–Schmid cited in § 4.1 are unverified here; I say below what they assert.

---

## 1. Overall assessment and recommendation

For the block I refereed, the mathematics is correct. I found no error in a statement or a proof of §§ 4.1–4.5 or Appendix B, nor in the Appendix C proofs these sections rest on (Proposition 4.2, Lemma C.1, Theorem 4.3, Proposition 4.12, Proposition 3.4). The one slip is a transposed product in the proof of Proposition 4.10 (p. 67), which does not affect the conclusion. The dictionary between invariant orders and step sets (Proposition 4.2), the majorization proof that a cone field's order is exactly exp C (Theorem 4.3), the scale–shape reading of the Loewner order (Lemma 4.1) and the ray base (Propositions 4.4, 4.5) are cleanly stated and the proofs are complete at the level a journal needs. Numerical sanity checks I ran (random composites of steps of exp Cα in d = 2, 3, 4; Lemma 4.1 on random Loewner pairs; the Frullani/compound-Poisson identity of Proposition 4.4(4); the radii, slopes and the dashed arrow of Figure 2; the openings k of Figure 3) all agree with the printed statements.

What needs work is at the level of claims and presentation rather than proofs: Table 2 (p. 32) does not say which cells are complete and the general linear cell along the stable order is less complete than §§ 4.3 and 4.7 let a reader believe (it describes only laws without a Gaussian part); one sentence of the "Prior art" paragraph of § 4.4 (p. 36) claims as new something that is the content of a theorem the same paragraph cites; and several sentences of § 4.1 read a theorem about increments as a statement about computation ("re-measurement of the original image") that the paper's own scope paragraph disclaims. These are all repairable without touching a proof.

**Recommendation for this block: minor revision.** I make no recommendation for the parts I read only for consistency; nothing in them contradicts §§ 4.1–4.5 or Appendix B.

---

## 2. The headline claims against what is proved

**The classification, "completely in some cases" (abstract p. 1; § 1 p. 3; Table 2 p. 32).** The abstract and the introduction promise that the table says cell by cell what is known, "a complete description in some cases and bounds or examples in the others". Table 2 does not mark completeness at all; the reader infers it from the wording of each cell ("the orbits …" versus "contains …"), and the only cell-by-cell accounting is the last paragraph of § 5 (p. 54), which says that four cells stop short of a classification and three more are classified on part of their parameters. Counting from § 5, exactly two of the nine cells are complete, (GL(d), rays) and (GL(d), Loewner); the two ray cells of the smaller groups are complete only as characterizations by Proposition 3.4(2), with the extension problem of open problem 4 unsolved. § 4.3 should say this where the table is, not six pages after the last cell is filled.

**The general linear cell along the stable order (Table 2 p. 32; Theorem 4.21(3)(c) p. 48; § 4.7 p. 48 "the row is known to be at least the one stated"; open problem 1 p. 55).** The cell as printed, and Theorem 4.21(3)(c), describe laws with no Gaussian part whose Lévy measure has a density: Proposition 4.13 assumes both. The text then says that the converse of Proposition 4.13 "would complete the profile clause" and make the rows of Table 3 exact. This leaves a wrong impression. Laws with a Gaussian part are also in the cell and are not mentioned: for b > 0 and γ ≥ α the family µΣ = N(0, 2bΣ) ∗ Sγ(Σ) is a (GL(d), ≤α)-cascade family (its increments are N(0, 2b(Σ′−Σ)) ∗ ρΣ,Σ′ with Σ′−Σ ≥ 0 because ≤α lies in the Loewner order, Proposition 4.20(1), and GL(d)-covariance is clear); the paper's own Proposition 4.24(3) is this family with κ = 0 made similarity-covariant by the trace term. Whether a positive increment of an orbit with a Gaussian part forces ordered Lévy measures is not addressed anywhere, so the converse of Proposition 4.13 alone would not complete the row. The cell should say that it describes laws without a Gaussian part, and § 4.7 and open problem 1 should state the gap.

**The orders of invariant cones (§ 1 p. 4; § 4.4 pp. 31–36).** The introduction's paragraph "These are exactly the closed invariant partial orders whose steps are closed under fractional powers (Theorem 4.3)" matches Theorem 4.3(2) exactly, and the cone-field reading in § 4.4 matches clauses (1) and (4). The introduction describes the cone as "containing no line"; Theorem 4.3(1) allows cones with lines (and gets a preorder), and the pointedness enters only in (2) and (4). This is a scope difference in the right direction and needs no change.

**The picture in the plane (p. 33, Figure 3 and the paragraph under it).** The reading of Theorem 4.21 in the plane is correct: for the round cone of opening k, β(C) = 2k/(1−k), so β(C) < 2 exactly when k < ½, and C ⊆ PSD(2) exactly when k ≤ 1, with the singular directions reached at k = 1. The three shaded regimes are what Theorem 4.21(2)(a)–(c) gives.

**The ray base (§ 4.5 pp. 36–37; abstract, "a non-Gaussian kernel pays in speed of shape change").** Proposition 4.5 proves exactly what § 4.5 and the introduction say of it: along the rays every rotation-invariant self-decomposable law keeps its orbit, with GL(d)-covariance, and Proposition 4.4(3) with Theorem 3.7 closes every rank-deficient step to every non-Gaussian orbit. The sentence "this costs nothing beyond what the isotropic theory requires" (p. 36) is right by Theorem 2.5 and Lemma 2.6(1).

**The sentences that read a statement for imaging.**

- § 4.1, p. 28 (and § 4.6, p. 37; abstract; § 5): "Off the order, a change of aperture is a re-measurement of the original image." What is proved is that the increment is not a probability measure (and for the Matérn orbit of index 1 not even a finite signed measure, Proposition E.4). "Re-measurement of the original image" is a statement about how the record is computed, which § 5 (p. 54) says the paper makes no statement about and which it defers to a further paper. The reading is reasonable, but it should be announced as a reading once (§ 4.1) and the mathematical content stated beside it.
- § 4.1, p. 27, use 1: "Shape selection … needs a group that carries every shape to every other, as GL(d) does on PD(d)." This is a definition of what the paper means by shape selection (the selected aperture transforms with the image under every affine map) dressed as a necessity. § 4.9 (p. 51) then concludes that neither smaller group "supports shape selection in the sense of § 4.1". That is consistent, but the sentence in § 4.1 should be worded as the definition it is: a similarity-covariant family selects shapes too; what it loses is covariance of the selection under shears.
- § 4.1, p. 27, use 1, "Under that normalization even the Gaussian reaches an adapted aperture only by measuring the image afresh", and § 4.2, p. 29, "a selection of shape at fixed volume is a re-measurement for every family": these rest on Lemma 4.1(2), which is proved; the wording question above applies.
- § 4.1, p. 27, the description of the practice. Three claims rest on page anchors I could not check: that step 2 of Lindeberg–Gårding divides the shape matrix by its least eigenvalue so that the local scale matrix keeps least eigenvalue w ([36] p. 396 step 2; [37] § 6.2); that they reject the fixed-volume normalization "because it overestimates the anisotropy" ([37] § 6.1); and that Mikolajczyk–Schmid normalize the warp "so that the patch is enlarged and never shrunk" ([43] § 3.3 p. 72). The first and third agree with secondary accounts (Mikolajczyk–Schmid normalize the transformation so that its largest eigenvalue is 1 and enlarge along the smallest). The whole reading of § 4.8 and § 5 rests on the first, so the author should confirm it against the page, as the paper's own rule ("a source is read at the page") requires; a quotation in § 4.1 would settle it for the reader.

**Scope sentences (§ 1 p. 5; § 5 p. 54).** "The paper is theory and makes no empirical claim about images" and "it does not compute the families on a grid" are consistent with the block, provided the re-measurement sentences are worded as readings.

---

## 3. Mathematical correctness

I checked every statement of the block and its proof. Findings, in order of the text.

**Lemma 4.1 (p. 28; proof p. 66).** Correct. The congruence M = (t2/t1)² N, the bounds in (3) (nd ≤ n1^{−(d−1)} gives nd/n1 ≤ (t2/t1)^{2d}), the converse construction and the planar disc of (4) all check, and a random test of 2000 Loewner pairs in the plane found no violation of (1), (3) or (4). The identification of δ with the affine-invariant Riemannian distance (p. 29) is the standard one.

**Proposition 4.2 (p. 34; proof pp. 70–71).** Correct. The computation in (3) (relative step of the composite M^{1/2}N′M^{1/2} with N′ = QᵀNQ, and the equivalence of transitivity with SK closed under products through the polar decomposition A1 = M1^{1/2}Q1) is complete. One small point in (4): C(K) is invariant under X ↦ cX, c ≥ 0, only in the sense that it is empty when I ∉ K (t = 0 forces I ∈ K); harmless, but a reader who tries c = 0 notices it.

**Lemma C.1 (pp. 71–73).** Correct, and it is the engine of Theorem 4.3. The paper's "x ≺ y" (sums of the k smallest entries of x at least those of y, equal totals) is the usual majorization read from the other end; the derivation of (2) from C4 by subtracting from equal totals is right, and (3) (symmetric closed convex cones are closed under majorization, by the dual description and Abel summation) and (4) (the eigenvalue cone, and the sign of the trace on a pointed invariant cone through the cyclic shifts) are proved completely.

**Theorem 4.3 (pp. 34–35; proof pp. 73–75).** Correct. The decisive step, that a C-causal curve ends at a relative step in exp C, is proved through the superadditive functionals F_w: g(t) = F_w(γ(0), γ(t)) is shown absolutely continuous with g′ ≥ Σ w↓_i λ↑_i(Y) ≥ 0 almost everywhere, which is sound (the Lipschitz control of the eigenvalues through Lemma C.1(1), the lower bound on the least eigenvalue of N(t), and the expansion N_h = I + hY + o(h) are all in place). Clause (2)'s description of the tangent cone through the Lie product formula, clause (3)'s closed order without a cone, and clause (4)'s extension to PSD(d) are complete. A random test of 4800 composites of steps of exp Cα (d = 2, 3, 4; α = 0.5, 1, 1.5, 3) found none outside the cone, as Lemma C.1(5) predicts.

**Proposition 4.12 (statement p. 42; proof pp. 75–76).** Correct; the three facts about curves, Jacobi's formula for (det γ)^s γ and the identification of ⪯Cα with λmin(M)^{d+α} ≥ det M are complete. This proof does not spend C4, as Appendix I says.

**Proposition 4.4 (p. 36; sketch p. 66).** Correct. In (3), "g is not linear" means "g(u) ≠ bu for every b ≥ 0", which is what Theorem 3.7 excludes; say so. In (4) the compound Poisson residual is right: the Lévy measure γ(e^{−x/λ²} − e^{−x})x^{−1}dx is nonnegative for λ > 1, has mass 2γ log λ by Frullani, and gives E e^{−uY} = ((1+u)/(1+λ²u))^γ; I verified both identities numerically to six digits for two parameter pairs.

**Proposition 4.5 (p. 37; proof p. 37).** Correct and complete.

**Lemma 4.6 (proof p. 67).** Correct, including the finiteness and positivity of c_{d,α} and the use of C2(iii) with the vanishing of the odd part of the integrand.

**Proposition 4.10 (proof p. 67).** The conclusion is correct, but the display "Here Mt = e^{tB}e^{tBᵀ}" is wrong as written: the relative step of (Σt, I) with Σt = e^{−tB}e^{−tBᵀ} is Σt^{−1} = e^{tBᵀ}e^{tB}, and it is this matrix whose least eigenvalue is min_{|x|=1}|e^{tB}x|². The two products have the same spectrum, so nothing downstream changes. Correct the display.

**Proposition 4.11(2) (proof p. 67)** and **Lemma 4.14 (sketch pp. 67–68).** Correct. In Lemma 4.14(4) the example step diag(λ², …, λ², λ^{2(1+α)}) sits exactly on the boundary of ⪯α and yields R(λ) ≥ λ^α; the dyadic profile of (5) gives β− = 0, β = 1 as claimed.

**Proposition 4.15 (proof pp. 68–69).** Correct, but a page longer than it needs to be. The functional Λ(ϕ) = lim_{R↓0} ∫ ϕ(x/R) ρ(dx) is, by dominated convergence alone (ϕ bounded with compact support, ρ finite), equal to ρ({0}) ϕ(0). The three paragraphs "Λ vanishes on test functions vanishing near 0" and "Λ is a multiple of the point mass" prove this fact by a dilation-invariance argument and can be replaced by that one sentence; the paragraph "h is constant" then gives h ≡ ρ({0}) off 0 as now. As a by-product, which deserves a remark, the proof shows that a positive increment along a ray Σ → cΣ carries an atom at the origin of mass c^{−κ}; for the Matérn orbit this is the P(Y = 0) = λ^{−2γ} of Proposition 4.4(4), a nice consistency check between the two propositions.

**Proposition 4.18 (sketch p. 69)** and **Proposition 4.19 (proof p. 69).** Correct. (The text extraction of Lemma 2.9(2) on p. 12 shows "2c log a"; the rendered page reads ½ c log a, which is what the proof of Proposition 4.19 uses with κ = ½|S^{d−1}| k(0+), and which the Matérn case confirms: c = 2γ, κ = γ.)

**Proposition 4.24 (sketch pp. 69–70).** The bounds in (2) are derived correctly from the sandwich εI ≤α Σ ≤α tI and the three elementary inequalities (monotonicity of Ms in the Lévy measure, Ms((aI)∗L) = a² M_{s/a}(L), and 1 − cos 2τ ≤ 4(1 − cos τ)); the covariance and the increments in (3) check, including the role of the Gaussian factor in Lemma 4.8 for the rank-deficient step. Clause (1), however, is not proved in Appendix B at all: the sketch says "the rest is the proof of Proposition H.9(1)". A pointer is not a sketch; either give the argument (it is five lines: the path condition from Proposition 4.20(1), Theorem 3.5(2), symmetry from −I ∈ S(d), the triplet from C2(ii)) or say in Appendix I that 4.24(1) is proved in H.9.

**Proposition 3.4 (proof pp. 76–77).** Correct; the no-zeros argument through 1 − |ρ̂(2ω)|² ≤ 4(1 − |ρ̂(ω)|²) is complete.

**Cited facts in the block.** C4 is used only through Lemma C.1(2), where the inequality is applied to log λ↓ of M, N and of M^{1/2}NM^{1/2}, with the equality of the totals supplied by the determinant; that is exactly the form stated in § 2.4. Theorem 4.21's proof deliberately avoids C4 by rederiving the order properties from causal curves (p. 81), and the axiom printout on p. 105 is consistent with that. No other cited fact enters the block except C2(iii) in Lemma 4.6, Proposition 4.13 and 4.19, used with symmetric Lévy measures and a vanishing odd part, which is correct.

---

## 4. The numerical examples (the block's part)

Figures 2 and 3 are the only computed objects in the block, and both are plots of closed-form expressions. Figure 2 (p. 30): I recomputed the disc radii at t2 = 2t1 (Loewner 2√2 log 2 ≈ 1.96; α = 0.5, 1, 1.5: 0.39, 0.65, 0.84), the slopes in panel (b) (2, 0.4, 2/3, 6/7, 0) and the dashed arrow (log-anisotropy log 2 is reached on the Loewner edge at log(t2/t1) = ½ log 2 and on the stable edge of index 1 at (3/2) log 2, a volume-scale ratio of exactly 2), and they agree with the caption and with § 4.8 (the minor-axis factors 4, 2.52, 2.07 at α = 1, 1.5, 1.9 also check). Figure 3 (p. 33): k = 1/3 and 1/2 for C1, C2. The caption's "discs checked against the two orders on random steps" is a sensible self-test of the formulas, not a numerical finding, and nothing is concluded from the figures that the formulas do not show. The figures are reproducible from the captions alone. One omission: the caption of Figure 2(b) does not say which slants (or which M) the four crosses correspond to.

---

## 5. The trust base (the block's part)

Appendix I (pp. 103–105) is consistent with what the block's proofs actually use: Theorem 4.3 rests on C4 through Lemma C.1(2) and (5) in its clauses (1), (2) and (4) and in nothing else; Proposition 4.2 and 4.12 rest on no cited fact; Lemma 4.6 and Propositions 4.13, 4.19 rest on C2. The twenty statements listed as sketched include every proof of Appendix B that is labelled a sketch (4.4, 4.18, 4.24, Lemma 4.14) and nothing that is not, and § 1.1's statement that the complete proofs are in the deposited sources is the right disclosure. I checked that each sketch in Appendix B contains the decisive steps; the exception is Proposition 4.24(1), as said above. Nothing in the block is claimed as verified that the text elsewhere qualifies.

---

## 6. Novelty and relation to prior work (the block's part)

**Lemma 4.1** is textbook matrix analysis and is presented as such; the paper claims nothing for it beyond the reading. **Proposition 4.2** is elementary. The affine-invariant metric remark (p. 29) is correctly attributed to Pennec–Fillard–Ayache and Bhatia.

**Theorem 4.3 against Lawson and Hilgert–Hofmann–Lawson (p. 36, "Prior art").** The paragraph says what is new "against the sources read": the reading on PD(d) through step sets and their spectra, the proof by majorization, "the equality of the order with exp C without a closure", and cones that are not pointed. The third item is overstated. For a pointed Ad(O(d))-invariant cone C ⊆ Sym(d), the theorem on Ol'shanskiĭ semigroups (the one the paragraph itself cites for transitivity, HHL Cor. V.4.58, in Lawson's polar form in *Polar and Ol'shanskiĭ decompositions*, J. reine angew. Math. 448 (1994)) states that O(d) exp C is a closed subsemigroup of GL(d); the order it induces on PD(d) = GL(d)/O(d) is "relative step in exp C" by definition, so "the order is exp C without a closure" is that theorem read on PD(d), not something new to it. What is new in Theorem 4.3 is the self-contained proof by majorization, the non-pointed case of clause (1), the characterization by fractional powers in clause (2) for this space, and the counterexample (3). The paragraph should say so and cite Lawson 1994. The reason given for not using HHL's divisibility theorem, that GL(d) is not connected, is not a reason: Proposition D.1 already shows that everything can be read on GL⁺(d), which is connected.

**The stable orders.** The paper is right that they are the Loewner order in other coordinates (Proposition 4.12(3)) and that what is new is their role as the orders of the stable orbits (Proposition 4.7); the step set of an orbit is, as § 4.6 says, Urbanik's decomposability semigroup transported to the orbit. I found nothing in the block claimed as new that is known, and nothing attributed wrongly, beyond the sentence above.

**Proposition 4.4(4).** The Gamma-mixture representation and the self-decomposability of the symmetric law with transform (1+|ω|²)^{−γ} are classical (the variance-gamma class); the paper does not claim them.

---

## 7. Exposition and structure (the block's part)

The block is readable on its own. § 4.1 is the clearest statement in the paper of what the axioms are for; § 4.4's "picture in the plane" (p. 33) is the right entry point to the cones and should stay. Where it becomes hard to follow:

- **Table 2 (p. 32)** is set inside § 4.4, two pages after § 4.3 ends, and its (similarities, Loewner) cell is a fourteen-line paragraph of seven citations. A table cell should hold one line and a pointer; the detail belongs in § 4.9. The three cells of the diagonal row read the same way.
- **§ 4.3's glossary** (pp. 29–31) defines exponent cone, exponent spread, shape-blind and dilation ratio only so that the table can use them before §§ 4.6 and 4.9 do. It is honest but long; a journal version could cut the table to the terms of §§ 4.4–4.7 and move the rest of the row descriptions to § 4.9.
- **Forward references that carry weight:** "step set" is used in § 4.3 (p. 29, "the step set of the stable orbit") before Proposition 4.2 defines it; ecc and es are used in Table 2 before Proposition 4.24; Proposition 4.20(1) is cited in § 4.2 for the stable orders lying in the Loewner order. None is load-bearing for a proof, and the bullets of § 4.3 flag the last two.
- **§ 4.2** interrupts itself with the one-parameter-group paragraph and the GL⁺(d) paragraph (p. 28) between the list of groups and Lemma 4.1; both are pointers to Appendices D and G and could be two sentences.
- **§ 4.4** states Theorem 4.3 but keeps Lemma C.1, on which the theorem's idea rests, in Appendix C; a reader who wants to see why majorization is the tool has to go there. Stating clauses (2) and (5) of Lemma C.1 in § 4.4 (without proof) would make the subsection self-contained. Conversely, Theorem 4.3(3), the closed order without a cone, is a remark and could move to the appendix.
- **§ 4.5**'s paragraph after Proposition 4.4 and the one before Proposition 4.5 repeat § 1 and § 3.4; one could go.
- **Appendix B** is where the routine proofs belong, and the proof of Proposition 4.15 can lose a page (§ 3 above).

Where the paper leans on an earlier paper in this block: only on Theorem 2.5 and Lemma 2.6(1) (restated) in § 4.5, and on Lemma 2.9(2) (restated) in Proposition 4.19. The block does not require the earlier papers.

---

## 8. Required changes

1. **p. 67, proof of Proposition 4.10.** Replace "Mt = e^{tB}e^{tBᵀ}" by Mt = Σt^{−1} = e^{tBᵀ}e^{tB}; the relative step of (Σt, I) is the inverse of Σt, and it is this matrix whose least eigenvalue is min|e^{tB}x|². The conclusion stands, the display does not.
2. **pp. 29–32 (§ 4.3, Table 2) and p. 54 (§ 5).** Say at the table which cells are complete descriptions and which are bounds, examples or partial; the abstract promises it and only § 5 delivers it, six pages after the table.
3. **p. 32 (GL(d), stable cell), p. 48 (after Theorem 4.21) and p. 55 (open problem 1).** State that the cell and Theorem 4.21(3)(c) describe laws without a Gaussian part, and either add the sufficient condition for a law with one (N(0, 2bΣ) ∗ an orbit of the cell is in the cell) or say that such laws are not described; drop or qualify "would complete the profile clause", since the converse of Proposition 4.13 does not settle laws with a Gaussian part.
4. **p. 36, "Prior art".** Qualify the sentence that lists "the equality of the order with exp C without a closure" among what is new: for pointed cones it is the Ol'shanskiĭ-semigroup theorem read on PD(d) (cite Lawson 1994); what is new is the majorization proof, the non-pointed case and clause (2). Remove the "not connected" reason, which Proposition D.1 already disposes of.
5. **p. 28 (§ 4.1, last paragraph) and wherever "re-measurement of the original image" is asserted (pp. 37, 38, 54, abstract).** State once that this is the paper's reading of "the increment is not a probability measure", which is what is proved; the paper disclaims statements about computation (§ 5, p. 54), and the sentence as written is one.
6. **p. 27, § 4.1, use 1.** Word "needs a group that carries every shape to every other" as the definition of shape selection the paper adopts, not as a necessity; § 4.9 relies on that definition.
7. **pp. 69–70, Appendix B.3, Proposition 4.24(1).** Give the sketch (five lines) or say in Appendix I that the proof is Proposition H.9(1); "the rest is the proof of Proposition H.9(1)" is a pointer, not a sketch.
8. **p. 27, § 4.1.** Confirm against the pages, and preferably quote, the three descriptions of the practice on which § 4.8 and § 5 rest: Lindeberg–Gårding's step 2 and their reason for rejecting the fixed-volume normalization ([36] p. 396; [37] §§ 6.1–6.2), and Mikolajczyk–Schmid's normalization of the warp ([43] § 3.3, p. 72). I could not check them from this session, and the imaging conclusions of the paper depend on the first.

## Suggestions

1. **pp. 68–69, proof of Proposition 4.15.** Replace the dilation-invariance argument by the observation Λ(ϕ) = ρ({0}) ϕ(0) (dominated convergence), and add the remark that a positive ray increment carries an atom c^{−κ} at the origin, which matches P(Y = 0) = λ^{−2γ} in Proposition 4.4(4).
2. **p. 36, Proposition 4.4(3).** Write "g is not of the form bu, b ≥ 0" for "g is not linear".
3. **p. 35, the majorization paragraph.** Bhatia states (III.21) through partial sums of the largest entries; say "equivalently" rather than "in this form".
4. **p. 34, Proposition 4.2(4).** Note that C(K) is empty unless I ∈ K, so the invariance under c ≥ 0 is about a nonempty C(K).
5. **p. 32, Table 2.** Shorten the (similarities, Loewner) cell and the diagonal row to one line and a pointer each; mark complete cells with a sign.
6. **p. 32, footer of Table 2.** "One linear flow {e^{sB}}, with rotations" is unclear; say "B with a skew part allowed" or drop the phrase.
7. **p. 30, Figure 2(b).** Say which slants the four crosses mark.
8. **p. 28, § 4.2.** Reduce the one-parameter-group and the GL⁺(d) paragraphs to pointers to Appendices G and D.
9. **pp. 34–35, § 4.4.** State Lemma C.1(2) and (5) in the subsection; move Theorem 4.3(3) to Appendix C.
10. **p. 37, § 4.5.** Cut one of the two paragraphs that restate the obstruction of § 3.4.
11. **p. 29, Lemma 4.1.** The Horn–Johnson anchors (Thm. 7.7.3(a), Cor. 7.7.4(c),(e)) should be checked against the second edition's numbering by the librarian; the facts are standard either way.
12. **p. 36, "Prior art".** Cite the decomposability-semigroup reading of the step set here as well as in § 4.6, since Theorem 4.3(2)'s tangent cone is Jurek's Lie wedge in the symmetric case.
