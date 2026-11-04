# Referee report, round 2, part A: the front of the paper

Manuscript: *Spatial scale space from hemigroup axioms: rotation-invariant self-decomposable kernels in dimension d*, review build `iso-review-2`, 86 pages.

Part reviewed in detail: abstract; §1 and §1.1; §2 (all restated statements and the cited facts C1–C7); Appendix B; the declarations and the statement on the use of AI. Read for consistency with them: §3, §4, Appendix A (statements, and the proofs as far as the front's claims rest on them), and `lean-axiom-report.txt`. Pages are those printed in the PDF.

What I could reach outside the manuscript: the three earlier papers supplied; the Lean axiom report supplied; Florack, ter Haar Romeny, Koenderink, Viergever 1992 (full text); Burgeth, Didas, Weickert, *The Bessel scale-space* (DSSCV 2005, full text); Pauwels 1998 CWI survey restating the 1995 result; Kühn–Schilling, *A probabilistic proof of Schoenberg's theorem* (for the numbering of C6 in Schilling–Song–Vondraček); the abstracts and bibliographic records of Duits et al. 2004, Koenderink 1984, Wolfe 1978, Lindeberg 2011. I could not open Sato's book, Bingham–Goldie–Teugels, Hazod–Siebert, Florack's book, Lindeberg 2011 or Duits et al. 2004 at the page; where a page reference is reported as "unverified" below it means that and nothing more.

---

## 1. Overall assessment and recommendation

**Recommendation for the front of the paper: minor revision.** The headline claims of the abstract and of §1 are each carried by a numbered statement of §3 or Appendix A, with the qualifications in place, and the few places where the headline is looser than the statement are small and listed in §2 below. The restatements of §2 agree with the line paper, the cone paper and the time-causal paper at the statement numbers given, with one exception that must be fixed (Proposition 2.6 renumbers the clauses of its source). The seven cited facts are stated as the paper uses them, and the departures from the sources that §1.1 announces are the departures I find. Appendix B's inventory and its Table 3 agree with `lean-axiom-report.txt` row by row: 195 distinct declarations, 144 on the logical axioms alone, 51 on one or more of the nine named axioms, none on anything else; the per-statement sets of cited facts in Table 3 are exactly the unions Lean reports. The account of what is machine-checked is clear enough for a reader who has never used a proof assistant, and it is candid to a degree I have rarely seen.

What the front does badly is its relation to the scale-space literature. What it says of the six papers it cites is accurate as far as I could verify it (Florack et al. 1992 verbatim; the Pauwels family; the α-scale spaces), but the manuscript cites fewer scale-space papers than its own line paper does, and it drops precisely the ones a JMIV referee will look for: the Bessel scale space of Burgeth, Didas and Weickert, whose transforms are this paper's Matérn transforms in every dimension; the Poisson scale space of Felsberg and Sommer; Iijima's priority; the "pyramidal" architecture axiom of Alvarez, Guichard, Lions and Morel, which is a hemigroup written in this field thirty years ago; and the time-causal scale-space literature (Koenderink 1988; Lindeberg 2016; Lindeberg and Fagerström 1996), which §2.3 replaces by the author's own paper. These are required changes, not suggestions, because the paper presents itself as a scale-space paper and because the line paper shows the author knows the references. Two further required changes concern the trust base: the repository is private, so a referee cannot run the verification, and the witness and probe declarations that Appendix B describes are absent from the report supplied. The paper is also far too long for a journal; that is a matter for the editor and for the referees of the appendices, and I say in §7 what the front should lose.

---

## 2. The headline claims against what is proved

I checked every sentence of the abstract and of §1 that makes a claim against the statement that carries it. Those that agree are listed briefly; the ones that need attention are developed.

**Abstract (p. 1).**
- "The kernels that take the signal to each scale are the dilations of one rotation-invariant self-decomposable law, with Fourier transform e^{−F(t|ξ|)}, and every such law but the point mass occurs." Theorem 3.6 (p. 16) gives μ̂_{0,t}(ξ) = e^{−F(χ(t)|ξ|)}, so μ_{0,t} is the dilation by χ(t) of the law with exponent F(|·|); Lemma 3.8 (p. 17) gives the converse. "Every such law but the point mass": a rotation-invariant self-decomposable μ ≠ δ_0 has a real radial transform (Lemma 3.4(1)), never vanishing (C4), and −log μ̂ = F(|·|) with F ∈ A_d by Proposition 3.10(2). Correct.
- "Such a kernel with no Gaussian part has a density bounded near its centre exactly when c > d, where c is the power at which the transform falls off." Theorem 3.12(5) (p. 21) with Corollary 3.13(2) (p. 21). The theorem assumes c > 0; for a nontrivial datum with a = 0 that is automatic (k_d ≡ 0 would make the law δ_0). Correct.
- "Otherwise a point source is recorded as a spike, whose growth is computed from the Lévy measure, with its constant." Proposition 3.17 (p. 24), for 0 < c ≤ d. Correct.
- "One F gives a kernel in each dimension that admits it, with the same c." Corollary 3.13(3). Correct.
- "the Matérn functions for γ > d/2, do so for ½ < γ ≤ 1." c = 2γ; bounded on the line iff 2γ > 1, spike in the plane iff 2γ ≤ 2. Correct (Example 3.14, p. 22).
- "Each higher dimension admits strictly fewer F, as an explicit one-parameter family shows." Proposition 3.19(2) and Theorem 3.21(4). Correct.
- "An F that grows like c log r determines a radial characteristic function, and is admitted one dimension up exactly when that function of the radius is a characteristic function there." Proposition 3.18(2)–(3) (pp. 26–27). The abstract omits the hypothesis F ∈ A_d (admitted in dimension d), which clause (2) requires; "an F that grows like c log r" alone does not determine a law. One word fixes it: "An admitted F that grows like c log r".
- "The statements are machine-checked in Lean 4, assuming seven theorems of the literature, except four proved in print: this correspondence with its readings, that family as laws, and a constant's closed form." Matches the second list of §1.1 (Proposition 3.18, Corollary A.9, Proposition A.14, Lemma A.7) and Appendix B. Correct.
- Wording: "The axioms studied here ask only that the stages compose, a hemigroup indexed by two scales, and that rescaling the signal relabels the scales." The axioms also ask linearity, positivity, unit mass, continuity, translation and rotation invariance (Definition 3.1). "Ask of the cascade only that the stages compose" is what is meant.

**§1, "The answers" (p. 3).**
- First answer: as for the abstract. "Each has a radially nonincreasing density" is Proposition 3.15(1). Correct.
- Second answer, "A kernel with a Gaussian part is bounded and smooth in every dimension." Theorem 3.12 is stated for Gaussian coefficient 0. The case a > 0 is argued in one sentence of prose on p. 20 ("since its transform is at most a Gaussian's") and in the bullet on p. 22. The argument is right (|μ̂| ≤ e^{−a|ξ|²/2}, so C1 applies for every n), but it is not a numbered statement, it is not machine-checked, and §1.1 does not list it among what is proved in print only. Either add it as a clause of Theorem 3.12 or name it in §1.1 as prose. As it stands §1.1's "every ... theorem ... that the second list does not name" is machine-checked is true, and the a > 0 sentence falls outside both lists.
- "−log μ̂(ξ)/log|ξ| → c as |ξ| → ∞, with 0 < c ≤ ∞ (Corollary 3.13)": clause (2) with a = 0. Correct.
- "for c > d + N the density is sure to have N continuous derivatives": Theorem 3.12(2). Correct.
- "When c < d the density grows at the centre like |x|^{c−d}, up to a factor that varies more slowly than every power, and when c = d at least like log(1/|x|)": Propositions 3.16 and 3.17. Correct.
- Third answer: A_{d+1} ⊊ A_d is Proposition 3.19(2); A_∞ = S is Proposition 2.6(3) in the paper's numbering (see §3 below for the numbering), reproved as Theorem A.15(3); the Cin rays are Proposition 3.19(3)/Theorem A.16; the test is Proposition 3.18(3); the critical values decreasing like d^{−1/2} is Theorem 3.21(3). All correct. "an exponent of A_d whose Lévy measure there is cut off sharply, with a jump in its profile, is not admitted in dimension d+1": Proposition 3.19(1) needs only a discontinuity of the polar profile anywhere, not a cut-off; the sentence is narrower than the result, which is harmless.
- "In time-causal scale space a kernel is the law of a random delay on [0,∞), and the families are classified in the author's paper [11]." The phrase "time-causal scale space" names a literature (Koenderink 1988; Lindeberg and Fagerström 1996; Fagerström 2005; Lindeberg 2016, 2023), in which kernels are not in general the laws of random delays and which classifies nothing in this sense. What is meant is "in the time-causal theory of the same axioms [11]". Say so, here and in §2.3 (p. 9, "In time-causal scale space a kernel is a law on the half-line").

**§1, "Scope" (pp. 3–4).** Accurate and useful. "The record of a bounded image is bounded for every kernel" is trivially true and worth saying.

**§1, "Relation to scale-space theory" (p. 4).** Checked sentence by sentence:
- "In the scale-space literature isotropy is imposed together with a semigroup in the scale or with a diffusion equation, and the answer is the Gaussian or a kernel with transform e^{−a|ξ|^p}, called stable here when 0 < p ≤ 2." Correct as a summary of the six papers cited; the bound p ≤ 2 is where positivity enters in Pauwels et al.
- Koenderink ([28], p. 365): the derivation of the diffusion equation from causality with a homogeneous isotropic coefficient is the content of that paper; the page is unverified.
- Florack et al. 1992: **verified against the full text.** Isotropy φ(ω) = φ(|ω|) is their (6) on p. 379; the family φ(ω;σ) = exp(ασ^p ω^p) is their (23) on p. 380, the separability condition (24) and its solution (25) are on p. 380, and the text says "The separability requirement fixes p = 2". The sentence is accurate.
- Florack's book (Crux 3.1, p. 54; Assumption 3.1, Paradigm 3.1, p. 57; Result 3.2, p. 61): unverified.
- Lindeberg 2011 (§3.1 and §4.1.1): the conclusion (Gaussian in the isotropic case) is right; the section numbers are unverified; note that the JMIV version and the KTH technical report are numbered differently, and the paper should cite the journal's numbering.
- Pauwels et al.: the family e^{−a|ω|^α t}, α > 0, from recursivity and scale invariance, with rescaling t^{1/α}, is confirmed by Pauwels's own 1998 restatement; the two pages (694, 695) and the treatment of the plane by rotation invariance are unverified but consistent with the paper's structure.
- Duits et al.: α-scale spaces generated by −(−Δ)^α for α ∈ (0,1], the Poisson scale space at α = ½ (pp. 267, 277): consistent with the abstract and with Burgeth et al.'s summary of that paper; pages unverified.
- "Here neither a semigroup, nor separability, nor a differential equation is assumed." Correct.

What this paragraph compares with is accurate. What it omits is the subject of §6 below.

**§1, "Relation to probability" (p. 4).** The classification "in a theorem of Sato on the self-similar processes with independent increments" is Sato 1991 / [38] Thm. 16.1, and the paper says so in Table 2. "In both the action of a dilation on the parameter is prescribed. Here it is a relabelling of the scales that the axioms leave free." That is the right account of what the axioms add. "The proofs given here are written out from the seven cited facts of §2.6": true for the formal development; for the printed proofs it is true except that the printed proof of Theorem 3.6 cites Theorem 2.3 of the line paper, whose proof rests on Bochner's theorem as well (line paper, abstract and §1.1). The formal development avoids Bochner because A_d is *defined* through the existence of the law (p. 17: "the 'if' half of the theorem takes probability measures with the transforms (3.1) as given"). A reader of §1.1 and Appendix B ("the formal proofs of this paper rest on none of them") deserves one sentence saying why the trust base of the classification is smaller here than in the line paper.

**§1, "What the paper contributes" (pp. 4–5).** "The main result is that the rotation-invariant self-decomposable laws on R^d are exactly the kernels from scale zero of the isotropic scale spaces that the axioms define." This is Theorem 3.6 + Lemma 3.8 + Proposition 3.10 as stated, with the qualification "up to a relabelling of the scales" given in the next sentence and the point mass excluded. Correct. Items 1 and 2 are accurate summaries of §3.3 and §3.4. "For probability theory the paper claims no new result": within the front I find nothing presented as the paper's own that is known; Table 2 (pp. 32–33) is where the attribution is done, and it is careful. The only place where a reader might be misled is p. 11, §2.4, where the classical threshold on the line is credited to Sato's Theorem 28.4 and Remark 28.6 and to Zolotarev and Wolfe, and the unboundedness for c ≤ 1 to Sato–Yamazato: that is the right chain of credit, and I could not verify the page numbers.

**§4 (pp. 29–30).** Consistent with §1; the four limitations are the right ones and are stated with their statement numbers. "The dictionary covers the exponents of logarithmic growth only" is the correct scope of Proposition 3.18.

---

## 3. Mathematical correctness, for the part reviewed

**The restated statements of §2 against the earlier papers.** Every restatement was compared with the source at the number given.

| manuscript | source | agreement |
|---|---|---|
| Def. 2.1 (p. 7) | line paper Def. 3.1 | identical, (A1)–(A8), (ND) |
| Lemma 2.2 (p. 8) | line paper Lemma 4.1 | identical, including the two-clause form (symmetry under (A3)) and the converse |
| (2.1) and its integrability conditions (p. 8) | line paper (2.3), Lemma 2.15 | identical (the line paper writes the variable ω ∈ R; the manuscript r ≥ 0) |
| Theorem 2.3 (p. 8) | line paper Thm. 7.3 | identical, including "F ≢ 0" and the normalisation χ(1) = 1 |
| self-decomposability (2.2) | line paper Def. 2.12, Sato Def. 15.1 | identical (λ ∈ (0,1) against b > 1) |
| "admissible = exponents of symmetric s.d. laws" | line paper Prop. 2.13 | identical; but see the note below |
| Lévy continuity, §2.5 | line paper Prop. 2.8 | identical |
| the dilation-fixed function, §2.5 | line paper Lemma 6.3 | identical |
| Def. 2.4 (p. 9) | cone paper Def. 4.1 | identical |
| delay law, Rem. 4.3; kernels of a time-causal family, proof of Prop. 4.5 | cone paper | as cited |
| Prop. 2.5 (p. 9) | cone paper Lemma 4.2 | identical (a_V = ½ b_0) |
| subordinated slice S | cone paper Prop. 4.6 | identical |
| **Prop. 2.6 (p. 10)** | **cone paper Prop. 4.9** | **clauses renumbered: see below** |
| Prop. 2.7 (p. 10) | cone paper Prop. 3.3 and Lemma 3.1 | identical (Cin rays, superposition, ϖ = −dk) |
| Cor. 2.8 (p. 10) | cone paper Cor. 3.9 | identical ("at γ = ½ it sits at the threshold" dropped, harmless) |
| Matérn member, folded profile 2γe^{−x/θ} | cone paper §5.2, Prop. 4.5(2) | consistent (range 1/√2 gives 2γe^{−√2x}) |
| delay datum, Def. 4.11; Lem. 4.12(3); Rem. 4.10 numerics 12.61, 5.24, 3.21 | cone paper | as cited |
| Student-t, Prop. 3.11(4) | cone paper Prop. 5.10 | identical density and transform |
| evolution equation, [10, Prop. 6.2] (p. 30) | cone paper Prop. 6.2 | as cited |
| time-causal Thm. 7.3, Props. 8.5, 8.8, 8.17 | time-causal paper v1.1.0 | as cited (gamma: k = γe^{−t}; stable: k ∝ t^{−α}; inverse-gamma: self-decomposable) |

**The one defect (required).** Proposition 2.6 is titled "[10, Prop. 4.9]" and the paper says (p. 7) "A restated statement carries its released number in its title, and its proof is at that number." The source's Proposition 4.9 has four clauses: (1) A_1 is the cone and A_{d+1} ⊆ A_d; (2) S ⊆ A_d; (3) A_∞ ⊆ B, with consequences on F' and on lattice-step profiles; (4) A_∞ = S. The manuscript's clause (3) is the source's clause (4); the source's clause (3) is dropped. "Proposition 2.6(3)" is cited at least nine times (pp. 3, 9, 16, 25, 29, 70, 71 and Table 2), and the proof of Theorem A.15 (p. 71) says "The identification A_∞ = S ... is Proposition 2.6(3)". A reader who follows the paper's own rule to the cone paper lands on the wrong clause. Fix: state in the title or the sentence after it "clauses (1), (2) and (4) of [10, Prop. 4.9]; the source's clause (3) is not used".

**A note on Prop. 2.13 of the line paper.** The manuscript cites "[9, Prop. 2.13]" for "the admissible functions are exactly the exponents of the symmetric self-decomposable laws on the line" (p. 8). The line paper itself says of that proposition that it "is stated for orientation: it lies on no proof path" and cites Sato Cor. 15.11 for it. The manuscript's §1.1 does say the fact is "cited from the literature ([9], §1.1)". It would be cleaner to cite Sato Cor. 15.11 directly.

**The cited facts C1–C7 (pp. 11–13) as stated against their use.**
- C1 (Sato Prop. 28.1): used in Theorem 3.12(2) (p. 42) with the integral ∫|μ̂||ξ|^N and in clause (5); and in Lemma A.2's commentary as "the other direction" of Feller's equivalence. The use matches the statement. Table 3 and the report agree (origin_density_smooth, origin_density_bounded_smooth, origin_dichotomy).
- C2 (Sato Thm. 15.10): used in Proposition 3.10 (p. 38, both directions: the forward reading produces λ and k_η, the converse checks the form with λ = σ_{d−1}), and through it everywhere a law is read as a datum. The statement includes "measurable in η and nonincreasing in r" and no restriction on A or γ, which is what the proof of Prop. 3.10 needs (the right-continuous modification is done in print). Matches.
- C3 (Sato Thm. 8.1): (i), (ii), (iii) as used in Prop. 3.10, Thm. 3.21 (p. 74), Thm. A.16 (p. 76), Prop. A.4 (p. 45, "let μ_1 be its law (C3(iii))"). Matches. The split into three axioms is the right granularity, and Table 3 uses it.
- C4 (Sato Prop. 15.5): used once, at the top of Prop. 3.10 (p. 38). Matches.
- C5 (Wolfe 1978 Thm. 2): used in Prop. 3.15 (p. 47, "By C5 it is symmetric unimodal"). The manuscript's reading of Wolfe through Kanter's definitions is set out on p. 12 and at the end of the proof of Prop. 3.15 (pp. 47–49, the Borel-ness of W_d). The statement on p. 12 covers every symmetric self-decomposable law; the paper says Wolfe's printed proof covers those with no Gaussian part and names Kanter's Lemma 3.1 and Thm. 3.2 for the rest. That is the honest form, and the formal statement (mixing measure on all probability measures, a.e. a uniform law) is implied by the printed one. Matches.
- C6 (Schoenberg + Bernstein representation): used once, Theorem A.15(3) (p. 72). The composition "SSV Thm. 13.14 and Thm. 3.2, one direction of each, uniqueness dropped" is accurate: Kühn and Schilling (arXiv 1808.00190) cite "[24, Theorem 13.14]" with [24] = Schilling, Song, Vondraček, *Bernstein functions*, 2nd ed. 2012, for exactly the Bochner form (positive definite in every dimension ⇒ f Bernstein). The uniqueness that C6 drops is reproved in print as step (b) on p. 73. Page 212 unverified. Matches.
- C7 (BGT Thm. 1.7.1′): the form at the origin, one direction, for the distribution function of a finite measure, ℓ slowly varying on all of (0,∞). Used in Prop. 3.16 (p. 53, through the Gaussian average M(λ) read as a Laplace transform of the mass of balls). The paper's account of the departure from the book (p. 13) is accurate as far as I recall the book. Matches.

**Appendix B against the Lean report, row by row.** I parsed the inventory (pp. 77–78) and the report by script (`out/A/check_inventory.py`). Results:
- The inventory names 198 declarations, 195 distinct; the three under two statements are `polarProfileOf` (Def. 3.9, Def. 3.20), `OriginDatum.polar_decomposition` (Def. 3.9, Lemma A.1) and `measurable_gaussVar` (Prop. 3.11, Thm. 3.12). The report has exactly these 195 names, no more, no fewer. The counts 144 / 51 / none other (p. 79) are correct.
- No declaration depends on an axiom outside `propext`, `Classical.choice`, `Quot.sound` and the nine names on p. 79. Every one of the nine is used by at least one declaration (`schoenberg_radial_bernstein` by `filtration_top` only; `density_of_integrable_charFun` by three).
- Table 3 (p. 79) agrees with the report for every row, at the clause level where the table gives clauses: Thm. 3.6/Cor. 3.7: C3(ii),(iii); Prop. 3.10: C2, C3(i–iii), C4; Thm. 3.12: C1 in `origin_density_smooth`, `origin_density_bounded_smooth`, `origin_dichotomy` (clauses 2 and 5), nothing in clauses 1, 3, 4; Prop. 3.15: C5 + C3(ii),(iii) in `radial_monotone_family`, C5 + C2 + C3(iii) in `radial_monotone_law`; Prop. A.4: C3(iii); Prop. A.5: `origin_upper_bound`, `origin_upper_bound_of_heat` on nothing, `origin_density_lower`/`_log_order`/`_ball_log_order` on C3(iii), `origin_density_upper`/`_order` on C2, C3(iii), C5; Props. 3.16 and 3.17: C7 in every rate declaration, C2, C3(iii), C5 added only in `origin_rate`, `origin_rate_critical`, `origin_rate_profile`, `origin_rate_profile_critical` (the forms with the density's existence); Prop. 3.19: C2, C3, C4; Thm. 3.21: C2, C3, C4 in the membership and strictness declarations, nothing in `criticalValues_strictAnti`, `criticalValues_tendsto`, `criticalValues_existsUnique_window` (clauses 2, 3); Thm. A.15: C2, C3, C4, and C6 in `filtration_top` only; Thm. A.16: C2, C3, C4 in `no_cin_ray_in_the_plane`, nothing in `cin_ray_scaled`; every other listed statement on nothing. The eight reports printed on pp. 80–81 are verbatim those of the file.
- For the four print-only statements Table 3 says Prop. 3.18 and Cor. A.9: C2, C3, C4; Prop. A.14: C2, C3, C4 in clause (3); Lemma A.7: none. I read the printed proofs (pp. 60–64, 74–75, 57–59): Prop. 3.18 uses Prop. 3.10, Cor. 3.13 and Lemma A.3 and nothing else; Cor. A.9 uses Props. 3.18 and 3.19; Prop. A.14(3) uses Prop. 3.10(2) and Thm. 3.21(1); Lemma A.7 is calculus. The rows are right.

**What the report cannot confirm (required).** Appendix B, "Formal examples" (p. 80), describes declarations in `Witnesses.lean` (`witness_isotropic_classification`, ..., `witness_no_cin_ray`, said to rest on no cited fact) and in `Probes.lean` (`threshold_three_lt`, "rests on no cited fact"; `probe_witness_four`, "rests on C2, C3 and C4"). None of these appears in `lean-axiom-report.txt`, which covers the 195 inventory declarations only. The claims about them are therefore unverified by the material given to the referee. Either add their reports to the file or say in Appendix B that the report file covers the inventory and not the examples.

---

## 4. The worked examples and figures

Not my part. Nothing in the front contradicts what §3.3–3.4 compute, and the front's use of the numbers (c = 3/2 for γ = 3/4; w_2 ≈ 5.24, w_3 ≈ 3.21; "w = 4 ... admitted on the line and in the plane and not in space") is consistent with Figure 2 and with the cone paper's Remark 4.10, where the same three values are reported (there under the letter c). The statement in §1.1 that the admission of F^{(4)} on the line and in the plane rests on the computed value w_2, and only w_3 < 4 is in Lean, is consistent with Appendix B.

---

## 5. The trust base

**Is the account clear, complete and honest?** Yes, with the gaps below.

- *Clear.* A reader who has never used a proof assistant learns from §1.1 (pp. 5–7): which statements have formal counterparts (all of §3 and Appendix A but four, named); what Lean checked (that each follows from the formal definitions, Lean's three logical axioms, and seven named theorems taken without proof); that the agreement between the formal and the printed statements is a reading by AI agents and not a machine check; which three cited facts depart from their sources and how; that the examples, figures and constants are computed, not checked; that five statements are formalised in a form about transforms and need no law to exist; and that one example's numbers (w_2) are outside Lean. The two lists on p. 5 are the right device. The sentence "A definition is listed as machine-checked when it has a formal counterpart" (p. 5) clashes with Appendix B, which lists definitions as "formalised in Lean" and only proved statements as "machine-checked"; use Appendix B's two words in §1.1 too.
- *Complete.* Three omissions. (i) The a > 0 case of boundedness and smoothness (p. 20) is proved in one printed sentence and is in neither list (see §2). (ii) The witness and probe declarations are described but not reported (see §3). (iii) §1.1 does not say that the formal classification rests on fewer cited facts than the line paper's because A_d is defined through the existence of the law (see §2, "Relation to probability"). None of these makes the account dishonest; all three make it incomplete at points where a careful reader will stop.
- *Honest.* The departures of C5, C6 and C7 from their sources are disclosed, and I find them accurately described. The sentences "the review is a reading, not a machine check" (p. 6) and "Beyond me, no human has reviewed the paper" (p. 82) are the right things to say. Nothing is said or implied to be verified that the report does not support, with the exception of the witness/probe declarations above, which the report neither supports nor contradicts.

**The report against the paper.** As in §3: every row of the inventory and of Table 3 agrees with `lean-axiom-report.txt`; no declaration depends on an assumption outside the nine named; the 195/144/51 counts are right.

**Access.** Appendix B and the Data and code availability statement say the repository is private until release and that a verification export is deposited "with each released version". The submitted version is not released, so a referee cannot run `lake build`, cannot read the formal statements, and cannot check the AI review's claim that each printed statement "says what its formal counterpart says, or less". For a paper whose trust base is the formal development this is not acceptable at submission: the verification export (development, ledger, blueprint sources, scripts) must be made available to the referees, by an anonymous deposit or a reviewer link. Required.

**The statement on the use of AI (pp. 81–82).** It discloses that the prose, statements, proofs, code and the formal development are the agents' work, that no human other than the author has reviewed the paper, and that the author takes responsibility. This meets the disclosure requirement of the Springer/JMIV policy as I understand it (AI not an author; use disclosed; responsibility with the human author). The quantitative claim ("between twenty-two and forty-six to one") is not checkable by a referee and need not be in the paper; the pointer to `notes/PROCESS.md` in a private repository is not a reference a reader can follow. Suggest shortening to the disclosure and the responsibility sentence.

**Declarations.** "No data were generated or analysed" is right for a theoretical paper; the competing-interests and funding statements are in order.

---

## 6. Sources and relation to prior work

**The Sources table (pp. 32–33)** was read for consistency with the front; it attributes the threshold on R^d (Knopova–Schilling; Grzywny–Ryznar–Trojan), the rate (Leonenko; Leonenko–Olenko; Soni–Soni; Bingham–Inoue), the shape (Watanabe), the dictionary (Jurek–Vervaat; Sato–Yamazato; Wolfe 1982), the radial classes (Schoenberg; Gneiting), and the step/radius facts (Cambanis–Huang–Simons; Fang–Kotz–Ng; Daley–Porcu). The attributions I could check (Schoenberg 1938; Gneiting 1999, strictness; Burgeth et al.; Kühn–Schilling for C6) are right. I did not find a closer or earlier source for the threshold c > d in the gap d/2 < c ≤ d that the paper fills; the paper's own account of Knopova–Schilling (bounded for c > d, unbounded for c ≤ d/2) is what the table says.

**Relation to scale-space theory in §1 (p. 4).** What is said of Koenderink, Florack et al., Florack's book, Lindeberg, Pauwels et al. and Duits et al. is accurate as far as reached (Florack et al. 1992 verified verbatim; the Pauwels family and the α-scale-space range verified through secondary sources; the rest consistent with the literature as I know it). What is missing is the problem, and it is a required change because the manuscript's own line paper (§1, "Relation to the scale-space axiomatics") already has most of it and the manuscript silently dropped it:

1. **The Bessel scale space** (Burgeth, Didas, Weickert, DSSCV 2005, LNCS 3753, pp. 84–95). Its kernel is defined, in every dimension n, by the transform (1 + 4π²|k|²)^{−t/2}; that is this paper's Matérn transform (1 + |ξ|²/2)^{−γ} with γ = t/2 as the scale parameter and the range fixed. The line paper says exactly this ("compose the same transforms into their Bessel scale space by varying the smoothness at fixed range ...; here the cascade parameter is the range, at fixed smoothness"). The present paper introduces the Matérn kernels on p. 2, calls them "the Bessel kernel of potential theory" on pp. 2 and 22, devotes Example 3.14 and Figure 1 to them, and never mentions that the same transforms are a known scale space in this journal's literature. The comparison is also mathematically pointed: in the Bessel scale space the parameter t moves c = 2γ = t through the threshold d, so the kernel's behaviour at its centre changes with scale, whereas in the present family c is fixed and the stages are dilations. This belongs on p. 4 and in Example 3.14.
2. **The Poisson scale space** (Felsberg and Sommer, JMIV 21, 2004; Felsberg and Sommer 2001). The paper names "the Poisson kernel of scale space" on p. 9 and cites only Duits et al. for it. The line and cone papers cite Felsberg and Sommer; this one should.
3. **Iijima** (Iijima 1962; Weickert, Ishikawa, Imiya 1999). The Pauwels family was derived by Iijima, as Pauwels's own 1998 survey says and as the line paper says. A JMIV paper on the axiomatics should say so.
4. **Alvarez, Guichard, Lions, Morel 1993** (ARMA 123). Their architectural axiom is the "pyramidal structure" T_{t+h} = T_{t+h,t} ∘ T_t with transition operators T_{t+h,t}: a two-parameter composition law, which is a hemigroup in the vocabulary of this paper, written in the scale-space literature thirty years ago. The paper's claim that the hemigroup "is what separates this class from the semigroup axioms" (p. 8) needs this precedent and a sentence on the difference (their further axioms, linearity not assumed, and the evolution equation they derive). The line and time-causal papers cite it; this one does not.
5. **Time-causal scale space.** §1 (p. 3) and §2.3 (p. 9) use "time-causal scale space" as if it were the author's [11] alone. Koenderink's *Scale-time* (1988), Lindeberg and Fagerström (1996), Fagerström (2005), Lindeberg (JMIV 2016; and the 2023 scale-covariant time-causal papers) are the literature of that name, and the cone and time-causal papers cite them. Cite them and rephrase (see §2).
6. **Relativistic scale spaces** (Burgeth, Didas, Weickert, Scale Space 2005): kernels in K-Bessel functions, non-exponential transforms; cited in the cone paper. Optional here, but it is the other known non-Gaussian family with Bessel kernels.
7. **Recursive and first-order smoothing filters** and the **temporal/time-causal** cascades of first-order integrators (Lindeberg 2016) are the implementation side of the Matérn members of integer index that the cone paper treats; one sentence pointing there would help the imaging reader, since this paper has "no discretization, no implementation".

Scale-space axiomatics without a semigroup: Alvarez et al. (item 4) is the one to name; Pauwels et al. and Duits et al. keep it; Lindeberg 2011 keeps it. The paper's statement that the semigroup is kept everywhere in the literature is not wrong for the six papers cited, but it is incomplete without item 4.

**Two bibliographic notes.** (a) Table 2 says three sources are cited in the numbering of a version "that was read, which is not the journal's" (Hokkaido preprint for [3], arXiv for [6] and [31]); for a journal version these should be the published numbers or the note should stay. (b) "[38], Thm. 14.14, p. 86" (p. 2) for the self-decomposability of the stable laws, and "[21], Def. 2.14.16, p. 380 / Thm. 2.14.21, p. 383" for the convolution hemigroup: unverified.

---

## 7. Exposition and structure of the front

- **Page 1** says what the paper shows (the rotation-invariant families the hemigroup axioms allow in R^d) and why it matters (a larger class of apertures; spikes; a family of the line need not exist in the plane). It does this in two paragraphs, and it is good. The abstract, however, is 230 words of which the last half is a list of results stated in a vocabulary (self-decomposable, Lévy measure, radial characteristic function) the abstract does not gloss. A JMIV reader meets "self-decomposable" first in the abstract; one parenthesis ("the law is a contracted copy of itself convolved with an independent remainder") would do.
- **The change of vocabulary** is announced explicitly on p. 2 ("So from here on the paper uses the vocabulary of that theory: a kernel is a law, ... its transform ... the exponent"), with the four terms a scale-space reader needs (law, transform, exponent, self-decomposable), then the Lévy measure and the profile. That is sufficient; "gauge", "canonical gauge" and "residual" are defined in §2.2 before use, "subordination" in §2.3, "slowly varying" and "regularly varying" on p. 13 and p. 22. Two terms are used before they are defined: "radial characteristic function" (p. 3, defined p. 26) and "Cin ray" (named p. 10, used p. 3 as "elementary exponent", fine). Nothing serious.
- **§1 is six pages.** The three questions, the three answers, the scope and the two "relation" paragraphs are the right skeleton. What could go: the second paragraph of "The answers" repeats the "Second" answer in the designer's voice; the "Plan of the paper" paragraph duplicates the section headings; §1.1's paragraphs "The form of five formal statements", "Outside the formal verification" and "The review of the formal statements" are Appendix B material and should move there, leaving §1.1 at one page with the two lists and the seven facts. The "What is assumed" list (C1–C7) in §1.1 duplicates §2.6; keep the one-line names only.
- **§2 is seven pages** and is the right thing to have, since the paper is meant to be readable alone. §2.4 (the threshold on the line) and §2.5 are well placed. The notation note §2.7 and Table 1 are useful; Table 1 belongs where it is.
- **Appendix B is five pages.** The inventory (pp. 77–78) and Table 3 are what a referee needs; the eight verbatim Lean reports (pp. 80–81) are redundant with the report file and can go to the verification export; "Versions and commands", "The guard of the repository" and "Two standard steps" can be compressed to a paragraph.
- **The 86 pages.** From the front alone a journal version loses about four pages (§1.1 and Appendix B as above). The appendices are for the other referees; my impression is that the proofs of Lemma 3.3 (pp. 33–35), of the Borel-ness of W_d (pp. 48–49) and of Lemma A.11–A.12 (pp. 68–69) are textbook material that could be cited or deposited.
- **Division between main text and appendices.** The notation table and the sources belong in the appendix, as they are. The two bounds (A.4, A.5) are rightly out of the main text. Proposition 3.16's constant R(d,c) and Proposition 3.17's Q, B in the main text are right. I would move Proposition A.6 and Lemma A.7 (the factor K and the constant ϰ_d) into §3.3, since §3.3 uses K, C_k, ϰ_d on p. 24 before the reader has seen their statement; as printed, p. 24 says "The number ϰ_d depends on the dimension alone: ϰ_d = ½(γ_E − ψ(d/2)) − log 2 ... (Lemma A.7)" and the reader has to go to p. 57.

---

## 8. Required changes and suggestions

### Required

1. **p. 10, Proposition 2.6.** Say that it restates clauses (1), (2) and (4) of [10, Prop. 4.9] and that the paper's clause (3) is the source's clause (4); the paper's own rule (p. 7) sends the reader to the wrong clause nine times.
2. **p. 4, "Relation to scale-space theory", and p. 22, Example 3.14.** Cite and compare the Bessel scale space of Burgeth, Didas and Weickert (2005): the same transforms (1 + 4π²|k|²)^{−t/2} in every dimension, composed along the index at fixed range, so that c = t crosses the threshold d with the scale; the line paper already makes the comparison and this paper dropped it.
3. **p. 4 and p. 8.** Cite Alvarez, Guichard, Lions and Morel (1993), whose pyramidal-structure axiom T_{t+h} = T_{t+h,t}T_t is a hemigroup in the scale-space literature, and say how the present axioms differ; the sentence "Axiom (A6) ... is what separates this class from the semigroup axioms" needs the precedent.
4. **p. 3 and p. 9.** Replace "In time-causal scale space a kernel is the law of a random delay" by "In the time-causal theory of the same axioms [11]", and cite the time-causal scale-space literature (Koenderink 1988; Lindeberg and Fagerström 1996; Fagerström 2005; Lindeberg 2016), as the cone and time-causal papers do.
5. **p. 4 and p. 9.** Cite Felsberg and Sommer for the Poisson scale space and Iijima (with Weickert, Ishikawa, Imiya 1999) for the priority on the Pauwels family; both are in the line paper.
6. **p. 80, Appendix B "Formal examples", and p. 79.** The witness and probe declarations are not in `lean-axiom-report.txt`; add their reports or say that the report covers the inventory only. As given, "rests on no cited fact" for `witness_*` and `threshold_three_lt` is unverified.
7. **p. 77 and p. 82.** Make the verification export available to the referees (anonymous deposit or reviewer link); a private repository cannot carry the trust base of a submitted paper.
8. **p. 20 and p. 3.** "A kernel with a Gaussian part is bounded and smooth in every dimension" is proved in one prose sentence and is in neither list of §1.1; add it as a clause of Theorem 3.12 or list it as proved in print.
9. **p. 1, abstract.** "An F that grows like c log r determines a radial characteristic function": add "admitted" (F ∈ A_d), the hypothesis of Proposition 3.18(2).

### Suggestions

1. **p. 1, abstract.** "ask only that the stages compose" → "ask of the cascade only that the stages compose"; gloss "self-decomposable" in one parenthesis.
2. **p. 5, §1.1.** Use Appendix B's words: definitions "formalised in Lean", proved statements "machine-checked"; the sentence "A definition is listed as machine-checked when ..." then goes.
3. **p. 5–7, §1.1.** Move "The form of five formal statements", "Outside the formal verification" and "The review of the formal statements" to Appendix B; keep the two lists and the seven names. Saves a page and a half.
4. **p. 4, "Relation to probability", or p. 17.** One sentence saying why the classification here rests on C3(ii),(iii) alone while the line paper's rests also on Bochner's theorem: A_d is defined through the existence of the law, and Lemma 3.8 builds the family from it.
5. **p. 8.** Cite Sato Cor. 15.11 directly for "the admissible functions are exactly the exponents of the symmetric self-decomposable laws"; the line paper's Prop. 2.13 is itself a citation of it.
6. **p. 24.** Move Proposition A.6 and Lemma A.7 (K, C_k, ϰ_d) into §3.3 before Proposition 3.17, which uses them.
7. **pp. 80–81.** Drop the eight verbatim Lean reports; the file is the record.
8. **p. 82, AI statement.** Keep the disclosure and the responsibility sentence; drop the word-count ratio and the pointer to a private file.
9. **p. 4.** Cite Lindeberg 2011 by the journal's section numbers, and check "[28], p. 365", "[38], Thm. 14.14", "[21], Def. 2.14.16 and Thm. 2.14.21", which I could not verify.
10. **Table 2, p. 33.** For a journal version replace the preprint/arXiv numbering of [3], [6], [31] by the published numbering, or keep the note.

---

### Record of the checks (for the editor)

- `out/A/check_inventory.py`: parses the inventory of pp. 77–78 and `lean-axiom-report.txt`; confirms 195 distinct declarations, 198 names, 144/51, no foreign axiom, and prints the cited facts per statement, which were compared with Table 3 by hand.
- Florack et al. 1992: full text read; (6) on p. 379, (23)–(25) on p. 380, "The separability requirement fixes p = 2" on p. 380.
- Burgeth, Didas, Weickert 2005: full text read; transform (1 + 4π²|k|²)^{−t/2}, kernel in K_{(n−t)/2}, semigroup in t.
- Pauwels 1998 (CWI): restates the 1995 result as transform e^{−a|ω|^α}, α > 0, with rescaling t^{1/α}, from recursivity and scale invariance; credits Iijima.
- Kühn–Schilling 2018: Theorem B (Schoenberg, Bochner form) "proved in [24, Theorem 13.14]", [24] = Schilling, Song, Vondraček, 2nd ed. 2012.
- Line paper v0.1, cone paper v0.1, time-causal paper v1.1.0: every restated statement located at the number cited and compared (table in §3).
