# Referee report, round 2, part D: the dimension as a restriction (§3.4, its proofs in Appendix A.5) and the conclusion (§4)

Manuscript: *Spatial scale space from hemigroup axioms: rotation-invariant self-decomposable kernels in dimension d*, review build `iso-review-2`, 86 pages. Files read: the manuscript, `line-paper.pdf`, `cone-paper.pdf`, `time-causal-paper.pdf`, `lean-axiom-report.txt`. Page numbers are those printed in the PDF. Computations are in `out/D/check_D.py`, `check_D2.py`, `check_D3.py`.

My part: Proposition 3.18 (the dictionary, print only) with its proof (pp. 60–62); Lemma A.8 (the shadow) with its proof (pp. 62–63); Proposition 3.19 with its proof (pp. 63–64); Corollary A.9 (print only, p. 64); Definition 3.20, Theorem 3.21 and Lemmas A.10–A.13 with their proofs (pp. 65–70, 74); Proposition A.14 (print only, pp. 66, 74–75); Theorems A.15 and A.16 with their proofs (pp. 70–73, 75–76); the main text of §3.4 (pp. 25–29), Figure 2, §4 and §4.1 (pp. 29–30); the rows of Table 2 and Table 3 and the lines of the Lean report that concern these statements.

---

## 1. Overall assessment and recommendation

**Recommendation for this part: minor revision.** I read every proof of §3.4 and Appendix A.5 line by line, recomputed every constant and limit that the text states, and compared the printed clauses with the Lean report. I found no false statement and no proof with a gap that a reader could not close from the page. The four print-only statements that fall in my part (Proposition 3.18, Corollary A.9, Proposition A.14) are correct, and their proofs are complete at the level of detail the paper sets for itself. The numerical claims (the critical values, the limit √d·w_d → √π and how it is approached, the bounds of Lemma A.11, the example w = 4, the shadow of the step, the Matérn exponent through the dictionary) all reproduce. Figure 2 shows what its caption says.

What needs revision is not the mathematics of §3.4 but the account around it. (i) Two of the three open problems of §4.1 are answered by the paper's own objects in a few lines: every stage of a cascade whose kernel has no Gaussian part and a finite c is a compound Poisson law with an atom at the centre of mass (χ(s)/χ(t))^c, and the step datum's exponent *is* the exponent of an infinitely divisible law in the next dimension (invert the shadow formula of Lemma A.8, an Abel transform; I verified the construction numerically in d = 1 and d = 2). A paper must not list as open what it can settle from its own definitions. (ii) Appendix A.5 presents the strictness of the filtration four times (Prop. 3.19(2), Thm. 3.21(4), Thm. A.15(1), Thm. A.15(3)) and the Cin-ray exclusion twice (Prop. 3.19(3), Thm. A.16), and the reproof of A_∞ = S through C6 follows the same route as the cone paper's own proof of [10, Prop. 4.9(4)], which the text does not say; Theorem A.15(2) is a remark about a bound of the cone paper that "no other statement of this paper uses". (iii) Corollary A.9(2) is Schoenberg's classical witness Ω_d ∈ Φ_d \ Φ_{d+1} and should be attributed as such, given the paper's own standard that it claims no new result for probability. (iv) The example w = 4 is described in §1.1 and Appendix B as resting on a computed value 4 ≤ w_2, while Table 2 cites the cone paper's Lemma 4.12, which proves k_2^(4) nonincreasing in print; the two accounts disagree and the second is right.

Nothing in my part is circular: Theorem 3.21's proof rests on Lemmas A.10 and A.13 and Proposition 3.10; Proposition 3.19 on Lemma A.8 and Proposition 3.10; Theorem A.15(3)'s nesting cites the cone paper but also proves it in one line; Theorem A.16 is independent of the nesting, as announced.

---

## 2. The headline claims against what is proved (my part)

**Abstract, p. 1.** "Each higher dimension admits strictly fewer F, as an explicit one-parameter family shows." Proved: Theorem 3.21(4), and independently Proposition 3.19(2). "An F that grows like c log r determines a radial characteristic function, and is admitted one dimension up exactly when that function of the radius is a characteristic function there." Proved as Proposition 3.18(2)–(3), **but with a qualification missing**: F must already belong to A_d. An F of logarithmic growth that is not admitted in dimension d determines nothing (clause (2) starts from F ∈ A_d). Write "An F admitted in dimension d that grows like c log r…".

**§1, the third answer, p. 3.** Every sentence has a carrying statement: nesting (Prop. 2.6), strictness (Prop. 3.19), the remaining exponents (Prop. 2.6(3)), the Cin rays (Prop. 3.19(3)/Thm. A.16), the jump test (Prop. 3.19(1)), the dictionary (Prop. 3.18), the family with critical values "that decrease like d^{-1/2}" (Lemma A.11, not Theorem 3.21(3) as cited; the theorem gives the limit, the lemma the order; harmless but the citation could name both).

**§3.4, p. 27, first paragraph after Proposition 3.18.** "So an exponent of logarithmic growth is in A_d exactly when r ↦ 1 − rF′(r)/c is a radial characteristic function on R^d, of a law with no atom at the origin and a finite logarithmic moment." This reads more than the proposition proves. Clause (2) gives the direction A_d ⇒ φ is such a function. The converse direction, as worded, presupposes that F is differentiable and that F(r) = c∫_0^r (1−φ(u)) du/u, which is not part of "an exponent of logarithmic growth". The exact statement is the bijection of clause (2): F ∈ A_d with logarithmic growth c if and only if F = c∫_0^r(1−φ)du/u for a radial characteristic function φ of such a law. Reword.

**§3.4, p. 29, the paragraph "As laws the members of the family are ordinary kernels in every dimension."** Accurate and important for imaging: it says what "not admitted" means (the filter exists; what is lost is the cascade). I would make the same point for the Cin rays, where the text (p. 28) says only that a Cin ray "is the exponent of no isotropic family in the plane or in any higher dimension". The filter e^{−b Cin(τ|ξ|)} is nevertheless a probability kernel in the plane and in space (§4 below, finding on the third open problem); a user who builds a filter from a Cin transfer function loses the stages, not the filter.

**§4, p. 30.** "An exponent whose polar profile in dimension d has a jump is not admitted in dimension d+1 (Proposition 3.19), and an exponent of logarithmic growth is admitted there exactly when a radial characteristic function on R^d is still one on R^{d+1} (Proposition 3.18)." Correct, with the same implicit "admitted in dimension d" (vacuous otherwise, since A_{d+1} ⊆ A_d). "The test in dimension d is on the Lévy measure, whose polar profile must be nonincreasing (Proposition 3.10)." Correct.

**"For probability theory the paper claims no new result" (p. 5).** Against my part: Proposition 3.19(1)–(2) and Theorem 3.21 are, as far as I can find, not in the literature (the cone paper has d = 1, 2 and numerics; the literature on Schoenberg's classes Φ_d treats the infinitely-divisible-in-every-dimension side, not the self-decomposable filtration). They are small results, but they are results about self-decomposable laws on R^d, and the sentence undersells them; "claims no new result" is not the same as "is not new". Conversely, Corollary A.9(2) — ζ ↦ Ω_d(τ|ζ|) is not a characteristic function on R^{d+1} — *is* known: it is Schoenberg's witness for Φ_{d+1} ⊊ Φ_d (Schoenberg 1938; a direct proof in Golinskii, Malamud and Oridoroga, Trans. AMS 370 (2018), who show Ω_n ∈ Φ_n \ Φ_{n+1}). The corollary derives it from the dictionary, which is a nice reading, but the statement must name its classical source; Table 2 cites Gneiting [17] only for the strictness in general.

---

## 3. Mathematical correctness, statement by statement

### Proposition 3.18 (pp. 26–27; proof pp. 60–62). Print only; closest reading.

*Preamble (p. 60–61).* Ω_d well defined and independent of e by O(d)-invariance of σ_{d−1}; Ω_1 = cos; (A.15) by the symmetry θ ↦ −θ. The reduction E e^{i⟨ξ,X⟩} = E Ω_d(|ξ||X|) by averaging over θ and exchanging a bounded continuous integrand: correct. X has the law of RU by (A.15) and Fubini: correct.

*Step A, (A.16).* The substitution r = vR/ρ inside E∫_0^R and two uses of Tonelli: correct (I rechecked the change of variable; dr/r is invariant). (A.17) by polar coordinates and (A.15): correct.

*Step B.* ∫_1^∞ k dr/r = c E log^+ R and ∫_0^1 k r dr ≤ c/2: correct.

*Step C.* The datum (0, 1_{(0,1)}) has exponent H_d(|ξ|) by (A.17)+(A.16) with R ≡ 1: correct. Lemma A.3(1) (p. 40) with c = 1, C_k = 0 gives H_d(s) ≤ log s + 13/4 for s ≥ 1; Corollary 3.13(2) gives H_d(s)/log s → 1. The two-sided bound ½E log^+R − ½log s_0 ≤ E H_d(R) ≤ E log^+R + 13/4: correct (I rechecked the lower bound: H_d ≥ 0 and H_d(R) ≥ ½log R on {R ≥ s_0}). So the equivalence of clause (1) holds.

*Clause (1).* k_d = c Pr(|X| > ·) is nonincreasing, in [0, c], k_d(0+) = c because Pr(X = 0) = 0; the two integrability conditions by Step B; exponent c∫_0^{|ξ|}(1−φ)dv/v by (A.17)+(A.16); F ∈ A_d by Proposition 3.10(2); F(r)/log r → c by Corollary 3.13(2). Correct.

*Clause (2), existence.* a = 0 from Corollary 3.13(1) and the finite logarithmic limit; k_d(0+) = c from 3.13(2); the right-continuous modification G = k_d(·+)/c is a survival function with G(0+) = 1 and G(∞) = 0, so R exists with values in (0, ∞); X = RU; E log^+|X| = (1/c)∫_1^∞ k_d dr/r; F(ρ) = c∫_0^ρ(1−φ)dv/v by (A.17) and (A.16) (the latter applied to k = cPr(R > ·), which equals k_d off a countable set, so (A.17) is unchanged). Continuous differentiability from the continuity of φ. Correct. The claim "Pr(|X| > r) = k_d(r+)/c for every datum with that exponent" is justified because the datum was arbitrary and Proposition 3.10(1) makes k_d unique a.e., which fixes the right limits.

*Clause (2), uniqueness and the bijection.* c_1 = c from the logarithmic limit; φ_1 = φ on (0,∞) by differentiating the two integral representations (both integrands continuous), and at 0; the law of X by the preamble. The identification of the image with {F ∈ A_d : a = 0, k_d(0+) ∈ (0,∞)} uses Corollary 3.13(2) in both directions. Correct.

*Clause (3), if.* Rotation invariance of X′ from the radial characteristic function; ΠX′ has the law of X because the characteristic function of ΠX′ at ξ is that of X′ at (ξ, 0); Pr(X′ = 0) ≤ Pr(ΠX′ = 0) = 0; radial function of X′ is φ by the preamble in dimension d+1; clause (1) in dimension d+1 gives E log^+|X′| < ∞ (since ∫_0^1(1−φ)du/u = F(1)/c < ∞) and F ∈ A_{d+1}. Correct.

*Clause (3), only if.* Clause (1) in dimension d gives the logarithmic growth; clause (2) in dimension d+1 gives X′ with radial function 1 − rF′(r)/c, which clause (2) in dimension d identifies with φ. Correct.

**Verdict: the proof proves the printed statement.** One wording point: in clause (3) the statement says "Every such X′ is rotation invariant" — "such" means with characteristic function φ(|ζ|), fine.

### Lemma A.8 (p. 60; proof pp. 62–63). Machine-checked, but read in full.

The normalisation C_d ∫(1+u²)^{−(d+1)/2}du = 1 is proved by the elegant trick h = 1_{(1,2)} in (A.18), both sides being log 2 — correct, and I confirmed C_d = Γ((d+1)/2)/(√π Γ(d/2)) numerically for d = 1..4. Derivation of (A.18): the inner integral over y with y = ru gives (|S^d| r^{d})^{−1}·k̄(r)/C_d = k̄(r)/(|S^{d−1}| r^d) since C_d|S^d| = |S^{d−1}|: correct. Clause (2): monotone because each k′(r√(1+u²)) is; continuity by dominated convergence, with the dominating function k′((r_0/2)√(1+u²))(1+u²)^{−(d+1)/2} ≤ k′(r_0/2)(1+u²)^{−(d+1)/2}, which is integrable because Definition 3.9 makes k′ finite-valued: correct; the countable exceptional set (two u per discontinuity) is handled. k̄(0+) = k′(0+) by monotone convergence: correct. Clause (3): the image measure, the null line {Πz = 0} (needs d+1 ≥ 2, stated), the integrability transfer through |Πz| ≤ |z| and the monotone function |x|² ∧ 1, the exponent at (ξ, 0): all correct.

### Proposition 3.19 (p. 27; proof pp. 63–64). Machine-checked.

Clause (1): Lemma A.8 ⇒ (a′, k̄) is a datum in dimension d with exponent F(|ξ|) ⇒ F ∈ A_d (Prop. 3.10); uniqueness a.e. (Prop. 3.10(1)) plus continuity of k̄ and monotonicity of k_d give equality everywhere by the squeeze r_n ↓ r, s_n ↑ r on the conull set: correct. Clause (2): the step datum satisfies Definition 3.9 (∫_0^1 ≤ b/2, ∫_1^∞ = b log^+τ); radiality of the exponent by substitution; the jump at τ; A_{d+1} ⊆ A_d from clause (1): correct. Clause (3): at d = 1 the exponent of (0, b1_{(0,τ)}) is b Cin(τ|ω|) by (3.2) with |S^0| = 2 — correct; then clause (2) and nesting. Correct.

### Corollary A.9 (p. 64). Print only.

Clause (1): the datum (0, c Pr(|X| > ·)) of 3.18(1) has a continuous profile by 3.19(1), so Pr(|X| = r) = jump/c = 0. Correct. Clause (2): X = τU satisfies the hypotheses of 3.18(1) with c = b; the profile is b1_{(0,τ)}; so G is the function of 3.19(2), G ∉ A_{d+1}, and 3.18(3) turns that into "Ω_d(τ|ζ|) is not a characteristic function on R^{d+1}". Correct — and classical (see §2 and §6).

### Definition 3.20 and Lemma A.10 (pp. 28, 65; proof pp. 66–68). Machine-checked.

I rederived (A.19) from (3.4): the power term gives 2^{3/2}Γ(m)/(Γ(d/2) r), the bump term 2w[P(d/2, r²/2) − P(d/2, r²/4)]; checked against a direct quadrature of (3.4) at d = 3, w = 4, r = 1.5 (4.1186959918 both). The derivative, the substitution z = r²/2 and the criterion (A.20): correct (2^{3/2}/(4√2) = ½). The supremum: h_d > 0 exactly on (0, d log 2), h_d → 0 at both ends, so attained: correct. The first-order condition m(1−q) = z*(1−q/2) with q = λ_d e^{z*/2} ∈ (0,1): correct. The next-dimension test h_{d+1}(z*) = √m M_d (1−q/√2)/√((1−q)(1−q/2)) and the inequality (1−q/√2)² − (1−q)(1−q/2) = (3/2 − √2)q > 0: correct. The Gamma factor by log-convexity, Γ(m+½) ≤ √m Γ(m): correct. Hence w_{d+1} < w_d. The lemma is proved.

The paragraph after the proof (p. 68) says 3/2 − √2 is the reciprocal of 6+4√2, the cone paper's bound, and "This paper does not explain the coincidence." It is not a coincidence that needs a paper: both numbers are (1 − 2^{−1/2})², the cone paper's from λ_1 = 2^{−1/2} at d = 1 ([10], p. 82, "(1 − 2^{−1/2})²/2"), this paper's from λ_{d+1}/λ_d = 2^{−1/2}. Either say this in one sentence or drop the paragraph.

### Lemma A.11 (p. 65; proof pp. 68–69). Machine-checked.

Γ(m) = m^m e^{−m} I_m with I_m = ∫_{−1}^∞ e^{−mφ(u)}du: correct. The four comparisons for φ(u) = u − log(1+u): on (−1, 0] φ ≥ u²/2 (φ′(s) ≤ s there); on [0,∞) φ ≥ ψ := u²/(2(1+u)) (ψ′ = (s²+2s)/(2(1+s)²) ≤ s/(1+s)); ψ ≥ u²/4 on [0,1], ≥ u/4 on [1,∞); φ ≤ u²/2 on [0,∞): all correct. I_m ≤ √(π/2m) + √(π/m) + (4/m)e^{−m/4} ≤ K/√m with K = √(π/2) + √π + 4 (using 4/m ≤ 4/√m): correct. I_m ≥ e^{−1/2}/√m: correct. M_d ≤ m^m e^{−m} (since h_d(z) < z^m e^{−z}) gives the lower bound on w_d; M_d ≥ h_d(m) = m^m e^{−m}(1 − ε_d) with ε_d = 2^{−d/2}e^{m/2} = e^{1/4}(e/4)^{d/4} gives the upper bound when ε_d < 1. Correct. Numerically ε_1 = 1.166, ε_2 = 1.059, ε_3 = 0.961, so the upper bound exists from d = 3 on, as the main text (p. 29) and the Figure 2 caption say; the bounds hold at every d I checked (e.g. d = 3: 0.214 ≤ 3.206 ≤ 63.8; d = 20: 0.094 ≤ 0.460 ≤ 1.33).

### Lemma A.12 (p. 65; proof p. 69). Machine-checked.

S_m = √m I_m; the pointwise limit of f_m(v) = e^{−mφ(v/√m)} to e^{−v²/2} through |φ(u) − u²/2| ≤ |u|³/(3(1−|u|)); the domination by e^{−v²/4} + e^{−|v|/4} from the three comparisons: correct. Clause (2) restates the bounds of A.11 in terms of S_m: correct. Clause (3): √m w_d → √(2π)/2 = √(π/2), then √d w_d = √(d/m)·√m w_d → √2·√(π/2) = √π: correct.

### Lemma A.13 (p. 66; proof pp. 69–70). Machine-checked.

The identity f(x) = k_d(r)/(|S^{d−1}| r^d) through u = r²/2v, the finiteness of k_d(r) (the bound on g_u(x)/u on (0,1] and g_u ≤ (2π)^{−d/2} on [1,∞)), the Lévy integrability ∫(|x|²∧1)f ≤ d∫_0^1 k_I du + ∫_1^∞ k_I du/u: all correct. It is the cone paper's computation [10, App. A, "What the bridge computation reads"] with monotonicity dropped, and the text says so.

### Theorem 3.21 (p. 28; proof p. 74). Machine-checked.

Clause (1), w ≤ w_D: Lemma A.13 + Lemma A.10 + Proposition 3.10(2): correct. Clause (1), w > w_D: Proposition 3.10(1) gives a datum (a, k_D); the measure ν′ with density k_D^(w)(|x|)/(|S^{D−1}||x|^D) is a Lévy measure by A.13; both triplets (0, ν′, 0) and (aI, ν_D, 0) have the transform e^{−F^(w)(|ξ|)} because both Lévy measures are symmetric (so the compensator term integrates to zero — correct and stated); C3(ii) gives a = 0 and ν′ = ν_D; the radial densities agree a.e.; then the strictly increasing stretch of k_D^(w) near r_0 = √(2z*) contradicts a.e. agreement with a nonincreasing function (the u_n ↓ r, v_n ↑ s argument): correct. Clauses (2)–(4): correct consequences of A.10–A.12.

### Proposition A.14 (p. 66; proof pp. 74–75). Print only; closest reading.

Clause (1): the integration by parts of ∫_0^∞(1−e^{−σu})u^{−3/2}du = 2σΓ(½)σ^{−1/2} = 2√(πσ), with the boundary term vanishing at both ends (at 0 like u^{1/2}): correct. F^(w)(r) = √(2π) r + w∫_1^2(1−e^{−ur²/2})du/u: correct.

Clause (2): (A.21) by the x ↦ β/x symmetrisation: correct (standard). E e^{−σκ/Z_0²} = e^{−√(2σκ)}: I rederived the substitution z = √2 x, β² = σκ/2, and (A.21): correct; at κ = 2π it is e^{−2√(πσ)}. The compound Poisson sum: E exp(−σΣU_j) = exp[−w log 2 (1 − E e^{−σU_1})] = exp[−w∫_1^2(1−e^{−σu})du/u] because the U_j have density 1/(u log 2) on [1,2]: correct. W ≥ 2π/Z_0² > 0 a.s. The mixture √W Z has characteristic function e^{−F_I(|ξ|²/2)} = e^{−F^(w)(|ξ|)}: correct. The factorisation into the rotation-invariant Cauchy law (transform e^{−√(2π)|ξ|}, the mixture against the ½-stable summand 2π/Z_0²) and the compound Poisson law (the mixture against ΣU_j, equivalently Σ_{j≤N}√U_j Z_j): correct. Infinite divisibility by the n-th root construction W_n = 2π/(n²Z_0²) + Σ_{j≤N_n}U_j with N_n ~ Poisson((w log 2)/n): E e^{−σW_n} = e^{−F_I(σ)/n}: correct (this is also immediate from Bochner subordination of an infinitely divisible mixing law, but the explicit root is fine).

Clause (3): F^(w) ∈ A_D ⇔ μ_D^(w) self-decomposable, the admissibility half supplied by Proposition 3.10(2); then Theorem 3.21(1) and (4). Correct, including the case w > w_1: infinitely divisible in every dimension and self-decomposable in none.

**Verdict: the proposition is correct and its proof complete.**

### Theorem A.15 (p. 70; proof pp. 70–73). Machine-checked.

Clause (2) (p. 70): 2M_2w_2 = Γ(3/2) < 1; M_2 > 1/15 by evaluation at z = ½ with the stated rational bounds on e^{−1/2}, e^{−1/4}, 2^{−3/2}: all correct (M_2 = 0.0845, 1/15 = 0.0667). w_2 < 7.5 < 6+4√2 = 11.66; w_1 = 12.61 > 6+4√2, so at d = 1 the set is (w_2, 6+4√2]: correct. Clause (1) (pp. 70–71): the same proof as Theorem 3.21(1), repeated verbatim. Clause (3), nesting: a one-line proof from the projection (the residuals project) is given, though the clause cites Proposition 2.6(1): correct either way; strictness from (1)–(2): correct.

Clause (3), A_∞ = S through C6 (pp. 71–73). S ⊆ A_∞: Proposition 2.5, the monotonicity of (3.4) in r when k_I is nonincreasing, Lemma A.13, Proposition 3.10(1): correct. A_∞ ⊆ S: for each d, the datum (a_d, k_d); (c·)_*ν_d ≤ ν_d because k_d is nonincreasing (I rechecked the density of the image, k_d(|y|/c)/(|S||y|^d)); step (a) makes η ↦ F(|η|) and η ↦ F(|η|) − F(c|η|) negative definite on R^d; dilation by √2 keeps that; continuity; the d = 0 case; f ≥ 0 and g_c ≥ 0 from C6's inequality with n = 1 (a neat derivation, which also disposes of the need to know that F is nondecreasing); C6 gives representations of f and g_c; a = a_c = 0 from the limit at 0; the identity f = f(c²·) + g_c and step (b) give D_{c²}m + m_c = m, so D_λ m ≤ m for λ ∈ (0,1]; ∫(1∧t²)m ≤ ∫(1∧t)m; step (c) gives m(dt) = k(t)t^{−1}dt with k nonincreasing; the two integrability conditions of Definition 2.4 from ∫(1∧t)m < ∞. Correct.

Step (a) (pp. 72–73): the identity Σa_ja_k(ψ(η_j)+ψ(η_k)−ψ(η_j−η_k)) = 2α|Σa_jη_j|² + ∫P_a dL, with P_a = (Σa_j(1−cos θ_j))² + (Σa_j sin θ_j)² ≥ 0, and the subtraction for (α′, L′) ≤ (α, L); the complex case by K_{jk} real symmetric: correct. Step (b) (p. 73): the three-point identity (1−e^{−σt}) + (1−e^{−(σ+2)t}) + e^{−σt}(1−e^{−t})² = 2(1−e^{−(σ+1)t}) (I expanded it: correct), the finite measure n(dt) = (1−e^{−t})²m(dt) determined by its Laplace transform at the integers through moments on [0,1]: correct. Step (c) (p. 73): the image under log, the shift property, φ(θ) = sup_n 2^n m̃((θ, θ+2^{−n}]) nondecreasing in n by halving, the squeeze by monotone convergence, finiteness from the finite rays: correct.

**But**: this route — self-decomposability in every dimension ⇒ negative definite in every dimension ⇒ Bernstein by Schoenberg ⇒ the mixing law's Lévy measure decreases under dilation ⇒ its density is k(t)/t with k nonincreasing — is exactly the cone paper's proof of [10, Prop. 4.9(4)] (cone paper pp. 35–36, which reads the dilation inequality through [50, Cor. 15.11] where this paper proves step (c) by hand). The manuscript presents it as "the formal proof does not use that proposition. It derives the identification from Schoenberg's radial theorem, C6, by the route that follows" (p. 71), which is true, but a reader should be told that the route is the cone paper's own, written out with the three steps that the cone paper took from the literature. As it stands, a reader may take the "alternative derivation" for an independent argument.

### Theorem A.16 (p. 75; proof p. 76). Machine-checked.

The datum in dimension d from Proposition 3.10(1); the shadow ν̄ on the line is a symmetric Lévy measure (|x_1| ≤ |x|); the exponent at (ω, 0, …, 0) is b Cin(τ|ω|); C3(ii) gives a = 0 and ν̄ = ν_1 (both Lévy measures symmetric, so the compensators vanish — stated). The support: ν({|x_1| > τ}) = 0, rotated to every unit vector u, and {|x| > τ} covered by countably many slabs through a dense sequence (the inequality ⟨u_n, x⟩ ≥ |x| − |u_n − x/|x|| |x| > τ: correct); then k_d = 0 a.e. on (τ, ∞) by Lemma A.1 and everywhere by monotonicity. The edge: a point rη ∈ S_ε with k_d(r) ≠ 0 has r ∈ (τ(1−ε), τ] and η ∈ K_ε; k_d(r)/r ≤ 2k_d(τ/2)/τ for ε ≤ ½; ν(S_ε) ≤ (σ(K_ε)/|S^{d−1}|)Mτε versus ν(S_ε) = ν_1({τ(1−ε) < |y| < τ}) ≥ bε; dividing by ε and letting the caps shrink to the two σ-null poles (d ≥ 2): contradiction. Correct and self-contained.

### Is anything presented as two results? Is anything circular?

Presented twice or more:
- Strictness of every inclusion A_{d+1} ⊊ A_d: Proposition 3.19(2) (step datum), Theorem 3.21(4) (the family), Theorem A.15(1) (the family again, same proof text as 3.21(1), pp. 70–71 vs p. 74), Theorem A.15(3) (restated chain).
- The Cin rays: Proposition 3.19(3) and Theorem A.16 (declared, with a second proof).
- A_∞ = S: Proposition 2.6(3) (cited from the cone paper) and Theorem A.15(3) (reproved by the cone paper's route, see above).
- Theorem A.15(2) is a remark on the bound 6+4√2 of [10, Lem. 4.12(1)] that "no other statement of this paper uses" (p. 70); it is a comparison with the earlier paper, not a theorem clause.

Circularity: none. Proposition 3.19(2)'s nesting comes from clause (1); Theorem 3.21(4) cites Theorem A.15(3) for A_{d+1} ⊆ A_d, which A.15(3) proves in one line from the projection and also attributes to Proposition 2.6(1); Theorem A.16 does not use the nesting. The dictionary (3.18) uses Lemma A.3(1) and Corollary 3.13, which do not use §3.4.

### Gaps and unjustified steps found

None that break a proof. Small points a reader must supply:
- p. 62, clause (2) existence of Prop. 3.18: the sentence "cG = k_d off the countable set of the discontinuities of k_d" is where the a.e. uniqueness of Proposition 3.10(1) is used to make "Pr(|X| > r) = k_d(r+)/c for every datum" true for every datum, not only the one constructed; say so in one clause.
- p. 63, Lemma A.8(2): the dominated-convergence bound uses that k′ is finite at r_0/2; this is Definition 3.9's codomain [0, ∞), fine, but "which is integrable" could say why.
- p. 71, A.15(1), and p. 74, 3.21(1): the a.e.-agreement contradiction needs u_n < v_n for large n; implicit in u_n ↓ r < s ↑ v_n.
- p. 64, Cor. A.9(2): "ξ ↦ G(|ξ|) is the exponent of the datum (0, k_d) with k_d(r) = b Pr(τ > r) = b1_{(0,τ)}(r)" — fine.

---

## 4. The worked examples and figures (my part), reproduced

All values below are from `out/D/check_D.py`, `check_D2.py`, `check_D3.py`, independent of the paper's scripts.

| claim (page) | paper | recomputed | status |
|---|---|---|---|
| w_1, w_2, w_3 (p. 29, 65) | 12.61, 5.24, 3.21 | 12.6063, 5.2423, 3.2056 | agrees |
| √d·w_d at d = 1, 20 (p. 65) | 12.61, 2.056 | 12.606, 2.0562 | agrees |
| √π (p. 65) | 1.7725 | 1.77245 | agrees |
| first d with √d·w_d < √π (p. 65) | between 55 and 56 | 55: 1.77278, 56: 1.77197 | agrees |
| minimum of √d·w_d (p. 65) | d = 81, 1.7661 | d = 81, 1.76610 | agrees |
| increasing after 81 up to 300 (p. 65) | yes | nondecreasing on 81..300 (1.7695 at 200, 1.7705 at 300) | agrees |
| w_2, w_3 against √(π/d) (p. 29) | about 4.2 and 3.1 times | 4.18, 3.13 | agrees |
| upper bound of Lemma A.11 available for d ≥ 3 (p. 29, Fig. 2) | ε_3 < 1 ≤ ε_2 | ε_2 = 1.059, ε_3 = 0.961 | agrees |
| M_2 > 1/15, w_2 < 7.5 (p. 70) | | M_2 = 0.0845, w_2 = 5.24 | agrees |
| w_1 > 6+4√2 (p. 70) | | 12.61 > 11.66 | agrees |
| w = 4: profiles in d = 1, 2 nonincreasing, in d = 3 increasing on an interval (p. 28–29, Fig. 2b) | | d = 1, 2: nowhere increasing; d = 3: increasing exactly on (1.204, 1.737) | agrees; the shaded band of Fig. 2(b) spans about r ∈ [1.2, 1.75] |
| (A.19) against (3.4) at d = 3, w = 4, r = 1.5 | | 4.11870 both | agrees |
| shadow of b1_{(0,τ)} from the plane to the line (p. 27) | (2b/π)arccos(r/τ) | Lemma A.8's integral at r/τ = 0.1, 0.5, 0.9, 0.99 equals (2b/π)arccos(r/τ) to 6 digits; falls from b to 0 | agrees |
| Matérn exponent in the dictionary (p. 27) | φ(r) = (1+r²/2)^{−1} | 1 − rF′(r)/(2γ) = (1+r²/2)^{−1} at r = 0.5, 1, 2 | agrees |
| Ω_2 = J_0, Ω_3 = sin t/t (p. 26) | | sphere averages at t = 0.7, 2.0 agree to 6 digits | agrees |
| polar profile of the Matérn kernel on the line and in space (p. 25) | 2γe^{−√2r}, 2γ(1+√2r)e^{−√2r} | rederived from K_{1/2}, K_{3/2}; and equal to 2γ·Pr(|X_1| > r) for the Matérn-1 law in R^1 and R^3, as p. 27 says | agrees |

**The case w = 4: what is proved, what is computed.** Proved in Lean (p. 80): w_3 < 4 and F^(4) ∉ A_D for D ≥ 3. Proved in print: that k_2^(4) (and k_1^(4)) is nonincreasing, in the cone paper [10, Lem. 4.12(2)] by elementary inequalities (cone paper p. 82), which with Lemma A.10 is 4 ≤ w_2, and F^(4) ∈ A_2 is [10, Lem. 4.12(3)] — which this paper's Table 2 cites. Yet §1.1 (p. 6) says "That it is admitted on the line and in the plane rests on the computed value w_2 ≈ 5.24" and Appendix B (p. 80) says "The other inequality of the example, 4 ≤ w_2, is the computed one." The two accounts disagree; the trust-base account should say that 4 ≤ w_2 is proved in print in the cone paper and only w_2 ≈ 5.24 itself is computed.

**Figure 2.** Panel (a): twenty values, logarithmic scale, the lower bound in every dimension, the upper bound from d = 3, the asymptote √(π/d), the line w = 4 crossing between d = 2 and d = 3: all as captioned and consistent with my values (upper bound 63.8 at d = 3, 1.33 at d = 20; lower bound 0.30 at d = 1, 0.094 at d = 20). Panel (b): the three profiles at w = 4 by (A.19), with the values I computed (k_1(1) = 2.89, k_2(2) = 3.11, k_3(2) = 4.08, k_3(0.5) = 6.5) matching the curves, and the increasing stretch of k_3^(4) in the shaded band. The figure shows what the caption says.

---

## 5. The trust base (my part)

Table 3 (p. 79) against `lean-axiom-report.txt`, declaration by declaration for the statements of my part:

- Prop. 3.19 (`profile_one_dimension_down`, `profile_one_dimension_down_of_classA`, `not_classA_succ_of_profile_discontinuous`, `step_datum_separates`, `cin_ray_not_classA`, `stepOriginDatum`): C2, C3(i)(ii)(iii), C4 — agrees with "C2, C3, C4".
- Lemma A.8 (`shadow_profile_mean`, `shadow_profile_regular`, `shadow_datum`, `lintegral_shadow`, `OriginDatum.shadow`, `shadowProfile`): logical axioms only — agrees with "none".
- Def. 3.20 (twelve declarations): logical axioms only — agrees.
- Thm. 3.21: `separating_family_critical_values`, `witness_classA_iff`, `witness_classA_iff_le`, `witness_not_classA_of_gt`, `separating_family_strict` on C2, C3, C4; `criticalValues_strictAnti`, `criticalValues_tendsto`, `criticalValues_existsUnique_window` on none — agrees with "C2, C3, C4, in clauses (1) and (4)".
- Lemmas A.10, A.11, A.12, A.13 (all declarations listed): logical axioms only — agrees.
- Thm. A.15: `filtration_witness`, `filtration_strict` on C2, C3, C4; `filtration_top` on C2, C3, C4, C6; `filtration_witness_exists` on none — agrees with "C2, C3, C4; and C6 for A_∞ = S in clause (3)".
- Thm. A.16: `no_cin_ray_in_the_plane` on C2, C3, C4; `cin_ray_scaled` on none — agrees.

No declaration of my part depends on an assumption outside the nine named in Appendix B. The report lists only `propext`, `Classical.choice`, `Quot.sound` and the nine names.

Honesty of the account: §1.1's notes that Proposition 3.19(1) is two formal statements and that Lemma A.8(1)'s "mean" wording has no formal counterpart (p. 7) are accurate and welcome. Two things to fix: (i) the w = 4 account (§4 above) — "the computed one" is wrong, it is proved in [10]; (ii) Theorem A.15(2), the inequality w_2 < 6+4√2 — Appendix B lists four declarations for A.15 and the reader cannot tell whether clause (2) is among them (`filtration_witness_exists` may be the nonemptiness of the windows, which is Lemma A.10). Since §1.1 claims that every clause not on the second list has a formal counterpart, say which declaration carries A.15(2), or move the clause to a remark outside the formal inventory.

---

## 6. Sources and relation to prior work (my part)

- **Prop. 3.18 row (p. 33).** The attribution of clauses (1)–(2) to the random-integral representation ∫_0^∞ e^{−s}dY(s) (Jurek–Vervaat, Sato–Yamazato, Wolfe) and its radial form (Jurek 1992; Jurek–Mason) is appropriate: the law of |X| is the jump law of the driving process, c its rate. The Schoenberg-class facts are cited to [44] and [17]. **Missing**: Corollary A.9(2)'s conclusion, Ω_d(τ|·|) ∉ Φ_{d+1}, is Schoenberg's witness for the strictness (Schoenberg, Ann. Math. 39 (1938); a direct proof in Golinskii, Malamud, Oridoroga, Trans. AMS 370 (2018) 1–25, who prove Ω_n ∈ Φ_n \ Φ_{n+1}). Name it at the corollary and in the row.
- **Prop. 3.19 / Cor. A.9 row.** Cambanis–Huang–Simons, Fang–Kotz–Ng and Daley–Porcu cover the radius of a projected rotation-invariant *law*. Lemma A.8 is the same operation on a Lévy measure and the formula k̄(r) = 2C_d r^d∫_r^∞ k′(s)s^{−d}ds/√(s²−r²) is Matheron's *descente* (the turning-bands operator) in the form of an Abel transform (Matheron 1965, 1973; Gneiting, JMVA 69 (1999) for the dimension walk; [7] already in the list). A citation at Lemma A.8 would place the "shadow" in the vocabulary a spatial-statistics reader knows, and would also point the author to the inversion used in §4 below.
- **Thm. 3.21 row.** Correct: [10, Lem. 4.12] has w = 8 ∈ A_1 \ A_2 and w = 4 ∈ A_2 \ A_3, and [10, Rem. 4.10] the three values. The strictness at every step and the limit are new here; see §2 on how the paper describes that.
- **Thm. A.15(3)'s reproof of A_∞ = S**: see §3 — it is the cone paper's own route and should be described as such, with [50, Cor. 15.11] named as what step (c) replaces.
- I found no prior source for the dimension filtration of radial self-decomposable exponents (the literature on Φ_d concerns infinite divisibility in every dimension, the type G side; the cone paper's Remark 4.10 says the same).

---

## 7. Exposition and structure (my part)

§3.4 (pp. 25–29) is readable by the intended reader: "radial characteristic function", "isotropic correlation function", "Schoenberg classes", "shadow", "critical values" are each introduced where first used; the three statements are announced and read back in plain words. Two improvements: the sentence "A polar profile with a jump belongs to a Lévy density that is cut off sharply at some radius" (p. 27) is inexact (a jump need not be a cutoff to zero; "has a jump at some radius" suffices); and the loose "exactly when" sentence after Proposition 3.18 (§2 above).

Appendix A.5 (pp. 60–77, 17 pages) is where the length is. A journal version should: (a) delete Theorem A.15(1) (it is Theorem 3.21(1)+(4), with the same proof text) and A.15(2) (a remark on the cone paper's bound, with the "coincidence" paragraph of p. 68); (b) keep A.15(3) as a proposition "A_∞ = S from C6" only if the author wants the formalised route in print, and say it is the route of [10, Prop. 4.9(4)]; the proofs of steps (a)–(c) (3 pages) can be compressed to references plus step (c); (c) keep Theorem A.16's proof, which is short and elementary, but as "second proof of Proposition 3.19(3)" rather than a theorem; (d) move the paragraph of computed values on p. 65 ("No statement uses these values") to the Figure 2 caption. That saves about five pages without losing a proved fact.

Division main text / appendix: right for this part. Lemma A.8 could be stated in the main text (it is the idea behind the test and takes six lines), with Proposition 3.19 then reading as its corollary.

---

## §4 and §4.1: is it a conclusion of what was shown; are the open questions open

§4 (pp. 29–30) summarises what §3 proves, with the right statement numbers, and its four limitations are honest (no generator; nothing on locality or extrema; the stages not examined at their centre; the dictionary only for logarithmic growth). The imaging readings are accurate (see §2 for the one clause to add on "not admitted").

§4.1 lists three open problems. **Two of them are answered by the paper's own objects.**

**(a) "The stages" (p. 30).** "Which stages have a density, and which have an atom at the centre? Where a stage has a density, is it bounded near the centre, and what number takes the place of c?" By (3.1) the stage μ_{s,t} has exponent F(χ(t)|ξ|) − F(χ(s)|ξ|). For a datum (a, k_d) the dilation by χ has the polar profile k_d(r/χ), so the stage is the infinitely divisible law (C3(iii), uniqueness by C3(ii)) with Gaussian coefficient a(χ(t)² − χ(s)²) and Lévy measure of polar profile k_d(r/χ(t)) − k_d(r/χ(s)) ≥ 0. Its total mass is, for c = k_d(0+) < ∞,

  ∫_0^∞ [k_d(r/χ(t)) − k_d(r/χ(s))] dr/r = c · log(χ(t)/χ(s)),

by the computation ∫_ε^A k(u)du/u − ∫_{ε/λ}^{A/λ} k(v)dv/v = ∫_ε^{ε/λ} k du/u − ∫_A^{A/λ} k dv/v → c log(1/λ) − 0 (λ = χ(s)/χ(t); the first term is squeezed between k(ε/λ)log(1/λ) and k(ε)log(1/λ), the second is at most ∫_A^∞ k dv/v, which Definition 3.9 makes tend to 0). I checked it numerically for k = c e^{−r}. So for a = 0 and c < ∞ **every stage with s > 0 is a compound Poisson law**: it has an atom at the centre of mass (χ(s)/χ(t))^c, and no density; its absolutely continuous part has the explicit Lévy density. For c = ∞ the Lévy measure of the stage is infinite and the stage has no atom (Sato [38], Thm. 27.4); for a > 0 the stage has a smooth density. The number that "takes the place of c" is c log(χ(t)/χ(s)). This is three lines from Definition 3.9 and (3.1), and it is a striking imaging fact — a stage of a Matérn cascade from scale s to scale t leaves a fraction (s/t)^{2γ} of the image untouched — so it belongs in the paper (in §3.3 or §4), not in the open list. What stays open is only whether the absolutely continuous part is bounded near the centre when c < ∞, and whether the stage has a density when c = ∞ and a = 0. The limitation sentence in §4 ("the stages … are not examined") and the Scope paragraph of §1 are then also to be revised.

**(b) "The step witnesses" (p. 30).** "Is [the exponent of a step datum] still the exponent of an infinitely divisible law [in the next dimension]?" **Yes.** Lemma A.8 says the shadow of a profile k′ in dimension d+1 is k̄(r) = 2C_d r^d ∫_r^∞ k′(s) s^{−d} ds/√(s²−r²), an Abel transform of k′(s)s^{−d}. Prescribing k̄ = b1_{(0,τ)} and inverting (Abel's inversion formula, with the support of k′ in (0, τ]),

  k′(s) s^{−d} = −(b/(πC_d)) · d/ds ∫_s^τ r^{1−d} dr/√(r² − s²),

which is **positive**, because the integral is strictly decreasing in s; for d = 1 it is k′(s) = bτ/√(τ²−s²), for d = 2 it is k′(s) = (2b/π)[arccos(s/τ) + s/√(τ²−s²)]. Then ν′ = (σ_d/|S^d|) ⊗ k′(s)ds/s is a Lévy measure on R^{d+1} (k′ is bounded near 0 and has an integrable (τ−s)^{−1/2} singularity at τ; I checked ∫(|z|²∧1)ν′ < ∞ numerically), and the infinitely divisible law with triplet (0, ν′, 0) has the rotation-invariant exponent ζ ↦ G(|ζ|), because its restriction to R^d has Lévy measure the shadow, whose profile is the step. I verified numerically that the shadow of these k′ is b on (0, τ) for d = 1 and d = 2 at four radii each. So the step datum's exponent is the exponent of an infinitely divisible law in dimension d+1 whose Lévy measure has an *increasing* radial profile — exactly what Proposition 3.19(1) says must happen. For d = 1 there is even an exact identity in R³: b Cin(τr) = G_3(r) + b(1 − Ω_3(τr)), with G_3 the exponent of the step datum in R³ and the second term the compound Poisson exponent of the uniform law on the sphere of radius τ (verified by differentiation and numerically), so the Cin ray is infinitely divisible in R³ as well. It is not infinitely divisible in every dimension: by C6 that would make σ ↦ Cin(τ√(2σ)) a Bernstein function, whose derivative (1−cos(τ√(2σ)))/(2σ) is not monotone. The genuinely open question is therefore the *last* dimension in which a step exponent is infinitely divisible — a second, finite filtration, between A_d and the type G class. Replace the open problem by that.

**(c) "The derivatives".** I have not found the R^d statement in the literature either; the question stands. (I could not verify the Sato–Yamazato theorem numbers 1.6 and 1.7 from the files available; the reference is plausible.)

Missing from the list, and worth a line: whether the critical values w_d have a closed form (the text says they have none, p. 29, which is an assertion, not a theorem); whether the dictionary extends to c = ∞ (the limitation says it does not, so the question is natural); and the generator question of the cone paper's Prop. 6.2 in R^d, already named as a limitation.

---

## 8. Required changes and suggestions (my part)

### Required changes

1. **p. 30, §4.1 "The stages":** remove or rewrite. Every stage with s > 0 of a family with a = 0 and c < ∞ is compound Poisson with an atom of mass (χ(s)/χ(t))^c at the centre (Lévy mass c log(χ(t)/χ(s)), from Definition 3.9 and (3.1)); only the boundedness of the absolutely continuous part and the c = ∞ case stay open. State the fact in the paper and adjust the limitation sentence in §4 and the Scope paragraph of §1 (p. 3).
2. **p. 30, §4.1 "The step witnesses":** the question is answered affirmatively by inverting Lemma A.8 (Abel inversion gives a positive profile in dimension d+1 whose shadow is the step; explicit for d = 1, 2 above). Either state the answer as a proposition or drop the question; the open question is the last dimension in which the step exponent is infinitely divisible.
3. **p. 64, Cor. A.9(2), and Table 2, p. 33:** attribute the conclusion Ω_d(τ|·|) ∉ Φ_{d+1} to Schoenberg (1938) (direct proof: Golinskii–Malamud–Oridoroga 2018); the paper's own rule ("no new result for probability", p. 5) requires it.
4. **pp. 6 and 80 versus Table 2, p. 33:** the inequality 4 ≤ w_2 (F^(4) ∈ A_2) is proved in print in [10, Lem. 4.12(2)–(3)], not "the computed one"; make the trust-base account agree with Table 2.
5. **p. 1 (abstract) and p. 27:** qualify the dictionary's headline by "an F admitted in dimension d" and replace the sentence "an exponent of logarithmic growth is in A_d exactly when r ↦ 1 − rF′(r)/c is a radial characteristic function" by the bijection that Proposition 3.18(2) proves (F = c∫_0^r(1−φ)du/u).
6. **pp. 70–71, Theorem A.15:** delete clause (1) (duplicate of Theorem 3.21(1)/(4) with the same proof text) and clause (2) (a comparison with a bound of the cone paper that nothing uses); if A.15(2) stays, say which Lean declaration carries it (Appendix B lists four for A.15).
7. **p. 71, the reproof of A_∞ = S:** say that the route (self-decomposable in every dimension ⇒ Bernstein by C6 ⇒ dilation-monotone Lévy measure ⇒ nonincreasing delay profile) is that of [10, Prop. 4.9(4)], with step (c) replacing [50, Cor. 15.11]; as written, "an alternative derivation" suggests independence.

### Suggestions

1. **p. 68:** replace "This paper does not explain the coincidence" by the explanation: both constants are (1 − 2^{−1/2})², from λ_1 = 2^{−1/2} in [10] and λ_{d+1}/λ_d = 2^{−1/2} here — or delete the paragraph.
2. **p. 60, Lemma A.8:** cite Matheron's descente / turning-bands operator (Matheron 1965, 1973; Gneiting 1999; [7]) and give the Abel form k̄(r) = 2C_d r^d∫_r^∞ k′(s)s^{−d}ds/√(s²−r²), which is both more recognisable and what the inversion in required change 2 uses.
3. **p. 28:** after "What the clause excludes is a Cin ray taken alone", add that the filter e^{−b Cin(τ|ξ|)} is still a probability kernel in the plane and in space (it is infinitely divisible there), so that the imaging reader sees what is lost: the stages, not the aperture.
4. **p. 27:** "cut off sharply at some radius" → "has a jump at some radius".
5. **p. 3, §1:** cite Lemma A.11 (the order d^{−1/2}) beside Theorem 3.21 for "critical values that decrease like d^{−1/2}"; the theorem's clause (3) is the limit.
6. **p. 65:** move the paragraph of computed values (crossing between d = 55 and 56, minimum at d = 81) to the Figure 2 caption or a footnote; it is correct (I reproduced it) but interrupts the lemmas.
7. **p. 75–76, Theorem A.16:** keep the proof, which is the most elementary argument in the appendix, but title it "second proof of Proposition 3.19(3)" and drop the theorem number.
8. **p. 29, Figure 2 caption:** add the numerical range of the increasing stretch in panel (b), r ∈ (1.20, 1.74), so a reader can check it from (A.19).
9. **p. 33, Table 2, row Thm. 3.21:** say in one clause what is new here relative to [10]: strictness at every step and the limit √d·w_d → √π.
10. **pp. 72–73, steps (a)–(c):** if kept, compress (a) to "the Lévy–Khintchine exponent of the residual is negative definite" with a reference, and keep only (c) in full; three pages become one.
