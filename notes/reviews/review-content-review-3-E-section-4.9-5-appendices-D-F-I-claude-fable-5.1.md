# Referee report E — §4.9, §5 and Appendices D, F–I (the rest read for consistency)

Manuscript: *Spatial scale space from hemigroup axioms: affine covariance and shape adaptation* (110 pp.). Block reviewed in detail: §4.9 (pp. 51–53, with Proposition 4.24 and its proof in Appendix B.3, pp. 69–70), §5 and §5.1 (pp. 54–56), Appendix D (pp. 83–84), Appendix F (pp. 88–93), Appendix G (pp. 93–94), Appendix H (pp. 94–103), Appendix I and the declarations (pp. 103–106). The rest of the paper (§§1–4.8, Appendices A–C, E) was read for consistency with this block. Page numbers are those printed in the PDF.

---

## 1. Overall assessment and recommendation

**Recommendation: major revision.**

The mathematics of this block is, with the exceptions listed in §3 below, correct as far as the printed arguments go, and the two computations (Remarks E.5 and H.3) reproduce exactly from their descriptions. The block's purpose — to fill the rows of the two smaller groups in Table 2 and to say what the results mean for shape adaptation — is served, and the open-problems list is unusually candid. Three things keep me from recommending minor revision. (i) The paper states as *open* a question that its own Theorem 3.5 settles: a cascade family of the scheme has infinitely divisible increments, so for the general linear group along a stable order (and along any cone order of Theorem 4.21(2)(c)) the ordered-density condition on the profile is *necessary*, not only sufficient. This closes the profile clause of Theorem 4.21(3)(c), Proposition 4.20(2), the cell (GL(d), stable order) of Table 2, open problem 1 as it bears on the row, and the second question of open problem 3 — and it changes the honest count of "complete" cells in §5 (p. 54). The text currently says the opposite (p. 48, p. 55). (ii) The sketch of Proposition H.8(3) does not prove its statement under the first of its two hypotheses (infinitely divisible increments with a moving Gaussian part); the statement is true, but by a different argument. (iii) Twenty statements, among them most of those that Table 2 cites for the similarity and diagonal rows (F.2–F.5, H.1, H.2, H.4–H.8), are printed with sketches only, their complete proofs being "deposited" (p. 104). A journal cannot publish Table 2's claims on the strength of proofs that are not in the paper or its supplement; the journal version must either print them or move those cells to a clearly marked "stated with proof in the supplement" status. Together with the length (about 20 pages in this block alone, of which Appendices D and G and more than half of H could go to a supplement), this is a restructuring, not a list of corrections.

---

## 2. The headline claims against what is proved

I take the claims that bear on this block.

**"With the similarities, non-Gaussian families cascade along the Loewner order" (abstract, p. 1; intro p. 5; §5 p. 54).** Supported: Proposition H.1(3) (p. 95) gives the family N(0, 2bΣ) ∗ S_α(Σ + κ tr(Σ) I) with ακ² − (d+1)κ − 1 ≥ 0, and I checked the proof (§3 below). The condition on κ is only sufficient and is large (κ ≳ (d+1)/α); the text says so (p. 95). Fine.

**"a departure from rotation invariance at most four times the eccentricity of the aperture" (§5, p. 54; §4.9, p. 52; intro, p. 5).** The quantity bounded is the *exponent spread of the non-Gaussian part*, es(ψ_Σ) ≤ 4 ecc(Σ) (Proposition 4.24(2), last sentence, p. 53). The intro (p. 5) says this precisely ("the exponent of their non-Gaussian part changes under a rotation by at most a factor of …"); §5 says "a departure from rotation invariance", which a reader will take as a statement about the kernel. The kernel's Gaussian part is as anisotropic as N(0, 2bΣ) is. Say "of the non-Gaussian part" in §5 and in Table 2's cell. Also: the bound is not claimed sharp and is far from the examples (the stable orbit, which is not a Loewner family, has ecc^{α/2}; the H.6 family has ecc^{pα/2} with pα/2 < α²/(2(d+α)) < 1); a sentence saying that no example with spread growing like ecc(Σ)^1 is known would place the bound honestly.

**"So the rigidity of the general linear group with the Loewner order needs both: the Loewner order alone does not force the Gaussian, and the general linear group alone does not either (Theorem 4.21(3))" (p. 5).** Correct as stated: the first half is Proposition H.1(3) (and the products of Proposition F.4(3)), the second half is Theorem 4.21(3)(c)–(d) with α < 2. The sentence cites only Theorem 4.21; cite H.1(3) for the first half. No sentence in this block reads the smaller groups as showing that "the rigidity is a property of the group" alone; §4.9 (p. 52) correctly says that Theorem 3.6 "needs the whole general linear group, since its proof transports one rank-deficient step to every other".

**"For the positive diagonal group a family that cascades along each axis is, at the diagonal apertures, a product of self-decomposable laws on the line" (p. 5; §4.9 p. 52; Table 3 p. 51).** Supported by Proposition F.2 (p. 89) and F.4(3) (p. 91); proofs checked. "Such families gain anisotropy along the axes as fast as the Gaussian does and cannot turn": correct, the extremal Loewner steps of Lemma 4.1(3) are diagonal, so the Gaussian's bound (t₂/t₁)^d is attained within the frame; and the frame is fixed.

**"The price of a smaller group is shape selection, which needs a group that carries every shape to every other" (p. 5; §4.9 p. 51; §5 p. 54).** This overstates. A family of the similarities has a kernel at every Σ, so an aperture can be *selected* by the second-moment matrix exactly as before; what is lost is the covariance of the selected measurement under the deformations outside the group (an affine image of the pattern is no longer measured by the transported aperture). Say "the price is the affine covariance of the selection", which is what §4.1 use 1 actually asks for.

**"Within these limits four cells of Table 2 stop short of a classification … Three more are classified on part of their parameters" (§5, p. 54).** This is the only place where the "completely in some cases" of the abstract (p. 1) and of the intro ("a complete description in some cases and bounds or examples in the others", p. 3) is made cell by cell, and it says: two of nine cells are complete descriptions, (GL(d), rays) and (GL(d), Loewner). Table 2 itself (p. 32) does not mark completeness, and the abstract's "completely in some cases" does not say "two of nine". Two corrections: (a) mark in Table 2 which cells are complete; (b) by §3.1 below, the cell (GL(d), stable order) *is* complete, so the count becomes three of nine, and the sentence "Along the stable orders the orbit of a general profile is described by a sufficient condition" (p. 54) is wrong.

**"a non-Gaussian kernel loses nothing the practice uses, and it loses the cascade between its stages" (§5, p. 54).** Scoped by "as far as the apertures are concerned", which is right; but the practice also uses the Gaussian's semigroup for computation (pyramids, separability) and the scale normalisation of derivatives, none of which the paper treats (and §5 says the computation is left to a further paper). Keep the sentence with "as far as the apertures of the iteration are concerned" moved to the front.

**Table 2, row "similarities", column "Loewner" (p. 32).** Every item traces to a statement: 4.24(2), H.5, H.9, H.6, H.8, H.7(3), H.1(3). The cell is a paragraph; see §7.

**Table 3, rows "frame families" and "one linear flow" (p. 51).** Supported by F.1, F.2, G.1 and 4.11. The entry "orbit of a self-decomposable profile k: at least the cone read off R" is right for single steps (which is what Table 3 is about) and stays "at least" even after §3.1 below, since the single-step converse remains open; say in the caption that Table 3 is about single steps and Table 2 about families, because after the correction the two tables will read differently for the same kernel.

**Scope sentences (§5, p. 54).** "it makes no statement about images", "It treats the apertures a family offers, not how a shape is chosen", the exclusion of singularity theory and of grids: all accurate and all honoured in the block.

---

## 3. Mathematical correctness

### 3.1 A result the paper states as open is a corollary of its own Theorem 3.5 (pp. 48, 54, 55)

After Theorem 4.21 (p. 48): "For general profiles the row is known to be at least the one stated: that µ_I ∈ F_α forces R(λ) ≥ λ^α is the open converse of Proposition 4.13." Open problem 1 (p. 55): "The converse would complete the profile clause of Theorem 4.21(3)(c) and of Proposition 4.20(2)". Open problem 3 (p. 55): "Whether two cones with the same number β(C) … carry the same families is not decided either."

These conflate two questions. The open converse of Proposition 4.13 is about *one* positive increment. Membership µ_I ∈ F_α is about a (GL(d), ≤_α)-cascade family, with (K1) and (K2) on all pairs, and (GL(d), ≤_α) has the path condition (Proposition 4.20(1), p. 46). So Theorem 3.5(2) applies, exactly as the paper applies it for the similarities in Proposition H.9(1) (p. 103): every increment µ_{Σ,Σ'} and every kernel µ_Σ is infinitely divisible. Then, as in the sketch of Proposition H.2(1) (p. 96), the triplets add and C2(ii) gives L_{Σ'} = L_Σ + L_{µ_{Σ,Σ'}} ≥ L_Σ, i.e. n_Σ ≤ n_{Σ'} almost everywhere along every step Σ ≤_α Σ' in PD(d). Lemma 4.14(4) (p. 44), applied to the steps diag(λ², …, λ², λ^{2(1+α)}) of its proof (p. 68), gives R(λ) ≥ λ^α, that is α ≤ β₋(k) — with the one technicality that the a.e. ordering is turned into the pointwise one by right-continuity of k, as H.2(1) already does; since the law determines k only up to a null set, R should be defined for the right-continuous representative anyway (at present R is not a function of the law). Consequently:

- **Theorem 4.21(3)(c)** can read: for 0 < α < 2, a rotation-invariant self-decomposable law µ_I = N(0, aI) ∗ ν_k (every such law has this form by the polar criterion, Definition 2.8 and [16, Prop. 3.11], p. 11) lies in F_α if and only if k = 0 or β₋(k) ≥ α. The Gaussian part is free, since it cascades along the Loewner order and the convolution of two families is a family (Lemma 3.3(3)). The cell (GL(d), stable order) of Table 2 is then a complete description.
- **Theorem 4.21(2)(c)**, for a cone C of definite directions with β(C) < 2: the same argument along the steps e^{tX*}, with X* ∈ C attaining β(C) (attained, p. 82), gives through Proposition 4.13(2) the inequality R(λ) ≥ λ^{β(C)} for every λ ≥ 1; conversely C ⊆ C_{β(C)} and the ≤_{β(C)}-family restricts. So the (GL(d), ⪯⁺_C)-families are exactly the orbits of N(0, aI) ∗ ν_k with β₋(k) ≥ β(C): they depend on C only through β(C). This answers the second question of open problem 3 in the affirmative.
- **Proposition 4.20(2)** becomes an "if and only if"; **open problem 1** survives only as the single-step question (and Table 3's "at least" survives with it); §5's "four cells stop short" becomes three, and the abstract's "completely in some cases" should say which.

I have checked each step against the printed statements (Theorem 3.5(2) p. 20 and its proof p. 64; Proposition 4.20(1) p. 46 and proof pp. 79–80; Lemma 4.14(4) p. 44 and proof p. 68; Proposition 4.13(2) p. 43). Nothing beyond the paper's own results is used. If the author sees an obstacle I have missed, the place to look is whether the (K2)-continuity along the geodesic chain of Theorem 3.5(3)(c) is available for the kernels of a (GL(d), ≤_α)-family — it is, as (K2) is required on all of P_W.

### 3.2 §4.9 and Proposition 4.24 (pp. 51–53, proof pp. 69–70)

- The family displayed on p. 52, N(0, 2bΣ) ∗ S_α(Σ + κ tr(Σ) I) with ακ² − (d+1)κ − 1 ≥ 0, is H.1(3). Note that Proposition 4.24(3) (p. 53) uses a *different* family, N(0, 2b(Σ + κ tr(Σ) I)) ∗ S_α(Σ), with no condition on κ; the two are easily confused since both carry the trace term. A sentence in §4.9 distinguishing them would help.
- 4.24(1): correct (path condition of 4.20(1) plus Theorem 3.5(2); symmetry from −I ∈ S(d); last sentence is F.3(4)).
- 4.24(2): the sandwich εI ≤_α Σ ≤_α tI with ε = ε_α(Σ), t = t_α(Σ) is right (proof of 4.20(1), p. 79: (λ₁^{d+α}/det Σ)^{1/α} and (λ_d^{d+α}/det Σ)^{1/α}, ratio ecc^{(d+α)/α}). The three bounds follow as printed. The exponent-spread bound uses g(cu) ≤ 4c g(u) for c ≥ 1, obtained from g(4u) ≤ 4g(u) and monotonicity; correct. The moment bound uses T_r(L_I) nondecreasing in r; correct. The Loewner variant with λ_min, λ_max: correct, the increments coming from H.9(1).
- 4.24(3): the orbit S_α(Σ) is a (GL(d), ≤_α)-family by 4.20(2); the Gaussian part cascades along Loewner since P + κ tr(P) I ≥ 0; GL(d)-covariance fails at A = (I + e₁e₁ᵀ)^{1/2}, ω = e₁ as the proof says (the exponents 2b(2 + κ(d+1)) and 2b(2 + 2κd) differ for d ≥ 2). The rank-deficient step: Lemma 4.8 with C = b(P + κ tr(P) I) orders the stable densities, which 4.7(3) excludes. Correct.
- The sentence "every family has es(ψ_Σ) ≤ 4 ecc(Σ)" (p. 52) is fine; when L_I = 0 the spread is 1 by the convention on the empty infimum. Fine.

### 3.3 §5 and §5.1 (pp. 54–56)

Beyond §3.1 and the wording points of §2: open problem 5(d) says the computation of Remark H.3 "finds a positive increment that is not infinitely divisible, a numerical observation"; see §4 for what the computation can and cannot show. Open problem 7 is well posed. Open problem 4's statement that the (D⁺(d), ≤_α) condition of F.5(2) is "necessary, its converse open" is right if the converse means *extension off the frame's shapes*: on the frame's shapes the condition is also sufficient, since D_u = e^B with B = diag(log u) ∈ D_α and B-self-decomposability at t = 1 is exactly the increment (K1) asks for; say so (p. 92, after F.5).

### 3.4 Appendix D (pp. 83–84)

Proposition D.1 is correct. (1): the joint stabiliser B = R H_u R^{-1} with R = (Σ + Σ')^{1/2} and u an eigenvector of R^{-1}ΣR^{-1} commutes with the pair and has determinant −1; the singular case is handled. (2): SO(d) is transitive on spheres for d ≥ 2, so µ̂_I is radial; the no-zero argument along the ray of I is that of Lemma 3.9; the increments are quotients and GL(d)-covariance follows by uniqueness of transforms. (3): the point masses δ_{√t−√s} satisfy (K1)–(K4) for GL⁺(1) and fail (K3) at −1. The appendix is three lines of content and could be a remark in §4.2.

### 3.5 Appendix F (pp. 88–93)

- **F.1** (p. 88): (3) is Kelker's lemma through the Cauchy equation of Lemma 3.10; the step "A = diag(s)^{-1} in the hypothesis gives the variance 2bs_i²" is right. Correct.
- **F.2** (p. 89): the reduction φ(λxe_i + η) = φ(xe_i + η) ρ̂(xe_i + η), the use of Lemma 3.8 at x = 0 (where ρ̂ = 1 on a neighbourhood of 0 in H because φ(0) = 1), the elimination of ρ̂ and the limit x → 0 with λ = x₀/x > 1 are all correct. One remark: (D2) is asked for λ > 1 only, and the proof uses exactly that. Correct.
- **F.3** (p. 90): (1)–(4) correct. Family (ii), ((det Σ)^{1/(2d)} I)_* µ_I, is an (S(d), Loewner)-family because det is monotone along Loewner and the increment is a dilated residual; its kernels at singular Σ are δ₀, as A.3 notes. (4) follows. Correct.
- **F.4** (pp. 90–91): correct. In (3), the product form on the orbit of I is forced by the axis steps (Loewner), and the converse family (∆(Σ)^{1/2})_*(ν₁ ⊗ ⋯ ⊗ ν_d) is one extension; the text is honest that the others are not described.
- **F.5** (p. 92): (1) correct (the relative step of D_s², D_{s'}² is D_u²). (2) correct. (4)(a): the 2×2 block of BΘ_r + Θ_rB is [[2(1+α), (2+α)r], [(2+α)r, 2]] with determinant 4(1+α) − (2+α)²r², negative exactly when r² > 4(1+α)/(2+α)², which is < 1 for α > 0; the derivative argument (the increment's Gaussian covariance Θ − e^{−tB}Θe^{−tB} must be PSD, hence its t-derivative at 0) is right. (4)(b), (c) correct.

### 3.6 Appendix G (pp. 93–94)

Proposition G.1 is correct and elementary. One slip: "in the plane S_α(I) rides the curves of B = diag(1, b) for 1 ≤ b ≤ 1 + α" (p. 94). Condition (4.4) with d = 2 reads (2+α) min(1, b) ≥ 1 + b, which holds for 1/(1+α) ≤ b ≤ 1+α; the printed range is the upper half. The appendix lies outside the scheme by its own account and is cited only by the last row of Table 2 and Table 3; see §7.

### 3.7 Appendix H (pp. 94–103)

- **H.1** (p. 95): (1) correct (Lemma 4.8 with C = ½(C(Σ') − C(Σ)); Lemma 4.8 allows any real C). (2) correct; I verified the sandwich, the limit ε → 0 (h continuous to rank one, Loewner closed, ⪯_α ⊆ Loewner), and the inequality ∏(η_i/η_d) ≥ (η_d/h₀)^α ⇒ η_d/η₁ ≤ (h₀/c₁)^α. (3) correct: with A = (1+dκ)/κ and B = κ/(1+κ) the condition (d+α)κ² ≥ (1+dκ)(1+κ) is A ≤ (d+α)B and is ακ² − (d+1)κ − 1 ≥ 0 as stated; the bounds λ_min(M) ≥ 1 + Bu and tr M ≤ d + Au follow from κτI ≤ H ≤ (1+κ)τI; the chain det M ≤ (tr M/d)^d ≤ (1 + (d+α)Bu/d)^d ≤ (1+Bu)^{d+α} is Bernoulli applied to (1+Bu)^{(d+α)/d}. The values after the proposition — bound ((1+dκ)/(1+κ))^α, eccentricity of the stable part at most (1+κ)/κ — check.
- **H.2** (p. 96): (1) the passage from an a.e. ordering of the densities to the pointwise inequality D m(r) ≤ m(r/λ) needs the right-continuity of k, which is assumed; the sketch is correct though terse (one approaches r e_v from outside along points where the a.e. inequality holds, uses monotonicity of m on both sides, and then right-continuity). (2) correct with the cone of 4.13(2): ∏(η_d/η_i) ≤ R((h₀/η_d)^{1/2})² and R nondecreasing with η_d ≥ c₁; note c₁ ≤ h₀ is needed for R to be evaluated at an argument ≥ 1, and it holds since h(e₁e₁ᵀ) ≤ h₀I by the extended ordering. (3), (4) correct.
- **H.4** (p. 97): correct. (4): monotone limits along Σ_ε, countable additivity on shells by domination by L_I; (5): QΣ_εQᵀ ≤ Σ ≤ I for ε ≤ λ_min(Σ). Correct.
- **H.5** (p. 98): (1): es(ψ_{ν_H}) ≤ 4 ecc(H) uses that g(u) = ψ_I(√u e) is nondecreasing, which the sketch attributes to "k nonincreasing in the substitution"; the cleaner reason is self-decomposability (ψ_I(cω) ≤ ψ_I(ω) for c ≤ 1). (2)–(4) correct.
- **H.6** (p. 99): correct. det h(Σ) = det Σ; the density display follows; monotonicity along Loewner by (d+α)γ ≥ 1 and Loewner–Heinz; equivariance since dγ + p = 1; L_* = 0 by domination by n_I; (3) correct.
- **H.7** (pp. 100–101): (1) correct. (2): the inequality ψ_ℓ(aτ) ≥ (a²/4) ψ_ℓ(τ), 0 < a ≤ 1, is *not* a pointwise inequality between 1 − cos(aθ) and (a²/4)(1 − cos θ) (false at a = 0.4, θ = 5π); it holds for the exponent because ψ_ℓ(2τ) ≤ 4ψ_ℓ(τ) and ψ_ℓ is nondecreasing (self-decomposable on the line), as in the proof of 4.24(2). Say so; the sketch gives no reason. The fourth-moment identity ∫⟨v,u⟩²⟨w,u⟩² σ(du) = (1 + 2⟨v,w⟩²)/(d(d+2)) is right, and so are the bounds 4d(d+2) and d+2. (3): the sketch's "two cones of directions around the least and the largest eigenvectors would carry equal mass on every shell, which forces k(r) = k(λr) a.e." does not, as written, force anything: with k nonincreasing, comparing the masses of two cones on which q_Σ takes values in [λ₁, λ₁+δ] and [λ_d−δ, λ_d] only yields inequalities that monotonicity already gives. What does work: rotation invariance of L_Σ, which disintegrates as σ(du) ⊗ (2k(s/q_Σ(u)^{1/2}) ds/s), makes the direction-u profile σ-a.e. independent of u (uniqueness of the disintegration, applied to every rotation), so k(s/q₁^{1/2}) = k(s/q₂^{1/2}) for a.e. s and two values q₁ < q₂ of q_Σ, which is k(r) = k(λr) with λ = (q₂/q₁)^{1/2}, hence k constant, hence 0. Replace the sketch.
- **H.8** (p. 102): (1) and (2) correct (the sandwich L_{λ_min I} ≤ L_Σ ≤ L_{λ_max I} and (2.4); Lemma 2.9(2) for the exponents). **(3) is not proved by its sketch under the first hypothesis.** The sketch says the increment ρ of Σ ≤ tI satisfies ρ̂(ω/ε) → t^{−c/2} e^{∆_Σ(ω/|ω|)}. Under infinitely divisible increments, ρ̂(ω) = exp[−½⟨ω, (C(tI) − C(Σ))ω⟩ − (ψ_{tI} − ψ_Σ)(ω)], and when C(tI) ≠ C(Σ) — which is the generic case, e.g. C(Σ) = c₀Σ — the Gaussian factor at ω/ε tends to 0 for every ω outside ker(C(tI) − C(Σ)), so ρ̂(ω/ε) → 0 almost everywhere, ρ({0}) = 0, and the Fourier identity reads 0 = 0: nothing about ∆_Σ follows. The sketch is valid only when C ≡ 0 (second hypothesis) or C(tI) = C(Σ). The statement is nevertheless true, by this argument: N := L_Σ − L_I is a *finite* signed measure, because its positive and negative parts are dominated by L_{λ_max I} − L_I and L_I − L_{λ_min I}, whose mass on the unit ball is ∫_0^1 (k_d(s/√t) − k_d(s)) ds/s = (c/2) log t − ∫_{1/√t}^1 k_d(s) ds/s < ∞ (monotone convergence). Then ψ_Σ(ru) − ψ_I(ru) = N(ℝ^d) − N̂(ru), and under (D) the limit ℓ(u) := lim_r N̂(ru) exists for σ-a.e. u. For such u, N̂(ru) = (π_u N)^(r) with π_u N a finite signed measure on the line; a finite measure whose transform converges at infinity has at most an atom at 0, of mass ℓ(u) (its transform minus ℓ(u) tends to 0, and a Rajchman measure has no atoms), so ℓ(u) = N(u^⊥); and ∫ N(u^⊥) σ(du) = ∫ N(dx) σ({u ⊥ x}) = 0 by Fubini, so ℓ(u) = 0 for σ-a.e. u and ∆_Σ = N(ℝ^d) a.e. This needs no Gaussian hypothesis at all, so clause (3) can be stated under the single hypothesis of (2). Either print this argument or restrict (3) to C ≡ 0.
- **H.9** (pp. 102–103): correct; this is Theorem 3.5(2) with the path condition of the Loewner order (3.5(3)(a)) and symmetry from −I. It is the same argument as §3.1 above, which is why its omission for the general linear row is surprising.

### 3.8 Appendix I (pp. 103–105)

The list of twenty sketched statements matches the sketch markers in the text (I counted them). The ledger of cited facts is consistent with the axiom-guard printout: `wedge_axis_row` depends on C2 and C3 and not on C1 or C4, as the proof in Appendix C.4 (p. 81, first paragraph) promises; `causalLE_order` on C4; `gw_family_infinitelyDivisible` on C1. One inconsistency with §3.1 above: Appendix I lists "C1: Proposition 4.24, for its clause (1)" and "C1: Proposition H.9", i.e. the author's development knows that Theorem 3.5 feeds the similarity cells, yet the general linear stable cell is not given the same treatment.

### 3.9 Consistency with the rest (read, not refereed in detail)

- The statement "the Loewner order alone does not force the Gaussian" (p. 5) and Table 2's last row rely on 4.11; its clause (2) (p. 67) and clause (1) (pp. 80–81) are consistent with the use in G.1 and Table 2.
- Proposition A.3(4) (p. 61), F.3(3) and §4.9 "The ray column" agree on the two families with the same isotropic member.
- Remark 4.23 (p. 51) cites D.1(3) correctly.
- Lemma 3.3(3) (p. 18) is what F.5(4)(c), 4.24(3) and H.1(3) use to convolve two families; it requires transforms without zeros, which all three have.
- The isotropic-paper statements restated in §2.3 are used in H.8 (Definition 2.8, Lemma 2.9(2)) within their stated hypotheses (profile bounded at the origin, Gaussian coefficient 0 for the datum of L_I; the kernel's own Gaussian part C(I) is separate and is handled by H.4). Consistent.

---

## 4. The numerical examples

**Remark H.3 (p. 97), reproduced.** From the description alone I implemented the increment transform ρ̂(ω) = e^{−b⟨ω,Pω⟩}(1 + ⟨ω, h(Σ)ω⟩)/(1 + ⟨ω, h(Σ')ω⟩) with Σ = diag(1, 0.3), P = diag(0.05, 0.55), h(Σ) = Σ + 2 tr(Σ) I (so h(Σ) = diag(3.6, 2.9), h(Σ') = diag(4.85, 4.65)), sampled on the frequency grid of a square of side 60·√4.85 = 132.14 and inverted by FFT at 1024² and 2048² points (spacings 0.129 and 0.0645, frequencies to 24.3 and 48.6 — all as printed). Results:

| b | n | total mass | min/max of density | negative mass |
|---|---|---|---|---|
| 2 | 1024 | 1.000000 | −1.3·10⁻¹⁷ | 1·10⁻¹⁶ |
| 2 | 2048 | 1.000000 | −1.4·10⁻¹⁷ | 1·10⁻¹⁶ |
| 2 | 4096 | 1.000000 | −1.8·10⁻¹⁷ | 1·10⁻¹⁶ |
| 0.1 | 1024 | 1.000000 | −1.0·10⁻² | 1.28·10⁻² |
| 0.1 | 2048 | 1.000000 | −0.96·10⁻² | 1.40·10⁻² |
| 0.1 | 4096 | 1.000000 | −0.96·10⁻² | 1.38·10⁻² |

The ray steps Σ → 1.4Σ used as calibration give min/max ≈ −2·10⁻¹⁷ at b = 2 (both resolutions) and, at b = 0.1, −1.4·10⁻⁷ at 1024 and −10⁻¹⁶ at 2048. An independent 2-D quadrature of the inverse Fourier integral at ten points (no periodisation) agrees with the FFT values and confirms genuine negativity at b = 0.1 (e.g. −2.5·10⁻² at x = (0.5, 0)) and positivity at b = 2 at every point tested. So the remark's numbers — "nonnegative to rounding, minimum −10⁻¹⁷ of its maximum at both resolutions" and "negative mass about 10⁻²" — are reproduced exactly.

Three remarks on design. (a) At b = 0.1 the Gaussian factor along ω₁ is e^{−0.005ω₁²}, which is 0.055 at the 1024-grid's cut-off ω₁ = 24.3: the transform is truncated there, and the ray calibration shows the resulting error (10⁻⁷); the b = 0.1 figure should be quoted at the 2048 resolution, where the truncation is e^{−12}. (b) What the computation can show is stated correctly ("positivity at b = 2 is not proved"), but one consequence of the paper's own Theorem 3.5(1) is worth adding, because it is both a sharper check and the right reading: if the full-step increment at b = 2 is positive, it is not infinitely divisible (signed Lévy measure), so by Theorem 3.5(1) *some sub-step along the segment Σ + τP must have a non-positive increment*. I checked: at b = 2 the sub-steps τ: 0 → ½ and ½ → 1 are positive to rounding, but 0 → ¼, 0 → 0.1 and 0 → 0.02 have negative mass 8·10⁻⁶, 1.0·10⁻³ and 1.1·10⁻³. So the computation is consistent with the theorem, and the remark's last sentence ("the example shows why the axioms require continuity along the order") would be better supported by this sub-step observation than by H.9 alone. (c) For the full step, positivity sets in between b = 0.3 (negative mass 1.4·10⁻³) and b = 0.5 (zero to rounding); the remark's two values 0.1 and 2 are far from the threshold, which is fine for its purpose.

Reproducibility: adequate, with two things to add — that the "square of side 132" is the *spatial* square (the text's "frequency grid of a square" plus "frequencies up to π over the spacing" is only consistent on that reading) and the resolution at which the b = 0.1 negative mass is quoted.

**Remark E.5 (p. 88), reproduced** (outside my block, done for consistency since it took ten minutes). With the five-point symbol, n = 64t, the lattice increment ((1 + D_{t²I})/(1 + D_{t² diag(1+ε,1)}))^γ and its negative mass summed over the grid, the slopes in log t fitted over t ∈ {4, 8, 16, 32} are 0.0030, 0.0283, 0.1064 at γ = 1 and 0.0060, 0.0544, 0.1768 at γ = 2 — to four decimals the printed values. The description is complete. The remark's conclusion ("grows linearly in log t; a numerical finding and not proved") is the right strength: four points at a ratio of 2 cannot distinguish a·log t from a slowly bending curve, and the text claims no more.

---

## 5. The trust base

Section 1.1 (pp. 6–7) and Appendix I (pp. 103–105) are clear about the four cited facts, about which formal declarations rest on which, and about the two remarks and three figures being computations. Three points need saying more clearly.

1. **The line paper.** §1.1 says the development "requires Mathlib and the shared library ScaleSpaceCore, which makes no assumption of its own, and no formal development of the line paper", and that the line-paper statements restated in §2.2 "and the two restated inside the proof of Proposition A.3" are "proved in its released version". Yet Appendix I lists Proposition A.3 among the statements "machine-checked on Lean's logical axioms alone, with no cited fact" (p. 104), and A.3's printed proof (p. 62) uses [15, Prop. 6.6] (existence of the gauge χ) and [15, Lem. 6.3]. Either the formal proof of A.3 re-proves these inside the development (then say so, and the sentence "no formal development of the line paper" is misleading), or the formal statement of A.3 takes the gauge as a hypothesis (then A.3 as printed is not what is machine-checked). The same question arises for Theorem 2.5, listed as resting on "C2 at d = 1", whose proof in the isotropic paper reduces to the line's Theorem 2.3. A reader cannot tell from the text which of Theorem 2.3, Lemma 2.2, [15, Prop. 6.6], [15, Rem. 6.7], [15, Lem. 6.3] are inside the formal development and which are assumed. One table would settle it.

2. **The sketched statements.** "A sketched statement is machine-checked like every other" (p. 104) is a claim about the deposited development; the printed paper gives the reader only the sketch, and §3.7 above shows that one sketch (H.8(3)) does not prove its statement under one of its hypotheses and another (H.7(3)) gives an argument that does not work as written. That the formal proof may be right does not change what the reader can check. Since the prompt's instruction is to read the printed proofs as if nothing were machine-checked, the honest statement is that for the twenty listed statements the paper does not contain a proof.

3. **The review of the formal statements.** "compared with the printed ones by AI agents … and the review found none" (p. 7, p. 104), and the declaration "Beyond me, no human has reviewed it" (p. 106). This is honest, and I note it so that the editor does not read "machine-checked" as "independently verified": the correspondence between printed and formal statements rests on the author and on agents.

Nothing in this block is claimed as verified that the text elsewhere qualifies; the numerical remarks are flagged as such wherever they are cited (§3.3 p. 20, §5.1 p. 55, Appendix I p. 105).

---

## 6. Novelty and relation to prior work

Within this block the prior work named is Kelker (F.1), Urbanik and Jurek–Mason (G, 4.11), Hazod–Siebert (G), Jurek's Lie-wedge paper (G.1(4)), Rosiński and Ryznar (E.1, not my block). The attributions I can check are right in substance (Urbanik's class for one flow; Jurek's exponents of the Gaussian). I could not verify page numbers into the two books.

Missing, and relevant to Appendix G and to open problem 4:

- The random-integral representation of operator-self-decomposable laws: Jurek and Vervaat, *Z. Wahrsch. verw. Gebiete* 62 (1983) 247–262, and Sato and Yamazato, *Stoch. Proc. Appl.* 17 (1984) 73–100, who identify Urbanik's class with the stationary laws of Ornstein–Uhlenbeck-type processes ∫₀^∞ e^{−tB} dY_t. This makes the "one linear flow" row (Proposition G.1) explicit — every member is such an integral — and is the natural tool for the open converse of F.5(2) (which laws are B-self-decomposable for every B in D_α).
- Operator-scaling random fields: Biermé, Meerschaert and Scheffler, *Stoch. Proc. Appl.* 117 (2007) 312–332, where a matrix exponent E with eigenvalues of positive real part scales a field anisotropically; this is the one-flow row in the language of random fields, and the paper's remark that the row is "shape drift locked to scale" (p. 94) would place it.

On the question whether prior work treats the order and the group as a choice: within the smaller-group results nothing I know anticipates Propositions F.2 (products from diagonal covariance and axis cascades), F.5 or H.1(3), and the exponent-spread functional is new. The statement "In the scale-space and vision work read for this paper, neither the order of a linear family nor its group is posed as a choice" (p. 5) is suitably hedged by "read for this paper"; I know no counterexample.

---

## 7. Exposition and structure

- **§4.9** is a summary of three appendices and reads as a list of pointers; the one new statement (4.24) comes at its end. The "Frames", "ray column", "one flow", "similarities with Loewner", "stable order" paragraphs each compress a proposition to a sentence, and the Loewner paragraph (p. 52) cites H.5, H.6, H.2, H.8, H.7 in four lines. A journal reader will not follow it without the appendix open. Suggest: state H.1(3) and 4.24 in §4.9, keep F.2 as a stated proposition there (it carries two rows of Table 3), and reduce the rest to one paragraph with a single forward reference.
- **Table 2's similarity/Loewner cell** (p. 32) is a paragraph in a table cell citing six statements. Cut it to "non-Gaussian families exist (H.1(3)); kernels infinitely divisible with es(ψ_Σ) ≤ 4 ecc(Σ) (4.24(2)); no uniform bound in general (H.6)" and move the rest to §4.9.
- **Definitions used before given:** es, ecc, "shape-blind", "frame" are previewed in the §4.3 bullets (pp. 29–31), which is adequate. "Rank-one limit" (H.4(4)) is used in §4.9 ("the Lévy measures of the part at the thinnest apertures", p. 52) without the name; use the name there.
- **Load-bearing forward references:** §4.9 → Appendix H throughout; §5's cell count → Table 2 and the appendices. Acceptable if the appendices stay in the paper; not if they go to a supplement, in which case §5's count must be restated as what the printed paper proves.
- **Appendix D** should be a remark in §4.2 (its content is three lines). **Appendix G** lies outside the scheme by the paper's own account and could go to the supplement, with Table 2's last row and Table 3's last row kept as a remark citing it. **Appendix F**: keep F.1–F.2 (short, used by Table 3), condense F.3–F.5 to one proposition stating the parameter sets, the two families with the same isotropic member, and the three strictness examples of F.5(4). **Appendix H**: for the journal, H.1(3), H.9 and H.5(2)–(3) with H.6(1)–(2) carry the cell; H.2, H.4(4)–(5), H.7 and H.8 are refinements that the main text cites only in the Loewner cell, and can go to the supplement. **Appendix I** is right for the paper; the two-page axiom-guard printout could be shortened to the five "depends on" lines.
- **§5** repeats the introduction's three readings almost verbatim (p. 54 vs pp. 3–5); keep the "What this means for shape adaptation" paragraph and the limitations, drop the first paragraph.
- **The author/AI declaration** (p. 106) is clear and should stay.

---

## 8. Required changes

1. **p. 48 (after Theorem 4.21), p. 54 (§5, "four cells"), p. 55 (open problems 1 and 3), p. 46 (Proposition 4.20(2)), p. 32 (Table 2, cell GL(d)/stable), p. 1 (abstract):** the profile clause of Theorem 4.21(3)(c) and Proposition 4.20(2) are "if and only if" by Theorem 3.5(2) and C2(ii) (§3.1 above); the general linear stable cell is a complete description; the families along ⪯⁺_C depend on C only through β(C). Correct the sentence that calls this open, restate the cell, the open problems and the count in §5, and say in the abstract how many cells are complete. Reason: the text states as open what its own theorem proves, and the headline "completely in some cases" is under-counted.

2. **p. 102, Proposition H.8(3):** the sketch does not prove the statement under the first hypothesis when C(tI) ≠ C(Σ). Replace by the finite-signed-measure argument of §3.7 (or restrict (3) to C ≡ 0). Reason: a printed proof that does not prove the printed statement.

3. **p. 102, sketch of Proposition H.7(3):** the cone-mass comparison does not force k(r) = k(λr); use the uniqueness of the disintegration of a rotation-invariant measure over the sphere. Reason: the argument as written does not reach its conclusion.

4. **pp. 103–104 and 6–7, trust base:** state which line-paper statements (Theorem 2.3, Lemma 2.2, [15, Prop. 6.6], [15, Rem. 6.7], [15, Lem. 6.3]) are re-proved inside the formal development and which the formal proofs of Proposition A.3 and Theorem 2.5 take as hypotheses; reconcile "no formal development of the line paper" with A.3 being "machine-checked on Lean's logical axioms alone". Reason: the reader cannot tell what A.3's formal counterpart assumes.

5. **pp. 88–103 and 104, the twenty sketched statements:** for the journal, either print the complete proofs of the statements Table 2 cites (F.2–F.5, H.1, H.2, H.4–H.8) or move those cells to a clearly marked "proof in supplement" status and restate §5's count accordingly. Reason: Table 2 is the main result, and the paper must contain the proofs of what it tabulates.

6. **p. 54 (§5) and p. 32 (Table 2):** "a departure from rotation invariance at most four times the eccentricity" must say "of the non-Gaussian part (its exponent spread)". Reason: the kernel's Gaussian part is not bounded in this sense.

7. **p. 5, p. 51, p. 54:** "the price of a smaller group is shape selection" → "the affine covariance of the selection". Reason: selection by the second-moment matrix remains possible; what is lost is covariance under deformations outside the group.

8. **p. 97, Remark H.3:** say that the side 132 is the spatial square and quote the b = 0.1 negative mass at the 2048 resolution (the 1024 grid truncates the transform at 0.055 of its value). Reason: reproducibility; the 1024 ray calibration already shows the truncation error.

9. **p. 94, Proposition G.1 discussion:** "1 ≤ b ≤ 1 + α" → "1/(1+α) ≤ b ≤ 1 + α". Reason: (4.4) at d = 2 gives the symmetric range.

10. **p. 92, after Proposition F.5:** state that on the frame's shapes the condition of F.5(2) is also sufficient (D_u = e^B with B = diag(log u) ∈ D_α), so that "its converse open" refers to the extension off the frame's shapes only. Reason: as written, the reader takes a settled equivalence for an open one.

## Suggestions

1. **p. 97, Remark H.3:** add the sub-step check (a positive non-infinitely-divisible full step forces a non-positive sub-step by Theorem 3.5(1); at b = 2 the steps 0 → ¼, 0 → 0.1 have negative mass 8·10⁻⁶, 1.0·10⁻³); it is the reading the theory gives of the computation and a cheaper test than positivity.

2. **p. 51 (Table 3 caption):** say that Table 3 concerns single steps and Table 2 families, since after required change 1 the profile row reads "at least" in one and "exactly" in the other.

3. **p. 52, §4.9:** distinguish in one sentence the family of H.1(3) (trace term in the stable part, condition on κ) from that of 4.24(3) (trace term in the Gaussian part, no condition).

4. **p. 53, after Proposition 4.24:** say that no family of the Loewner cell with exponent spread growing like ecc(Σ)^1 is known (the examples have exponents below 1), so that the bound 4 ecc(Σ) is read as an upper bound and not as the behaviour.

5. **p. 93–94, Appendix G:** cite Jurek–Vervaat (1983) and Sato–Yamazato (1984) for the integral representation of B-self-decomposable laws, and Biermé–Meerschaert–Scheffler (2007) for operator scaling in random fields; the first pair is also the natural tool for open problem 4's diagonal part.

6. **p. 98, Proposition H.5(1) sketch:** replace "g nondecreasing, as k is nonincreasing in the substitution" by "g nondecreasing by self-decomposability of ν_I".

7. **p. 100, Proposition H.7(2) sketch:** state that ψ_ℓ(aτ) ≥ (a²/4)ψ_ℓ(τ) comes from ψ_ℓ(2τ) ≤ 4ψ_ℓ(τ) and monotonicity, not from a pointwise inequality of cosines (which fails).

8. **p. 43, Proposition 4.13 / p. 44, Lemma 4.14:** define the dilation ratio R for the right-continuous representative of k, so that R, β₋(k) and the completed cell of required change 1 are functions of the law.

9. **pp. 83–84, Appendix D:** reduce to a remark in §4.2; **pp. 93–94, Appendix G** and **H.2, H.4(4)–(5), H.7, H.8**: supplement.

10. **p. 54, §5, first paragraph:** drop; it repeats pp. 3–5.

11. **p. 104, Appendix I:** replace the axiom-guard listing by its five one-line summaries, and add the table of required change 4.

---

*Scripts used for §4 (written from the manuscript's descriptions alone): `work-E/h3_sign_test.py`, `work-E/h3_quadrature_check.py`, `work-E/e5_lattice_check.py`.*
