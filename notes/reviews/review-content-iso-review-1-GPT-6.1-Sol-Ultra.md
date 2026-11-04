Referee report on :codex-file-citation{path="D:\research\hemigroup-iso\review-build-iso-review-1.pdf" purpose="source"}. Page references below are to the PDF’s printed pages.

## 1. Overall assessment and recommendation

**Recommendation: major revision.** The principal mathematical arguments are substantially sound: I found no fatal error in the classification, the boundedness threshold, the centre asymptotics, the displayed lower-bound constants, or the proofs of strict filtration and Cin exclusion. The paper nevertheless requires major revision because its novelty comparison misses directly relevant classical Hankel theorems and Bessel-potential kernels; several surrounding claims are wrong; one alternative printed proof is incomplete; and the imaging interpretation overstates what central singularity and continuous differentiability imply for a filter. The quantitative separating family remains a plausible contribution, but the journal version must identify its contribution after correcting the prior-work comparison. The Lean account is unusually explicit about its limitations, but the private verification artifacts cannot presently be checked by a referee.

I read the printed arguments independently of the claimed formal verification. I also checked the worked constants and figures. My source audit has limits: I could inspect the relevant Hankel and Bessel-potential sources and the Bernstein-function statements, but could not directly inspect every cited page of Sato, Wolfe, Kanter and Watanabe, or retrieve the released line and cone papers. I therefore distinguish mathematical checks against the restated facts from exact verification of their source wording.

## 2. Headline claims against the results

### Classification

The claims on pp. 1–3 and 29 are supported by Theorem 3.6, Corollary 3.7, Lemma 3.8 and Proposition 3.10. The paper correctly declines to count the classification of the underlying laws as new. Its contribution here is the derivation from these measurement axioms, including the unspecified relabelling of scales.

The phrase “readable on its own” needs a modest qualification. Section 2 supplies sufficient statements to follow the dimensional reduction, but Theorem 2.3—the indispensable classification on the line—is an external black box. This manuscript does not independently prove its classification from its axioms without that result.

### Rate at the centre

Proposition 3.15 proves what it states on p. 25:

\[
q(s)\sim R(d,c)s^{-d}\widehat\mu(e/s),\qquad 0<c<d,
\]

and

\[
q(s)\sim(2\pi)^{-d}I(s),\qquad c=d.
\]

The explicit constant below threshold is correct. At the boundary, however, the result is an equivalence with a law-dependent truncated transform integral, together with a logarithmic lower bound. It is **not** a universal equivalence \(q(s)\sim C\log(1/s)\). The body generally observes this distinction; the abstract’s compressed description of a spike whose rate is given with its constant should preserve it.

The novelty wording on pp. 1, 4–5, 21–22 and 29 requires substantial revision. Classical Hankel results imply the whole subcritical conclusion in dimensions two and three, and the boundary conclusion in every dimension \(d\ge2\); the details appear in §6 below. The assertion that the relevant higher-dimensional antecedents consist only of small-time results and geometric-stable examples is wrong.

This does not establish that the entire all-dimensional specialization was previously printed in self-decomposable terminology. It does establish that the current comparison misses a direct antecedent in precisely the dimensions relevant to imaging.

### Boundedness threshold and bounds

Theorem 3.12 supports the claimed threshold, including \(c=d\) on the unbounded side. The qualifications “from scale zero” and “with no Gaussian part” are present in the abstract, contributions, theorem and conclusion. They are essential and should remain.

The distinction between a class-wide statement and its known ingredients is broadly reasonable. Nevertheless, “not found stated” is only a report of a bounded search, not evidence that the result is mathematically new. The threshold is a short synthesis of transform estimates, Fourier inversion and the positive-transform observation; it should be presented that way.

Proposition 3.16 supplies a genuinely displayed radius and constant. Proposition 3.17 displays its constant in terms of \(C'_\beta\), whose existence is stated in Theorem 3.12(4). Its proof makes that constant constructive, but the statement does not display a complete formula from the datum. Thus “with explicit constants” is somewhat stronger than the presentation of the upper bound. Supply the substitution, rather than require the reader to reconstruct it across pp. 26 and 40–41.

The sentence “The power cannot be improved” after Proposition 3.16 is **wrong as written**: that proposition allows \(c>d\), whereas the optimality argument invokes an upper estimate restricted to \(c\le d\). A bounded Matérn kernel with \(c>d\) has a positive constant lower bound near zero, stronger than the displayed vanishing power \(r^{c-d}\).

### Strict filtration and critical values

Theorem 3.19 proves strictness at every finite step. Lemmas A.4 and A.5 prove strict decrease of the critical values and exact order \(d^{-1/2}\). These claims are mathematically supported.

The qualitative strictness claim should, however, be separated from the quantitative analysis of this particular witness family. A short projection argument using step polar profiles proves strictness without the bump family; see §6. I did not locate an earlier publication explicitly stating this self-decomposable chain, so I would not call the historical novelty claim disproved. I would call its positioning incomplete.

The fourth “open problem” on p. 30 is not open given the paper’s own formulas:

\[
\boxed{\sqrt d\,w_d\longrightarrow\sqrt\pi}.
\]

### Cin rays

Theorem 3.20 supports the assertion that no nonzero member of a Cin ray lies in \(\mathcal A_2\), and hence none lies in a higher class.

The “building blocks” language on pp. 3 and 27 is acceptable because p. 29 explicitly explains that superpositions of excluded rays may survive. That explanation should be retained: exclusion of individual extreme rays does not exclude their mixtures.

### Imaging interpretation and “dimension enters twice”

The two mathematical effects are correctly distinguished: dimension restricts admissible exponents and changes the boundedness threshold for an admitted exponent. Corollary 3.13 supports the dimension independence of \(c\). The repeated phrase “dimension enters twice” is defensible as an organizing description, though it is repeated excessively.

The interpretation on pp. 2, 20, 22 and 30 needs correction:

* An unbounded central density describes the ideal point-source response. It does not mean that filtering an ordinary bounded image produces an infinite value.
* Since the kernel remains an \(L^1\) probability density, \(\|p*f\|_\infty\le\|f\|_\infty\) for bounded \(f\).
* Pixel or voxel measurements integrate over cells; their masses remain finite.
* A density’s value at one point can be changed without changing the law or convolution operator. The invariant statement is divergence of the radial limit and absence of any locally bounded representative.

The assertion that a derivative filter “needs \(N\) continuous derivatives” on pp. 22 and 30 is **wrong as a general necessity**. Weak derivatives can define derivative filters. For example, the one-dimensional Laplace kernel has an integrable weak first derivative despite failing to be \(C^1\). The theorem supplies a sufficient classical regularity condition; it does not establish an implementation requirement or the relevant operator bounds for derivative filtering.

### Scope and Student-t

The Student-t clause is properly conditional on p. 20, and I found no later use that silently drops its condition. The transform identity for the Gaussian inverse-gamma mixture is unconditional; its identification with an admissible cascade family is conditional.

The p. 30 “open problem” is nevertheless misleading: the text itself says that the time-causal paper cites a theorem establishing the needed self-decomposability. Not reading that theorem is an omitted verification, not an open mathematical problem.

There is also a definite endpoint error on p. 30: “the stable kernels have \(c=\infty\)” includes the Gaussian endpoint of Proposition 3.11(3). At that endpoint the Lévy profile vanishes and \(c=0\). Smoothness remains true, but for the Gaussian reason.

## 3. Mathematical correctness

### Classification, operator correspondence and polar form

I found no missing regularity hypothesis in Lemma 3.3, pp. 15–16 and 31–33. Its proof uses exactly boundedness, translation invariance, positivity and mass preservation to obtain a probability convolution kernel. The approximate-identity argument, tightness and identification of the limiting measure are valid.

The equivalence between pointwise convergence of characteristic functions and strong convergence of convolution operators on \(L^1\) is correctly proved using Gaussian smoothing and approximation. In particular, the argument does not assume that weak convergence of measures is convergence in total variation.

Lemmas 3.4 and 3.5, pp. 17 and 33–34, correctly establish that one marginal determines a rotation-invariant law and that projection preserves cascade, dilation covariance and nondegeneracy. Theorem 3.6’s necessity argument obtains self-decomposability from the actual cascade residuals. Its sufficiency and uniqueness proofs on pp. 34–35 correctly use continuity at zero and the impossibility of a nonzero exponent invariant under a fixed nontrivial dilation.

Corollary 3.7 and Lemma 3.8 then supply the operator classification and realization of every admissible pair. There is no mismatch between Definitions 3.1–3.2 and the axioms used in these proofs.

Proposition 3.10, pp. 19 and 35–37, correctly uses the polar criterion and Lévy-triplet uniqueness. Averaging directional profiles and identifying rotation-invariant measures through their radial images are legitimate. The proof respects uniqueness only almost everywhere.

One minor literal error occurs in the restated Proposition 2.7 on p. 10: \(k(x)=\varpi((x,\infty))\) selects a right-continuous representative, whereas admissibility permits arbitrary nonincreasing representatives. State that convention or write the identity almost everywhere. The exponent is unaffected.

Proposition 3.11, pp. 20 and 37, has the correct squared causal scales and Gaussian variance convention. The Student-t assumptions are used consistently.

### The threshold and Corollary 3.13

Theorem 3.12’s proof on pp. 39–41 is correct, including the boundary.

The important point at \(c=d\) is stronger than the logarithmic growth limit \(F(r)/\log r\to d\). Lemma A.3 gives

\[
\widehat\mu(\xi)\ge
e^{-13c/4-2C_k}|\xi|^{-c},\qquad |\xi|\ge1.
\]

At \(c=d\), this forces logarithmic divergence of the transform integral. Regular variation of index \(-d\) alone would not suffice: a slowly varying factor could decay enough to make the integral converge.

Lemma A.2, pp. 37–38, correctly converts a local measure bound into integrability of a nonnegative transform. The contribution outside the fixed ball tends to zero under the Gaussian test, and positivity permits monotone convergence on the Fourier side.

For \(c>d\), Fourier integrability gives a bounded continuous representative vanishing at infinity. This proves existence of that representative, not continuity of every density modified on a null set.

Corollary 3.13, pp. 23–24 and 41–42, correctly separates the Gaussian coefficient before extracting the logarithmic coefficient, covers \(c=0,\infty\), and proves dimension independence of the two coefficients.

### Radially nonincreasing density and C5

Proposition 3.14’s proof on pp. 44–45 is sound conditional on C5. It does not simply rotate lower-dimensional uniform densities as though they were densities in the ambient space.

Its decisive construction is ball mass as a function of ambient ball volume. A ray in a \(k\)-dimensional convex set contributes a function proportional to

\[
\min\{\text{constant},v^{k/d}\},
\]

which is concave because \(k\le d\). Mixtures preserve concavity; the right derivative produces a nonincreasing radial density. The final identification through radial images is also justified.

The absence of an origin atom is correctly established on p. 44 from transform decay, the Gaussian identity and dominated convergence.

The measurability argument has one underexplained step. “Analytic implies universally measurable” is correct. But the assertion that \(K\mapsto u_K\) is Borel is merely stated, including across changes in dimension. Supply a reference or the short argument by stratifying compact convex sets according to their span dimension. This is a repairable omitted justification, not a counterexample to the proposition.

I could not independently confirm the exact historical allegation about Wolfe’s use of Kanter on pp. 77–78. Even if that omission is as described, the Gaussian extension is routine: split off the Gaussian component and use closure of the symmetric-unimodal class under convolution, a property explicitly stated in [Kanter’s original abstract](https://www.researchgate.net/publication/248217414_Unimodality_and_Dominance_For_Symmetric_Random_Vectors). For this paper’s isotropic proposition, convolution of the radial nonincreasing jump density with the radial Gaussian gives a direct repair.

The paper’s identification of the affected results is otherwise consistent: only the Gaussian case of Proposition 3.14 uses C5 in that case; the no-Gaussian centre results do not. The text should provide the extension instead of leaving an impression of unresolved mathematical doubt.

### Proposition 3.15: transform, Tauberian step and constant

The printed proof on pp. 46–49 proves the printed proposition. I found no error in the passages singled out for scrutiny.

The proof does **not** mistake a radial Fourier transform for a Laplace transform. It constructs

\[
M(\lambda)=\int_{\mathbb R^d}e^{-\lambda|x|^2}\,\mu(dx),
\]

which is the genuine Laplace transform of the image probability measure under \(x\mapsto|x|^2\). Lemma A.2 expresses this through a Gaussian average of the Fourier transform.

Writing \(\chi(\rho)=\widehat\mu(\rho e)\), Lemma A.3 establishes

\[
\chi(\rho)=\rho^{-c}L(\rho)
\]

with \(L\) slowly varying. Step 1 supplies the domination required for the Gaussian integral; the proof does not rely on an unjustified exchange of a regular-variation limit and integration.

Below threshold the slowly varying normalizer is

\[
\ell(\lambda)=\lambda^{c/2}\chi(\sqrt\lambda),
\]

and the Karamata index is \(c/2>0\). The direction used is precisely the Tauberian direction stated in C7.

At the boundary, the normalizer changes to

\[
\ell(\lambda)=P(\sqrt\lambda),\qquad
P(R)=\int_0^R\chi(\rho)\rho^{d-1}\,d\rho.
\]

The proof establishes \(L(R)/P(R)\to0\), slow variation of \(P\), and equivalence of Gaussian and sharp cutoffs. Karamata is then applied with index \(d/2>0\), **not index zero**. Thus C7’s exclusion of zero index causes no gap.

The shell inequalities on pp. 48–49 prove the monotone-density step, including for any permissible nonincreasing representative. The relevant ball-mass index is \(c\) below threshold and \(d\) at threshold.

The constant is

\[
R(d,c)=
\frac{\Gamma((d-c)/2)}
     {2^c\pi^{d/2}\Gamma(c/2)}.
\]

Indeed, the Gaussian step gives

\[
I_c=2^{-c}\frac{\Gamma((d-c)/2)}{\Gamma(d/2)}.
\]

Karamata gives ball constant \(I_c/\Gamma(1+c/2)\), and the shell step multiplies this by \(c/|S^{d-1}|\), yielding exactly \(R(d,c)\).

The boundary lower bound on \(I(s)\), and hence the stated logarithmic lower bound on \(q(s)\), also follow with the printed constants.

### Bounds and Lemmas A.1–A.6

The statements and constants of Propositions 3.16–3.17, p. 26, agree with their proofs on pp. 42–43 and 46.

The lower-bound proof legitimately uses \(d\ge2\) to choose an orthogonal direction and fill the prescribed ball by the convolution of two annuli. The compound-Poisson factor, small-jump estimate and dyadic annuli yield the displayed constant

\[
c_1=\frac{\kappa_0}{4}\tau^c e^{-C_k}
       \min\{2^{c-d},4^{c-d}\}.
\]

The upper-bound comparison gives

\[
A_\beta=(2\pi)^{d/2}e^{1/2}C'_\beta.
\]

For completeness, the proof supplies the usable choice

\[
C'_\beta=(2\pi)^{-d}C_\beta
 |S^{d-1}|\,2^{(d-\beta)/2-1}
 \Gamma((d-\beta)/2),
\]

with \(C_\beta\) constructed in Theorem 3.12(1)’s proof. Displaying this would make the upper constant genuinely explicit in the statement.

The upgrade from an almost-everywhere lower bound to every positive radius uses radial monotonicity correctly. The logarithmic-order limits are correct within Proposition 3.17’s stated range.

The error is the adjoining optimality sentence, already identified: for \(c>d\), continuity and \(p(0)>0\) supply a constant lower bound, and the cited argument does not apply.

I found no mathematical error in Lemmas A.1–A.6. In particular, A.6 requires only measurable delay data and integrability before its final monotonicity clause; it is legitimately used for the nonmonotone witness delay profile.

### Filtration, Cin exclusion and the Schoenberg route

The proofs of Lemmas A.4–A.5 and Theorem 3.19 on pp. 50–54 are correct. The derivative criterion gives monotonicity exactly for \(w\le w_d\). The maximizer comparison

\[
M_{d+1}>\sqrt m\,M_d
\]

and Gamma log-convexity prove strict decrease of \(w_d\). The exclusion argument correctly handles the fact that a Lévy profile is determined only almost everywhere.

Theorem 3.20’s support and edge-cap argument on pp. 54–55 is also correct. Its projected Lévy measure has a step at the cutoff, whereas a higher-dimensional isotropic measure with the prescribed finite polar profile has edge mass \(o(\varepsilon)\). The contradiction is valid.

The alternative derivation of \(\mathcal A_\infty=\mathcal S\) on p. 54 is **incomplete as printed** in two places:

1. It invokes uniqueness of the Bernstein representation, although printed C6 states only existence.
2. It passes from dilation domination of \(m\) to \(m(dt)=k(t)\,dt/t\) with nonincreasing \(k\), without proof or reference.

Both conclusions are valid and can be supplied. For the second, one can construct the positive infinitely divisible delay law, show its residuals remain positive infinitely divisible laws, and apply the one-dimensional polar criterion. This gap does not invalidate the theorem’s main printed route, which already invokes Proposition 2.6(3); it does invalidate the claim that the alternative paragraph is a complete derivation from the printed cited facts.

### The seven cited facts

| Fact | Assessment |
|---|---|
| C1, p. 11 | The stated weighted Fourier-integrability implication is mathematically correct and used within its hypotheses. |
| C2, p. 12 | The polar criterion is used with infinite divisibility and Lévy integrability in place; the averaging argument supplies the needed isotropic form. |
| C3, p. 12 | Existence, uniqueness and converse are used appropriately, including when comparing projected or explicitly constructed Lévy measures. |
| C4, p. 12 | Self-decomposability is used to obtain infinite divisibility before applying the representation and polar criterion. |
| C5, p. 12 | The Kanter interpretation supports the printed density argument, subject to the measurability justification and source-page qualification discussed above. |
| C6, p. 13 | Composing the radial theorem with the Bernstein representation is sound; add uniqueness if the p. 54 argument is retained. |
| C7, p. 13 | The finite-measure, positive-index restriction is legitimate, and both applications satisfy it. |

There is a small but definite error in the account of C6 on pp. 6 and 13: adding \(d=0\) does not genuinely strengthen the hypothesis. Taking all frequency vectors equal to zero in dimension one already gives the dimension-zero condition \(f(0)\ge0\). The theorem remains sound; the explanation of the departure should be corrected. The relevant source statements are Theorems 13.14 and 3.2 of [Schilling–Song–Vondraček’s second edition](https://doi.org/10.1515/9783110269338).

C7’s stated departure—one direction of an equivalence under narrower hypotheses—is sound.

I found that Section 3 uses Section 2’s restatements within their stated hypotheses. I cannot certify their exact agreement with the released companion papers, or certify all the claimed original page checks, without the unavailable source texts.

### Two supposed open problems that the manuscript already settles

The critical-value question on p. 30 follows immediately from p. 52:

\[
m^m e^{-m}(1-\varepsilon_d)\le M_d\le m^m e^{-m},
\qquad \varepsilon_d\to0.
\]

Thus \(M_d\sim m^m e^{-m}\), and Stirling’s formula gives

\[
w_d\sim\frac{\sqrt{2\pi}}{2\sqrt m},
\qquad \sqrt d\,w_d\to\sqrt\pi.
\]

The first question on p. 30—the profile expression for the slowly varying factor—is likewise accessible through the paper’s own sphere-averaging argument. Define

\[
K(r)=\exp\!\left(\int_r^1(c-k_d(u))\,\frac{du}{u}\right).
\]

For the one-variable cosine exponent \(\varphi\) used in Lemma A.3,

\[
\varphi(\rho)=c\log\rho-\log K(1/\rho)
              +c\gamma_E+C_k+o(1).
\]

Moreover, the bound already proved in A.3,

\[
|\varphi(\rho t)-\varphi(\rho)|\le2c|\log t|,
\]

permits sphere averaging with \(t=|\eta_1|\), since its logarithm is integrable. Consequently

\[
L(\rho)\sim
\exp\!\left(
-C_k-c\gamma_E
-\frac c2[\psi(1/2)-\psi(d/2)]
\right)K(1/\rho),
\]

where \(\psi\) is the digamma function. This is an asymptotic expression, not an identity at arbitrary radius. It answers the question in the context in which p. 30 asks it. Replace the purported open problem by this consequence, with its short proof.

## 4. Numerical examples

The Matérn calculations on pp. 24–25 are correct. From (3.7), for \(0<\gamma<d/2\),

\[
p(r)\sim
2^{-\gamma}\pi^{-d/2}
\frac{\Gamma(d/2-\gamma)}{\Gamma(\gamma)}
r^{2\gamma-d}.
\]

Since

\[
\widehat\mu(e/r)\sim2^\gamma r^{2\gamma},
\]

the requested ratio is

\[
\frac{p(r)}
 {R(d,2\gamma)r^{-d}\widehat\mu(e/r)}
\longrightarrow1.
\]

At \(\gamma=d/2\),

\[
p(r)\sim
\frac{2(2\pi)^{-d/2}}{\Gamma(d/2)}
\log(1/r),
\]

and \((2\pi)^{-d}I(r)\) has exactly the same leading coefficient. The second requested ratio also tends to one.

Independent numerical integration of the Gaussian-gamma mixture gives the following checks:

| \(r\) | Subcritical ratio, \(d=2,\gamma=3/4\) | Subcritical ratio, \(d=3,\gamma=3/4\) | Boundary ratio \(p(r)/[(2\pi)^{-2}I(r)]\), \(d=2,\gamma=1\) |
|---:|---:|---:|---:|
| \(10^{-2}\) | 0.88651 | 0.99800 | 1.02726 |
| \(10^{-4}\) | 0.98863 | 0.999998 | 1.01308 |
| \(10^{-6}\) | 0.998863 | 0.999999998 | 1.00861 |

These computations check the normalizations; the analytic calculations establish the limits. I did not rerun the deposited scripts, which are unavailable in this review build.

Figure 1 itself, p. 21, is consistent with the formulas. The line curve tends to

\[
p_1(0)=
(2\pi)^{-1/2}\frac{\Gamma(1/4)}{\Gamma(3/4)}
\approx1.18034.
\]

Its limiting log-log slope is therefore zero. The p. 25 statement that the slopes in Figure 1 are \(2\gamma-d\) is **wrong for this bounded curve**. The plane and space slopes are correctly \(-1/2\) and \(-3/2\). Clarify the caption so its slope clause applies only to the unbounded curves.

Figure 2, p. 28, agrees with the displayed critical-value formula. Direct maximization reproduces

\[
w_1\approx12.606252,\qquad
w_2\approx5.242276,\qquad
w_3\approx3.205618.
\]

Thus the crossing of \(w=4\) between dimensions two and three is correct, as are the plotted profile behaviors. The figure illustrates the witness; it cannot prove strict decrease in every dimension or the asymptotic order. The text correctly assigns those conclusions to the lemmas.

## 5. Trust base and reproducibility

The account on pp. 5–7 and 55–59 is substantially clear and candid. It explicitly distinguishes:

* kernel checking of formal proofs;
* the seven external mathematical assumptions;
* computations and explanatory prose;
* the unformalized agreement between formal and printed statements;
* the AI-only review of that agreement.

It also discloses the absence of human review of the formal statements. These are valuable disclosures. The distinction on p. 6 between a theorem about every law with a specified transform and existence of such a law is particularly useful.

However, “verified” must consistently mean derivability of the actual Lean declarations from their actual assumptions. It does not establish the truth of the cited axioms, fidelity to the intended mathematics, agreement with the PDF, or novelty. The abstract’s final sentence should retain a compact indication of this conditional status.

Appendix B provides a useful declaration inventory, versions, build commands and selected axiom reports. It does **not presently give a referee what is needed to repeat the check**, because the repository and review tag are private. A promise of an export at release does not permit verification during review.

Before acceptance, provide a review-accessible frozen export containing the complete formal sources, dependency manifest, trust ledger, blueprint and figure scripts. Identify an immutable commit or archive checksum and a version-specific archival identifier; a concept DOI alone identifies a series, not necessarily this revision.

There is also a distinction between the guard and the paper-specific claim. On p. 56 the guard permits twelve axioms, including three from the affine companion, whereas this paper claims dependence only on its seven facts. The eight displayed reports support that claim for those eight declarations. The complete paper-specific report, or a stricter paper-specific guard, should be included for all declarations claimed here.

The AI comparison passes and formal witness examples described on pp. 7 and 57 are evidence of a review process, not a proof of semantic agreement. The paper does say this, but the evidence itself should be accessible if invoked as support. I recommend qualified human review of the principal declarations and cited axioms; another AI pass would not resolve the disclosed independence limitation.

The personal account and numerical ratio of AI to author words on p. 58 add no useful mathematical assurance. A shorter contribution and responsibility declaration would suffice.

## 6. Novelty and relation to prior work

### Missing fixed-law antecedents

The most important omission is the classical Hankel literature. [Bingham–Inoue, *An Abel–Tauber theorem for Hankel transforms*](https://eprints.lib.hokudai.ac.jp/repo/huscap/all/69120/re370.pdf), Theorems 1.1–1.2 and equation (1.4), pp. 1–2 of the preprint, supply an exact Gamma-factor equivalence and its truncated-integral boundary form.

Here is the application, rather than a claim that their paper explicitly states this self-decomposable specialization. Set

\[
\chi(t)=\widehat\mu(te),\quad
\nu=d/2,\quad f(t)=t^{(d-3)/2}\chi(t).
\]

Ball inversion expresses \(\mu(B_s)\) through the Hankel transform of \(f\). For finite \(c\), the polar-profile layer-cake representation gives \(tF'(t)\to c\) in \(d\ge2\), hence eventual decrease of \(f\) when \(c>(d-3)/2\). Theorem 1.2 then yields the printed ball constant and the shell argument yields \(R(d,c)\). This covers every \(0<c<d\) in dimensions two and three. At \(c=d\), Theorem 1.1’s error is \(O(L)\), negligible against \(\int^R L(t)\,dt/t\), yielding the printed boundary equivalence in every \(d\ge2\).

The flagship example has a still older exact antecedent. [Aronszajn–Smith, *Theory of Bessel potentials I*](https://www.numdam.org/article/AIF_1961__11__385_0.pdf), Chapter II §4, equation (4,2), p. 416, gives the power constant, logarithmic boundary and finite-centre case; equation (4,6), p. 417, identifies the transform. With their Bessel kernel,

\[
p(x)=2^{d/2}G_{2\gamma}(\sqrt2\,x).
\]

This is exactly the manuscript’s example. It does not settle novelty for the whole class, but Table 3 must include it.

### Heat-kernel comparison

The distinction from the exact small-time limit is broadly correct: [Grzywny–Ryznar–Trojan](https://arxiv.org/pdf/1606.04178), Theorem 3.9, takes a joint small-time/spatial limit; Theorem 5.7 gives comparability for sufficiently small times; its geometric-stable example includes all-time regimes. These do not directly establish the manuscript’s exact fixed-time equivalence.

But “the literature does not study one law” and “a limit \(t\to0\) says nothing about one kernel” on pp. 4 and 22 are too categorical. The first is wrong: all-time examples include fixed laws. Replace the second by “does not directly establish the required spatial asymptotic at \(t=1\).”

[Cho–Kang–Kim](https://arxiv.org/pdf/1901.08745), Proposition 2.3 and Corollary 2.13, provide further time-regime and bounded-time comparison results worth distinguishing. Positive-index regular-variation or positive lower-scaling hypotheses in [Cygan–Grzywny–Trojan](https://arxiv.org/pdf/1504.08358) and [Mimica](https://arxiv.org/pdf/1503.01600) prevent their principal results from immediately subsuming the logarithmic-exponent case.

I have not exhaustively ruled out the entire generalized-hyperbolic/type-G, Picard/Orey or local-Lévy-density literature named in the review request. I therefore do not certify a universal negative novelty claim. The concrete missing antecedents above are sufficient to require revision.

### Table 3, row by row

| Row, p. 21 | Verdict |
|---|---|
| Theorem 3.12 | Broadly fair about known ingredients; incomplete without Bessel potentials, and the boundary needs the lower bound on the slowly varying factor. |
| Corollary 3.13 | Appropriately not counted as new; the comparison is consistent with the stated logarithmic and Gaussian-coefficient limits. |
| Proposition 3.14 | Correctly identified as known; distinguish Watanabe’s characterization from this particular consequence and retain the no-atom argument. |
| Proposition 3.15 | Materially incomplete because it omits both exact Bessel-kernel asymptotics and the general Hankel antecedent. |
| Proposition 3.16 | A useful explicit radius and constant may be an addition; I located no exact predecessor for these particular constants. |
| Proposition 3.17 | Properly linked to density-average and transform estimates; its status is principally an explicit consequence, and the full constant should be displayed. |

Version-specific citations need checking. The available GRT arXiv version has a Theorem 5.8 concerning a Green function, whereas the manuscript cites the published Corollary 5.8. That is a reason to identify the version precisely, not a demonstrated erroneous citation.

### Dimension dependence

The comparison with Schoenberg and Gneiting on pp. 4 and 29 correctly distinguishes positive-definite functions from self-decomposable exponents. But the fact that Gneiting’s witnesses vanish does not make the classical dimension literature irrelevant: characteristic functions can generate self-decomposable exponents through

\[
F(r)=\int_0^r[1-\phi(u)]\,\frac{du}{u}.
\]

There is also a direct shorter proof of strictness using the paper’s own edge argument. In dimension \(d\), take \(k_d=b1_{(0,\tau)}\). If its exponent belonged to \(\mathcal A_{d+1}\), projected Lévy uniqueness would identify the prescribed \(d\)-dimensional measure. Isotropy and projected support force the higher-dimensional support inside radius \(\tau\). Its density is bounded near that edge; integration over the extra coordinate therefore makes the projected density tend to zero as \(r\uparrow\tau\). The prescribed density instead tends to \(b/(|S^{d-1}|\tau^d)>0\), a contradiction.

Thus qualitative strictness is a short structural consequence. The smooth separating family and quantitative critical values deserve their own emphasis. I did not establish that the exact strict self-decomposable chain was previously published, so this is a demand for better positioning, not an assertion of plagiarism or a proved historical priority error.

### Other positioning

The manuscript appropriately treats Sato and Hazod–Siebert as classification antecedents, Sato–Yamazato as the line-rate antecedent, and Watanabe as the shape antecedent. I found no mathematical misuse of those results as restated, but cannot certify every original page quotation.

The connection between the bounded part of the density family and the Matérn covariance parameter range is correctly explained on pp. 2 and 24. Extending the name “Matérn kernel” to singular parameters is clearly declared and should retain its distinction from a covariance function.

The scale-space comparisons on p. 4 are plausible and appropriately hypothesis-dependent. They should remain tied to the particular positivity, semigroup, separability and regularity assumptions cited; they are not blanket uniqueness assertions about every formulation of isotropic scale space.

## 7. Exposition and structure

The main obstacle is repetition, rather than absence of definitions. The abstract, questions, answers, contributions, subsection introductions and conclusion repeatedly state the same threshold and dimension-filtration claims. The journal version should remove much of that repetition.

Section 2 is useful and mostly sufficient for following the paper as an application of earlier theorems. The principal load-bearing external dependence is Theorem 2.3. The p. 54 alternative proof, the time-causal classification used to guarantee named families, and the source interpretation of C5 are the places where the manuscript still asks the reader to trust unexpanded arguments. Identify those dependencies plainly.

The notation is introduced in time, but overloaded letters and repeated redefinitions make the route harder than necessary. Definition 3.18 need not redefine \(\mathcal A_d,\mathcal A_\infty,\mathcal S\) already defined in §2.3. “Origin datum” also adds terminology for a standard isotropic Lévy triplet; a brief explanation suffices.

The division between Section 3 and Appendix A should be adjusted. Routine operator correspondence and transport calculations can remain deferred. The Gaussian–Laplace construction, the two Karamata indices and the boundary normalizer should be visible near Proposition 3.15, because they carry the principal analytical claim. Conversely, the lengthy elementary Stirling bounds and declaration inventory belong in supplementary material.

Specific material that can be reduced or removed:

* Theorem 3.12(3) largely duplicates the general threshold while adding the explicit mixture; move that mixture beside the examples.
* Proposition 3.17’s logarithmic-order conclusions follow from Proposition 3.15; retain them only if their explicit-radius aspect is explained.
* Theorem 3.19(2)’s old bound \(6+4\sqrt2\) is provenance from the cone paper, not essential to the new theorem; reduce it to a remark.
* Figure 1 is useful, after correcting its slope description; Figure 2 is useful for the quantitative witness, but unnecessary for qualitative strictness.
* Appendix B’s declaration-by-declaration inventory and selected command output can be replaced in print by a compact trust summary and a stable supplementary archive.
* The purported open problems about the profile factor, critical-value limit and unread Student-t theorem should be replaced by consequences or omitted.

A substantially shorter main text is possible without losing any proved result.

## 8. Required changes

1. **Revise the rate novelty claims and Table 3 (pp. 1, 4–5, 21–22, 25, 29)** to address the Hankel and Bessel-potential antecedents, because the current comparison misses direct fixed-law results.

2. **Restrict the lower-bound optimality claim to \(0<c\le d\) (p. 26)**, because it is false for the \(c>d\) cases admitted by Proposition 3.16.

3. **Correct the Figure 1 slope statement (pp. 21, 25)**, because the bounded line curve has limiting log-log slope zero.

4. **Rewrite the sampling and derivative-filter interpretations (pp. 2, 20, 22, 30)**, because an ideal point-response singularity does not imply infinite bounded-image measurements, and \(C^N\) regularity is not a necessary derivative-filter condition.

5. **Correct the stable-family endpoint statement (p. 30)**, because the Gaussian endpoint has \(c=0\), not \(c=\infty\).

6. **Replace the critical-value “open problem” by \(\sqrt d\,w_d\to\sqrt\pi\) (pp. 30, 52)**, because the limit follows immediately from the displayed bounds and Stirling’s formula.

7. **Replace or resolve the slowly varying-factor “open problem” (pp. 30, 38–39)**, because the existing cosine-exponent and sphere-averaging argument gives the profile expression with an explicit multiplicative constant.

8. **Complete the alternative Schoenberg proof (pp. 13, 54)** by supplying Bernstein-representation uniqueness and the dilation-domination-to-profile step, because the printed paragraph currently omits both.

9. **Justify the Borel map \(K\mapsto u_K\) and explain the Gaussian extension (pp. 6, 12, 44–45)**, because these are the unresolved explanatory steps in the printed use of C5.

10. **Correct the claim that dimension zero strengthens C6 (pp. 6, 13)**, because its condition is already implied by the dimension-one hypothesis.

11. **Recast the Student-t item as an omitted source verification (pp. 20, 30)**, because the manuscript already identifies a cited theorem that supplies the condition.

12. **Provide a frozen, review-accessible verification export and complete paper-specific axiom report (pp. 55–59)**, because the private repository prevents repetition of the advertised check.

13. **Reassess the remaining contribution and qualitative-filtration positioning (pp. 4–5, 27–29)**, because strictness has a short projection proof whereas the quantitative witness analysis is a distinct achievement.

## Suggestions

1. **Display the complete upper-bound constant in Proposition 3.17 (pp. 26, 40–41)**, so “explicit constants” can be read without reconstructing several proofs.

2. **Adopt a right-continuous profile convention in Proposition 2.7 (p. 10)**, so its pointwise tail-measure identity is literally correct.

3. **Replace the categorical small-time comparison (pp. 4, 22)** with a statement about what those theorems do not directly imply, so the scope distinction remains accurate.

4. **Move a compact outline of Proposition 3.15’s proof into the main text (pp. 25, 46–49)**, so readers can assess the central analytical claim without searching the appendix.

5. **Unify qualitative strictness and Cin exclusion through a projection lemma (pp. 27–29, 54–55)**, leaving the bump family as a separate quantitative result.

6. **Shorten the repeated questions, answers, contributions and conclusion (pp. 2–5, 29–30)**, because they restate results rather than advance the argument.

7. **Move the detailed formal inventory and elementary Stirling estimates to supplements (pp. 51–52, 55–58)**, because their full length is unnecessary in the journal text.

8. **Retain a concise AI contribution and responsibility declaration while removing the word-count ratio (p. 58)**, because the latter does not help assess correctness or reproducibility.
