# Verification of the content review, round 1 (the affine paper, `review-1`): numerics, references, novelty suggestion, exposition and length

*2026-11-03. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is checked
against the text, the blueprint and the sources before anything changes. This record verifies part
of `review-content-review-1-Gemini-4.0-Argon-High.md`: its § 4 (both items), § 6 (with the
suggestion to cite Felsberg's 2002 dissertation), § 7 (every bullet except the last item of the
first bullet, the forward reference in the proof of Theorem 3.5(3)(c), and except the abstract's
$C_\alpha$), and § 8 required changes 10 and 11 and suggestions 1, 3 and 4. The headline claims and
the mathematics are verified elsewhere. This record changes no `.tex`, `.lean` or blueprint file.*

## Inputs and conventions

- **The build.** `review-build-review-1.pdf`, 108 pages, byte-identical to `paper/main.pdf`
  (`cmp`), and `git diff review-1 HEAD -- paper blueprint` is empty: the sources are those of the
  frozen build. Page numbers are the PDF's, which are the printed ones and the report's. Text was
  read with `pdftotext -layout`; sources are cited as file:line.
- **Scripts.** The two deposited scripts were re-run in this container
  (`records/affine/check-grid-matern-cross-shape.py`, 6 s; `records/affine/check-gaussian-matern-step.py`,
  20 s). Two scripts of this verification are in `verify-round1-paper-scripts/`:
  `numerics_parameters.py` (reads the grid, stencil and box parameters off the deposited scripts by
  importing them) and `sketch_overlap.py` (how much of a body sketch repeats its full proof), each
  with its `-output.txt`. Lengths are `python3 records/affine/measure-section-pages.py paper`, run
  today, in `verify-round1-paper-scripts/measure-section-pages-review-1-output.txt`. A page holds
  about 51 lines of body text.
- **Sources.** Through the librarian's CLI: `library search --corpus`, `library search <key>`,
  `library page <key> --printed N`, `library resolve <key> --json`.
- **The author's decisions** that bear on the length items: `adr/0006` (2026-11-03: the smaller
  groups, § 4.9 and Appendices F–H, stay in this paper; no page budget), and the source comments of
  `paper/appendix-proofs.tex:1-28` and `paper/appendix-wedge-axis.tex:1-19` (Q-0290, Q-0312: which
  proofs are sketched in the body and printed whole in Appendix C).
- **Verdicts.** **CONFIRMED**: the finding holds as stated. **PARTLY**: part holds, part not
  (both are said). **REFUTED**: the paper is right, and why.
- **Classes of fix.** **safe**: adds a missing parameter, a reference identifier or a definition in
  a legend, which `adr/0003` lets a session do. **author**: changes structure, length, what is
  printed where, or what is claimed.

---

## 1. Remark E.5: design and the referee's arithmetic (report § 4.1, p. 87)

**The report.** "The analytical prediction from the continuum asymptotic of Proposition E.4(3)–(4)
… if the radial integral … is cut off at the grid spacing $a \approx 1/t$, gives a slope in
$\log t$ of $\mathcal B_2\Theta = \varepsilon/(\pi(1+\varepsilon))$." It recomputes $0.003152$,
$0.028937$, $0.106103$ against the printed $0.0032$, $0.0289$, $0.1061$ and fitted $0.0030$,
$0.0283$, $0.1064$, and for $\gamma = 2$ the values $0.0063$, $0.0579$, $0.2122$ against $0.0060$,
$0.0544$, $0.1768$, "confirming agreement to first order in $\varepsilon$ and departure at
$\varepsilon = 0.5$".

**What p. 87 prints** (`paper/appendix-orbits.tex:259-273`): "At $\gamma = 1$ and
$\varepsilon = 0.01, 0.1, 0.5$ the slopes fitted over $t \in \{4, 8, 16, 32\}$ are 0.0030, 0.0283 and
0.1064. The heuristic comparison is with 0.0032, 0.0289 and 0.1061, the values
$\varepsilon/(\pi(1+\varepsilon))$ of Proposition E.4(4) … At $\gamma = 2$ the slopes are 0.0060,
0.0544 and 0.1768, against 0.0063, 0.0579 and 0.2122, which are $\gamma$ times the index-1 values,
the first-order term in $P$; they follow it only for small $\varepsilon$."

**Check.**
- The continuum value. For $\Sigma = t^2I$, $\Sigma' = t^2\operatorname{diag}(1+\varepsilon, 1)$:
  $P' = \Sigma'^{-1/2}P\Sigma'^{-1/2} = \operatorname{diag}(\varepsilon/(1+\varepsilon), 0)$, so
  $p_1 - p_2 = \varepsilon/(1+\varepsilon)$ and Proposition E.4(4) (p. 87) gives
  $\mathcal B_2\Theta = (p_1-p_2)/\pi = \varepsilon/(\pi(1+\varepsilon))$, as printed.
- The arithmetic. $\varepsilon/(\pi(1+\varepsilon)) = 0.003152$, $0.028937$, $0.106103$;
  twice that $0.006303$, $0.057875$, $0.212207$. The printed four-digit values are these, rounded.
  The referee's arithmetic is right and agrees with the paper.
- The fitted slopes. The re-run of `check-grid-matern-cross-shape.py` prints the same six fitted
  slopes and six predictions, digit for digit. The rest of its output agrees with the deposited
  `check-grid-matern-cross-shape-output.txt` up to the sign of a tied minimum's position ((0, 1)
  against (0, −1), a symmetric tie) and to digits at the rounding floor ($10^{-15}$).
- The script's prediction is `gamma / np.pi * eps / (1 + eps)` (line 103), the blueprint's
  annotation calls the $\gamma = 2$ value $2\varepsilon/(\pi(1+\varepsilon))$, the first-order term
  (`blueprint/src/parts/05-orbits.tex:1858-1862`), and the paper says the same. Open Problem 6
  (p. 56) and p. 87 say that the lattice law is not proved.

**Verdict: CONFIRMED** (the referee's arithmetic, and the paper's numbers, are right). No action.

## 2. Remark H.3: design (report § 4.1, p. 96)

**The report.** The step from $\operatorname{diag}(1, 0.3)$ by $P = \operatorname{diag}(0.05, 0.55)$,
$h(\Sigma) = \Sigma + 2\operatorname{tr}(\Sigma)I$, so $h(\Sigma) = \operatorname{diag}(3.6, 2.9)$ and
$h(\Sigma') = \operatorname{diag}(4.85, 4.65)$; "for small $b = 0.1$ the quadrupole negative lobe
near the origin along the $x_1$-axis survives (giving negative mass $\approx 10^{-2}$), whereas for
$b = 2$ … ($\min/\max \approx -10^{-17}$)". "Nothing is concluded that a computation cannot show."

**What p. 96 prints** (`paper/appendix-similarity-loewner.tex:163-176`): $\kappa = 2$, the step,
"At $b = 2$ the computed density is nonnegative to rounding: its minimum is $-10^{-17}$ of its
maximum at two resolutions … At $b = 0.1$ it is negative, with negative mass about $10^{-2}$. These
are numerical findings, and positivity at $b = 2$ is not proved."

**Check.**
- $\operatorname{tr}\Sigma = 1.3$, $\operatorname{tr}\Sigma' = 1.9$: $h(\Sigma) = \operatorname{diag}(3.6, 2.9)$,
  $h(\Sigma') = \operatorname{diag}(4.85, 4.65)$. Right.
- The re-run of `check-gaussian-matern-step.py`: at $\kappa = 2$, $b = 2$, min/max $-1.5\cdot10^{-17}$
  ($n = 1024$ and $2048$; deposited $-1.2$ and $-1.4\cdot10^{-17}$); at $b = 0.1$, negative mass
  $1.3\cdot10^{-2}$ and $1.4\cdot10^{-2}$. The deposited output agrees to the rounding floor.
- The direction. `numerics_parameters.py` recomputes the $b = 0.1$, $n = 2048$ density with the
  deposited formula: its minimum is at $x = (-0.387, 0)$, on the $x_1$-axis. The relative step of
  the elliptical part, $h(\Sigma)^{-1/2}(h(\Sigma') - h(\Sigma))h(\Sigma)^{-1/2} = \operatorname{diag}(0.347, 0.603)$,
  widens $e_1$ least, which is where Remark E.3's mechanism puts the negative lobe. The referee's
  "along the $x_1$-axis" is right; it is not printed and need not be. Its sentence about the tails
  at large $|x|$ is the referee's reading and is not a claim of the paper.

**Verdict: CONFIRMED.** No action.

## 3. Remark E.5: the discretization is not stated (report § 4.2, first item; required change 10)

**The report.** "the periodic grid size $N \times N$ of $\mathbb Z_N^2$ is not stated, and the exact
stencil weights of 'the nine-point discretization of $\nabla\cdot S\nabla$' are not given (for
diagonal $S = \operatorname{diag}(s_1, s_2)$, standard central differences give a 5-point stencil
unless a specific isotropic-anisotropic 9-point weighting is chosen)."

**What p. 87 prints.** "A script deposited with the paper computes it by the fast Fourier transform
on $\mathbb Z^2$. It uses the nine-point discretization of $\nabla\cdot S\nabla$, the Matérn family
of index $\gamma$ built from it, and the step from $t^2I$ to $t^2\operatorname{diag}(1+\varepsilon, 1)$,
with $t$ the aperture in grid spacings." No grid size, no weights, no formula for the lattice
Matérn symbol, no file name. The data-availability paragraph (`paper/declarations.tex:16-20`) says
the scripts are deposited, by remark, not by name.

**What the script does** (`check-grid-matern-cross-shape.py:13-23, 35-60`).
- The symbol is
  $D_S(\theta) = a(2-2\cos\theta_1) + c(2-2\cos\theta_2) + b_+(2-2\cos(\theta_1+\theta_2)) + b_-(2-2\cos(\theta_1-\theta_2))$,
  $a = S_{11} - |S_{12}|$, $c = S_{22} - |S_{12}|$, $b_\pm = \max(\pm S_{12}, 0)$, the generator of a
  random walk on $\pm e_1, \pm e_2, \pm(e_1+e_2), \pm(e_1-e_2)$, for diagonally dominant $S$. The
  lattice Matérn law has the symbol $(1 + D_S)^{-\gamma}$, and the increment
  $((1 + D_S)/(1 + D_{S'}))^{\gamma}$.
- **For the steps of Remark E.5 the stencil is five-point.** $S = t^2I$ and
  $S' = t^2\operatorname{diag}(1+\varepsilon, 1)$ are diagonal, so $b_+ = b_- = 0$ at every point
  computed (`numerics_parameters-output.txt`, the rates of $S$ and $S'$). The diagonal neighbours
  carry weight only in the script's "turning step", which the paper does not report. "Nine-point" is
  right for the scheme and wrong for the computation printed. The blueprint's annotation says
  "nine-point random-walk discretization" (`blueprint/src/parts/05-orbits.tex:1847`); the paper
  dropped "random-walk".
- The torus is $n \times n$ with $n$ the least power of 2 at or above
  $\max(256, 40\,\lambda_{\max}(S')^{1/2})$: $n = 256, 512, 1024, 2048$ for $t = 4, 8, 16, 32$, so
  $n = 64t$ for every $\varepsilon$ of the remark.

**Verdict: CONFIRMED**, and sharper than the report: the printed "nine-point" is the five-point
stencil for the steps computed.

**Fix (safe; paper-side, `paper/appendix-orbits.tex:261-263`, about 3 lines in an appendix).** In
place of "It uses the nine-point discretization of $\nabla\cdot S\nabla$, the Matérn family of
index $\gamma$ built from it, …", for instance: "It uses the random-walk discretization
$D_S(\theta) = a(2-2\cos\theta_1) + c(2-2\cos\theta_2) + b_+(2-2\cos(\theta_1+\theta_2)) + b_-(2-2\cos(\theta_1-\theta_2))$
of $\langle\theta, S\theta\rangle$, with $a = S_{11} - |S_{12}|$, $c = S_{22} - |S_{12}|$ and
$b_\pm = \max(\pm S_{12}, 0)$, which for the diagonal $S$ used here is the five-point stencil, the
lattice Matérn symbol $(1 + D_S)^{-\gamma}$, and the $n \times n$ torus with $n = 64t$." Optionally
name the file, `check-grid-matern-cross-shape.py`, here or in the data-availability paragraph. The
blueprint annotation (`05-orbits.tex:1847`) can say "five-point for these diagonal steps" in the
same pass; it is an annotation, not a statement.

## 4. Remark H.3: the box and the resolutions are not stated (report § 4.2, second item; required change 10)

**The report.** "the spatial/frequency box size and the two grid resolutions at which the FFT was
evaluated are not stated."

**What p. 96 prints.** "A script deposited with the paper computes its would-be increment by the
fast Fourier transform. … at two resolutions". No box, no resolution.

**What the script does** (`check-gaussian-matern-step.py:28-45, 59-63`). An $n \times n$ grid
centred at the origin, side $L = 60\cdot\text{scale}$ with
$\text{scale} = \max(\lambda_{\max}(h(\Sigma')), 2b\lambda_{\max}(P))^{1/2}$, and $n = 1024$ and
$2048$. For the printed step, $\kappa = 2$ and both $b = 0.1$ and $b = 2$, the scale is
$\sqrt{4.85} = 2.202$, so $L = 132.1$, spacing $0.129$ and $0.065$, and the frequencies run to
$\pi/dx = 24.3$ and $48.7$ (`numerics_parameters-output.txt`). The density is the inverse FFT of
$e^{-b\langle\omega,P\omega\rangle}(1 + \langle\omega,H\omega\rangle)/(1 + \langle\omega,H'\omega\rangle)$
on that grid, divided by $dx^2$.

**Verdict: CONFIRMED.**

**Fix (safe; paper-side, `paper/appendix-similarity-loewner.tex:166`, 1–2 lines).** After "computes
its would-be increment by the fast Fourier transform", for instance: "on a square of side
$60\,\lambda_{\max}(h(\Sigma'))^{1/2} \approx 132$ centred at the origin, sampled at $1024^2$ and
$2048^2$ points (frequencies up to about 24 and 49)", and "at these two resolutions" for "at two
resolutions". Optionally name the file, `check-gaussian-matern-step.py`.

## 5. Felsberg's anisotropic Poisson scale space (report § 6.1, fourth bullet)

**The report.** "You might also mention Felsberg and Sommer's work on anisotropic Poisson scale
spaces (e.g., Felsberg's 2002 Kiel dissertation, where extending the Poisson kernel anisotropically
along one direction while keeping the orthogonal scale fixed is discussed heuristically); Theorem
3.7 and Proposition 4.7(3) rigorously explain why such a rank-1 step has no positive convolution
increment for the elliptical Poisson orbit."

**What the paper prints.** Felsberg is cited only as a co-author of Duits, Felsberg, Florack and
Platel (p. 4, `paper/01-introduction.tex:316-317`, "easily accounted for", p. 494). The Poisson scale
space is named six times (`04-classical.tex:706`, `05-landscape.tex:48`, `05-orbits.tex:147, 208`,
`05-table.tex:31`, `05-wedges.tex:81`), and the one place that credits it, § 3.5 (p. 24,
`04-classical.tex:705-706`), credits it to Duits et al. as their $\alpha = \tfrac12$. `paper/references.bib`
has no Felsberg–Sommer entry.

**The sources.**
- **The dissertation is not held.** `library search --corpus` for "Felsberg" returns three items,
  `duits2003scale`, `felsberg2001scale` and `felsberg2004monogenic`; searches for "structure
  multivector", "low-level image processing", "anisotropic Poisson", "Poisson scale-space", "Kiel"
  and `--type thesis` return no thesis; it is not in the acquisition queue (`library acquire list`).
  Nothing is asserted here about its content.
- **`felsberg2004monogenic`** (JMIV 21, 2004). `library search … "anisotrop"`: p. 7 puts
  tensor-valued diffusivity and anisotropic diffusion "out of the scope of this paper". The
  positioning note `READING-alpha-scale-spaces-positioning.md` (pp. 6, 24, Note 2) records that a
  matrix scale is out of their scope. No anisotropic Poisson kernel there.
- **`felsberg2001scale`** (DAGM 2001, LNCS 2191), read at the page, p. 130 (`library page
  felsberg2001scale --printed 130`), the conclusion: "The new approach can easily be extended to
  anisotropic denoising by introducing a 2 × 2 scaling matrix instead of the real scale parameter
  s. The behaviour for low-energy edges is supposed to be better in that case." That is a Poisson
  kernel indexed by a $2\times2$ matrix, proposed in one sentence with no analysis. It is a general
  matrix, not the one-direction step the referee describes; the existing reading note,
  `READING-felsberg2004monogenic.md`, read only pp. 124–125 of this paper.
- **The referee's mathematical claim** is right for the held sentence: the elliptical Poisson
  orbit is the stable orbit $S_1(\Sigma)$, $g(u) = u^{1/2}$, so Theorem 3.7 (p. 21) excludes a
  probability increment on every rank-deficient step from a definite $\Sigma$, and
  Proposition 4.7(3) bounds the anisotropy a full-rank step can gain, $(t_2/t_1)^{2/3}$ in the plane
  (p. 36, `05-orbits.tex:146-148`). The paper already states both for the Poisson kernel; it does
  not say whose proposal the anisotropic Poisson kernel is.

**Bearing on the prior-art record.** `PRIOR-ART-positioning.md`, row C, says "No non-Gaussian
kernel indexed by a covariance matrix in any source read", with Felsberg–Sommer pp. 6–7 among the
sources. `felsberg2001scale`, p. 130, proposes one (without analysis). The paper prints no claim of
that kind (`adr/0006` item 6 claims no such novelty), so no printed sentence is wrong, but the
record's row is incomplete.

**Verdict: PARTLY.** The dissertation is not held and its content is unverified. The point behind
the suggestion holds through a held source: Felsberg and Sommer proposed the matrix-indexed Poisson
kernel (2001, p. 130), and the paper, which prices exactly that extension, cites neither of their
papers. The affine paper also credits the Poisson scale space to Duits et al. alone, the gap that
round 2 of the isotropic paper fixed there (`paper-iso/02-line-papers.tex:223`, `felsberg2004monogenic`,
Thm. 1, p. 7).

**Fix (author: a new citation and sentence).** (a) A reading note
`records/affine/READING-felsberg2001scale-anisotropic.md` for p. 130 first (the article's rule: a
source is read at the page and recorded before the statement that rests on it). (b) In § 3.5
(`04-classical.tex:706`), credit the Poisson scale space to Felsberg and Sommer
(`felsberg2004monogenic`, Thm. 1, p. 7) beside Duits et al. (c) Where the Poisson kernel's speed
limit is stated (`05-orbits.tex:146-148`, or § 1 beside the "easily accounted for" sentence,
`01-introduction.tex:316-318`), one sentence: Felsberg and Sommer proposed a $2\times2$ scaling
matrix in place of the scalar scale (`felsberg2001scale`, p. 130), and Theorem 3.7 and
Proposition 4.7(3) say which of its steps cascade. Two bib entries enter the subset. (d) A line in
`PRIOR-ART-positioning.md` row C, or a successor record, noting p. 130. (e) If the author wants the
dissertation, a librarian request (`library acquire request`); it should not be cited unread.

## 6. The rest of § 6: positioning and the "order and group as a choice" claim (report § 6.1, other bullets; § 6.2)

**The report.** Every other bullet of § 6.1 says "Accurately positioned/contrasted/credited"; § 6.2
answers "Yes, with the phrasing the author uses on p. 5".

**Check.** The page anchors the report names exist where it says: Iijima via Weickert et al. and
Pedersen–Sato on p. 5 (lines 12, 43), the Lie-semigroup "Prior art" paragraph on p. 35 (Lawson,
Hilgert–Hofmann–Lawson), the operator-self-decomposable "Prior art" on p. 41 (Urbanik). The quoted
sentence is p. 5, `01-introduction.tex:319-320`, "In the scale-space and vision work read for this
paper, neither the order of a linear family nor its group is posed as a choice." The held
`felsberg2001scale` sentence of item 5 does not pose an order or a group as a choice, so it does not
touch this sentence. The substance of the positioning is the prior-art verifier's.

**Verdict: CONFIRMED** (assessments, no finding). No action.

## 7. Proposition 4.20 has load-bearing references to Appendix H (report § 7.1, second bullet; required change 7)

**The report.** "its preamble says 'use the functionals es, $\mathcal M_s$, $T_s$ and cond of
Proposition H.5', Clause (3) states that $(\mu_\Sigma)$ 'is a family as in Proposition H.4', and
Clause (4) says 'with $\psi_\Sigma$ as in Proposition H.4'."

**What pp. 46–47 print.** All three, verbatim (`paper/05-orbits.tex:833-835, 865-868, 871-872`,
a shared statement, `% shared with blueprint prop:similarity-stable-order-families`). The paragraph
before it (p. 46) defines es and says the other functionals "are defined with Proposition H.5 in
Appendix H". What H.4 adds to clause (3), which already names the symmetric triplet
$(C(\Sigma), L_\Sigma, 0)$, is similarity covariance and
$\psi_\Sigma(\omega) := \int(1 - \cos\langle\omega, x\rangle)\,L_\Sigma(dx)$ (p. 96). H.5 defines
$\mathcal M_s(L) := \int(|x|^2\wedge s^2)\,xx^{\mathsf T}/|x|^2\,L(dx)$, $T_s := \operatorname{tr}\mathcal M_s$
and $\operatorname{cond}M := \lambda_{\max}(M)/\lambda_{\min}(M)$ (p. 97). **A further point:** $T_s$
is named in the preamble and used nowhere in clauses (1)–(5).

**Verdict: CONFIRMED**, with the unused $T_s$ added.

**Fix (safe in content; made at the blueprint node and re-transcribed, `adr/0004`; about 3 lines).**
In the preamble, define $\operatorname{cond}$ and $\mathcal M_s$ inline (two short formulas) and drop
$T_s$; in clause (3), replace "a family as in Proposition H.4" by "covariant under the similarities,
$(\sqrt c\,Q)_*\mu_\Sigma = \mu_{cQ\Sigma Q^{\mathsf T}}$"; in clause (4), define $\psi_\Sigma$ by its
integral. The claim is unchanged. Required change 7 asks for the same; the verifier of the
headline claims may hold it too, and one fix serves both.

## 8. Table 2 and its legend use terms defined later (report § 7.1, third bullet; suggestion 3)

**The report.** "Table 2 (p. 31) and its legend (pp. 28, 30) use $C_\alpha$, $K_\alpha$,
$R(\lambda)$, $\beta_-(k)$, $\operatorname{es}(\psi_\Sigma)$, and $\operatorname{ecc}(\Sigma)$ ten to
fifteen pages before they are formally defined … the formulas for $R(\lambda)$, $\beta_-(k)$, and
$C_\alpha$ should be stated in one line each in the bullet list of § 4.3."

**What pp. 28–31 print, term by term** (`paper/05-table.tex:22-51`).

| Term | In a Table 2 cell? | In the legend | Defined | Verdict |
|---|---|---|---|---|
| $\le_\alpha$ (the column) | header | formula: $\lambda_{\min}(M)^{d+\alpha} \ge \det M$ (p. 28) | there | defined |
| $C_\alpha$ | no | "$C_\alpha$ of the paragraph after the table (Proposition 4.12)" (p. 28) | formula p. 35 (§ 4.4) and Prop. 4.12, p. 41; the paragraph after the table (p. 30) names the chain and gives no formula; p. 32 gives $k = \alpha/(\alpha+2)$ for $d = 2$ only | **the pointer does not deliver** |
| $K_\alpha$ | yes (diagonal row) | in words: "the set of matrices $B$ for which $S_\alpha(I)$ is its own image under $e^{-tB}$ convolved with a residual, for every $t$" (p. 30) | Prop. 4.10, p. 40 | defined in the legend |
| es | yes | "the least $K \ge 1$ with $\psi(Q\omega) \le K\psi(\omega)$ for every $Q \in O(d)$" (p. 30) | again p. 46 | defined in the legend |
| ecc | yes | "the ratio of its extreme eigenvalues" (p. 30) | again p. 46 | defined in the legend |
| $R(\lambda)$ | yes (GL row, stable column) | named only: "the dilation ratio $R$ of a Lévy profile $k$" (p. 30) | Prop. 4.13, p. 42 | **not defined** |
| $\beta_-(k)$ | yes | named only: "its lower exponent $\beta_-(k)$" (p. 30) | Lemma 4.14(3), p. 43 | **not defined** |

"Lévy profile" is not defined in the legend either; Proposition 4.13 (p. 42) takes $k$ nonincreasing
with Lévy density $k(|x|)|x|^{-d}$.

**Verdict: PARTLY.** Right for $R(\lambda)$, $\beta_-(k)$ and the profile $k$, which the legend
names without defining, 11–12 pages before Proposition 4.13 and Lemma 4.14; right for $C_\alpha$,
whose legend pointer leads to a paragraph without its formula (it is not used in a cell). Wrong for
$K_\alpha$, es and ecc, which the legend defines; and the distance is 4–12 pages, not 10–15.

**Fix (safe: definitions in a legend; `paper/05-table.tex`, the bullets at lines 25-34 and 49-50,
not shared; about 4 lines).** In the stable-order bullet, replace "$C_\alpha$ of the paragraph after
the table" by "$C_\alpha := \{X \in \mathrm{PSD}(d) : (d+\alpha)\lambda_{\min}(X) \ge \operatorname{tr} X\}$".
In the profile bullet: "a Lévy profile is a nonincreasing $k \ge 0$ on $(0,\infty)$, the law having
Lévy density $k(|x|)|x|^{-d}$; its dilation ratio is $R(\lambda) := \inf_{r:\,k(r)>0} k(r/\lambda)/k(r)$,
$\lambda \ge 1$, and its lower exponent $\beta_-(k) := \inf_{\lambda>1}\log R(\lambda)/\log\lambda$."

## 9. Self-containment with respect to the earlier papers (report § 7.2, first bullet)

**The report.** "§ 2 (pp. 7–11) and the two restated lemmas inside the proof of Proposition A.3
(p. 62) make the manuscript self-contained with respect to [15], [16], and [17]."

**Check.** § 2 is 7.39 pages (measured), restating the line paper (§ 2.2), the isotropic paper
(§ 2.3) and the cited facts (§ 2.4); § 1.1 says the same of the two lemmas in Proposition A.3
(`01-introduction.tex:432-434`).

**Verdict: CONFIRMED** (an assessment). No action.

## 10. References [15]–[17] carry no identifier (report § 7.2, second bullet; required change 11)

**The report.** "References [15], [16], and [17] are cited only as 'Daniel Fagerström. Spatial scale
space from hemigroup axioms: …, September/October 2026. version 0.1', with no journal, preprint
server (arXiv ID), DOI, or URL. A reader cannot find them."

**What p. 106 prints.** "[15] Daniel Fagerström. Spatial scale space from hemigroup axioms:
characterization of the kernels on the line, September 2026. version 0.1." [16] the isotropic paper,
October 2026, [17] the cone paper, September 2026, each "version 0.1", nothing else.

**Check.**
- **The records hold DOIs.** `paper/references.bib:165-200`: `fagerstrom2026spatial` doi
  10.5281/zenodo.22761632, `fagerstrom2026cone` 10.5281/zenodo.22864170, `fagerstrom2026isotropic`
  10.5281/zenodo.23357468, each with publisher Zenodo. The librarian agrees (`library resolve … --json`:
  type `preprint`, the same DOIs, and the verification-export repository and tag in the note; the
  isotropic record also carries the concept DOI 10.5281/zenodo.23357467). `README.md:14-15` gives
  the isotropic paper's version and concept DOIs; `paper/main.tex:37-43` gives the concept DOIs of
  all three.
- **The style drops them.** `paper/main.tex:185` is `\bibliographystyle{plain}`, which prints no
  `doi` field and no `publisher` for `@misc`. So none of the 44 of 58 references that have a DOI in
  the subset prints it, not only [15]–[17].
- **Precedent.** The isotropic paper had the same defect and fixed it by `plainurl`
  (`CITATION-AUDIT-paper-iso-fixes.md`, item 2; `paper-iso/main.tex:116`). A scratch `bibtex` run
  of this paper's `main.aux` with `plainurl` (TeX Live's `urlbst`) prints
  "doi:10.5281/zenodo.22761632" etc. for [15]–[17] and a DOI for all 44, with two warnings
  ("empty publisher" in `lindeberg1994scale` and `linnik1977decomposition`, which `plain` also has).

**Verdict: CONFIRMED** for the printed list. The fix is the paper's, not a bibliography record's:
the librarian's records are complete.

**Fix (safe: a reference identifier; `paper/main.tex:185`, one line).** `\bibliographystyle{plainurl}`,
as in the isotropic paper; about 44 more lines in the references, outside the main text (+0.9 page),
then a rebuild. One point for the author: the records carry the **version** DOIs, while the
repository's rule ("cited as its released version (concept DOI, …)", `CLAUDE.md`) and the comment at
`main.tex:37-43` speak of concept DOIs. The version DOI with "version 0.1" pins the statement
numbers the paper cites, which is what the rule asks; if the concept DOI is wanted in print, that is
a change to the librarian's records (the `doi` field), not to the paper.

## 11. The "four-fold narrative repetition" (report § 7.3, first sub-bullet; suggestion 1, first part)

**The report.** "Every result is narrated in the Abstract (p. 1), at length in § 1 (pp. 1–6), again
in § 4.3 (pp. 28–32), again in the prose before and after each statement in §§ 4.4–4.9 (pp. 32–54),
and a fifth time in § 5 (pp. 54–55). Merging the preview in § 4.3 with § 1 and trimming § 5 will save
8–10 pages immediately."

**Measured** (`measure-section-pages-review-1-output.txt`; paragraph lines from the PDF).

| Part | Pages | Of which a narration of results |
|---|---|---|
| Title and abstract | 0.56 | the abstract, ~19 lines |
| § 1 before § 1.1 | 5.75 | "The classification", "The general linear group with the Loewner order", "… from the rays to the Loewner order", "Smaller groups": 19 + 16 + 28 + 12 = ~75 lines, ~1.5 pages. The rest is the question ("What is an affine scale space?", "The two choices", ~55 lines), scope, the two relations to the literature (~47 lines) and the plan |
| § 1.1 | 0.84 | none (the trust base) |
| § 4.3 | 3.40 | ~1.25 pages of prose (~64 lines), of which the legend is ~25 lines that the table needs and "The inclusions", "The isotropic members", "The general linear row along the chain" ~35 lines; Table 2, one page (p. 31); Figure 2, one page (p. 29), which belongs to § 4.2's Lemma 4.1 and lands here as a float |
| § 5 before § 5.1 | 0.99 | the summary paragraph, ~16 lines; the shape-adaptation paragraph and the limitations are not repetition |
| § 5.1 | 1.40 | none (the open problems) |

**Verdict: PARTLY.** The repetition is there: the results are summarized in the abstract, § 1, § 4.3
and § 5, which is the standard frame of a long paper, and `adr/0006` item 3 makes Table 2 the main
result that § 1 reports. The saving is not. Everything in § 4.3 and § 5 that is a narration of
results is about 1 page (the 35 lines of § 4.3 after the legend, the 16 of § 5); with § 1's 1.5
pages shortened as well, 2–2.5 pages. "8–10 pages" would need the table, the figure, the legend or
the open problems to go, which the report does not propose. The narration "before and after each
statement in §§ 4.4–4.9" was not measured.

**Fix (author: length and what is printed where).** If the author wants it: fold "The inclusions",
"The isotropic members" and "The general linear row along the chain" (§ 4.3) into § 1's
"The classification", keeping the legend with the table (−0.5 to −0.7 page); shorten § 5's summary
paragraph to two sentences that point to § 1 (−0.2 page).

## 12. Sketches in the body and full proofs in Appendix C (report § 7.3, second sub-bullet; suggestion 1, second part)

**The report.** "Theorem 4.21 has a 1.5-page proof sketch in § 4.7 (pp. 49–50) and a 3-page complete
proof in Appendix C.4 (pp. 80–82) that re-proves parts of Theorem 4.3(4) and Proposition 4.12(1) from
scratch. Similarly, Lemma 4.8 and Proposition 4.13 have half-page sketches in § 4.6 (pp. 39, 43) that
are 80% identical to their full proofs in Appendix C.3 (pp. 77–78). Print each proof once."

**Measured** (`sketch_overlap-output.txt`; words after stripping LaTeX).

| Statement | Sketch | Full proof | Sketch's 4-grams found in the full proof | Sketch words aligned in order |
|---|---|---|---|---|
| Lemma 4.8 | 124 words (~0.2 p., p. 39) | 366 words (C.3) | 21 % | 53 % |
| Proposition 4.13 | 231 words (~0.4 p., p. 43) | 489 words (C.3) | 18 % | 55 % |
| Theorem 4.21 | 620 words (~1.1 p., pp. 49–50) | 1697 words (C.4, 2.32 p.) | 22 % | 31 % |

**Check.**
- The double printing is deliberate. `paper/appendix-wedge-axis.tex:1-19` (Q-0312, review flags 3
  and 30): the review of that round asked for complete proofs of the main theorem and of every
  statement it spends; for `lem:stable-tail`, `prop:orbit-step-cone` and `thm:wedge-axis` "the main
  text keeps its sketch, with a pointer here". § 1.1 states the convention for "Sketch".
- "80 % identical" is refuted. The sketches are compressions to a third or a quarter of the length,
  with about a fifth of their 4-grams taken verbatim: the same steps, said shorter.
- C.4 does re-derive that $\preceq^+_C$ is a GL($d$)-invariant partial order (the paragraph "The
  orders", about 0.8 page, pp. 80–81), saying "Its antisymmetry is that of Theorem 4.3(4), and the
  causal curves give it directly". The source comment says why (`appendix-wedge-axis.tex:776-778,
  794-795`): the author's decision on W2F-1, the "entry-free route", proves the orders "without C4".
  Citing Theorem 4.3(4) instead, as suggestion 6 asks, would put the Gel'fand–Naimark–Lidskii fact C4
  into Theorem 4.21's trust base, which Appendix I's ledger would then have to record.

**Verdict: PARTLY.** The double printing is real (about 1.7 pages of body sketches for proofs printed
whole in Appendix C) and is a decision of Q-0312; the "80 %" is refuted; the re-derivation in C.4
is real and deliberate, and the shortening the report proposes has a cost in the trust base.

**Fix (author).** Options with their savings: drop the three sketches for one-sentence pointers
(−1.5 page of main text; the main text would then print no argument for its headline theorem
4.21); or keep the sketch of Theorem 4.21 and drop the two short ones (−0.5 page). Shortening C.4 by
citing Theorem 4.3(4) saves about 0.6 page and adds C4 to Theorem 4.21's dependencies; that is
suggestion 6, outside this record.

## 13. Duplicate propositions (report § 7.3, third sub-bullet; suggestion 4)

**The report.** "Proposition 3.4(3) (p. 18) and Proposition 4.5 (p. 36) state virtually the same
characterization of (GL($d$), rays); Proposition E.2 (p. 85) is just the $\gamma = 1$ special case of
Proposition 4.17 (p. 45)." Suggestion 4: merge 4.5 into 3.4(3); fold E.2's formula into 4.17.

**Proposition 3.4(3) against Proposition 4.5, exactly.**

| | Proposition 3.4(3), p. 18 | Proposition 4.5, p. 36 |
|---|---|---|
| Setting | a (GL($d$), $W$)-cascade family of the scheme, $W$ the ray order: axioms (K1)–(K4) on PSD($d$), with continuity | probability measures $(\mu_\Sigma)_{\Sigma\in\mathrm{PD}(d)}$, no scheme |
| Hypotheses | the scheme's | (R1) GL($d$)-covariance on PD($d$); (R2) a cascade along the ray of $I$ only |
| Conclusion | $\mu_\Sigma = (\Sigma^{1/2})_*\mu_I$ on all of PSD($d$), $\mu_I$ rotation invariant, self-decomposable, $\ne\delta_0$; $\widehat\mu_\Sigma = \vartheta(\langle\omega,\Sigma\omega\rangle)$ | the same on PD($d$), and the cascade along every ray with the increment $(\Sigma^{1/2})_*\rho_\lambda$ |
| Converse | each such $\mu_I$ is the isotropic member of **exactly one** family | each such $\mu_I$ gives a family satisfying (R1), (R2) |
| Proof | C.2, about 0.45 page for (3) | p. 36, about 14 lines |

The paper says so itself (p. 18): "Clause (3) is read again without the scheme in § 4.5, as
Proposition 4.5. The scheme adds the boundary of PSD($d$), by continuity, and the uniqueness of the
family." And C.2's proof of (3) repeats 4.5's argument for the orbit form ("this is the orbit form …
of Proposition 4.5, obtained here from (b) alone").

**Proposition E.2 against Proposition 4.17.** E.2 (p. 85): $d \ge 2$, index 1,
$\Sigma \le \Sigma'$ in PD($d$), $\Sigma' \ne \Sigma$: a positive finite increment exists iff
$\Sigma' = \lambda^2\Sigma$, $\lambda > 1$, "and then $\rho$ is the probability measure
$\lambda^{-2}\delta_0 + (1-\lambda^{-2})\mu_{\Sigma'}$". 4.17 (p. 45): $d \ge 1$, every $\gamma > 0$,
no order hypothesis, the same equivalence, $\rho = (\Sigma^{1/2})_*\nu_\lambda$. E.2's proof begins
"By Proposition 4.17 at $\gamma = 1$, which needs neither $d \ge 2$ nor $\Sigma \le \Sigma'$" and then
names $\rho$; the lead of E.2 says "this is Proposition 4.17 at index 1, with the increment named".

**Verdict: PARTLY for 3.4(3)/4.5**: the conclusion is the same on PD($d$), but the hypotheses differ
(4.5 asks much less: no scheme, one ray) and 3.4(3) adds the boundary and uniqueness; the paper
already says this, and the overlap is in the proofs. **CONFIRMED for E.2/4.17**: E.2 is 4.17 at
$\gamma = 1$ with stronger hypotheses than it needs, plus an explicit $\rho$, and the paper says so.

**Fix (author: structure; blueprint nodes `prop:gw-ray-families`, `prop:ray-families`,
`prop:matern-cross-shape`, `prop:matern-steps`).** (a) Keep 4.5 as the statement and prove 3.4(3)
from it in two lines (boundary by (K2)-continuity, uniqueness by 3.4(2)), deleting the repeated
orbit argument of C.2 (−0.3 page of appendix); or state 3.4(3) once and make 4.5 a remark (−0.5
page of main text, but § 4.5 loses its scheme-free statement, which the report's own reader of § 4
uses). (b) Fold E.2's formula into 4.17 as a sentence ("at $\gamma = 1$, $\rho = \lambda^{-2}\delta_0 + (1-\lambda^{-2})\mu_{\Sigma'}$"), and let Remark E.3 refer to 4.17 (−0.3 page of
appendix). Both change which blueprint nodes print where.

## 14. Moving Appendices D–H out, and the 45–50 page target (report § 7.3, fourth sub-bullet; suggestion 1)

**The report.** "At 108 pages (55 pages of main text and 48 pages of appendices) … Moving the
detailed 20-page exploration of incomplete cells in Appendices D–H to Electronic Supplementary
Material (while keeping Propositions F.2 and H.1(3) in the main text) would reduce the article to a
sharp, cohesive 45–50 pages." Suggestion 1: "from 108 pages to 45–55 pages".

**Measured** (pages, `measure-section-pages-review-1-output.txt`).

| Part | Pages | | Part | Pages |
|---|---|---|---|---|
| Title, abstract | 0.56 | | A Operators and kernels, the scheme | 9.91 |
| § 1 (with § 1.1, 0.84) | 5.75 | | B Deferred proofs, § 4 | 3.03 |
| § 2 Earlier papers | 7.39 | | C The complete proof of the GL row | 13.18 |
| § 3 Scheme, classical theory | 11.05 | | D Orientation-preserving group | 1.09 |
| § 4.1–4.2 | 2.45 | | E Step set: two further results | 3.72 |
| § 4.3 At a glance (with Table 2, Fig. 2) | 3.40 | | F Smaller groups | 5.19 |
| § 4.4 Invariant wedges | 3.57 | | G One linear flow | 1.37 |
| § 4.5 GL along rays | 1.45 | | H Similarities with Loewner | 8.80 |
| § 4.6 Step set of an orbit | 10.93 | | I Verification | 1.88 |
| § 4.7 GL row along the chain | 2.19 | | Back matter | 0.64 |
| § 4.8 Shape adaptation | 2.98 | | References (58) | 3.3 |
| § 4.9 Smaller groups | 1.17 | | | |
| § 5 (with § 5.1, 1.40) | 2.39 | | | |
| **Main text** | **55.89** | | **Appendices** | **48.16** |

**Check.**
- The report's sizes are right: 55.89 and 48.16 pages; D–H are 20.17 pages (pp. 83.0–103.2).
- **What each proposed move saves:** D–H to supplementary material, −20.2 pages, plus about +0.8
  if F.2 and H.1(3) come into the body: −19.4. The repetition (item 11): −1 to −2.5. The body
  sketches (item 12): −0.5 to −1.5. C.4 citing Theorem 4.3(4): −0.6. The mergers (item 13): −0.3
  to −0.8 (E.2's share is already counted with E). Together about −22 to −25 pages: **about 83–86
  pages, with a main text of about 52–54.** Required change 6 (a complete proof of Proposition 4.15)
  adds 1–2 pages back.
- **45–50 pages is not reachable by these moves.** The main text alone is 55.89 pages. A 45–50
  page article would need Appendices A–C (26.1 pages) out as well, and 6–11 pages cut from the body.
- **Relation to `adr/0006`.** Item 5: "E, the smaller groups, stays in this paper … § 4.9 and
  Appendices F–H keep their place, and no material moves to a sequel." Item 7: "No page budget …
  Pass 4 … does not apply, since no venue limit binds it." The ADR counted the smaller groups as
  16.5 pages of a 106-page build; today F–H are 15.36 and § 4.9 1.17. The suggestion splits in two:
  moving **D and E** (4.81 pages) touches no decision; moving **F–H** (15.36 pages) out of the
  article's body reverses item 5's "keep their place", even if supplementary material is not a
  sequel, and would need a new ADR superseding item 5 (the ADR's own "Consequences" names what it
  changes: `tab:landscape`'s rows, § 1's "Smaller groups", the blueprint's `05-smaller-groups.tex`).
  The report's "core story" keeps F.2 and H.1(3), which is the ADR's reason for item 5 ("the
  rigidity is a property of the group"). The report names JMIV; item 1 of the ADR names JMIV or SSVM
  as the readership but sets no venue limit. A venue limit, if the author chooses one, is what would
  bring item 7 into question. The isotropic paper's split into a paper and a supplement (Q-0448) is
  the precedent for the mechanics.

**Verdict: PARTLY.** The sizes are right and the moves are possible; the 45–50 (or 45–55) page target
is inconsistent with the moves proposed, which reach about 83–86 pages; and the move of F–H runs
against `adr/0006` item 5.

**Fix (author).** No action without a decision. If taken: a new ADR (superseding `adr/0006` items 5
and, with a venue, 7), then the move by the Q-0448 mechanics.

---

## Summary

| # | Finding (report) | Verdict | Fix | Class | Where |
|---|---|---|---|---|---|
| 1 | Remark E.5: design and arithmetic (§ 4.1) | CONFIRMED (paper and referee agree; re-run reproduces the slopes) | none | — | — |
| 2 | Remark H.3: design (§ 4.1) | CONFIRMED (re-run; minimum on the $x_1$-axis) | none | — | — |
| 3 | E.5 discretization not stated (§ 4.2; RC 10) | CONFIRMED; the printed "nine-point" is five-point for the diagonal steps computed | state $D_S$, the five-point reduction, $(1+D_S)^{-\gamma}$, $n = 64t$; optionally the file name | safe | `paper/appendix-orbits.tex:261-263` (+ annotation `blueprint/src/parts/05-orbits.tex:1847`) |
| 4 | H.3 box and resolutions not stated (§ 4.2; RC 10) | CONFIRMED | side $\approx 132$, $1024^2$ and $2048^2$ points, Nyquist 24 and 49 | safe | `paper/appendix-similarity-loewner.tex:166` |
| 5 | Cite Felsberg's anisotropic Poisson work (§ 6.1) | PARTLY: dissertation not held, unverified; `felsberg2001scale` p. 130 proposes a 2×2 scale matrix; the paper cites neither Felsberg–Sommer paper and credits the Poisson scale space to Duits et al. alone | reading note for p. 130; credit `felsberg2004monogenic` Thm. 1 p. 7 in § 3.5; one sentence citing `felsberg2001scale` p. 130 with Thm. 3.7/Prop. 4.7(3); amend `PRIOR-ART-positioning.md` row C; request the dissertation only if wanted | author | `04-classical.tex:706`; `05-orbits.tex:146-148` or `01-introduction.tex:316-318`; `records/affine/` |
| 6 | Other positioning; order/group as a choice (§ 6.1, § 6.2) | CONFIRMED (assessments; anchors exist) | none | — | — |
| 7 | Prop. 4.20 leans on H.4/H.5 (§ 7.1; = RC 7) | CONFIRMED, and $T_s$ is named but unused | inline cond, $\mathcal M_s$, $\psi_\Sigma$, similarity covariance; drop $T_s$ | safe (claim unchanged), at the blueprint node, mirrored | `prop:similarity-stable-order-families`; `paper/05-orbits.tex:833-872` |
| 8 | Table 2 legend uses later terms (§ 7.1; sugg. 3) | PARTLY: $R(\lambda)$, $\beta_-(k)$, the profile, $C_\alpha$'s pointer, yes; $K_\alpha$, es, ecc are defined in the legend | one-line formulas for $C_\alpha$, the profile, $R(\lambda)$, $\beta_-(k)$ | safe | `paper/05-table.tex:25-34, 49-50` |
| 9 | Self-contained w.r.t. [15]–[17] (§ 7.2) | CONFIRMED (assessment) | none | — | — |
| 10 | [15]–[17] have no identifier (§ 7.2; RC 11) | CONFIRMED in print; the records hold the DOIs; `plain` drops every DOI (44 of 58) | `\bibliographystyle{plainurl}`, as `paper-iso`; author's call on version vs concept DOI (librarian's records if concept) | safe | `paper/main.tex:185` |
| 11 | Four-fold repetition, "save 8–10 pages" (§ 7.3; sugg. 1) | PARTLY: the repetition is there; the saving is ~1 page from § 4.3 and § 5, 2–2.5 with § 1 | fold § 4.3's three paragraphs into § 1, shorten § 5's summary | author | `05-table.tex:114-154`, `06-open-problems.tex:35-59`, `01-introduction.tex:198-287` |
| 12 | Sketches duplicate Appendix C, "80 % identical" (§ 7.3; sugg. 1) | PARTLY: double printing real and deliberate (Q-0312); 80 % refuted (18–22 % verbatim, a third of the length); C.4's re-derivation deliberate (no C4, W2F-1) | drop sketches for pointers (−0.5 to −1.5 p.); citing Thm. 4.3(4) in C.4 (−0.6 p.) adds C4 to Thm. 4.21's trust base | author | `05-orbits.tex:283-298, 564-585`; `05-wedge-axis.tex:102-163`; `appendix-wedge-axis.tex` |
| 13 | Duplicate propositions (§ 7.3; sugg. 4) | PARTLY for 3.4(3)/4.5 (hypotheses differ; paper says so); CONFIRMED for E.2/4.17 | prove 3.4(3) from 4.5; fold E.2's $\rho$ into 4.17 | author | blueprint `prop:gw-ray-families`, `prop:ray-families`, `prop:matern-cross-shape`, `prop:matern-steps` |
| 14 | D–H to supplementary material, 45–50 pages (§ 7.3; sugg. 1) | PARTLY: sizes right (D–H 20.2 p.); the moves reach ~83–86 p., not 45–50; F–H runs against `adr/0006` item 5 | none without a decision; a new ADR first | author | `adr/0006`; `paper/main.tex` |
