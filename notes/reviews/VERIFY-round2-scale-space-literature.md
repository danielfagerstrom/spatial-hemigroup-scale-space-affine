# Verification of the second external round: the scale-space literature and the attributions it proposes

Queue item Q-0433, 2026-10-13. Scope: the findings on the literature of
`review-round2-iso-review-2-E-literature-exposition-claude-fable.md` (read in full) and those of
parts A, C and D that concern the scale-space literature or an attribution, held against the
review build `iso-review-2` (commit `5713c03`; `paper-iso/*.tex` is unchanged since) and against
the sources, read at the page through the librarian's CLI. Nothing in the paper was edited.
Statement numbers are those of the review build (Theorem 3.6 `thm:isotropic-classification`,
Proposition 3.11 `prop:isotropic-bridge`, Theorem 3.12 `thm:origin-boundedness-d`, Example 3.14
`ex:matern`, Propositions 3.15–3.19, Lemma A.8 `lem:shadow-polar-profile`, Corollary A.9
`cor:dictionary-filtration`).

**Method.** Each claim of a reviewer was looked up in the source it names. A formula is quoted
from a page image; prose from the text layer where the layer is clean, and each reading note says
which. The reviewers read copies of their own or quoted from memory, so a verdict below is on the
claim, at the held page. The author's three earlier papers were read first for their own
positioning (§ 9).

**Reading notes written for this record** (`records/affine/`): `READING-burgeth2005bessel.md`,
`READING-burgeth2005relativistic.md`, `READING-alvarez1993axioms-architecture.md` (a second note
on that source), `READING-weickert1999linear.md`, `READING-felsberg2004monogenic.md` (with the
two pages read of `felsberg2001scale`), `READING-koenderink1988scale.md`,
`READING-lindeberg1996scalespace.md`, `READING-fagerstrom2005temporal.md`,
`READING-lindeberg2016time.md`, `READING-deriche1987using.md`,
`READING-daley2014dimension-montee.md` and `READING-sato1999levy-thm-27-13.md` (second notes).
Notes of earlier sessions that settle a point are named where they do.

**Correction, 2026-10-13 (Q-0450; the citation audit `CITATION-AUDIT-paper-iso-2026-10-13.md`,
row 45).** In the row 7e of § 0, in § 7e and in the row of § 10.6 on the two bounds, "(19),
p. 9" of `bogdan2014density` (arXiv v2) should read "(19), p. 11": p. 9 has (17) and (18), the
definitions of the weak scalings, and (19), the condition that the scaling exponents lie
strictly between 0 and 2, is on p. 11, as `READING-bogdan2014density.md` has it. The paper
(`paper-iso/sources.tex`) is corrected. The record below is left as it was written.

## 0. The verdicts

| | the reviewers' claim | verdict | settled at |
|---|---|---|---|
| 1 | The Matérn kernels are the kernels of the Bessel scale space of Burgeth, Didas and Weickert; it is a semigroup in its index, not scale invariant; its scaled version is their dilations; it remarks the dependence of the smoothness on the dimension (A, C, E) | **CONFIRMED**, with two corrections of detail | `burgeth2005bessel`, pp. 86, 87, 89, 90 |
| 2 | The two-scale composition and the scale invariance with a free relabelling are axioms of Alvarez, Guichard, Lions and Morel; what the paper drops relative to them is locality (A, E) | **CONFIRMED** | `alvarez1993axioms`, pp. 203, 204, 206, 214, 226–227 |
| 3 | The sentences "a semigroup leads to the Gaussian or to stable kernels" are wrong about the field (E); "correct as a summary of the six papers cited" and incomplete (A) | **PARTLY**: two of the four sentences already carry "rotation and scale invariance" and are true; two do not | the four sentences, § 3 below; `pauwels1995extended`, p. 694; `burgeth2005bessel`, p. 89 |
| 3′ | Iijima has the priority "on the Pauwels family" (A) | **REFUTED** as worded; the priority on the Gaussian axiomatics is confirmed | `weickert1999linear`, pp. 239–240 |
| 3″ | The Poisson scale space is Felsberg and Sommer's (A, E) | **CONFIRMED** | `felsberg2004monogenic`, Thm. 1, p. 7, and p. 8 |
| 4 | "In time-causal scale space a kernel is the law of a random delay" names a literature without citing it (A, E) | **CONFIRMED** for the missing citations; **PARTLY** for A's "kernels are not in general the laws of random delays" | the four sources, p. 159, pp. 229–231, pp. 97 and 100, p. 50 |
| 5 | The Matérn kernels on the line are the recursive filters of Deriche and of Young and van Vliet, and first-order Tikhonov regularization (Nielsen, Florack and Deriche) (E, A) | **PARTLY**: true of the cascades of identical first-order sections and of Deriche's smoothing function of 1987; false of the recursive Gaussians of Deriche (1993) and of Young and van Vliet; the regularization source is not held | `fagerstrom2026cone`, pp. 46, 60, 63; `deriche1987using`, pp. 170, 178 |
| 6 | The "shadow" is Matheron's descente applied to the Lévy measure (D, E) | **REFUTED** as an identification; the kinship with dimension walks is real and already cited | `daley2014dimension`, § 2, pp. 1815–1816, and Prop. 11, p. 1821 |
| 7a | $\Omega_d$ not a characteristic function on $\mathbb R^{d+1}$ is Schoenberg's (1938) and is not attributed (D) | **REFUTED**: it is attributed, to the held source that states it; Schoenberg's page states the inclusion only | `sources.tex`, the row of Proposition 3.19; `daley2014dimension`, Lemma 12, p. 1822; `schoenberg1938metric`, pp. 816–817 |
| 7b | Sato (1982) for absolute continuity, Sato (1980) for the polar criterion (E) | **CONFIRMED** through Sato's book; the second is already attributed, with Wolfe | `sato1999levy`, Thm. 27.13, p. 181, and pp. 196, 117 |
| 7c | Grzywny–Ryznar–Trojan's Theorem 3.9 is the nearest statement in print of the rate through the profile in $\mathbb R^d$ (E) | **CONFIRMED**, as a small-time statement | `grzywny2019asymptotic`, Thm. 3.9, p. 26 |
| 7d | The constant of (A.9) is the constant of Cygan–Grzywny–Trojan's Theorem 8 (C) | **CONFIRMED**; the matching limit is their Theorem 9 | `cygan2017asymptotic`, Thms. 8 and 9, p. 16 of arXiv v2 |
| 7e | Bogdan–Grzywny–Ryznar beside the two bounds (C: add it; E: say why it does not apply) | **E CONFIRMED, C PARTLY** | `bogdan2014density`, (19), p. 9, and pp. 2–3 of arXiv v2 |
| 8 | The rate at a fixed kernel with its constant in $\mathbb R^d$ is new (E) | **REFUTED**: it is in Leonenko's book, as the Sources table says | `leonenko1999limit`, Thms. 1.4.3 and 1.4.4, pp. 65–67 |

## 1. The Bessel scale space

**The claim** (E § 2(a)–(c), § 6.2 item 1; A § 6 item 1; C § 6): its transform is
$(1 + 4\pi^2|k|^2)^{-t/2}$ in every dimension; it is a semigroup in $t$; "scaled Bessel
scale-spaces" $G^n_{t,\sigma}(x) = \sigma^nG^n_t(\sigma x)$ are the paper's dilations; it "is not
scale invariant"; $G_n(x,n+1) \propto e^{-|x|}$ is continuous and not differentiable,
$G_n(x,n+3) \propto (1+|x|)e^{-|x|}$ is $C^2$; and this is "Theorem 3.12(2)'s ladder for the
Matérn example, in print in the field in 2005".

**Verdict: CONFIRMED.** Every quotation is on the page (`READING-burgeth2005bessel.md`):

- the definition and "in every dimension $n$": p. 86 (image);
- the semigroup in $t$: § 2.2, p. 88, and Proposition 2.1(1), p. 89 (image): "an additive
  semi-group for any fixed $n \ge 0$";
- "the Bessel scale-space is not scale invariant" and "the smoothness is increased by $t$":
  p. 89 (image);
- the two closed forms with "continuous function, not differentiable at $x = 0$" and "twice
  continuous differentiable", and "a merely continuous function convolved with $G_n(x,n+k)$
  produces only a $C^{k-1}$-smoothed version": p. 87 (image);
- the scaled family: § 2.4, p. 89 (image), and p. 90 (image): "fixing the parameter $t$ and using
  $\tau$ as parameter also leads to a scale-space structure".

**Two corrections of detail.**

1. *The scaled family.* The source defines $G^n_{t,\tau}(x) := \tau^nG^n_t(\tau x)$ and prints
   the transform $(1 + 4\pi^2\tau^2|k|^2)^{-t/2}$, which is the transform of
   $\tau^{-n}G^n_t(x/\tau)$; the abstract has $\tau$ where the display has $\tau^2$. Reviewer E
   quotes the definition as printed. Read by its transform, the family is the dilations of the
   Bessel kernel by $\tau$, and that is the sense in which it is the paper's family.
2. *The constants of p. 87* are too small by a factor $\sqrt\pi$ (the general formula of p. 86 is
   right). The paper takes no constant from this source and should not.

**The exact relation to the paper** (in its convention $\xi = 2\pi k$):

- The Matérn kernel of index $\gamma$ is the Bessel kernel at $t = 2\gamma$ dilated by
  $1/\sqrt2$: $p(x) = 2^{d/2}G_d(\sqrt2\,x, 2\gamma)$, for every $d$ and $\gamma > 0$. The
  kernel from scale zero at scale $s$ (Proposition 3.11(2)) is the scaled Bessel kernel with
  $t = 2\gamma$, $\tau = s/\sqrt2$. So "index $t = 2\gamma$" is right; the normalisation of the
  frequency is a factor $\sqrt2$ in the size. Checked numerically (appendix).
- The semigroup of the source runs along $t = 2\gamma$ at a fixed size. The paper's family runs
  along the size at a fixed $\gamma$: the family that p. 90 fixes $t$ for and that Figure 5 of
  the source draws, **with no composition law stated**. The hemigroup is that law.
- **Theorem 3.12(2)** at $c = 2\gamma = t$: $c = d + 1$ gives $N = 0$ and $c = d + 3$ gives
  $N = 2$, the two statements of p. 87; for $t = d + k$, $k \ge 1$ an integer, the theorem gives
  $N = k - 1$, the count of the remark. So the remark is the Matérn case of the theorem at
  integer $c - d$, **exactly**; and $G_n(\cdot,n+1)$ shows that $N$ cannot be raised at
  $c = d + 1$. The remark is stated without proof and for the filtered function. The source has
  nothing for $c \le d$: no unbounded kernel, no threshold. Reviewer C's "Theorem 3.12(2) is the
  quantitative form of Burgeth et al.'s remark that smoothness grows with their $t$, with the
  threshold at the dimension" is right, the threshold being the paper's part.
- Reviewer E's § 2(f) (the Sobolev form $R^n_t : H^s \to H^{s+t}$): on p. 89, as quoted.

**The earlier papers** say this, and the manuscript does not: the line paper at pp. 1, 3, 4 and
43, the cone paper at pp. 2, 4 and 47 (quoted in `READING-burgeth2005bessel.md`, § 6). "The
manuscript … dropped" it is accurate. The header comment of `paper-iso/01-introduction.tex`
(Q-0428, the fixes round) records why: "No sentence places the Matern kernels in the scale-space
literature: no reading note supports one". That note now exists.

## 2. Alvarez, Guichard, Lions and Morel

**The claim** (E § 6.2 item 2, from memory; A § 6 item 4): their architecture is
$T_{t+h} = T_{t+h,t}T_t$ with transition operators; their scale invariance is
$T_tH_\lambda = H_\lambda T_{t'(t,\lambda)}$ with a free $t'$; "What makes their linear case the
heat equation is the locality/regularity axiom on $T_{t+h,t}$, exactly what the manuscript does
not impose"; the line paper's "orthogonal" is wrong.

**Verdict: CONFIRMED** at the page (`READING-alvarez1993axioms-architecture.md`):

- [Causality] $T_{t+s} = T_{t+s,s}\circ T_s$, "A weaker version of the pyramidal hypothesis",
  with [Recursivity] the semigroup "strong version": p. 203 (image). The words "pyramidal
  structure" of the reviewers are the source's "pyramidal architecture" and "pyramidal
  hypothesis".
- [Scale invariance] "For any $\lambda$ and $t$, there exists $t'$ such that
  $D_\lambda T_{t'} = T_tD_\lambda$": p. 206 (image); "no condition has been imposed on the
  relation between $t'$ and $(t,\lambda)$": p. 226 (image); and its form is derived:
  $t'(t,\lambda) = h^{-1}(\lambda h(t))$, Lemma 1(iv), p. 227 (image), the counterpart of the
  gauge.
- The linear case: Theorem 3, p. 214 (image), under [Causality], [Regularity-bis],
  [Locality-bis], [Temporal regularity], [Comparison principle] and the two invariances: linear
  transition operators that commute with the isometries give the heat equation "up to a
  rescaling $t' = h(t)$".

**What the paper keeps and what it drops** (the table of the note, § 5): it keeps linearity,
translation and rotation invariance, the two-scale cascade, the scale invariance with a
relabelling that is not prescribed, and **the comparison principle**, which for a linear filter
is $F_t \ge 0$ (p. 204), the paper's (A4). It asks continuity in the scales (A7) where the source
asks a regularity that gives a generator (for a linear operator, a Lipschitz bound at $t = 0$,
p. 209). It **drops locality**. So "no PDE" follows from dropping locality and regularity, not
from dropping positivity. Two differences of form: the source states its scale invariance for
the operators from scale zero and (A8) is on every stage; the source works on bounded functions
with the supremum norm and the paper on $L^1$.

**"Orthogonal".** The line paper (p. 4: "The axiomatics of [2], which classify the nonlinear
evolutions, are orthogonal to the question asked here") and the time-causal paper (§ 2: "a
different theory and outside the scope") describe the source by its nonlinear results. Its
architecture and its Theorem 3 are linear and are the closest precedent in print. The reviewers
are right. The existing note `READING-alvarez1993axioms.md` is accurate for what it read
(projection invariance, Theorems 3 and 5); it did not read § 2.1.

## 3. "A semigroup leads to the Gaussian or to stable kernels"

**The sentences as they stand** (`iso-review-2`):

1. Abstract, first sentence (`main.tex`): "Scale-space axioms usually ask the cascade to be a
   semigroup, which with rotation and scale invariance leads to Gaussian and stable kernels."
2. § 1, first paragraph (`01-introduction.tex:190–196`): "Scale-space axioms usually ask the
   cascade to be a semigroup in one scale parameter, as those of the extended class of Pauwels,
   Van Gool, Fiddelaers and Moons do [35]. A semigroup asks more than a cascade needs: … With
   rotation and scale invariance the axiom systems of the literature then arrive at the
   Gaussian, or, where the kernels are asked to be positive, at the kernels whose Fourier
   transform at the frequency $\xi \in \mathbb R^d$ is $e^{-|\xi|^p}$, $0 < p < 2$".
3. § 1, third paragraph (`01-introduction.tex:242–244`): "The Gaussian and the symmetric stable
   laws … are self-decomposable, and they are the laws at which the semigroup axiom systems
   arrive."
4. "Relation to scale-space theory", first sentence (`01-introduction.tex:357–359`): "In the
   scale-space literature isotropy is imposed together with a semigroup in the scale or with a
   diffusion equation, and the answer is the Gaussian or a kernel with transform
   $e^{-a|\xi|^p}$, called stable here when $0 < p \le 2$."

**What is true**, with the page for each attribution and whether the source is held:

- *A semigroup with scale invariance:* the transforms $e^{-a|\omega|^\alpha t}$, $\alpha > 0$
  (`pauwels1995extended`, p. 694, the plane by rotation invariance, § III, p. 695; held,
  `READING-pauwels1995extended.md`). The kernel is positive exactly for $0 < \alpha \le 2$
  (zero crossings for $\alpha > 2$, pp. 694–695); these are the stable kernels and the
  Gaussian. Duits et al.: generator $-(-\Delta)^\alpha$, positive for $\alpha \in (0,1]$
  (`duits2004axioms`, pp. 267, 277; held, `READING-duits2004axioms.md`). The Poisson scale space,
  $\alpha = \tfrac12$: Felsberg and Sommer (`felsberg2001scale`, p. 124;
  `felsberg2004monogenic`, Thm. 1, p. 7; both held).
- *The Gaussian alone* needs a requirement of another kind: Koenderink's causality, through a
  diffusion equation (`koenderink1984structure`, p. 365; held); separability in Florack et al.
  (`florack1992scale`, p. 380; held); Florack's book (`florack1997image`, pp. 54, 57, 61; held);
  non-enhancement in Lindeberg (`lindeberg2011generalized`, § 3.1; held; its axioms assume
  neither rotation nor scale invariance, `READING-lindeberg2011generalized.md`, § 1); and, in
  the linear case of Alvarez et al., locality (§ 2 above).
- *Iijima:* as reported by Weickert, Ishikawa and Imiya (`weickert1999linear`, pp. 239–240;
  held; Iijima's own papers are not), linearity, translation invariance, scale invariance with a
  free $\sigma'(\sigma,\lambda)$ and a "(Generalized) semigroup property" give the kernels with
  transform $\exp(-\xi^{2m})$, $m = 1, 2, \dots$, and positivity gives $m = 1$. The derivation
  "assumes implicitly that the frequency response of the scale-space kernel is continuously
  differentiable at the origin" (`felsberg2004monogenic`, p. 8), without which the Poisson
  kernel satisfies the axioms (its Thm. 1).
- *Without scale invariance:* the Bessel scale space is a semigroup of rotation-invariant
  kernels in every dimension that is neither Gaussian nor stable (§ 1), and so are the
  relativistic scale spaces, with exponent $t(\sqrt{|\xi|^2 + m^2} - m)$
  (`burgeth2005relativistic`, pp. 3, 5, and Proposition 2.4, p. 7; held).

**Verdict: PARTLY.**

- Sentences 1 and 2 already say "with rotation and scale invariance", and with it they are true
  (a kernel of the paper is a probability kernel, so positivity is in the word). Reviewer E's
  "same claim p. 1, lines 5–7" is not right for them. Sentence 2 has its logic the wrong way
  round: positivity gives $0 < p \le 2$, the Gaussian included, and it is a further requirement
  that leaves $p = 2$.
- Sentences 3 and 4 lack the qualification and are false of the Bessel and relativistic scale
  spaces. Sentence 4 is also the one that reviewer A checked and found "correct as a summary of
  the six papers cited", which it is; it is wrong as a sentence about "the scale-space
  literature".
- None of the four says that the two-scale cascade has a precedent (§ 2).

**3′. Iijima and "the Pauwels family"** (A § 6 item 3: "The Pauwels family was derived by Iijima,
as Pauwels's own 1998 survey says and as the line paper says"). **REFUTED as worded.** What is
reported of Iijima is the family $\exp(-\xi^{2m})$ with integer $m$, of which only the Gaussian
is positive; no stable kernel with $0 < p < 2$ is in it. The line paper says that Iijima derived
the uniqueness of the Gaussian (its p. 4), not the family. The 1998 survey of Pauwels that the
reviewer read is not identified and not held. What stands: Iijima for the first axiomatics of
the Gaussian, cited through `weickert1999linear`.

## 4. The time-causal literature

**The sentences** (`iso-review-2`): § 1, third answer (`01-introduction.tex:311–313`): "In
time-causal scale space a kernel is the law of a random delay on $[0,\infty)$, and the families
are classified in the author's paper [11] (version 1.1.0, Thm. 7.3)." § 2.3
(`02-line-papers.tex:236–239`): "In time-causal scale space a kernel is a law on the half-line
$[0,\infty)$ of delays: the record at a time uses the signal at earlier times only, and the delay
is how far back it reaches."

**The claim** (A § 2 and § 6 item 5; E § 6.2 item 5): the phrase names a literature (Koenderink
1988; Lindeberg and Fagerström 1996; Fagerström 2005; Lindeberg 2016, 2023) and cites only the
author's paper; A adds "in which kernels are not in general the laws of random delays and which
classifies nothing in this sense".

**Verdict.** The missing citations: **CONFIRMED.** All four sources are held and were read at
their first page (the four reading notes). The time-causal paper of the series cites them (its
[19], [24], [8], [23]) and places itself against them at its pp. 2, 4 and 76; the cone paper
cites Lindeberg 2016 and 2023 (its p. 4 and p. 66). The manuscript cites none.

A's further sentence: **PARTLY.** In each of the three sources read for it the kernels are
positive, of unit mass and supported on the past (`fagerstrom2005temporal`, Definition 1, p. 100:
"Positivity", "Unit area", "Temporal causality"; `lindeberg1996scalespace`, p. 231: truncated
exponentials normalised to unit $L^1$ norm; `lindeberg2016time`, p. 50: cascades of the same). So
a kernel there is the density of a law on the half-line of delays. None of these sources says
"law" or "random delay": the reading is the series'. And a classification exists there, under
another axiom (`lindeberg1996scalespace`, abstract: "a complete classification is given of the
scale-space kernels that satisfy this property of non-creation of structure and respect the time
direction as causal"). What the sentence gets wrong is the scope: "the families are classified"
is true of the families of the hemigroup axioms.

## 5. The recursive-filter reading of the Matérn kernels

**The claim** (E § 6.2 item 6, required change 5; A § 6 item 7): "on the line the Matérn kernel
of index 1 is the two-sided exponential, the symmetric first-order recursive filter, and the
index-$n$ kernel is the cascade of $n$ such filters …; first-order Tikhonov regularization gives
the same transform … (Nielsen et al.) … it is the family of the recursive Gaussian
approximations"; cite Deriche, Young and van Vliet, Nielsen–Florack–Deriche; "The cone paper
devotes a section to this".

**What the cone paper says** (`fagerstrom2026cone`, v0.1): the Matérn families of integer index
are exactly the admissible families whose stages are cascades of identical first-order sections
run forward and backward (Theorem 5.4, p. 45; Corollary 5.5, p. 46; Proposition 7.2, p. 60). The
cascade of $\gamma$ identical sections, with transfer $(1 + \sigma^2\omega^2/2\gamma)^{-\gamma}$,
is a Matérn member (Remark 7.4, p. 63). And the same remark, with Example 7.12: **the recursive
Gaussians of Deriche (1993) and of Young and van Vliet (1995) are not kernels of an admissible
family**: the first has zeros on the real axis, the second a signed profile that goes negative.
It cites Deriche 1993, Young and van Vliet 1995, van Vliet et al. 1998 and Triggs and Sdika
2006. It does not cite Nielsen, Florack and Deriche (reviewer E's dagger on that item is wrong),
nor Deriche 1987.

**Verdict: PARTLY.**

- Right: the kernels of integer index on the line are the cascades of identical first-order
  recursive sections, and the cone paper proves it. A reader of this paper is not told.
- Right, and found at the page: Deriche's smoothing function of 1987,
  $k(\alpha|x| + 1)e^{-\alpha|x|}$ (`deriche1987using`, (67)–(68), p. 178, with (26)–(27),
  p. 170), is the Matérn kernel of index 2 on the line. The identification is this record's
  (`READING-deriche1987using.md`); the source does not make it.
- Wrong: "the family of the recursive Gaussian approximations". The published recursive
  Gaussians have complex poles and are outside the class, by the cone paper's own test. A
  sentence that cites Deriche (1993) or Young and van Vliet for the Matérn kernels would
  misattribute.
- Not verifiable: the Tikhonov reading (Nielsen, Florack and Deriche 1997) is not held.

**The sentence**, if one is wanted (§ 10.4): the cone paper's result, cited as such.

## 6. Matheron's descente

**The claim** (E § 2(d), required change 8: the formula of Lemma A.8 "is Matheron's descente
(the inverse of the montée, the 'dimension walk' of Gneiting 2002 and of [7]), applied to the
radial Lévy density"; D § 6: "Matheron's descente (the turning-bands operator) in the form of an
Abel transform").

**Verdict: REFUTED as an identification** (`READING-daley2014dimension-montee.md`). The held
source that prints the two operators is Daley and Porcu, § 2, p. 1815: the Montée
$If(x) = \int_x^\infty uf(u)\,du/\int_0^\infty uf(u)\,du$ maps $\Phi_d$ into $\Phi_{d-2}$, the
Descente $Df(x) = -f'(x)/[xf''(0+)]$ maps $\Phi_d$ into $\Phi_{d+2}$ (Proposition 5, p. 1816).

- The descente raises the dimension. The shadow lowers it. The name is the wrong one of the two.
- Both operators act on the radial characteristic function, change it, and move it two
  dimensions. The shadow acts on the Lévy measure, by projection, one dimension down, and leaves
  the exponent as a function of the radius unchanged.
- What the formula of Lemma A.8 is: with $v = (1+u^2)^{-1/2}$ it reads
  $\bar k(r) = \int_0^1 k'(r/v)f_{d|d+1}(v)\,dv$, with the beta density of Daley and Porcu's
  Theorem 4. That is their (3.8) (Proposition 11, p. 1821) for the radial part of a Lévy measure
  in place of a Schoenberg measure (weights checked, appendix). The Sources table cites that
  proposition already, for laws.
- Whether Matheron (1965) has an operator of order one that integrates along one coordinate, and
  under which name, needs the book, which is not held; Gneiting (2002) is not held either.
  Reviewer D's Abel form is a rewriting of the lemma and needs no source.

The clause for the Sources row is in § 10.6. No sentence should say "descente".

## 7. The other attributions

**7a. $\Omega_d$ and Schoenberg** (D § 2, § 6, required change 3: Corollary A.9(2)'s conclusion
"is Schoenberg's witness for $\Phi_{d+1} \subsetneq \Phi_d$ (Schoenberg 1938; a direct proof in
Golinskii, Malamud and Oridoroga … 2018)", and "Table 2 cites Gneiting [17] only for the
strictness in general"). **REFUTED.**

- The conclusion is attributed. The row of Proposition 3.19 and Corollary A.9 in `sources.tex`
  ends its "See also" with "Lemma 12, p. 1822, for the last assertion of Corollary A.9(2)", and
  that lemma reads "For every $d = 1, 2, \dots$, $\Omega_d \in \Phi_d \setminus \Phi_{d+1}$"
  (`READING-daley2014dimension.md`, at the image). The reviewer looked in the row of the
  dictionary and missed it; the clause can be made plainer (§ 10.6).
- Schoenberg (1938): § 2.1, p. 816, prints the chain with $\supset$ for inclusion and says
  nothing on strictness; Theorem 1 (p. 816) is the representation by $\Omega_m$
  (`READING-schoenberg1938metric.md`, at the images of pp. 816, 817, 828; text-layer searches
  for "proper", "strict", "not positive definite" and "does not belong" find nothing). The
  earlier blind check stands. The appendix of that paper was not read, so "Schoenberg nowhere
  states it" is not claimed; "the cited pages do not" is.
- The paper of 2018 is not needed: the statement is in print in 2014 in a held source, which
  derives it from Gneiting's Euclid hat (1999, p. 94, held). It would be a later second proof.

**7b. Sato 1982 and Sato 1980** (E § 2(d), required change 7). **CONFIRMED through the book**
(`READING-sato1999levy-thm-27-13.md`): Theorem 27.13, p. 181, "Any nondegenerate
selfdecomposable distribution on $\mathbb R^d$ is absolutely continuous", "proved in [392]"
(p. 196), [392] being Sato (1982). The paper does not cite the theorem; the row of Proposition
3.15 can. The polar criterion is already given "to Wolfe and to Sato in $\mathbb R^d$"
(`02-line-papers.tex:449`, with the book's p. 117); the book's attribution has both names, and
reviewer E's has one. Neither article is held, so neither can be cited at a page of its own.

**7c. Grzywny–Ryznar–Trojan, Theorem 3.9** (E § 2(d), required change 6). **CONFIRMED**
(`READING-grzywny2019asymptotic.md`, § 2, p. 26 of the published article): for a Lévy process
with radially nonincreasing densities and $\psi \in \Pi_\ell^\infty$, $\ell$ bounded,
$p(t,x)/(t|x|^{-d}\ell(|x|^{-1})e^{-t\psi(|x|^{-1})}) \to \Gamma(d/2)/(2\pi^{d/2})$ as
$t \to 0+$ with $t\psi(|x|^{-1}) \to \infty$. It is a statement as the time tends to $0$, not at
a fixed time (the note: "Neither is a statement about $p(t,\cdot)$ at a fixed $t$"). The
reviewer's consistency check holds: $R(d,\tau c)/(\tau c) \to \Gamma(d/2)/(2\pi^{d/2})$ as
$\tau \to 0$ (appendix), so the paper's constant for the law at time $\tau$ tends to theirs. The
row of Proposition 3.17 names only the line; it should name this theorem and its regime.

**7d. The constant of (A.9)** (C § 2, suggestion S3). **CONFIRMED**
(`READING-cygan2017asymptotic.md`, § 3, at the image of p. 16 of arXiv v2):
$\tilde{\mathcal C}_{d,\alpha} = 2^{-\alpha}\Gamma((d-\alpha)/2)/(\Gamma(d/2)\Gamma(1+\alpha/2))$,
and $B_c = I_c/\Gamma(1 + c/2) = R(d,c)|S^{d-1}|/c$ is this function of the index at
$\alpha = c$ (appendix; the note had recorded it). Their Theorem 8 is the limit at infinity; the
limit at the origin, which is the paper's, is their Theorem 9, with the same constant. There the
measure is the potential measure, $\alpha \in [0,2]$ and $d \ge 3$.

**7e. Bogdan–Grzywny–Ryznar** (C suggestion S1: add it as "the standard two-sided bound"; E
§ 6.1 and suggestion 16: it does not apply, say why). **E CONFIRMED, C PARTLY**
(`READING-bogdan2014density.md`, §§ 2 and 4): the two-sided estimate (Theorem 21, Corollary 23
of arXiv v2) assumes scalings with exponents in $(0,2)$ ((19), p. 9), which the paper's laws
with a finite $c$ fail; the authors leave the case open (pp. 2–3); and Theorem 26 makes the
lower bound of that form equivalent to the scalings. Only the statements without scaling hold
for the paper's laws (Corollary 7, p. 8, an upper bound). So the paper may name it only with the
reason it does not cover the case. It was cited before Q-0428 and removed then.

## 8. Is the rate at a fixed kernel in $\mathbb R^d$ new?

Reviewer E (§ 2(d)) writes that the rate of Propositions 3.16 and 3.17, "the fixed-time ($t=1$)
version, with the Riesz constant and the slowly varying factor $K$ exact", is "new as stated",
and that the paper's "no new result for probability" would have to be withdrawn in a probability
journal. The reviewer could not reach Leonenko's book (its list of unread sources, and § 6.1:
"Not reachable at the page level"). The book was read at the page images for the first round
(`READING-leonenko1999limit.md`): Theorem 1.4.3, p. 65, gives the mass of a small ball of a
rotation-invariant probability law on $\mathbb R^n$ whose transform is $r^{-\alpha}L(r)$,
$0 < \alpha < n$, $n \ge 1$, with the constant $1/c_4(n,\alpha) = R(d,c)|S^{d-1}|/c$ and no
monotonicity; Theorem 1.4.4, pp. 66–67, gives the density when it is monotone, with
$c_5(n,\alpha) = R(d,c)$ exactly; its Example 1.4.1, p. 67, is the Bessel potential, the Matérn
kernel. So clause (1) of Proposition 3.16 is in print with its constant, for one fixed law, and
the row of the Sources table that says so is right. Reviewer E's remark comes from not having
the book. What the paper adds to that theorem is the passage from the Lévy measure to the
transform, with the factor $K$ and the constant $C_k$ (Corollary 3.13(2), Proposition A.6,
Lemma A.7), and the boundary case $c = d$, which the book calls open (the note, § 7); the row of
Proposition 3.17 will say where the nearest statement through the Lévy measure is (7c).

## 9. What the earlier papers of the series say

Read first, as the author's own positioning (`library get <citekey> --format md` for the text,
`library search` for the pages).

- **The line paper** (`fagerstrom2026spatial`, v0.1), "Relation to the scale-space axiomatics",
  p. 4: Iijima ([18], [35]) with the implicit regularity and the Poisson counterexample of
  Felsberg and Sommer ([10], § 2.1, Thm. 1 and p. 8); Koenderink, Lindeberg, Florack; "The
  extended class of [28] and the α-scale spaces of [6] keep the semigroup and weaken other
  requirements, and they meet the present class in the symmetric stable family"; the Bessel
  scale space (§ 1); "The axiomatics of [2] … are orthogonal". Its bibliography has Alvarez et
  al., Burgeth et al. (Bessel), both papers of Felsberg and Sommer, Iijima, Weickert et al.,
  Lindeberg 1990 and 1994.
- **The cone paper** (`fagerstrom2026cone`, v0.1), "Relation to the literature", p. 4, and
  Remark 5.6, p. 47: the Bessel scale space with "no composition law stated for the range family
  at fixed order"; the relativistic scale spaces; Lindeberg's time-causal limit kernel as "the
  nearest construction"; the Poisson scale space; § 7 and Remark 7.4, p. 63, on the recursive
  filters (§ 5 above).
- **The time-causal paper** (`fagerstrom2026hemigroup`, v1.1.0), pp. 2, 4 and 76: Koenderink's scale-time [19], Lindeberg and Fagerström [24], Fagerström 2005 [8] ("the
  semigroup theory"), Lindeberg 2016 [23], with the relation "containment, not competition".

The manuscript's bibliography has, of all these, Koenderink 1984, Florack et al., Florack's
book, Lindeberg 2011, Pauwels et al. and Duits et al. The reviewers' "regression" is accurate
for the Bessel scale space, Felsberg and Sommer, Iijima through Weickert et al., Alvarez et al.,
and the time-causal sources. It is not accurate for Nielsen, Florack and Deriche (cited by none
of the three).

## 10. What the paper should say

Each text below is a proposal for the response plan. Every anchor is from a note that read it,
named in brackets after the text. **The main text ends on page 30 of 30 and the abstract has 250
words**: the word counts are given so that the plan can find the room. New citekeys for
`references.bib` (all held, `library bib export`): `alvarez1993axioms`, `burgeth2005bessel`,
`burgeth2005relativistic`, `felsberg2001scale`, `felsberg2004monogenic`, `weickert1999linear`,
`koenderink1988scale`, `lindeberg1996scalespace`, `fagerstrom2005temporal`, `lindeberg2016time`,
and, if the clauses of § 10.6 are taken, `bogdan2014density` again.

### 10.1 The abstract

The first sentence is true as it stands (§ 3, sentence 1) and needs no replacement. What the
abstract lacks is the credit for its example. Replace the clause "those with transform
$(1 + |\xi|^2/2)^{-\gamma}$, whose densities are \Matern{} functions for $\gamma > d/2$, do so"
by (three words longer; without "of scale-space theory" it is the same length):

```latex
the Bessel kernels of scale-space theory, with transform $(1 + |\xi|^2/2)^{-\gamma}$ and
\Matern{} densities for $\gamma > d/2$, do so
```

Reviewer E's suggestion 1 (the list of the four printed proofs out of the last sentence) would
free the three words.

If the author wants the first sentence to say what the qualification is for, the accurate form
is (two words longer):

```latex
Scale-space axioms usually ask the cascade to be a semigroup, which with rotation and scale
invariance leaves only the Gaussian and the stable kernels.
```

[`READING-pauwels1995extended.md`, p. 694; `READING-burgeth2005bessel.md`, pp. 86, 89.]

### 10.2 The first paragraph of § 1

Replaces `01-introduction.tex:187–202` (232 words now; 274 below).

```latex
A scale-space representation measures a signal through an aperture whose size is the scale. A
measurement is convolution with a probability kernel, and the record at a coarser scale is
computed from the record at a finer one by a further convolution, a \emph{stage} of the cascade.
Scale-space axioms usually ask the cascade to be a semigroup in one scale parameter, as those of
the extended class of Pauwels, Van Gool, Fiddelaers and Moons do \sscite{pauwels1995extended}. A
semigroup asks more than a cascade needs: every stage has to be itself one of the apertures, so
that one parameter indexes the stages and the apertures alike. With rotation and scale
invariance the semigroup axioms of the literature leave the probability kernels whose Fourier
transform at the frequency $\xi \in \RR^d$ is $e^{-t|\xi|^p}$, for one $p$ with $0 < p \le 2$.
The Gaussian is $p = 2$, and a further requirement such as locality singles it out (``Relation
to scale-space theory'' below). The axioms studied here ask only that the stages compose. With
$\mu_{s,t}$ the kernel of the stage from scale $s$ to scale $t$, this is
$\mu_{r,t} = \mu_{s,t} * \mu_{r,s}$ for $r \le s \le t$, and how a stage depends on its two
scales is left free. Such a family is a \emph{convolution hemigroup}
(\sscite{hazod2001stable}, Def.~2.14.16, p.~380). In scale-space theory this form of the
cascade is the causality axiom of Alvarez, Guichard, Lions and Morel, who state it as a weaker
version of the semigroup (\sscite{alvarez1993axioms}, \S2.1, p.~203). Their axioms also ask the
stages to be local, and an evolution equation follows. Locality is not asked here, and no
generator of the scale evolution is claimed. What is gained is a larger class of apertures.
```

What changed: the order of positivity and the Gaussian is put right; the cascade has its
precedent; "What is given up with the semigroup is an evolution equation in one scale parameter"
is gone, because Alvarez et al. obtain an evolution equation without a semigroup (their Theorem
2(ii)): what gives it up is not asking locality.
[`READING-pauwels1995extended.md`, pp. 694–695, 698; `READING-alvarez1993axioms-architecture.md`,
pp. 203, 207, 211, 214.]

### 10.3 "Relation to scale-space theory"

Replaces `01-introduction.tex:357–380` (293 words now).

```latex
\paragraph{Relation to scale-space theory.} The two-scale cascade is the causality axiom of
Alvarez, Guichard, Lions and Morel, who state it as the weaker form of the semigroup, and their
scale invariance, like axiom (A8), lets a dilation relabel the scales in a way that is not
prescribed (\sscite{alvarez1993axioms}, pp.~203, 206 and~226). They ask in addition that the
stages be regular and local. For linear operators that commute with the isometries the heat
equation follows, up to a rescaling of the scale (Thm.~3, p.~214). The present axioms keep their
comparison principle as positivity and do not ask locality.

The axiom systems that keep a semigroup with scale invariance arrive at the transforms
$e^{-a|\xi|^p}$: Pauwels et al.\ from recursivity and scale invariance
(\sscite{pauwels1995extended}, p.~694 and \S III, p.~695), Duits et al.\ as the semigroups
generated by $-(-\Delta)^\alpha$, positive for $\alpha \in (0,1]$ (\sscite{duits2004axioms},
pp.~267 and~277), with the Poisson scale space of Felsberg and Sommer at $\alpha = \tfrac12$
(\sscite{felsberg2004monogenic}, Thm.~1, p.~7). The kernels with $0 < p \le 2$ are called stable
here. A requirement of another kind leaves the Gaussian alone: positivity in the first axiom
system, Iijima's, whose derivation uses derivatives of the transform at the origin
(\sscite{weickert1999linear}, pp.~239--240; \sscite{felsberg2004monogenic}, p.~8); a diffusion
equation derived from causality (\sscite{koenderink1984structure}, p.~365); separability
(\sscite{florack1992scale}, (23)--(25), p.~380); self-similar positive Schwartz filters
(\sscite{florack1997image}, Result~3.2, p.~61); the non-enhancement of local extrema
(\sscite{lindeberg2011generalized}, \S3.1 and \S4.1.1).

Without scale invariance a semigroup of rotation-invariant kernels need not be of this kind. The
Bessel scale space of Burgeth, Didas and Weickert is the semigroup in $t \ge 0$ of the kernels
with transform $(1 + |\xi|^2)^{-t/2}$, which at $t = 2\gamma$ are dilations of the \Matern{}
kernels of index $\gamma$ (\sscite{burgeth2005bessel}, pp.~86 and~89). It runs along the index
and is not scale invariant. Its authors also dilate the kernels at a fixed index, with no
composition law for the dilations (p.~90). The hemigroup is that law
(Proposition~\ref{prop:isotropic-bridge}). The relativistic scale spaces of the same authors
are a second such semigroup \sscite{burgeth2005relativistic}.

By the first answer the kernels of the present axioms are a larger class, which contains the
stable kernels of every index $0 < p \le 2$ and the \Matern{} kernels
(Proposition~\ref{prop:isotropic-bridge}). By the second and the third the dimension enters. The
Gaussian and the stable kernels are smooth and are admitted in every dimension
(\S\ref{sec:isotropic-origin}). The kernels of a general family can be unbounded at their
centre, in the dimensions $d \ge c$, and its exponent may be admitted up to some dimension
only.
```

413 words by the count that gives 293 for the present paragraph: 120 longer. The present
paragraph's sentences on Koenderink, Florack and Lindeberg are compressed to make room for
Alvarez et al., Iijima, Felsberg and Sommer and the Bessel scale space. If room is short, the
sentence on the relativistic scale spaces and the clause on Florack's book go first; the
sentences on Alvarez et al. and on the Bessel scale space are the ones the reviewers require.
The text is set as four short paragraphs under one heading, where the present one is a single
paragraph. What this says of the paper's own, in scale-space terms: the class as a whole (the first answer), obtained without a semigroup
and without locality, with the Matérn kernels of the Bessel scale space as a known member and
the hemigroup as the composition law that its authors did not have.
[`READING-alvarez1993axioms-architecture.md`, pp. 203, 204, 206, 211, 214, 226;
`READING-pauwels1995extended.md`; `READING-duits2004axioms.md`;
`READING-felsberg2004monogenic.md`, pp. 7–8; `READING-weickert1999linear.md`, pp. 239–240;
`READING-koenderink1984structure.md`; `READING-florack1992scale-p380.md`;
`READING-florack1997image.md`; `READING-lindeberg2011generalized.md`;
`READING-burgeth2005relativistic.md`, pp. 3, 7; `READING-burgeth2005bessel.md`, pp. 86, 89, 90.]

Two smaller places in § 2 follow from it:

- `02-line-papers.tex:144–145`, "Axiom (A6), the \emph{cascade}, is what separates this class
  from the semigroup axioms of Pauwels et al.": add after the citation "and is the causality
  axiom of Alvarez et al.\ (\sscite{alvarez1993axioms}, p.~203)".
- `02-line-papers.tex:216–218`, "A familiar example is the Poisson kernel of scale space, the
  $\alpha = \tfrac12$ member of the $\alpha$-scale spaces (\sscite{duits2004axioms}, p.~267)":
  replace by "A familiar example is the kernel of the Poisson scale space of Felsberg and
  Sommer (\sscite{felsberg2004monogenic}, Thm.~1, p.~7), the $\alpha = \tfrac12$ member of the
  $\alpha$-scale spaces (\sscite{duits2004axioms}, p.~267)".

### 10.4 The sentence that introduces the Matérn kernels, and Example 3.14

In § 1 (`01-introduction.tex:242–247`), replace "and they are the laws at which the semigroup
axiom systems arrive. Among those added are the laws with transform $(1 + \omega^2/2)^{-\gamma}$,
$\gamma > 0$, whose profile is $2\gamma e^{-\sqrt2\,x}$. This paper calls these laws and their
dilations the \emph{\Matern{} kernels} of index $\gamma$." by:

```latex
and they are the laws at which the semigroup axiom systems with scale invariance arrive. Among
those added are the laws with transform $(1 + \omega^2/2)^{-\gamma}$, $\gamma > 0$, whose
profile is $2\gamma e^{-\sqrt2\,x}$. This paper calls these laws and their dilations the
\emph{\Matern{} kernels} of index $\gamma$. They are known to scale-space theory as the kernels
of the Bessel scale space, a semigroup along the index $\gamma$ at a fixed size
\sscite{burgeth2005bessel}. Here the cascade runs along the size, at a fixed index. On the line
the kernels of integer index are those computed by a cascade of identical first-order recursive
filters, run forward and backward along the signal (\prog{B}{Prop.~7.2 and Cor.~5.5}).
```

(70 words longer; 43 without the last sentence, which is the answer to reviewer E's required
change 5 and can be left to the cone paper.) No recursive Gaussian is cited here: those of
Deriche (1993) and of Young and van Vliet are outside the class (§ 5).
[`READING-burgeth2005bessel.md`, § 5; `fagerstrom2026cone`, pp. 46, 60, 63.]

In Example 3.14 (`03-isotropic.tex:909–911`), replace "For every $\gamma > 0$ it is the Bessel
kernel of potential theory, dilated by $1/\sqrt2$ (\sscite{aronszajn1961theory}, (4,1),
p.~416)." by:

```latex
For every $\gamma > 0$ it is the Bessel kernel of potential theory, dilated by $1/\sqrt2$
(\sscite{aronszajn1961theory}, (4,1), p.~416), which is the kernel of the Bessel scale space at
its scale $2\gamma$ (\sscite{burgeth2005bessel}, p.~86). Its authors note that the kernel with
$2\gamma = d + 1$ is continuous and not differentiable at the centre, and the kernel with
$2\gamma = d + 3$ twice continuously differentiable (p.~87): the cases $N = 0$ and $N = 2$ of
clause (2) of the theorem.
```

(53 words longer. The two kernels are multiples of $e^{-\sqrt2|x|}$ and of
$(1 + \sqrt2|x|)e^{-\sqrt2|x|}$ in the paper's scaling; the constants printed in the source are
not to be used, § 1.) Optional, one sentence more, if the recursive reading is wanted with a
source of the field: "On the line the kernel of index $2$ is the smoothing function of Deriche's edge
detector (\sscite{deriche1987using}, (67)--(68), p.~178)."
[`READING-burgeth2005bessel.md`, §§ 3 and 5; `READING-aronszajn1961theory.md`, § 3;
`READING-deriche1987using.md`.]

### 10.5 The two sentences on time-causal scale space

§ 1 (`01-introduction.tex:311–313`), replace "In time-causal scale space a kernel is the law of
a random delay on $[0,\infty)$, and the families are classified in the author's paper
\sscite{fagerstrom2026hemigroup} (version~1.1.0, Thm.~7.3)." by:

```latex
A time-causal scale space measures a signal in time from its past alone
(\sscite{koenderink1988scale}; \sscite{lindeberg1996scalespace};
\sscite{fagerstrom2005temporal}; \sscite{lindeberg2016time}). Under the hemigroup axioms its
kernels are the laws of random delays on $[0,\infty)$, and the families are classified in the
author's paper \sscite{fagerstrom2026hemigroup} (version~1.1.0, Thm.~7.3).
```

§ 2.3 (`02-line-papers.tex:236–237`), replace "In time-causal scale space a kernel is a law on
the half-line $[0,\infty)$ of delays:" by "In the time-causal theory of the same axioms
\sscite{fagerstrom2026hemigroup} a kernel is a law on the half-line $[0,\infty)$ of delays:".

(20 words longer in all.)

**The sum for the main text**, by one count throughout: § 10.2 is 42 words longer, § 10.3 120,
§ 10.4 70 and 53, § 10.5 20, the two clauses of § 2 about 15: some 320 words, two thirds of a
page, in a main text that ends on its last allowed page. The response plan has to find them;
reviewer E's § 7.5 names where.
[`READING-koenderink1988scale.md`, p. 159; `READING-lindeberg1996scalespace.md`, pp. 229, 231;
`READING-fagerstrom2005temporal.md`, pp. 97, 100; `READING-lindeberg2016time.md`, p. 50.]

### 10.6 The rows of the Sources table (`sources.tex`)

The table is the one place of the attributions in probability. The scale-space attributions stay
in § 1 and in Example 3.14, once.

- **Row of Theorem 3.12.** Replace "(the source quoted in Example~\ref{ex:matern})" by "(the
  sources quoted in Example~\ref{ex:matern}, where two of the kernels above the threshold are
  given with their derivatives)".
- **Row of Proposition 3.15, the shape.** Append:

```latex
That a self-decomposable law on $\RR^d$ which is not degenerate is absolutely continuous:
\sscite{sato1999levy}, Thm.~27.13, p.~181, proved by Sato in 1982 (p.~196).
```

- **Row "Proposition 3.16, on the line, and the method of its proof".** Append:

```latex
The constant of the mass of a ball in clause (1), $R(d,c)\,|S^{d-1}|/c$, is the constant of
these two theorems at the index $c$.
```

- **Row of Proposition 3.17, the rate through the profile.** Replace the cell by:

```latex
On the line: the same theorem of Sato and Yamazato, with their lemma cited at
Corollary~\ref{cor:origin-profile-exponent} above. In $\RR^d$, for the \Levy{} processes whose
laws have radially nonincreasing densities and as the time $\tau$ tends to $0$: the density at
$x$ is asymptotic to $\tau$ times the \Levy{} density at $x$ times the transform of the law at
the frequencies of length $1/|x|$ (\sscite{grzywny2019asymptotic}, Thm.~3.9). The constant
$R(d,\tau c)$ of the proposition for the law at time $\tau$ agrees with it in that limit.
```

- **Row of the two bounds.** Append:

```latex
The two-sided estimates of \sscite{bogdan2014density} for such processes assume an exponent
whose growth lies between two powers of positive order ((19), p.~9, of the arXiv version), which
a finite $c$ excludes.
```

- **Row of Proposition 3.19 and Corollary A.9.** Replace the sentence "See also … Corollary
  A.9(2)." by:

```latex
See also \sscite{daley2014dimension}: Prop.~11 with (3.8), p.~1821, for the radius law of a
radial characteristic function in a lower dimension, the law of its radius times an independent
variable with values in $(0,1)$. The formula of Lemma~\ref{lem:shadow-polar-profile} is (3.8)
with the \Levy{} measure in place of the law. And Lemma~12, p.~1822: $\Omega_d$ is a
characteristic function on $\RR^d$ and not on $\RR^{d+1}$, which is the last assertion of
Corollary~\ref{cor:dictionary-filtration}(2).
```

- **No change**: the row of the dictionary (Schoenberg for the chain and its intersection,
  Gneiting for the strictness) and the attribution of the polar criterion in § 2.6.

[`READING-sato1999levy-thm-27-13.md`; `READING-cygan2017asymptotic.md`, § 3;
`READING-grzywny2019asymptotic.md`, § 2; `READING-bogdan2014density.md`, § 2;
`READING-daley2014dimension.md`, § 1; `READING-daley2014dimension-montee.md`, § 2.]

### 10.7 What should not be written

- "the Pauwels family was derived by Iijima" (§ 3′).
- "the shadow is Matheron's descente" (§ 6).
- That the recursive Gaussians of Deriche (1993) or of Young and van Vliet are Matérn kernels
  (§ 5).
- Schoenberg (1938) for $\Omega_d \notin \Phi_{d+1}$ at pp. 816–817 (§ 7a).
- That the relativistic kernels are members of the class: true by reviewer E's argument, and
  carried by no statement of the paper (`READING-burgeth2005relativistic.md`).
- Any constant from p. 87 of Burgeth et al., or their definition $\tau^nG^n_t(\tau x)$ of the
  scaled kernel (§ 1).

## 11. Not held

For the librarian's acquisition queue (`library acquire request`). DOIs from
`library acquire identify` on 2026-10-13.

| source | DOI | what it would settle |
|---|---|---|
| M. Nielsen, L. Florack and R. Deriche, "Regularization, scale-space, and edge detection filters", J. Math. Imaging Vision 7 (1997), 291–307 (also ECCV 1996, LNCS 1065, doi:10.1007/3-540-61123-1_128) | 10.1023/A:1008282127190 | Item 5: whether first-order Tikhonov regularization is stated there with the transform $(1 + \lambda\omega^2)^{-1}$ and its kernels on the line and in the plane, so that the Matérn kernels of integer index have a second scale-space source. Needed only if the paper cites it. |
| G. Matheron, *Les variables régionalisées et leur estimation*, Masson, Paris, 1965 | none | Item 6: Matheron's own definitions of montée and descente, and whether an operator of order one (integration along one coordinate) is among them. Needed only if the paper wants that vocabulary. |
| T. Gneiting, "Compactly supported correlation functions", J. Multivariate Anal. 83 (2002), 493–508 | 10.1006/jmva.2001.2056 | Item 6: the "dimension walks" as reviewers D and E cite them. Daley and Porcu (held) print the two operators and cover the need. |
| K. Sato, "Class L of multivariate distributions and its subclasses", J. Multivariate Anal. 10 (1980), 207–232 | 10.1016/0047-259X(80)90014-7 | Item 7b: a direct citation of the polar criterion in $\mathbb R^d$; now through Sato's book, p. 117, with Wolfe (1978, held). |
| K. Sato, "Absolute continuity of multivariate distributions of class L", J. Multivariate Anal. 12 (1982), 89–94 | 10.1016/0047-259X(82)90085-9 | Item 7b: a direct citation of the absolute continuity; now through Sato's book, Thm. 27.13, p. 181, and p. 196. |
| T. Iijima, "Basic theory on normalization of pattern (in case of typical one-dimensional pattern)", Bull. Electrotech. Lab. 26 (1962), 368–388 (in Japanese; `iijima1962basic` is a record without a file) | none | Item 3: Iijima's axioms at his own page. The paper can cite him through Weickert, Ishikawa and Imiya (held), as the line paper does. |
| The 1998 survey of E. Pauwels that reviewer A read (a CWI report; not identified) | — | Item 3′: what Pauwels says of Iijima. Not needed: Weickert et al. report Iijima's result. |

Not needed, listed so that it is not asked for again: L. Golinskii, M. Malamud and L. Oridoroga,
"Radial positive definite functions and Schoenberg matrices with negative eigenvalues", Trans.
Amer. Math. Soc. 370 (2018), 1–25, doi:10.1090/tran/6876 (item 7a: the statement is in Daley and
Porcu 2014, held).

Held and cited above at the first page only: `koenderink1988scale`, `lindeberg1996scalespace`,
`fagerstrom2005temporal`, `lindeberg2016time`, `felsberg2001scale`. Held and not read for this
record, the cone paper's audit having read them: `deriche1993recursively`, `young1995recursive`,
`vanvliet1998recursive`. Held and named by reviewer E outside the eight items:
`madan1990variance`, `whittle1954stationary` (`READING-whittle1954stationary.md`),
`wendel1952left`, `babaud1986uniqueness`, `yuille1986scaling`, `witkin1983scale`,
`lindeberg1990scalespace`, `lindeberg2023time`.

## Appendix: the numerical checks

Run with `uv run --with mpmath python` on 2026-10-13; the script is reproduced here and kept
nowhere else.

```python
from mpmath import besselk, gamma, pi, sqrt, exp, mpf, quad, inf, cos

def G(n, x, t):                       # Burgeth et al., p. 86
    r = abs(x); nu = (n - t) / 2
    return besselk(nu, r) / r**nu / (sqrt(pi)**n * sqrt(2)**(n + t - 2) * gamma(t / 2))
def printed1(n, x): return exp(-abs(x)) / (pi**(n / 2.) * 2**n * gamma((n + 1) / 2.))
def printed3(n, x): return (1 + abs(x)) * exp(-abs(x)) / (pi**(n / 2.) * 2**(n + 1) * gamma((n + 3) / 2.))
def p(d, g, x):                       # the paper's (3.7)
    r = abs(x)
    return 2 / ((2 * pi)**(d / 2.) * gamma(g)) * (r / sqrt(2))**(g - d / 2.) * besselk(g - d / 2., sqrt(2) * r)
def R(d, c): return gamma((d - c) / 2.) / (2**c * pi**(d / 2.) * gamma(c / 2.))
def S(d): return 2 * pi**(d / 2.) / gamma(d / 2.)

x = mpf('0.7')
for n in (1, 2, 3): print(n, G(n, x, n + 1) / printed1(n, x), G(n, x, n + 3) / printed3(n, x))
print(2 * quad(lambda y: G(1, y, 2), [0, inf]))
for d, g in ((1, .75), (2, .75), (3, 2.), (2, 1.5)):
    y = mpf('0.37'); print(d, g, p(d, g, y) / (2**(d / 2.) * G(d, sqrt(2) * y, 2 * g)))
a, u = mpf('1.3'), mpf('0.9')
print(2 * quad(lambda y: (1 + a * y) * exp(-a * y) * cos(u * y), [0, inf]) / (4 * a**3 / (a * a + u * u)**2))
for d in (1, 2, 3): print(d, R(d, 1e-6) / 1e-6, gamma(d / 2.) / (2 * pi**(d / 2.)))
for d, c in ((2, 1.5), (3, .7), (5, 1.9)):
    Ic = (4 * pi)**(-d / 2.) * S(d) * 2**(d - c - 1) * gamma((d - c) / 2.)
    print(d, c, Ic / gamma(1 + c / 2.), 2**(-c) * gamma((d - c) / 2.) / (gamma(d / 2.) * gamma(1 + c / 2.)), R(d, c) * S(d) / c)
for d in (1, 2, 3): print(d, 2 * S(d) / S(d + 1), 2 * gamma((d + 1) / 2.) / (gamma(.5) * gamma(d / 2.)))
```

Output, in the order of the prints:

- the general formula over the printed constant of p. 87, for $n = 1, 2, 3$, both displays:
  $1.7724538509 = \sqrt\pi$ six times; the mass of $G_1(\cdot,2)$: $1.0$;
- the paper's (3.7) over $2^{d/2}G_d(\sqrt2\,x, 2\gamma)$ at four pairs $(d,\gamma)$: $1.0$;
- the transform of $(1 + \alpha|x|)e^{-\alpha|x|}$ over $4\alpha^3/(\alpha^2 + u^2)^2$: $1.0$;
- $R(d,\tau c)/(\tau c)$ at $\tau c = 10^{-6}$ against $\Gamma(d/2)/(2\pi^{d/2})$:
  $0.50000029$ and $0.5$; $0.15915492$ and $0.15915494$; $0.07957744$ and $0.07957747$;
- $I_c/\Gamma(1 + c/2)$, the constant of Cygan–Grzywny–Trojan at $\alpha = c$, and
  $R(d,c)|S^{d-1}|/c$: equal to twelve digits at three pairs $(d,c)$;
- $2C_d$ against the constant of the beta density $f_{d|d+1}$: equal for $d = 1, 2, 3$.
