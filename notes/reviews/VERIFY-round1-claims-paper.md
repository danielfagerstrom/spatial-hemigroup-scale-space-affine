# Verification of the round-1 content review (affine paper): the headline claims

**What this is.** The verification that article-kit `PROCESS.md` § 9 requires before a referee
finding changes anything: each finding in the scope below is checked against the printed build, the
paper sources, the blueprint and the open problems, and given a verdict and, where action is
warranted, a minimal fix with its class. Nothing in the paper, the blueprint or the Lean was edited.

**Scope.** The headline claims and the claims-level wording: report § 2 items 1–6 (every
sub-bullet), § 7 first bullet (the abstract's $C_\alpha$), § 8 required changes 1, 2, 3, 4, 5 and 8,
and suggestions 2 and 5. The mathematics of § 3, the numbers, the references and the exposition are
other verifiers' scope.

**Inputs.**
- Report: `records/affine/reviews/review-content-review-1-Gemini-4.0-Argon-High.md`.
- Build read by the referee: `records/affine/reviews/review-build-review-1.pdf` (108 pp.; page numbers
  below are its printed pages, read with `pdftotext -layout`).
- Sources of that build: `paper/main.tex` (abstract), `paper/01-introduction.tex`,
  `paper/04-classical.tex` (Def. 3.1, Thms 3.6–3.7), `paper/05-landscape.tex` (§§ 4.1–4.2),
  `paper/05-table.tex` (§ 4.3, Table 2), `paper/05-orbits.tex` (Props 4.7, 4.13, 4.18, 4.20),
  `paper/05-wedge-axis.tex` (Thm 4.21), `paper/05-shape-adapted.tex` (§ 4.8, Prop 4.22, Table 3),
  `paper/05-smaller-groups.tex` (§ 4.9), `paper/06-open-problems.tex` (§ 5, § 5.1),
  `paper/appendix-smaller-groups.tex` (Props F.1–F.5), `paper/appendix-similarity-loewner.tex`
  (Prop H.1); blueprint node `prop:shape-adapted-apertures` in
  `blueprint/src/parts/05-shape-adapted.tex` (its annotation).
- No source outside the repository was needed: every finding in scope is internal to the paper.

**Verdict key.** **CONFIRMED**: the referee is right. **PARTLY**: part of the finding holds, and the
section says exactly which part. **REFUTED**: the paper is right as printed. **Fix class**: *safe* =
narrows a claim to what is proved, fixes a wording or a typo, completes a citation (allowed to a
session by `adr/0003`); *author* = changes what the paper claims or its structure, or chooses between
substantive routes. Every fix below is in paper prose (abstract, §§ 1, 4.3, 4.8, 4.9, 5, Table 2,
Table 3), none in a statement shared with the blueprint, so none needs a blueprint change first.

---

## F1. "Classification" and the completeness of Table 2 (report § 2 item 1; § 8 required change 4)

### F1a. The abstract's "classifies … completely in some cases"

**Report.** "The Abstract (p. 1) states that *'The main result classifies the families of three groups
(general linear, similarities, positive diagonal) along the ray, stable and Loewner orders, completely
in some cases.'* … Out of the nine cells … **only two cells** — (GL(d), rays) … and (GL(d), Loewner) —
are complete classifications on PSD(d). A third cell, (D+(d), Loewner), is classified only on the
positive definite diagonal matrices … The remaining six cells are incomplete." § 1 of the report:
"claiming a 'classification' when 7 of the 9 cells of Table 2 are incomplete".

**PDF p. 1 prints:** "The main result classifies the families of three groups (general linear,
similarities, positive diagonal) along the ray, stable and Loewner orders, completely in some cases."
**PDF p. 3** (§ 1) prints the qualified form: "The main result of the paper is the classification of
the families in dimension d ≥ 2 over the two choices, Table 2 in §4.3. … For each group and each order
the table says what is known of the families, a complete description in some cases and bounds or
examples in the others, and cites the statements that prove it."

**Check, cell by cell** (Table 2, PDF p. 31; each against the statements it cites and § 5.1):

| cell | what the cited statements prove | complete? | what it lacks |
|---|---|---|---|
| GL(d), rays | Prop 3.4(3): kernels from scale zero are $(\Sigma^{1/2})_*\mu_I$, $\mu_I$ rotation invariant, self-decomposable, $\ne\delta_0$; "Conversely every such $\mu_I$ is the isotropic member of exactly one" family. Prop 4.5 the same off the scheme. | **yes, on PSD(d)** | — |
| GL(d), $\le_\alpha$ | Thm 4.21(3)(c): $\mathfrak F_\alpha \ni S_\gamma(I)$ iff $\gamma\ge\alpha$; contains the law of every profile with $R(\lambda)\ge\lambda^\alpha$ (sufficient only). After the theorem (p. 49): "that $\mu_I \in \mathfrak F_\alpha$ forces $R(\lambda) \ge \lambda^\alpha$ is the open converse of Proposition 4.13". | **no** | the converse (Open Problem 1); and laws outside the profile class of Prop 4.13 (a nonincreasing radial profile $k$, no Gaussian part) are not addressed. Exact only among the stable orbits. |
| GL(d), Loewner | Thm 3.6: iff the affine Gaussian scale space, $b>0$. | **yes, on PSD(d)** | — |
| S(d), rays | Prop F.3(2): the families are exactly the maps of Prop 3.4(2) (continuous, covariant, trivial at 0 and not at $I$, every kernel self-decomposable), determined by the kernels at $\mathrm{diag}(\sigma)$, $\sigma\in\Delta_d$. | **an exact (iff) characterization, implicit** | which choices of kernels on $\Delta_d$ extend to a continuous field on PSD(d) (Open Problem 4, first sentence). |
| S(d), $\le_\alpha$ | Prop 4.20(3)–(5): necessary conditions (infinitely divisible, symmetric, $\mathrm{es}(\psi_\Sigma)\le 4\,\mathrm{ecc}(\Sigma)^{(d+\alpha)/\alpha}$); inclusions; one family in neither neighbour. | **no** | any characterization; the sharp exponent (Open Problem 5(a)). |
| S(d), Loewner | Prop 4.20(4): $\mathrm{es}(\psi_\Sigma)\le 4\,\mathrm{ecc}(\Sigma)$; Props H.5, H.6, H.7, H.8, H.9; H.1(3) an example. | **no** | any characterization; a necessary condition for bounded shape (Open Problem 5(b)); 5(c), 5(d). |
| D+(d), rays | Prop F.4(2): the families are the maps of Prop 3.4(2); on the frame's shapes exactly $(D_s)_*\mu_I$ with any self-decomposable $\mu_I\ne\delta_0$, each realized by $\Sigma\mapsto(\Delta(\Sigma)^{1/2})_*\mu_I$. | **complete on the frame's shapes; exact (iff) but implicit off them** | which fields over $\mathrm{Corr}(d)$ extend continuously (Open Problem 4, second sentence). |
| D+(d), $\le_\alpha$ | Prop F.5(2): on the frame's shapes, $\mu_I$ is $B$-self-decomposable for every $B\in\mathcal D_\alpha$ (necessary only); F.5(3) two sources of families; F.5(4) strictness. | **no, not even on the frame's shapes** | the converse of F.5(2) and every family off the frame's shapes (Open Problem 4, third sentence). |
| D+(d), Loewner | Prop F.4(3): on the orbit of $I$ the kernels are $\otimes_i(s_i)_*\nu_i$, $\nu_i$ self-decomposable, not all $\delta_0$, and conversely every such product extends by $\Sigma\mapsto(\Delta(\Sigma)^{1/2})_*(\nu_1\otimes\dots\otimes\nu_d)$. | **complete on the frame's shapes only** | the families off the frame's shapes (only one extension is given). § 5.1 does not name this cell explicitly; Problem 4's "the same question over the correlation matrices for the positive diagonal group (Proposition F.4)" is the ray question. |

So: two cells complete on all of PSD(d); two more (the ray cells of the smaller groups) exact iff
characterizations whose explicit parametrization is open; one (D+, Loewner) complete on the frame's
shapes; four (GL along $\le_\alpha$, both similarity cells off the rays, D+ along $\le_\alpha$)
described by necessary or sufficient conditions, bounds and examples.

**Verdict: PARTLY.** "Completely in some cases" is true (two cells complete, three more complete in a
restricted sense), and § 1 (p. 3) states the qualification exactly. But the abstract's main verb,
"classifies the families of three groups … along the ray, stable and Loewner orders", claims a
classification of all nine cells, and four of them are not classified in any sense. The referee's
count "7 of 9 incomplete" is too high: the (S, rays) and (D+, rays) cells are iff characterizations
(Prop 3.4(2)) with an open parametrization, and (D+, Loewner) is complete on the frame's shapes.

**Fix (safe, abstract in `paper/main.tex`).** Bring the abstract to § 1's wording, e.g. "The main
result describes the families of three groups (general linear, similarities, positive diagonal) along
the ray, stable and Loewner orders, completely in some cases and by bounds or examples in the others."
(Word budget: +6 words against the 250-word limit the header comment records; F3's fix can recover
them.)

### F1b. § 5's "two descriptions stop short of a classification"

**Report.** "Section 5 (p. 55) is wrong by omission … omits that (i) (S(d), rays) stops short of
classifying which choices of self-decomposable laws on the simplex $\Delta_d$ extend continuously …
(ii) (D+(d), rays) and (D+(d), Loewner) do not classify the families off the diagonal matrices over
Corr(d) … and (iii) (D+(d), $\le_\alpha$) does not even classify the families *on* the frame's shapes".

**PDF p. 55 prints:** "Within these limits two descriptions stop short of a classification: the orbit of
a general profile is described by a sufficient condition, and the similarity row through bounds on the
shape of its kernels."

**Check.** The sentence names (GL, $\le_\alpha$) ("the orbit of a general profile … sufficient
condition") and "the similarity row" ("through bounds"). Against the table above it (i) omits
(D+, $\le_\alpha$), which is incomplete on the frame's shapes themselves (Prop F.5(2) necessary only,
converse open by Open Problem 4); (ii) omits (D+, Loewner) off the frame's shapes; (iii) omits the open
continuous-field questions of the two smaller-group ray cells (Open Problem 4); and (iv) mislabels the
(S, rays) cell, which is not described "through bounds" but by an iff characterization (Prop F.3(2))
with an open parametrization. The referee's points (i) and (iii) hold as stated; (ii) holds, with the
precision that for the Loewner cell § 5.1 does not name the gap.

**Verdict: CONFIRMED.**

**Fix (safe, `paper/06-open-problems.tex`).** Replace the sentence so that it accounts for every cell,
e.g.: "Within these limits four cells of Table 2 stop short of a classification: the general linear row
along the stable orders, where the orbit of a general profile is described by a sufficient condition;
the similarities along the stable and Loewner orders, described through bounds on the shape of their
kernels; and the diagonal group along the stable order, where the condition on the frame's shapes is
necessary and its converse open. Three more are classified on part of their parameter set: the ray
cells of the two smaller groups up to which kernels extend to a continuous field over the shapes, and
the diagonal group with the Loewner order on the frame's shapes (problems 1, 4 and 5)." Optionally
(safe) add to Open Problem 4 one clause naming the (D+, Loewner) families off the frame's shapes, so
that the sentence's pointer is complete.

### F1c. Table 2, cell (D+(d), $\le_\alpha$)

**Report.** "It reads *'on the frame's shapes $(D_s)_*\mu_I$ with $\mu_I$ operator-self-decomposable for
every diagonal exponent in $K_\alpha$; … off the frame's shapes not described (Proposition F.5)'*, which
presents the necessary condition on the frame's shapes as if it were a characterization".

**PDF p. 31 prints:** "on the frame's shapes (Ds)∗µI with µI operator-self-decomposable for every
diagonal exponent in Kα; strictly between the restricted Loewner cell and the ray cell, and not the
union of the restrictions of the Loewner and GL(d) cells; off the frame's shapes not described
(Proposition F.5)".

**Check.** Prop F.5(2) is one-directional: "The kernels from scale zero of a $(\mathrm D_+(d),
\le_\alpha)$-cascade family … are, on the orbit of $I$, $\mu_{D_s^2} = (D_s)_*\mu_I$ … where
$\mu_I \ne \delta_0$ is $B$-self-decomposable for every $B \in \mathcal D_\alpha$". The prose after F.5
(p. 92) says "Its converse … [is] part of problem 4", and Open Problem 4 says "the converse of
Proposition F.5(2) … [is] not described". The cell is written in the same form as the (D+, rays) cell
beside it, "on the frame's shapes the images $(D_s)_*\mu_I$ of any self-decomposable $\mu_I$", which
*is* a characterization; read side by side, the stable cell reads as one too.

**Verdict: CONFIRMED.**

**Fix (safe, Table 2 in `paper/05-table.tex`).** "on the frame's shapes $(D_s)_*\mu_I$ with $\mu_I$
operator-self-decomposable for every diagonal exponent in $K_\alpha$, a necessary condition whose
converse is open; …".

### F1d. Table 2, cell (D+(d), Loewner)

**Report.** The cell "States *'on the frame's shapes the products … of self-decomposable laws on the
line'*, without noting in the cell that off the frame's shapes only one extension … is given and the
general classification off the diagonal is open."

**PDF p. 31 prints:** "on the frame's shapes the products (s1)∗ν1 ⊗ · · · ⊗ (sd)∗νd of self-decomposable
laws on the line (Propositions F.2 and F.4(3))".

**Check.** Prop F.4(3) proves the product form "on the orbit of $I$" and, conversely, that each product
extends by $\Sigma \mapsto (\Delta(\Sigma)^{1/2})_*(\nu_1\otimes\dots\otimes\nu_d)$; nothing describes the
families off the frame's shapes. The cell says "on the frame's shapes" and is accurate as far as it
goes, but unlike the two cells to its left it does not say that the rest is undescribed.

**Verdict: CONFIRMED** (an omission in the cell, not a false statement).

**Fix (safe, Table 2).** Append "; off the frame's shapes one extension, $(\Delta(\Sigma)^{1/2})_*
(\nu_1\otimes\dots\otimes\nu_d)$, and the families not described". If F1b's optional clause is added to
Open Problem 4, cite it here.

---

## F2. One rank-deficient step for GL(d) (report § 2 item 2; § 8 required change 1)

### F2a. "admits the Gaussian alone" (abstract) and "admits only Gaussian families" (§ 1)

**Report.** "saying that any such order $W$ *'admits the Gaussian alone'* is false unless $W$ is
**contained in the Loewner order**. If $W$ contains a rank-deficient Loewner step $wI \le_W wM$ *and*
also contains a step $\Sigma \le_W \Sigma'$ where $\Sigma' - \Sigma$ is not positive semidefinite, then
$e^{-b\langle\omega,(\Sigma'-\Sigma)\omega\rangle}$ is not a characteristic function and $W$ **admits no
family at all** … The Abstract and §1 must say *'admits at most the Gaussian …'*".

**PDF p. 1 prints:** "For the general linear group, an order with one step from a positive definite
matrix that widens the aperture in some directions and leaves it unchanged in the others admits the
Gaussian alone."
**PDF pp. 3–4 print:** "A linear map carries such a step to one from the identity, so for the general
linear group every order of the scheme that contains one rank-deficient step admits only Gaussian
families (Proposition 4.22(3))."

**Check.**
- *Does the scheme require $W \subseteq$ Loewner?* No. Definition 3.1 asks of $\le_W$ only that it be "a
  partial order … on PSD(d) that is *G-invariant* … and *contains the rays*". Containment in the Loewner
  order is a hypothesis of individual statements (Prop F.3(4): "contained in the Loewner order"), not of
  the scheme, and the paper itself studies orders outside it: Thm 4.21(2)(a), "If $C \not\subseteq
  \mathrm{PSD}(d)$, there is none."
- *Can the referee's case arise?* Yes. A GL(d)-invariant order can contain both a rank-deficient
  Loewner step and a non-Loewner step: e.g. $\preceq^+_C$ of Thm 4.3(4) for an $O(d)$-invariant pointed
  cone $C \ni I$ that contains $e_1e_1^{\mathsf T}$ and a matrix with a negative eigenvalue
  ($C = \{X : \operatorname{tr} X \ge \kappa\|X\|_F\}$, $0 < \kappa < 1$ suitable, is one). By Thm 4.21(2)(a)
  it carries no family.
- *What Prop 4.22(3) proves.* "for every $(\mathrm{GL}(d), W)$-cascade family of kernels there is a
  $b > 0$ with $\widehat\mu_{\Sigma,\Sigma'}(\omega) = e^{-b\langle\omega,(\Sigma'-\Sigma)\omega\rangle}$ for
  every pair $\Sigma \le_W \Sigma'$" — a statement about every family, with no existence claim. The
  blueprint annotation of `prop:shape-adapted-apertures` says so explicitly: "**Not claimed**: … the
  existence of a $(\mathrm{GL}(d), W)$-family in (3), which needs $\Sigma' - \Sigma$ positive semidefinite on
  every pair of $W$."
- *The two sentences.* § 1's "admits only Gaussian families" is exactly clause (3): every family it
  admits is Gaussian, vacuously so when there is none. The abstract's "admits the Gaussian alone" reads
  as "admits the Gaussian, and nothing else", which asserts existence; that holds only when $W \subseteq$
  Loewner (then the affine Gaussian scale space restricts by Lemma 3.3(1) and Thm 3.6), and fails in the
  case above.

**Verdict: PARTLY.** CONFIRMED for the abstract (the wording asserts an existence that Prop 4.22(3)
does not prove and that fails for orders outside the Loewner order). REFUTED for § 1: "admits only
Gaussian families" is exact as printed.

**Fix.** (i) *safe*, abstract: "… admits only Gaussian families" (or "admits no family but the
Gaussian"), the wording of § 1 and of clause (3); same word count. (ii) Optional, *author*: stating the
dichotomy the referee proposes ("and admits them exactly when the order lies in the Loewner order; none
otherwise") in the abstract or after Prop 4.22 is a new claim. It follows in two lines from Lemma 3.3(1),
Thm 3.6 and clause (3), but no node states it, and the blueprint annotation lists the existence as not
claimed; adding it would be a widening, so it is the author's call (and, if wanted, belongs in the node
first).

### F2b. Does § 1 say where Theorem 3.7's affine-orbit form comes from?

**Report.** "§1 (p. 3) should note when citing Theorem 3.7 that the single-step theorem assumes the
affine-orbit form $\widehat\mu_\Sigma(\omega) = e^{-g(\langle\omega,\Sigma\omega\rangle)}$, which in the
scheme comes from GL(d)-covariance together with the ray cascade."

**PDF p. 3 prints**, in the sentences just before the citation of Thm 3.7: "One step decides it. The
axioms make every aperture a linear image of the aperture at the identity, which is rotation invariant
(Lemma 3.9). Call a step Σ → Σ′ … rank-deficient … The increment of one such step is a probability
measure only for the Gaussian (Theorem 3.7)." And p. 4, next paragraph: "Along the rays alone the
families of the general linear group are the affine orbits of the rotation-invariant self-decomposable
laws (Proposition 4.5)."

**Check.** Lemma 3.9 (`lem:affine-reduction`) is the reduction to the form
$e^{-g(\langle\omega,\Sigma\omega\rangle)}$, and § 1 cites it as the source of the form one sentence before
it cites Thm 3.7. For a general order $W$ the same form comes from the rays (Prop 3.4(3), used in the
proof of Prop 4.22(3)); § 1 does not cite 3.4(3) at that sentence but states the ray result in the next
paragraph.

**Verdict: REFUTED.** § 1 says where the form comes from (Lemma 3.9), in the sentence before the
citation.

**Fix.** None needed. Optional (safe): cite Prop 3.4(3) beside Prop 4.22(3) in § 1's sentence on
"every order of the scheme", since for a general $W$ that is where the form comes from.

---

## F3. Shape-adapted apertures; "w and s are variances" (report § 2 item 3; § 8 required change 8)

**Report, assessment.** "This claim is completely supported by Proposition 4.22(1)–(2) … The
qualification in the Abstract … and in §1 (p. 4) matches the hypotheses of Proposition 4.22(2) and
Proposition 4.4 exactly." Checked: Prop 4.22(2) takes $g$, $\mu_I$ and the orbit "as in Proposition 4.4"
(continuous, nonnegative $g$, $g(0)=0$, $e^{-g(|\omega|^2)}$ a characteristic function, so a positive
transform), and its conclusion is "if and only if $g(u) = bu$ for some $b \ge 0$". The abstract's "among
linear images of rotation-invariant laws with a positive transform only the Gaussian reaches them by
further smoothing" matches ($b = 0$ is $\delta_0$, the degenerate Gaussian). **Agreed; no action.**

**Report, terminology.** "On p. 51, the author writes *'w and s are variances, not volume scales. At the
boundary the variance along the minor axis is $n_1^{-d/\alpha}$ times that of the first stage.'* For
$0 < \alpha < 2$, an $\alpha$-stable law has **infinite variance**; $w$ and $s$ are matrix scale parameters
in the variance gauge, not variances."

**PDF p. 51 prints:** "For the stable orbit of index α, write wI for the first stage, as in
Proposition 4.22, and sS for an aperture of shape S, with det S = 1 and least eigenvalue n1; w and s are
variances, not volume scales. … At the boundary the variance along the minor axis is n1^{−d/α} times
that of the first stage."

**Check.** In the example $\mu_{wI} = (\sqrt w\,I)_*S_\alpha(I)$ and $\mu_{sS} = ((sS)^{1/2})_*S_\alpha(I)$,
$0<\alpha<2$; $S_\alpha(I)$ has transform $e^{-|\omega|^\alpha}$ and no second moment, so $w$, $s$ and
"the variance along the minor axis" ($s\,n_1$) are not variances of the kernels. What they are is fixed
in the paper's own terms: the aperture matrix is "proportional to its covariance in the Gaussian case"
(§ 1, p. 2), and the *variance gauge* is defined in § 3.1 (p. 18, after Prop 3.4) and Prop A.3 as "the
coordinate in which the scale of the Gaussian member is proportional to its variance". The sentence
contrasts $w$, $s$ (squared-length parameters) with the volume scale $t$ of Lemma 4.1, which is right in
intent; the word "variance" is what is wrong. The same word recurs two lines below the example for the
Gaussian ("the minor axis keeps the variance of the first stage"), where it is correct, and in the
paragraph heading the proposition ("the variance $w$ of the isotropic first stage"), where it describes
the Gaussian practice of Lindeberg and Gårding and is correct there.

**Verdict: CONFIRMED.**

**Fix (safe, `paper/05-shape-adapted.tex`).** "… $w$ and $s$ are scale parameters in the variance gauge,
squared lengths rather than volume scales." and "At the boundary the scale parameter along the minor
axis, $s\,n_1$, is $n_1^{-d/\alpha}$ times that of the first stage." Leave the Gaussian sentence as is.

---

## F4. "Turning" and "turning speed" (report § 2 item 4; § 8 suggestion 2)

**Report, assessment.** The mathematical claims on $C_\alpha$ and the threshold "match Theorem 4.21(3) …
and Proposition 4.7(3) … accurately." Checked: Thm 4.21(3)(c) "$\mathfrak F_\alpha$ contains
$S_\gamma(I)$, $0<\gamma<2$, if and only if $\gamma \ge \alpha$"; (3)(d) "For $2 \le \alpha \le \infty$,
$\mathfrak F_\alpha$ is the set of centred Gaussian laws". **Agreed; no action.**

**Report, terminology.** "In the Abstract (p. 1) and §1 (pp. 3–4), the author uses *'turning speed'* and
*'how fast the shape may turn'* for the bound $\sqrt{n_d/n_1} \le (t_2/t_1)^{d\alpha/(d+\alpha)}$ …
Yet on p. 52 (Table 3) and p. 53 (§4.9), *'turning'* is used in its literal sense (rotating the frame's
axes) … inconsistent."

**Every use** (`grep -n -i turn paper/*.tex`, comments excluded; uses of "turn" as "turns on", "turns …
into", "in turn", "returns" are idiom and not counted):
- *Shape change in general* (the referee's first sense):
  abstract, `main.tex:144`, p. 1: "a non-Gaussian kernel pays in turning speed";
  § 1, `01-introduction.tex:214`, p. 3: "how fast the shape may turn along them";
  § 1, `:253`, p. 4: "Each order limits how fast the shape may turn as the scale grows";
  § 4.1, `05-landscape.tex:118`, p. 26: "3. *Turning.* When the shape is re-estimated as the scale grows,
  the adapted apertures trace a curve in scale and shape, not a ray. … each family limits how fast the
  shape may change along it";
  § 4.6, `05-orbits.tex:123`: "Shape adaptation turns the aperture as the scale grows (§4.1, the third
  use)";
  § 4.8, `05-shape-adapted.tex:138`, p. 52: "*Turning: the speed limit.*", followed by "each family's
  limit on the anisotropy gained by further smoothing";
  § 4.9, `05-smaller-groups.tex:19`, p. 53: "Following a shape across scale and turning remain".
- *Rotation of the axes* (the literal sense):
  Table 3 row "frame families", `05-shape-adapted.tex:167`, p. 52: "the Gaussian's bound along the
  frame's axes only; no turning";
  `05-shape-adapted.tex:178`, p. 52: "The stable orbits turn too, in any orientation";
  § 4.9, `05-smaller-groups.tex:37–38`, p. 53: "Such a family gains anisotropy along its axes as fast per
  step as the Gaussian does and cannot turn, while the stable orbits turn with a smaller gain per step.
  Turning alone therefore does not exclude non-Gaussian kernels."; § 1, `01-introduction.tex:283`, p. 4,
  the same "cannot turn"; `appendix-smaller-groups.tex:78–79` and `appendix-linear-flow.tex:67–68`, the
  same; `05-orbits.tex:372`: "the skew part of $B$, the turning of the flow" (rotation; consistent with
  this sense).

**Check against Prop 4.7(3).** The bound is on "the anisotropy gained, $\sqrt{n_d/n_1}$", with $n_i$ the
eigenvalues of the relative shape $N = S_1^{-1/2}S_2S_1^{-1/2}$; it applies whether $S_2$ is a coaxial
stretch of $S_1$ or a rotation of it (a rotated anisotropic $S_1$ has $N \ne I$), and the clause adds
"the relative shape of a step in the cone may be any $N \ne I$ in that range, with any eigenvectors". So
the quantity priced in the abstract and § 1 is shape change, of which rotation is one kind; under the
literal sense used for the frame families (which do change shape, along their axes, at the Gaussian's
rate), "turning speed" names the wrong quantity. The paper's own § 5 already uses the right words:
"a stable kernel keeps a cascade only at a lower speed of shape change (Table 3)" (p. 54), as does
§ 4.2: "how fast an adapted aperture may change its shape between two scales" (p. 26).

**Verdict: CONFIRMED.** The word carries two senses, and the frame passages ("gains anisotropy … and
cannot turn") only make sense under the second.

**Fix (safe, prose).** Reserve "turn" for rotation of the axes (the frame passages stay as they are) and
say "shape change" for the rest: abstract "pays in speed of shape change"; § 1 (two places) "how fast the
shape may change"; § 4.1 item 3 heading "*Changing shape.*" (or "*Re-estimating the shape.*"); § 4.6 line
123 "Shape adaptation changes the shape of the aperture as the scale grows"; § 4.8 heading "*Shape
change: the speed limit.*"; § 4.9 line 19 "Following a shape across scale and changing it remain". The
main-file comment at `main.tex:123` can follow. Blueprint annotations (`05-smaller-groups.tex:237`,
`:812`) already use only the literal sense; nothing changes there.

---

## F5. Rational symbols cascade at most along rays (report § 2 item 5; § 8 required change 2)

**Report.** "The Abstract states: *'Filters whose symbol in $-\nabla\cdot\Sigma\nabla$ is a decaying rational
function without zeros cascade at most along rays, and so do the linear images of a Matérn law.'*
Section 5 (p. 54) repeats … Proposition 4.18 (p. 45) proves this **only for affine orbits** … for
**fixed** polynomials $P, Q$ independent of $\Sigma$ … Without GL(d)-covariance (for example, if the
rational function coefficients depend on $\Sigma$ under $S(d)$, or if elliptic solves
$(I - s_i^2\partial_i^2)^{-1}$ are applied axis by axis as in Proposition F.2), non-ray cascades exist."

**PDF p. 1 prints:** "Filters whose symbol in −∇·Σ∇ is a decaying rational function without zeros
cascade at most along rays, and so do the linear images of a Matérn law."
**PDF pp. 54–55 print:** "The filters whose symbol in the shape's operator is a decaying rational function
without zeros on [0, ∞), which finitely many elliptic solves compute, keep none across shapes: they
cascade at most along rays (Proposition 4.18)."
**PDF p. 52 prints** (§ 4.8): "The filters whose symbol in the shape's operator is a decaying rational
function without zeros on [0, ∞) cascade at most along rays (Proposition 4.18), and along all of them
when the law is self-decomposable."
**PDF p. 4** (§ 1) prints the exact form: "So are the orbits of a law whose transform is a decaying
rational function of ⟨ω, Σω⟩ without zeros on [0, ∞) (Proposition 4.18)."

**Check.** Prop 4.18's hypotheses: fixed real polynomials $P, Q$ with $\deg P > \deg Q$, $P(0) = Q(0)$,
neither vanishing on $[0,\infty)$; $Q(|\omega|^2)/P(|\omega|^2)$ the characteristic function of a
probability measure $\mu_I$; $\mu_\Sigma := (\Sigma^{1/2})_*\mu_I$, so that $\widehat\mu_\Sigma(\omega) =
Q(\langle\omega,\Sigma\omega\rangle)/P(\langle\omega,\Sigma\omega\rangle)$. Conclusion: a positive finite
increment $\mu_{\Sigma'} = \mu_\Sigma*\rho$ between definite matrices forces $\Sigma' = c\,\Sigma$, $c \ge 1$.
A transform $R(\langle\omega,\Sigma\omega\rangle)$ with *one* rational $R$ for every $\Sigma$ is exactly an
affine orbit, so "symbol in $-\nabla\cdot\Sigma\nabla$" carries the affine-orbit structure only if $R$ is
the same at every $\Sigma$; the abstract does not say so, while it does say "linear images" for the
Matérn law in the same sentence. On the referee's two examples:
- *Axis-by-axis solves* (Prop F.2 / F.4(3) with Laplace factors): the symbol
  $\prod_i(1+s_i^2\omega_i^2)^{-1}$ is not a function of $\langle\omega,\Sigma\omega\rangle$, so it is not a
  "symbol in $-\nabla\cdot\Sigma\nabla$" and does not contradict the abstract or § 4.8 as worded. It does
  bear on § 5's non-restrictive clause "which finitely many elliptic solves compute": such a product
  filter is computed by finitely many elliptic solves (in the axis operators) and does cascade off the
  rays (coordinatewise steps of the frame's shapes), so a reader who takes the clause as the class is
  misled.
- *Σ-dependent coefficients under S(d)*: not verified, and doubtful in the simplest case. With one
  scalar factor, $R(c(\Sigma)\langle\omega,\Sigma\omega\rangle)$ is the Matérn-type orbit at $c(\Sigma)\Sigma$,
  and Prop 4.18 applied to that orbit again allows only rays. No such family is in the paper. The
  finding does not need the example: the hypothesis is missing from the sentence either way.

**Verdict: PARTLY.** CONFIRMED that the abstract, § 4.8 (p. 52) and § 5 (p. 54) drop the hypothesis that
the rational function is one and the same for every $\Sigma$ (the affine orbit of Prop 4.18), and that
§ 5's elliptic-solve clause reads as wider than the result. The referee's assertion that "non-ray cascades
exist" for filters with a Σ-dependent rational symbol in $-\nabla\cdot\Sigma\nabla$ is unsupported; the
axis-by-axis example is not a counterexample to the sentences as worded. § 1 (p. 4) is exact.

**Fix (safe, prose).** Abstract: "The linear images of a law whose transform is a decaying rational
function of $|\omega|^2$ without zeros cascade at most along rays, and so do those of a Matérn law" (or
keep the operator and add "one … for every $\Sigma$": "Filters whose symbol in $-\nabla\cdot\Sigma\nabla$ is
one decaying rational function without zeros, the same for every $\Sigma$, cascade at most along rays").
§ 4.8 (p. 52) and § 5 (p. 54): "The affine orbits whose symbol in the shape's operator is a decaying
rational function without zeros on $[0,\infty)$, the same for every shape, …", and in § 5 make the
elliptic-solve clause restrictive to solves "in the shape's operator" (the class § 4.6 describes after
Prop 4.18: "finitely many solves of shifted equations $(\mathcal L_\Sigma - z)v = w$").

---

## F6. The similarities with the Loewner order (report § 2 item 6; § 8 required change 5, suggestion 5)

**Report, assessment.** "Proposition H.1(3) … and Proposition 4.20(4) … fully support the claim that
non-Gaussian (S(d), Loewner)-cascade families exist and satisfy $\mathrm{es}(\psi_\Sigma) \le
4\,\mathrm{ecc}(\Sigma)$." Checked: H.1(3) gives a family satisfying (K1), (K2), (K4) and (K3) for every
similarity, with a stable part "rotation invariant only when $\Sigma$ is a multiple of $I$"; Prop 4.20(4),
last sentence, gives the bound "with $\varepsilon := \lambda_{\min}(\Sigma)$, $t := \lambda_{\max}(\Sigma)$
and $\mathrm{ecc}(\Sigma)$ in place of $\mathrm{ecc}(\Sigma)^{(d+\alpha)/\alpha}$" for $(G, \text{Loewner})$
families. **Agreed; no action.**

### F6a. "a property of the group"

**Report.** "*'So the rigidity of the general linear group with the Loewner order is a property of the
group, and the Loewner order alone does not force the Gaussian.'* This is a half-truth: GL(d) *alone*
does not force the Gaussian either, since (GL(d), $\le_\alpha$) admits non-Gaussian families for all
$0 < \alpha < 2$ (Theorem 4.21). Rigidity is a joint property of the *pair*".

**PDF p. 4 prints**, in the paragraph "Smaller groups": "For the similarities with the Loewner order
non-Gaussian families survive (Proposition H.1(3)). The exponent of their non-Gaussian part changes under
a rotation by at most a factor of four times the eccentricity of the aperture, the ratio of its extreme
eigenvalues (Proposition 4.20(4)). So the rigidity of the general linear group with the Loewner order is
a property of the group, and the Loewner order alone does not force the Gaussian."

**Check.** In its paragraph the sentence draws the conclusion of H.1(3): keeping the Loewner order and
shrinking the group loses the rigidity, so the rigidity depends on the group. "Is a property of the
group" says more: that the group carries it. That is false by the paper's own results: GL(d) with the
rays admits every rotation-invariant self-decomposable orbit (Thm 4.21(3)(a), Prop 3.4(3)), and with
$\le_\alpha$, $0<\alpha<2$, the stable orbits of index $\gamma \ge \alpha$ (Thm 4.21(3)(c)). The previous
part of § 1 (pp. 3–4) says what forces the Gaussian: GL(d) with one rank-deficient step (Prop 4.22(3)).

**Verdict: CONFIRMED.**

**Fix (safe, `paper/01-introduction.tex:279`).** E.g. "So the rigidity of the general linear group with
the Loewner order needs both: the Loewner order alone does not force the Gaussian, and the general linear
group alone does not either (Theorem 4.21(3))." The intro's header comment at line 132 ("the rigidity is a
property of the group") can follow.

### F6b. $b > 0$ in § 4.9's example

**Report.** "In §4.9 (p. 53), the example from Proposition H.1(3) is stated with $b > 0$ … In fact,
Proposition H.1(3) (p. 94) allows $b = 0$, so the purely non-Gaussian family $\mu_\Sigma =
S_\alpha(\Sigma + \kappa\operatorname{tr}(\Sigma)I)$ is already an (S(d), Loewner)-cascade family with no
Gaussian part at all."

**PDF p. 53 prints:** "For 0 < α < 2, b > 0 and κ > 0 with ακ² − (d + 1)κ − 1 ≥ 0, one is an affine
Gaussian convolved with a stable kernel whose shape is pulled towards the isotropic one, µΣ = N(0, 2bΣ) ∗
Sα(Σ + κ tr(Σ)I)".

**Check.** Prop H.1(3) (`appendix-similarity-loewner.tex`): "Let $b \ge 0$ and $\kappa > 0$ with
$\alpha\kappa^2 - (d+1)\kappa - 1 \ge 0$, and put $h(\Sigma) := \Sigma + \kappa\operatorname{tr}(\Sigma)I$ and
$C(\Sigma) := 2b\Sigma$". The prose after it: "In clause (3) the non-Gaussian part carries the shape of
$\Sigma$, and $b = 0$ is allowed, so no Gaussian part is needed for that." At $b = 0$ (K4) holds, since
$\mu_I = S_\alpha((1+d\kappa)I) \ne \delta_0$. So § 4.9 states a special case; it is not false, but it
hides the stronger fact that the appendix states. Table 2's "not every family is a Gaussian convolved with
a shape-blind part (Proposition H.1(3))" (p. 31) is accurate as printed and needs no change.

**Verdict: CONFIRMED** (for § 4.9; the Table 2 cell is accurate).

**Fix (safe, `paper/05-smaller-groups.tex:22`).** "$b \ge 0$", and "one is an affine Gaussian, trivial
when $b = 0$, convolved with a stable kernel …" (or add after the display: "With $b = 0$ it has no
Gaussian part.").

---

## F7. The abstract's undefined $C_\alpha$ (report § 7 first bullet; § 8 required change 3)

**Report.** "Mentions *'generated by cones $C_\alpha$'* and *'For $0 < \alpha, \gamma < 2$ … from $\alpha = 2$
on'* without defining $C_\alpha$ or explaining what the parameter $\alpha$ represents."

**PDF p. 1 prints:** "Along a chain of invariant orders generated by cones Cα, a non-Gaussian kernel pays
in turning speed. For 0 < α, γ < 2 the linear images of the isotropic γ-stable law cascade along the order
of Cα exactly when γ ≥ α; from α = 2 on only the Gaussian does."

**Check.** The abstract says that $C_\alpha$ are cones generating a chain of invariant orders, and earlier
names "the ray, stable and Loewner orders"; it never says what $\alpha$ indexes, where the chain starts
and ends, or that the order of $C_\alpha$ for $0<\alpha<2$ is the stable order of index $\alpha$ (§ 4.7,
p. 48: "$C_\alpha := \{X \in \mathrm{PSD}(d) : (d+\alpha)\lambda_{\min}(X) \ge \operatorname{tr} X\}$, … from the
rays ($\alpha = 0$) through the stable orders ($0 < \alpha < 2$) … to the Loewner order ($\alpha = \infty$)").
"From $\alpha = 2$ on" is unreadable without that.

**Verdict: CONFIRMED.**

**Fix (safe, abstract).** Either the referee's one-line definition, or, cheaper in words, say what the
index means and drop the symbol: "Along a chain of invariant orders indexed by $0 \le \alpha \le \infty$,
from the rays through the stable orders ($0 < \alpha < 2$) to the Loewner order, a non-Gaussian kernel
pays in speed of shape change. For $0 < \alpha, \gamma < 2$ the linear images of the isotropic
$\gamma$-stable law cascade along the order of index $\alpha$ exactly when $\gamma \ge \alpha$; from
$\alpha = 2$ on only the Gaussian does." Check the 250-word budget with F1a's and F5's changes.

---

## Summary

| finding | verdict | fix | class | where |
|---|---|---|---|---|
| F1a abstract "classifies … completely in some cases" (§2.1) | PARTLY: "some cases" true (2 cells complete on PSD(d), 3 more in a restricted sense); "classifies" overclaims 4 cells; referee's "7 of 9" too high | "describes … completely in some cases and by bounds or examples in the others" | safe | abstract, `paper/main.tex` |
| F1b § 5 "two descriptions stop short" (§2.1, RC 4) | CONFIRMED: omits (D+, ≤α), (D+, Loewner) off the frame's shapes, the ray cells' continuity questions; mislabels (S, rays) as "bounds" | rewrite the sentence to account for every cell; optionally name (D+, Loewner) off the frame's shapes in Open Problem 4 | safe | `paper/06-open-problems.tex` |
| F1c Table 2 (D+, ≤α) (§2.1, RC 4) | CONFIRMED: F.5(2) is necessary only, converse open | add "a necessary condition whose converse is open" | safe | Table 2, `paper/05-table.tex` |
| F1d Table 2 (D+, Loewner) (§2.1, RC 4) | CONFIRMED (omission) | add "off the frame's shapes one extension, the families not described" | safe | Table 2, `paper/05-table.tex` |
| F2a "admits the Gaussian alone" (§2.2, RC 1) | PARTLY: abstract asserts existence Prop 4.22(3) does not give (fails for $W \not\subseteq$ Loewner, Thm 4.21(2)(a)); § 1's "admits only Gaussian families" is exact | abstract: "admits only Gaussian families"; stating the "exactly when $W \subseteq$ Loewner, else none" dichotomy is a new claim | safe (narrowing); author (dichotomy) | abstract; node first if the dichotomy is wanted |
| F2b § 1 on the source of the affine-orbit form (§2.2) | REFUTED: § 1 cites Lemma 3.9 for it one sentence earlier | none; optionally cite Prop 3.4(3) at the "every order" sentence | safe (optional) | `paper/01-introduction.tex` |
| F3 "w and s are variances" (§2.3, RC 8) | CONFIRMED: infinite variance for α < 2; the paper's term is the variance gauge | "scale parameters in the variance gauge"; "the scale parameter along the minor axis, $s\,n_1$" | safe | § 4.8, `paper/05-shape-adapted.tex` |
| F4 "turning" in two senses (§2.4, sugg. 2) | CONFIRMED: shape change in abstract, § 1, §§ 4.1, 4.6, 4.8, 4.9; axis rotation in Table 3, § 4.9 frames, App. F, G | "turn" for rotation only; "shape change" elsewhere (abstract, § 1 ×2, § 4.1 item 3, § 4.6, § 4.8 heading, § 4.9) | safe | prose; no blueprint change |
| F5 rational symbols without the orbit hypothesis (§2.5, RC 2) | PARTLY: abstract, § 4.8, § 5 drop "the same rational function for every Σ" (the affine orbit); referee's "non-ray cascades exist" unsupported, the axis-by-axis example is not such a symbol; § 1 exact | "linear images of a law whose transform is a decaying rational function of $\lvert\omega\rvert^2$ …"; § 5's elliptic-solve clause restricted to the shape's operator | safe | abstract; §§ 4.8, 5 |
| F6a "a property of the group" (§2.6, RC 5) | CONFIRMED: GL(d) with rays or ≤α admits non-Gaussian families (Thm 4.21(3)) | "needs both: neither the Loewner order alone nor the group alone forces the Gaussian" | safe | § 1, `paper/01-introduction.tex:279` |
| F6b $b > 0$ in § 4.9 (§2.6, sugg. 5) | CONFIRMED: H.1(3) has $b \ge 0$; Table 2 cell accurate | "$b \ge 0$", with "no Gaussian part when $b = 0$" | safe | § 4.9, `paper/05-smaller-groups.tex:22` |
| F7 abstract's undefined $C_\alpha$ (§7, RC 3) | CONFIRMED | say what α indexes (rays at 0, stable orders 0 < α < 2, Loewner at ∞), or define $C_\alpha$ | safe | abstract |
