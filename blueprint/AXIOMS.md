# The axiom ledger

This module's **trust boundary**: the analysis it cites rather than proves. Every `[A]` node of
the blueprint names its entries here with `\ledger{A<N>}`, and every entry carries a page-anchored
citation into a held source, read at the page and recorded in `records/affine/`. The rule is the
programme's, inherited from Paper V: prove the structural content, take the deep analysis as an
interface, and keep the boundary as narrow as the argument allows.

Each entry names the Lean axiom(s) it admits in a `**Lean:**` line. They are declared in
`Formalization/AffineHemigroup/Interfaces.lean` (Q-0281, the statement skeleton), each stated at its
page's letter as transcribed in `AXIOMS-verbatim.md`, and listed in `trust-boundary.txt`.
`Formalization/CIAxiomGuard.lean` prints an entry's axiom in the lines of the proved theorems that
spend it, which each entry's `**Lean:**` line names; `linkage check` enforces the entry's shape and its
resolution from the nodes.

Each entry is also a blueprint node, its **interface node** (the author's decision of 2026-10-06,
Paper V's convention): `thm:cited-A<N>` in chapter 2 (`blueprint/src/parts/02-cited-facts.tex`),
the entry's statement as used, `\leanok` on the statement because the axiom is declared, and no
proof. A node that names the entry on its status line uses the interface node, so the dependency
graph shows a proved node as fully proved only when it rests on no entry. The first label of each
`**Blueprint:**` line below is that node.

Format contract (enforced by `linkage check`, fatal checks 2 and 6):

```
## A<N> — <one-line statement of what is taken on trust>
**Blueprint:** `<label>`
**Cite:** @<citekey> — <page anchor>

- **Statement as used.** …
- **Primary — <the named theorem>.** …
```

| chapter | entries |
|---|---|
| Ch. 3 — the isotropic theory: the origin behaviour, and the filtration (§ 3.1) | A1–A4 |
| Ch. 3 — the isotropic theory: the reading (2.1) of the isotropic classification (§ 3.2) | A2–A4 |
| Ch. 5 — the stable orbits' step cone (§ 5.5) and the anisotropy budget (§ 5.6) | A3, A5 |
| Ch. 4, 5 — the null array: infinitely divisible increments of a cascade (§ 4.3), and the similarity cascades (§ 5.6) | A6, A3 |
| Ch. 5 — the cells of smaller groups (§ 5.6): the ray column (no entry), the similarities with the stable order | A6, A3 |
| Ch. 5 — invariant wedges (§ 5.3): orders on $\mathrm{PD}(d)$ and their cones (the logarithmic majorization of a product, since 2026-10-05; `prop:stable-order-generated` spends none), the general linear row along the chain of wedges | A9; A5, A3 |
| Ch. 3 — the isotropic theory: the radially nonincreasing density of the kernels from scale zero (§ 3.1) | A8 (A2, A3 through the polar reading) |
| Ch. 3 — the isotropic theory: the top of the filtration, $\mathcal{A}_\infty = \mathcal{S}$ (§ 3.3, since 2026-10-07) | A10 (A2–A4 through the polar reading) |
| Ch. 3 — the isotropic theory: the rate of the density and of the mass of a small ball at the origin, $0 < c \le d$ (§ 3.1, since 2026-10-11) | A11 (A8, A2, A3 for the existence of the density) |
| Ch. 3 — the isotropic theory: the increment of the density at the centre, $d < c \le d+2$ (§ 3.1, since 2026-10-16) | A11 (A1, A2–A4) |

## A1 — A probability measure on $\mathbb{R}^d$ whose characteristic function has an integrable $n$-th moment has a $C^n$ density vanishing at infinity
**Blueprint:** `thm:cited-A1` (the interface node, ch. 2, since 2026-10-06); `thm:origin-boundedness-d`
**Cite:** @sato1999levy — Proposition 28.1, printed p. 190 (condition (28.1) and its conclusion; the proof on the same page)
**Lean:** `AffineHemigroup.density_of_integrable_charFun` (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent by `AffineHemigroup.origin_density_smooth` and `origin_density_bounded_smooth`, `thm:origin-boundedness-d`(2), and at `n = 0` by `AffineHemigroup.origin_dichotomy`, `thm:origin-boundedness-d`(5), wave 2 of Q-0281); the density is nonnegative, at the page's letter (2026-10-05, below)

- **2026-10-05 — restated at the page's letter** (the author's decision; no new source, no new page). <!-- CHANGED Q-0281 wave 2: A1's Lean conclusion gains `∀ x, 0 ≤ g x` --> The Lean conclusion of `density_of_integrable_charFun` now says that the density is nonnegative, `∃ g, (∀ x, 0 ≤ g x) ∧ ContDiff ℝ n g ∧ μ = g · Lebesgue ∧ …`. Sato's "density $g(x)$" of a probability measure is nonnegative by definition (Prop. 28.1, p. 190, `AXIOMS-verbatim.md` A1); the interface as first typed omitted the sign, so that the measure it named was $g^+ \cdot$ Lebesgue and the $C^n$ function need not have been the density itself (blind review R2-1). The statement as used, the citation and the verdict of the audit are unchanged; what the entry carries is the page's, no wider.

- **Statement as used.** If a probability measure $\mu$ on $\mathbb{R}^d$ satisfies
  $\int_{\mathbb{R}^d}|\hat\mu(z)|\,|z|^n\,dz<\infty$ for some $n\in\mathbb{Z}_+$, then $\mu$ has a
  density $g$ of class $C^n$ on $\mathbb{R}^d$ and the partial derivatives of $g$ of orders
  $0,\dots,n$ tend to $0$ as $|x|\to\infty$. Read at $n=0$ it says: an integrable characteristic
  function gives a bounded continuous density vanishing at infinity.
- **Primary — Sato, Proposition 28.1, p. 190.** Stated in $\mathbb{R}^d$ and proved there, by
  Fourier inversion (the book's Proposition 2.5(xii)), differentiation under the integral sign,
  and the Riemann–Lebesgue theorem. The dimension enters the statement only as the dimension of
  the integral $dz$, and that is the whole source of the threshold $d$ in
  `thm:origin-boundedness-d`.
- **What the entry does NOT carry.** Any converse: the implication is one-way, and
  $\int|\hat\mu|=\infty$ says nothing about the density when $\hat\mu$ changes sign. For a
  nonnegative transform the converse is `lem:positive-transform-origin`, this module's own
  Gaussian smoothing, which cites nothing; the law of every isotropic origin datum has the positive
  transform $e^{-F_d}$, so the necessity half of `thm:origin-boundedness-d` (clause (4)) spends no
  entry beyond A3(iii), the existence of the law (Q-0151; until then it assumed hypothesis (H) off
  the subordinated slice); its clause (5), the dichotomy, joins clause (2) and spends this entry
  through it (until Q-0286 the dichotomy was the last sentence of clause (4)). Nor any
  behaviour at the origin:
  the entry is silent about the size of $g$ near any particular point, and the origin enters this
  module's theorem through the decay exponent alone.
- **Why it is cited and not proved.** It is elementary — inversion plus dominated differentiation
  — and would be `[T]` in a repository with a Lean development. It is an entry here only because
  this module has none, and it is the first candidate to retire when one opens. Recorded in
  `records/affine/READING-sato1999levy-dimension-d.md` § 3, where the page is quoted.

## A2 — The polar criterion: an infinitely divisible law on $\mathbb{R}^d$ is self-decomposable exactly when its Lévy measure has a radially nonincreasing polar profile
**Blueprint:** `thm:cited-A2` (the interface node, ch. 2, since 2026-10-06); `prop:isotropic-polar-reading`, `prop:isotropic-polar-classification` (through `prop:isotropic-polar-reading`(1)), `thm:filtration-strict`, `thm:no-cin-ray-in-the-plane`, `prop:isotropic-radial-monotone` (clause (2), through `prop:isotropic-polar-reading`(1)), `prop:origin-upper-bound-d` (the existence of the density of its clause (2), through `prop:isotropic-radial-monotone`(2), since Q-0415); `prop:wedge-axis-profiles` (clause (2), the whole cell of the general linear group along a cone of the chain, applied directly to the law at $I$, already infinitely divisible, without `prop:isotropic-polar-reading`; round 3, the author's decision D10)
**Decision:** Q-0144 (2026-09-27) — Kept. Spent through the then clause (5) of `thm:origin-boundedness-d`; since Q-0286 (2026-10-04), which dropped that clause as a duplicate, spent by `prop:isotropic-polar-reading`(1) directly and through it by `thm:filtration-strict` and `thm:no-cin-ray-in-the-plane`.
**Cite:** @sato1999levy — Theorem 15.10, printed p. 95 (formula (15.8), both directions, with "Selfdecomposability imposes no restriction on $A$ and $\gamma$", corrected 2026-10-04 against the page image, `AXIOMS-verbatim.md`); Corollary 15.11, same page, for the case $d=1$
**Lean:** `AffineHemigroup.sato_polar_criterion` (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent by `AffineHemigroup.polar_reading`, `polar_reading_unique`, `polar_reading_admissible`, `classA_iff_originDatum` and `polar_classification`, `prop:isotropic-polar-reading` and `prop:isotropic-polar-classification`, by `filtration_witness`, `filtration_strict`, `thm:filtration-strict`, and by `no_cin_ray_in_the_plane`, `thm:no-cin-ray-in-the-plane`, wave 2 of Q-0281; and by `radial_monotone_law`, `prop:isotropic-radial-monotone`(2), through `polar_reading_converse`, wave 2, group B; and, through `radial_monotone_law`, by `origin_density_upper` and `origin_density_order`, `prop:origin-upper-bound-d`, Q-0415; and by `polar_mean_form`, and through it `wedge_axis_cell`, `wedge_axis_cone_laws` and their Gaussian ends `wedge_axis_cell_gaussian` and `wedge_axis_cone_laws_gaussian`, `prop:wedge-axis-profiles`(2), applied to a law already infinitely divisible, round 3, guarded); self-decomposability is stated at Sato's Definition 15.1 (`AffineHemigroup.IsSelfDecomposableSato`)

- **Statement as used.** An infinitely divisible $\mu$ on $\mathbb{R}^d$ with generating triplet
  $(A,\nu,\gamma)$ is self-decomposable if and only if
  $\nu(B)=\int_S\lambda(d\xi)\int_0^\infty\mathbf 1_B(r\xi)\,k_\xi(r)\,dr/r$ for a finite measure
  $\lambda$ on the unit sphere $S=S^{d-1}$ and a nonnegative $k_\xi(r)$, measurable in $\xi$ and
  nonincreasing in $r>0$. Both directions are used, both in `prop:isotropic-polar-reading`(1),
  which spends the entry directly for an isotropic law that may have a Gaussian part: the forward
  direction puts a self-decomposable law, made infinitely divisible by **A4**, into the form of
  `def:isotropic-origin-datum`, and the converse reads the datum's law as self-decomposable.
  `thm:filtration-strict` spends the entry only through that clause, in both directions and at
  two dimensions at once: the converse puts the witness family's law into $\mathcal{A}_d$, the
  forward direction keeps it out of $\mathcal{A}_{d+1}$. `thm:no-cin-ray-in-the-plane` spends it
  through the same clause, in the forward direction only. Until Q-0286 the case without a Gaussian
  part was stated a second time as clause (5) of `thm:origin-boundedness-d`, and the two later
  nodes read it there; that clause was dropped as a duplicate, and `thm:origin-boundedness-d` no
  longer spends this entry.
- **Primary — Sato, Theorem 15.10, p. 95.** Stated and proved in $\mathbb{R}^d$; the notes at
  p. 117 attribute it to Lévy in one dimension and to Wolfe for the general case. Corollary 15.11
  on the same page is the case $d=1$, and is the representation Theorems 28.4 and 53.8 read their
  constant off.
- **What the entry does NOT carry.** The identification of the article's polar profile $k_d$ with
  the source's $k_\xi$: that is the polar decomposition of a rotation-invariant measure, written
  out in `def:isotropic-origin-datum` and in the proof of `prop:isotropic-polar-reading`(1), and it is this module's own
  arithmetic, not the source's. Nor the rotation-averaging step of that proof, which is Fubini on
  the compact group. Nor uniqueness of $(\lambda,k_\xi)$: the statement is used only up to
  modification of the profile on a Lebesgue-null set, and the clause says so.
- **Where the reading is recorded.** `records/affine/READING-sato1999levy-dimension-d.md` § 2,
  which sets (15.8) against the released module B's (4.6) at the page and shows the two agree at
  $d=1$ with Sato's constant $c=k(0+)+k(0-)$.

## A3 — The Lévy–Khintchine representation on $\mathbb{R}^d$ exists and its generating triplet is unique
**Blueprint:** `thm:cited-A3` (the interface node, ch. 2, since 2026-10-06); `prop:line-levy-unique` ((ii) and (iii) at $d = 1$, since Q-0365; through it the Lean of `thm:isotropic-classification`'s necessity); `thm:isotropic-classification` (`[A]` since 2026-10-08, the author's regrading: its necessity spends (ii)–(iii) at $d = 1$ through `prop:line-levy-unique`); `cor:isotropic-classification-operators` (since Q-0407, the theorem read on operators: it spends what the theorem's necessity spends, through it, and nothing else); `thm:no-cin-ray-in-the-plane`, `thm:origin-boundedness-d` (the existence of the datum's law, (iii)), `prop:origin-lower-bound-d` (the existence of the datum's law and of a truncated datum's, (iii)), `prop:isotropic-polar-reading`, `prop:isotropic-polar-classification` (through `prop:isotropic-polar-reading`(1), and (ii) in clause (3)), `thm:filtration-strict`, `prop:isotropic-radial-monotone` (clause (2), through `prop:isotropic-polar-reading`(1)), `prop:origin-upper-bound-d` ((iii), through `prop:isotropic-radial-monotone`(2) for the density of its clause (2) and through `prop:origin-lower-bound-d` for its clause (3), since Q-0415), `lem:elliptical-stable`, `prop:stable-step-cone`, `prop:stable-exponent-cone`, `prop:anisotropy-budget`, `prop:one-parameter-families`, `prop:orbit-step-cone`, `prop:tempered-step-cone`, `prop:bounded-profile-rays`, `prop:similarity-stable-family`, `prop:similarity-orbit-family`, `prop:similarity-general-sandwich`, `prop:similarity-general-bounded-shape`, `prop:similarity-degenerate-family`, `prop:similarity-line-family`, `prop:similarity-general-index-zero`, `prop:similarity-cascade-families`, `prop:similarity-stable-order-families`, `prop:similarity-stable-order-kernels`, `prop:diagonal-stable-order-families`, `thm:wedge-axis`, `prop:wedge-axis-profiles` ((i)–(ii) through `prop:similarity-orbit-family`(1), (iii) for the law of a profile and its increments, and (i) directly for the triplet of the law at $I$ in clause (2); round 3)
**Cite:** @sato1999levy — Theorem 8.1, printed pp. 37–38 (clause (i) with (8.1)–(8.2) on p. 37, the uniqueness clause (ii) and the converse (iii) on p. 38); Definition 8.2, same page, for the names
**Lean:** `AffineHemigroup.levy_khintchine_exists` (clause (i)), `AffineHemigroup.levy_khintchine_unique` (clause (ii)), `AffineHemigroup.levy_khintchine_converse` (clause (iii)) (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent by `AffineHemigroup.polar_reading`, `polar_reading_unique`, `polar_reading_admissible`, `classA_iff_originDatum` and `polar_classification`, `prop:isotropic-polar-reading` and `prop:isotropic-polar-classification`, by `filtration_witness`, `filtration_strict`, `thm:filtration-strict`, and by `no_cin_ray_in_the_plane`, `thm:no-cin-ray-in-the-plane`, wave 2 of Q-0281; `polar_reading_unique` spends (ii) and (iii) only; `radial_monotone_law`, `prop:isotropic-radial-monotone`(2), spends (iii) only, through `polar_reading_converse`, wave 2, group B; `origin_lower_bound`, `origin_lower_bound_density` and `origin_lower_bound_ball`, `prop:origin-lower-bound-d`, spend (iii) only, for the law of the truncated datum, through `OriginDatum.law_eq_conv`, wave 2, group B; `origin_density_lower`, `origin_density_log_order` and `origin_ball_log_order`, `prop:origin-upper-bound-d`(3), spend (iii) only, through `origin_lower_bound`, and `origin_density_upper` and `origin_density_order` (iii) only, through `radial_monotone_law` and `origin_lower_bound`, while `origin_upper_bound` and `origin_upper_bound_of_heat` spend nothing (Q-0415, checked against the guard's output, 2026-10-11); wave 2, group G, § 5.6: `sim_stable_not_shape_blind`, `prop:similarity-stable-family`(3), spends (iii) only, through `exists_stable_increment`; `sim_orbit_id_increment`, `sim_orbit_bounded_shape` and `sim_orbit_index_zero`, `prop:similarity-orbit-family`(1)–(3), spend (i)–(ii) for the triplet of the increment and its uniqueness and (iii) for the law of the profile, and `sim_orbit_log`, (4), spends nothing; `sim_general_id_increment`, `sim_general_rank_one_limit`, `sim_general_rank_one_exp_limit` and `sim_general_sandwich`, `prop:similarity-general-sandwich`, spend (i)–(ii), and `sim_general_covariance` and `sim_general_finite_increment` (ii) only; `sim_bounded_shape_levy`, `sim_bounded_shape_exp` and `sim_bounded_shape_moments`, `prop:similarity-general-bounded-shape`(2)–(4), spend (i)–(ii) through it (checked against the guard's output, 2026-10-06); `sim_cascade_infinitelyDivisible`, `sim_cascade_general` and `sim_cascade_elliptical`, `prop:similarity-cascade-families`, spend (i)–(ii), and (iii) in clause (3), through `prop:similarity-orbit-family`; `stable_order_gl_row` and `stable_order_gl_row_examples`, `prop:similarity-stable-order-families`(2), through `prop:orbit-step-cone`, and `stable_order_cell_strict`, `prop:similarity-stable-order-kernels`(3), spend (iii) only; `stable_order_sim_kernels`, `stable_order_sandwich` and `loewner_order_sandwich`, `prop:similarity-stable-order-kernels`(1)–(2), spend (i)–(ii); `anisotropy_budget`, `prop:anisotropy-budget`(1), spends (i)–(ii), through `anisotropy_levy`; wave 2, group I: `line_family_cascade`, `prop:similarity-line-family`(1), spends (iii) only, for the increments, and `line_family_not_shape_blind`, (3), (ii)–(iii), (iii) making the law infinitely divisible; `line_family_levy`, `line_family_functionals` and `line_family_levy_not_shape_blind` spend nothing; `degenerate_cascade` and `degenerate_rotation_invariant_limit`, `prop:similarity-degenerate-family`(1) and (3), spend (iii) only, through `exists_stable_increment` and `exists_ellipticalStable`, and `degenerate_unbounded`, (2), nothing (checked against the guard's output, 2026-10-06); Q-0365: `line_levy_unique`, `prop:line-levy-unique`, spends (ii)–(iii) at $d = 1$, discharging the shared library's hypothesis `ScaleSpace.SymLevyUnique` of `ScaleSpace.main_analysis`, and through it `isotropic_classification` and `isotropic_classification_necessity` (`thm:isotropic-classification`), `polar_classification` and `radial_monotone_family` spend (ii)–(iii), where Paper V's interface `SpatialLine.fourier_toolbox_levy_unique` was spent before (checked against the guard's output, 2026-10-08); `wedge_axis_profiles`, `wedge_axis_cell`, `wedge_axis_cone_laws` and their Gaussian ends `wedge_axis_cell_gaussian` and `wedge_axis_cone_laws_gaussian`, `prop:wedge-axis-profiles`, print (i)–(iii), `polar_mean_form` (i) only, round 3, guarded)

- **Statement as used.** An infinitely divisible $\mu$ on $\mathbb{R}^d$ has
  $\widehat\mu(z)=\exp[-\tfrac12\langle z,Az\rangle+i\langle\gamma,z\rangle+\int(e^{i\langle
  z,x\rangle}-1-i\langle z,x\rangle\mathbf 1_D(x))\nu(dx)]$ for a symmetric nonnegative-definite
  $A$, a $\gamma\in\mathbb{R}^d$ and a measure $\nu$ with $\nu(\{0\})=0$ and
  $\int(|x|^2\wedge1)\nu(dx)<\infty$; the triplet $(A,\nu,\gamma)$ is **unique**; and conversely
  every such triplet occurs. `thm:no-cin-ray-in-the-plane` spends it through
  `prop:isotropic-polar-reading`(1), forward direction, and directly once: on $\mathbb{R}$ two Lévy
  measures with the same symmetric exponent are equal, which identifies the projected Lévy measure
  with the ray's. Until Q-0316 its proof also read the triplet of the given law itself, using the
  uniqueness twice more (the Lévy measure rotation invariant; the law equal to the datum's) and (i)
  once, on a law **A4** had made infinitely divisible; the blind register review of the isotropic
  paper (Appendix A flag 17) found that route repeated what the polar reading supplies, and the proof
  now reads the datum's exponent from `eq:isotropic-exponent`. `thm:filtration-strict` reads (iii)
  for the law that `lem:delay-polar-profile` builds in dimension $d+1$ and the
  uniqueness (ii) to identify that law's Lévy measure with the datum's, besides what it spends
  through `prop:isotropic-polar-reading`(1). `prop:isotropic-polar-reading` reads all three
  clauses: (i) to give a triplet to a self-decomposable law, once **A4** has made it infinitely
  divisible; (ii) to make its Lévy measure rotation invariant and its Gaussian form a multiple of
  $|z|^2$; (iii) for the existence of the law of a datum. The stable-cone section (Q-0241) reads
  two clauses.
  The converse (iii), transcribed from p. 38: *"(iii) Conversely, if $A$ is a symmetric
  nonnegative-definite $d \times d$ matrix, $\nu$ is a measure satisfying (8.2), and
  $\gamma \in \mathbb{R}^d$, then there exists an infinitely divisible distribution $\mu$ whose
  characteristic function is given by (8.1)."* It is spent in `lem:elliptical-stable`(2), for the
  elliptical stable law $S_\alpha(H)$ with triplet $(0, n_H(x)\,dx, 0)$, and in
  `prop:stable-step-cone` (b)$\Rightarrow$(a), for the increment with triplet
  $(0, (n_{\Sigma'} - n_\Sigma)(x)\,dx, 0)$; `prop:stable-exponent-cone` and
  `prop:similarity-stable-family`(3) spend it through those two nodes. `prop:orbit-step-cone`
  spends it in the same two ways for a general radial profile, and `prop:tempered-step-cone`
  (Q-0263) and `prop:bounded-profile-rays` (Q-0151) spend it only through that node, for the laws and increments of its profiles stable at
  the origin; its exponential-moment clause builds the law a second time by hand and spends
  nothing. `prop:anisotropy-budget`(1)
  reads (i) and the uniqueness (ii), *"The representation of $\hat\mu(z)$ in (i) by $A$, $\nu$, and
  $\gamma$ is unique"* (p. 38): to give a law a Lévy measure, to make it rotation invariant, to
  identify the Lévy measure of $L_*\mu$ with $L_*\nu$ (a change of the compensator, this module's
  arithmetic), and to read $\nu = (e^{-tB})_*\nu + \nu_t$ off a convolution.
  The five nodes of Q-0264 (conjecture A$'$ beyond elliptical parts) read it in the same ways.
  `prop:similarity-general-sandwich` reads (i) and the uniqueness (ii) to make the Lévy measure of a
  symmetric part symmetric, to carry it under a similarity, and to order it along an infinitely
  divisible increment. `prop:similarity-general-bounded-shape` and
  `prop:similarity-general-index-zero` spend it through that node, the latter also (iii) once, for
  the non-Gaussian factor of an increment, and (i)–(ii) directly in its clause (3), for the triplet of
  the increment (blind review W2H-4). `prop:similarity-degenerate-family` spends (iii) through
  `lem:elliptical-stable`(2) and `prop:stable-step-cone`(1), and (i)–(ii) through the two nodes
  above in its clauses (2)–(3); `prop:similarity-line-family` spends (iii) for its laws and
  increments, built from Lévy measures laid along lines, and (ii) once, to read the rotation
  invariance of a law off its Lévy measure. `prop:similarity-cascade-families` (Q-0265) reads (i) and
  the uniqueness (ii) once, to give the kernel from scale zero of a similarity cascade a triplet and to
  read its drift $0$ and the symmetry of its Lévy measure off the symmetry of the law.
  `prop:similarity-stable-order-kernels` (Q-0267; clauses (3)–(5) of `prop:similarity-stable-order-families` until the round-2 split, 2026-11-03) reads (i)–(ii) in the same way for a cascade along the stable order, and (iii) through `lem:elliptical-stable`(2) and `prop:similarity-stable-order-families`(2), for the laws and increments of its example; `prop:similarity-stable-order-families` spends (iii) through `prop:orbit-step-cone`, for the general linear row of its clause (2). `thm:wedge-axis` (Q-0266)
  spends it only through other nodes: (i)–(ii) through `prop:anisotropy-budget`(1), and (iii) through
  `lem:elliptical-stable`(2), `prop:stable-step-cone`(1) and `prop:similarity-stable-order-families`(2), for
  the stable orbits and the profiles of the general linear row. `prop:diagonal-stable-order-families`
  (Q-0282) spends (iii) through `lem:elliptical-stable`(2) and `prop:similarity-stable-order-families`(2),
  for the laws of its (3)(b) and (4)(b)–(c).
- **Primary — Sato, Theorem 8.1, pp. 37–38.** Stated and proved on $\mathbb{R}^d$; the section's
  opening paragraph on p. 37 names it the Lévy–Khintchine representation and attributes it to de
  Finetti, Kolmogorov, Lévy and Khintchine. Definition 8.2 on p. 38 supplies the vocabulary this
  module already uses — *generating triplet*, *Gaussian covariance matrix*, *Lévy measure*, and
  *purely non-Gaussian* for $A=0$.
- **What the entry does NOT carry.** Nothing about self-decomposability: that is A2, and the two
  are spent side by side. Nothing about images of infinitely divisible laws under linear maps —
  the book's Proposition 11.10 would give the projection directly, and the node deliberately does
  not use it, restricting the *exponent* to a line and applying uniqueness on $\mathbb{R}$ so that
  the boundary stays at one theorem; the projection itself is a Tonelli computation on the radial
  density, this module's own arithmetic. Nor uniqueness of A2's polar profile, which is read only
  up to a Lebesgue-null set.
- **Why it is cited and not proved.** It is the first theorem of the subject and would be an import
  in a repository with a Lean development; it is an entry here only because this module has none,
  and it is the second candidate to retire when one opens, after A1. Recorded in
  `records/affine/READING-sato1999levy-triplet-uniqueness.md`, where the pages are quoted.

## A4 — A self-decomposable law on $\mathbb{R}^d$ is infinitely divisible
**Blueprint:** `thm:cited-A4` (the interface node, ch. 2, since 2026-10-06); `prop:isotropic-polar-reading`, `prop:isotropic-polar-classification` (through `prop:isotropic-polar-reading`(1)), `thm:filtration-strict`, `thm:no-cin-ray-in-the-plane`
**Decision:** Q-0205 (2026-09-28) — Admitted with the reduction route of `notes/PLAN-d-dimensional-port.md`.
**Cite:** @sato1999levy — Proposition 15.5, printed p. 93 (its first sentence; the proof on the same page); Definition 15.1, printed p. 90, for the word
**Lean:** `AffineHemigroup.selfDecomposable_infinitelyDivisible` (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent by `AffineHemigroup.polar_reading`, `polar_reading_admissible`, `classA_iff_originDatum` and `polar_classification`, `prop:isotropic-polar-reading` and `prop:isotropic-polar-classification`, by `filtration_witness`, `filtration_strict`, `thm:filtration-strict`, and by `no_cin_ray_in_the_plane`, `thm:no-cin-ray-in-the-plane`, wave 2 of Q-0281); the first clause of the proposition only

- **Statement as used.** If a probability measure $\mu$ on $\mathbb{R}^d$ is self-decomposable, that
  is if for every $b > 1$ there is a probability measure $\rho_b$ on $\mathbb{R}^d$ with
  $\widehat\mu(z) = \widehat\mu(b^{-1}z)\,\widehat\rho_b(z)$ for every $z$ (Definition 15.1,
  (15.1)), then $\mu$ is infinitely divisible. It is used to supply the triplet **A3** and **A2**
  are stated for. In `prop:isotropic-polar-reading`(1), forward direction, membership in
  $\mathcal{A}_d$ supplies a self-decomposable law; the converse direction spends no entry of this
  ledger beyond **A2** and **A3**(iii), the datum's law being infinitely divisible by
  construction. `thm:filtration-strict` spends it through that clause's forward direction, in its
  exclusion step. `thm:no-cin-ray-in-the-plane` spends it through the same forward direction
  (until Q-0316 also directly, at the first step of its proof, which gave the law a triplet; the
  proof now reads the datum the polar reading supplies).
  Until Q-0286 the case without a Gaussian part was the then clause (5) of
  `thm:origin-boundedness-d`, listed here, and the two later nodes spent the entry through it
  without declaring it (the gap the drafting gate of the paper's section 3 found); that clause was
  dropped as a duplicate, both nodes now declare the entry, and `thm:origin-boundedness-d` no
  longer spends it.
- **Primary — Sato, Proposition 15.5, p. 93.** *"If $\mu$ is selfdecomposable, then $\mu$ is
  infinitely divisible and, for any $b > 1$, $\rho_b$ in (15.1) is uniquely determined and
  infinitely divisible."* Stated on $\mathbb{R}^d$ and proved there from Theorem 9.3 and the proof of
  Theorem 15.3, the null-array argument.
- **What the entry does NOT carry.** The rest of the proposition: the uniqueness and the infinite
  divisibility of the residual $\rho_b$, and the semi-self-decomposable clause. Nor anything the
  kernel-level classification needs: `thm:isotropic-classification` shows membership in
  $\mathcal{A}_d$ from Definition 15.1 alone, and its residuals are the cascade's increments. The
  entry is spent only where $\mathcal{A}_d$ is read as the polar form (2.1).
- **Why it is cited and not proved.** Its proof is the $d$-dimensional null array, the one step of
  Paper V's route that does not port verbatim (the plan's S4), and which the reduction route
  otherwise avoids. Mathlib has no infinite divisibility, so unlike A1 and A3 it would not retire
  by an import. Recorded in `records/affine/READING-sato1999levy-prop-15-5.md`, where the page is
  quoted.

## A5 — An operator-self-decomposable law, with a contracting exponent, and its residuals are infinitely divisible
**Blueprint:** `thm:cited-A5` (the interface node, ch. 2, since 2026-10-06); `prop:anisotropy-budget`, `thm:wedge-axis`
**Decision:** the author (2026-10-01) — Admitted as written, with Q-0241 (#15).
**Cite:** @jurek1993operator — Theorem 3.3.5, printed p. 83 (its last sentence), with the opening of § 3.4, printed pp. 89–90; the original is @urbanik1972levy Proposition 5.2, printed p. 134
**Lean:** `AffineHemigroup.operatorSelfDecomposable_infinitelyDivisible` (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent since wave 2 of Q-0281, group G, by `AffineHemigroup.anisotropy_levy` and, through it, `anisotropy_budget`, `prop:anisotropy-budget`(1), the symmetric form, the smoothing and the budget being Lean core; `anisotropy_budget_converse` does not spend it; and since wave 2, group H, through `anisotropy_budget`, by `wedge_axis_non_gaussian`, `wedge_axis_row` and `wedge_axis_row_members`, `thm:wedge-axis`(2)(c) and (3), checked against the guard's output on 2026-10-06)

- **Statement as used.** Let $B$ be a real $d \times d$ matrix with $e^{-tB} \to 0$ as
  $t \to \infty$, and let $\mu$ be a probability measure on $\mathbb{R}^d$ such that for every
  $t \ge 0$ there is a probability measure $\rho_t$ with $\mu = (e^{-tB})_*\mu * \rho_t$. Then
  every $\rho_t$ is infinitely divisible, and so is $\mu$. Used once, in the necessity clause (1)
  of `prop:anisotropy-budget`, to give $\mu$ and $\rho_t$ generating triplets (**A3**), from which
  the node derives $(e^{-tB})_*\nu \le \nu$ itself. `thm:wedge-axis` (Q-0266) spends it only through
  `prop:anisotropy-budget`(1), in the necessity half of its clause (2)(c), with $B = X/2$ for a positive
  definite $X$ in the cone, so that $e^{-tB} \to 0$; for cascade families along an order with the path
  condition, **A6** would supply the same infinite divisibility, a route that node does not take.
- **Primary — Jurek–Mason, Theorem 3.3.5, p. 83**, transcribed from the page image: *"A full
  measure $\mu$ on $\mathbb{R}^d$ is operator-decomposable if and only if its Urbanik
  decomposability semigroup $\mathbf{D}(\mu)$ contains a one-parameter semigroup
  $\{\exp(-tQ)\colon t \ge 0\}$ with $Q$ invertible and $\exp(-tQ) \to 0$ as $t \to \infty$.
  Furthermore, if $\mu = \exp(-tQ)\mu * \mu_t$ for $t \ge 0$, then each $\mu_t$ is infinitely
  divisible."* The opening of § 3.4, pp. 89–90, removes fullness for the last sentence and adds the
  law itself: *"The assumption of fullness in Theorem 3.3.5 was used only in the proof of the
  necessity, so we may drop that assumption in this section. For $Q$ with $\exp(-tQ) \to 0$ as
  $t \to \infty$, we say that a measure $\mu$ is $\exp(-tQ)$-decomposable if for each $t \ge 0$,
  there is a measure $\nu_t$ such that $\mu = \exp(-tQ)\mu * \nu_t$. (3.4.1) From the last part of
  Theorem 3.3.5, each $\nu_t$ is infinitely divisible. The assumption on $Q$ implies
  $\nu_t \Rightarrow \mu$ as $t \to \infty$, so $\mu$ is also infinitely divisible [cf.
  Proposition 1.8.1(b)]."* Their $Q$ is this module's $B$, with the same sign; their "measure" in
  this chapter is a probability measure, and $\mathbf{D}(\mu)$ is defined on p. 53 by
  $\mu = A\mu * \mu_A$ for some probability measure $\mu_A$.
- **Original — Urbanik 1972, Proposition 5.2, p. 134**, transcribed from the page image (the scan
  has no text layer): *"Suppose that a one-parameter semigroup $\exp tQ$ ($t \ge 0$) fulfils the
  condition $\lim_{t\to\infty}\exp tQ = 0$. Then each $\exp tQ$-decomposable for $t \ge 0$
  probability measure $\mu$ is a Lévy's measure. Moreover, for every $t \ge 0$
  $\mu = \exp tQ\mu * \lambda_t$, where $\lambda_t$ is an infinitely divisible measure."* Urbanik's
  $Q$ is $-B$, and "Lévy's measure" is his name for a limit law of an affinely normed
  infinitesimal array (p. 119), which § 6's first paragraph, p. 136, calls infinitely divisible:
  *"By Proposition 5.2 all such measures are Lévy's measures and, consequently, are infinitely
  divisible."* Sato–Yamazato (@sato1984operator, p. 76) call the class $Q$-selfdecomposable,
  (2.1), and state Urbanik's theorem in that form.
- **What the entry does NOT carry.** The inequality of Lévy measures: Jurek–Mason print it as
  Proposition 3.4.1(b), p. 90 (*"for each $t \ge 0$ and each Borel subset $B$ of
  $\mathbb{R}^d \setminus \{0\}$, $M(B) \ge M(\exp(tQ)B)$"*), and the node derives it from **A3**
  instead, so the entry stays at infinite divisibility. Nothing for an exponent with $e^{-tB}$ not
  tending to $0$, where the entry is silent and the node claims nothing. Nothing about fullness,
  the Gaussian part, the representation theorems of § 3.4, or the exponent sets of § 3.3.
- **Where the reading is recorded.** `records/affine/READING-jurek1993operator.md` and
  `records/affine/READING-urbanik1972levy.md`.

## A6 — Khintchine's theorem: the limit of the row sums of a null array on $\mathbb{R}^d$ is infinitely divisible
**Blueprint:** `thm:cited-A6` (the interface node, ch. 2, since 2026-10-06); `thm:cascade-infinitely-divisible`, `prop:similarity-cascade-families`, `prop:similarity-stable-order-kernels`, `prop:wedge-axis-profiles` (through `thm:cascade-infinitely-divisible`(2); round 3)
**Decision:** the author (2026-10-03) — Admitted, `notes/PLAN-article-structure.md` decision 2 ("What the null array changes"); read at the page by Q-0265.
**Cite:** @sato1999levy — Theorem 9.3, printed p. 47, with Definition 9.2 and (9.1) on the same page; Definition 2.2, printed p. 7, for "converges", and the sentence after Definition 2.4, printed p. 8, for the law of a sum of independent variables
**Lean:** `AffineHemigroup.khintchine_null_array` (`Formalization/AffineHemigroup/Interfaces.lean`, typed by Q-0281; spent since wave 2 of Q-0281, group C, by `AffineHemigroup.cascade_interval_infinitelyDivisible` and, through it, `chain_infinitelyDivisible`, `gw_family_infinitelyDivisible` and `isotropic_family_infinitelyDivisible`, all guarded; and in wave 2, group G, by `sim_cascade_infinitelyDivisible`, `sim_cascade_general` and `sim_cascade_elliptical`, `prop:similarity-cascade-families`, and by `stable_order_sim_kernels`, `stable_order_sandwich` and `loewner_order_sandwich`, `prop:similarity-stable-order-kernels`(1)–(2), all through `thm:cascade-infinitely-divisible`(2), all guarded; and by `mexp_infinitelyDivisible` and `law_form_of_mem_coneLaws`, `prop:wedge-axis-profiles`, through the same clause, round 3, guarded); the measure form, with the rows nonempty (r_n >= 1), which the page's indexing presupposes

- **Statement as used.** Let $r_n \ge 1$ be integers and $\mu_{n,k}$, $1 \le k \le r_n$,
  $n = 1, 2, \dots$, probability measures on $\mathbb{R}^d$ with $\lim_{n\to\infty}\max_{1\le k\le r_n}\mu_{n,k}(\{|x| >
  \varepsilon\}) = 0$ for every $\varepsilon > 0$. If $\mu_{n,1} * \dots * \mu_{n,r_n} * \delta_{-b_n}$
  converges weakly to a probability measure $\mu$ for some $b_n \in \mathbb{R}^d$, then $\mu$ is
  infinitely divisible. Used once, in `thm:cascade-infinitely-divisible`(1), with $r_n = n + 1$, rows
  that multiply out to the same law for every $n$, and $b_n = 0$, so the convergence is trivial;
  every other clause of that node, `prop:similarity-cascade-families` and
  `prop:similarity-stable-order-kernels` (Q-0267, for the stable order on PSD($d$), whose path condition
  `prop:similarity-stable-order-families`(1) checks) spend it through (1).
- **Primary — Sato, Theorem 9.3, p. 47**, transcribed from the page image: *"THEOREM 9.3
  (Khintchine [254]). Let $\{Z_{nk}\}$ be a null array on $\mathbb{R}^d$ with row sums $S_n$. If,
  for some $b_n \in \mathbb{R}^d$, $n = 1, 2, \dots$, the distribution of $S_n - b_n$ converges to a
  distribution $\mu$, then $\mu$ is infinitely divisible."* With Definition 9.2, same page: *"A double
  sequence of random variables $\{Z_{nk}\colon k = 1, 2, \dots, r_n;\ n = 1, 2, \dots\}$ on
  $\mathbb{R}^d$ is called a* null array *if, for each fixed $n$, $Z_{n1}, Z_{n2}, \dots, Z_{nr_n}$
  are independent and if, for any $\varepsilon > 0$, (9.1)
  $\lim_{n\to\infty}\max_{1\le k\le r_n}P[\,|Z_{nk}| > \varepsilon\,] = 0$. The sums
  $S_n = \sum_{k=1}^{r_n}Z_{nk}$, $n = 1, 2, \dots$, are called the* row sums.*"* "Converges" is
  Definition 2.2, p. 7 (for every bounded continuous $f$, $\int f\,d\mu_n \to \int f\,d\mu$), and p. 8
  gives *"If $X_1$ and $X_2$ are independent random variables on $\mathbb{R}^d$ with distributions
  $\mu_1$ and $\mu_2$, respectively, then $X_1 + X_2$ has distribution $\mu_1 * \mu_2$."* The measure
  form above is the theorem read through a realization of the rows by coordinate maps on product
  spaces (standard measure theory); nothing beyond that translation is added. Stated and proved on
  $\mathbb{R}^d$ (proof pp. 48–51).
- **What the entry does NOT carry.** The infinitesimality of the array: `thm:cascade-infinitely-divisible`
  proves it from the continuity of the transforms, through Lévy's continuity theorem on
  $\mathbb{R}^d$ and the portmanteau inequality, both theorems of Mathlib (wave 2 of Q-0281; the
  earlier route of the proof, the one-dimensional truncation inequality, is also in Mathlib; Sato's
  E 12.12, p. 67, is that criterion as an exercise, read and not cited). Theorem 9.7 and Lemma 9.6 (p. 51, additive processes in law), which would give the node's
  clause (1) through a process, are read and not cited. Nothing about the triplet of the limit (that is
  **A3**), and no convergence of triplets.
- **Why it is cited and not proved.** It is the subject's central limit theorem for triangular arrays,
  and Mathlib has no infinite divisibility, so like A4 it would not retire by an import. Its admission
  is what lets the cascade axioms give infinitely divisible increments, which the module had avoided
  (the draft's Lemma 2.6). Recorded in `records/affine/READING-sato1999levy-null-array.md`, where the
  pages are quoted.

## A8 — Wolfe's theorem: a symmetric self-decomposable law on $\mathbb{R}^d$ is symmetric unimodal in Kanter's sense
**Blueprint:** `thm:cited-A8` (the interface node, ch. 2, since 2026-10-06); `prop:isotropic-radial-monotone`; `prop:origin-upper-bound-d` (the existence of the density of its clause (2), through `prop:isotropic-radial-monotone`(2), since Q-0415)
**Decision:** Q-0316 (2026-10-04) — Admitted as the brief of Q-0316 directs (item 1), on the author's call recorded in `records/affine/GATE-paper-iso.md` item 18 between positioning prose and a node; the author keeps the veto. The number A7 is left free (the brief's numbering). **Admitted as a Lean interface: the author's decision of 2026-10-05, after the librarian's independent audit** of the transcription (`AXIOMS-verbatim.md` § A8, verdict MATCH, read in Kanter's sense), with the audit's two amendments: $K$ nonempty, and the $\sigma$-algebra of the mixing space named, $W_d$ not asserted measurable.
**Cite:** @wolfe1978unimodality — Theorem 2, printed p. 144, with the definition of $U_n$ on the same page, and the definitions of "symmetric" and of class L, printed pp. 141–142; @kanter1977unimodality — Definition 1.2, printed p. 66, and Definition 3.1, printed p. 70, for the meaning of "symmetric unimodal"; @sato1999levy — Definition 15.1, printed p. 90, and Theorem 15.3(ii), printed p. 91, for "class L"; for the laws with a Gaussian part, which Wolfe's printed proof does not cover (below), @kanter1977unimodality — Lemma 3.1, printed p. 70, with Lemma 2.1, printed p. 68, and Definition 2.2, printed p. 69, and Theorem 3.2, printed p. 74
**Lean:** `AffineHemigroup.wolfe_symmetric_unimodal` (`Formalization/AffineHemigroup/Interfaces.lean`, admitted 2026-10-05, wave 2 of Q-0281, group B; spent by `AffineHemigroup.radial_monotone_law` and `radial_monotone_family`, `prop:isotropic-radial-monotone`(2) and (1), through `radial_monotone_of_selfDecomposable`, both guarded, the second also printing A3(ii)–(iii) through `thm:isotropic-classification` (Paper V's interface until Q-0365); and, through `radial_monotone_law`, by `origin_density_upper` and `origin_density_order`, `prop:origin-upper-bound-d`, Q-0415; its vocabulary `kanterUniform` and `IsKanterUniform` is in `Formalization/AffineHemigroup/Defs/Kanter.lean`, with `kanterUniform_zero`, $u_{\{0\}} = \delta_0$, and `isProbabilityMeasure_kanterUniform`, every $u_K$ a probability measure); the mixture as `Λ.join = μ`, $\Lambda$ concentrated on $W_d$ as "$\Lambda$-almost every measure is a $u_K$"

- **Statement as used.** Let $\mu$ be a probability measure on $\mathbb{R}^d$ that is symmetric,
  $\mu(B) = \mu(-B)$ for every Borel $B$, and self-decomposable in the sense of
  `eq:self-decomposable`. Then $\mu$ is *symmetric unimodal*: there is a probability measure
  $\Lambda$ on the set $W_d$ of the uniform laws $u_K$ of the nonempty compact convex symmetric sets
  $K \subset \mathbb{R}^d$ with
  $\mu(A) = \int_{W_d} u_K(A)\,\Lambda(du_K)$ for every Borel $A$. Precisely, $\Lambda$ is a
  probability measure on the measurable space of the probability measures on $\mathbb{R}^d$, with the
  $\sigma$-algebra generated by the evaluations $\nu \mapsto \nu(A)$ (the Giry $\sigma$-algebra, which
  on the probability measures of a Polish space is the Borel $\sigma$-algebra of weak convergence,
  Kanter's convention on p. 70), and it is concentrated on $W_d$: $\Lambda$-almost every measure is a
  $u_K$. That $W_d$ is a measurable set is not used by the statement or by any formal proof
  (Kanter's Corollary 3.1, p. 72, states it; the audit found its printed proof to cover only the
  $K$ with nonempty interior in their span). The reading from Kanter's $\nu$, a measure on $W_d$
  with its relative $\sigma$-algebra, to "$\Lambda$-almost every measure is a $u_K$" does use it,
  and it holds: **$W_d$ is a countable union of weakly compact sets, hence a Borel set** (since
  2026-10-12, Q-0424). For $k, n \ge 1$ the sets $K$ of dimension $k$ with
  $\tfrac1n\bar B \cap \operatorname{span}K \subseteq K \subseteq n\bar B$ form a compact family
  in the Hausdorff metric, by Blaschke's selection theorem, $K \mapsto u_K$ is weakly continuous
  on it, every $K$ of dimension $k \ge 1$ is in one of these families, and $k = 0$ gives
  $\delta_0$ alone. The argument is written out in the proof of record of
  `prop:isotropic-radial-monotone`, its paragraph "The set $W_d$ is a Borel set", from
  `records/affine/reviews/VERIFY-round1-mathematics.md`, item 6(a); it is prose and is not
  formalized, and Blaschke's selection theorem is used as a classical theorem, cited in that
  proof since Q-0430 (Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Thm. 1.8.7,
  p. 63; Lemma 1.8.14, p. 66, and p. 45 for the comparison by support functions; read at the page
  images, `records/affine/READING-schneider2014convex.md`). Until
  then the entry, the proof and the docstring of the axiom asserted a weaker fact with no
  argument: $W_d$ analytic, being the image of the Polish space of the nonempty compact convex
  symmetric sets under the Borel map $K \mapsto u_K$, hence universally measurable (blind review
  W2B-1). That route is correct too and needs two cited theorems; the docstring of the axiom in
  `Interfaces.lean` still words the reading that way, and is to follow at the next Lean item.
  The Lean puts $\Lambda$ on all measures on $\mathbb{R}^d$ rather than on the probability measures;
  the two are equivalent, because the probability measures form a measurable set and
  $\Lambda$-almost every measure, being a $u_K$, lies in it. $K$ is nonempty because
  Kanter's quotient presupposes it; a nonempty symmetric convex $K$ contains $0$. Here $u_K(A) =
  \mathrm{Vol}_V(A \cap K)/\mathrm{Vol}_V(K)$, $V$ being the linear span of $K$ and $\mathrm{Vol}_V$
  the Lebesgue measure of $V$, of dimension $\dim K \in \{0,\dots,d\}$; at $\dim K = 0$,
  $u_{\{0\}} = \delta_0$. The source writes $\lambda_K$ for $u_K$ and $\nu$ (Kanter) or $\eta$ (Wolfe)
  for $\Lambda$; the module renames them because $\lambda$ is its contraction ratio and $\nu$ its
  Lévy measure. Spent once, by `prop:isotropic-radial-monotone`, for the kernels from scale zero and
  for the laws of the isotropic origin data; both are symmetric, rotation invariance at $Q = -I$.
- **Primary — Wolfe, Theorem 2, p. 144**, transcribed from the page image: *"THEOREM 2. A symmetric
  n-dimensional distribution function of class L is symmetric unimodal."* The definition it reads,
  same page: *"Let $W_n$ stand for the set of all probability measures on $R_n$ and let
  $\lambda_k(A) = \mu(K \cap A)$ for all Borel measurable sets in $R_n$ where u denotes Lebesgue
  measure and $K$ is a compact, convex, symmetric subset of $R_n$. Let $U_n$ stand for all measures u
  on $R_n$ that are of the form $\mu = \int_{W_n}\lambda_K\,d\eta(\lambda_K)$ where $\eta$ is a
  measure on $W_n$. Kanter [3] defines an n-dimensional distribution function to be symmetric
  unimodal if it generates a measure that is contained in $U_n$."* Wolfe's restatement drops the
  normalization and takes $n$-dimensional Lebesgue measure; the definition of record is Kanter's.
- **The definition — Kanter, Definitions 1.2 and 3.1, pp. 66 and 70**, transcribed from the page
  images: *"If $K$ is a compact, convex subset of $R^N$ we define the probability measure
  $\lambda_K$ on $R^N$ by (1.2) $\lambda_K(A) = \mathrm{Vol}_L(A \cap K)/\mathrm{Vol}_L(K)$ where $A$
  is any Borel subset of $R^N$ and $L$ is the affine subspace spanned by $K$"* (p. 66, with
  $\mathrm{Vol}_L$ the $k$-dimensional Lebesgue measure of Definition 1.1), and *"Let $L$ be a linear
  subspace of $R^N$. We shall let $W_L$ stand for the set of all probability measures on $L$ of the
  form $\lambda_K$ where $K$ is a compact symmetric subset of $L$. [...] We let $U_L$ stand for all
  the measures $\mu$ on $R^N$ which are of the form (3.1) $\mu = \int_{W_L}\lambda_K\,d\nu(\lambda_K)$
  where $\nu$ is a measure on $W_L$. [...] We shall call a random vector in $R^N$, symmetric unimodal
  if its distribution is in $U_N$"* (p. 70). Kanter's Theorem 3.1, p. 73, makes the class closed
  under weak convergence, so the mixtures and their weak closure are one class.
- **The words — Sato, Definition 15.1, p. 90, and Theorem 15.3(ii), p. 91.** Wolfe's "class L"
  (pp. 141–142) is the class of limits of normalized sums $(X_1 + \dots + X_k)/B_k - A_k$ of independent
  vectors forming an infinitesimal system. Sato defines a law on $\mathbb{R}^d$ to be
  *"selfdecomposable, or of class L"* by (15.1) (p. 90), which is `eq:self-decomposable` with
  $\lambda = b^{-1}$, and Theorem 15.3(ii) (p. 91) reads, from the page image: *"For any
  selfdecomposable distribution $\mu$ on $\mathbb{R}^d$ we can find $\{Z_n\}$ independent, $b_n > 0$,
  and $c_n \in \mathbb{R}^d$ satisfying (15.2) and (15.3)"*, that is
  $P_{b_nS_n + c_n} \to \mu$ with $\{b_nZ_k\}$ a null array: Wolfe's definition with $B_n = 1/b_n$
  and $A_n = -c_n$. Only this direction is read.
- **What the entry does NOT carry.** A density: Kanter's class contains laws with no density (the
  uniform law on a segment of $\mathbb{R}^2$, the point mass), and the entry says nothing about
  absolute continuity. The radially nonincreasing density is `prop:isotropic-radial-monotone`'s own
  step, which treats the sets of dimension $k < d$ and the point mass and spends nothing for them.
  Nor the proof of Wolfe's theorem, which rests on his polar criterion (Theorem 1, p. 143; the
  multivariate form of **A2**) and on Kanter's Theorem 4.1 (p. 78, *"Let $X$ be a symmetric
  infinitely divisible random vector in $R^N$. Suppose the Levy-Khinchine measure $M_X$ is in $U_N$;
  then $X$ is a symmetric unimodal random vector in $R^N$"*), read at the page and not cited
  separately. That printed proof does not carry a law with a Gaussian part $a > 0$: Theorem 4.1 is
  stated under *"$q_X \equiv 0$ ... (no Gaussian part)"* (p. 77), and its proof (p. 79) is the
  compound Poisson series with Theorem 3.2 (p. 74) and Theorem 3.1 (p. 73), which does not restore
  $q_X$. The statements do cover it: Wolfe's Theorem 2 for all of class L, and Watanabe's
  Proposition (1983, p. 488) for the isotropic case with $a \ge 0$; the next bullet says how the
  entry is carried for $a > 0$. Nor anything about laws that are not symmetric, and no pointwise
  bound on any density.
- **The Gaussian part: carried by printed proofs, through Kanter's Lemma 3.1 and Theorem 3.2**
  (rewritten 2026-10-12, Q-0424, on the author's decision D5, route (A), of the response to the
  external review of the isotropic paper; `records/affine/reviews/VERIFY-round1-mathematics.md`,
  item 6(b); Kanter's pp. 68, 69, 70, 71, 72, 74, 77, 78 and 84 read again at the page image for
  this item). Wolfe states Theorem 2 for every symmetric distribution function of class L, and a
  self-decomposable law may have a Gaussian part. His printed proof (p. 144) ends with Kanter's
  Theorem 4.1, and Kanter states that theorem for laws with no Gaussian part: p. 77, from the page
  image, *"We shall assume $q_X \equiv 0$, unless otherwise stated (no Gaussian part)"*, $q_X$
  being the quadratic form of his Lévy–Khinchine formula (4.1), and nothing in the statement of
  Theorem 4.1 (p. 78) or in its proof (p. 79) restores $q_X$. So Wolfe's printed proof covers the
  symmetric self-decomposable laws with no Gaussian part. Two results of Kanter's paper cover the
  others, each transcribed from the page image:
  - **Lemma 3.1, p. 70:** *"Let $L$ be a linear subspace of $R^N$ and let $\mu$ be a log-concave,
    symmetric, probability measure on $L$ with $d\mu/d\,\mathrm{Vol}_L = f$ where $f \in T_L$.
    Then $\mu \in U_L$."* $T_L$ is *"the set of all log-concave, symmetric nonnegative functions
    $f$ on $L$ with $\int_L f\,d\,\mathrm{Vol}_L = 1$"* (Definition 2.2, p. 69), a function being
    log-concave *"if $\log f$ has values in $[-\infty, +\infty)$ and is concave"* (p. 68), and a
    measure with such a density is a log-concave measure by the second half of Lemma 2.1, p. 68:
    *"Conversely if $L$ and a log-concave density function $f$ are given, then the measure $\mu$
    defined by $d\mu = f\,d\,\mathrm{Vol}_L$ is logarithmically concave."* The same in words,
    p. 84: *"any symmetric random vector $X$ which is unimodal according to Anderson or Sherman is
    unimodal in our sense as well"*.
  - **Theorem 3.2, p. 74:** *"Let $\mu_1, \mu_2 \in U_N$. Then $\mu_1 * \mu_2 \in U_N$."*

  **The argument, complete from A2, A3, A4 and these two results.** Let $\mu$ be symmetric and
  self-decomposable on $\mathbb{R}^d$. By **A4** it is infinitely divisible, and by **A3**(i) it
  has a generating triplet $(A, \nu, \gamma)$. Its transform is real, so it equals its complex
  conjugate, which is the form (8.1) with the triplet $(A, \check\nu, -\gamma)$, $\check\nu$ being
  the image of $\nu$ under $x \mapsto -x$. By **A3**(ii), $\check\nu = \nu$ and $\gamma = 0$. By
  **A3**(iii) there is an infinitely divisible law $\mu_0$ with triplet $(0, \nu, 0)$. Its
  transform is $\exp[-\int(1 - \cos\langle z,x\rangle)\,\nu(dx)]$, the odd part of the integrand
  integrating to $0$ against the symmetric $\nu$. It is real, so $\mu_0$ is symmetric. By **A2**
  for $\mu$, $\nu$ has the polar form (15.8), and by **A2** for $\mu_0$, which has the same
  $\nu$, $\mu_0$ is self-decomposable; the criterion puts no condition on $A$. The transforms
  multiply: $\mu = N(0, A) * \mu_0$, with $N(0,A)$ the centred Gaussian law of covariance $A$. Now
  $\mu_0 \in U_d$ by Wolfe's theorem in the case that his printed proof covers. If $A = 0$ then
  $\mu = \mu_0$. Otherwise let $L$ be the range of $A$. On $L$ the law $N(0,A)$ has a density
  proportional to $\exp(-\tfrac12\langle x, (A|_L)^{-1}x\rangle)$, which is symmetric and
  log-concave, so $N(0,A) \in U_L$ by Lemma 3.1, and $U_L \subseteq U_d$: a compact convex
  symmetric subset of $L$ is one of $\mathbb{R}^d$, with the same uniform law, and the inclusion of
  $W_L$ in $W_d$ is continuous for weak convergence, so a mixing measure on $W_L$ is carried to
  one on $W_d$. By Theorem 3.2, $\mu \in U_d$. Where the module spends the entry for a law with a
  Gaussian part, $A = aI$ with $a > 0$ and $L = \mathbb{R}^d$, and the step $U_L \subseteq U_d$
  is not needed.

  So the entry is carried by printed proofs for every symmetric self-decomposable law, and the
  caveat of 2026-10-11 is withdrawn. That version of this bullet read "carried by Wolfe's
  statement, not by a printed proof", and said that whether Kanter shows that a centred Gaussian
  law is symmetric unimodal in his sense "was not found", the word "Gaussian" occurring once in
  the text layer of his paper. The search was for the word. The result is Lemma 3.1, which is
  stated for log-concave densities. Nothing else changes: the argument above is prose and backs
  the entry, it is not spent by any Lean proof, Kanter's two results are not ledger entries, and
  the Lean interface is the axiom as audited, Wolfe's statement. The module spends the entry for
  a law with a Gaussian part in one node,
  `prop:isotropic-radial-monotone`, whose kernels and data may have a Gaussian coefficient
  $a > 0$. `prop:origin-upper-bound-d` and `prop:origin-rate-d`, which reach the entry through
  that node, are stated for a datum with Gaussian coefficient $0$, and no other node reads the
  entry. For the rotation-invariant case the conclusion that node draws, a radially nonincreasing
  density, is also in print as a statement that allows a Gaussian part: Watanabe 1983, the
  Proposition of p. 488 (`records/affine/READING-watanabe1983isoperimetric.md` § 3). Its proof of that
  direction is one sentence, a reference to "Theorem 4" of Kanter's paper (evidently his Theorem
  4.1) and to two theorems of lecture notes of Sato in Japanese, which are not held; so it is a
  second statement and not a second proof read here. The alternative that narrows the entry to
  laws with no Gaussian part and proves the Gaussian case of `prop:isotropic-radial-monotone`
  directly (route (B) of the verification record, a lemma on the convolution of two radially
  nonincreasing functions) was not taken: it changes the statement of the cited fact and the
  Lean. Recorded in `records/affine/READING-kanter1977unimodality.md`, addenda of 2026-10-11 and
  2026-10-12, and `blueprint/AXIOMS-verbatim.md` § A8, addendum; the isotropic paper says it in
  its § 1.1 and after C5.
- **Why it is cited and not proved.** Its proof ends with Kanter's Theorem 4.1. The proof of that
  theorem printed on p. 79 writes the law of a finite Lévy–Khinchine measure as a compound Poisson
  series and concludes by the closure of his class under convolution (Theorem 3.2, p. 74) and
  under mixtures; for an infinite measure it truncates and concludes by the closure under weak
  convergence (Theorem 3.1, p. 73), a page of measure theory on spaces of measures. Nothing
  else in the module needs that machinery; the node it serves is positioning for the open problem
  of the paper's § 4. Recorded in `records/affine/READING-wolfe1978unimodality.md` § 3 and
  `records/affine/READING-kanter1977unimodality.md` §§ 1–3 and its addendum, where the pages are
  quoted. (Corrected on 2026-10-11, Q-0417: until p. 79 was read this bullet described the proof
  as "a semigroup argument on the convolution powers of an infinitely divisible law (from p. 78
  on)"; that describes Kanter's Lemma 4.1 and Corollary 4.1, which the printed proof of Theorem
  4.1 does not cite.)

## A9 — The logarithmic spectrum of a product of two positive definite matrices is weakly majorized by the sum of their logarithmic spectra
**Blueprint:** `thm:cited-A9` (the interface node, ch. 2, since 2026-10-06); `lem:spectral-cones-products`, `lem:spectral-cones` (clause (5), through clause (2)), `thm:cone-orders` (clause (1), the superadditivity of $F_w$), `lem:cone-orders-closed`, `lem:cone-orders-psd` (clause (2))
**Decision:** the author's decision of 2026-10-05 — § 5.3's matrix analysis admitted as an interface (ADR-0020): this entry only; Ky Fan's minimum principle is proved in-house, and there is no Cauchy–Binet and no majorization entry. The weak form (the partial sums only) is the session's narrowest-reading decision, taken under the delegation of safe-direction choices (`CLAUDE.md`) while only the parallel in PDM was held. **Re-read at MA on 2026-10-06 (librarian); the weak form stands; the axiom unchanged.** The page states full majorization, of which the admitted weak form is a strict consequence (see "Statement as used").
**Cite:** @bhatia1997matrix — Corollary III.4.6 (Lidskii), relation (III.21), printed p. 73; $\prec$ as in (III.15), p. 71, and (II.2)–(II.3), p. 28. Parallel: @bhatia2007positive — Exercise 6.5.3, relation (6.47), printed p. 228, which is (III.21) with the pointer "See MA p. 73"; the definitions of "positive" and $\lambda^\downarrow$ read on pp. 4 and 57–58 of MA (pp. 1 and 5 of PDM)
**Lean:** `AffineHemigroup.gelfand_naimark_logMajorized` (`Formalization/AffineHemigroup/Interfaces.lean`, admitted 2026-10-05, wave 2 of Q-0281, group F; spent by `AffineHemigroup.logSpec_product_majorized`, `lem:spectral-cones-products`, and through it by the nodes listed above); the partial-sum inequalities for $1 \le k \le d$, with $\lambda(MN)$ read as `eigUp (M * N)`

- **Statement as used.** Weak form. For $M, N \in \mathrm{PD}(d)$ and $1 \le k \le d$,
  $$\sum_{i \le k}\log\lambda^\downarrow_i(MN) \le \sum_{i \le k}\bigl(\log\lambda^\downarrow_i(M) +
  \log\lambda^\downarrow_i(N)\bigr) ,$$
  where $\lambda(MN)$ are the eigenvalues of $MN$ with multiplicity, real and positive because they
  are those of $M^{1/2}NM^{1/2}$, and $\lambda^\downarrow$ is the decreasing arrangement.
  **What the page states.** MA Corollary III.4.6 states, for positive matrices $A, B$, the
  *full* majorization $\log\lambda(AB) \prec \log\lambda^\downarrow(A) + \log\lambda^\downarrow(B)$:
  by (III.15) and (II.2)–(II.3) the partial sums of the $k$ largest entries are bounded for
  $k = 1, \dots, n$, **and the totals are equal**. The entry uses only the partial-sum half, a strict
  consequence of the page; the equality of the totals,
  $\sum_i\log\lambda_i(MN) = \sum_i(\log\lambda_i(M) + \log\lambda_i(N))$, is
  $\det(MN) = \det M\det N$ and is **proved in-house** as before (`logSpec_product_majorized`), so the
  module's majorization $\ell(M^{1/2}NM^{1/2}) \prec \ell(M) + \ell(N)$ of `lem:spectral-cones`(2)
  follows from the entry and a determinant.
  - **The reading of $\prec$.** MA defines it on p. 28: $x \prec y$ when
    $\sum_{j \le k} x^\downarrow_j \le \sum_{j \le k} y^\downarrow_j$ for $1 \le k \le n$ (II.2)
    and the totals are equal (II.3); on logarithms, $\log x \prec \log y$ is the same with products
    (III.14)–(III.15), p. 71. The right-hand vector $\log\lambda^\downarrow(A) + \log\lambda^\downarrow(B)$
    is already in decreasing order, so it is its own $y^\downarrow$, and $\log\lambda(AB)$ enters
    through its decreasing rearrangement $x^\downarrow$. The entry takes the partial sums (II.2) only.
  - **Orderings.** The page compares decreasing rearrangements through the partial sums of the
    largest entries. The module's $\prec$ (`lem:spectral-cones`) uses the partial sums $s_k$ of the
    smallest entries, reversed, with equal totals; the two agree once the totals are equal, which is
    how `logSpec_product_majorized` passes from one to the other.
  - **"Positive."** MA's "positive" is positive semidefinite (p. 4), $A, B$ complex Hermitian of any
    size, and zero coordinates are allowed there, so a logarithm may be $-\infty$. For positive
    definite $M, N$ every term is finite; the entry reads positive definite, which is what
    $\log\lambda(AB)$ needs.
  - **Real case.** The page is for complex positive matrices. A real positive definite matrix is a
    complex one with the same characteristic polynomial, so the real statement is a specialization.
- **Primary — Bhatia, *Matrix Analysis* (GTM 169, Springer, 1997), Corollary III.4.6 (Lidskii), (III.21), p. 73**, transcribed from the page image by the librarian (`AXIOMS-verbatim.md` § A9): *"Let $A, B$ be two positive matrices. Then all eigenvalues of $AB$ are nonnegative and $\log\lambda^{\downarrow}(A) + \log\lambda^{\uparrow}(B) \prec \log\lambda(AB) \prec \log\lambda^{\downarrow}(A) + \log\lambda^{\downarrow}(B)$. (III.21)"* The entry uses the second half. MA derives it from the Gel'fand–Naimark singular-value theorem III.4.5, (III.17), p. 71, through (III.20), p. 72, applied to $A^{1/2}, B^{1/2}$. The parallel in PDM, Exercise 6.5.3, (6.47), p. 228, is (III.21) verbatim, with the pointer "See MA p. 73". Recorded in `records/affine/READING-bhatia1997matrix-lidskii.md` and, for PDM, `records/affine/READING-bhatia2007positive-gelfand-naimark.md`.
- **What the entry does NOT carry.** The lower bound, the first half of (III.21). The equality of the totals, which is $\det(MN) = \det M\det N$ and is proved (the page does state it). Singular values of products that are not normal (III.17). Horn's inequalities, or any description of the set of spectra of $M^{1/2}QNQ^{\top}M^{1/2}$ over $Q \in \mathrm{O}(d)$. Semidefinite $M, N$, for which a logarithm may be $-\infty$. Ky Fan's minimum principle, the additive companion used in `lem:spectral-cones`(1), which is proved in-house.
- **Why it is cited and not proved.** Its proof goes through compound matrices and the
  Cauchy–Binet formula: the $k$-th compound of $M^{1/2}NM^{1/2}$ is the product of the compounds, and
  its largest eigenvalue is the product of the $k$ largest eigenvalues. That is about 1,000 Lean
  lines that Mathlib does not hold for matrices (its exterior powers have functoriality and a basis,
  but no inner product, and the Cauchy–Binet formula is a TODO), and nothing else in the module needs
  them (records/formalization/SKELETON.md, wave 2, group D, the price of `lem:spectral-cones-products`).

## A10 — Schoenberg's radial theorem with the representation of a Bernstein function: if $\xi \mapsto f(|\xi|^2)$ is continuous and negative definite on $\mathbb{R}^d$ for every $d$, then $f(\sigma) = a + b\sigma + \int_{(0,\infty)}(1 - e^{-\sigma t})\,m(dt)$
**Blueprint:** `thm:cited-A10` (the interface node, ch. 2, since 2026-10-07); `lem:filtration-top` (its inclusion $\mathcal{A}_\infty \subseteq \mathcal{S}$, twice), `thm:filtration-strict` (clause (3), the identification $\mathcal{A}_\infty = \mathcal{S}$, through `lem:filtration-top`)
**Decision:** the author's decision of 2026-10-07 — "I admit Schoenberg's radial theorem as a cited interface." The composition and the narrowing are the session's (Q-0281, wave N), taken under the delegation of safe-direction choices (`CLAUDE.md`): **one composite entry**, the necessity direction of Thm. 13.14 followed by the forward direction of Thm. 3.2, as Paper V's A23 composes them, with the class of Bernstein functions never named; and **without the uniqueness of the triplet**, which Thm. 3.2 prints and `lem:bernstein-triplet-unique` proves in-house, the ledger being as narrow as the argument allows.
**Cite:** @schilling2012bernstein — Theorem 13.14 (Schoenberg; Bochner), printed p. 212, the direction "continuous and negative definite radially in every dimension ⇒ Bernstein" (proof pp. 212–214); Definition 3.1 and Theorem 3.2, printed p. 21, the direction "Bernstein ⇒ the representation (3.2)" (proof pp. 21–22); Definition 4.3, printed p. 36, with its $\mathbb{R}^d$ form (4.8), printed pp. 45–46, for "negative definite"; the Index of notation (pdf p. 13) for $\mathbb{N} = \{1, 2, 3, \dots\}$
**Lean:** `AffineHemigroup.schoenberg_radial_bernstein` (`Formalization/AffineHemigroup/Interfaces.lean`, admitted 2026-10-07, Q-0281 wave N; spent twice by `AffineHemigroup.classS_of_classAInf`, `lem:filtration-top`, and through it by `filtration_top`, the tag of `lem:filtration-top` and the fourth declaration of `thm:filtration-strict`, all guarded); $f(0) := f(0+)$, $d$ over all of $\mathbb{N}$, the hermitian condition automatic (below)

- **Statement as used.** Let $f$ be a real function on $[0,\infty)$ with $f \ge 0$ on $(0,\infty)$.
  Suppose that for every integer $d \ge 0$ the function $\xi \mapsto f(|\xi|^2)$ on $\mathbb{R}^d$ is
  continuous and negative definite in the sense of Def. 4.3:
  $$\sum_{j,k=1}^n \bigl(f(|\xi_j|^2) + f(|\xi_k|^2) - f(|\xi_j - \xi_k|^2)\bigr)\,c_j\,\overline{c_k} \ge 0$$
  for every $n$, all $\xi_1, \dots, \xi_n \in \mathbb{R}^d$ and all $c_1, \dots, c_n \in \mathbb{C}$.
  Then there are $a, b \ge 0$ and a measure $m$ on $(0,\infty)$ with
  $\int_{(0,\infty)}(1 \wedge t)\,m(dt) < \infty$ such that
  $$f(\sigma) = a + b\sigma + \int_{(0,\infty)} \bigl(1 - e^{-\sigma t}\bigr)\,m(dt) \qquad \text{for every } \sigma > 0 .$$
  It is the page's *"for all $d \in \mathbb{N}$ the function $\xi \mapsto f(|\xi|^2)$, $\xi \in
  \mathbb{R}^d$, is continuous and negative definite"* ⇒ *"$f$ is a Bernstein function"* (Thm. 13.14),
  composed with *"[a Bernstein function] admits the representation $f(\lambda) = a + b\lambda +
  \int_{(0,\infty)} (1 - e^{-\lambda t})\,\mu(dt)$, where $a, b \ge 0$ and $\mu$ is a measure on
  $(0,\infty)$ satisfying $\int_{(0,\infty)} (1 \wedge t)\,\mu(dt) < \infty$"* (Thm. 3.2).
  `lem:filtration-top` spends it twice, in its inclusion $\mathcal{A}_\infty \subseteq \mathcal{S}$: for
  $f = F(\sqrt{2\,\cdot})$, and for each $f - f(c^2\,\cdot)$, $0 < c \le 1$.
  - **$f(0) := f(0+)$.** The theorem is stated for $f : (0,\infty) \to [0,\infty)$ and evaluates
    $f(|\xi|^2)$ at $\xi = 0$; the book fixes $f(0)$ nowhere at Thm. 13.14, and fixes $f(0) := f(0+)$
    everywhere else (p. 15, p. 211, and $a = f(0+)$ in the proof of Thm. 3.2, p. 22). The entry takes
    $f$ on $[0,\infty)$; its continuity hypothesis at $\xi = 0$ forces $f(0) = f(0+)$, so the entry is
    the theorem under the book's convention.
  - **$d$ over all of $\mathbb{N}$, $d = 0$ included.** The book's $\mathbb{N}$ is $\{1, 2, 3, \dots\}$
    (Index of notation). Asking the hypothesis at $d = 0$ as well is equivalent to the page's
    hypothesis, so the entry assumes exactly what the book assumes: on $\mathbb{R}^0$, a single
    point, continuity is empty and the sum is $f(0)\,|\sum_j c_j|^2$, so the hypothesis there
    says $f(0) \ge 0$, and that is the hypothesis at $d = 1$ with $n = 1$, $\xi_1 = 0$ and
    $c_1 = 1$ (it also follows from continuity at $\xi = 0$ and $f \ge 0$ on $(0,\infty)$).
    (Sharpened on 2026-10-12, Q-0424: this sentence read "at least as strong as the page", which
    is true and which the isotropic paper had turned into "C6 assumes more than its source"; the
    paper's two sentences are corrected, `records/affine/reviews/VERIFY-round1-mathematics.md`,
    item 4. The departure from the page is the composition of one direction of each of the two
    theorems, and a conclusion that leaves out the uniqueness of the triplet.)
  - **The hermitian condition is automatic.** Def. 4.3 asks $\psi(-\xi) = \overline{\psi(\xi)}$ and the
    sum with $\overline{\psi(\xi_k)}$; for the real even function $\psi(\xi) = f(|\xi|^2)$ both reduce to
    what is written. "$\ge 0$" is in $\mathbb{C}$: the sum is real and nonnegative. "Continuous" is
    ordinary continuity; the book defines no other.
  - **The conclusion.** A measure on $(0,\infty)$ is, in the Lean, a measure on $\mathbb{R}$ with
    $m((-\infty,0]) = 0$; the identity is stated in $[0,\infty]$, every term being nonnegative, which is
    the real identity with a finite integral.
- **Primary — Schilling, Song, Vondraček, *Bernstein Functions: Theory and Applications*, 2nd ed. (de Gruyter, 2012), Theorem 13.14, p. 212, with Definition 3.1 and Theorem 3.2, p. 21**, transcribed from the page images by the librarian (`AXIOMS-verbatim.md` § A10): *"**Theorem 13.14** (Schoenberg; Bochner). A function $f : (0,\infty) \to [0,\infty)$ is a Bernstein function if, and only if, for all $d \in \mathbb{N}$ the function $\xi \mapsto f(|\xi|^2)$, $\xi \in \mathbb{R}^d$, is continuous and negative definite."* *"**Theorem 3.2.** A function $f : (0,\infty) \to \mathbb{R}$ is a Bernstein function if, and only if, it admits the representation $f(\lambda) = a + b\lambda + \int_{(0,\infty)} (1 - e^{-\lambda t})\,\mu(dt)$, (3.2), where $a, b \ge 0$ and $\mu$ is a measure on $(0,\infty)$ satisfying $\int_{(0,\infty)} (1 \wedge t)\,\mu(dt) < \infty$. In particular, the triplet $(a, b, \mu)$ determines $f$ uniquely and vice versa."* *"**Definition 4.3.** A function $f : S \to \mathbb{C}$ is negative definite if it is hermitian, i.e. $f(s^*) = \overline{f(s)}$, and if $\sum_{j,k=1}^{n} ( f(s_j) + \overline{f(s_k)} - f(s_j + s_k^*) )\, c_j \bar{c}_k \ge 0$ (4.2) holds for all $n \in \mathbb{N}$, all $s_1,\dots,s_n \in S$ and all $c_1,\dots,c_n \in \mathbb{C}$"*, with $\xi^* = -\xi$ on $\mathbb{R}^d$ (p. 45). Recorded in `records/affine/READING-schilling2012bernstein-schoenberg.md`.
- **What the entry does NOT carry.** **The converse of Thm. 13.14** (its sufficiency direction, Example 13.13: a Bernstein function is radially negative definite in every dimension): the inclusion $\mathcal{S} \subseteq \mathcal{A}_\infty$ is proved from `lem:delay-polar-profile` and the polar criterion (**A2**, **A3**(iii)). **The uniqueness of the triplet**, the last sentence of Thm. 3.2, and its converse: `lem:bernstein-triplet-unique` proves it from the uniqueness of a finite measure on $(0,\infty)$ by its Laplace transform (the shared library's `ScaleSpace.laplace_uniqueness_locally_finite`, Lean core, `ScaleSpaceCore` v0.4.0; Paper V's until the switch to v0.4.0). **The class of Bernstein functions** (Def. 3.1's $C^\infty$ and alternating signs of the derivatives): the entry passes from the radial hypothesis to the representation, so nothing about derivatives is cited, and $a = 0$ is proved in the node from continuity. **The hypothesis**: that the radial functions are negative definite is proved in the node, by `lem:lk-negative-definite`, from the Lévy–Khintchine form the polar reading supplies (**A2**–**A4**); Schoenberg's equivalence of the negative definite and the exponential forms (Prop. 4.4) is not used. **Everything else [B]'s proof of Prop. 4.9(4) spends**: the infinite divisibility of the residual (Sato Prop. 15.5, its second clause; **A4** carries the first only), replaced by the residual's comparison of Lévy measures $(c\,\cdot)_*\nu_d \le \nu_d$, read off the nonincreasing polar profile; Bernstein's theorem on completely monotone functions and the complete monotonicity of $e^{-f}$; and the half-line characterization of self-decomposable laws (Sato Cor. 15.11 with Thm. 24.11, or SSV Prop. 5.17, p. 57, read and not used), replaced by the uniqueness of the triplet and the trunk's `ScaleSpace.exists_profile_of_dilate_le` (`lem:dilation-decreasing-profile`).
- **Why it is cited and not proved.** The necessity direction of Thm. 13.14 takes a limit in the dimension through the vague compactness of the radialised measures and the Bessel estimates of Lemma 13.15 (pp. 213–214), and Thm. 3.2's representation is Bernstein's theorem on completely monotone functions (Thm. 1.4, the Hausdorff–Bernstein–Widder theorem). Mathlib (v4.31.0, pinned) has neither, nor the classes they are stated for: no completely monotone or Bernstein functions and no negative definite functions.

## A11 — Karamata's Tauberian theorem at the origin: for a finite measure $\nu$ on $[0,\infty)$, $\int e^{-sx}\,\nu(dx) \sim c\,s^{-\rho}\ell(s)$ as $s \to \infty$ gives $\nu([0,x]) \sim c\,x^{\rho}\ell(1/x)/\Gamma(1+\rho)$ as $x \downarrow 0$
**Blueprint:** `thm:cited-A11` (the interface node, ch. 2, since 2026-10-11); `prop:origin-rate-d` (Step 4 of its proof, once in each clause); `prop:centre-increment` (Step 4 of the proof of `prop:origin-rate-d` run in dimension $d+2$ on $\mu_{d+2}$, once in each of clauses (2) and (3); no Lean)
**Decision:** the author's decision of 2026-10-11 — "adopt the rate as a proposition" (hub queue item Q-0416, whose brief names Karamata's Tauberian theorem and the monotone density theorem as the cited facts). The narrowing is the session's, taken under the delegation of safe-direction choices (`CLAUDE.md`): **one entry instead of the two the brief allowed**. The monotone density theorem (Thm. 1.7.2b of the same book) is not admitted: Step 5 of `prop:origin-rate-d` is its proof, carried out on spherical shells, and is machine-checked. Nor are Potter's bounds (Thm. 1.5.6) and Proposition 1.5.9a, which the refereed derivation used: Steps 1 and 3′ prove what the argument needs of them. The entry itself is narrowed to the direction, the measures and the parameter range the proof uses (below).
**Cite:** @bingham1987regular — Theorem 1.7.1′ (attributed there to Feller (1971), XIII, § 5), printed p. 38, the direction (1.7.2′) ⇒ (1.7.1′); the Laplace–Stieltjes transform (1.7.0a), printed p. 37, with Theorem 1.7.1 (Karamata Tauberian Theorem) on the same page, whose method of proof the page says yields 1.7.1′; the definition of a slowly varying function, (1.2.1), printed p. 6, and of the class $R_0$, printed p. 18
**Lean:** `AffineHemigroup.karamata_tauberian_zero` (`Formalization/AffineHemigroup/Interfaces.lean`, admitted 2026-10-11, Q-0416; spent in one place, `AffineHemigroup.tendsto_ball_of_gauss`, Step 4 of the proof, and through it by `origin_ball_rate` and `origin_ball_rate_critical`, the mass of a small ball in the two clauses of `prop:origin-rate-d`, and by `origin_density_rate`, `origin_density_rate_critical`, `origin_density_log_lower`, `origin_rate` and `origin_rate_critical`, which read them, all guarded and pinned); a finite measure on $[0,\infty)$, $c > 0$, $\rho > 0$, the Tauberian direction only (below)

- **Statement as used.** Let $\nu$ be a finite measure on $[0,\infty)$, let $\ell$ be a positive
  measurable function on $(0,\infty)$ with $\ell(\lambda x)/\ell(x) \to 1$ as $x \to \infty$ for
  every $\lambda > 0$, and let $c > 0$ and $\rho > 0$. If
  $$\frac{\int_{[0,\infty)} e^{-sx}\,\nu(dx)}{c\,s^{-\rho}\,\ell(s)} \to 1 \quad (s \to \infty),
  \qquad\text{then}\qquad
  \frac{\nu([0,x])}{c\,x^{\rho}\,\ell(1/x)/\Gamma(1+\rho)} \to 1 \quad (x \downarrow 0) .$$
  It is the page's *"Û(s) ∼ cs^{−ρ}ℓ(s) (s → ∞)"* ⇒ *"U(x) ∼ cx^ρℓ(1/x)/Γ(1+ρ) (x → 0+)"* for
  $U(x) = \nu((-\infty,x])$. `prop:origin-rate-d` spends it for the image $\nu$ of the law $\mu$
  under $x \mapsto |x|^2$, whose transform is $\int e^{-s|x|^2}\mu(dx)$: in clause (1) with
  $\rho = c/2$ and $\ell(s) = s^{c/2}\widehat\mu(\sqrt s\,e)$, in clause (2) with $\rho = d/2$ and
  $\ell(s) = \int_0^{\sqrt s}\widehat\mu(r e)\,r^{d-1}dr$.
  - **$U$ is the distribution function of a finite measure.** The page takes $U$ non-decreasing on
    $\mathbb{R}$ with $U = 0$ on $(-\infty,0)$ and $\hat U(s) < \infty$ for all large $s$, and defines
    $\hat U$ on p. 37 for right-continuous $U$. The entry takes $U(x) = \nu((-\infty,x])$ for a finite
    measure $\nu$ with $\nu((-\infty,0)) = 0$: non-decreasing, right-continuous, $0$ for $x < 0$, with
    $\hat U(s) = \int e^{-sx}\nu(dx)$ finite for every $s \ge 0$. A narrowing.
  - **$\ell$ on $(0,\infty)$.** The page's $\ell \in R_0$ is positive and measurable on a neighbourhood
    $[X,\infty)$ of infinity; the entry asks positivity on $(0,\infty)$ and, in the Lean,
    measurability on $\mathbb{R}$. A narrowing, and the book's own convention (p. 6: "we may (and
    often shall) suppose ℓ defined on (0,∞)").
  - **$c > 0$ and $\rho > 0$.** The page has $c \ge 0$, $\rho \ge 0$, with the case $c = 0$ read as
    $o(\cdot)$ (p. 37, after Theorem 1.7.1). The entry takes $c > 0$, where "∼" is the quotient
    tending to $1$, and $\rho > 0$, the range of the two uses.
  - **One direction.** The page states an equivalence. The entry is the Tauberian implication,
    from the transform to $U$.
- **Primary — Bingham, Goldie, Teugels, *Regular Variation* (Encyclopedia of Mathematics and its Applications 27, Cambridge University Press, 1987), Theorem 1.7.1′, p. 38**, transcribed from the page image (`AXIOMS-verbatim.md` § A11): *"**Theorem 1.7.1′** (Feller (1971), XIII, § 5). Let $U$ be non-decreasing on $\mathbb{R}$, $U(x) = 0$ for all $x < 0$, and such that $\hat U(s) < \infty$ for all large $s$. Let $\ell \in R_0$, $c \ge 0$, $\rho \ge 0$. The following are equivalent: $U(x) \sim cx^{\rho}\ell(1/x)/\Gamma(1+\rho)$ $(x \to 0+)$, (1.7.1′); $\hat U(s) \sim cs^{-\rho}\ell(s)$ $(s \to \infty)$. (1.7.2′)"* The transform, p. 37: *"If $U : \mathbb{R} \to \mathbb{R}$ has locally bounded variation (see Appendix 6), is right-continuous, and vanishes on $(-\infty,0)$, we define its Laplace–Stieltjes transform (LS transform) $\hat U(s) := \int_{-\infty}^{\infty} e^{-sx}\,dU(x) = \int_{[0,\infty)} e^{-sx}\,dU(x)$, (1.7.0a)"*. Slow variation, p. 6: *"Let $\ell$ be a positive measurable function, defined on some neighbourhood $[X,\infty)$ of infinity, and satisfying $\ell(\lambda x)/\ell(x) \to 1$ $(x \to \infty)$ $\forall\lambda > 0$; (1.2.1) then $\ell$ is said to be slowly varying (in Karamata's sense)."* Recorded in `records/affine/READING-bingham1987regular-karamata.md` (this item's reading at the page images; Q-0414's note `READING-bingham1987regular.md`, on that item's branch, has the same pages and the book's page mapping).
- **What the entry does NOT carry.** **The Abelian direction** (1.7.1′) ⇒ (1.7.2′), and the cases $c = 0$ and $\rho = 0$. **Theorem 1.7.1** itself, the form at $x \to \infty$, $s \to 0+$. **The behaviour of the transform**: that $\int e^{-s|x|^2}\mu(dx)$ is asymptotic to a constant times $\widehat\mu(\sqrt s\,e)$, or to $s^{-d/2}$ times the truncated integral at $c = d$, is Steps 1–3′ of `prop:origin-rate-d`, proved from `lem:positive-transform-origin`(1), `lem:isotropic-exponent-log`(2) and the monotonicity of the transform along rays. **Three other results of the book that the refereed derivation used**, each proved in the form the proof needs and machine-checked: the **monotone density theorem** (Thm. 1.7.2b, pp. 39–40), replaced by its own argument (1.7.5) on spherical shells (`AffineHemigroup.tendsto_radial_density_of_ball`); **Potter's bounds** (Thm. 1.5.6, p. 25), replaced by a dyadic iteration of one ratio limit for a monotone function (`AffineHemigroup.antitoneOn_dyadic_bound`); **Proposition 1.5.9a** (p. 26), replaced by a direct proof that the truncated integral of the transform is slowly varying (`AffineHemigroup.IsRayProfile.tendsto_truncMoment_dilate`). The uniform convergence theorem (Thm. 1.2.1) is not used.
- **Why it is cited and not proved.** The book's proof of Theorem 1.7.1 (pp. 37–38) passes through the continuity theorem for Laplace–Stieltjes transforms of unbounded measures (Feller (1971), XIII.1, Theorem 2a), which rests on the uniqueness theorem and a selection argument; Karamata's own route is by polynomial approximation of an indicator. Mathlib (v4.31.0, pinned) has neither a continuity theorem for Laplace transforms of measures nor any regular variation, and the shared library has only the uniqueness of a finite measure by its Laplace transform. A proof would be a development of its own.

## What is deliberately NOT here

- **Sato Theorems 28.4 (p. 191) and 53.8 (pp. 410–411)**, the one-dimensional origin behaviour of
  a self-decomposable density. They are the line repository's ledger entry A10 and are **not** read
  from this module: nothing here cites them, and the reason is the finding of
  `records/affine/READING-sato1999levy-dimension-d.md` § 3 — both are stated on $\mathbb{R}$, so
  there is nothing in them for a $d$-dimensional node to spend. Their conclusion, transported to
  $\mathbb{R}^d$, was named as a **hypothesis** of the blueprint, (H) (`def:radial-origin-asymptotic`,
  Q-0043 to Q-0151). Q-0151 made it unnecessary: the unboundedness it delivered is
  `thm:origin-boundedness-d`(4) for every datum, by Gaussian smoothing of a positive transform, and
  the definition was withdrawn (the author, 2026-10-03). Its pointwise rate, in every dimension
  $d \ge 1$, is `prop:origin-rate-d` since Q-0416, on entry **A11** and not on these two theorems;
  a radially nonincreasing density is
  `prop:isotropic-radial-monotone` since Q-0316, on entry **A8**. A
  hypothesis a node carries is not an entry in this ledger; an entry is something a source
  supplies.
- **Karamata's Tauberian theorem in `thm:origin-boundedness-d`** (Sato's route to Theorem 53.8,
  through Feller pp. 445–446). `thm:origin-boundedness-d`(3) replaces it by an exact Gamma
  identity, which is why the subordinated half needs no Tauberian input and holds at the threshold
  $c=d$ as well as below it. The threshold theorem still spends no Tauberian theorem. The rate at
  the origin does: since Q-0416 the theorem is entry **A11**, spent by `prop:origin-rate-d` and, through Step 4 of that proof run in dimension
  $d+2$, by `prop:centre-increment`.
- **The monotone density theorem, Potter's bounds and Proposition 1.5.9a of Bingham, Goldie and
  Teugels** (Thm. 1.7.2b, pp. 39–40; Thm. 1.5.6, p. 25; Prop. 1.5.9a, p. 26), read at the page
  for Q-0416 and not cited: `prop:origin-rate-d` proves what its argument needs of each (entry
  **A11**, "What the entry does NOT carry").
- **The stable-cone section spends A3 and A5 and nothing else.** Sato's Theorem 14.14 (p. 86,
  the rotation-invariant stable laws) is read at the page and not cited: `lem:elliptical-stable`
  builds the law from its Lévy density with **A3**(iii), and its exponent identity is a
  substitution (`records/affine/READING-sato1999levy-stable-laws.md`). The **Tauberian theorem** the
  proposal expected for necessity is not used: `lem:stable-tail` needs only the weak tail, which
  homogeneity gives. Jurek–Mason's Propositions 3.3.6, 3.3.10 and 3.4.1 and Sato–Yamazato's
  representation theorems are read and named in annotations, not used. Three things
  `prop:tempered-step-cone` (Q-0263) could have cited are avoided: the **moment theorem for
  infinitely divisible laws** (exponential moments from those of the Lévy measure), replaced by a
  construction of the law as an $L^2$ sum of independent compound Poisson vectors and Fatou's lemma,
  without **Lévy's continuity theorem on $\mathbb{R}^d$**; the **Lévy densities of named families**
  (the normal-inverse-Gaussian, the tempered stable laws), replaced by one subordination of the
  heat kernel computed in the node, the names left unchecked and unused; and **Bessel functions**,
  which that subordination never meets.
- **The Q-0264 nodes cite two things less than they could.** The **Loewner–Heinz inequality**
  ($\Sigma \le \Sigma' \Rightarrow \Sigma^p \le \Sigma'^p$ for $0 < p < 1$), which
  `prop:similarity-degenerate-family` needs, is proved in that node from the integral representation
  of $\tau^p$ and the order reversal of inversion. The **injectivity of the logarithmic cosine
  transform on the sphere** (spherical harmonics, the Funk–Hecke formula), which a directional
  form of `prop:similarity-general-index-zero` under positive increments would want, is not used:
  that node's clause (3) is stated for the difference of exponents, where the blow-up needs only
  dominated convergence, and the directional form on Lévy measures is left open.
- **The nodes holding the draft's § 2.2–§ 2.4 (in chapters 4 and 5) spend nothing.** They read
  the uniqueness of the Fourier transform of a probability measure on $\mathbb{R}^d$, Fubini,
  Fourier inversion for a Schwartz function and the Gaussian and Gamma integrals, as the chapter's
  earlier nodes already do, and each node's annotation names what it uses. Three things the draft
  leans on there are deliberately avoided rather than cited. The **Lévy–Khintchine representation
  on $\mathbb{R}^d$** (A3's theorem), through which the draft's Lemma 2.7 reads a negative definite
  exponent: `lem:charfn-one-on-subspace` states the lemma for a probability measure instead, and no
  rigidity node needs infinite divisibility. **Khintchine's null-array theorem** (the draft's Lemma
  2.6, through [V, Thm. 5.2] ported to $\mathbb{R}^d$): `lem:affine-reduction` and the rigidity do
  without it; it is now entry **A6**, spent only by `thm:cascade-infinitely-divisible`,
  `prop:similarity-cascade-families` and `prop:similarity-stable-order-kernels` (the author's decision
  of 2026-10-03). The scheme (`def:gw-cascade-family`) and the parameter-space lemma
  (`lem:parameter-space`) spend nothing: the latter reads Fourier uniqueness, the polar decomposition and
  dominated convergence. Nor do the ray column's nodes (Q-0267: `lem:gw-kernels-from-origin`,
  `prop:gw-ray-families`, `prop:similarity-ray-families`, `prop:diagonal-ray-families`; and
  `lem:gw-kernels-self-decomposable`, Q-0281 wave 1, which states for every wedge datum that a family's
  kernels from scale zero are self-decomposable and zero-free).<!-- CHANGED Q-0281 wave 1: blind check KS-9 --> Their kernels are
  infinitely divisible by **A6**, the ray order having the path condition, and self-decomposable laws are
  infinitely divisible by **A4**; neither is spent, because all those nodes need is that a
  self-decomposable law has a characteristic function without zeros, which `prop:gw-ray-families`(1)
  proves in a few lines (the first zero along a ray, and $1 - |\varphi(2\xi)|^2 \le 4(1 - |\varphi(\xi)|^2)$). And the
  **small-argument asymptotics of the Bessel potential and its derivatives** (the draft's proof of
  Proposition 2.15): the remark after the proof of `prop:matern-cross-shape` writes the Green's function
  as the Laplace transform of the heat kernel and reads the leading term off one Gamma integral, and
  `prop:matern-negative-mass` reads its logarithmic negative mass off the same leading term.<!-- CHANGED Q-0281 wave 2: blind review W2E-2 -->
  **Lévy's continuity
  theorem** is not cited either: the continuity axiom (K2) of `def:affine-cascade-family` is stated
  on the transforms, and the one proof that needs weak convergence, that of
  `thm:cascade-infinitely-divisible`(1), takes the theorem from Mathlib (next item).<!-- CHANGED Q-0281 wave 2: blind review W2C-1 -->
- **Lévy's continuity theorem on $\mathbb{R}^d$, read at the page and not admitted (Q-0314).** The
  brief of Q-0314 admitted it as **A7** (the author following review flag 13), so that the paper could
  claim the converses of `lem:operators-to-kernels`(4)–(5) and the operator form of the rigidity. Its
  anchor is Sato 1999, Proposition 2.5(vii), printed p. 9 (*"If $\widehat\mu_n(z) \to \widehat\mu(z)$
  for every $z$, then $\mu_n \to \mu$"*, with Definition 2.2, p. 7), transcribed from the page image in
  `records/affine/READING-sato1999levy-continuity.md`. Writing the statement found that the converse
  needs less: $\mu_n * f \to \mu * f$ in $L^1$, which `lem:kernels-to-operators`(1) proves by Gaussian
  smoothing (a Fourier integral, dominated convergence and Scheffé's argument), citing nothing.
  Since wave 2 of Q-0281 (group C) one proof uses the theorem itself: that of
  `thm:cascade-infinitely-divisible`(1) shows the steps of a cascade infinitesimal through Lévy's
  continuity theorem on $\mathbb{R}^d$ and the portmanteau inequality, and takes both from Mathlib
  (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`,
  `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`). **The author's decision of
  2026-10-05** (blind review W2C-1, `records/formalization/REVIEW-wave2.md`) accepts that route: a
  theorem Mathlib proves is a standard theorem, not a citation and not an entry, and the guard prints
  A6 and Lean core for that node. So no entry is admitted, the number A7 is unused, and the reading
  note keeps the transcription.<!-- CHANGED Q-0281 wave 2: blind review W2C-1 -->
- **The isotropic classification and the bridge (§ 3.2, `03-isotropic.tex`) spend nothing but A2–A4, and
  those only in the reading (2.1).** `thm:isotropic-classification` and `prop:isotropic-bridge`
  cite released statements of the line and cone modules — [V, Thm. 7.3], [V, Prop. 2.8] (Lévy's
  continuity theorem **on the line**), [V, Lem. 6.3], [B, Lem. 4.2], [B, Prop. 4.5], [B, Prop.
  5.10(2)] — restated where they are used. A released statement is cited by its version, and its
  own ledger stays in its own repository; it is not copied here. What the draft's native port
  would have needed is avoided rather than cited: the **null array in $\mathbb{R}^d$** (the
  draft's port note on [V, § 5]), **Lévy's continuity theorem on $\mathbb{R}^d$**, **Bochner's
  theorem**, and the **no-lattice lemma**. The null array has been entry **A6** since 2026-10-03,
  and these nodes still do not spend it; `thm:cascade-infinitely-divisible`(4) gives the isotropic
  increments' infinite divisibility through it, independently of them. The one place these nodes
  need infinite divisibility on $\mathbb{R}^d$, the reading of $\mathcal{A}_d$ as the polar form, is A4. The causal kernels of
  `prop:isotropic-bridge` are taken as given by the node (the Lean hypothesis `IsCausalKernels`),
  and so is, in its Student-t clause, the family whose delay law is the inverse-gamma law (the
  hypothesis `hT` of `isotropic_bridge_student_family`). That these families exist is in print,
  and it is cited in the node's annotation and in the paper, not admitted here, because no
  declaration reads it: the classification of the time-causal paper (`fagerstrom2026hemigroup`,
  version 1.1.0, Thm. 7.3, with its Prop. 8.17 for the inverse-gamma delay), on Halgreen's theorem
  that the inverse-gamma laws are self-decomposable (pp. 13–15,
  `records/affine/READING-halgreen1979self.md`; Bondesson, § 4, pp. 51–52,
  `READING-bondesson1978infinite.md`).<!-- CHANGED Q-0431: the Student-t clause is presented on
  the published theorem it rests on (the author's section review of 2026-10-12); the node's
  logical form and its Lean are unchanged -->

- **Stirling's formula.** `lem:threshold-limit` needs only its order, $\Gamma(m) \asymp
  m^{m-1/2}e^{-m}$, and proves the two-sided bound
  $e^{-1/2} \le \Gamma(m)\,m^{1/2-m}e^m \le \sqrt{\pi/2}+\sqrt\pi+4$ for $m \ge 1$ in its own proof
  (the substitution $t = m(1+u)$ and elementary bounds on $u - \log(1+u)$), so nothing is cited.
- **Four historical or naming citations the draft's prose makes in chapter 2 and 3, checked at the
  page and found decorative.** Lindeberg 2011 (Corollary 2.9's comparison of
  `thm:affine-rigidity` with his semigroup-plus-non-enhancement derivation), Whittle 1954 and
  Lindgren–Rue–Lindström 2011 (Proposition 2.10 and Proposition 3.2(1)'s naming of
  `prop:affine-orbits`(4) and `prop:discrete-helmholtz`(1)'s families as the anisotropic and the
  continuum Matérn covariance), read at the page at Q-0225, and Lindeberg–Gårding 1994 (Remark
  2.17's claim that practised shape-adapted smoothing re-smooths the original image with each new
  $\Sigma$), read at the page at Q-0255 once the library acquired it: all four are read
  (`records/affine/READING-lindeberg2011generalized.md`,
  `records/affine/READING-whittle1954stationary.md`,
  `records/affine/READING-lindgren2011explicit.md`,
  `records/affine/READING-lindeberg1994shape.md`) and the prose is accurate, but none is a fact a
  node's proof rests on — each node proves its family's characteristic function, positivity or
  generator in-house, and the citation only attaches a name or a comparison.
- **Three classical theories the draft's §§ 2.4, 3 and 4 name, avoided rather than cited**
  (Q-0209). The **self-decomposability of the Gamma law** (behind the Matérn orbit's ray increments
  for non-integer $\gamma$): `prop:affine-orbits`(4) writes the residual as an explicit compound
  Poisson law through Frullani's integral. The **Herschel–Maxwell characterization** in a
  non-orthogonal frame (the draft's Proposition 3.3): `lem:rotation-invariant-image` solves the
  functional equation with a non-diagonal matrix in its own proof. The **Calderón–Zygmund theory**
  (Remark 4.1's "singular integral"): `prop:matern-hessian` works on $L^2$, where the Riesz
  transforms are Fourier multipliers, and the principal-value kernel and the $L^p$ bounds are
  named in its annotation as not claimed.
- **The Lie theory of semigroups and invariant cone fields, and the matrix inequalities behind it,
  proved rather than cited** (Q-0266). The correspondence between invariant orders on $\mathrm{PD}(d)$
  and invariant cones (`prop:invariant-orders`, `lem:spectral-cones`, `thm:cone-orders`,
  `prop:stable-order-generated`) is in print in general form: Lawson 1989 (Prop. 6.3, Thm. 4.9,
  Thms. 7.4–7.5), Hilgert–Hofmann–Lawson 1989 (Prop. V.1.7, Cor. V.4.58, Thm. VI.5.1) and
  Hilgert–Ólafsson 1997 (Thm. 2.2.2, Lemma 2.3.1, Thm. 2.3.4), all read at the page
  (`records/affine/READING-lawson1989ordered.md`, `records/affine/READING-hilgert1989lie.md`,
  `records/affine/READING-hilgert1997causal.md`; and `records/affine/READING-faraut1994analysis.md` for
  the setting). None is an entry: the four nodes prove what they use, with Ky Fan's minimum
  principle written out, and the annotations say which statements the sources contain. One matrix
  inequality is cited instead of proved since the author's decision of 2026-10-05: the logarithmic
  majorization of a product, entry **A9**, whose proof through compound matrices and Cauchy–Binet
  costs more than everything else in the section. No Cauchy–Binet entry and no general majorization
  entry are admitted, and `prop:stable-order-generated` spends nothing: its proof reads the stable
  orders through the map $\Phi_\alpha$ and the Loewner order, not through `thm:cone-orders`. Besides
  A9, the entries spent in that section are A5 and A3, by `thm:wedge-axis` through
  `prop:anisotropy-budget` and the stable-cone nodes.
