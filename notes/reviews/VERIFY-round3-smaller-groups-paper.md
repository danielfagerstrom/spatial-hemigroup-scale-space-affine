# Verification of the content review, round 3 (the affine paper, `review-3`), report E: § 4.9, § 5 and Appendices D and F–I

*2026-11-03. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is checked
against the text, the blueprint and the sources before anything changes. This record verifies
report E of the round-3 content review,
`review-content-review-3-E-section-4.9-5-appendices-D-F-I-claude-fable-5.1.md` (major revision; ten
required changes, eleven suggestions, and the claims of its §§ 2–7). This record changes no `.tex`,
`.lean` or blueprint file.*

## Inputs and conventions

- **The build.** `review-build-review-3.pdf`, 110 pages, frozen at `59c56bd`. `git diff 59c56bd HEAD
  -- paper blueprint Formalization` is `paper/references.bib` only (+2 lines), so the sources are
  those of the build; `paper/main.pdf` was rebuilt after that change and is not byte-identical.
  Printed page = PDF page (checked on every page of `pdftotext -layout`). Page numbers are the
  report's. Sources are cited as file:line; numbers of labels are from `paper/main.aux`.
- **Scripts** (`verify-round3-paper-scripts/`, each with its `-output.txt`):
  `sketched_statements.py` (the twenty sketched statements: blueprint node, `\lean` tags, `\leanok`
  on statement and proof, proof of record against sketch in non-comment source characters, pages
  calibrated on Appendix C, which prints proofs of record: 5520 characters a page);
  `remark_h3_checks.py` (Remark H.3 re-run through the deposited
  `records/affine/check-gaussian-matern-step.py`, unchanged, with the referee's further claims).
- **Lean.** Not rebuilt here. `Formalization/AffineHemigroup` has no `sorry` outside comments
  (`Probes*.lean`, lines 17); declarations were read in source.
- **Librarian.** `library resolve` and `library search` (Sato–Yamazato 1984, p. 73); the reading
  notes `READING-jurek1982integral.md`, `READING-jurek1983integral-driving-process.md`,
  `READING-sato1984operator.md`.
- **Decisions that bear on these findings.** `PLAN-review-response-paper.md` § 0: D1–D2 (4.15 and
  4.19 printed in full; the other twenty sketches stay, the deposit gets a citable address), D3 (no
  merging of propositions, no supplement; Appendices D and E stay), D5. § R2.0: D8 (4.20 split,
  (3)–(5) printed as 4.24 in § 4.9), D9 (F.2 and H.1 stay in the appendices). `adr/0006` items 5
  (§ 4.9 and Appendices F–H keep their place) and 7 (no page budget). `adr/0003` (what a session may
  change). Round 2's verdict on a condensed Table 2 cell: `VERIFY-round2-structure-paper.md` § 4.3.
- **Verdicts.** **CONFIRMED**: the finding holds as stated. **PARTLY**: part holds, part not (both
  said). **REFUTED**: the paper is right, and why.
- **Classes of response.** **safe**: a change a session may make under `adr/0003`, stated exactly,
  with its route (paper-side text, or blueprint and re-transcription under `adr/0004`). **author**:
  changes what the paper claims or its structure, reverses D1–D9, or chooses between routes; a new
  theorem or the closing of an open problem is always the author's. **decline**: wrong, or against
  a rule or decision.

---

## 1. Headline (i): Theorem 3.5 makes the ordered-density condition necessary for (GL(d), ≤α) (report § 3.1; required change 1; suggestions 2, 8)

**Quotes.** All in the build. p. 48 (`paper/05-wedge-axis.tex:99-100`): "For general profiles the
row is known to be at least the one stated: that µI ∈ Fα forces R(λ) ≥ λα is the open converse of
Proposition 4.13." p. 55, problem 1 (`06-open-problems.tex:97-107`): "The converse would complete the
profile clause of Theorem 4.21(3) and of Proposition 4.20(2)". p. 55, problem 3
(`06-open-problems.tex:124-125`): "Whether two cones with the same number β(C) … carry the same
families is not decided either." p. 54 (`06-open-problems.tex:84-86`): "four cells … stop short …
Along the stable orders the orbit of a general profile is described by a sufficient condition". The
same conflation is in the blueprint's annotations: `thm:wedge-axis` (`05-table.tex:116-120`),
`prop:similarity-stable-order-families` (`05-smaller-groups.tex:2371-2374`), `lem:dilation-ratio`
(`05-orbits.tex:948-949`), and p. 44 (`05-orbits.tex:598`).

**The argument, step by step** (d ≥ 2, 0 < α < 2; µI ∈ Fα with family (µΣ,Σ′) along ≤α).
1. *Kernels.* (K3) with G = GL(d) gives µΣ = (Σ^{1/2})∗µI (Prop. 3.4(3), p. 18). ✓
2. *Path condition.* Prop. 4.20(1) (p. 46): (G, ≤α) has (P) for every G ⊇ dilations; the chains are
   Theorem 3.5(3)(c) on PD(d) and the ray chains (p. 20–21). ✓
3. *Infinite divisibility.* Theorem 3.5(2): every µΣ,Σ′ and every µΣ is infinitely divisible. The
   paper already states this for G = GL(d): Prop. 4.24(1) (p. 53) is for "a closed subgroup G of
   GL(d) with S(d) ⊆ G", so GL(d) included; its axiom line in Appendix I is "C1: Proposition 4.24,
   for its clause (1)" (p. 104). ✓
4. *Triplets add.* µΣ′ = µΣ ∗ µΣ,Σ′ (K1 at 0 ≤α Σ ≤α Σ′); by C2(ii) the Lévy measures satisfy
   LΣ′ = LΣ + L(µΣ,Σ′) ≥ LΣ and the Gaussian parts add. ✓
5. *Ordered densities everywhere.* For µI = N(0, aI) ∗ ν with ν the law of Prop. 4.13(1) of a profile
   k, LΣ = nΣ(x)dx, so nΣ ≤ nΣ′ a.e. With k right-continuous this is everywhere: this is exactly
   Proposition H.2(1) (p. 96) with h = id and C(Σ) = aΣ, whose statement already asks k right-continuous
   and whose Lean is `AffineHemigroup.sim_orbit_id_increment` (`SimilarityOrbit.lean:195-207`: from an
   infinitely divisible increment between `N(0,C S) ∗ orbit(h S)` and `N(0,C S′) ∗ orbit(h S′)` to
   `det M ≤ λmin(M)^d R(λmin(M)^{1/2})²`). ✓
6. *The rung.* Lemma 4.14(4), "only if" half (blueprint `05-orbits.tex`, proof of (4)): the step
   I ⪯α M := diag(λ², …, λ², λ^{2(1+α)}) and Prop. 4.13(2) give R(λ) ≥ λ^α for every λ > 1, so
   α ≤ β₋(k). ✓
7. *Gaussian part, sufficiency.* N(0, 2bΣ) cascades along Loewner ⊇ ≤α (Prop. 4.20(1)); the product
   of two families whose transforms have no zeros satisfies (a)–(d) of Lemma 3.3(2), so it is a
   family by Lemma 3.3(3). (The report cites Lemma 3.3(3); right, through (a)–(d).) ✓
8. *Cones of Theorem 4.21(2)(c).* For C with β(C) < 2 and X* ∈ C attaining β(C) (attained, p. 48),
   the curve s ↦ e^{sX*} has relative velocity X* ∈ C, so I ⪯⁺C e^{tX*}; (⪯⁺C, PSD(d)) has (P) by
   that curve and the ray chains. Step 5 at M = e^{tX*} (λmin(M) = e^{tλ}, det M = e^{t(d+β)λ},
   λ := λmin(X*) > 0) gives R(μ) ≥ μ^{β(C)} for every μ = e^{tλ/2} > 1. Conversely C ⊆ C_{β(C)}
   (Thm. 4.21(2)(c)) and Lemma 3.3(1) restricts every ≤_{β(C)}-family. ✓

**What it proves.** No gap in the logic; the referee's own "place to look" ((K2) on all of PW) is
not an obstacle, since (K2) is an axiom on all pairs. Precisely:
- (A) *Within the profile class, no new cited fact.* For a ≥ 0 and k as in Prop. 4.13 and
  right-continuous, N(0, aI) ∗ µI^{(k)} ∈ Fα **iff** R(λ) ≥ λ^α for every λ ≥ 1 (i.e. α ≤ β₋(k)).
  Prop. 4.20(2) becomes an "iff" (for right-continuous k), the profile clause of 4.21(3)(c) the same,
  with the Gaussian part free (this also answers report C's required change 3, which found laws
  with a Gaussian part undescribed). Rests on C1 (Thm. 3.5) and C2, which 4.24(1) and H.2(1)
  already spend.
- (B) *The whole cell.* To say that every µI ∈ Fα is of that form needs the polar criterion: a
  rotation-invariant self-decomposable law is N(0, aI) ∗ ν_k with k nonincreasing ([16, Prop. 3.11],
  restated on p. 11 by citation; Sato Thm. 15.10). In the shared development that is the axiom
  `AffineHemigroup.sato_polar_criterion` (A2, `blueprint/trust-boundary.txt:23-24`), which is **not**
  among the affine paper's four cited facts C1–C4 (§ 1.1, p. 6). So (B) adds a fifth cited fact to
  this paper's trust base, or a proof of A2's Lévy-measure half (a rotation-invariant L with
  (√c)∗L ≥ L for c ≥ 1 has a nonincreasing polar profile). With (B), (GL(d), ≤α) is a complete
  description and § 5's count of complete cells is three, not two.
- (C) *Cones.* With (A)/(B), the (GL(d), ⪯⁺C)-families with β(C) < 2 are those of ≤_{β(C)}: they
  depend on C only through β(C), which answers problem 3's second question. Problem 3's first
  question (orders without a cone) is untouched.
- Also: the tempered profiles r^{−α}j of Prop. E.1 have β₋ = β = α (Lemma 4.14, p. 44), so their
  family cell becomes exact (in F_β iff β ≤ α).

**What it does not prove.** The single-step converse (does one positive increment force ordered
densities?) stays open: problem 1 as stated for single steps, p. 43's "For a general profile it is
open", Prop. 4.19's last sentence, and Table 3's "at least" rows. The representative point
(suggestion 8) is real but narrower than said: R depends on the value of k at its jumps; for the
right-continuous representative k̃, R_{k̃} ≥ R_k (a limit from the right of the quotients), so
sufficiency holds for any representative and necessity yields R_{k̃}. Stating the new clause for
right-continuous k, as H.2 does, settles it; R's definition need not change.

**Why the paper says "open".** No record discusses the route. The annotations identify the family
converse with the single-step converse of `prop:orbit-step-cone`; the prior-art record closed the
factor-theorem route to the latter (`PRIOR-ART-positioning.md:220-224`); round 1 confirmed the open
statement without testing it (`VERIFY-round1-mathematics-paper.md:102-114`).

**Verdict: CONFIRMED** (with the qualifications above: right-continuity; (B) needs A2).

**Response: author** (a new theorem clause; closes part of open problem 1 and problem 3's second
question; changes Table 2, § 5's count, possibly the abstract and Appendix I). Options:
- (a) Add (A) as a clause of `prop:similarity-stable-order-families`(2) and of `thm:wedge-axis`(3)(c)
  (the "iff" for right-continuous k, with N(0, aI) ∗ ·) and (C) to (2)(c); proof ≈ 6 lines from
  4.24(1), H.2(1), Lemma 4.14(4); Lean an assembly of `gw_family_infinitelyDivisible`,
  `sim_orbit_id_increment` and the dilation-ratio lemma (estimated under 150 lines; Theorem 4.21's
  guard then gains `khintchine_null_array`, and Appendix I's "C1:" line changes). Blind referee per
  `CLAUDE.md`. Print ≈ +0.3 page. Rewrite p. 48's sentence, problem 1 (single step only), problem 3,
  Table 2's GL(d)/≤α cell ("exactly the orbits … with β₋(k) ≥ α, with any Gaussian part"), § 5.
- (b) (a) plus (B): the cell complete. Needs the author's decision to add A2 to § 1.1's list (or a new
  node proving its Lévy-measure half); then § 5 counts three complete cells and the abstract can say so.
- (c) No new statement: replace "is the open converse of Proposition 4.13" (p. 48, p. 44,
  problem 1's last sentence, the three annotations) by "is not stated here". This is the only
  `adr/0003`-safe reading, and it leaves a provable statement unproved.

*Recommended: (a), with (B) put to the author as a trust-base question.* (a) costs no new cited fact
and settles what reports C and E both found missing; (B) is worth one more cited fact only if the
author wants Table 2 to claim the cell complete. Suggestion 2 (Table 3's caption: single steps;
Table 2: families) becomes **safe** once (a) lands.

---

## 2. Headline (ii): the sketch of Proposition H.8(3) (report § 3.7; required change 2)

**Quote.** p. 102, sketch of (3) (`appendix-similarity-loewner.tex:565-570`): "the increment ρ has
0 < ρ̂ ≤ 1, and ρ̂(ω/ε) → t^{−c/2}e^{∆Σ(ω/|ω|)}". In the build.

**Check.** Under the first hypothesis (infinitely divisible Loewner increments, a Gaussian part
allowed), the full increment's transform carries exp[−½⟨ω, (C(tI) − C(Σ))ω⟩], which tends to 0
along ω/ε off ker(C(tI) − C(Σ)); the sketch's limit is then false and the identity reads 0 = 0. The
referee is right about the **sketch**. The **proof of record** does not do this
(`blueprint/src/parts/05-smaller-groups.tex:2135-2149`): under the first hypothesis it takes the
Lévy measure ν of the increment's triplet, L_{tI} = LΣ + ν (A3(i)–(ii)), symmetrizes it, and lets ρ be
the law with triplet (0, ν′, 0) (A3(iii)), the **non-Gaussian factor**, with ρ̂ = e^{−(ψ_{tI} − ψΣ)};
the Gaussian term never enters. The rest of the argument is then valid as printed. The Lean
(`sim_index_zero_blowup`, `SimilarityIndexZero.lean:651`) is `\leanok`. The referee's
finite-signed-measure route is a correct alternative under the first hypothesis only (it needs the
Lévy-measure sandwich of H.4(2)); its "(3) can be stated under the single hypothesis of (2)"
misreads (2), which has two hypotheses, and (3) is already stated under either.

**Verdict: PARTLY.** The defect is confirmed in the printed sketch only; the proof of record and the
statement are right; the replacement argument is unnecessary.

**Response: safe** (paper-side; the sketch is not shared text). In `appendix-similarity-loewner.tex:565`,
replace "For the step $\Sigma \le tI$, $t := \lambda_{\max}(\Sigma)$, the increment $\rho$ has" by "For the
step $\Sigma \le tI$, $t := \lambda_{\max}(\Sigma)$, let $\rho$ be its increment under the second hypothesis
and, under the first, the non-Gaussian factor of its increment, the law with triplet $(0, \nu', 0)$, where
$\nu = L_{tI} - L_\Sigma$ by C2(ii) and $\nu'$ is its symmetrization (C2(iii)). Then $\widehat\rho =
e^{-(\psi_{tI} - \psi_\Sigma)}$ has". Decline the referee's replacement argument and its restriction to C ≡ 0.

---

## 3. Proposition H.7: the sketches of (2) and (3) (report § 3.7; required change 3; suggestion 7)

**Quotes.** In the build: p. 101 ("satisfies ψℓ(aτ) ≥ (a²/4)ψℓ(τ) for 0 < a ≤ 1",
`appendix-similarity-loewner.tex:489-491`) and p. 102 ("two cones of directions … would carry equal
mass on every shell, which forces k(r) = k(λr) almost everywhere", `:516-518`).

**(3).** The proof of record (`05-smaller-groups.tex:2032-2050`) is the sketch's route: an open set U
around u₊ with qΣ > m′ on U and qΣ < m″ on its reflection; with k nonincreasing the sector over U
carries at least 2σ(U)I_{m′} and its image at most 2σ(U)I_{m″}; rotation invariance makes the masses
equal, so I_{m′} ≤ I_{m″}, while monotonicity gives the reverse pointwise. The comparison thus gives
an inequality **opposite** to monotonicity, which forces k(s/√m′) = k(s/√m″) a.e. The referee's "only
yields inequalities that monotonicity already gives" is wrong. The sketch omits that one sentence.
**(2).** Confirmed that the sketch gives no reason; the pointwise cosine inequality fails (a = 0.4,
θ = 5π: 0 against 0.08). The proof of record gives the referee's reason (`05-smaller-groups.tex:1935-1937`).

**Verdict.** (3): **REFUTED** as a gap; the sketch is terse. (2): **CONFIRMED** (omitted reason).

**Response: safe** (paper-side sketch). (2): after "for $0 < a \le 1$" insert ", from $\psi_\ell(2\tau) \le
4\psi_\ell(\tau)$ and the monotonicity of $\psi_\ell$". (3): replace the sentence by "If $L_\Sigma$ were
rotation invariant, a cone of directions around the largest eigenvector, on which $q_\Sigma > m'$, and its
reflection, on which $q_\Sigma < m''$, would carry equal mass on every shell; as $k$ is nonincreasing this
gives $\int_a^b k(s/\sqrt{m'})\,ds/s \le \int_a^b k(s/\sqrt{m''})\,ds/s$, the reverse of the pointwise
inequality, so $k(r) = k(\lambda r)$ almost everywhere with $\lambda = (m'/m'')^{1/2} > 1$, and then $k = 0$."
Decline the referee's disintegration route (correct, not the proof of record's).

---

## 4. Headline (iii): the twenty sketch-only statements (report §§ 1, 5.2; required change 5)

**Quote.** p. 104 (Appendix I): the list of twenty and "Their complete proofs are in the LaTeX
sources deposited". The referee's count matches (`appendix-verification.tex:49`).

**Check** (`sketched_statements-output.txt`). Every one of the twenty has a blueprint node with a
complete proof, `\leanok` on the statement and on the proof, and 2–12 declarations in its `\lean` tag:
4.4, 4.18, 4.24, A.3, D.1, E.1, E.4, F.2–F.5, H.1, H.2, H.4–H.8, 4.14, A.5. The sketches are 10–54 %
of the proofs of record (E.4 and A.5 lowest). The defects found in § 2 and § 3 are in sketches, not in
proofs of record.

**Cost of printing.**

| what is printed in place of the sketches | proofs of record | sketches | net |
|---|---|---|---|
| all twenty | 21.2 pp. | 7.5 pp. | **+13.6 pp.** |
| the eleven Table 2 cites in the smaller-group rows (F.2–F.5, H.1, H.2, H.4–H.8) | 11.1 pp. | 3.7 pp. | **+7.4 pp.** |
| H.7 and H.8 only (the two sketches found wanting) | — | — | +2.1 pp. |

(Calibrated on Appendix C; ±20 %. Round 1's estimate, "+15 pages" for 22, agrees.) A supplement is
the other route; D3 says "no supplement".

**Verdict: CONFIRMED** that the paper contains no complete proof of the twenty; **REFUTED** that
their status is hidden (§ 1.1, p. 6, and p. 104 say so). Report A (required 6) asks the same for 4.24,
A.3 and 4.4.

**Response: author** (reverses D1–D2). Options: (a) keep D2 and repair the two defective sketches
(§§ 2–3, safe; recommended); (b) print the eleven Table 2 cites (+7.4 pp.); (c) print all (+13.6 pp.);
(d) a supplement (reverses D3). *Recommended: (a).* D2 was taken with these costs known; the review's
case rests on two sketches, both repaired by one sentence each, and `adr/0006` sets no budget that (b)
or (c) would serve. If the author wants a journal-ready version, (b) is the smallest set that makes
every claim of Table 2's smaller-group rows checkable in print.

---

## 5. The trust base: the line paper's statements (report § 5.1; required change 4; suggestion 11)

**Quotes.** p. 7 (§ 1.1): "The formal development requires Mathlib and the shared library
ScaleSpaceCore, which makes no assumption of its own, and no formal development of the line paper";
p. 104: A.3 "machine-checked on Lean's logical axioms alone".

**Check.** The two sentences are consistent, and the text does not say why.
`isotropic_corner_gauge` (`Formalization/AffineHemigroup/IsotropicCorner.lean:294-310`) concludes ∃χ
and obtains it from `ScaleSpace.canonical_gauge`, which is [V, Prop. 6.6] proved in ScaleSpaceCore
(`ScaleSpaceCore.GaugeLevy`; `Upstream.lean:19-25`): the formal statement does not take the gauge
as a hypothesis. [V, Lem. 6.3]'s argument is reproved inside A.3's proof (blueprint
`04-classical.tex:916-917`). [V, Thm. 7.3] is `ScaleSpace.main_analysis` in ScaleSpaceCore, which
takes Paper V's cited clause as a hypothesis that `line_levy_unique` discharges from C2 (A3) —
hence Theorem 2.5's "C2 at d = 1" (`Upstream.lean:21-25`). Report A (required 5) and report B (a) ask
the same.

**Verdict: PARTLY.** Nothing is inconsistent or unchecked; the text does not let a reader see it.

**Response: safe.** In § 1.1 after "no formal development of the line paper", and in Appendix I's
"What is proved", one sentence: "The line paper's statements that the formal proofs use, its
Theorem 7.3 and Proposition 6.6, are proved in ScaleSpaceCore, Theorem 7.3 with the line paper's
cited clause discharged from C2 at d = 1; the fact of its Lemma 6.3 is proved again in the proof of
Proposition A.3." The fixing session confirms Lemma 2.2's and Remark 6.7's status before writing it
(Remark 6.7 is the definition φ = χ²). Suggestion 11 (shorten the axiom printout to its summary
lines): **safe, optional**. § 5.2–5.3 (what "machine-checked" means; the agents' review): no change;
both are already said (p. 7, p. 104, p. 106).

---

## 6. "Four times the eccentricity" (report § 2; required change 6; suggestions 3, 4) and the intro's citation

**Quotes.** p. 54 (`06-open-problems.tex:47`): "a departure from rotation invariance at most four
times the eccentricity of the aperture"; Table 2, p. 32: "es(ψΣ) ≤ 4 ecc(Σ)".

**Check.** Table 2 names the quantity, es(ψΣ) of the non-Gaussian part: the finding is **refuted** for
Table 2. For § 5 the claim "the kernel's Gaussian part is not bounded in this sense" is **refuted**:
Prop. 4.24(2)'s Loewner variant (p. 53) also gives cond C(Σ) ≤ ecc(Σ), the exponent spread of a
quadratic exponent is its condition number, and the spread of a sum is at most the largest of its
terms (H.5(1), p. 98); so the kernel's whole exponent has spread ≤ 4 ecc(Σ). That combined statement
is not printed, so § 5's undefined "departure from rotation invariance" outruns the statement.
Suggestion 4: the paper's Loewner examples have spread ecc^{pα/2} with p ≤ α/(d+α) (H.6, p. 99;
the report's "<" is "≤", equality at γ = 1/(d+α)), or bounded spread (H.1(3), H.7(2)); none grows like
ecc¹. Suggestion 3: confirmed, the two families differ (H.1(3), p. 95: trace term in the stable part,
condition on κ; 4.24(3), p. 53: trace term in the Gaussian part, any κ > 0). The intro (p. 5,
`01-introduction.tex:295-296`): its "So …" sentence cites only 4.21(3), H.1(3) two sentences earlier.

**Verdict: PARTLY.**

**Response: safe.** § 5 (`06-open-problems.tex:46-47`): "with a departure from rotation invariance at
most four times the eccentricity of the aperture" → "with an exponent spread of the non-Gaussian part
at most four times the eccentricity of the aperture". After 4.24 (paper-side prose, p. 53), optional:
"The families of the cell exhibited here have spreads at most ecc(Σ)^{α²/(2(d+α))} (Proposition H.6) or
bounded (Propositions H.1(3) and H.7(2)); whether the factor ecc(Σ) is attained is open." § 4.9 (p. 52),
optional: one clause after the display, "in Proposition 4.24(3) the trace term moves to the Gaussian part,
and no condition on κ is needed". p. 5: "(Proposition H.1(3) and Theorem 4.21(3))".

---

## 7. "The price of a smaller group is shape selection" (report § 2; required change 7)

**Quotes.** p. 5 (`01-introduction.tex:300-301`), p. 51 (`05-smaller-groups.tex:22-23`), p. 54
(`06-open-problems.tex:65-66`).

**Check.** § 4.1's use 1 (p. 27) defines shape selection with covariance: "The selected shape must
transform with the image, which needs the covariance group." p. 51 says "in the sense of § 4.1" and
is right. pp. 5 and 54 drop the qualifier and read as "selection is impossible", which is false, as
the referee says. Report C (required 6) makes the same point at § 4.1.

**Verdict: PARTLY.**

**Response: safe.** p. 5: "The price of a smaller group is shape selection that transforms with the
image, which needs …"; p. 54: "at the price of shape selection that transforms with the image, which
needs …". Keep p. 51. Do not adopt "the affine covariance of the selection" verbatim: for the
similarities the selection keeps its covariance under the group.

---

## 8. Remark H.3 (report § 4; required change 8; suggestion 1)

**Reproduced** (`remark_h3_checks-output.txt`, through the deposited script unchanged). h(Σ) =
diag(3.6, 2.9), h(Σ′) = diag(4.85, 4.65), side 132.14, spacings 0.1290 and 0.0645, largest frequencies
24.35 and 48.69. b = 2: min/max −1.5·10⁻¹⁷ at 1024², 2048², 4096². b = 0.1: negative mass 1.28·10⁻²,
1.40·10⁻², 1.38·10⁻² (min/max −1.0·10⁻², −9.6·10⁻³, −9.6·10⁻³). The referee's table matches to the
digits printed. One difference: his calibration ray Σ → 1.4Σ is not the script's, which uses Σ → 2Σ
at 2048² only; at 1024² and b = 0.1 the 1.4Σ ray gives −1.4·10⁻⁷ (reproduced), the 2Σ ray −8.9·10⁻¹⁰.
The Gaussian factor at the 1024 grid's edge is 0.052 (reproduced): the 1024 value is truncated, the
2048 and 4096 values agree. Sub-steps at b = 2: 0 → ½ and ½ → 1 nonnegative to rounding; 0 → ¼, 0 →
0.1 negative mass 8–9·10⁻⁶ and 1.0·10⁻³ at both resolutions (reproduced); 0 → 0.02 is 4.9·10⁻² at
1024² and 1.1·10⁻³ at 2048², not converged. The threshold of the full step lies between b = 0.4
(2.2·10⁻⁴) and b = 0.5 (rounding); the report's "between 0.3 and 0.5" is right. The deduction of
suggestion 1 is valid: if every sub-step increment along Σ + τP were a probability measure, they would
form a cascade along an interval with continuous transforms, infinitely divisible by Theorem 3.5(1).

**Verdict: CONFIRMED** (wording ambiguous; the b = 0.1 value is better quoted at 2048²); suggestion 1
correct, its smallest sub-step unresolved.

**Response: safe** (paper-side remark, `appendix-similarity-loewner.tex:168-174`). "on the frequency
grid of a square of side … centred at the origin" → "on the frequency grid of a spatial square of side
… centred at the origin"; "negative mass about $10^{-2}$" → "negative mass $1.4\cdot10^{-2}$ at $2048^2$
points (at $1024^2$ the Gaussian factor is still $0.05$ at the largest frequency)". Suggestion 1:
**safe, optional**: one sentence and an extension of the deposited script, quoting only the 0 → ¼ and
0 → 0.1 sub-steps. Remark E.5 is report D's block; not re-run here.

---

## 9. Proposition G.1: the range of b (report § 3.6; required change 9)

**Quote.** p. 94 (`appendix-linear-flow.tex:62`; blueprint annotation `05-smaller-groups.tex:1001`):
"Sα(I) rides the curves of B = diag(1, b) for 1 ≤ b ≤ 1 + α".

**Check.** (d + α)λmin(sym B) ≥ tr B at d = 2 is (2 + α)min(1, b) ≥ 1 + b, i.e. 1/(1+α) ≤ b ≤ 1 + α;
by Prop. 4.10 this is exactly when Sα(I) is B-self-decomposable. The printed sentence is true and
gives half the range.

**Verdict: PARTLY** (true, incomplete).

**Response: safe.** Both places: "for $1 \le b \le 1 + \alpha$" → "exactly for $1/(1+\alpha) \le b \le
1 + \alpha$ (Proposition 4.10)". The paper copy is prose after the shared statement; the blueprint copy
is in an annotation.

---

## 10. Proposition F.5: "its converse open" (report § 3.3; required change 10)

**Quote.** p. 93 (`appendix-smaller-groups.tex:329-330`): "Its converse, and the families off the
frame's shapes, … are part of problem 4"; p. 55, problem 4: "the converse of Proposition F.5(2)".

**Check.** The referee's computation holds: for D_s² ≤α D_{s′}², u = s′/s, B := diag(log u) ∈ Dα
(F.5(1)), and B-self-decomposability at t = 1 gives µ_{D_{s′}²} = µ_{D_s²} ∗ (D_{s′})∗ρ. So every law
of F.5(2) gives kernels with increments between the frame's shapes. The converse of F.5(2) in the
paper's sense is that every such law is the isotropic member of a family on PSD(d), which asks for the
extension off the frame's shapes; that is open. The paper's sentence does not equate the two, but
"its converse" is ambiguous.

**Verdict: PARTLY.**

**Response: safe** (paper-side prose and problem 4). "Its converse, and the families off the frame's
shapes" → "Whether every such law is the isotropic member of a family, which asks for an extension off
the frame's shapes, and those families"; problem 4, "the converse of Proposition F.5(2)" → "whether every
law of Proposition F.5(2) is the isotropic member of a family". Stating the sufficiency on the frame's
shapes as a fact is a new clause: **author**, not recommended (it says nothing about a family).

---

## 11. Proposition H.5(1): the reason g is nondecreasing (suggestion 6)

**Check.** The sketch's reason (p. 99, `appendix-similarity-loewner.tex:328`) is the proof of record's:
g(a²u) = ∫(1 − cos⟨√u e, y⟩) k(|y|/a)|y|^{−d} dy is nondecreasing in a because k is nonincreasing
(`05-smaller-groups.tex:1613-1614`). **REFUTED** as a defect. **Response: decline.**

---

## 12. Missing prior work in Appendix G (report § 6; suggestion 5)

**Check.** Sato–Yamazato 1984 is held and read (`READING-sato1984operator.md`); its abstract, p. 73,
characterizes Urbanik's operator-self-decomposable laws as the limit laws of Ornstein–Uhlenbeck-type
processes (`library search sato1984operator "limit distribution"`). The blueprint cites it
(`05-smaller-groups.tex:995`); `paper/references.bib` does not. Jurek–Vervaat 1983 is held and read, but
it is the *scalar* case (self-decomposable laws in a Banach space, `READING-jurek1983integral-driving-
process.md`); the operator form ∫₀^∞ e^{−tQ}dY is Jurek 1982, p. 385, held and read
(`READING-jurek1982integral.md`). Biermé–Meerschaert–Scheffler 2007 is not held (`library search
--corpus "operator scaling random fields"`: nothing). The attribution to Jurek–Vervaat is **wrong** for
the operator case.

**Verdict: PARTLY.**

**Response: author** (a prior-art citation, as the open decisions of `PRIOR-ART-positioning.md` § 7
are). Recommended: one sentence after G.1 citing Sato–Yamazato 1984 (p. 73) and Jurek 1982 (p. 385) for
the integral representation, both read; not Jurek–Vervaat; Biermé et al. only after acquisition and a
reading note.

---

## 13. Structure and length (report § 7; suggestions 9, 10; § 3.4)

**Claims.**
- "Appendix D … three lines of content": **refuted**. D.1 has three clauses, eight `\lean`
  declarations, a 2380-character sketch and a 6646-character proof of record.
- Appendices G, H.2, H.4(4)–(5), H.7, H.8 to a supplement; F.3–F.5 condensed into one proposition;
  Appendix D to a remark: reverse `adr/0006` item 5 and D3 (no supplement, no merging).
- H.1(3), 4.24 and F.2 stated in § 4.9: 4.24 already is (D8); F.2 and H.1 in § 4.9 is what D9 declined.
- Table 2's (similarities, Loewner) cell cut: round 2 declined a condensed cell
  (`VERIFY-round2-structure-paper.md` § 4.3); this one drops H.8, H.7(3) and the shape-carrying point of
  H.1(3).
- § 5's first paragraph dropped: D3 shortened § 5's summary already; the paragraph is 11 lines.
- "Rank-one limit" unnamed in § 4.9 (p. 52): **confirmed**.

**Response.** **author** for the moves and merges, recommended **decline** (each reverses a decision
taken with the measurements); **safe** for the name: § 4.9 (p. 52), "the Lévy measures of the part at
the thinnest apertures" → "the rank-one limit of the Lévy measures (Proposition H.4(4))".

---

## 14. Claims checked that need no change

§ 2: H.1(3)'s family and its κ condition; "the rigidity needs both"; F.2 and F.4(3); Table 3's frame and
flow rows. § 3.2: 4.24(1)–(3) (including GL(d)-covariance failing at A = (I + e₁e₁ᵀ)^{1/2}). § 3.5: F.1–F.5,
including F.5(4)(a)'s determinant 4(1+α) − (2+α)²r². § 3.7: H.1, H.2 (c₁ ≤ h₀ holds as the report says),
H.4, H.6, H.9. § 3.8: the twenty match the sketch markers; the axiom printout matches. § 3.9: consistent.
All agree with the build and the blueprint.

---

## Summary

| # | Finding (report) | Verdict | Class | Response |
|---|---|---|---|---|
| 1 | (i) Thm 3.5 makes R(λ) ≥ λ^α necessary for (GL(d), ≤α) and the cone orders (§ 3.1, RC 1, S 2, S 8) | CONFIRMED: complete within the profile class for right-continuous k, Gaussian part free; the whole cell needs A2 (polar criterion), not among C1–C4; cones depend only on β(C); single-step converse stays open | author | (a) add the iff to 4.20(2), 4.21(3)(c) and (2)(c) (≈ 6-line proof from 4.24(1), H.2(1), 4.14(4); Lean an assembly), rewrite p. 48, problems 1 and 3, Table 2, § 5; (b) + A2 for a complete cell; (c) "not stated here". Recommend (a), A2 to the author |
| 2 | (ii) H.8(3) sketch fails under ID increments with a Gaussian part (RC 2) | PARTLY: sketch only; the proof of record uses the non-Gaussian factor and is right | safe | one sentence in the sketch naming ρ; decline the replacement argument |
| 3 | H.7(3) sketch does not force k(r) = k(λr) (RC 3); H.7(2) no reason (S 7) | (3) REFUTED (the mass comparison is opposite to monotonicity); (2) CONFIRMED | safe | expand both sketches by a clause |
| 4 | (iii) twenty sketches: print or supplement (RC 5) | CONFIRMED (no proof in print; all twenty have complete, `\leanok` blueprint proofs) | author | keep D2 and repair §§ 2–3 (recommended); print eleven +7.4 pp.; all +13.6 pp.; supplement reverses D3 |
| 5 | line-paper statements in the formal development (RC 4, S 11) | PARTLY: consistent ([V, Prop 6.6], [V, Thm 7.3] proved in ScaleSpaceCore), not said | safe | one sentence in § 1.1 and Appendix I |
| 6 | "four times the eccentricity" (RC 6, S 3, S 4) | PARTLY: Table 2 already precise; whole exponent is bounded too (cond C ≤ ecc); § 5 vague | safe | § 5 names es of the non-Gaussian part; optional sentences after 4.24 and in § 4.9; cite H.1(3) on p. 5 |
| 7 | "price … is shape selection" (RC 7) | PARTLY: p. 51 right by § 4.1's definition; pp. 5, 54 drop it | safe | "shape selection that transforms with the image" on pp. 5, 54 |
| 8 | Remark H.3 (RC 8, S 1) | CONFIRMED, reproduced; the referee's calibration ray differs from the script's | safe | "spatial square"; quote 1.4·10⁻² at 2048²; sub-step sentence optional |
| 9 | G.1: 1 ≤ b ≤ 1 + α (RC 9) | PARTLY: true, half the range | safe | "exactly for 1/(1+α) ≤ b ≤ 1+α", paper and blueprint annotation |
| 10 | F.5: "its converse open" (RC 10) | PARTLY: the converse in the paper's sense needs the extension | safe | reword p. 93 and problem 4; the frame-shapes fact is author's, not recommended |
| 11 | H.5(1): reason for g nondecreasing (S 6) | REFUTED | decline | — |
| 12 | Appendix G citations (S 5) | PARTLY: Sato–Yamazato right; Jurek–Vervaat is the scalar case (operator: Jurek 1982); Biermé et al. not held | author | cite Sato–Yamazato p. 73 and Jurek 1982 p. 385 (recommended) |
| 13 | structure and length (§ 7, S 9, S 10, § 3.4) | Appendix D "three lines" REFUTED; moves reverse adr/0006, D3, D9; "rank-one limit" CONFIRMED | author / safe | decline the moves (recommended); name the rank-one limit in § 4.9 |
| 14 | the correctness checks of §§ 2–3 | CONFIRMED | — | none |
