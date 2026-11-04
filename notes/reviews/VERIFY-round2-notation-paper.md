# Verification of the external review, round 2: notation, and the mathematics of the proposed fixes

**What this is.** Article-kit `PROCESS.md` § 9 asks that every finding of an external review be
checked against the text, the blueprint and the sources before anything changes. This record checks
items 5, 6, 11, 12, 13, 14, 15 and 19 of `review-presentation-review-2-Gemini-4.0-Argon-High.md`
(twenty ranked changes): the notation, and the mathematics each proposed fix would put into the
paper. The other twelve items are verified in other records. Nothing but this file and the scripts
under `verify-round2-paper-scripts/` was written; no `.tex`, `.lean` or blueprint file changed.

## Inputs and conventions

**Inputs.** The build the reviewer read, `review-build-review-2.pdf` (108 pages, byte-identical to
`paper/main.pdf`; checked with `cmp`). Its printed page numbers equal its PDF page numbers; each page
was read with `pdftotext -f N -l N -layout`. Also read: `paper/*.tex` (the sources of that build);
`paper/main.aux` for statement numbers and pages; `blueprint/src/parts/*.tex`, the text of record;
`paper-iso/*.tex`, to see which shared nodes the released isotropic paper prints too. Sources read
at the page through the librarian (`library page`, `library search`): `fagerstrom2026isotropic` [16]
pp. 6, 15–16; `fagerstrom2026cone` [17] pp. 34–35; `fagerstrom2026spatial` [15] pp. 10, 32–33;
`sato1999levy` [54] pp. 95, 432.

**Scripts** (in `verify-round2-paper-scripts/`, each with its saved output):
`item11_matern_increment.py` (sympy, mpmath) and `items13_14_19_matrix_checks.py` (numpy).

**Verdicts.** CONFIRMED: the defect is real as stated. PARTLY: what holds is said, and what does
not. REFUTED: the paper is right, and the reason is given. Each proposed fix is judged separately:
*right*, *partly right* (corrected text given), or *wrong*.

**Classes.** *safe*: a wording, letter or pointer change a session may make under `adr/0003`;
where it touches a `% shared with blueprint` statement or a `% proof of` proof, it is made in the
blueprint first and re-transcribed (`adr/0004`, `linkage check --pin-shared` for a pinned node).
*author*: it changes a convention used across the paper, what is claimed, or chooses between
routes. *decline*: wrong, or against a rule (the verbatim restatement of a released module, the
programme's notation of Paper V, `CLAUDE.md` "An earlier module is cited as its released version").

---

## 5. The class $\mathcal A_d$ and the origin data (pp. 9, 11) — PARTLY; fix partly right (citation wrong); safe

**Quotes.** Both are in the build: the p. 9 sentence before Theorem 2.5, verbatim
(`02-line-papers.tex:204–206`), and the p. 11 sentence after Definition 2.8 that the fix would
replace ("An origin datum describes its law, …", `02-line-papers.tex:335`).

**The defect.** PARTLY.
- What holds: the paper never states the equivalence "$F \in \mathcal A_d$ iff $F(|\xi|) = F_d(\xi)$
  for an origin datum" as such, nor cites the statement that proves it.
- What does not: the link is stated in prose. P. 10 (`02-line-papers.tex:273–276`): "The origin
  data below describe the laws of the class $\mathcal A_d$ through their Lévy measures. The Lévy
  measure of a rotation-invariant self-decomposable law is described by one function of the
  radius, by the polar criterion of self-decomposability ([54], Thm. 15.10, p. 95)". The link to
  Proposition 4.13 is also made: p. 41 says its profile "is the polar profile of Definition 2.8
  divided by the area of the sphere, $k = k_d/|S^{d-1}|$", and p. 42 cites the polar criterion again
  for the laws of 4.13(1) (`05-orbits.tex:541`). So "the reader cannot connect Theorem 2.5 to
  Definition 2.8 or to Proposition 4.13" is overstated.

**The proposed text.** The equivalence is true. It is the released isotropic paper's
**Proposition 3.11** ("the polar form of $\mathcal A_d$", [16] pp. 15–16; blueprint node
`prop:isotropic-polar-reading`, `03-isotropic.tex:7688`). Clause (1) gives the equivalence, and it
says the datum is unique, "$k_d$ up to modification on a Lebesgue-null set". Clause (2) gives
admissibility with $a_{\mathrm V} = \tfrac12 a'$, $k = k_1$, and "So $\mathcal A_d$ is the set of $F$
for which $F(|\cdot|)$ is the exponent of an isotropic origin datum in dimension $d$". Sato's
Thm. 15.10 (p. 95) is the polar criterion. The rotation-invariant reading, with the surface measure
and a profile independent of the direction, is Sato's E 18.13 (p. 432). What the fix gets wrong:
- **The citation.** `[17, Prop. 4.9]` is the cone paper's "dimension filtration" ([17] p. 34): it
  defines $\mathcal A_d$ and proves nesting, the slice and the top. It is neither the polar
  criterion nor the equivalence, which [17] does not state. The citation is `[16, Prop. 3.11]`.
- **"For a unique isotropic origin datum".** Unique only with $k_d$ taken up to a Lebesgue-null
  set, since a nonincreasing $k_d$ is fixed only at its points of continuity.
- It drops the first sentence's content: the Gaussian coefficient $a$, and that the law is
  symmetric infinitely divisible. Those are what §4.6 reads.

**Response: safe** (paper prose after a shared definition; it adds a pointer to a released
statement and changes no claim). Keep the existing first sentence, and add after it:

> The data describe exactly the class $\mathcal A_d$: an $F$ lies in $\mathcal A_d$ if and only if
> $\xi \mapsto F(|\xi|)$ is the exponent $F_d$ of an isotropic origin datum in dimension $d$, and the
> datum is then unique, $k_d$ up to a Lebesgue-null set \prog{Iso}{Prop.~3.11}.

Restating Proposition 3.11 itself as a seventh shared statement in §2.3 would also be correct, but it
changes the list of §2.3. That is the author's call, and it is not needed, since no proof of this
paper cites it.

## 6. The letter $k$; $k_I$ against $k_{\mathrm I}$ (pp. 8, 10–11, 41–42, 100–101) — PARTLY; fix 1 right and safe, fix 2 decline

**Quotes.** Both are in the build: Definition 2.8 on p. 11 (`02-line-papers.tex:326–328`) and
Proposition H.8 on p. 100 (`appendix-similarity-loewner.tex:525–527`). H.8's sketch and H.9(2) are
on p. 101.

**Every use of $k_I$.**
- Italic $k_I$ (the polar profile of $\mu_I$'s datum): only in Appendix H, in the H.8 statement and
  sketch and in H.9(2) (`appendix-similarity-loewner.tex:526, 527, 559, 601`; pp. 100–101). The
  blueprint has it at `05-smaller-groups.tex:2057–2058, 2107–2117, 2195`.
- Upright $k_{\mathrm I}$ (the delay profile): only in §2.3, pp. 10–11 (`02-line-papers.tex:288–331`).

**Claim (a): $k_I$ collides with $k_{\mathrm I}$.** CONFIRMED, though mild. The two never share a
page (90 pages apart), and p. 8 declares the typefaces ("an upright subscript I … one of the
time-causal theory; the italic $I$ of $\mu_I$ is the identity matrix"). But the glyph pair is the
same at a glance, and H.8 cites Definition 2.8, where $k_{\mathrm I}$ appears.

**Claim (b): four meanings of $k$.** PARTLY. The paper's own list on p. 13
(`02-line-papers.tex:558–561`) already declares three of them, the folded profile, $k_d$ and the
profile $k = k_d/|S^{d-1}|$ of Proposition 4.13. It also gives the factor the review presents as a
finding: "At $d = 1$ the last is half the folded profile, which counts both directions". The
factor is right ($|S^0| = 2$; [16] Prop. 3.11(2) gives $k_1$ = folded profile). The fourth,
$k_{\mathrm I}$, is a different symbol. "Unnormalized profile" is the wrong word: $k$ is $k_d$
divided by $|S^{d-1}|$. The folded $k$ of (2.1) is never read after §2. `eq:admissible-line` is
referenced only at `02-line-papers.tex:204, 541, 558`. So it never meets the bare $k$ of §4.6 in a
statement.

**Fix 1** ($k_I \to k_d$ in H.8, its sketch and H.9(2)): **right**. $k_I$ is the polar profile of the
datum $(0, k_I)$ of $L_I$. The sketch's $L_{tI}(K_A(\varepsilon)) = \overline\sigma(A)\int_\varepsilon^1
k_I(rt^{-1/2})\,dr/r$ is (2.4) with that profile, and $c = k_d(0{+})$ is the $c$ of Lemma 2.9, which
the sketch uses. $k_d$ has no other meaning in Appendix H. **Safe**, blueprint first:
`prop:similarity-general-index-zero` (pinned `+255c352524b3`; statement and proof),
`prop:similarity-cascade-families` (pinned `+f33d542fd9b1`; clause (2)). Re-transcribe and
re-pin.

**Fix 2** (folded $k \to k_{\mathrm V}$): **decline**. $k$ for the folded profile is the
notation of both released papers: [15] p. 10 ("folded profile $k = 2h$ in (2.3)") and [16] p. 6
("$k$ the folded profile. A subscript V marks an object of the line"). The paper's §2.2 follows
them. Renaming it departs from the programme's notation (Paper V's; `CLAUDE.md`, "Notation") and
from the restated (2.1). It buys nothing, since the folded $k$ is not used after §2.

## 11. The Matérn failure across shapes, brought into §4.6 (pp. 45, 85) — PARTLY; fix right in substance, details corrected; safe

**Quotes.** The p. 45 paragraph is in the build verbatim (`05-orbits.tex:748–753`), and so is
Remark E.3 on p. 85 (`appendix-orbits.tex:175`).

**The defect.** PARTLY. The paragraph is a list of four pointers. But it states the mechanism in
words: the increment is "negative near the origin in the directions the step widens least, and its
negative mass diverges logarithmically". What it lacks is the formula. §4.6 already introduces
$\mathcal L_\Sigma = -\nabla\cdot\Sigma\nabla$ (p. 44), so the formula fits the section.

**The proposed text.** Every formula was checked against Remark E.3 and Proposition E.4 and computed
(`item11_matern_increment.py`, output saved):
- $(1+\langle\omega,\Sigma\omega\rangle)/(1+\langle\omega,\Sigma'\omega\rangle) =
  1 - \langle\omega,P\omega\rangle\widehat K_{\Sigma'}(\omega)$: an identity.
- $K_{\Sigma'}(x) = (\det\Sigma')^{-1/2}G(\Sigma'^{-1/2}x)$, with $G$ the Green's function of $1-\Delta$
  ($\widehat G = (1+|\omega|^2)^{-1}$ from the subordination integral of Remark E.3): right.
- Off the origin the density is $q = \nabla\cdot P\nabla K_{\Sigma'}$. With the paper's convention
  $\widehat\mu(\omega) = \int e^{i\langle\omega,x\rangle}\mu(dx)$, $\nabla\cdot P\nabla$ has symbol
  $-\langle\omega,P\omega\rangle$, so the increment is $\delta_0 + q$: right.
- The limit $(\det\Sigma')^{1/2}r^dq(\Sigma'^{1/2}r\hat y) \to \mathcal B_d(d\langle\hat y,P'\hat y\rangle
  - \tr P')$ with $\mathcal B_d = \tfrac12\pi^{-d/2}\Gamma(d/2)$ is E.4(2). It was checked three ways:
  from the Newtonian leading term for symbolic $d$, exactly at $d = 3$, and numerically at $d = 2$
  (error $1.5\cdot10^{-16}$). Also $\mathcal B_d = 1/|S^{d-1}|$, and E.4(4)'s
  $\mathcal B_2\Theta = (p_1-p_2)/\pi$ and $\varepsilon/(\pi(1+\varepsilon))$ hold.
- "Negative on an open cone": right, and the bracket has mean zero over the sphere. It needs $P'$
  not a multiple of $I$. That is equivalent to $\Sigma'$ not a multiple of $\Sigma$, since
  $P' = I - \Sigma'^{-1/2}\Sigma\Sigma'^{-1/2}$.

Details to correct:
1. The hypotheses: $d \ge 2$ and $P \in \PSD(d)\setminus\{0\}$, as in E.4.
2. "Around the least-widened direction" should read "around a least eigenvector of $P'$, in the
   coordinates $y = \Sigma'^{-1/2}x$".
3. "Integrating $r^{-d}$ over shells" is loose. The masses on $\{a < |\Sigma'^{-1/2}x| < 1\}$ are
   $\mathcal B_d\Theta\log(1/a) + o(\log(1/a))$ with the $\Theta$ of E.4(3), and they diverge
   exactly when $\Theta > 0$.
4. The conclusion (no finite signed increment) should be stated, since it is the point.
5. Register (`WRITING.md` § 2): seven long sentences, most over one main and one subordinate
   clause. It also restates Remark E.3 nearly in full.

**Response: safe** (paper prose, no shared statement). A shorter version:

> \paragraph{The size of the failure.} For the \Matern{} orbit of index $1$ and a step
> $\Sigma \to \Sigma' = \Sigma + P$, $0 \ne P \in \PSD(d)$, $d \ge 2$, the would-be increment has the
> transform $1 - \langle\omega,P\omega\rangle\,\widehat\mu_{\Sigma'}(\omega)$. Off the origin it is the
> function $q = \nabla\cdot P\nabla K_{\Sigma'}$, where the density $K_{\Sigma'}$ of $\mu_{\Sigma'}$ is
> a linear image of the Green's function of $1 - \Delta$. Near the origin, in the coordinates
> $y = \Sigma'^{-1/2}x$ and with $P' := \Sigma'^{-1/2}P\Sigma'^{-1/2}$, $q$ is $(\det\Sigma')^{-1/2}
> |S^{d-1}|^{-1}|y|^{-d}(d\langle\hat y,P'\hat y\rangle - \tr P')$ to leading order. Unless $\Sigma'$ is
> a multiple of $\Sigma$, the bracket is negative around a least eigenvector of $P'$. The negative
> mass on $\{a < |y| < 1\}$ then grows like $\log(1/a)$, so the increment is not even a finite signed
> measure (Proposition~E.2 with Remark~E.3, and Proposition~E.4, with a computation on a grid in
> Remark~E.5; all in Appendix~E.2).

The labels go through `\ref` as in the current paragraph.

## 12. $\mathcal K_\alpha$ against $K_\alpha$; the four symbols for the stable order (pp. 14, 20, 38–48) — (a) CONFIRMED, (b) REFUTED; fix 1 author, fix 2 decline

**Quote.** The p. 14 sentence is in the build verbatim (`02-line-papers.tex:574–577`).

**Claim (a): $\mathcal K_\alpha$ against $K_\alpha$.** CONFIRMED. This is an owed change that is
already open: `records/affine/GATE-affine.md:94` ("$K_\alpha$ and $\mathcal K_\alpha$ nearly
identical: rename one (§2.5 sets them apart meanwhile)"; flags App. A 13, whole-paper 18, draft 5).
Uses:
- $\mathcal K_\alpha$ (step cone, $\subseteq \PD(d)$): 7 source lines. They are Theorem 3.5(3)(c)
  (p. 20, `04-classical.tex:400–411`, shared `thm:cascade-infinitely-divisible+de46b7d00859`), its
  proof (`appendix-classical.tex:657–658`), Table 1 and the p. 14 sentence.
- $K_\alpha$ (exponent cone, $\subseteq \gl(d)$): 20 source lines in 7 files. They are Proposition
  4.10 and its prose (`05-orbits.tex:356–422`), Proposition 4.12(2) (`05-orbits.tex:467–471`), §4.9
  (`05-smaller-groups.tex:78`), Table 2 (`05-table.tex:40, 99`), App. B (`appendix-proofs.tex:152–157`),
  Prop. F.5 (`appendix-smaller-groups.tex:281, 292`) and App. C (`appendix-wedge-axis.tex:399`).
  The blueprint has 26 lines in 5 parts.
- The two meet in Table 1, on p. 14, and in Proposition 4.12, whose clause (2) has $K_\alpha$ beside
  $\exp C_\alpha$, which is $\mathcal K_\alpha$.

**Claim (b): four symbols cause friction.** REFUTED. They are two pairs, and each pair is forced by
the order of proof:
- $\preceq_\alpha$ is defined by its step condition in Proposition 4.7(2) (p. 38), before $C_\alpha$
  exists. Proposition 4.12(1) (p. 41) proves it equals $\preceq_{C_\alpha}$.
- $\le_\alpha$ on $\PSD(d)$ is defined in Proposition 4.20(1) (p. 45; `05-orbits.tex:787–790`).
- The preamble of Theorem 4.21 already says "on $\PSD(d)$ the order $\preceq^+_{C_\alpha}$ is the
  $\le_\alpha$ of Proposition 4.20(1)" (p. 47, `05-wedge-axis.tex:42–44`), and Table 1 lists
  "$\le_\alpha = \preceq^+_{C_\alpha}$".
- "One page after" is two pages (p. 45 to p. 47).

**Fix 1** (rename the exponent cone): **author**, since it is a convention across the paper and the
blueprint and touches shared statements (`prop:stable-exponent-cone+728b3876351b`,
`prop:stable-order-generated`, `prop:diagonal-stable-order-families`, Table 2). The options:
- (a) The exponent cone to $\mathfrak k_\alpha$: about 20 paper lines in 7 files and 26 blueprint
  lines, with re-pins.
- (b) The step cone to another letter: 7 paper lines in 3 files and one shared statement. But
  $\mathcal K_\alpha$ is an instance of Proposition 4.2's step sets $\mathcal K$, $\le_{\mathcal K}$
  (Table 1), and renaming it breaks that family.
- (c) Keep both, relying on the p. 14 sentence.

**Recommendation: (a), with $\mathfrak k_\alpha$**, not $E_\alpha$. A fraktur letter marks a subset of
$\gl(d)$, as $\gl(d)$ itself does. $\mathfrak k$ is unused in the paper; the only fraktur in use is
$\mathfrak F_\alpha$, a set of laws. $E_\alpha$ is worse: $E_1$ and $E_c$ are eigenspaces in the proof
of Proposition 4.22 (`05-shape-adapted.tex:71`), and $E_a$ is the shell of Proposition E.4. The one
cost: in Lie theory $\mathfrak k$ names the compact subalgebra, here $\mathfrak{so}(d)$, which
$K_\alpha$ contains. The paper never writes it, so this is acceptable.

**Fix 2** ($\le_\alpha$ in Theorem 4.21(3)): **decline as given**. $\le_\alpha$ exists only for
$0 < \alpha < 2$ (Proposition 4.20 rests on Proposition 4.7). Theorem 4.21(3) runs over
$0 \le \alpha \le \infty$, including $2 \le \alpha < \infty$, where no $\le_\alpha$ is defined. Writing
it there needs a new definition $\le_\alpha := \preceq^+_{C_\alpha}$ for every $\alpha$, which is an
author's convention change. Clause (2) needs $\preceq^+_C$ for a general $C$ in any case, and the
identification the fix asks for is already in the preamble.

## 13. The two scale conventions (pp. 9, 18, 28, 48–50) — PARTLY; fix right in substance, details corrected; safe

**Quotes.** Both are in the build verbatim: p. 18 (`04-classical.tex:311–324`) and p. 50.

**The defect.** PARTLY.
- What holds: no single sentence of this paper says that the volume scale $t(\Sigma)$ of Lemma 4.1
  is a length while the ray parameter is a squared length, with $t(vI) = \sqrt v$.
- What does not:
  - "Cites … instead of writing out the one-line relation" is refuted: p. 18 writes $\varphi = \chi^2$
    and says in words what each coordinate is.
  - Proposition A.3(1) gives the slice the dilation action $S_\lambda s = \lambda^2 s$ (p. 59).
  - P. 48 and p. 50 say that $w$ and $s$ are variances ("squared lengths rather than volume
    scales"), and p. 14 says "The prose writes $v$ and $w$ for variances".
  - The citations are right. [15] Rem. 6.7 (pp. 32–33) is the units statement itself ("$t$ in this
    article is a length, the standard deviation of the Gaussian member … the variance gauge
    $\tilde t^2$"), and [15] Prop. 6.6 is the canonical gauge.

**The proposed text.** Checked against Proposition A.3 and computed
(`items13_14_19_matrix_checks.py`):
- $A\cdot\Sigma = \lambda^2\Sigma$ for $A = \lambda I$: right.
- $t(\lambda^2\Sigma) = \lambda t(\Sigma)$ and $t(sI) = \sqrt s$: right.
- The formula $\widehat\nu_{sI,s'I}(\omega) = \exp[-(F(\sqrt{s'}|\omega|) - F(\sqrt s|\omega|))]$:
  right. It follows from Theorem 2.5's (2.3) and A.3(2), $\mu_{s,t} = \nu_{\varphi(s)I,\varphi(t)I}$
  with $\chi(\varphi^{-1}(v)) = \sqrt v$, for the pair $(\chi, F)$ of Theorem 2.5.
- Also $t(\varphi(t)I) = \chi(t)$: the volume scale of the slice is the canonical-gauge scale.

Details to correct:
1. "The canonical gauge $\chi(t) = t$ of Theorem 2.5": Theorem 2.5 names no canonical gauge. It is
   named after Theorem 2.3 (p. 9) and is [15] Prop. 6.6.
2. The fix drops the two correct citations.
3. It names the variance $s, s'$, where p. 14's convention is $v, w$.

**Response: safe** (paper prose). Keep the p. 18 sentence and add after it:

> A dilation by $\lambda$ acts on the parameter by $\Sigma \mapsto \lambda^2\Sigma$. So $v$ in $vI$ is a
> squared length, while the volume scale $t(\Sigma) := (\det\Sigma)^{1/(2d)}$ of
> Lemma~\ref{lem:loewner-scale-shape} is a length, with $t(vI) = \sqrt v$. In the variance gauge the
> slice has $\widehat\mu_{vI,wI}(\omega) = \exp[-(F(\sqrt w\,|\omega|) - F(\sqrt v\,|\omega|))]$ for
> $0 \le v \le w$, with $(\chi, F)$ as in Theorem~\ref{thm:isotropic-classification}, and the volume
> scale of $\varphi(t)I$ is $\chi(t)$.

## 14. The opening of §3.2 (p. 19) — PARTLY; fix mathematically right for $\GL(d)$, wrong in scope; safe (a smaller change)

**Quote.** In the build verbatim (`04-classical.tex:327–335`).

**The defect.** PARTLY.
- What holds: "and that this is itself an axiom" is opaque where it stands. Its meaning, Lemma
  A.5(3)'s title "The isotropic member is the axiom of the parameter space $\PD(d)$", arrives only in
  the next paragraph.
- What does not: "full" and "stabilizer" are defined where used (p. 19, "A law that no proper
  subspace carries, a full law"; "The stabilizer of a law is the set of linear maps that leave it
  unchanged"). The polar-decomposition point is already made ("$A$ and $AQ$ give the same matrix
  for every orthogonal $Q$, so that $\PD(d) = \GL(d)/\Orth(d)$").

**The proposed text.**
- The polar decomposition $A = (AA^{\tp})^{1/2}Q$: right (checked numerically).
- $\mu_{AA^{\tp}} = A_*\mu_I = (\Sigma^{1/2})_*Q_*\mu_I$: right.
- "Must be invariant … for this kernel to be well-defined": the family is indexed by $\Sigma$ by
  definition, so this is not a well-definedness condition. (K3) at $A = Q$ forces
  $Q_*\mu_I = \mu_{QQ^{\tp}} = \mu_I$ (Lemma A.5(5)).
- "Indexing a $\GL(d)$-covariant orbit of non-degenerate kernels by $\PD(d)$ is equivalent to …
  an isotropic member at $\Sigma = I$": right. It is Lemma A.5(3), (a)⇔(c), for a full $\mu_0$, and
  any covariant map puts its rotation-invariant member at $I$. "Non-degenerate" should be "full",
  A.5's word. A rotation-invariant member $\ne \delta_0$ is full by A.5(2), so nothing breaks.

What the fix loses:
1. Why the parameter set is the closed $\PSD(d)$: the origin and the singular matrices, where a step
   can be rank-deficient. That is the theme of §3.4.
2. The scheme's generality. The paragraph is stated for $G = \GL(d)$, while §3.2 serves every $G$:
   for $G \supseteq \Orth(d)$ smaller than $\GL(d)$ a kernel fixes its parameter only on
   $\{AA^{\tp} : A \in G\}$, and without $\Orth(d) \subseteq G$ there is no isotropic member (A.5(5)).
   The second paragraph would then repeat it.
3. It opens with a rhetorical question.

**Response: safe** (paper prose). Replace only the opaque sentence:

> This subsection says why the positive definite matrices are the right index for the kernels: an
> orbit of laws can be indexed covariantly by $\PD(d)$ exactly when it has a rotation-invariant
> member, and when $G$ contains $\Orth(d)$ the axioms supply one, the kernel $\mu_I$.

Optionally add "(the polar decomposition $A = (AA^{\tp})^{1/2}Q$)" after "for every orthogonal $Q$".

## 15. The frequency letter, and "kernel" (pp. 7, 16, 49) — (1) PARTLY, (2) REFUTED as a defect, (3) CONFIRMED; classes split

**Quotes.** P. 7 is in the build verbatim. On p. 49 the build has "Its kernel is the eigenspace of
$M$ for the eigenvalue 1" (`05-shape-adapted.tex:38`).

**Claim (1): three frequency letters.** PARTLY.
- §2.3's $\xi$ and C2's $z$ are in statements that the released isotropic paper prints too, and
  they are verbatim from blueprint nodes shared with it: `def:isotropic-kernel-family`,
  `thm:isotropic-classification`, `def:isotropic-origin-datum`, `lem:radial-marginal`,
  `lem:isotropic-exponent-log` (`paper-iso/03-isotropic.tex:203, 338, 381, 563`,
  `paper-iso/appendix-isotropic.tex:496`), and `thm:cited-A3` (`paper-iso/supp-cited-facts.tex:52`,
  Sato's letters). Changing them breaks the restatement of a released module. **Decline** there.
- The defect that is real is that p. 7's own rule ("From §3 on, $\omega$ is the frequency on
  $\RR^d$") is broken six times:
  - p. 22: Lemma 3.8, a shared statement (`lem:charfn-one-on-subspace`, `04-classical.tex:516–526`);
  - p. 64: its proof (`appendix-classical.tex:680`);
  - p. 60: proof of Prop. A.3 (`appendix-classical.tex:433`);
  - p. 67: proof of record of Prop. 4.15 (`appendix-proofs.tex:214–262`), where $\xi$ is a second
    frequency beside a fixed $\omega$;
  - p. 75: proof of Prop. 3.4(1) (`appendix-wedge-axis.tex:430–449`), where $\xi$, $z$ and $z_0$
    are all frequencies in one argument and $\omega$ follows in clause (2);
  - p. 79: proof of record of Prop. 4.11(1) (`appendix-wedge-axis.tex:740`).
- The review's "pp. 60, 63 and 75 mix $\xi$, $\omega$ and $z$": p. 75 is confirmed; p. 60 has $\xi$
  alone, and p. 63 has none.
- **Safe**: write $\omega$ (and $\omega_0$ for $z_0$) on pp. 22, 60, 64, 75 and 79. Keep $\xi$ on
  p. 67 as the second frequency, and amend p. 7 to "… and $\xi$ for a second frequency where a proof
  needs two". Blueprint first for Lemma 3.8 and the two proofs of record.

**Claim (2): "kernel from scale zero", "aperture kernel".** The count holds: 70 in the paper sources
and 76 in the PDF text, so "over 60" is right. But the proposal is **declined**:
- "Kernel from scale zero" is the programme's term. The released isotropic paper uses it 26 times,
  and it is inside the restated Theorem 2.5, a verbatim shared statement.
- The blueprint has it 92 times, and Table 1 defines "kernel of a pair; kernel from scale zero".
- "Aperture" already names the parameter $\Sigma$ (Table 1, "aperture parameters").

One real inconsistency is small: p. 7 restricts "kernel" to "a law in its role as an aperture",
while Definition 3.1(2) calls the stages $\mu_{\Sigma,\Sigma'}$ kernels. **Safe**: on p. 7, "for a law
in its role as an aperture or as a stage".

**Claim (3): "kernel" for $\ker P$.** CONFIRMED, but three occurrences, not four: clause (1) and the
proof twice (`05-shape-adapted.tex:38, 71, 79`; p. 49). Clause (3) of the same statement says
"cascade family of kernels". Elsewhere the paper writes "the null space $\ker P$"
(`04-classical.tex:447, 465, 505`). **Safe**, blueprint first (`prop:shape-adapted-apertures`,
`05-shape-adapted.tex:34, 79, 87`, statement and proof of record): "Its null space $\ker P$ is the
eigenspace …", "the null space $\ker P$ is …", "minus the dimension of its null space".

## 19. Motivating causal curves and majorization in §4.4 (pp. 31–34) — PARTLY; fix right in its claims, incomplete on majorization, misstates the definition; safe

**Quotes.** Both are in the build (p. 32 for both; the first is on pp. 30–31).

**The defect.** PARTLY.
- What holds: the four sentences on p. 32 are compressed, and the one-step test $\log M \in C$ is not
  stated before Theorem 4.3.
- What does not:
  - The paper does say why majorization is needed, after the theorem (p. 34): "Clause (3) of
    Proposition 4.2 is the reason majorization is the tool: the spectrum of a composite is not a
    function of the two spectra, but majorization bounds it uniformly over the rotation between
    the eigenframes".
  - Proposition 4.2(3) gives the example: $\mathrm{diag}(4,1)$ followed by $\mathrm{diag}(4,1)$ or by
    $\mathrm{diag}(1,4)$ gives $\mathrm{diag}(16,1)$ or $4I$ (checked).
  - The curves are the content of "orders generated by cone fields", and p. 31 motivates them by the
    allowed velocities.

**What Theorem 4.3(1) says.** The review is right: $\Sigma \preceq_C \Sigma'$ if and only if
$M = \Sigma^{-1/2}\Sigma'\Sigma^{-1/2} \in \exp C$ (p. 34). That is $\log M \in C$, since $\exp$ is a
bijection of $\Sym(d)$ onto $\PD(d)$.

**The role of majorization.** The review is right but incomplete. Lemma C.1(2), the log-majorization
from C4 (checked over 2000 random pairs), does two things:
- it gives the transitivity of $\le_{\exp C}$ through C.1(5) and Proposition 4.2(3);
- it gives the converse "causal curves end in the order", through the superadditivity of the
  functionals $F_w$ (proof of Theorem 4.3, p. 72).

Both also need C.1(3)–(4): an invariant cone is read through a permutation-symmetric cone $D$ of
eigenvalues, which is closed under majorization (Davis). The "if" direction needs no majorization:
the geodesic $\Sigma^{1/2}M^t\Sigma^{1/2}$ has relative velocity orthogonally conjugate to $\log M$
(checked). The claim $\log(M^{1/2}NM^{1/2}) \ne \log M + \log N$ for non-commuting $M, N$ is true:
equality would give $\tr e^{X+Y} = \tr e^Xe^Y$, the equality case of Golden–Thompson, which forces
$XY = YX$ (checked numerically).

**What the fix gets wrong.**
- "A single step $\Sigma \preceq_C \Sigma'$ has the elementary algebraic test" states Theorem
  4.3(1)'s conclusion as if it were the definition. $\preceq_C$ is defined by curves.
- It omits C.1(3)–(4).
- It duplicates the p. 34 paragraph.

**Response: safe** (paper prose; `05-wedges.tex`). Replace the four sentences with:

> An order is described by its set of relative steps $M = \Sigma^{-1/2}\Sigma'\Sigma^{-1/2}$
> (Proposition~4.2), and a cone $C$ of symmetric matrices plays the part of the allowed velocities.
> A single step is tested by its logarithm: Theorem~4.3(1) shows that a curve of the cone field
> joins $\Sigma$ to $\Sigma'$ exactly when $\log M \in C$. Steps do not compose by multiplication, and
> $\log(M^{1/2}NM^{1/2}) \ne \log M + \log N$ when $M$ and $N$ do not commute. So it is not obvious
> that the test is transitive. A comparison of spectra by partial sums, majorization, bounds the
> spectrum of the composite whatever the relative position of the eigenframes, with one cited
> inequality (C4, Theorem~2.13), and gives both the transitivity and that a curve of the cone field
> ends at a step in $\exp C$.

The p. 34 paragraph then needs no change.

---

## Summary

| Item | Claim | Verdict | Fix | Class | Response |
|---|---|---|---|---|---|
| 5 | $\mathcal A_d$ = origin data unstated | PARTLY (stated in prose, p. 10; Prop 4.13 linked, p. 41) | partly right: wrong citation ([17, Prop. 4.9] → [16, Prop. 3.11]); uniqueness up to null sets | safe | one sentence after Def. 2.8 citing [16, Prop. 3.11] |
| 6 | $k_I$ vs $k_{\mathrm I}$ | CONFIRMED (mild; declared p. 8) | right | safe, via blueprint (2 pinned nodes) | $k_I \to k_d$ in H.8, its proof, H.9(2) |
| 6 | four meanings of $k$; rename folded $k$ to $k_{\mathrm V}$ | PARTLY (p. 13 already declares them and the factor ½) | decline | decline | $k$ is both released papers' folded profile; unused after §2 |
| 11 | §4.6 paragraph only points to E.2 | PARTLY (mechanism in words; formula missing) | right in substance (all formulas check), details loose | safe | shorter paragraph given; hypotheses $d \ge 2$, $P \ne 0$; $\mathcal B_d = 1/\lvert S^{d-1}\rvert$ |
| 12 | $\mathcal K_\alpha$ vs $K_\alpha$ | CONFIRMED (owed, GATE-affine.md:94) | rename | author | recommend exponent cone → $\mathfrak k_\alpha$ (~20 paper + 26 blueprint lines) |
| 12 | four order symbols; $\le_\alpha$ in Thm 4.21(3) | REFUTED (two forced pairs; identified in Thm 4.21's preamble) | wrong ($\le_\alpha$ undefined for $2 \le \alpha < \infty$) | decline | none |
| 13 | length vs variance scale unreconciled | PARTLY (stated p. 18, A.3(1), p. 48, p. 50; [15] Rem. 6.7 right) | right in substance; misnames the gauge's source, drops citations, reuses $s$ | safe | one sentence after p. 18's, with $v, w$ and $t(vI) = \sqrt v$ |
| 14 | §3.2 opening opaque | PARTLY ("itself an axiom" opaque; rest defined in place) | right for $\GL(d)$; loses PSD/rank-deficiency and $G \ne \GL(d)$ | safe | replace the one sentence |
| 15 | $\xi$, $\omega$, $z$ | PARTLY (§2.3 and C2 inherited: decline; p. 7's rule broken 6 times in §§3–4/apps) | partly right | safe for §§3–4 and apps (blueprint for Lemma 3.8 and 2 proofs of record); decline for §2.3/C2 | $\omega$ on pp. 22, 60, 64, 75, 79; p. 7 amended |
| 15 | "kernel from scale zero" → "aperture kernel" | REFUTED as a defect (programme's term, in a restated statement) | decline | decline | only p. 7's "as an aperture" → "as an aperture or as a stage" (safe) |
| 15 | "kernel" for $\ker P$ in Prop 4.22 | CONFIRMED (3 occurrences, not 4) | right | safe, via blueprint | "null space $\ker P$" |
| 19 | §4.4 does not motivate curves/majorization | PARTLY (p. 34 and Prop 4.2(3) do, after the statement) | claims right; majorization role incomplete; definition misstated | safe | four-sentence replacement given |

**For the author:** item 12, which cone to rename and to which letter (recommendation:
$K_\alpha \to \mathfrak k_\alpha$). Item 5's optional restatement of [16, Prop. 3.11] as a shared
statement in §2.3 (recommendation: a sentence only).
