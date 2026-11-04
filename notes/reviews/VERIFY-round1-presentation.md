# Verification of the presentation review, round 1 (the isotropic paper, `iso-review-1`)

*Q-0423, 2026-10-12. Article-kit `docs/PROCESS.md` § 9: every finding of an external review is
verified against the text before anything changes. This record verifies the twenty items of
`review-presentation-iso-review-1-GPT-6.1-Sol-Ultra.md`. It changes no `.tex` file. The content
review of the same build (`review-content-iso-review-1-GPT-6.1-Sol-Ultra.md`) is verified by another
agent, and this record only notes where the two reviews raise the same point.*

## What was read, and the conventions of this record

- **The text.** `paper-iso/*.tex` at the branch `queue/q-0423`. `git diff iso-review-1 HEAD -- paper-iso`
  is empty, so the sources are those of the frozen build. Page numbers are the printed pages of
  `review-build-iso-review-1.pdf`, which are also its PDF page numbers (checked on pp. 1, 2, 5, 21,
  30, 47, 58, 61). Each quotation was located with `pdftotext` and in the source, and is given as
  file:line. Pages 7, 14, 21 and 28 were also read as page images, and the two PNG figures as images.
- **The standard.** Article-kit `docs/WRITING.md` and `docs/PUBLICATION-TEMPLATE.md` § B.
- **The author's decisions.** `records/affine/REVIEW-author-paper-iso.md`. Decisions of the
  dispatching session are in `records/affine/REPOSITIONING-paper-iso.md`. The notation changes
  already owed at the blueprint are in `records/affine/GATE-paper-iso.md`.
- **The page budget.** The main text is 29.96 pages of 30
  (`records/affine/measure-section-pages-q0417-iso-output.txt`). A page holds about 51 lines of
  body text (A4, one-inch margins, 11 pt), so the margin is 2 lines. Every cost below is an
  estimate in printed lines of the main text. It has to be measured by a build before a freeze.
  The appendices and the back matter are outside the budget.
- **Shared text.** A statement under a `% shared with blueprint` marker, and a proof of record, is
  changed at the blueprint and mirrored. The affine paper of this repository prints four statements
  of this paper: `def:isotropic-kernel-family`, `thm:isotropic-classification`,
  `def:isotropic-origin-datum` and `lem:isotropic-exponent-log` (`paper/02-line-papers.tex:159`,
  `240`, `273`, `327`). The Lean development uses `OriginDatum` in 29 files.
- **Dispositions.** ACCEPT, ACCEPT IN PART, DECLINE, AUTHOR.

The removals that pay for the additions are named once here and cited by letter in the items.

| | removal | lines | needs |
|---|---|---|---|
| Ra | The lead of § 2.7 lists the seven letters in a sentence of seven lines (`02-line-papers.tex:545-553`), and the table then names each in its row. Shorten to "Seven letters keep a second role inside a statement, and the table names each: $c$, $\tau$, $\lambda$, $t$, $a$, $x$ and $s$." | −4 | nothing |
| Rb | § 3.4, opening: the sentence on what the cone paper proved and did not claim (`03-isotropic.tex:1238-1241`). It stands with the same anchors in § 1 (`01-introduction.tex:313-318`, contributions 2 and 3) and, for the first half, in § 2.3 (`02-line-papers.tex:310-312`). Keep a clause: "the first two steps are the cone paper's (§ 2.3)". | −2 | nothing |
| Rc | § 1.1, "Where to look" (`01-introduction.tex:565-567`): one sentence, "The inventory is Appendix B." The caption of Table 1 and the plan of § 1 already name the appendix. | −2.5 | nothing |
| Rd | After Proposition 3.15 (`03-isotropic.tex:1062-1065`): drop "the density is $|x|^{c-d}$ times a slowly varying factor, which comes from the transform", once item 7 has said it in the opening. | −1.5 | item 7 |
| Re | § 1 (`01-introduction.tex:237-238`): drop "named after the entire cosine integral $\Cin$ that gives their exponents". Proposition 2.7 defines $\Cin$ where it is used. | −1 | nothing |
| Rf | § 4, second paragraph (`04-conclusion.tex:114-125`), about ten lines: the two tiers of what is claimed, said a fourth time. Compress to two sentences that point to the contributions of § 1. | −6 | the dispatching session, see below |
| Rg | Table 3 with its anchors moved to an appendix table (item 8). | −12 to −16 | a decision, with the content review |
| Rh | The blueprint notation batch (item 9): the rows of Table 2 lose their second roles. | −4 to −6 | the blueprint |

Rf reverses a decision of the dispatching session, "the same items in four places" (the abstract, the
contributions of § 1, the opening of § 3.3 and § 4; `REPOSITIONING-paper-iso.md` § 16.1). The content
review asks for the same cut (its § 7 and suggestion 6: the claims are repeated). The alternative
with the same origin is the fourth paragraph of the opening of § 3.3 (`03-isotropic.tex:808-812`),
about −4 lines.

---

## 1. Explain why a scale-space researcher should relax the semigroup assumption (pp. 1, 4)

**Facts.**
- The quotation "weakens this one axiom." is on p. 1 (`01-introduction.tex:134`). Right.
- "The reader learns what was relaxed before learning what that relaxation permits." Right. What the
  relaxation permits is said in two later places. The third paragraph of § 1 (p. 2,
  `01-introduction.tex:158-169`) lists the Gaussian, the stable laws and the laws with transform
  $(1+\omega^2/2)^{-\gamma}$ as "these laws", without saying which of them a semigroup already gives.
  "Scale-space neighbours" (p. 4, `01-introduction.tex:323-339`) says it outright: with a semigroup
  the answer is the Gaussian or the stable kernels, and here the Matérn kernels are among the
  families.
- "The opening presents this as a development in the author's series." Right for the first
  paragraph, which names the line paper, the cone paper and the time-causal paper before any
  consequence.
- The second half of the fix, "identify the two design questions", describes something the text
  has: the three questions of p. 2 (`01-introduction.tex:171-189`).

**Judgement.** A real obstacle, and the fix is one sentence at the place where the relaxation is
introduced. The claim about the semigroup has to stay tied to the axioms of the cited papers. The
content review (§ 6, "Other positioning") asks that these comparisons are not read as blanket
uniqueness statements. No statement is touched and no figure is needed.

**Disposition: ACCEPT** (the first half; the second half is in the text).
Replace the first two sentences of the third paragraph (`01-introduction.tex:158-161`) by:

> This is what the weaker axiom buys. With a semigroup in the scale, the scale-space literature
> arrives at the Gaussian and at the symmetric stable laws, with transforms $e^{-|\omega|^p}$,
> $0 < p \le 2$ (\sscite{sato1999levy}, Thm.~14.14, p.~86; see "Scale-space neighbours" below). With
> a hemigroup every symmetric self-decomposable law gives a family. Among those added are the laws
> with transform $(1 + \omega^2/2)^{-\gamma}$, $\gamma > 0$, the symmetric variance-gamma laws
> (\sscite{fischer2025variance}, (24), p.~241).

Cost: +1.5 lines, paid by Ra. The new sentence restates a result, so the scope audit compares it
with "Scale-space neighbours" before the next freeze (`WRITING.md` § 5).

## 2. Bring the substantive scope limits into the first three pages (pp. 5, 30)

**Facts.**
- The quotation "What the paper leaves open or does not treat is listed in §4.1." is on p. 5
  (`01-introduction.tex:393-394`). Right.
- "This postpones information needed to interpret the title and the opening claims." Right in part.
  Three of the limits are on the first five pages. "From scale zero" and "no Gaussian part" are in
  the abstract (`main.tex:161-163`), in the second answer (p. 2, `01-introduction.tex:216-217`) and
  in "Scope" (p. 5, `01-introduction.tex:393`). The conditional Student-t clause is on p. 3
  (`01-introduction.tex:254-257`). What stands on p. 30 only is "Not treated"
  (`04-conclusion.tex:201-204`): the stages $\mu_{s,t}$ with $s > 0$, the generator, locality and
  the extrema of the smoothed signal.
- "Scope" is on p. 5, not within the first three pages. Right.

**Judgement.** A scale-space reader does bring expectations about locality, extrema and an evolution
equation, and a pointer to p. 30 does not meet them. One sentence does. The list itself stays in
§ 4.1, where the author's review put it (Q-0408: "Not treated" moved from the remark to § 4.1).
`WRITING.md` § 1 asks for candour about limits where the claim is made.

**Disposition: ACCEPT.** Replace the sentence quoted by:

> The stages $\mu_{s,t}$ with $s > 0$ are not examined at their centre, and nothing is claimed in
> $\RR^d$ on locality, on the extrema of the smoothed signal or on a generator of the scale
> evolution (\S\ref{sec:open-problems}).

Then move the paragraph "Scope" to follow "Families in every dimension at once", so that it is on
p. 3 with the answers. Cost: +1.5 lines for the sentence, paid by Ra; the move costs nothing. No
statement is touched. The content review's required change 4 rewrites the sentences on sampling
near the same place, so the two edits are made together.

## 3. Rewrite the abstract around the present paper's results (p. 1)

**Facts.**
- "The author's earlier papers classified the apertures on the line" is in the abstract
  (`main.tex:158-159`). Right. It is the second sentence, and the same sentence carries the
  definition of the axioms ("weaken the semigroup to a hemigroup, a two-parameter cascade, and that
  name no dimension").
- "a spike, whose rate is given with its constant" (`main.tex:165`). Right.
- "'Rate' also conceals the different forms of the conclusions below and at the threshold." Right.
  Proposition 3.15 has an asymptotic equivalence with the constant $R(d,c)$ for $c < d$, and for
  $c = d$ an equivalence with a truncated integral of the transform and a logarithmic lower bound
  (`03-isotropic.tex:1033-1053`). "With its constant" fits the first only.
- "line's building blocks" is not explained in the abstract (`main.tex:173`). Right.
  `REPOSITIONING-paper-iso.md` § 20, item 5, already lists this as open for the author.
- "Series history occupies the opening, while classification, applications, novelty qualifications,
  and verification compete in one dense paragraph." The abstract is one paragraph of 249 words. Its
  order is: the setting, the axioms, the question, the classification, the threshold with its
  consequence and the Matérn example, the filtration, what is known and what is new, the
  verification. That is the order the review proposes, with the question added.

**Overlap.** The content review (§ 2, "Rate at the centre") makes the same point on "rate": at
$c = d$ the result is not an equivalence with a constant times $\log(1/s)$. Its required change 1
rewrites the novelty sentences of the abstract.

**Judgement.** Three faults are real: the grammatical subject of the second sentence, "rate", and
"building blocks". The order is not at fault. The abstract was rewritten in the repositioning pass to
open with the question, which is the author's rule for § 1 (comment 4 of the author's review:
questions, then answers) and the template's contract (the object, the gap, the contribution). A
reordering that drops the question would undo that. The abstract has a gate of 250 words
(`records/affine/check-paper-iso-backmatter.py`), and it will be rewritten once more for the content
review, so it is edited once, after that response is planned.

**Disposition: ACCEPT IN PART** (the three sentences; not a new order).
- Second sentence: "The axioms studied here weaken the semigroup to a hemigroup, a two-parameter
  cascade, and name no dimension. On the line the author's earlier papers classified the apertures
  they allow." (+2 words)
- "The kernels from scale zero, which take the signal to each scale, are again the dilations of
  …" (+7 words; item 5).
- "Otherwise a point source is recorded as a spike, with an explicit asymptotic rate when $c < d$
  and at least logarithmic growth when $c = d$." (+7 words)
- "…and that of the line's elementary exponents only the Gaussian is itself admitted in the
  plane." (+2 words; item 14)
- Drop "The dimension enters twice." and the "And" before "the exponents" (−5 words).

Net +13 words, a formula counted as one word. They are recovered from the two sentences on what is classical and what is known
(22 words now), which the content response rewrites, and from "which determine the families" (4
words). The page length does not change. No statement is touched.

## 4. Give a plain-language verification contract before the detailed inventory (pp. 5–7)

**Facts.**
- "every proof is machine-checked" is on p. 5 (`01-introduction.tex:430-431`). Right.
- "What is neither." is the paragraph heading on p. 7 (`01-introduction.tex:543`). Right.
- "The broad opening claim precedes its most important qualifications by two pages." Right in part.
  The third sentence of § 1.1 is nearly the contract the review asks for: "So the proof assistant
  has verified each of these statements from the definitions, its own logical foundations and the
  seven cited facts listed below" (`01-introduction.tex:432-433`). What comes a page and a half
  later is the list of what is outside the check.
- "'Neither' is especially obscure." Overstated. The first sentence under the heading says "Three
  things in the paper are neither machine-checked nor cited". The heading alone is elliptical.

**Overlap.** The content review (§ 5) asks that "verified" always means that the Lean declarations
follow from their assumptions, and that it does not mean the truth of the cited facts, the agreement
with the PDF or novelty. Same point.

**Judgement.** The reader of the brief has never used a proof assistant. For that reader the limits
of the check belong beside the claim. The fix is one sentence at the head, inside § 1.1, so the rule
of `WRITING.md` § 4 holds: nothing honesty-critical leaves the subsection. The three-part shape of
§ 1.1 (what is machine-checked, what is assumed, what is neither) is the author's decision (c) of
2026-10-11 and stays. The author's sentence on who reviewed the formal statements stays word for
word, as the review also asks.

**Disposition: ACCEPT IN PART.** After the third sentence of § 1.1 add:

> Four things are outside that check, and each is taken up below: the cited facts themselves, which
> are assumed; what the prose draws from the statements, the worked examples among them; the two
> figures; and the agreement between each formal statement and the statement printed here, which
> was reviewed by AI agents only.

Rename the heading "What is neither." to "Outside the formal verification." The paragraph under it
is unchanged. If the author prefers the present heading, the added sentence does the work alone.
The proposed opening "Lean checks that the formal conclusions follow from the formal definitions
and seven assumed external theorems" is declined as a replacement, because the third sentence says
it. Cost: +3 lines, paid by Rc and Rb. The new sentence has no `\ref` and names no cited fact by its
label, so the trust-base check of `linkage check` reads it as prose (`LINKAGE.md` rule 13).

## 5. Define "from scale zero" once, and add the missing explanatory diagram (pp. 1–2, 15)

**Facts.**
- "kernels from scale zero" is in the abstract (`main.tex:161`) and on pp. 1 and 2
  (`01-introduction.tex:147`, `198`). Right. The phrase is not on p. 15. That page has
  Definition 3.2, where the stages $\mu_{s,t}$ are defined.
- Is it defined before its first use? No. Its first use is in the abstract, with no gloss. In § 1 it
  is introduced by use: "the kernel from scale zero to scale $t$ has the transform …"
  (p. 1, `01-introduction.tex:145-146`), after "the stage from scale $s$ to scale $t$"
  (`01-introduction.tex:135`). The symbol $\mu_{0,t}$ for a kernel of the family is not written in
  § 1 or § 2. It first appears in Theorem 3.6 (p. 17, `03-isotropic.tex:382`). The hemigroup law
  $\mu_{r,t} = \mu_{s,t} * \mu_{r,s}$ is on p. 1 (`01-introduction.tex:136`).
- "requires the reader to distinguish scale zero from the spatial origin". Right. The paper has
  three zeros: scale zero, the centre of the kernel (the origin of $\RR^d$; the headings of §§ 2.4
  and 3.3 and several statement titles say "origin"), and the "profile at the origin" $k_d(0{+})$,
  which is at radius zero of the Lévy measure.
- "Neither existing figure explains that architecture." Right. Figure 1 is the Matérn density and
  Figure 2 the critical values.

**Judgement.** A real obstacle, since the abstract and every statement on the centre rest on the
phrase. One clause
at the first use, with the symbol, removes it. The composition law is already on p. 1 in symbols, so
a figure with three nodes would show what one displayed formula shows. A figure costs about 5 lines
and a caption, which the budget does not have.

**Disposition: ACCEPT IN PART** (the definition; not the figure).
Replace `01-introduction.tex:145-147` by:

> Up to a relabelling of the scales, the kernel $\mu_{0,t}$ from scale zero to scale $t$, which
> takes the signal itself to its record at scale $t$, has the transform $e^{-F(t|\omega|)}$ for one
> function $F$, the \emph{exponent} of the family. So the kernels from scale zero are the dilations
> of one law. Zero is here a scale; the point $x = 0$ of a kernel is called its centre.

Cost: +1 line, paid by Ra. The abstract's gloss is in item 3. No statement is touched.
**For the author:** a schematic of the cascade (signal, record at $s$, record at $t$, with the
arrows $\mu_{0,s}$, $\mu_{s,t}$, $\mu_{0,t}$) is the one new figure the review asks for. It costs
about 0.1 page, which Rf or Rg would pay.

## 6. Replace "origin datum" with vocabulary that explains its contents (pp. 18–19)

**Facts.**
- "Hence the name origin datum." is on p. 18 (`03-isotropic.tex:487`). Right.
- "The name emphasizes where one parameter is evaluated, rather than what the pair represents."
  Right as a description. The definition says what the pair is: a Gaussian coefficient $a$ and a
  polar profile $k_d$ (`03-isotropic.tex:495-496`).
- "Explain $k_d(r)\,dr/r$ as the intensity assigned to a radial interval, then define
  $c = k_d(0+)$." The text does both. The paragraph before the definition has "the displacements of
  size between $r_1$ and $r_2$ have the rate $\nu_d(\{r_1 < |x| < r_2\}) = \int_{r_1}^{r_2}
  k_d(r)\,dr/r$" (`03-isotropic.tex:478-480`), and the definition has $c := k_d(0{+})$
  (`03-isotropic.tex:515`). The review asks for something that is there.
- "State explicitly that $f_d$ is the density of the jump-intensity measure, whereas $p$ is the
  smoothing-kernel density." The text introduces $f_d$ as the radial density of the Lévy measure
  (`03-isotropic.tex:473-474`). It never sets it against the density $p$ of the kernel. Table 2 has
  a row for $\nu_d$, $f_d$ and none for $p$, $q$.

**Overlap.** The content review (§ 7): "'Origin datum' also adds terminology for a standard
isotropic Lévy triplet; a brief explanation suffices."

**Judgement.** The confusion between the two densities is a real risk for a reader new to Lévy
measures, and one sentence and one table row prevent it. The rename is not worth its cost. "Origin
datum" is a defined term of a shared definition that the affine paper prints, the Lean structure is
`OriginDatum`, and "polar profile" is the cone paper's term for its (4.6). A rename changes no
mathematics and the reader still has to learn a pair of a Gaussian coefficient and a radial profile.
The boxed dictionary the review asks for is Table 2.

**Disposition: ACCEPT IN PART** (the contrast; not the rename).
- After "has a radial one, $f_d(|x|)$" (`03-isotropic.tex:473-474`) add: "It is the rate of the
  displacements per unit volume, not the density of the kernel, which is written $p$ from
  \S\ref{sec:isotropic-origin} on."
- Table 2: a row "$p$, $q$: the density of a kernel and its radial form, $p(x) = q(|x|)$ (not the
  Lévy density $f_d$)".

Cost: +2 lines, paid by Rf. No statement is touched.
**DECLINE** the rename: a defined term of a shared definition, explained where it is introduced.

## 7. Explain the slowly varying factor where the reader first needs it (pp. 2, 13, 25)

**Facts.**
- "the power at which the transform of the kernel falls off" is on p. 2
  (`01-introduction.tex:218`). Right. The sentence goes on to define $c$ exactly:
  $-\log\widehat\mu(\xi)/\log|\xi| \to c$. So § 1 does not say that the transform is a constant
  times $|\xi|^{-c}$, but it does not say that it is not.
- "Slowly varying" is defined on p. 13, before the cited fact C7, with the logarithm as its example
  (`02-line-papers.tex:511-514`). Right.
- The factor $L$ is written out on p. 25, after Proposition 3.15: "$\widehat\mu(\rho e) =
  \rho^{-c}L(\rho)$ with $L$ slowly varying" (`03-isotropic.tex:1062-1063`). Right. It is used
  before that, on p. 22, as "$|x|^{c-d}$ times a slowly varying factor"
  (`03-isotropic.tex:801-802`).
- Not in the review: the opening of § 3.3 gives the two bounds that are proved, a constant times
  $|\xi|^{-c}$ from below and a constant times $|\xi|^{-\beta}$ for every $\beta < c$ from above
  (p. 22, `03-isotropic.tex:793-796`). The author's review record chose the bounds for the opening
  (Q-0408, "The dispatching session's reading"), and "slowly varying" was taken out of § 1 on
  purpose in round 3 (`REPOSITIONING-paper-iso.md` § 16.3).

**Judgement.** Right in substance. The reader meets "a slowly varying factor" on p. 22 with a
definition nine pages back, in a subsection on cited facts that the paper invites a reader to skip
to or past, and the identity that ties the factor to the transform comes three pages later. The fix
belongs in the opening of § 3.3, after the two bounds, not in § 1, whose definition by the limit is
exact. The statement of C7 stays in § 2.6, as the review says.

**Disposition: ACCEPT IN PART** (§ 3.3; § 1 unchanged).
- After "so it is integrable exactly when $c > d$." (`03-isotropic.tex:796`) add: "The transform
  need not be a constant times $|\xi|^{-c}$. It is $|\xi|^{-c}L(|\xi|)$ with a factor $L$ that
  varies slowly: $L(\lambda\rho)/L(\rho) \to 1$ as $\rho \to \infty$ for every $\lambda > 0$, as
  for a constant or a logarithm (\S\ref{sec:cited-facts}; Lemma~\ref{lem:isotropic-exponent-log}(2))."
- `03-isotropic.tex:801-802`: "which is $|x|^{c-d}L(1/|x|)$, with the same factor" for "which is
  $|x|^{c-d}$ times a slowly varying factor".
- Rd after the proposition.

Cost: +2.5 lines, of which Rd pays 1.5 and Rb the rest. No statement is touched. The fourth open
problem of § 4.1 is about the same factor, and the content review says it can be answered, so the
wording there waits for that response.

## 8. Turn Table 3 into a comparison table instead of a literature survey in cells (p. 21)

**Facts.**
- The caption begins "What is in print about the six statements of §3.3" (p. 21,
  `03-isotropic.tex:776`). Right.
- "long source histories and clause references make the table difficult to scan". Right. The table
  is set in `\footnotesize` with four columns (the statement, on the line, in $\RR^d$ in print,
  here), and the third column has cells of six to eight lines with up to six anchored citations
  (`03-isotropic.tex:715-775`).
- "Together with Figure 1, it interrupts the opening explanation of $c$ between pp. 20 and 22."
  Right, and more than the review says. Figure 1 and Table 3 are one float on a page of their own
  (`03-isotropic.tex:695-781`). The page falls inside a sentence: p. 20 ends "the limit of its polar
  profile at radius zero" and p. 22 begins "(Definition 3.9)".
- Not in the review: the header comment of § 3.3 says the table comes "after a dictionary of three
  sentences" (`03-isotropic.tex:671-673`). In the source and in the build the dictionary paragraph
  follows the float (`03-isotropic.tex:816-823`, p. 22). The caption carries one sentence of it.

**Overlap.** The content review judges Table 3 row by row (§ 6) and requires new rows and sources
(required change 1: the Hankel theorems of Bingham and Inoue, the Bessel potentials of Aronszajn and
Smith). The table's content changes in that response.

**Judgement.** The table earns its place, as the review says, and its present form is the result of
two constraints: every attribution once with its anchor (round 3 of Q-0414), and one float page so
that no float falls inside the theorem. The review's four columns with the anchors in a second table
would shorten the main text by about a quarter of a page, which would pay for every addition of
this record. It also changes where the paper keeps the anchors of its novelty comparison, and the
content response changes the rows. So the restructuring is one decision with that response.

**Disposition: ACCEPT IN PART.**
- Now, as a prose edit: the caption gains the dictionary. After "A law in print at time $\tau$ is a
  kernel with $\tau c$ in place of $c$." add "Here $\tau$ is the time of a Lévy process with the
  transforms $e^{-\tau F_d}$, and the kernel is its law at $\tau = 1$." Cost: +1 line, paid by Rf.
- **For the author, with the content response:** the columns "statement; known before, by scope
  (the line; $\RR^d$); here; sources by number", cells of at most three lines, and the anchors in a
  table of Appendix A. Figure 1 and the table become two floats, the figure at the head of § 3.3
  (the author's rule 4 of Q-0408) and the table after the dictionary paragraph. Estimated effect on
  the main text: −12 to −16 lines (Rg). It needs a build to see that no float falls inside
  Theorem 3.12.

## 9. Remove avoidable notation collisions and simplify Table 2 (pp. 13–14, 17, 47)

**Facts.**
- "Seven letters keep a second role inside a statement." is on p. 13 (`02-line-papers.tex:546`).
  Right. The seven are $c$, $\tau$ (as $\tau_a$), $\lambda$ (as $\lambda_d$), $t$, $a$, $x$ and $s$
  (`02-line-papers.tex:546-552`).
- Does Table 2 document seven letters with a second role? Yes, and two of them have more than two
  roles. $\lambda$ is a dilation factor, the contraction ratio, the number $\lambda_d$ and, in C2, a
  measure on the sphere (`02-line-papers.tex:568-570`). $\tau$ is the time of a Lévy process, the
  cut-off of a $\Cin$ ray, a constant of Proposition 3.16 and, as $\tau_a$, a translation
  (`02-line-papers.tex:590-591`, `597-599`).
- "The principal $c$ also denotes a gauge ratio". Right: the uniqueness clauses of Theorem 3.6
  (p. 17, `03-isotropic.tex:383-387`) and of Corollary 3.7 (p. 18, `03-isotropic.tex:445-450`).
- "and a local Tauberian constant". Right: C7 has "let $c > 0$ and $\rho > 0$"
  (p. 13, `02-line-papers.tex:527`), and the lead says that this $c$ is not the profile at the
  origin (`02-line-papers.tex:520-521`). Further uses the review does not list: $c_1$ and $\tau$ in
  Proposition 3.16, $c_j$ in C6, and "the cone paper, which writes $c$ for $w$"
  (`03-isotropic.tex:1247`).
- "on p. 47, $\chi$, previously the gauge, becomes a radial transform". Right: "Write
  $\chi(\rho) := \widehat\mu(\rho e)$" in the proof of Proposition 3.15
  (`appendix-isotropic.tex:1333`).
- "use $r$ for spatial distance". Proposition 3.15 writes $s$ for a distance
  (`03-isotropic.tex:1031-1053`), and Propositions 3.16 and 3.17 write $r$
  (`03-isotropic.tex:1117`, `1155`). Right that the three are not alike.
- "The table documents collisions that could largely be eliminated." Right, and already on record.
  `GATE-paper-iso.md` lists them as owed at the blueprint: item 1 (the gauge ratio $c$, suggested
  $\lambda$), item 5 ($\tau_a$), item 9 (the heat variance $t$), item 15 ($\lambda_d$ and the
  dilation factor $a$ of Lemma A.3(2)) and item 22 (the scales $x \le y$ of
  $\mu^{\mathrm I}_{x,y}$). New in the review: $\chi$ in the proof of the rate, $s$ in
  Proposition 3.15, and the $c$ of C7.

**Overlap.** The content review (§ 7): "overloaded letters and repeated redefinitions make the route
harder than necessary".

**Judgement.** The finding is right and the paper cannot act on it alone. Every collision but the
table's own layout sits in a shared statement or a proof of record. The gauge ratio $c$ is in a
statement that the affine paper prints, and the dilation factor $a$ in another. A rename there
changes the blueprint, the Lean docstrings and both papers. Proposition 3.15 and its proof are
printed by this paper only. The notation table itself is required by `WRITING.md` § 0 and was asked
for in Q-0310, so it stays. A table with one meaning per symbol is possible only after the renames.

**Disposition: ACCEPT IN PART.**
- Now, as a prose edit: Ra, the lead of § 2.7 in one sentence.
- **Blueprint batch, for a decision** (one pull request at the blueprint, mirrored in both
  papers): the gauge ratio $c \to \lambda$ in `thm:isotropic-classification` and
  `cor:isotropic-classification-operators` (GATE item 1, with item 16); the distance $s \to r$ in
  `prop:origin-rate-d`; $\chi(\rho) \to h(\rho)$ in its proof of record; the scales
  $x \le y \to u \le v$ in `prop:isotropic-bridge` (GATE item 22); the dilation factor $a$ and
  $\lambda_d$ (GATE item 15). Table 2 then loses five second roles and the row for $s$ (Rh), and
  is regrouped by subject with a column for the place of definition.
- **DECLINE** the rename of $c$ and $\rho$ inside C7 and of the source's letters inside C2, C3 and
  C6. A cited fact is stated in the letters of its source so that it can be compared with the page,
  and the lead of each says that its letters are local.

## 10. Make the literature's process time visibly distinct from imaging scale (pp. 3–4, 21–22)

**Facts.**
- "Table 3 needs a dictionary" and "the law at time $\tau$ has the power $\tau c$ in place of $c$."
  are on p. 22 (`03-isotropic.tex:816`, `821-822`). Right.
- "The necessary explanation is present, but follows the table it explains." Right for that
  paragraph. Incomplete: the caption of Table 3 has the key sentence
  (`03-isotropic.tex:777-778`), and § 1 has the whole dictionary on pp. 3–4
  (`01-introduction.tex:288-293`).
- "The introduction also uses $t$ for process time, while §3.3 switches to $\tau$." **Wrong as
  stated.** Is the process time $t$ in § 1 and $\tau$ in § 3.3? No. The time of the Lévy process is
  $\tau$ in § 1 as well, on the pages the review cites (`01-introduction.tex:290-298`, and in the
  contributions, `357-360`, `375-376`). The $t$ of p. 3 is in the paragraph on the classification
  (`01-introduction.tex:262-266`). It is the time of Sato's self-similar process with independent
  increments, another process, whose time is the scale of this paper.
- Table 2's row for $\tau$ says "in §3.3" (`02-line-papers.tex:597`). The same use is in § 1.

**Overlap.** The content review (suggestion 3, and § 6 "Heat-kernel comparison") finds "the
literature does not study one law" wrong and "a limit $\tau \to 0$ says nothing about one kernel"
too categorical. Both sentences are in this paragraph and in § 1.

**Judgement.** The paper already keeps the two parameters apart by letter. What it does not say is
how they act differently, and the review's display says it in one line: the time multiplies the
exponent, the scale rescales the frequency. That sentence is worth its line and a half. The table's
place is item 8.

**Disposition: ACCEPT IN PART.**
- In the dictionary paragraph, before its last sentence (`03-isotropic.tex:822`), add: "The time
  is not the scale. The time $\tau$ multiplies the exponent, $e^{-\tau F_d(\xi)}$, and the scale $t$
  of this paper rescales the frequency, $e^{-F(\chi(t)|\xi|)}$." Cost: +1.5 lines, taken from the
  margin.
- The caption's sentence of item 8.
- Table 2, the row for $\tau$: "in §1 and §3.3".
- **DECLINE** "use $\tau$ consistently for process time": it is so used. The $t$ of the
  classification paragraph is the time of a different process.

The last sentence of the paragraph is reworded in the content response.

## 11. Make §3.4's witness construction follow the result (pp. 27–28)

**Facts.**
- "So it is built like a subordinated exponent, and the witnesses of the theorem are not
  subordinated." is on p. 27 (`03-isotropic.tex:1250-1251`). Right.
- "The opening gives a useful question, then accumulates series history, subordination terminology,
  witnesses, and critical values." Right in part. The opening has three paragraphs: the question,
  the answers by number, the separating family with the plan (`03-isotropic.tex:1211-1258`). The
  series history is two sentences of the second paragraph (`03-isotropic.tex:1230-1232`,
  `1238-1241`) and the clause "of the cone paper, which writes $c$ for $w$"
  (`03-isotropic.tex:1246-1247`).
- "Lead with the conclusion: some exponents lose the required self-decomposability at every
  dimensional step." The second paragraph does: "At every step some exponents are lost"
  (`03-isotropic.tex:1224`).
- "define $w_d$ as the largest permitted value in dimension $d$. Explain the failure through loss
  of monotonicity." Both are there: "nonincreasing exactly when $w$ is at most a critical value
  $w_d$" (`03-isotropic.tex:1252-1253`), and "what is lost … is the monotonicity of that profile"
  after the theorem (`03-isotropic.tex:1308-1315`).
- "Move the earlier paper's parameter convention and numerical history after the theorem." The
  numerical history is after the theorem (`03-isotropic.tex:1323-1325`). The parameter convention
  is in the opening.

**Overlap.** The content review (§ 7, suggestion 5) wants the qualitative strictness kept apart from
the quantitative study of this family, and the bound $6 + 4\sqrt2$ reduced to a remark.

**Judgement.** The order of the opening is the author's (Q-0408: the question in the reader's terms,
the results by number, then the family and the plan), and it already leads with the conclusion after
the question. What the review saw is real on a smaller scale: the quoted sentence sets "built like a
subordinated exponent" against "not subordinated" for a reader who has just learned the word, and
the opening repeats attributions that § 1 and § 2.3 carry.

**Disposition: ACCEPT IN PART** (three local edits; not a reordering).
- Replace `03-isotropic.tex:1246-1251` by: "Strictness is shown on one explicit family of exponents
  $F^{(w)}$, $w > 0$. It has the form of the bridge, $F^{(w)}(r) = F^{(w)}_{\mathrm I}(r^2/2)$ for
  a delay datum (\S\ref{sec:line-bridge}), with the delay profile a power plus a step of height $w$
  on $[1,2]$. That profile is not monotone, so the family is none of the subordinated families.
  Its members that separate two classes are called \emph{witnesses} below."
- Move "of the cone paper, which writes $c$ for $w$" to the paragraph after Theorem 3.19 that
  cites the cone paper's values (`03-isotropic.tex:1321-1325`).
- Rb.

Cost: none. This edit is where the 2 lines of Rb come from. No statement is touched.
**DECLINE** the reordering: it would undo the order the author asked for, and the second paragraph
already opens with the conclusion.

## 12. Put the main boundedness statement first in Theorem 3.12 (pp. 20, 22–23)

**Facts.**
- "5. (The dichotomy.)" is the fifth clause, on p. 23 (`03-isotropic.tex:879`). The theorem begins
  on p. 22. Right.
- "the answer is the fifth clause of a theorem containing decay estimates, derivative regularity, a
  mixture construction, and Gaussian-blur estimates". Right: clauses (1) to (4)
  (`03-isotropic.tex:840-878`).
- Not in the review: the theorem's title states the answer ("the boundedness threshold in dimension
  $d$ is the dimension", `03-isotropic.tex:836`), the opening states it before the theorem
  (`03-isotropic.tex:789-791`), and the comment after the theorem begins "Clause (5) is the
  threshold" (`03-isotropic.tex:890`).
- The heading of § 3.3 is "The origin in dimension $d$" (`03-isotropic.tex:650`), and of § 2.4 "The
  origin on the line". The plan of § 1 calls § 3.3 "the kernels at their centre"
  (`01-introduction.tex:401`).

**Overlap.** The content review (§ 7): "Theorem 3.12(3) largely duplicates the general threshold
while adding the explicit mixture; move that mixture beside the examples." Both reviews want the
theorem lighter.

**Judgement.** The clause order is that of the proof: (1) gives (2), (4) gives (5). The theorem is a
shared statement. Its clause numbers are cited in at least ten places of this paper, among them Table 1
("C1, in clauses (2) and (5)") and Proposition 3.17, and in the Lean docstrings. The affine paper
does not print it. A reader is told the answer three times around the statement, so a reordering
buys little. The heading is another matter. "The origin" names nothing an imaging reader recognizes,
and the paper's own prose says "centre". A heading is not shared text.

**Disposition: ACCEPT IN PART** (the headings and one pointer; not the clause order).
- § 3.3: "The kernel at its centre". § 2.4: "The kernel at its centre, on the line". The same for
  the heading of A.3. The labels stay.
- Before the theorem (`03-isotropic.tex:830`), add to the sentence on the Gaussian part: "The
  threshold itself is its clause (5)." Cost: +0.5 line, taken from the margin.
- **For a decision at the blueprint**, together with the content review's point: split
  `thm:origin-boundedness-d` into a theorem (the dichotomy and the ladder of derivatives) and a
  proposition (the decay, the blurred kernel, the mixture), or leave it. A split renumbers every
  statement after 3.12.
- **DECLINE** the review's title "Central boundedness and singularities": "the kernel at its
  centre" is the paper's phrase in § 1 and § 4.

## 13. Give §3.2 a roadmap matching its three different jobs (pp. 16–20)

**Facts.**
- "The second half of the subsection gives the class $\mathcal{A}_d$ … an explicit form." is on
  pp. 16–17 (`03-isotropic.tex:318-319`). Right.
- "'Reduction to the line' promises a proof method, but the subsection also supplies a
  parameterization and several kernel constructions." Right. After Lemma 3.8 the subsection has
  Definition 3.9 and Proposition 3.10 (the polar form), then Proposition 3.11 (the mixtures and
  three named families).
- "less clearly signposted changes of purpose". The changes are signposted by a sentence each
  ("The theorem names the class $\mathcal{A}_d$ and does not say which functions belong to it",
  `03-isotropic.tex:468`; "The bridge from the time-causal theory … carries over to $\RR^d$",
  `03-isotropic.tex:571`). There are no headings inside the subsection.
- The Student-t clause is clause (4) of Proposition 3.11, titled "(The Student-t kernels,
  conditional.)" (`03-isotropic.tex:616`), and the paragraph after the proposition says what the
  two levels of hypothesis are (`03-isotropic.tex:639-648`).

**Judgement.** Four pages with one heading is long for this reader, and the plan sentence names two
things where there are three. Two run-in headings and a plan of three parts are enough. The opening
of § 3.2 is the one the author asked for (Q-0406, comment 2) and is not touched. The Student-t
clause cannot become a remark: it is a clause of a shared statement with two Lean declarations, and
§ 1.1 says that a remark has no formal counterpart.

**Disposition: ACCEPT IN PART.**
- Replace the sentence quoted by: "The subsection has three parts: the classification by projection
  (to Lemma~\ref{lem:isotropic-realisation}), a test for membership in $\mathcal{A}_d$ by a radial
  profile (Definition~\ref{def:isotropic-origin-datum}, Proposition~\ref{prop:isotropic-polar-reading}),
  and the Gaussian variance mixtures, which lie in every class
  (Proposition~\ref{prop:isotropic-bridge})."
- Run-in headings: `\paragraph{The class $\mathcal{A}_d$ in polar form.}` at
  `03-isotropic.tex:468`, and `\paragraph{Gaussian variance mixtures in $\RR^d$.}` at
  `03-isotropic.tex:571`.

Cost: +1.5 lines, paid by Rf. No statement is touched.
**DECLINE** the remark for the Student-t clause, for the reason above.

## 14. Explain Cin rays through their profiles before using the name (pp. 3, 10–11, 29)

**Facts.**
- "members of the Cin rays, the extreme rays of the cone" is on p. 3
  (`01-introduction.tex:236-237`). Right. The sentence introduces the cone, its extreme rays, the
  name and the cosine integral at once. The profile comes one sentence later
  (`01-introduction.tex:238-240`).
- Where is the explanation of superpositions of $\Cin$ rays? On p. 29 only, after Theorem 3.20: "A
  member of $\mathcal{A}_2$ is admissible on the line, so it is still a superposition of $\Cin$
  rays and a Gaussian term. The theorem says that none of those rays is itself in $\mathcal{A}_2$"
  (`03-isotropic.tex:1358-1360`). The abstract (`main.tex:173`), § 1 (p. 3,
  `01-introduction.tex:241-242`) and the opening of § 3.4 (p. 27, `03-isotropic.tex:1234`) say
  "building blocks" without it. Right.

**Overlap.** The content review (§ 2, "Cin rays") accepts "building blocks" because p. 29 explains
it, and asks that the explanation is kept.

**Judgement.** "Of the building blocks of the line only the Gaussian gives a family in the plane"
invites the inference that nothing built from the other blocks does, which is false, and the
correction is 26 pages away. The author's review record met the same misreading once
(Q-0408: "The theory in the plane is not assembled from the line's pieces" was corrected). This is
the one item where the text can mislead, and the fix is a sentence.

**Disposition: ACCEPT.** Replace `01-introduction.tex:235-242` by:

> The exponents of the line form a convex cone, and every one of them is a superposition of a
> Gaussian term and of elementary exponents, each with a \Levy{} measure whose density is
> proportional to $1/|x|$ up to a cut-off and zero beyond it (\S\ref{sec:line-bridge}). These are
> the members of the $\Cin$ rays, the extreme rays of the cone other than the Gaussian one
> (Proposition~\ref{prop:line-extreme-rays}). No member of a $\Cin$ ray lies in $\mathcal{A}_2$
> (Theorem~\ref{thm:no-cin-ray-in-the-plane}). So of the building blocks of the line only the
> Gaussian gives a family in the plane by itself. Their superpositions can: an exponent in
> $\mathcal{A}_2$ is still a superposition of $\Cin$ rays and a Gaussian term.

In the opening of § 3.4 (`03-isotropic.tex:1234-1235`): "All the building blocks of the line but
the Gaussian are lost at the first step, each taken by itself." Cost: +1.5 lines, paid by Re and
Rb. No statement is touched. The abstract's clause is in item 3.

## 15. Present the "bridge" as a Gaussian variance mixture (pp. 3, 9–10, 20)

**Facts.**
- "Run a Brownian motion in $\RR^d$ for such a random time." is on p. 3
  (`01-introduction.tex:246-247`). Right. In § 1 the process comes first and the mixture second.
- The review cites pp. 9–10 for the same fault. **Wrong for those pages.** § 2.3 opens as the
  review proposes: "Blur the signal with a Gaussian whose variance is not fixed but drawn at random,
  and average over the draws. The result is a Gaussian variance mixture, the law of a Brownian
  motion at a random time" (p. 9, `02-line-papers.tex:205-208`). The author asked for that opening
  (the author's review, § 2: "Subordination … needs a bit more introduction").
- "retain the explanation of why the endpoint scales are squared". It is on p. 10
  (`02-line-papers.tex:283-284`).
- "'Delay,' 'bridge,' and 'subordinated slice' then become additional vocabulary". Right. "Delay
  datum" and "delay profile" are in shared statements (Definition 3.9, Definition 3.18), and
  "subordinated slice" in the title of clause (3) of Theorem 3.12 and in Definition 3.18.

**Judgement.** § 1 should say it as § 2.3 does, kernel first. That is a reordering of two sentences
inside the paragraph the author asked for (comment 4), and it keeps the citation of the time-causal
theory. The heading of § 2.3, "The causal bridge and the dimension filtration", uses the series'
word. The author's own word for the subsection was "subordination", which is on the teach list of
`WRITING.md` § 0.

**Disposition: ACCEPT IN PART.**
- Replace `01-introduction.tex:246-249` ("Run a Brownian motion … (§2.3).") by: "Draw the variance
  of a centred Gaussian on $\RR^d$ from such a law, and average. The result is a \emph{Gaussian
  variance mixture}. It is the law of a Brownian motion run for the random time, and the
  construction is called \emph{subordination} (\S\ref{sec:line-bridge})."
- Heading of § 2.3: "Subordination and the dimension filtration". The label stays.

Cost: 0 lines. No statement is touched.
**DECLINE** removing "delay", "bridge" and "subordinated slice": they are terms of shared
statements and of the cone paper, and each is introduced in § 2.3.

## 16. Make Table 1 interpretable without proof-assistant experience (p. 7)

**Facts.**
- "every other statement" and "none" are the last row of Table 1 (p. 7,
  `01-introduction.tex:533`). Right.
- "its second column mixes dependencies of checked implications with results establishing existence
  of the law or density". Right for two rows: the upper bound ("none for the bounds of clauses (1)
  and (2); C3(iii) for clause (3); C2, C3(iii) and C5 for the existence of the density") and the
  rate ("C7 for the limits; C2, C3(iii) and C5 for the existence of the density")
  (`01-introduction.tex:526-529`). The paragraph before the table explains the difference
  (`01-introduction.tex:503-510`).
- "'None' can sound stronger than intended." Right. The column heading says "cited facts", but the
  cell reads alone as "nothing".
- "Use 'assumed external theorem' in place of 'cited fact'". The term is defined on p. 6: "Seven
  theorems of the literature are taken as given, the cited facts C1 to C7"
  (`01-introduction.tex:456-457`). Its first uses are earlier, in the plan and in the first
  paragraph of § 1.1 (`01-introduction.tex:399`, `433`).

**Overlap.** The content review (§ 5) on what "verified" means, and on the twelve axioms of the
guard against the seven of this paper (item 19).

**Judgement.** The gloss on "none" is cheap and right. "Cited fact" is the term of both papers, of
the blueprint's ledger and of `WRITING.md` § 4, and it is defined a page before the table. It
should be defined at its first use. Descriptive names in the cells would repeat the list that
stands half a page above. Two columns for the two kinds of dependence would be clearer, but which
fact enters where is a statement about the formal proofs, so that change belongs with the
verification of the content review's § 5.

**Disposition: ACCEPT IN PART.**
- Caption of Table 1, add: "'None' means none of C1 to C7: the statement is verified from the
  definitions and the logical foundations of the proof assistant alone."
- Plan of § 1 (`01-introduction.tex:399`): "and the seven theorems of the literature that are used
  and not proved, the \emph{cited facts}".

Cost: +1.5 lines, paid by Rf.
**DECLINE** the rename of "cited fact" and the names in the cells, for the reasons above. The
split into two columns is left to the content verification.

## 17. Enlarge Figure 1 and label its visual lesson directly (p. 21)

**Facts.**
- "Here $c = 3/2$: the density is bounded on the line and unbounded in the plane and in space." is
  in the caption (p. 21, `03-isotropic.tex:704`). Right.
- "the graphic is only roughly 7 cm wide". Right. It is set at `width=0.45\textwidth`
  (`03-isotropic.tex:701`). The text is 159.2 mm wide, so the figure is 71.6 mm.
- "Axis and legend lettering are very small at print size." Right, and measured. The script draws
  at `figsize=(6.4, 3.6)` inches with the default 10 pt lettering
  (`records/affine/fig-matern-centre.py:85`). 162.6 mm is reduced to 71.6 mm, so the lettering
  prints at 4.4 pt. The body is 11 pt and Table 3 below it 9 pt.
- "the reader must infer which end represents approach to the centre". Right. The horizontal axis
  is labelled $|x|$ only.
- "label the finite-height curve directly". The legend labels it: "$d = 1$ (bounded)". The label is
  in the legend and not on the curve.
- Why it is small: `REPOSITIONING-paper-iso.md` § 20, item 2: "Figure 1 is small (0.45 of the text
  width), so that it shares a page with Table 3", with the alternative left to the author at about
  a quarter of a page.

**Overlap.** The content review (§ 4, required change 3): the caption's "with slope $c - d$ at the
centre" is wrong for the bounded curve, whose slope tends to 0. The script's own output agrees
(`records/affine/fig-matern-centre-output.txt:13`).

**Judgement.** Lettering at 4.4 pt is a defect at any width. It can be cured without a line of the
budget, by drawing the figure at the size at which it is printed. "Beside the Matérn example" is
p. 24. The author's rule is that the figure stands at the head of the subsection, where the opening
names the example (Q-0408, rule 4), so it stays there.

**Disposition: ACCEPT IN PART.**
- Redraw by the script at the printed width: `figsize=(3.5, 2.4)` with the default lettering
  prints at 8 pt at `0.45\textwidth`. Label the curves on the plot in place of the legend. Label
  the axis "distance $|x|$ from the centre" and mark the left end "centre". No new figure and no
  change of length.
- Caption: "with slope $c - d$ at the centre for $d = 2, 3$" (the content review's correction).
- **For the author** (already open in the repositioning record): a larger figure on its own, at
  about a quarter of a page, possible if Table 3 is restructured (item 8).
- **DECLINE** the move beside the Matérn example, and the slope guides: the caption gives the
  slopes.

## 18. Make Figure 2's monotonicity failure conspicuous (p. 28)

**Facts.**
- "increasing on an interval for $d = 3$." is in the caption (p. 28, `03-isotropic.tex:1338`).
  Right.
- "small legends and formula-heavy bound labels". Right. The figure is drawn at
  `figsize=(10.0, 3.8)` and set at `0.86\textwidth`, 136.9 mm
  (`records/affine/fig-thresholds.py:113`, `03-isotropic.tex:1331`). The legends are 8 pt and print
  at 4.3 pt. The axis labels and titles print at 5.4 pt. Two legend entries are formulas,
  $e^{-1/2}/(2\sqrt m)$ and $K/(2(1-\varepsilon_d)\sqrt m)$.
- "The decisive upward segment in panel (b) is subtle." Right. The profile $k^{(4)}_3$ increases on
  about $[1.20, 1.74]$ (`records/affine/fig-thresholds-output.txt:37`), from about 4.03 to 4.17 on
  an axis from 0 to 8.
- "line styles that remain distinct in grayscale, including the $w = 4$ reference line". Right.
  $k^{(4)}_1$ is solid black and $k^{(4)}_3$ solid red, and the line $w = 4$ is thin blue
  (`records/affine/fig-thresholds.py:119`, `128`).
- Not in the review: the axis and both panel titles say "threshold(s)". The paper's term has been
  "critical values" since round 3 (`REVIEW-register-paper-iso-s1s4-2026-10-11b-fixes.md`, flag 18).

**Judgement.** All four points hold, and the one that matters is the interval: the figure is there
to show a profile that fails to be monotone, and the eye does not find where. The cure is in the
script. Stacking the panels would cost about 0.15 page.

**Disposition: ACCEPT IN PART.**
- Redraw at `figsize=(6.7, 2.6)` with the default lettering, which prints at 8 pt. In panel (b)
  shade the interval $[1.20, 1.74]$ and label it "$k^{(4)}_3$ increases". Draw $d = 1$ solid,
  $d = 2$ dashed and $d = 3$ dash-dotted, in black, and the line $w = 4$ dotted with its label on
  the line. In panel (a) call the two curves "lower bound" and "upper bound", the caption naming
  Lemma A.5. Say "critical value" on the axis and in the titles.
- **DECLINE** enlarging or stacking, for the budget.

No change of length. The caption already separates what is computed from what is proved.

## 19. Give Appendix B an ordinary-language entry point and reconcile its counts (pp. 55–58)

**Facts.**
- "one of the twelve axioms listed in blueprint/trust-boundary.txt." is on p. 56
  (`appendix-verification.tex:130`). Right.
- "A novice moves from seven assumed theorems to twelve permitted axioms amid long declaration
  lists." Right. A list of 26 items of Lean names stands between the opening and the count
  (`appendix-verification.tex:62-120`).
- "The explanation exists, but is distributed across implementation-oriented prose." Overstated. The
  three counts are reconciled in the next paragraph, in three consecutive sentences: "Nine of the
  twelve axioms of that file are the seven cited facts of this paper, C3 being three. The other
  three are cited facts of the companion paper on affine covariance"
  (p. 56, `appendix-verification.tex:132-134`). That is what the review asks to have stated
  together.
- "Explain that a declaration is a named formal definition or result." The appendix uses
  "declaration" without saying it (`appendix-verification.tex:56-58`). Right.
- "Explicitly identify their status for this manuscript." The appendix does not say that no
  statement of this paper rests on the three other axioms. It says that Table 1 lists which of the
  seven each statement rests on.

**Overlap.** The content review (§ 5, required change 12): the guard permits twelve axioms and the
paper claims seven facts, the eight printed reports support the claim for eight declarations, and a
report or a guard for this paper alone is asked for. The counts of seven, nine and twelve are the
same point.

**Judgement.** An entry paragraph in plain words is right for the reader of the brief, and the
appendix is outside the page budget. The sentence on the three other axioms is a claim about the
formal development. It can be printed only when a check has shown it for every declaration listed,
which is the content review's request. Moving the reports to a supplement is against the standard:
`WRITING.md` § 4 puts the inventory in a verification appendix, and `linkage check` compares the
stamped block printed in the paper with what Lean prints (`LINKAGE.md` rule 13).

**Disposition: ACCEPT IN PART.**
- Second paragraph of Appendix B, new: "A \emph{declaration} is a named definition or proved
  statement of the formal development. An \emph{axiom}, in Lean's report, is a declaration taken
  without proof, and the report on a declaration lists every axiom its proof uses. This paper's
  seven cited facts are nine such axioms, C3 being three. The file that the check reads lists
  twelve, because it also serves the companion paper, which has three cited facts of its own."
- `appendix-verification.tex:130`: "or one of the twelve axioms listed in
  \texttt{blueprint/trust-boundary.txt}, nine of which are this paper's".
- A sentence "No declaration listed above depends on the other three" only after the check the
  content review asks for.
- **DECLINE** moving the lists and the reports to a supplement, for the reason above.

Cost: none in the main text.

## 20. Replace the project diary in the AI disclosure with publication-relevant information (p. 58)

**Facts.**
- "the agents' words outnumber mine by between twenty-one and forty-five to one." is on p. 58
  (`ai-statement.tex:51-52`). Right.
- "Word ratios, archived days, and 'the module'". Right: "over the module's first fourteen archived
  days" (`ai-statement.tex:53`). "Module" is a word of the programme. The same sentence prints a
  path of the repository, `notes/PROCESS.md`, and the repository is private until the release.
- "The autobiographical sentence about spare time". Right: "I would not, unaided and in spare time,
  have written this." (`ai-statement.tex:55`).
- What the review asks to retain is in the statement: the extent, the allocation of decisions, the
  review by agents only, that no human has reviewed the formal statements, and the responsibility
  (`ai-statement.tex:38-49`, `57`).

**Overlap.** The content review (§ 5, last paragraph, and suggestion 8) asks for the same: remove
the ratio, keep a short declaration of contribution and responsibility.

**Judgement.** The statement has the six-line form that the author decided for the series on
2026-09-14, and it is written in the first person as the author's declaration. `WRITING.md` § 6
rules what a number must be if one is printed (from the archive, dated, a lower bound). It does not
require a number. Its first rule is never to claim less AI involvement than there was. The
statement meets that without the ratio, through "the prose, statements, proofs and code … are the
agents' work, mostly unattended". Two external readers found the ratio and the last sentence but
one out of place. Whether the form of record changes is not an editor's choice.

**Disposition: AUTHOR.** The choice is between:
- (a) the six-line form as it stands, the same in every paper of the series, with the ratio;
- (b) the same statement without the fourth and fifth lines (the ratio with its period, and the
  sentence on spare time), which stay in `notes/PROCESS.md`. The affine paper's statement shares
  those lines and would follow.

In either case two words are fixed for a reader outside the programme: "the module's" (say what is
counted: this paper, or this paper and its companion; the archivist's derivation decides), and the
bare path `notes/PROCESS.md` (say "the file `notes/PROCESS.md` of the repository deposited with the
paper").

---

## List 1: prose edits that touch no statement, in the order to do them

The order puts first the edits that others depend on, then goes through the paper.

| order | item | edit | lines |
|---|---|---|---|
| 1 | 12 | headings of §§ 2.4, 3.3 and A.3 ("the kernel at its centre"); the pointer to clause (5) | +0.5 |
| 2 | 5 | $\mu_{0,t}$ and "from scale zero" defined on p. 1; scale zero against the centre | +1 |
| 3 | 14 | the $\Cin$ rays by their profile; "their superpositions can" (with Re) | +0.5 |
| 4 | 1 | what the weaker axiom buys | +1.5 |
| 5 | 2 | the exclusions in "Scope"; "Scope" moved to p. 3 | +1.5 |
| 6 | 15 | the mixture before the Brownian motion in § 1; heading of § 2.3 | 0 |
| 7 | 9 | the lead of § 2.7 in one sentence (Ra) | −4 |
| 8 | 6 | $f_d$ against $p$; a row of Table 2 | +2 |
| 9 | 13 | the three parts of § 3.2; two run-in headings | +1.5 |
| 10 | 7 | the factor $L$ in the opening of § 3.3 (with Rd) | +1 |
| 11 | 10, 8 | the time against the scale; the caption's dictionary | +2.5 |
| 12 | 11 | § 3.4: the quoted sentence, the cone paper's letter, Rb | −2 |
| 13 | 4 | the sentence on what is outside the check; the heading; Rc | +0.5 |
| 14 | 16 | "none" in the caption of Table 1; "cited facts" defined in the plan | +1.5 |
| 15 | 17, 18 | both figures redrawn at their printed size by their scripts; the caption of Figure 1 | 0 |
| 16 | 19 | the entry paragraph of Appendix B | 0 (appendix) |
| 17 | 3 | the abstract, once, after the content response is planned | 0 (250 words) |

**Net change of the main text: about +8 lines, 0.16 page**, against a margin of 2 lines (0.04
page). The additions are about 19 lines and the removals that need no decision (Ra to Re) about 11.
So the list does not fit as it stands. It fits with Rf (−6 lines, net about +2, which is the
margin). Rf needs the dispatching session's word, because it reverses "the same items in four
places". The restructured Table 3 (Rg) or the blueprint batch (Rh) would pay as well. Without any
of them the edits that Rf pays for are held back: items 6, 13 and 16 and the caption sentence of
item 8 (6 lines). The rest then nets about +2 lines, and a build decides. Every figure here is an estimate to be replaced by
`records/affine/measure-section-pages.py` after the edits.

## List 2: items that need a decision or a change at the blueprint

1. **Item 20, the AI statement** (the author): the form of record as it stands, or without the
   ratio and the sentence on spare time. Both external reviews ask for the second.
2. **Item 8, Table 3** (the author, with the content response): four short columns with the anchors
   in an appendix table, and the figure and the table as two floats. It frees 12 to 16 lines of the
   main text. The content review changes the rows of the same table.
3. **Item 9, the notation batch at the blueprint**: the gauge ratio $c$ (Theorem 3.6 and
   Corollary 3.7; the affine paper prints the theorem), $s$ in Proposition 3.15, $\chi$ in the
   proof of record of Proposition 3.15, $x \le y$ in Proposition 3.11, $a$ in Lemma A.3(2) (the
   affine paper prints the lemma), $\lambda_d$ in Lemma A.4. Each is a letter, with the Lean
   docstrings and the two papers re-transcribed. Most are owed since Q-0310
   (`GATE-paper-iso.md`, items 1, 15, 16, 22).
4. **Item 12, Theorem 3.12**: leave the clause order (recommended), or split the theorem at the
   blueprint into the threshold and a proposition of estimates. The content review suggests moving
   clause (3) as well.
5. **Rf, the repetition of the two tiers** (the dispatching session): § 4's second paragraph, or
   the fourth paragraph of the opening of § 3.3, reduced to a pointer. This is what pays for
   List 1.
6. **Item 5, a schematic of the cascade** (the author): the one new figure the review asks for,
   about 0.1 page.
7. **Item 17, the size of Figure 1** (the author; open since the repositioning record, § 20
   item 2): a larger figure on its own, about a quarter of a page.
8. **Item 4, the heading "What is neither"** (the author, if the heading is the author's wording):
   "Outside the formal verification", or the present heading with the new sentence at the head.
9. **Item 19, the sentence on the three other axioms**: after the check that the content review
   asks for.

Declined outright, with no decision asked: the rename of "origin datum" (item 6), of "cited fact"
(item 16), of "delay", "bridge" and "subordinated slice" (item 15); the letters of the cited facts
(item 9); the Student-t clause as a remark (item 13); the reordering of the opening of § 3.4
(item 11); the reports moved to a supplement (item 19); Figure 1 beside the Matérn example
(item 17).

## What the review got wrong about the text

1. **Item 10.** "The introduction also uses $t$ for process time, while §3.3 switches to $\tau$."
   The time of the Lévy process is $\tau$ in § 1 too, on the pages cited
   (`01-introduction.tex:290-298`). The $t$ of p. 3 is the time of Sato's self-similar process in
   the paragraph on the classification, another process.
2. **Item 10.** "The necessary explanation … follows the table it explains." The caption of Table 3
   has its key sentence, and § 1 has the dictionary on pp. 3–4.
3. **Item 15.** The fault is cited for pp. 9–10 as well. § 2.3 already opens with the random
   variance and the average, as the review proposes. Only § 1 (p. 3) leads with the Brownian motion.
4. **Item 6.** "Explain $k_d(r)\,dr/r$ as the intensity assigned to a radial interval, then define
   $c = k_d(0+)$." Both are in the text (`03-isotropic.tex:478-480`, `515`).
5. **Item 4.** The contract sentence the review proposes is the third sentence of § 1.1. "Neither"
   is explained by the first sentence under the heading.
6. **Item 11.** Three of the four parts of the fix describe the text as it is: the second paragraph
   leads with the conclusion, $w_d$ is introduced as the largest admitted value, and the numerical
   history follows the theorem.
7. **Item 19.** The counts of seven, nine and twelve are reconciled in three consecutive sentences
   directly after "twelve" is first said, not "distributed".
8. **Item 5.** The phrase is not on p. 15. In § 1 it is introduced by use on p. 1 ("the kernel from
   scale zero to scale $t$"). The fault is the abstract and the missing symbol.
9. **Item 2.** Of the limits listed, "from scale zero" is in the abstract and on pp. 2–3 and 5, and
   the Student-t condition on p. 3. Only the list "Not treated" is on p. 30 alone.
10. **Item 3.** The order the review proposes for the abstract is the order it has.
11. **Item 17.** The bounded curve is labelled, in the legend.
12. **Item 12.** Not an error, an omission: the theorem's title, the opening before it and the
    first words after it all state the dichotomy.

What the review missed and this verification found: the float page of Figure 1 and Table 3 falls
inside a sentence (item 8); the header comment of § 3.3 describes an order of the dictionary and the
table that the source does not have (item 8); Figure 2 says "thresholds" where the paper says
"critical values" (item 18); the printed lettering of the two figures is 4.4 pt and 4.3 to 5.4 pt
(items 17, 18); "cited facts" is used before it is defined (item 16); the row for $\tau$ in Table 2
names § 3.3 only (item 10).

## Closing table

| item | the review's title, short | facts right? | disposition | touches |
|---|---|---|---|---|
| 1 | why relax the semigroup | yes | ACCEPT | prose of § 1; +1.5 lines |
| 2 | scope limits early | in part: three of the limits are already early | ACCEPT | prose of § 1; +1.5 lines |
| 3 | the abstract | yes for three sentences; the order is already the proposed one | ACCEPT IN PART | abstract, 250 words; overlaps the content review ("rate", novelty) |
| 4 | verification contract | in part: the contract sentence exists | ACCEPT IN PART | § 1.1 (trust-base region, prose only); heading for the author |
| 5 | "from scale zero"; a diagram | yes, but for p. 15 | ACCEPT IN PART | prose of § 1; the figure for the author |
| 6 | "origin datum" | in part: two of the three explanations exist | ACCEPT IN PART; rename DECLINED | prose of § 3.2, Table 2; the rename would touch a shared definition, the affine paper and Lean |
| 7 | the slowly varying factor | yes | ACCEPT IN PART | prose of § 3.3; § 1 unchanged |
| 8 | Table 3 | yes | ACCEPT IN PART; restructuring AUTHOR | caption now; the table with the content review |
| 9 | notation collisions, Table 2 | yes | ACCEPT IN PART | lead of § 2.7 now; shared statements and a proof of record at the blueprint; the affine paper; Lean docstrings |
| 10 | process time against scale | no on $t$ and $\tau$; in part on the order | ACCEPT IN PART | prose of § 3.3, caption, Table 2 |
| 11 | § 3.4's opening | in part: most of the fix is in the text | ACCEPT IN PART; reordering DECLINED | prose of § 3.4; −2 lines |
| 12 | clause order of Theorem 3.12 | yes | ACCEPT IN PART; reordering to a blueprint decision | headings and one sentence; the clause order is a shared statement |
| 13 | roadmap of § 3.2 | yes | ACCEPT IN PART | prose of § 3.2; the Student-t clause is shared and stays |
| 14 | the $\Cin$ rays | yes | ACCEPT | prose of § 1 and § 3.4; the abstract through item 3 |
| 15 | the bridge as a mixture | yes for p. 3, no for pp. 9–10 | ACCEPT IN PART | prose of § 1; heading of § 2.3 |
| 16 | Table 1 | yes | ACCEPT IN PART | caption of Table 1, plan of § 1 |
| 17 | Figure 1 | yes; lettering measured at 4.4 pt | ACCEPT IN PART; size AUTHOR | the script and the caption; no new figure; overlaps the content review (slope) |
| 18 | Figure 2 | yes; lettering 4.3 to 5.4 pt | ACCEPT IN PART | the script; no new figure |
| 19 | Appendix B | in part: the counts are reconciled together | ACCEPT IN PART | Appendix B (outside the budget); one sentence waits for a check; overlaps the content review |
| 20 | the AI statement | yes | AUTHOR | the statement of record, shared in form with the affine paper; overlaps the content review |
