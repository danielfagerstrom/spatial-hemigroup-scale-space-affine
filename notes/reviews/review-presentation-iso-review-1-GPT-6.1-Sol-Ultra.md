I read D:/research/hemigroup-iso/review-build-iso-review-1.pdf for the specified reader, without assessing mathematical correctness. Page references below are the printed page numbers.
By page 3, that reader can identify the headline results and the practical bounded-kernel versus spike distinction. The motivation for weakening the semigroup assumption and the limits of the scale-space claims are less clear. All four subsection openings in §3 already state a purpose; §3.1 is adequate. The largest gains would come from changing emphasis, reducing specialized vocabulary, and separating explanation from the literature and verification inventories.

1. Explain why a scale-space researcher should relax the semigroup assumption — pp. 1, 4.
Quote: “weakens this one axiom.”
Problem: The opening presents this as a development in the author’s series. The reader learns what was relaxed before learning what that relaxation permits.
Fix: Immediately explain the consequence: allowing stages to depend on both endpoint scales admits families beyond Gaussian and stable semigroups, including the Matérn examples. Then identify the two design questions investigated here: whether an exponent remains admissible in the required dimension, and whether its kernel has a finite central height.
2. Bring the substantive scope limits into the first three pages — pp. 5, 30.
Quote: “What the paper leaves open or does not treat is listed in §4.1.”
Problem: This postpones information needed to interpret the title and the opening claims. A scale-space reader may import familiar expectations about locality, extrema, or evolution equations.
Fix: Move the explicit exclusions from p. 30 into the opening summary: central-behaviour results concern \(\mu_{0,t}\); stages with positive starting scale are not examined; locality, extrema of the smoothed signal, and a multidimensional generator are not established. Retain the conditional status of the Student-t construction.
3. Rewrite the abstract around the present paper’s results — p. 1.
Quote: “The author’s earlier papers classified the apertures on the line”; “a spike, whose rate is given with its constant.”
Problem: Series history occupies the opening, while classification, applications, novelty qualifications, and verification compete in one dense paragraph. “Rate” also conceals the different forms of the conclusions below and at the threshold.
Fix: Use this order: class of cascades studied; classification; \(c>d\) criterion and its sampling consequence; strict dimensional restrictions; novelty and verification qualification. Distinguish the \(c<d\) asymptotic from the \(c=d\) truncated-integral characterization. Remove “line’s building blocks” unless those blocks are explained.
4. Give a plain-language verification contract before the detailed inventory — pp. 5–7.
Quote: “every proof is machine-checked”; “What is neither.”
Problem: The broad opening claim precedes its most important qualifications by two pages. “Neither” is especially obscure because the ensuing paragraph discusses several different kinds of evidence.
Fix: Begin: “Lean checks that the formal conclusions follow from the formal definitions and seven assumed external theorems.” Immediately state that the external theorems, worked applications, figure computations, and agreement between printed and formal statements are outside that check. Preserve the disclosure that agreement received AI review only and no human reviewed the formal statements. Rename the latter passage “Outside the formal verification.”
5. Define “from scale zero” once, and add the missing explanatory diagram — pp. 1–2, 15.
Quote: “kernels from scale zero.”
Problem: This recurring expression requires the reader to distinguish scale zero from the spatial origin, while also distinguishing a full smoothing kernel from an interscale stage. Neither existing figure explains that architecture.
Fix: Introduce “the kernel \(\mu_{0,t}\) that maps the original signal to scale \(t\).” Thereafter use \(\mu_{0,t}\) or “full smoothing kernel” where appropriate. Add a three-node cascade diagram showing the original signal, its record at \(s\), and its record at \(t\), with arrows labelled \(\mu_{0,s}\), \(\mu_{s,t}\), and \(\mu_{0,t}\).
6. Replace “origin datum” with vocabulary that explains its contents — pp. 18–19.
Quote: “Hence the name origin datum.”
Problem: The name emphasizes where one parameter is evaluated, rather than what the pair represents. “Polar profile,” “profile at the origin,” and kernel density can easily merge in a novice’s reading.
Fix: Introduce the pair as “a Gaussian coefficient and a radial Lévy profile.” State explicitly that \(f_d\) is the density of the jump-intensity measure, whereas \(p\) is the smoothing-kernel density. Explain \(k_d(r)\,dr/r\) as the intensity assigned to a radial interval, then define \(c=k_d(0+)\). A boxed dictionary would help more than another coined name.
7. Explain the slowly varying factor where the reader first needs it — pp. 2, 13, 25.
Quote: “the power at which the transform of the kernel falls off.”
Problem: This wording invites the reader to imagine a constant multiple of \(|\xi|^{-c}\). The later singularity formula requires understanding the additional factor \(L\), whose explanation is separated from the initial description of \(c\).
Fix: For finite \(c\), explain that the transform has a power factor \(\rho^{-c}\) multiplied by a slowly varying factor \(L(\rho)\). Give the ratio definition and a simple example such as a logarithm. Explicitly connect that same factor to the central density asymptotic. Keep the Tauberian theorem’s technical statement in §2.6.
8. Turn Table 3 into a comparison table instead of a literature survey in cells — p. 21.
Quote: “What is in print about the six statements of §3.3.”
Problem: Its comparison earns a place, but long source histories and clause references make the table difficult to scan. Together with Figure 1, it interrupts the opening explanation of \(c\) between pp. 20 and 22.
Fix: Retain columns for result, previously available scope, present scope, and principal source. Move detailed source locations and derivation qualifications into notes or an appendix. Place the table after the uninterrupted §3.3 introduction and the process-time dictionary. Shorten the cells before considering any font reduction.
9. Remove avoidable notation collisions and simplify Table 2 — pp. 13–14, 17, 47.
Quote: “Seven letters keep a second role inside a statement.”
Problem: The table documents collisions that could largely be eliminated. The principal \(c\) also denotes a gauge ratio and a local Tauberian constant; on p. 47, \(\chi\), previously the gauge, becomes a radial transform.
Fix: Reserve \(c\) for the decay index and \(\chi\) for the gauge. Rename the gauge multiplier and Tauberian amplitude, use \(H(\rho)\) for the transform in the proof, and use \(r\) for spatial distance. Rebuild Table 2 by subject, with one principal meaning and a definition reference per symbol. Move source-specific symbol translations into local notes.
10. Make the literature’s process time visibly distinct from imaging scale — pp. 3–4, 21–22.
Quote: “Table 3 needs a dictionary”; “the law at time \(\tau\) has the power \(\tau c\) in place of \(c\).”
Problem: The necessary explanation is present, but follows the table it explains. The introduction also uses \(t\) for process time, while §3.3 switches to \(\tau\).
Fix: Use \(\tau\) consistently for process time. Before Table 3, display the correspondence: fixed kernel \(e^{-F_d}\); process law \(e^{-\tau F_d}\), with decay index \(\tau c\); imaging-scale kernel \(e^{-F(\chi(t)|\xi|)}\). Explain that the last operation rescales frequency, whereas process time multiplies the exponent.
11. Make §3.4’s witness construction follow the result — pp. 27–28.
Quote: “So it is built like a subordinated exponent, and the witnesses of the theorem are not subordinated.”
Problem: The opening gives a useful question, then accumulates series history, subordination terminology, witnesses, and critical values before the reader has a simple picture of the construction.
Fix: Lead with the conclusion: some exponents lose the required self-decomposability at every dimensional step. Then introduce one explicit family with parameter \(w\), and define \(w_d\) as the largest permitted value in dimension \(d\). Explain the failure through loss of monotonicity of its radial profile. Move the earlier paper’s parameter convention and numerical history after the theorem.
12. Put the main boundedness statement first in Theorem 3.12 — pp. 20, 22–23.
Quote: “5. (The dichotomy.)”
Problem: The subsection opening explains the physical question, but the answer is the fifth clause of a theorem containing decay estimates, derivative regularity, a mixture construction, and Gaussian-blur estimates.
Fix: State the boundedness dichotomy first, followed by the smoothness consequence. Present the explicit mixture and blurred-kernel estimates as supporting results or separately labelled consequences. Rename §3.3 “Central boundedness and singularities,” making its subject immediately recognizable to an imaging reader.
13. Give §3.2 a roadmap matching its three different jobs — pp. 16–20.
Quote: “The second half of the subsection gives the class \(A_d\) … an explicit form.”
Problem: “Reduction to the line” promises a proof method, but the subsection also supplies a parameterization and several kernel constructions. Its strong projection-slice explanation is followed by less clearly signposted changes of purpose.
Fix: Identify three deliverables explicitly: classification by projections; a radial-profile test for admissibility; Gaussian-mixture examples. Give the latter two descriptive internal headings. Put the conditional Student-t clause in a clearly labelled remark so its qualifications do not interrupt the main construction.
14. Explain Cin rays through their profiles before using the name — pp. 3, 10–11, 29.
Quote: “members of the Cin rays, the extreme rays of the cone.”
Problem: This introduces two unfamiliar abstractions simultaneously. “Building blocks” then risks suggesting that excluding the individual blocks excludes their superpositions. The useful clarification arrives only on p. 29.
Fix: Initially call them “elementary exponents with step-shaped jump profiles on the line.” Introduce the Cin formula and extreme-ray terminology in §2.3. Bring forward the p. 29 clarification: individual rays fail in the plane, while suitable superpositions can remain admissible.
15. Present the “bridge” as a Gaussian variance mixture — pp. 3, 9–10, 20.
Quote: “Run a Brownian motion in \(R^d\) for such a random time.”
Problem: This asks the intended reader to enter process theory when the kernel construction can be understood directly. “Delay,” “bridge,” and “subordinated slice” then become additional vocabulary to retain.
Fix: Lead with: choose a random variance, average the corresponding centred Gaussian kernels, and obtain the stated transform. Explain afterward why the mixing variable is called a delay in the time-causal theory. Rename “The causal bridge” to “Gaussian variance mixtures and dimensional admissibility,” and retain the explanation of why the endpoint scales are squared.
16. Make Table 1 interpretable without proof-assistant experience — p. 7.
Quote: “every other statement”; “none.”
Problem: The trust-base table is legible and useful, but its second column mixes dependencies of checked implications with results establishing existence of the law or density. “None” can sound stronger than intended.
Fix: Separate those two kinds of dependency into columns. Add: “‘None’ means none of the external theorems C1–C7; definitions, hypotheses, and Lean’s logical foundations still apply.” Use “assumed external theorem” in place of “cited fact,” with descriptive names alongside the C labels.
17. Enlarge Figure 1 and label its visual lesson directly — p. 21.
Quote: “Here \(c=3/2\): the density is bounded on the line and unbounded in the plane and in space.”
Problem: This figure earns its place by showing the practical consequence, but the graphic is only roughly 7 cm wide. Axis and legend lettering are very small at print size, and the reader must infer which end represents approach to the centre.
Fix: Enlarge it substantially, with final lettering around 8–9 points or larger. Mark \(r\to0\), label the finite-height curve directly, and add slope guides to the two unbounded curves. Place it beside the Matérn example rather than the literature table.
18. Make Figure 2’s monotonicity failure conspicuous — p. 28.
Quote: “increasing on an interval for \(d=3\).”
Problem: Both panels are useful, but small legends and formula-heavy bound labels make the central argument harder to see than necessary. The decisive upward segment in panel (b) is subtle.
Fix: Enlarge or vertically stack the panels. Mark the interval where the \(d=3\) profile increases and annotate its significance for admissibility. Use line styles that remain distinct in grayscale, including the \(w=4\) reference line. Keep the caption’s distinction between plotted computations and proved statements.
19. Give Appendix B an ordinary-language entry point and reconcile its counts — pp. 55–58.
Quote: “one of the twelve axioms listed in blueprint/trust-boundary.txt.”
Problem: A novice moves from seven assumed theorems to twelve permitted axioms amid long declaration lists. The explanation exists, but is distributed across implementation-oriented prose.
Fix: Explain that a declaration is a named formal definition or result. State together: seven external theorems produce nine imported assumptions because C3 has three parts; three further assumptions belong to the companion development. Explicitly identify their status for this manuscript. Show one annotated dependency report, with a compact printed-result crosswalk; place full helper inventories and raw reports in the versioned supplement.
20. Replace the project diary in the AI disclosure with publication-relevant information — p. 58.
Quote: “the agents’ words outnumber mine by between twenty-one and forty-five to one.”
Problem: Word ratios, archived days, and “the module” address the author’s production process rather than a journal reader’s assessment. The autobiographical sentence about spare time adds another change of register.
Fix: Retain the extent of AI drafting and formalization, the allocation of decisions, the AI-only review, the absence of human review of formal statements, and the author’s responsibility. Move word-count statistics and process chronology to the repository record.
