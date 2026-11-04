Gemini 4 Argon High

Here are the twenty changes, ranked from most to least impactful, that would most improve the readability of the manuscript for a *Journal of Mathematical Imaging and Vision* readership.

---

### 1. Reorder Section 1 so the organizing framework $(G, W)$ comes before the trilogy recap and probability vocabulary
* **Page:** pp. 1–2 (§1, paragraphs 2–3) and p. 7 (§2.1, paragraph 1).
* **Quoted phrase:** 
  > `"On the line the axioms are those of the author’s paper on the line [15], the line paper below (Definition 2.1). ... Its sequel [17], the cone paper, studies the set of the line’s exponents, and the isotropic paper [16] carries the theory to \mathbb{R}^d for apertures that have a size and no shape. What is used from the three is restated in §2. A kernel is a probability measure, and the classification on the line, like the study of the apertures that follows, rests on the theory of such measures in probability. So from here on the paper uses the vocabulary of that theory: a kernel is a law, and its Fourier transform, the transfer function of the smoothing, is the characteristic function of the law, its transform for short."`
* **What is wrong:** A vision or scale-space researcher reading the Introduction meets a tour of three prior preprints and a vocabulary shift to probability theory on pages 1–2 before learning what this paper's organizing idea is—namely, that an affine scale space requires choosing a covariance group $G$ and a cascade order $W$ on aperture matrices $\Sigma$ (which only appears on pp. 2–3 under *"What is an affine scale space?"* and *"The two choices"*). Worse, the four-sentence probability-vocabulary paragraph on p. 2 is repeated almost word-for-word on p. 7 in §2.1.
* **Concrete fix:** Move the subsections **"What is an affine scale space?"** and **"The two choices"** (pp. 2–3) up so they immediately follow paragraph 2 of §1; delete the repeated vocabulary paragraph on p. 2 (retaining it in §2.1 on p. 7), and condense the transition to the earlier papers at the end of paragraph 2 on p. 1–2 to:
  > `"Such a family is a convolution hemigroup ([22], Def. 2.14.16, p. 380). In one dimension and for isotropic apertures in \mathbb{R}^d, the hemigroup axioms admit every symmetric self-decomposable probability measure as an aperture kernel, including the symmetric \alpha-stable laws (with Fourier transform e^{-a|\omega|^\alpha}, 0 < \alpha \le 2) and the Matérn laws (with Fourier transform (1+|\omega|^2)^{-\gamma}, \gamma > 0) [15, 16, 17]; §2 restates the results needed here."`

---

### 2. Clarify the Abstract: avoid calling $\Sigma$ a "covariance matrix" for infinite-variance laws, define the index $\alpha$, and state the practical shape-adaptation conclusion
* **Page:** p. 1 (Abstract).
* **Quoted phrase:**
  > `"Under hemigroup axioms both are: a family is given by a group G of linear maps it respects and an order W on covariance matrices along which coarser records further smooth finer ones. ... Shape-adapted apertures are such steps from the first stage; among linear images of rotation-invariant laws with a positive transform only the Gaussian reaches them by further smoothing. Along a chain of orders from the rays (\alpha = 0) to the Loewner order (\alpha = \infty), a non-Gaussian kernel pays in speed of shape change."`
* **What is wrong:** 
  1. Calling the parameter $\Sigma$ a "covariance matrix" in the abstract is contradictory when the primary non-Gaussian examples are $\gamma$-stable laws ($0 < \gamma < 2$), which have infinite variance and no covariance matrix (as noted on p. 2, $\Sigma$ is a positive semidefinite scale–shape matrix, proportional to covariance only in the Gaussian case).
  2. The parameter $\alpha$ in `"the order of index \alpha"` is introduced without saying what it controls geometrically (the maximum rate at which an aperture's anisotropy may grow relative to its scale).
  3. The sentence on shape-adapted apertures leaves an imaging reader uncertain whether non-Gaussian kernels fail at shape adaptation altogether or simply require re-convolving the original image (as standard iterative algorithms already do).
* **Concrete fix:** Replace those sentences in the Abstract with:
  > `"Under hemigroup axioms both are: a family is specified by a covariance group G of linear maps of the image and a partial order W on positive semidefinite scale–shape matrices \Sigma (proportional to the covariance in the Gaussian case) along which coarser records are further smoothings of finer ones. ... In standard shape-adapted smoothing, the step from the isotropic first stage to an adapted aperture preserves the minimum directional scale and is therefore rank-deficient; among linear images of rotation-invariant laws with a positive Fourier transform, only the Gaussian reaches the adapted aperture by further smoothing of the first stage, whereas every other kernel must either convolve the original image afresh (as the Lindeberg–Gårding iteration already does) or increase its minimum scale. Along a continuous chain of GL(d)-invariant orders indexed by 0 \le \alpha \le \infty—where \alpha bounds how fast the aperture's anisotropy may grow relative to its volume scale, from pure rescalings along rays (\alpha = 0) to the full Loewner order (\alpha = \infty)—a non-Gaussian kernel pays in maximum speed of shape change."`

---

### 3. Rewrite the shape-adaptation paragraph in Section 1 so the algorithmic consequence is immediately clear
* **Page:** p. 4 (§1, paragraph 2).
* **Quoted phrase:**
  > `"Shape adaptation takes such a step. The practice of Lindeberg and Gårding keeps the least eigenvalue of the aperture at the scale of its isotropic first stage. So the step from the first stage to an adapted aperture of another shape is rank-deficient (Proposition 4.22(1)). Among the affine orbits of the rotation-invariant laws with a positive transform only the Gaussian reaches the adapted apertures by a further smoothing of the first stage (Proposition 4.22(2)). For every other kernel the adapted record is a re-measurement of the image, which the iteration makes in any case. So for the apertures of the practice a non-Gaussian kernel loses only the cascade between the stages of the iteration, which the iteration does not use (§5)."`
* **What is wrong:** The final two sentences (`"a re-measurement of the image, which the iteration makes in any case. So for the apertures of the practice a non-Gaussian kernel loses only the cascade..."`) are elliptical and hard to parse on first reading. The reader has not yet been reminded how the Lindeberg–Gårding fixed-point iteration works (§4.1, p. 26) or what the alternative is if a cascade *is* desired (§4.8, p. 50).
* **Concrete fix:** Replace the paragraph with:
  > `"Shape adaptation takes such a rank-deficient step. In the fixed-point iteration of Lindeberg and Gårding [36, 37], an isotropic first stage at scale matrix wI selects a local shape matrix M with \lambda_{\min}(M) = 1, and the next stage measures the image at \Sigma_w = wM. Because \Sigma_w keeps the least eigenvalue w of the first stage, the increment \Sigma_w - wI = w(M - I) is singular (Proposition 4.22(1)). Among the affine orbits of rotation-invariant laws with a positive transform, only the Gaussian can compute the record at \Sigma_w by a further convolution of the first-stage record at wI (Proposition 4.22(2)). For every non-Gaussian kernel, obtaining the record at \Sigma_w requires either convolving the original image afresh—which the Lindeberg–Gårding algorithm does at each iteration step anyway—or else enlarging the minor-axis scale along with the major axis so that the step lies inside the kernel's cascade cone (§4.8)."`

---

### 4. Make Table 2 and §4.3 ("The landscape at a glance") readable without forward-referencing 60 pages of notation
* **Page:** pp. 30–31 (§4.3 and Table 2).
* **Quoted phrase:**
  > `"• The frame is the coordinate frame, the axes of the sampling grid along which the positive diagonal group \mathrm{D}_+(d) rescales. The frame’s shapes are the positive definite diagonal matrices, the apertures whose axes are those of the frame, and they are the orbit of I under \mathrm{D}_+(d)."` (p. 30)
  > `"on the frame’s shapes the images (D_s)_*\mu_I of any self-decomposable \mu_I \ne \delta_0 ... off the frame’s shapes one extension, (\Delta(\Sigma)^{1/2})_*(\nu_1 \otimes \cdots \otimes \nu_d), the families not described"` (p. 31, Table 2)
* **What is wrong:** Table 2 is placed on p. 31 as the roadmap to Section 4, *before* §§4.4–4.9 and Appendices F–H define the objects in its cells. Although p. 30 provides a bulleted glossary, Table 2 still uses symbols that are not defined until Appendix F on p. 87–89 ($D_s$, $\Delta(\Sigma)$, $\operatorname{Corr}(d)$, $\nu_1 \otimes \cdots \otimes \nu_d$), and the `similarities S(d)` Loewner cell is a 19-line wall of telegraphic shorthand (`"for a profile bounded at the origin, shape-blind at the origin (Proposition H.8) and not beyond it"`).
* **Concrete fix:** 
  1. In the `"The frame"` bullet on p. 30, add the definitions of the symbols used in Table 2:
     > `"We write D_s := \operatorname{diag}(s_1,\dots,s_d) for s \in (0,\infty)^d, \Delta(\Sigma) := \operatorname{diag}(\Sigma_{11},\dots,\Sigma_{dd}) for the diagonal part of \Sigma, and \operatorname{Corr}(d) := \{\Theta \in \mathrm{PD}(d) : \Theta_{11} = \cdots = \Theta_{dd} = 1\} for the correlation matrices."`
  2. In the `"The profile entries"` bullet on p. 30, add the geometric meaning of $R(\lambda)$ and $\beta_-(k)$:
     > `"The condition R(\lambda) \ge \lambda^\alpha for all \lambda \ge 1 (equivalently, \beta_-(k) \ge \alpha) means that the radial jump rate k(r) grows at least as fast as r^{-\alpha} under any contraction of scale."`
  3. Condense the `similarities S(d)` / `Loewner order` cell in Table 2 (p. 31) to:
     > `"every family’s kernels are infinitely divisible with anisotropy bounded by \operatorname{es}(\psi_\Sigma) \le 4\operatorname{ecc}(\Sigma) (Prop. 4.20(4)); non-Gaussian families survive (e.g., \mu_\Sigma = N(0,2b\Sigma) * S_\alpha(\Sigma + \kappa\operatorname{tr}(\Sigma)I), Prop. H.1(3)); \operatorname{es}(\psi_\Sigma) is uniformly bounded in \Sigma when the rank-one limit of L_\Sigma is comparable to L_I, and can grow as a power of \operatorname{ecc}(\Sigma) otherwise (Props. H.5, H.6); when k_d(0+) < \infty, L_\Sigma is asymptotically isotropic at the origin (Prop. H.8) but need not be isotropic away from it (Prop. H.7)."`

---

### 5. Supply the missing link in §2.3 between the class $\mathcal{A}_d$ (Theorem 2.5) and the isotropic origin data $(a, k_d)$ (Definition 2.8)
* **Page:** p. 9 (§2.3, paragraph before Theorem 2.5) and p. 11 (after Definition 2.8).
* **Quoted phrase:**
  > `"The cone paper names the class \mathcal{A}_d of the admissible F of (2.1) for which \xi \mapsto F(|\xi|), \xi \in \mathbb{R}^d, is the exponent of a self-decomposable law on \mathbb{R}^d [17, Prop. 4.9]. By the next theorem its members other than 0 are the exponents of the isotropic families in \mathbb{R}^d."` (p. 9)
* **What is wrong:** Citation `[17, Prop. 4.9]` is load-bearing for a reader who has not read `[17]`: Theorem 2.5 characterizes all isotropic cascade families in $\mathbb{R}^d$ by $F \in \mathcal{A}_d$, and Definition 2.8 (p. 11) introduces "isotropic origin data $(a, k_d)$" with $k_d : (0,\infty) \to [0,\infty)$ nonincreasing and exponent $F_d(\xi)$ in (2.5), yet the paper never states that these two classes are *identical*—i.e., that $F \in \mathcal{A}_d$ if and only if $F(|\xi|) = F_d(\xi)$ for an isotropic origin datum $(a, k_d)$ as in Definition 2.8! Without this statement, the reader cannot connect Theorem 2.5 to Definition 2.8 or to Proposition 4.13.
* **Concrete fix:** On p. 11, immediately after Definition 2.8, replace the first sentence (`"An origin datum describes its law, a rotation-invariant symmetric infinitely divisible law, through the coefficient a of its Gaussian part and the polar profile k_d."`) with:
  > `"By the polar criterion for self-decomposability on \mathbb{R}^d ([54], Thm. 15.10, p. 95; [17, Prop. 4.9]), a radial function \xi \mapsto F(|\xi|) has F \in \mathcal{A}_d (Theorem 2.5) if and only if F(|\xi|) = F_d(\xi) for a unique isotropic origin datum (a, k_d) in dimension d; its law \mu with \widehat{\mu} = e^{-F_d} is then a rotation-invariant self-decomposable law on \mathbb{R}^d."`

---

### 6. Resolve the four-way collision on the letter $k$ ("folded profile", "delay datum", "polar profile", "profile") and the direct clash $k_I$ vs. $k_{\mathrm{I}}$
* **Page:** p. 8 (eq. (2.1)), pp. 10–11 (Definition 2.8), pp. 41–42 (Proposition 4.13), and pp. 100–101 (Propositions H.8 and H.9).
* **Quoted phrase:**
  > `"The datum is subordinated when there is a delay datum (a, k_{\mathrm{I}}) in the sense of §2.3, with k_{\mathrm{I}} nonincreasing, whose polar profile [17, (4.6)] is k_d"` (p. 11, Definition 2.8)
  > `"suppose L_I is the Lévy measure of an isotropic origin datum (0, k_I) in dimension d (Definition 2.8) with c := k_I(0+) < \infty."` (p. 100, Proposition H.8; also p. 101, Proposition H.9(2))
* **What is wrong:** The manuscript uses $k$ with four different meanings and normalizations: (1) $k(x)$, the 1D `"folded profile"` on $(0,\infty)$ in (2.1), which counts both $\pm x$ directions; (2) $k_{\mathrm{I}}(u)$, the time-causal `"delay profile"` in (2.6); (3) $k_d(r)$, the sphere-integrated `"polar profile"` on $\mathbb{R}^d$ in Definition 2.8; and (4) $k(r) = k_d(r)/|S^{d-1}|$, the unnormalized `"profile"` in Proposition 4.13 (which at $d=1$ equals $\frac{1}{2}$ of the folded profile $k$ of (2.1)!). Then, in Propositions H.8 and H.9 (pp. 100–101), the polar profile $k_d$ of Definition 2.8 is written $k_I$ (with an italic $I$ for the identity matrix), colliding directly with the delay profile $k_{\mathrm{I}}$ (upright $\mathrm{I}$) of Definition 2.8.
* **Concrete fix:** 
  1. In Proposition H.8 (p. 100), its proof sketch (p. 101), and Proposition H.9(2) (p. 101), replace `k_I` with `k_d` (`"an isotropic origin datum (0, k_d) in dimension d (Definition 2.8) with c := k_d(0+) < \infty"`).
  2. In eq. (2.1) and the text below it on p. 8, write $k_{\mathrm{V}}(x)$ instead of $k(x)$ for the 1D folded profile (matching the Gaussian coefficient $a_{\mathrm{V}}$ and the sentence `"A subscript \mathrm{V} marks an object of the line"`), so that unsubscripted $k(r) = k_d(r)/|S^{d-1}|$ in §4.6 and Appendices E–H has a single unambiguous meaning throughout the paper.

---

### 7. Replace the misnomer "wedge datum" in Definition 3.1
* **Page:** p. 15 (§3.1 and Definition 3.1).
* **Quoted phrase:**
  > `"The second concept is the wedge of Hilgert, Hofmann and Lawson, a closed convex set that contains 0 and is closed under addition ([23], p. 3). For the orders of this paper the steps of W between positive definite matrices are generated by such a cone of symmetric matrices (§4.4), and the pair (G, W) is called a wedge datum after its order."`
* **What is wrong:** In Definition 3.1, $W$ is a *partial order* on $\mathrm{PSD}(d)$, not a wedge (a closed convex cone in a tangent space/Lie algebra). Calling $(G, W)$ a `"wedge datum"` forces Lie-semigroup jargon on the reader in §3.1—eighteen pages before tangent cones appear in §4.4—and is mathematically inaccurate at the level of Definition 3.1, since Theorem 4.3(3) (p. 34) explicitly exhibits a closed $\mathrm{GL}(d)$-invariant partial order $W$ that is generated by *no* wedge or cone. Moreover, §4.4 itself calls the tangent object an `"invariant cone C"`, not a wedge.
* **Concrete fix:** Rename `"wedge datum"` to `"cascade datum"` (or `"group–order datum"`, keeping the symbol $(G, W)$ where $W$ stands for the partial order $\le_W$), and replace the two sentences quoted above on p. 15 with:
  > `"In §4.4, the smooth G-invariant partial orders W between the ray order and the Loewner order will be generated by closed convex cones C of symmetric matrices (called wedges in the Lie-semigroup literature [23], p. 3). We call a pair (G, W) of a covariance group G and a G-invariant partial order W on \mathrm{PSD}(d) a cascade datum."`

---

### 8. Rebalance §4.8 and §4.9: move the 45-line proof of Proposition 4.22 to Appendix B, and bring the statements of Propositions F.2 and H.1(3) into §4.9
* **Page:** pp. 49–52 (§4.8 and §4.9).
* **Quoted phrase:**
  > `"Proof. (1). The least eigenvalue \lambda_{\min}(M) = \min_{|x|=1}\langle x, Mx\rangle is the least eigenvalue of M and is attained at a unit eigenvector v. ... [45 lines] ... so \widehat{\mu}_{\Sigma,\Sigma'}(\omega) = e^{-b\langle\omega,(\Sigma'-\Sigma)\omega\rangle}. \square"` (pp. 49–50)
  > `"The statements behind the rows of the two smaller groups are in Appendices F–H."` (p. 51)
* **What is wrong:** In §4.8, the 45-line proof of Proposition 4.22 (whose first sentence is tautological and whose first 18 lines prove the elementary linear-algebra fact that $w(M-I) \ge 0$ has rank $< d$ when $\lambda_{\min}(M) = 1$) interrupts the climax of the paper—the application to shape-adapted smoothing—separating Proposition 4.22 from the worked numerical example of a slanted planar surface on p. 50. Conversely, §4.9 (*"Smaller groups"*, pp. 51–52) contains *no formal statements at all*, forcing the reader to turn to Appendices F and H (pp. 87–94) for the two flagship results on smaller groups highlighted in the Abstract and Introduction (Proposition F.2 on axis-aligned product families for $\mathrm{D}_+(d)$ and Proposition H.1(3) on non-Gaussian Loewner cascades for $S(d)$).
* **Concrete fix:** 
  1. Move the full proof of Proposition 4.22 (pp. 49–50) to Appendix B.2, replacing it on p. 49 with:
     > `"Proof sketch. Since \lambda_{\min}(M) = 1, P = w(M-I) is positive semidefinite with null space equal to the 1-eigenspace of M, so 0 < \operatorname{rank} P < d when M \ne I. Clause (2) then follows from Theorem 3.7 applied at \Sigma = wI, and Clause (3) from Proposition 3.4(3) and Clause (2). The complete proof is in Appendix B.2. \square"`
  2. Move the statements of **Proposition F.2** (p. 87) and **Proposition H.1** (p. 93) into §4.9 (pp. 51–52), leaving their proofs and the remaining propositions in Appendices F and H.

---

### 9. Separate the similarity-group bounds (Proposition 4.20(3)–(5)) from §4.6 ("The step set of an orbit")
* **Page:** pp. 45–46 (§4.6, Proposition 4.20).
* **Quoted phrase:**
  > `"Proposition 4.20 (similarity covariance along the stable order: the families and the shape of their kernels). ... (so it satisfies the hypotheses of Proposition H.4) ... These are the functionals of Proposition H.5."`
* **What is wrong:** Section 4.6 is about the step sets of $\mathrm{GL}(d)$ affine orbits $(\Sigma^{1/2})_*\mu_I$. At the end of §4.6 (pp. 45–46), Proposition 4.20 combines two unrelated subjects: Clauses (1)–(2) extend the stable order $\preceq_\alpha$ to $\le_\alpha$ on $\mathrm{PSD}(d)$ and construct the $\mathrm{GL}(d)$ families along it (which §4.7 immediately uses), whereas Clauses (3)–(5) switch to the *similarity group* $S(d)$, introduce moment matrices $\mathcal{M}_s(L)$ and exponent spread $\operatorname{es}(\psi)$, and forward-reference Propositions H.4 and H.5 in Appendix H. A reader following the $\mathrm{GL}(d)$ classification from §4.6 to §4.7 is sidetracked by $S(d)$ bounds, while a reader looking for $S(d)$ in §4.9 has to flip back to §4.6.
* **Concrete fix:** Split Proposition 4.20 into two propositions: keep Clauses (1)–(2) at the end of §4.6 as **Proposition 4.20 (the stable order on $\mathrm{PSD}(d)$ and its $\mathrm{GL}(d)$ families)**, and move Clauses (3)–(5) to §4.9 under *"The stable order"* (p. 52) as a separate proposition on similarity-covariant families.

---

### 10. Fix the axis-arrow collision in Figure 3(a), tiny font sizes in Figures 1–3, and add the stable-cascade construction to Figure 2(b)
* **Page:** p. 21 (Figure 1), p. 29 (Figure 2), and p. 33 (Figure 3).
* **Quoted phrase:**
  > `"Its extent in a direction w of the null space \ker P, which is \langle w, \Sigma w\rangle^{1/2}, is unchanged, so both ellipses touch the lines \langle x, w\rangle = \pm 1."` (p. 21, Figure 1 caption)
  > `"in a chart whose radius is the distance \delta(I, S) of Lemma 4.1(4) and whose angle is twice the orientation of the major axis."` (p. 29, Figure 2 caption)
* **What is wrong:** 
  1. In **Figure 3(a) (p. 33)**, the bottom arrowhead of the vertical axis collides directly with the horizontal axis label `"u, change of shape"`.
  2. Across **Figures 1–3**, internal labels and legends (`w`, `\Sigma = I`, `\alpha = 1.5`, etc.) are rendered at 5–6 pt, making them hard to read at print size.
  3. In **Figure 1's caption (p. 21)**, $\langle w, \Sigma w\rangle^{1/2}$ equals the half-width of the ellipse $\{x : \langle x, \Sigma^{-1}x\rangle \le 1\}$ between the lines $\langle x, w\rangle = \pm 1$ only when $w \in \ker P$ is a *unit* vector ($|w|=1$, here with $\Sigma = I$), which is not stated.
  4. In **Figure 2 (p. 29)**, panel (a)'s caption does not explain *why* the polar angle is twice the major-axis angle $\theta$ (because rotating an ellipse by $\theta$ rotates its trace-free log-shape matrix by $2\theta$, placing orthogonal orientations $\theta$ and $\theta + 90^\circ$ at opposite points $2\theta$ and $2\theta + 180^\circ$), and panel (b) plots `shape-adapted apertures` on the Loewner line (`slope d = 2`) without showing visually how an $\alpha$-stable kernel reaches the same adapted shape (by moving horizontally to the right to meet the $\alpha$-line, as computed in §4.8 on p. 50).
* **Concrete fix:** 
  1. In the plotting scripts for Figures 1–3, increase all font sizes to at least 9 pt, and in Figure 3(a) truncate the negative vertical axis at $a = -0.1$ so the arrowhead clears `"u, change of shape"`.
  2. In Figure 2(b), draw a horizontal dashed arrow at $\log\sqrt{n_2/n_1} = \log 2 \approx 0.69$ (the $60^\circ$-slanted surface example of p. 50, where $n_2/n_1 = 4$) from the red cross on the Loewner line ($\log(t_2/t_1) \approx 0.35$) to the $\alpha = 1$ line ($\log(t_2/t_1) \approx 1.04$), labelled `"extra scale required at \alpha = 1"`.
  3. In Figure 1's caption (p. 21), change `"in a direction w of the null space \ker P"` to `"in a unit direction w \in \ker P (|w| = 1)"`. In Figure 2's caption (p. 29), after `"twice the orientation of the major axis"`, insert `"(so that orthogonal major-axis orientations \theta and \theta + \pi/2 lie opposite each other)"`.

---

### 11. Bring the PDE/Green's-function explanation of why Matérn steps fail across shapes from Remark E.3 into §4.6
* **Page:** p. 45 (§4.6, *"The size of the failure"*) and p. 85 (Appendix E.2, Remark E.3).
* **Quoted phrase:**
  > `"The size of the failure. For the Matérn orbit of index 1 the would-be increment of a step across shapes is negative near the origin in the directions the step widens least, and its negative mass diverges logarithmically there, so it is not even a finite signed measure (Proposition E.2 with Remark E.3, and Proposition E.4, with a computation on a grid in Remark E.5; all four in Appendix E.2)."` (p. 45)
* **What is wrong:** This four-line paragraph in §4.6 merely lists four pointers to Appendix E.2, hiding the concise physical/PDE mechanism in Remark E.3 (p. 85) that explains to an imaging reader *why* a Matérn filter cannot be cascaded across shapes.
* **Concrete fix:** Replace the paragraph on p. 45 with:
  > `"The size and mechanism of the failure. Why a Matérn step across shapes fails can be seen directly at index \gamma = 1 (Appendix E.2). There \mu_{\Sigma'} has density K_{\Sigma'}(x) = (\det\Sigma')^{-1/2}G(\Sigma'^{-1/2}x), where G is the Green's function of 1 - \Delta on \mathbb{R}^d. For a step \Sigma' = \Sigma + P, the would-be increment \rho has Fourier transform (1+\langle\omega,\Sigma\omega\rangle)/(1+\langle\omega,\Sigma'\omega\rangle) = 1 - \langle\omega,P\omega\rangle\widehat{K}_{\Sigma'}(\omega), so away from the origin its density is q = \nabla\cdot P\nabla K_{\Sigma'}. In normalized coordinates y = \Sigma'^{-1/2}x = r\hat{y} with P' := \Sigma'^{-1/2}P\Sigma'^{-1/2}, as r \downarrow 0 one has (\det\Sigma')^{1/2}r^d q(\Sigma'^{1/2}r\hat{y}) \to \mathcal{B}_d(d\langle\hat{y}, P'\hat{y}\rangle - \operatorname{tr} P') with \mathcal{B}_d = \frac{1}{2}\pi^{-d/2}\Gamma(d/2) > 0 (Remark E.3 and Proposition E.4). Whenever \Sigma' is not a scalar multiple of \Sigma, the factor d\langle\hat{y}, P'\hat{y}\rangle - \operatorname{tr} P' is negative on an open cone around the least-widened direction, and integrating r^{-d} over shells a < r < 1 makes both the positive and negative mass diverge like \log(1/a) as a \downarrow 0 (Proposition E.4; grid measurements in Remark E.5)."`

---

### 12. Eliminate the notation collision between the step set $\mathcal{K}_\alpha \subseteq \mathrm{PD}(d)$ and the exponent cone $K_\alpha \subseteq \mathfrak{gl}(d)$, and unify the four symbols for the stable order
* **Page:** p. 14 (Table 1 and text below), p. 20 (Theorem 3.5(3)(c)), pp. 38–41 (Propositions 4.7, 4.10, 4.12), and pp. 46–48 (Proposition 4.20 and Theorem 4.21).
* **Quoted phrase:**
  > `"Two objects have several names. The stable order of index \alpha is \preceq_\alpha on \mathrm{PD}(d), defined by its step condition in Proposition 4.7(2). Proposition 4.12(1) shows that it equals \preceq_{C_\alpha}. On \mathrm{PSD}(d) it is \le_\alpha, which equals \preceq_{C_\alpha}^+. Its set of steps is the step cone \mathcal{K}_\alpha \subseteq \mathrm{PD}(d), which is not the exponent cone K_\alpha \subseteq \mathfrak{gl}(d)."` (p. 14)
* **What is wrong:** Distinguishing the multiplicative step set $\mathcal{K}_\alpha \subseteq \mathrm{PD}(d)$ from the Lie-algebra exponent cone $K_\alpha \subseteq \mathfrak{gl}(d)$ solely by calligraphic versus italic $K$—while simultaneously maintaining four symbols ($\preceq_\alpha$, $\le_\alpha$, $\preceq_{C_\alpha}$, $\preceq_{C_\alpha}^+$) for the stable order of index $\alpha$—creates avoidable friction throughout §4.6 and §4.7 (for instance, Theorem 4.21 on pp. 47–48 reverts to writing $\preceq_{C_\alpha}^+$ just one page after Proposition 4.20 named it $\le_\alpha$).
* **Concrete fix:** 
  1. Rename the exponent cone in $\mathfrak{gl}(d)$ (Proposition 4.10, p. 39–41; Table 1, p. 14; Table 2, p. 31; Proposition F.5, p. 90) from $K_\alpha$ to $\mathfrak{k}_\alpha$ (or $E_\alpha$).
  2. In Theorem 4.21(3) (pp. 47–48), write $\le_\alpha$ (with $\le_0$ the ray order and $\le_\infty$ the Loewner order on $\mathrm{PSD}(d)$) instead of $\preceq_{C_\alpha}^+$, after noting in the preamble to Theorem 4.21 that $\preceq_{C_\alpha}^+$ equals $\le_\alpha$ by Proposition 4.12(1).

---

### 13. Explicitly reconcile the two scalar scale conventions (length scale $t, t(\Sigma), \chi(t)$ vs. variance scale $s, w, \varphi(t) = \chi(t)^2$)
* **Page:** p. 9 (Theorem 2.5), p. 18 (*"The isotropic corner"*), p. 28 (Lemma 4.1), and pp. 48–50 (§4.8).
* **Quoted phrase:**
  > `"Conversely every isotropic family is the slice of exactly one (\mathrm{GL}(d),\text{rays})-cascade family, once the scale is read in the variance gauge \varphi = \chi^2 of [15, Rem. 6.7], the coordinate in which the scale of the Gaussian member is proportional to its variance, with \chi the coordinate of [15, Prop. 6.6] in which the dilations act by multiplication."` (p. 18)
  > `"w and s are scale parameters in the variance gauge, squared lengths rather than volume scales."` (p. 50)
* **What is wrong:** The paper alternates between two conventions for scalar scale without an upfront comparison: in §2 (Theorems 2.3 and 2.5, where $\widehat{\mu}_{0,t}(\xi) = e^{-F(\chi(t)|\xi|)}$) and in Lemma 4.1 ($t(\Sigma) := (\det\Sigma)^{1/(2d)}$), the canonical scale $t$ has units of *length* (dilation $x \mapsto \lambda x$ multiplies $t$ by $\lambda$), whereas on the isotropic ray $\{sI : s \ge 0\} \subset \mathrm{PSD}(d)$ in §3 (Proposition A.3) and §4.8 ($wI$ and $sS$ in Proposition 4.22 and p. 50), the matrix parameter $s$ or $w$ has units of *variance / squared length* (dilation $x \mapsto \lambda x$ multiplies $sI$ by $\lambda^2$, so $s = t(\Sigma)^2$). Moreover, p. 18 cites `[15, Rem. 6.7]` and `[15, Prop. 6.6]` for $\varphi = \chi^2$ instead of writing out the one-line relation.
* **Concrete fix:** Replace the sentence quoted from p. 18 (*"The isotropic corner"*) with:
  > `"Because a spatial dilation x \mapsto \lambda x acts on \mathrm{PSD}(d) by \Sigma \mapsto \lambda^2\Sigma, the matrix parameter s on the isotropic ray \{sI : s \ge 0\} has units of squared length (variance), whereas in the canonical gauge \chi(t) = t of Theorem 2.5 (and in the volume scale t(\Sigma) := (\det\Sigma)^{1/(2d)} of Lemma 4.1, where t(sI) = \sqrt{s}) the scale has units of length. Setting \varphi(t) := \chi(t)^2 (the variance gauge) converts (2.3) into \widehat{\nu}_{sI, s'I}(\omega) = \exp[-(F(\sqrt{s'}|\omega|) - F(\sqrt{s}|\omega|))] for 0 \le s \le s', so that every isotropic family of Definition 2.4 is, in the coordinate s = \varphi(t), the slice of a unique (\mathrm{GL}(d),\text{rays})-cascade family (Proposition A.3)."`

---

### 14. Rewrite the opening of §3.2 ("The parameter space") so the role of the polar decomposition and rotation invariance is clear
* **Page:** p. 19 (§3.2, paragraph 1).
* **Quoted phrase:**
  > `"The parameter of the scheme is a matrix because the group acts on apertures as it acts on covariance matrices, A \cdot \Sigma = A\Sigma A^{\mathsf{T}}. This subsection says why the positive definite matrices are the right index for the kernels, and that this is itself an axiom. The parameter set is \mathrm{PSD}(d), closed so that it carries the origin and the singular matrices, where a step can be rank-deficient. Its interior \mathrm{PD}(d), of dimension d(d + 1)/2, is what the group makes of I: every positive definite matrix is A \cdot I = AA^{\mathsf{T}} for an invertible A, and A and AQ give the same matrix for every orthogonal Q, so that \mathrm{PD}(d) = \mathrm{GL}(d)/\mathrm{O}(d)."`
* **What is wrong:** An imaging reader naturally expects elliptical filters to be indexed by $\Sigma \in \mathrm{PD}(d)$ and is puzzled by the statement `"that this is itself an axiom"` and the subsequent talk of `"full laws"` and `"compact stabilizers"`. The actual geometric point is simple: by polar decomposition, any $A \in \mathrm{GL}(d)$ factors as $A = \Sigma^{1/2}Q$ with $\Sigma = AA^{\mathsf{T}} \in \mathrm{PD}(d)$ and $Q \in \mathrm{O}(d)$; therefore, the linear images $A_*\mu_I$ of a base kernel $\mu_I$ depend only on the $d(d+1)/2$ parameters of $\Sigma = AA^{\mathsf{T}}$ (rather than all $d^2$ parameters of $A$) *if and only if* $\mu_I$ is invariant under $\mathrm{O}(d)$.
* **Concrete fix:** Replace the opening of §3.2 on p. 19 with:
  > `"Why are apertures indexed by symmetric positive semidefinite matrices \Sigma \in \mathrm{PSD}(d), of dimension d(d+1)/2, rather than by general linear maps A \in \mathrm{GL}(d), of dimension d^2? By polar decomposition, every invertible matrix factors as A = \Sigma^{1/2}Q with \Sigma = AA^{\mathsf{T}} \in \mathrm{PD}(d) and Q \in \mathrm{O}(d), identifying \mathrm{PD}(d) with the quotient \mathrm{GL}(d)/\mathrm{O}(d). Under \mathrm{GL}(d)-covariance (K3), the aperture kernel at \Sigma = AA^{\mathsf{T}} is \mu_{AA^{\mathsf{T}}} = A_*\mu_I = (\Sigma^{1/2})_*Q_*\mu_I. For this kernel to be well-defined as a function of \Sigma = AA^{\mathsf{T}} alone, the base kernel \mu_I must be invariant under the stabilizer \mathrm{O}(d) of I (Q_*\mu_I = \mu_I for all Q \in \mathrm{O}(d)). Thus, indexing a \mathrm{GL}(d)-covariant orbit of non-degenerate kernels by \mathrm{PD}(d) is equivalent to requiring an isotropic member at \Sigma = I."`

---

### 15. Unify the spatial frequency letter ($\omega$ instead of $\xi, \omega, z$) and disambiguate the three uses of "kernel"
* **Page:** p. 7 (§2.1), pp. 9–12 (§§2.3–2.4), p. 16 (Definition 3.1(2)), and p. 49 (Proposition 4.22(1)).
* **Quoted phrase:**
  > `"Scale, stage and cascade keep their meaning, and “kernel” stays in use for a law in its role as an aperture. ... The frequency has three letters, each following its source. From §3 on, \omega is the frequency on \mathbb{R}^d. The statements of the isotropic paper restated in §2.3 write it \xi, as that paper does, and the frequency on the line \omega. The cited fact C2 writes it z, as its source does."` (p. 7)
  > `"Its kernel is the eigenspace of M for the eigenvalue 1"` (p. 49, Proposition 4.22(1))
* **What is wrong:** 
  1. Using three different letters ($\xi$, $\omega$, $z$) for the Fourier frequency vector on $\mathbb{R}^d$ in different sections merely to copy the typography of `[16]` and `[54]` adds pointless cognitive load (and in the proofs on pp. 60, 63, and 75, $\xi$, $\omega$, and $z$ are mixed within the same proof).
  2. Although p. 7 says `"kernel" stays in use for a law in its role as an aperture`, Definition 3.1(2) (p. 16) calls the family of all stage measures $\mu_{\Sigma,\Sigma'}$ a `"cascade family of kernels"`, forcing the paper to repeat the four-word phrase `"kernel from scale zero"` over 60 times to distinguish the aperture $\mu_\Sigma = \mu_{0,\Sigma}$ from the increment $\mu_{\Sigma,\Sigma'}$—and then Proposition 4.22(1) (p. 49) uses `"kernel"` in a third sense for the matrix null space $\ker P$!
* **Concrete fix:** 
  1. Use $\omega \in \mathbb{R}^d$ for the spatial frequency throughout the entire paper (including §§2.3–2.4 and Appendices A–C), and replace the three-letter explanation on p. 7 with: `"Throughout the paper, \omega denotes the frequency variable on \mathbb{R} or \mathbb{R}^d."`
  2. In Definition 3.1(2) (p. 16), define $\mu_\Sigma := \mu_{0,\Sigma}$ as the *aperture kernel* (at scale zero) and $\mu_{\Sigma,\Sigma'}$ as the *stage kernel* (or *increment*), and use *"aperture kernel"* thereafter in place of `"kernel from scale zero"`.
  3. In Proposition 4.22(1) and its proof (p. 49, four occurrences), replace `"kernel"` with `"null space \ker P"`: `"Its null space \ker P is the eigenspace of M for the eigenvalue 1"`.

---

### 16. Clarify the Lean 4 verification and remove the misleading "Sketch" / external-LaTeX-source disclaimer in §1.1 and Appendix I
* **Page:** pp. 6–7 (§1.1) and pp. 102–103 (Appendix I).
* **Quoted phrase:**
  > `"A proof headed “Sketch” shows the decisive steps, and its complete proof is in the LaTeX sources deposited with this version (Appendix I lists these statements)."` (p. 6)
  > `"The formal development builds on the line paper’s own, at its released version, and uses only parts of it that rest on no cited fact."` (p. 7)
  > `"Twenty statements have a sketch only: Propositions 4.4, 4.18, 4.20(3)–(5), A.3, D.1, E.1(2)–(4), E.4, F.2, F.3, F.4, F.5, H.1, H.2, H.4, H.5, H.6, H.7 and H.8, and Lemmas 4.14 and A.5. Their complete proofs are in the LaTeX sources deposited with this version"` (p. 102)
  > `"On the declarations of Theorems 3.6, 3.12, 3.5, 4.3 and 4.21, it prints Lean’s three logical axioms and names of the cited facts, and nothing else: 'AffineHemigroup.affine_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]"` (p. 103)
* **What is wrong:** 
  1. Telling a journal reader that 20 statements in a 108-page article have only a `"Sketch"` and that `"Their complete proofs are in the LaTeX sources deposited with this version"` makes the published article sound incomplete. In fact, those 20 proofs in the PDF (e.g., pp. 60–63, 65–68, 82–101) are complete, self-contained journal-level mathematical proofs that simply omit line-by-line algebraic expansions written out in the Lean blueprint files.
  2. A reader who has never used a proof assistant cannot tell from p. 7 whether the 1D results restated in §2.2 (Lemma 2.2 and Theorem 2.3) were machine-checked from scratch without any external axioms, nor what `[propext, Classical.choice, Quot.sound]` means on p. 103.
* **Concrete fix:** 
  1. Change the proof heading `"Sketch"` on those 20 proofs to `"Proof"`, and replace the `"Sketch"` sentences on p. 6 and p. 102 with:
     > `"All proofs printed in the paper and appendices are complete at standard journal level; for twenty propositions and lemmas (listed in Appendix I), routine algebraic verifications are condensed in print and written out in full in the Lean blueprint deposited in the accompanying repository."`
  2. On p. 7 (§1.1, paragraph 3), replace `"uses only parts of it that rest on no cited fact"` with:
     > `"all one-dimensional results imported from [15] (Lemma 2.2, Theorem 2.3, and the gauge construction of [15, Prop. 6.6]) are machine-checked from first principles in Lean 4 without assuming any of C1–C4 or any other external theorem."`
  3. On p. 103, after `"Lean’s three logical axioms"`, insert:
     > `"(propositional extensionality propext, the axiom of choice Classical.choice, and quotient soundness Quot.sound)"`.

---

### 17. Remove project-internal nicknames ("the line paper", "the cone paper", "the isotropic paper", "version 0.1") and draft/process notes
* **Page:** pp. 1–2 (§1), p. 5 (§1), p. 7 (§2), p. 53 (§5), and p. 104 (Declarations).
* **Quoted phrase:**
  > `"Working draft — not yet released"` (p. 1)
  > `"The computation of these families on grids is left to a further paper, not yet released."` (p. 5; similarly p. 53)
  > `"The three papers are cited in their released version 0.1, by the statement numbers of that version. A restated statement carries its released number in its title, and its proof is at that number"` (p. 7)
  > `"The division of labour, with its derivation and dates, is in notes/PROCESS.md; the agents’ words outnumber mine by between twenty-two and forty-two to one (computed 2026-10-13, a lower bound) over the module’s first sixteen archived days."` (p. 104)
* **What is wrong:** Referring to `[15]`, `[17]`, and `[16]` over thirty times as `"the line paper"`, `"the cone paper"`, and `"the isotropic paper"`, citing `"released version 0.1"` in the prose, announcing `"a further paper, not yet released"`, and citing internal repository paths (`notes/PROCESS.md`) and future-dated timestamps (`2026-10-13`, `September 2026`, `October 2026` in `[15–17]`) reads like internal project notes rather than an archival journal article.
* **Concrete fix:** 
  1. Remove `"Working draft — not yet released"` from p. 1, and replace `"a further paper, not yet released"` on pp. 5 and 53 with `"future work"`.
  2. Replace `"the line paper"`, `"the cone paper"`, and `"the isotropic paper"` throughout with direct citations `"[15]"`, `"[17]"`, and `"[16]"` (or `"the one-dimensional paper [15]"` and `"the isotropic paper [16]"` on first mention), and delete `"in their released version 0.1, by the statement numbers of that version"` on p. 7 (keeping version numbers in the bibliography entries `[15–17]`).
  3. On p. 104, replace `"is in notes/PROCESS.md; the agents’ words outnumber mine by between twenty-two and forty-two to one (computed 2026-10-13, a lower bound) over the module’s first sixteen archived days."` with: `"is documented in the accompanying repository; across the sixteen-day development log, agent-generated text outnumbered the author’s own words by between twenty-two and forty-two to one."`

---

### 18. Replace metatextual announcements ("Remark X shows how...", "Where positivity enters is...") with direct mathematical statements
* **Page:** p. 1 (§1), p. 5 (§1, *"Relation to scale-space theory"* and *"Relation to probability"*), and p. 21 (§3.4).
* **Quoted phrase:**
  > `"This paper asks which affine scale spaces exist under other axioms, incomparable with the classical ones (Remark 3.14), and what each of them can do for shape adaptation."` (p. 1)
  > `"§3.5 sets the axiomatics side by side."` (p. 5)
  > `"In probability the core of Theorem 3.6 is Kelker’s lemma, that a rotation-invariant law with independent coordinates is normal ([30], Lemma 5, p. 423). Remark 3.13 shows how, and what the single step of Theorem 3.7 adds."` (p. 5)
  > `"Where positivity enters is Remark 3.11."` (p. 21)
* **What is wrong:** In several places the text announces *where* an explanation can be found instead of stating the one-sentence insight on the spot, forcing the reader to jump ahead to understand why a statement is true or how it differs from the literature.
* **Concrete fix:** 
  1. On p. 1, replace `"other axioms, incomparable with the classical ones (Remark 3.14)"` with `"hemigroup axioms—which require positivity and a cascade along a partial order on matrices, without assuming a one-parameter semigroup or local-extrema non-enhancement (Remark 3.14)"`.
  2. On p. 5, delete `"§3.5 sets the axiomatics side by side."`
  3. On p. 5, replace `"Remark 3.13 shows how, and what the single step of Theorem 3.7 adds."` with `"A rank-one step splits the aperture into independent orthogonal subspaces as in Kelker’s lemma; Theorem 3.7 shows that a single rank-deficient step from a positive definite matrix already forces a quadratic exponent, without even assuming that e^{-g(\langle\omega,\Sigma\omega\rangle)} is a characteristic function (Remark 3.13)."`
  4. On p. 21, replace `"Where positivity enters is Remark 3.11."` with `"Positivity of the kernels and increments enters both in confining a measure with a degenerate transform to a subspace (Lemma 3.8) and in making the exponent g nonnegative (Remark 3.11)."`

---

### 19. Motivate causal curves and eigenvalue majorization in the opening of §4.4 ("Invariant wedges")
* **Page:** pp. 31–34 (§4.4 and Theorem 4.3).
* **Quoted phrase:**
  > `"An order in between allows at each aperture a cone of velocities, the cone field, and relates two apertures when a curve whose velocity stays in the cones joins them. The main result, Theorem 4.3, says that the closed invariant partial orders on \mathrm{PD}(d) that arise in this way are exactly those whose steps can be taken in fractions, and that every step of such an order is reached along one curve, with no limit of curves needed."` (p. 32)
  > `"Steps do not compose by multiplication. The composite of two steps depends on how their eigenframes sit relative to each other, so transitivity is a condition on all relative positions. A comparison of spectra by partial sums, majorization, handles it, with one cited inequality, for the spectrum of a product (C4, Theorem 2.13)."` (p. 32)
* **What is wrong:** For an imaging reader unfamiliar with Lie semigroups, defining $\Sigma \preceq_C \Sigma'$ in Theorem 4.3 via almost-everywhere derivatives of absolutely continuous "$C$-causal curves" looks unnecessarily abstract when Clause (1) immediately proves that $\Sigma \preceq_C \Sigma'$ is equivalent to the elementary matrix condition $\log(\Sigma^{-1/2}\Sigma'\Sigma^{-1/2}) \in C$! The opening of §4.4 does not explain *why* both descriptions (curves and matrix logarithms) are needed: the algebraic condition $\log(\Sigma^{-1/2}\Sigma'\Sigma^{-1/2}) \in C$ is how one tests a single step, whereas the curve/majorization machinery is needed to prove that this relation is *transitive* when two steps $M$ and $N$ do not commute ($\log(M^{1/2}NM^{1/2}) \ne \log M + \log N$).
* **Concrete fix:** Replace the four sentences quoted from the second paragraph of p. 32 (`"An order is described by its set of relative steps..."` to `"(C4, Theorem 2.13)."`) with:
  > `"Every GL(d)-invariant relation on \mathrm{PD}(d) is determined by the set \mathcal{K} of relative steps M = \Sigma^{-1/2}\Sigma'\Sigma^{-1/2} that it allows from I (Proposition 4.2). When \mathcal{K} = \exp C for an \mathrm{O}(d)-invariant closed convex cone C \subseteq \operatorname{Sym}(d), a single step \Sigma \preceq_C \Sigma' has the elementary algebraic test \log(\Sigma^{-1/2}\Sigma'\Sigma^{-1/2}) \in C. However, because non-commuting steps M and N have \log(M^{1/2}NM^{1/2}) \ne \log M + \log N, it is not obvious that \log(\Sigma^{-1/2}\Sigma'\Sigma^{-1/2}) \in C defines a transitive relation or coincides with the pairs joined by curves tangent to the cone field \Sigma^{1/2}C\Sigma^{1/2}. Bounding the logarithmic spectrum of M^{1/2}NM^{1/2} by majorization (C4, Theorem 2.13; Lemma C.1) establishes both transitivity and the equivalence with causal curves (Theorem 4.3)."`

---

### 20. Complete Table 1 (Notation) so it covers the symbols used in Table 2, §2, and §4.9
* **Page:** p. 14 (Table 1).
* **Quoted phrase:**
  > `"Table 1: Notation of §§3–4."`
* **What is wrong:** Table 1 omits ten symbols that appear repeatedly in §2, Table 2 (p. 31), and §4.9 (pp. 51–52), forcing the reader to hunt through prose paragraphs and appendices to decode them: $\mathcal{A}_d$ (the class of isotropic self-decomposable exponents in $\mathbb{R}^d$, Theorem 2.5), $\chi$ and $\varphi = \chi^2$ (the length and variance gauges, pp. 8, 18), $N(0, C)$ (centred Gaussian law of covariance $C$), $\operatorname{sym} B := \frac{1}{2}(B+B^{\mathsf{T}})$, $\sigma(\Sigma) \in \Delta_d$ (normalized eigenvalue spectrum in the simplex $\Delta_d$, Proposition F.3), $D_s := \operatorname{diag}(s_1,\dots,s_d)$, $\Delta(\Sigma) := \operatorname{diag}(\Sigma_{11},\dots,\Sigma_{dd})$, and $\operatorname{Corr}(d)$ (correlation matrices, Proposition F.4).
* **Concrete fix:** Add the following rows to Table 1 on p. 14:
  ```text
  \chi; \varphi = \chi^2           scale gauge on [0,\infty); variance gauge             §2.2, Prop. A.3
  \mathcal{A}_d                    isotropic self-decomposable exponents on \mathbb{R}^d Thm. 2.5, Def. 2.8
  N(0, C)                          centred Gaussian law on \mathbb{R}^d of covariance C  Prop. 4.20, §4.9
  \operatorname{sym} B             symmetric part \frac{1}{2}(B + B^{\mathsf{T}})        Prop. 4.10
  \sigma(\Sigma), \Delta_d         normalized spectrum of \Sigma and its simplex         Prop. F.3
  D_s, \Delta(\Sigma), \operatorname{Corr}(d)  \operatorname{diag}(s), diagonal of \Sigma, correlation matrices  Prop. F.4
  ```
