/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.MarginalFamily
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.LineLevyUnique
import ScaleSpaceCore.MainAnalysis
import ScaleSpaceCore.MainConstruction

/-!
# `thm:isotropic-classification` — the isotropic classification in dimension `d`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `thm:isotropic-classification`.

## Trust

**Necessity spends this module's ledger A3, clauses (ii) and (iii), at `d = 1`, and nothing else**:
the shared library's `ScaleSpace.main_analysis` ([V, Thm. 7.3], analysis direction, at
`ScaleSpaceCore v0.3.0`) takes the uniqueness of the symmetric Lévy pair on the line as a
hypothesis, `ScaleSpace.SymLevyUnique`, and `line_levy_unique` (`prop:line-levy-unique`) discharges
it from A3 (Q-0365). Before the switch the necessity direction read Paper V's `main_analysis`, which
spends Paper V's interface `fourier_toolbox_levy_unique`; it reads no declaration of Paper V's now.
Sufficiency, uniqueness and `isotropic_classification_origin` are Lean core.
`isotropic_classification` is listed in `CIAxiomGuard.lean` (`Formalization/README.md` § Trust).

## The route

* **Necessity.** The marginal family of `lem:isotropic-marginal-family` (`marginalFamily`) is a
  `ScaleSpace.CascadeFamily` represented by the marginals, so `ScaleSpace.main_analysis`, with its
  hypothesis discharged by `line_levy_unique`, applies to it as it stands and returns a
  normalised gauge `χ` (`χ(1) = 1`), a profile `P` with `F := P.exponent ≢ 0`, and the cosine transforms of the marginals. Because the representation is
  a *hypothesis* of `main_analysis`, quantified over every kernel family, no identification of
  kernels is needed: the blueprint's step "two probability measures with `κ ∗ f = ν ∗ f` for all `f`
  are equal" is not taken. `F ∈ 𝒜_d` is witnessed by `μ_{0,1}`, whose residual at `c ∈ (0,1)` is
  `μ_{s_c,1}` with `χ(s_c) = c`; the residual identity is read off the display.
* **Sufficiency.** The axioms are read off the transform. The gauge's continuity and its conjugate
  `S_λ = χ^{-1}(λχ(·))` are the shared library's `ConstructionData.chi_continuousOn` and
  `ConstructionData.gaugeAction` (Lean core), built on the profile `P` and `χ`; (ND) is the
  dilation-invariance argument [V, Lem. 6.3] (`ScaleSpace.dilation_invariance`), extended from
  `[0,∞)` to the line by the evenness of `P.exponent`.
* **Uniqueness.** The blueprint's: logarithms of the kernels from the origin, the dilation ratio
  at `t' = χ'^{-1}(1)`, and [V, Lem. 6.3] again.

The blueprint's sufficiency proof also built the family from the residuals of the law `μ` in
`𝒜_d`; the statement does not need it (the family is given and the display is the hypothesis), so
the Lean takes the part of that proof that reads the axioms off the display. The construction is
its own node since the blind review of wave 1E (W1E-1): `lem:isotropic-realisation`,
`isotropic_realisation` at the end of this file, Lean core, every pair being realised by the
images `(χ(t)I)_* ρ_{χ(s)/χ(t)}` of the residuals and the sufficiency direction.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## Helpers -/

/-- Every `r ≥ 0` is the norm of a vector of `ℝ^d`, `d ≥ 1`. -/
theorem exists_norm_eq (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) : ∃ ξ : Rd d, ‖ξ‖ = r :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) r, by simp [abs_of_nonneg hr]⟩

/-- The unit vector `e₁` of `ℝ^d`, `d ≥ 1`. -/
theorem exists_unit (hd : 1 ≤ d) : ∃ e : Rd d, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1, by simp⟩

/-- An orthogonal matrix preserves the norm: `|Qᵀξ| = |ξ|`. -/
theorem norm_lin_transpose_of_orth {Q : Mat d} (hQ : Q ∈ orthSet d) (ξ : Rd d) :
    ‖lin Qᵀ ξ‖ = ‖ξ‖ := by
  have h := quad_act Q 1 ξ
  rw [act_orth_one hQ, quad_one, quad_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h.symm

/-- The real exponential with one of its values `1`: `e^{-x} = 1` forces `x = 0`. -/
theorem eq_zero_of_exp_neg_eq_one {x : ℝ} (h : ((Real.exp (-x) : ℝ) : ℂ) = 1) : x = 0 := by
  have h1 : Real.exp (-x) = 1 := by exact_mod_cast h
  have := Real.exp_eq_one_iff (-x) |>.1 h1
  linarith

/-- **[V, Lem. 6.3] for a profile, on `[0,∞)`**: if `P(br) = P(ar)` for every `r ≥ 0`, with
`0 ≤ a`, `0 < b` and `a ≠ b`, then `P` vanishes on `[0,∞)`. The evenness of `P.exponent` carries
the invariance from `[0,∞)` to the line, where `ScaleSpace.dilation_invariance` applies. -/
theorem exponent_eq_zero_of_dilation (P : ScaleSpace.SDProfile) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 < b) (hab : a ≠ b) (h : ∀ r : ℝ, 0 ≤ r → P.exponent (b * r) = P.exponent (a * r)) :
    ∀ r : ℝ, 0 ≤ r → P.exponent r = 0 := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- `a = 0`: `P(br) = P(0) = 0`.
    intro r hr
    have := h (r / b) (div_nonneg hr hb.le)
    rwa [← ha0, zero_mul, ScaleSpace.SDProfile.exponent_zero, mul_div_cancel₀ _ hb.ne'] at this
  · set κ : ℝ := a / b with hκ
    have hκpos : 0 < κ := div_pos hapos hb
    have hκ1 : κ ≠ 1 := by
      intro h1
      rw [hκ, div_eq_one_iff_eq hb.ne'] at h1
      exact hab h1
    have hpos : ∀ r : ℝ, 0 ≤ r → P.exponent r = P.exponent (κ * r) := by
      intro r hr
      have := h (r / b) (div_nonneg hr hb.le)
      rw [mul_div_cancel₀ _ hb.ne'] at this
      rw [this, hκ]
      congr 1
      field_simp
    have hall : ∀ ω : ℝ, P.exponent ω = P.exponent (κ * ω) := by
      intro ω
      rcases le_total 0 ω with hω | hω
      · exact hpos ω hω
      · have := hpos (-ω) (neg_nonneg.2 hω)
        rwa [P.exponent_neg, mul_neg, P.exponent_neg] at this
    intro r _
    exact ScaleSpace.dilation_invariance P.exponent P.continuous_exponent.continuousAt
      P.exponent_zero κ hκpos hκ1 hall r

/-- The profile of an `F ∈ 𝒜_d`, with `F(0) = 0`. -/
theorem classA_zero {F : ℝ → ℝ} (hF : classA d F) : F 0 = 0 := by
  obtain ⟨⟨P, hP⟩, -⟩ := hF
  rw [hP 0 le_rfl, ScaleSpace.SDProfile.exponent_zero]

/-- The kernels of a family satisfying the display are probability measures with a transform that
depends on `|ξ|` and on the profile `P` only. -/
private theorem display_profile {μ : ℝ → ℝ → Measure (Rd d)} {χ F : ℝ → ℝ}
    (P : ScaleSpace.SDProfile) (hP : ∀ r : ℝ, 0 ≤ r → F r = P.exponent r)
    (hχ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ
      = ((Real.exp (-(P.exponent (χ t * ‖ξ‖) - P.exponent (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  intro s t hs hst ξ
  rw [hrep s t hs hst ξ, hP _ (mul_nonneg (hχ0 t (hs.trans hst)) (norm_nonneg ξ)),
    hP _ (mul_nonneg (hχ0 s hs) (norm_nonneg ξ))]

/-! ## Necessity -/

/-- **`thm:isotropic-classification`, necessity**: an isotropic cascade family has the display, for
a normalised gauge and an `F ∈ 𝒜_d`, `F ≢ 0`. Spends ledger A3 at `d = 1`, through
`ScaleSpace.main_analysis` and `line_levy_unique`. -/
theorem isotropic_classification_necessity (hd : 1 ≤ d) {μ : ℝ → ℝ → Measure (Rd d)}
    {S : ℝ → ℝ → ℝ} (hμ : IsIsotropicCascadeFamily μ S) :
    ∃ (χ : ℝ → ℝ) (F : ℝ → ℝ), IsGauge χ ∧ χ 1 = 1 ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨e, he⟩ := exists_unit hd
  obtain ⟨hrad, hks, -⟩ := isotropic_marginal_family hμ e he
  obtain ⟨χ, P, hχ0, hχm, hχs, hχ1, hne, -, hcos⟩ :=
    ScaleSpace.main_analysis line_levy_unique (marginalFamily hμ e he).toCascadeCore
      (fun s t => marginal e (μ s t)) (marginalFamily_isKernelFamily hμ e he) S
      (marginalFamily hμ e he).covariant
  -- The display, through the radial form and the cosine transform of the marginals.
  have hdisp : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ
      = ((Real.exp (-(P.exponent (χ t * ‖ξ‖) - P.exponent (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
    intro s t hs hst ξ
    obtain ⟨hprob, hsym⟩ := hks s t hs hst
    rw [hrad s t hs hst ξ, ScaleSpace.charFun_eq_fourierCos_of_symmetric hsym,
      hcos s t ‖ξ‖ hs hst]
  have hχnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t := fun t ht => by
    simpa [hχ0] using hχm.monotoneOn (le_refl (0 : ℝ)) ht ht
  refine ⟨χ, P.exponent, ⟨hχ0, hχm, hχs⟩, hχ1, ⟨⟨P, fun _ _ => rfl⟩, μ 0 1,
    hμ.isProbability 0 1 le_rfl zero_le_one, ?_, ?_⟩, ?_, hdisp⟩
  · -- `μ_{0,1}` is self-decomposable, with residual `μ_{s_c,1}`, `χ(s_c) = c`.
    haveI := hμ.isProbability 0 1 le_rfl zero_le_one
    rw [ScaleSpace.isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    obtain ⟨sc, hsc0, hsc⟩ := hχs (le_of_lt hc0 : c ∈ Ici (0 : ℝ))
    have hsc0' : (0 : ℝ) ≤ sc := hsc0
    have hsc1 : sc ≤ 1 := by
      by_contra hcon
      have h := hχm (Set.mem_Ici.2 zero_le_one) hsc0 (lt_of_not_ge hcon)
      rw [hχ1, hsc] at h
      linarith
    refine ⟨μ sc 1, hμ.isProbability sc 1 hsc0' hsc1, fun ξ => ?_⟩
    rw [hdisp 0 1 le_rfl zero_le_one, hdisp 0 1 le_rfl zero_le_one, hdisp sc 1 hsc0' hsc1, hχ0, hχ1,
      hsc, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, zero_mul, zero_mul,
      ScaleSpace.SDProfile.exponent_zero, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring_nf
  · intro ξ
    rw [hdisp 0 1 le_rfl zero_le_one, hχ0, hχ1, zero_mul, one_mul,
      ScaleSpace.SDProfile.exponent_zero, sub_zero]
  · obtain ⟨ω, hω⟩ := hne
    refine ⟨|ω|, abs_nonneg ω, ?_⟩
    rcases le_total 0 ω with h | h
    · rwa [abs_of_nonneg h]
    · rwa [abs_of_nonpos h, P.exponent_neg]

/-! ## Sufficiency -/

/-- **`thm:isotropic-classification`, sufficiency**: a family of probability measures with the
display, for a gauge `χ` and an `F ∈ 𝒜_d` with `F ≢ 0`, is an isotropic cascade family, with the
dilation action `S_λ = χ^{-1}(λχ(·))`. Lean core. -/
theorem isotropic_classification_sufficiency (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S := by
  obtain ⟨⟨P, hP⟩, -⟩ := hF
  set CD : ScaleSpace.ConstructionData := ⟨P, χ, hχ.1, hχ.2.1, hχ.2.2⟩ with hCD
  have hχCD : CD.χ = χ := rfl
  have hχnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t := fun t ht => CD.chi_nonneg ht
  have hd' := display_profile P hP hχnn hrep
  -- `P` does not vanish on `[0,∞)`.
  have hPne : ¬ ∀ r : ℝ, 0 ≤ r → P.exponent r = 0 := by
    intro h
    obtain ⟨r, hr, hFr⟩ := hFne
    exact hFr (by rw [hP r hr, h r hr])
  refine ⟨CD.gaugeAction, ?_⟩
  exact
  { isProbability := hprob
    diag := fun t ht => by
      haveI := hprob t t ht le_rfl
      refine eq_of_charFun_eq fun ξ => ?_
      rw [hd' t t ht le_rfl ξ, charFun_dirac]
      simp
    cascade := fun r s t hr hrs hst => by
      haveI := hprob r t hr (hrs.trans hst)
      haveI := hprob s t (hr.trans hrs) hst
      haveI := hprob r s hr hrs
      refine eq_of_charFun_eq fun ξ => ?_
      rw [charFun_conv, hd' r t hr (hrs.trans hst) ξ, hd' s t (hr.trans hrs) hst ξ,
        hd' r s hr hrs ξ, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    continuous := fun ξ => by
      have h2 : ContinuousOn (fun p : ℝ × ℝ => χ p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        CD.chi_continuousOn.comp continuous_snd.continuousOn
          (fun p hp => (show (0 : ℝ) ≤ p.2 from hp.1.trans hp.2))
      have h1 : ContinuousOn (fun p : ℝ × ℝ => χ p.1) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        CD.chi_continuousOn.comp continuous_fst.continuousOn
          (fun p hp => (show (0 : ℝ) ≤ p.1 from hp.1))
      have hc : ContinuousOn (fun p : ℝ × ℝ =>
          ((Real.exp (-(P.exponent (χ p.2 * ‖ξ‖) - P.exponent (χ p.1 * ‖ξ‖))) : ℝ) : ℂ))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
        refine Complex.continuous_ofReal.comp_continuousOn
          (Real.continuous_exp.comp_continuousOn (ContinuousOn.neg (ContinuousOn.sub ?_ ?_)))
        · exact P.continuous_exponent.comp_continuousOn (h2.mul continuousOn_const)
        · exact P.continuous_exponent.comp_continuousOn (h1.mul continuousOn_const)
      exact hc.congr fun p hp => hd' p.1 p.2 hp.1 hp.2 ξ
    rotation := fun Q hQ s t hs hst => by
      haveI := hprob s t hs hst
      refine eq_of_charFun_eq fun ξ => ?_
      rw [push, charFun_map_lin, hd' s t hs hst, hd' s t hs hst, norm_lin_transpose_of_orth hQ]
    scale_bij := fun lam hlam =>
      ⟨fun _ hs => CD.gaugeAction_nonneg hlam hs, CD.gaugeAction_strictMonoOn hlam,
        CD.gaugeAction_surjOn hlam⟩
    scale := fun lam hlam s t hs hst => by
      haveI := hprob s t hs hst
      have hSs := CD.gaugeAction_nonneg hlam hs
      have hSst : CD.gaugeAction lam s ≤ CD.gaugeAction lam t :=
        (CD.gaugeAction_strictMonoOn hlam).monotoneOn hs (hs.trans hst) hst
      haveI := hprob _ _ hSs hSst
      have hgt : χ (CD.gaugeAction lam t) = lam * χ t := CD.chi_gaugeAction hlam (hs.trans hst)
      have hgs : χ (CD.gaugeAction lam s) = lam * χ s := CD.chi_gaugeAction hlam hs
      refine eq_of_charFun_eq fun ξ => ?_
      rw [charFun_push_smul_one, hd' s t hs hst, hd' _ _ hSs hSst, hgt, hgs, norm_smul,
        Real.norm_eq_abs, abs_of_pos hlam, mul_left_comm (χ t), mul_left_comm (χ s), mul_assoc,
        mul_assoc]
    nondegenerate := fun s t hs hst h => by
      have hst' : ∀ r : ℝ, 0 ≤ r → P.exponent (χ t * r) = P.exponent (χ s * r) := by
        intro r hr
        obtain ⟨ξ, hξ⟩ := exists_norm_eq hd hr
        have h1 := hd' s t hs hst.le ξ
        rw [h, charFun_dirac, hξ] at h1
        simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
        have := eq_zero_of_exp_neg_eq_one h1.symm
        linarith
      have htpos : 0 < χ t := CD.chi_pos (hs.trans_lt hst)
      have hne : χ s ≠ χ t := fun he => (hχ.2.1.injOn hs (hs.trans hst.le) he ▸ hst).false
      exact hPne (exponent_eq_zero_of_dilation P (hχnn s hs) htpos hne hst') }

/-! ## The node -/

/-- **`thm:isotropic-classification`**: a family `(μ_{s,t})_{0 ≤ s ≤ t}` of probability measures on
`ℝ^d` is an isotropic cascade family if and only if there are a gauge `χ` and an `F ∈ 𝒜_d`,
`F ≢ 0`, with `μ̂_{s,t}(ξ) = exp[-(F(χ(t)|ξ|) - F(χ(s)|ξ|))]`. -/
theorem isotropic_classification (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) :
    (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S) ↔
      ∃ (χ : ℝ → ℝ) (F : ℝ → ℝ), IsGauge χ ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
          charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨S, hμ⟩
    obtain ⟨χ, F, hχ, -, hF, hFne, hrep⟩ := isotropic_classification_necessity hd hμ
    exact ⟨χ, F, hχ, hF, hFne, hrep⟩
  · rintro ⟨χ, F, hχ, hF, hFne, hrep⟩
    exact isotropic_classification_sufficiency hd μ hprob χ F hχ hF hFne hrep

/-- **`thm:isotropic-classification`**, in particular: the kernels from the origin are
`μ̂_{0,t}(ξ) = e^{-F(χ(t)|ξ|)}`. -/
theorem isotropic_classification_origin (_hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (_hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : Rd d, charFun (μ 0 t) ξ = ((Real.exp (-F (χ t * ‖ξ‖)) : ℝ) : ℂ) := by
  intro t ht ξ
  rw [hrep 0 t le_rfl ht ξ, hχ.1, zero_mul, classA_zero hF, sub_zero]

/-- **`thm:isotropic-classification`**, uniqueness: if a gauge `χ'` and a real function `F'` on
`[0,∞)` **with `F'(0) = 0`** (`% CHANGED Q-0281`: without it the clause is false, `F' := F + 1`
satisfying the display) also satisfy the display, then `χ' = cχ` and `F' = F(c⁻¹ ·)` for some
`c > 0`, and `c = 1` when `χ(1) = χ'(1) = 1`. -/
theorem isotropic_classification_unique (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (_hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F) (hF0 : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (hχ' : IsGauge χ') (hF'0 : F' 0 = 0)
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∃ c : ℝ, 0 < c ∧ (∀ t : ℝ, 0 ≤ t → χ' t = c * χ t) ∧
      (∀ r : ℝ, 0 ≤ r → F' r = F (c⁻¹ * r)) ∧ (χ 1 = 1 → χ' 1 = 1 → c = 1) := by
  obtain ⟨⟨P, hP⟩, -⟩ := hF
  have hFz : F 0 = 0 := by rw [hP 0 le_rfl, ScaleSpace.SDProfile.exponent_zero]
  set CD : ScaleSpace.ConstructionData := ⟨P, χ, hχ.1, hχ.2.1, hχ.2.2⟩ with hCD
  set CD' : ScaleSpace.ConstructionData := ⟨P, χ', hχ'.1, hχ'.2.1, hχ'.2.2⟩ with hCD'
  have hχnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t := fun t ht => CD.chi_nonneg ht
  have hχnn' : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ' t := fun t ht => CD'.chi_nonneg ht
  -- Logarithms of the kernels from the origin.
  have key : ∀ t : ℝ, 0 ≤ t → ∀ r : ℝ, 0 ≤ r → F (χ t * r) = F' (χ' t * r) := by
    intro t ht r hr
    obtain ⟨ξ, hξ⟩ := exists_norm_eq hd hr
    have h := (hrep 0 t le_rfl ht ξ).symm.trans (hrep' 0 t le_rfl ht ξ)
    rw [hχ.1, hχ'.1, zero_mul, hFz, hF'0, hξ, sub_zero, sub_zero] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    linarith
  -- The dilation ratio at `t' = χ'^{-1}(1)`.
  obtain ⟨t', ht'0, ht'⟩ := hχ'.2.2 (Set.mem_Ici.2 zero_le_one)
  have ht'0' : (0 : ℝ) ≤ t' := ht'0
  have ht'pos : 0 < t' := by
    rcases eq_or_lt_of_le ht'0' with h | h
    · rw [← h, hχ'.1] at ht'
      exact absurd ht' zero_ne_one
    · exact h
  have hχt' : 0 < χ t' := CD.chi_pos ht'pos
  refine ⟨(χ t')⁻¹, inv_pos.2 hχt', ?_, ?_, ?_⟩
  · intro t ht
    -- `F(χ(t)r) = F(c⁻¹χ'(t)r)` for every `r`; a ratio `≠ 1` would make `F ≡ 0`.
    by_contra hcon
    rcases eq_or_lt_of_le ht with h0 | htpos
    · exact hcon (by rw [← h0, hχ.1, hχ'.1, mul_zero])
    have hb : 0 < χ t := CD.chi_pos htpos
    have ha : 0 ≤ χ t' * χ' t := mul_nonneg hχt'.le (hχnn' t ht)
    have hab : χ t' * χ' t ≠ χ t := by
      intro h
      apply hcon
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hχt'.ne', one_mul]
    have hdil : ∀ r : ℝ, 0 ≤ r → P.exponent (χ t * r) = P.exponent (χ t' * χ' t * r) := by
      intro r hr
      have h1 := key t ht r hr
      have h2 := key t' ht'0' (χ' t * r) (mul_nonneg (hχnn' t ht) hr)
      rw [ht', one_mul] at h2
      rw [← hP _ (mul_nonneg hb.le hr), ← hP _ (mul_nonneg ha hr), h1, ← h2, mul_assoc]
    obtain ⟨r, hr, hFr⟩ := hF0
    exact hFr (by rw [hP r hr, exponent_eq_zero_of_dilation P ha hb hab hdil r hr])
  · intro r hr
    have h := key t' ht'0' r hr
    rw [ht', one_mul] at h
    rw [← h, inv_inv]
  · intro h1 h1'
    -- `χ'(1) = cχ(1)` at the normalisation.
    have h := key 1 zero_le_one 1 zero_le_one
    have hk := key t' ht'0' 1 zero_le_one
    have hχ'1 : χ' 1 = (χ t')⁻¹ * χ 1 := by
      by_contra hcon
      have hb : (0 : ℝ) < 1 := one_pos
      have hab : χ t' ≠ 1 := by
        intro he
        apply hcon
        rw [h1', h1, he, inv_one, one_mul]
      have hdil : ∀ r : ℝ, 0 ≤ r → P.exponent (1 * r) = P.exponent (χ t' * r) := by
        intro r hr
        have h2 := key 1 zero_le_one r hr
        have h3 := key t' ht'0' r hr
        rw [h1, h1'] at h2
        rw [ht'] at h3
        rw [← hP _ (mul_nonneg zero_le_one hr), ← hP _ (mul_nonneg hχt'.le hr), h2, h3]
      obtain ⟨r, hr, hFr⟩ := hF0
      exact hFr (by rw [hP r hr, exponent_eq_zero_of_dilation P hχt'.le hb hab hdil r hr])
    rw [h1, h1', mul_one] at hχ'1
    rw [← hχ'1]

/-! ## Every pair is realised -/

/-- The residuals of the law `μ` of an `F ∈ 𝒜_d`, extended to `c ∈ [0,1]`: for each such `c`
there is a probability measure with transform `e^{-(F(|η|) - F(c|η|))}`; at `c = 0` it is `μ`, at
`c = 1` it is `δ₀`, and for `c ∈ (0,1)` it is a residual of `μ`, its transform forced by
`μ̂(cη) = e^{-F(c|η|)} ≠ 0`. -/
theorem classA_residual {F : ℝ → ℝ} (hF : classA d F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      ∀ η : Rd d, charFun ρ η = ((Real.exp (-(F ‖η‖ - F (c * ‖η‖))) : ℝ) : ℂ) := by
  have hF0 := classA_zero hF
  obtain ⟨-, μ, hμprob, hsd, hμcf⟩ := hF
  rcases eq_or_lt_of_le hc0 with h0 | hc0'
  · refine ⟨μ, hμprob, fun η => ?_⟩
    rw [hμcf, ← h0, zero_mul, hF0, sub_zero]
  rcases eq_or_lt_of_le hc1 with h1 | hc1'
  · refine ⟨Measure.dirac 0, inferInstance, fun η => ?_⟩
    rw [charFun_dirac, h1, one_mul, sub_self, neg_zero, Real.exp_zero]
    simp
  obtain ⟨ρ, hρprob, hρ⟩ := (ScaleSpace.isSelfDecomposable_iff_charFun μ).1 hsd c hc0' hc1'
  refine ⟨ρ, hρprob, fun η => ?_⟩
  have h := hρ η
  rw [hμcf, hμcf, norm_smul, Real.norm_eq_abs, abs_of_pos hc0'] at h
  have hne : ((Real.exp (-F (c * ‖η‖)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have h2 : charFun ρ η = ((Real.exp (-F ‖η‖) : ℝ) : ℂ) / ((Real.exp (-F (c * ‖η‖)) : ℝ) : ℂ) := by
    rw [eq_div_iff hne, mul_comm, ← h]
  rw [h2, ← Complex.ofReal_div, ← Real.exp_sub]
  congr 3
  ring

/-- **`lem:isotropic-realisation`**: every pair is realised. For every gauge `χ` and every
`F ∈ 𝒜_d` with `F ≢ 0` there is an isotropic cascade family with the display
`μ̂_{s,t}(ξ) = exp[-(F(χ(t)|ξ|) - F(χ(s)|ξ|))]`: the images
`μ_{s,t} := (χ(t)I)_* ρ_{χ(s)/χ(t)}` of the residuals of `F`'s law (`classA_residual`), which
`isotropic_classification_sufficiency` makes a family. Lean core. -/
theorem isotropic_realisation (hd : 1 ≤ d) (χ F : ℝ → ℝ) (hχ : IsGauge χ) (hF : classA d F)
    (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) :
    ∃ μ : ℝ → ℝ → Measure (Rd d),
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) ∧
      (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  -- The residuals, chosen for every `c` (`δ₀` off `[0,1]`).
  have hres : ∀ c : ℝ, ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      (0 ≤ c → c ≤ 1 → ∀ η : Rd d,
        charFun ρ η = ((Real.exp (-(F ‖η‖ - F (c * ‖η‖))) : ℝ) : ℂ)) := by
    intro c
    by_cases hc : 0 ≤ c ∧ c ≤ 1
    · obtain ⟨ρ, hρ, hρcf⟩ := classA_residual hF hc.1 hc.2
      exact ⟨ρ, hρ, fun _ _ => hρcf⟩
    · exact ⟨Measure.dirac 0, inferInstance, fun h0 h1 => absurd ⟨h0, h1⟩ hc⟩
  choose ρ hρprob hρcf using hres
  have hχnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t := fun t ht => by
    have h := hχ.2.1.monotoneOn (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (mem_Ici.2 ht) ht
    rwa [hχ.1] at h
  have hχmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → χ s ≤ χ t := fun s t hs hst =>
    hχ.2.1.monotoneOn (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst
  set μ : ℝ → ℝ → Measure (Rd d) := fun s t => push (χ t • (1 : Mat d)) (ρ (χ s / χ t)) with hμ
  have hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t) := fun s t _ _ => by
    haveI := hρprob (χ s / χ t)
    exact isProbabilityMeasure_push _ _
  have hdisp : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
    intro s t hs hst ξ
    have hs0 := hχnn s hs
    have ht0 := hχnn t (hs.trans hst)
    have hst' := hχmono s t hs hst
    have hc0 : 0 ≤ χ s / χ t := div_nonneg hs0 ht0
    have hc1 : χ s / χ t ≤ 1 := div_le_one_of_le₀ hst' ht0
    rw [hμ, charFun_push_smul_one, hρcf _ hc0 hc1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hprod : χ s / χ t * (χ t * ‖ξ‖) = χ s * ‖ξ‖ := by
      rcases eq_or_lt_of_le ht0 with h | h
      · have hs' : χ s = 0 := le_antisymm (h ▸ hst') hs0
        rw [← h, hs', zero_div, zero_mul, zero_mul]
      · field_simp
    rw [hprod]
  exact ⟨μ, hprob, isotropic_classification_sufficiency hd μ hprob χ F hχ hF hFne hdisp, hdisp⟩

end AffineHemigroup
