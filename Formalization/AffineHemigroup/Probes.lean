/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Witnesses
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Positive probes: a should-hold consequence of each headline declaration

The boundary harness's second check (article-kit `docs/LINKAGE.md` rule 5, `linkage boundary`;
`linkage.toml` `[boundary]`). Each probe **uses** one headline declaration and keeps one clause of
it, read at a model of `Witnesses.lean` where that makes it concrete. A headline statement weakened
into something that still type-checks — a clause dropped, a hypothesis strengthened, a conclusion
existential where it was universal — stops one of these from building. The file is part of the
library (CI builds it, the `sorry` guard covers it) and nothing in the library of the isotropic
paper imports it.

The probes here are those of the isotropic paper's headline declarations (chapter 3). Those of
chapters 4 and 5 stood here until Q-0452; they are in `AffineHemigroup.ProbesAffine`, which
imports this file.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- `thm:isotropic-classification`, necessity, keeps `F ≢ 0`: every isotropic cascade family has an
exponent in `𝒜_d` that is not identically `0`. A classification allowing `F ≡ 0` stops this. -/
theorem probe_isotropic_classification (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (S : ℝ → ℝ → ℝ) (hμ : IsIsotropicCascadeFamily μ S) :
    ∃ F : ℝ → ℝ, classA d F ∧ ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0 := by
  obtain ⟨-, F, -, hF, hne, -⟩ :=
    (isotropic_classification hd μ hμ.isProbability).1 ⟨S, hμ⟩
  exact ⟨F, hF, hne⟩

/-- `thm:isotropic-classification`, sufficiency, at the heat family: the pair `(id, heatF)` makes it
an isotropic cascade family. A theorem weakened to one direction stops this. -/
theorem probe_isotropic_classification_heat (hd : 1 ≤ d) :
    ∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily (heatFamily d) S := by
  obtain ⟨hprob, -, hχ, hF, hne, hrep⟩ := witness_isotropic_classification (d := d) hd
  exact (isotropic_classification hd _ hprob).2 ⟨id, heatF, hχ, hF, hne, hrep⟩

/-- `thm:isotropic-classification`, uniqueness: two normalised gauges of one family are equal on
`[0,∞)`. A uniqueness clause weakened to "up to a constant" with no normalisation stops this. -/
theorem probe_isotropic_classification_unique (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F) (hF0 : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (hχ' : IsGauge χ') (hF'0 : F' 0 = 0)
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ))
    (hχ1 : χ 1 = 1) (hχ'1 : χ' 1 = 1) :
    ∀ t : ℝ, 0 ≤ t → χ' t = χ t := by
  obtain ⟨c, -, hχc, -, h1⟩ :=
    isotropic_classification_unique hd μ hprob χ F hχ hF hF0 hrep χ' F' hχ' hF'0 hrep'
  intro t ht
  rw [hχc t ht, h1 hχ1 hχ'1, one_mul]

/-- `cor:isotropic-classification-operators`, necessity, keeps the representation and `F ≢ 0`: the
operator `Φ_{0,1}` of every isotropic cascade measurement family is convolution by a probability
measure whose transform is `e^{-F(χ(1)|ξ|)}`, for a gauge `χ` and an `F ∈ 𝒜_d` that is not
identically `0`. A corollary allowing `F ≡ 0`, or one that lost the operators, stops this. -/
theorem probe_isotropic_classification_operators (hd : 1 ≤ d)
    (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (S : ℝ → ℝ → ℝ) (hΦ : IsIsotropicOperatorFamily Φ S) :
    ∃ (χ F : ℝ → ℝ) (ν : Measure (Rd d)), IsGauge χ ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∃ _ : IsProbabilityMeasure ν, Φ 0 1 = ScaleSpace.mconvL1E ν) ∧
      ∀ ξ : Rd d, charFun ν ξ = ((Real.exp (-F (χ 1 * ‖ξ‖)) : ℝ) : ℂ) := by
  obtain ⟨χ, F, μ, hχ, hF, hne, hμ, hrep⟩ := (isotropic_classification_operators hd Φ).1 ⟨S, hΦ⟩
  refine ⟨χ, F, μ 0 1, hχ, hF, hne, hμ 0 1 le_rfl zero_le_one, fun ξ => ?_⟩
  rw [hrep 0 1 le_rfl zero_le_one ξ, hχ.1, zero_mul, classA_zero hF, sub_zero]

/-- `cor:isotropic-classification-operators`, sufficiency, at the heat family: operators that are
convolution by the heat family form an isotropic cascade measurement family. A corollary weakened
to one direction stops this. -/
theorem probe_isotropic_classification_operators_heat (hd : 1 ≤ d)
    (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d))
    (hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∃ _ : IsProbabilityMeasure (heatFamily d s t),
      Φ s t = ScaleSpace.mconvL1E (heatFamily d s t)) :
    ∃ S : ℝ → ℝ → ℝ, IsIsotropicOperatorFamily Φ S := by
  obtain ⟨-, -, hχ, hF, hne, hrep⟩ := witness_isotropic_classification (d := d) hd
  exact (isotropic_classification_operators hd Φ).2 ⟨id, heatF, heatFamily d, hχ, hF, hne, hΦ, hrep⟩

/-- `cor:isotropic-classification-operators`, uniqueness: two normalised representations of one
operator family have the same measures on `{0 ≤ s ≤ t}`, the same gauge and the same exponent on
`[0,∞)`. A clause that lost the measures, or the normalisation, stops this. -/
theorem probe_isotropic_classification_operators_unique (hd : 1 ≤ d)
    (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (χ F : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d))
    (hχ : IsGauge χ) (hF : classA d F) (hF0 : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = ScaleSpace.mconvL1E (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (μ' : ℝ → ℝ → Measure (Rd d)) (hχ' : IsGauge χ') (hF'0 : F' 0 = 0)
    (hΦ' : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ' s t), Φ s t = ScaleSpace.mconvL1E (μ' s t))
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ' s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ))
    (hχ1 : χ 1 = 1) (hχ'1 : χ' 1 = 1) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ s t) ∧ (∀ t : ℝ, 0 ≤ t → χ' t = χ t) ∧
      ∀ r : ℝ, 0 ≤ r → F' r = F r := by
  obtain ⟨hμ, c, -, hχc, hF', h1⟩ :=
    isotropic_classification_operators_unique hd Φ χ F μ hχ hF hF0 hΦ hrep χ' F' μ' hχ' hF'0 hΦ'
      hrep'
  refine ⟨hμ, fun t ht => ?_, fun r hr => ?_⟩
  · rw [hχc t ht, h1 hχ1 hχ'1, one_mul]
  · rw [hF' r hr, h1 hχ1 hχ'1, inv_one, one_mul]

/-- `thm:origin-boundedness-d`(5), above the threshold, at the Matérn law with `2γ > d`: it has a
density bounded near the origin. A dichotomy weakened to one direction stops this. -/
theorem probe_origin_dichotomy (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : (d : ℝ) < 2 * γ) :
    ∃ q : Rd d → ℝ, gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ x : Rd d, ‖x‖ < δ → q x ≤ M := by
  obtain ⟨ha, hc, -, hlaw, hiff⟩ := witness_origin_boundedness hd hγ
  exact (origin_dichotomy hd _ ha hc _ hlaw).2 (hiff.2 hγd)

/-- `thm:origin-boundedness-d`(4), at and below the threshold, at the Matérn law with `2γ ≤ d`: the
transform is not integrable. -/
theorem probe_origin_unbounded (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    ∫⁻ ξ, ENNReal.ofReal (charFun (gammaGaussLaw d γ) ξ).re = ⊤ := by
  obtain ⟨ha, hc, -, hlaw, -⟩ := witness_origin_boundedness hd hγ
  refine (origin_unbounded hd _ ha hc _ hlaw ?_).1
  rw [maternOriginDatum_profileAtOrigin, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hγd

/-- `thm:filtration-strict`(3): the first step of the filtration is strict, `𝒜_2 ≠ 𝒜_1`. -/
theorem probe_filtration_strict : {F : ℝ → ℝ | classA 2 F} ≠ {F | classA 1 F} :=
  (filtration_strict.1 1 le_rfl).ne

/-- `thm:filtration-strict`(1): the witness at the second step is in `𝒜_1` and not in `𝒜_2`. -/
theorem probe_filtration_witness {w : ℝ} (hw1 : threshold ((1 : ℕ) + 1 : ℝ) < w)
    (hw2 : w ≤ threshold (1 : ℕ)) : classA 1 (witnessF w) ∧ ¬ classA 2 (witnessF w) :=
  filtration_witness 1 le_rfl hw1 hw2

/-- `lem:filtration-top`, the inclusion `𝒜_∞ ⊆ 𝒮` that spends A10: a member of every `𝒜_d` is the
Brownian subordination of a causally admissible exponent. -/
theorem probe_filtration_top (F : ℝ → ℝ) (hF : classAInf F) :
    ∃ FI : ScaleSpace.CausalAdmissible, ∀ r : ℝ, 0 ≤ r → F r = FI.exponent (r ^ 2 / 2) :=
  (filtration_top F).1 hF

/-- `thm:no-cin-ray-in-the-plane`, its last sentence: `𝒜_2` contains the unit `Cin` ray at no
scale. -/
theorem probe_no_cin_ray : ¬ classA 2 (fun ω => 1 * ScaleSpace.cin (1 * |ω|)) :=
  (no_cin_ray_in_the_plane (d := 2) le_rfl one_pos one_pos).2

/-- `prop:origin-lower-bound-d`, at the Matérn law in dimension `d ≥ 2`: a lower bound `c₁|x|^{c-d}`
with `c = 2γ` and `c₁ > 0`, on a ball. -/
theorem probe_origin_lower_bound (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ E : Set (Rd d), MeasurableSet E →
      E ⊆ Metric.ball 0 δ →
        ENNReal.ofReal c₁ * ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ (2 * γ - d)) ≤
          gammaGaussLaw d γ E := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hc, hctop, hlaw, -⟩ := witness_origin_boundedness hd1 hγ
  obtain ⟨⟨ε₀, hε₀, hk⟩, h⟩ := origin_lower_bound hd _ ha hc hctop _ hlaw
  obtain ⟨hpos, hb⟩ := h ε₀ hε₀ hk
  have hc2 : (maternOriginDatum hd1 γ hγ).profileAtOrigin.toReal = 2 * γ := by
    rw [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)]
  rw [hc2] at hpos hb
  exact ⟨_, hpos, ε₀ / 2, by linarith [hε₀.1], hb⟩

/-- `prop:isotropic-radial-monotone`(1), at the heat family and `t = 1`: the kernel has a radially
nonincreasing density. -/
theorem probe_radial_monotone (hd : 1 ≤ d) :
    ∃ q : ℝ → ℝ, (∀ r ∈ Ioi (0 : ℝ), 0 ≤ q r) ∧ AntitoneOn q (Ioi 0) ∧
      heatFamily d 0 1 = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) :=
  radial_monotone_family hd _ _ (witness_radial_monotone (γ := 1) hd one_pos).1 one_pos

/-! ## The fresh-agent passes' coverage (Q-0376)

Probes for the conjuncts and clauses the adversarial passes found unprobed
(`blueprint/REVIEW-fidelity.md`, section "The fresh-agent passes"). -/

/-- `thm:origin-boundedness-d`(3), at the subordinated Gamma datum (`witness_origin_subordinated`):
the mixture density of the delay law is radially nonincreasing, and its value at the origin is
finite exactly when `2γ > d`. A clause dropping the density's monotonicity or the finiteness
dichotomy stops this. -/
theorem probe_origin_subordinated (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (∀ x y : Rd d, 0 < ‖x‖ → ‖x‖ ≤ ‖y‖ →
      mixtureDensity d (ProbabilityTheory.gammaMeasure γ 1) y ≤
        mixtureDensity d (ProbabilityTheory.gammaMeasure γ 1) x) ∧
    (ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) *
        ∫⁻ ξ, ENNReal.ofReal
          (charFun ((ProbabilityTheory.gammaMeasure γ 1).bind (gaussVar d)) ξ).re ≠ ⊤ ↔
      (d : ℝ) < 2 * γ) := by
  obtain ⟨ha, hc, hlaw, hFI, hsub, hprob, hρ0, hlap, hval⟩ := witness_origin_subordinated hd hγ
  refine ⟨(subordinated_law hd _ ha hc _ hlaw _ hFI hsub _ hρ0 hlap).2.2, ?_⟩
  rw [(subordinated_density_limit hd _ ha hc _ hlaw _ hFI hsub _ hρ0 hlap).2.2, hval,
    ← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff (by linarith)]

/-! ### Siblings: the other conjuncts the first probes did not read

The thin-probe finding is a pattern (a probe keeps one clause of a many-clause declaration), so the
other headline declarations were checked for it; these are the conjuncts that no probe read. -/

/-- `thm:origin-boundedness-d`(5), the necessity: at the Matérn law with `2γ ≤ d` no density is
bounded near the origin. A dichotomy weakened to its sufficiency stops this. -/
theorem probe_origin_dichotomy_converse (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    ¬ ∃ q : Rd d → ℝ, gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ x : Rd d, ‖x‖ < δ → q x ≤ M := by
  obtain ⟨ha, hc, -, hlaw, hiff⟩ := witness_origin_boundedness hd hγ
  intro h
  have := hiff.1 ((origin_dichotomy hd _ ha hc _ hlaw).1 h)
  linarith

/-- `thm:origin-boundedness-d`(4), its second and third sentences, at the Matérn law with
`2γ ≤ d`: no bound `μ(B) ≤ M|B|` near the origin, and no representative bounded near it. -/
theorem probe_origin_unbounded_near_zero (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    (¬ ∃ δ : ℝ, 0 < δ ∧ ∃ M : NNReal, ∀ B : Set (Rd d), MeasurableSet B →
        B ⊆ Metric.ball 0 δ → gammaGaussLaw d γ B ≤ M * volume B) ∧
      ∀ q : Rd d → ℝ, gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
        ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ x : Rd d, 0 < ‖x‖ ∧ ‖x‖ < δ ∧ M < q x := by
  obtain ⟨ha, hc, -, hlaw, -⟩ := witness_origin_boundedness hd hγ
  have hcd : (maternOriginDatum hd γ hγ).profileAtOrigin ≤ d := by
    rw [maternOriginDatum_profileAtOrigin, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hγd
  exact (origin_unbounded hd _ ha hc _ hlaw hcd).2

/-- `thm:filtration-strict`(3), its other two sentences: `𝒜_∞ ⊊ 𝒜_1`, and `𝒜_3 ≠ 𝒜_∞`. -/
theorem probe_filtration_strict_top :
    {F : ℝ → ℝ | classAInf F} ⊂ {F | classA 1 F} ∧
      {F : ℝ → ℝ | classA 3 F} ≠ {F | classAInf F} :=
  ⟨filtration_strict.2.1 1 le_rfl, filtration_strict.2.2 3 (by norm_num)⟩

/-- `thm:isotropic-classification`, uniqueness of the exponent: two normalised pairs of one family
have the same exponent on `[0,∞)`. -/
theorem probe_isotropic_classification_unique_exponent (hd : 1 ≤ d)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F) (hF0 : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (hχ' : IsGauge χ') (hF'0 : F' 0 = 0)
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ))
    (hχ1 : χ 1 = 1) (hχ'1 : χ' 1 = 1) :
    ∀ r : ℝ, 0 ≤ r → F' r = F r := by
  obtain ⟨c, -, -, hF', h1⟩ :=
    isotropic_classification_unique hd μ hprob χ F hχ hF hF0 hrep χ' F' hχ' hF'0 hrep'
  intro r hr
  rw [hF' r hr, h1 hχ1 hχ'1, inv_one, one_mul]

/-! ## `cor:origin-profile-exponent` (Q-0409) -/

/-- `cor:origin-profile-exponent`(1), at the Matérn datum, which has no Gaussian part: its exponent
`γ log(1 + |ξ|²)` is `o(|ξ|²)`. A clause that lost the coefficient `a/2` stops this. -/
theorem probe_exponent_gaussian_limit (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun ξ : Rd d => γ * Real.log (1 + ‖ξ‖ ^ 2) / ‖ξ‖ ^ 2) (cocompact (Rd d)) (𝓝 0) := by
  have h := exponent_gaussian_limit hd (maternOriginDatum hd γ hγ)
  rw [maternOriginDatum_a hd hγ, zero_div] at h
  refine h.congr fun ξ => ?_
  rw [maternOriginDatum_exponent hd hγ]

/-- `cor:origin-profile-exponent`(2), at the Matérn datum: `γ log(1 + |ξ|²)/log|ξ| → 2γ`, the
datum's profile at the origin as `maternOriginDatum_profileAtOrigin` computes it from the profile.
A clause with another limit, or one that truncated the quotient, stops this. -/
theorem probe_exponent_profile_limit (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun ξ : Rd d => ((γ * Real.log (1 + ‖ξ‖ ^ 2) / Real.log ‖ξ‖ : ℝ) : EReal))
      (cocompact (Rd d)) (𝓝 ((2 * γ : ℝ) : EReal)) := by
  have h := exponent_profile_limit hd (maternOriginDatum hd γ hγ)
  rw [maternOriginDatum_profileAtOrigin hd hγ, EReal.coe_ennreal_ofReal,
    max_eq_left (by linarith : (0 : ℝ) ≤ 2 * γ)] at h
  refine h.congr fun ξ => ?_
  rw [maternOriginDatum_exponent hd hγ, maternOriginDatum_a hd hγ, zero_mul, zero_div, sub_zero]

/-- `cor:origin-profile-exponent`(2), the last sentence, at the Matérn law: its transform falls off
at the power `2γ`, `-log|μ̂(ξ)|/log|ξ| → 2γ`. -/
theorem probe_transform_profile_limit (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun ξ : Rd d =>
        ((-Real.log ‖charFun (gammaGaussLaw d γ) ξ‖ / Real.log ‖ξ‖ : ℝ) : EReal))
      (cocompact (Rd d)) (𝓝 ((2 * γ : ℝ) : EReal)) := by
  have h := transform_profile_limit hd (maternOriginDatum hd γ hγ) (maternOriginDatum_a hd hγ) _
    (maternOriginDatum_isLawOf hd hγ)
  rwa [maternOriginDatum_profileAtOrigin hd hγ, EReal.coe_ennreal_ofReal,
    max_eq_left (by linarith : (0 : ℝ) ≤ 2 * γ)] at h

/-- `cor:origin-profile-exponent`(3), across dimensions: an isotropic origin datum in dimension
`d'` whose exponent is the Matérn exponent `γ log(1 + |ξ|²)` has no Gaussian part and profile at
the origin `2γ`, the two numbers read on the line. A clause weakened to one dimension, or to data
whose Gaussian coefficients are given equal, stops this. -/
theorem probe_origin_profile_dimension_free {d' : ℕ} (hd' : 1 ≤ d') {γ : ℝ} (hγ : 0 < γ)
    (O : OriginDatum d') (hO : ∀ ξ : Rd d', γ * Real.log (1 + ‖ξ‖ ^ 2) = O.exponent ξ) :
    O.a = 0 ∧ O.profileAtOrigin = ENNReal.ofReal (2 * γ) := by
  have h := origin_profile_dimension_free (d := 1) le_rfl hd' (maternOriginDatum le_rfl γ hγ) O
    (fun r => γ * Real.log (1 + r ^ 2)) (fun ξ => (maternOriginDatum_exponent le_rfl hγ ξ).symm) hO
  rwa [maternOriginDatum_a (d := 1) le_rfl hγ,
    maternOriginDatum_profileAtOrigin (d := 1) le_rfl hγ] at h

/-- The nesting `𝒜_D ⊆ 𝒜_d` for `d ≤ D`, from `classA_of_succ`. -/
theorem classA_of_le {F : ℝ → ℝ} {d : ℕ} : ∀ D : ℕ, d ≤ D → classA D F → classA d F := by
  intro D hdD
  induction D, hdD using Nat.le_induction with
  | base => exact id
  | succ n _ ih => exact fun h => ih (classA_of_succ h)

/-- `cor:origin-profile-exponent`(3), read for the classes: an exponent `F ∈ 𝒜_D` has one Gaussian
coefficient `a` and one profile at the origin `c`. In every dimension `d ≤ D` it has a datum
(`prop:isotropic-polar-reading`, with the nesting), and every datum of it there has these two
numbers. A consequence under the trust base, not a Lean-core statement: it spends A2, A3 and A4
through `classA_iff_originDatum`. -/
theorem probe_origin_profile_classA {D : ℕ} (hD : 1 ≤ D) (F : ℝ → ℝ) (hF : classA D F) :
    ∃ (a : ℝ) (c : ℝ≥0∞), ∀ d : ℕ, 1 ≤ d → d ≤ D →
      (∃ O : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = O.exponent ξ) ∧
      ∀ O : OriginDatum d, (∀ ξ : Rd d, F ‖ξ‖ = O.exponent ξ) →
        O.a = a ∧ O.profileAtOrigin = c := by
  have hnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := by
    obtain ⟨P, hP⟩ := hF.1
    intro r hr
    rw [hP r hr]
    exact ENNReal.toReal_nonneg
  obtain ⟨OD, hOD⟩ := (classA_iff_originDatum hD F hnn).1 hF
  refine ⟨OD.a, OD.profileAtOrigin, fun d hd hdD =>
    ⟨(classA_iff_originDatum hd F hnn).1 (classA_of_le D hdD hF), fun O hO =>
      origin_profile_dimension_free hD hd OD O F hOD hO⟩⟩

/-- `cor:origin-profile-exponent`(3) with `thm:origin-boundedness-d`(5): the threshold theorem
applies dimension by dimension to one number. If `F` has a datum in dimension `D` with no Gaussian
part and profile at the origin `c > 0`, then every law of a datum of `F` in dimension `d` has a
density bounded near the origin exactly when `c > d`, `c` being the number read in dimension `D`.
Spends A1, through `origin_dichotomy`. -/
theorem probe_origin_profile_threshold {d D : ℕ} (hd : 1 ≤ d) (hD : 1 ≤ D) (F : ℝ → ℝ)
    (OD : OriginDatum D) (hOD : ∀ ξ : Rd D, F ‖ξ‖ = OD.exponent ξ) (ha : OD.a = 0)
    (hc : 0 < OD.profileAtOrigin) (O : OriginDatum d) (hO : ∀ ξ : Rd d, F ‖ξ‖ = O.exponent ξ)
    (μ : Measure (Rd d)) (hμ : IsLawOf O μ) :
    (∃ q : Rd d → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ x : Rd d, ‖x‖ < δ → q x ≤ M) ↔
      (d : ℝ≥0∞) < OD.profileAtOrigin := by
  obtain ⟨ha', hc'⟩ := origin_profile_dimension_free hD hd OD O F hOD hO
  rw [← hc']
  exact origin_dichotomy hd O (ha'.trans ha) (by rw [hc']; exact hc) μ hμ

/-! ## `prop:origin-upper-bound-d` (Q-0415) -/

/-- The Matérn profile at the origin against a real `β`: `β < 2γ` is `β < c`. -/
theorem maternOriginDatum_ofReal_lt (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) {β : ℝ} (hβ : β < 2 * γ) :
    ENNReal.ofReal β < (maternOriginDatum hd γ hγ).profileAtOrigin := by
  rw [maternOriginDatum_profileAtOrigin]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hβ

/-- `prop:origin-upper-bound-d`(1), at the Matérn law with `2γ ≤ d`: the mass of the ball of radius
`r` is at most a constant times `r^β`, for every `0 < β < 2γ` and at every `r > 0`. A clause
weakened to small radii, or to one exponent, stops this. -/
theorem probe_origin_upper_bound (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β < 2 * γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r →
      gammaGaussLaw d γ (Metric.ball 0 r) ≤ ENNReal.ofReal (A * r ^ β) := by
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd hγ hγd
  obtain ⟨C', hC', -, hball, -⟩ :=
    origin_upper_bound hd _ ha hc _ hlaw hcd hβ0 (maternOriginDatum_ofReal_lt hd hγ hβ)
  exact ⟨_, by positivity, hball⟩

/-- `prop:origin-upper-bound-d`(1), the sentence on the constant: a constant `C'` of
`thm:origin-boundedness-d`(4), as `origin_unbounded_rate` gives it, is enough. With
`A = (2π)^{d/2} e^{1/2} C'` the bound of clause (1) holds at the Matérn law. A lemma that asked
more of `C'` than the heat bound stops this. -/
theorem probe_origin_upper_bound_of_heat (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 2 * γ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r → (gammaGaussLaw d γ (Metric.ball 0 r)).toReal ≤
      (2 * Real.pi) ^ ((d : ℝ) / 2) * Real.exp (1 / 2) * C' * r ^ β := by
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd hγ hγd
  haveI := hlaw.1
  obtain ⟨C', hheat⟩ := (origin_unbounded_rate hd _ ha hc _ hlaw hcd).2.2.1 β hβ0
    (maternOriginDatum_ofReal_lt hd hγ hβ)
  exact ⟨C', (origin_upper_bound_of_heat hd _ hheat).1⟩

/-- `prop:origin-upper-bound-d`(2), at the Matérn law with `2γ ≤ d`: it has a radially
nonincreasing density `q(|x|)` with `q(r) ≤ C r^{β-d}` at every `r > 0`, for every `0 < β < 2γ`.
Under the trust base (A8, A2, A3(iii), for the existence of `q`). -/
theorem probe_origin_density_upper (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β < 2 * γ) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → q r ≤ C * r ^ (β - d) := by
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd hγ hγd
  obtain ⟨q, -, hq, hμq, hup⟩ := origin_density_upper hd _ ha hc _ hlaw hcd
  exact ⟨q, hq, hμq, hup β hβ0 (maternOriginDatum_ofReal_lt hd hγ hβ)⟩

/-- `prop:origin-upper-bound-d`(3), the lower bound, at the Matérn law in dimension `d ≥ 2`: every
nonincreasing radial density of it is at least `c₁ r^{2γ-d}` at every radius below some `δ`, with
no exceptional set. A clause left at almost every radius stops this. -/
theorem probe_origin_density_lower (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 < γ) (q : ℝ → ℝ)
    (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Ioo (0 : ℝ) δ, c₁ * r ^ (2 * γ - d) ≤ q r := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hc, hctop, hlaw, -⟩ := witness_origin_boundedness hd1 hγ
  obtain ⟨⟨ε₀, hε₀, hk⟩, h⟩ := origin_lower_bound hd _ ha hc hctop _ hlaw
  have hpos := (h ε₀ hε₀ hk).1
  have hc2 : (maternOriginDatum hd1 γ hγ).profileAtOrigin.toReal = 2 * γ := by
    rw [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)]
  rw [hc2] at hpos
  refine ⟨_, hpos, ε₀ / 2, by linarith [hε₀.1], fun r hr => ?_⟩
  have hb := origin_density_lower hd _ ha hc hctop _ hlaw hε₀ hk hq hμq hr
  rwa [hc2] at hb

/-- `prop:origin-upper-bound-d`(3), the first limit, at the Matérn law with `2γ ≤ d`, `d ≥ 2`: for
every nonincreasing radial density `q` of it, `log q(|x|)/log(1/|x|) → d - 2γ` as `x → 0`. A limit
with another value, or along one ray, stops this. -/
theorem probe_origin_density_log_order (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun x : Rd d => Real.log (q ‖x‖) / Real.log (1 / ‖x‖)) (𝓝[≠] 0)
      (𝓝 ((d : ℝ) - 2 * γ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd1 hγ hγd
  have h := origin_density_log_order hd _ ha hc _ hlaw hcd hq hμq
  rwa [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)] at h

/-- `prop:origin-upper-bound-d`(3), the second limit, at the Matérn law with `2γ ≤ d`, `d ≥ 2`:
`log μ{|x| < r}/log r → 2γ` as `r ↓ 0`. No density is named. -/
theorem probe_origin_ball_log_order (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    Tendsto (fun r : ℝ => Real.log (gammaGaussLaw d γ (Metric.ball 0 r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 (2 * γ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd1 hγ hγd
  have h := origin_ball_log_order hd _ ha hc _ hlaw hcd
  rwa [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)] at h

/-- `prop:origin-upper-bound-d`, the bundle, at the Matérn law with `2γ ≤ d`, `d ≥ 2`: a radially
nonincreasing density exists whose logarithmic order at the origin is `d - 2γ`. Under the trust
base (A8, A2, A3(iii)). -/
theorem probe_origin_density_order (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun x : Rd d => Real.log (q ‖x‖) / Real.log (1 / ‖x‖)) (𝓝[≠] 0)
        (𝓝 ((d : ℝ) - 2 * γ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hc, hcd, hlaw⟩ := witness_origin_upper_bound hd1 hγ hγd
  obtain ⟨q, -, hq, hμq, -, -, hlim⟩ := origin_density_order hd _ ha hc _ hlaw hcd
  refine ⟨q, hq, hμq, ?_⟩
  rwa [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)] at hlim

/-! ## `prop:origin-rate-d` (Q-0416) -/

/-- The transform of the Matérn law, as a real number: `(1 + |ξ|²)^{-γ}`. -/
theorem charFun_gammaGaussLaw_re (_hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (ξ : Rd d) :
    (charFun (gammaGaussLaw d γ) ξ).re = (1 + ‖ξ‖ ^ 2) ^ (-γ) := by
  rw [(gammaGaussLaw_transform γ hγ).2 ξ, Complex.ofReal_re]

/-- The profile at the origin of the Matérn datum, as a real number: `2γ`. -/
theorem maternOriginDatum_profileAtOrigin_toReal (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (maternOriginDatum hd γ hγ).profileAtOrigin.toReal = 2 * γ := by
  rw [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by linarith)]

/-- `prop:origin-rate-d`(1), the mass of a ball, at the Matérn law with `2γ < d`, with the
transform in closed form: `μ{|x| ≤ s} ∼ R(d,2γ) |S^{d-1}| (2γ)⁻¹ (1 + s⁻²)^{-γ}`. A clause stated
with another normaliser than the transform stops this. Spends A11. -/
theorem probe_origin_ball_rate (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d) :
    Tendsto (fun s : ℝ => (gammaGaussLaw d γ (Metric.closedBall 0 s)).toReal /
        (rateConst d (2 * γ) * sphereArea d / (2 * γ) * (1 + s⁻¹ ^ 2) ^ (-γ))) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨ha, hc, hcd, hlaw, e, he⟩ := witness_origin_rate hd hγ hγd
  have h := origin_ball_rate hd _ ha hc hcd _ hlaw he
  rw [maternOriginDatum_profileAtOrigin_toReal hd hγ] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  rw [charFun_gammaGaussLaw_re hd hγ, norm_smul, he, mul_one,
    Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]

/-- `prop:origin-rate-d`(1), the constant, at the Matérn law with `2γ < d`: every nonincreasing
radial density `q` of it has `q(s) s^{d-2γ} → R(d,2γ) = Γ(d/2-γ)/(4^γ π^{d/2} Γ(γ))` as `s ↓ 0`,
which is the leading coefficient of the closed form of the density of the law with transform
`(1 + |ξ|²)^{-γ}`. A wrong constant in the clause stops this at the comparison with the closed
form. Spends A11. -/
theorem probe_origin_density_rate_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - 2 * γ)) (𝓝[>] 0) (𝓝 (rateConst d (2 * γ))) := by
  obtain ⟨ha, hc, hcd, hlaw, e, he⟩ := witness_origin_rate hd hγ hγd
  have h := origin_density_rate hd _ ha hc hcd _ hlaw he hq hμq
  rw [maternOriginDatum_profileAtOrigin_toReal hd hγ] at h
  have hg : Tendsto (fun s : ℝ => rateConst d (2 * γ) * (1 + s ^ 2) ^ (-γ)) (𝓝[>] 0)
      (𝓝 (rateConst d (2 * γ))) := by
    have h1 : Tendsto (fun s : ℝ => rateConst d (2 * γ) * (1 + s ^ 2) ^ (-γ)) (𝓝 0)
        (𝓝 (rateConst d (2 * γ) * (1 + (0 : ℝ) ^ 2) ^ (-γ))) := by
      refine (Continuous.tendsto ?_ 0)
      refine continuous_const.mul (Continuous.rpow_const (by fun_prop) fun s => Or.inl ?_)
      positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.one_rpow,
      mul_one] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h2 := h.mul hg
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  rw [charFun_gammaGaussLaw_re hd hγ, norm_smul, he, mul_one,
    Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
  have hR := (rateConst_pos (d := d) (c := 2 * γ) (by linarith) hγd).ne'
  have e1 : (1 + s⁻¹ ^ 2) ^ (-γ) = (1 + s ^ 2) ^ (-γ) * s ^ (2 * γ) := by
    have : 1 + s⁻¹ ^ 2 = (1 + s ^ 2) * (s ^ 2)⁻¹ := by field_simp; ring
    rw [this, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le, ← Real.rpow_neg hs0.le]
    congr 2
    push_cast
    ring
  have e2 : s ^ (-(d : ℝ)) * s ^ (2 * γ) * s ^ ((d : ℝ) - 2 * γ) = 1 := by
    rw [← Real.rpow_add hs0, ← Real.rpow_add hs0]
    have : -(d : ℝ) + 2 * γ + ((d : ℝ) - 2 * γ) = 0 := by ring
    rw [this, Real.rpow_zero]
  have h1 := (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + s ^ 2) (-γ)).ne'
  have h3 := (Real.rpow_pos_of_pos hs0 (-(d : ℝ))).ne'
  have h4 := (Real.rpow_pos_of_pos hs0 (2 * γ)).ne'
  rw [e1]
  have e3 : s ^ ((d : ℝ) - 2 * γ) = (s ^ (-(d : ℝ)) * s ^ (2 * γ))⁻¹ :=
    eq_inv_of_mul_eq_one_right e2
  rw [e3]
  field_simp

/-- `prop:origin-rate-d`(2), at the Matérn law of index `γ = d/2`: every nonincreasing radial
density `q` of it has `q(s) ≥ C log(1/s)` for small `s`, for a positive `C`. A clause weakened to
"unbounded" stops this. Spends A11. -/
theorem probe_origin_density_log_lower (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), C * Real.log (1 / s) ≤ q s := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  have hA := (sphereArea_eq_toSphere hd).2
  set Cs := (2 * Real.pi) ^ (-(d : ℝ)) * sphereArea d *
    Real.exp (-(13 / 4 * (d : ℝ)) - 2 * (maternOriginDatum hd γ hγ).tailConst) with hCs
  have hCs0 : 0 < Cs := by positivity
  exact ⟨Cs / 2, by positivity,
    origin_density_log_lower hd _ ha hcd _ hlaw hq hμq (by rw [← hCs]; linarith)⟩

/-- `prop:origin-rate-d`(1), the bundle, at the Matérn law with `2γ < d`: it has a nonincreasing
radial density `q` with `q(s) s^{d-2γ} → R(d,2γ)`. Under the trust base (A11, and A8, A2, A3(iii)
for the existence of the density). -/
theorem probe_origin_rate (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - 2 * γ)) (𝓝[>] 0) (𝓝 (rateConst d (2 * γ))) := by
  obtain ⟨ha, hc, hcd, hlaw, e, he⟩ := witness_origin_rate hd hγ hγd
  obtain ⟨q, -, hq, hμq, -, -⟩ := origin_rate hd _ ha hc hcd _ hlaw he
  exact ⟨q, hq, hμq, probe_origin_density_rate_matern hd hγ hγd q hq hμq⟩

/-- `prop:origin-rate-d`(2), the bundle, at the Matérn law of index `γ = d/2`: it has a
nonincreasing radial density `q` with `q(s) ∼ (2π)^{-d} ∫_{|ξ| ≤ 1/s} (1 + |ξ|²)^{-γ} dξ`. Under the
trust base (A11, and A8, A2, A3(iii) for the existence of the density). -/
theorem probe_origin_rate_critical (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s /
        ((2 * Real.pi) ^ (-(d : ℝ)) *
          ∫ ξ in Metric.closedBall (0 : Rd d) (1 / s), (1 + ‖ξ‖ ^ 2) ^ (-γ)))
        (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  obtain ⟨q, -, hq, hμq, -, hlim, -, -⟩ := origin_rate_critical hd _ ha hcd _ hlaw
  refine ⟨q, hq, hμq, ?_⟩
  simpa only [charFun_gammaGaussLaw_re hd hγ] using hlim

/-- `prop:origin-rate-d`(2), the mass of a ball, at the Matérn law of index `γ = d/2`, with the
transform in closed form: `μ{|x| ≤ s} ∼ (2π)^{-d} V_d s^d ∫_{|ξ| ≤ 1/s} (1 + |ξ|²)^{-γ} dξ`. No
density is named. Spends A11. -/
theorem probe_origin_ball_rate_critical (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d) :
    Tendsto (fun s : ℝ => (gammaGaussLaw d γ (Metric.closedBall 0 s)).toReal /
        ((2 * Real.pi) ^ (-(d : ℝ)) * (volume (Metric.ball (0 : Rd d) 1)).toReal * s ^ d *
          ∫ ξ in Metric.closedBall (0 : Rd d) (1 / s), (1 + ‖ξ‖ ^ 2) ^ (-γ)))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  have h := origin_ball_rate_critical hd _ ha hcd _ hlaw
  simpa only [charFun_gammaGaussLaw_re hd hγ] using h

/-- `prop:origin-rate-d`(2), the density, at the Matérn law of index `γ = d/2`: every
nonincreasing radial density `q` of it has `q(s) ∼ (2π)^{-d} ∫_{|ξ| ≤ 1/s} (1 + |ξ|²)^{-γ} dξ`. A
clause for one representative only stops this. Spends A11. -/
theorem probe_origin_density_rate_critical (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s /
        ((2 * Real.pi) ^ (-(d : ℝ)) *
          ∫ ξ in Metric.closedBall (0 : Rd d) (1 / s), (1 + ‖ξ‖ ^ 2) ^ (-γ)))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  have h := origin_density_rate_critical hd _ ha hcd _ hlaw hq hμq
  simpa only [charFun_gammaGaussLaw_re hd hγ] using h

/-- `prop:origin-rate-d`(2), the logarithmic bound on the truncated transform, at the Matérn law
of index `γ = d/2`: `∫_{|ξ| ≤ 1/s} (1 + |ξ|²)^{-γ} dξ ≥ |S^{d-1}| e^{-13d/4 - 2C_k} log(1/s)` at
every `0 < s ≤ 1`, not only for small `s`. Lean core. -/
theorem probe_origin_transform_ball_log (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    sphereArea d * Real.exp (-(13 / 4 * (d : ℝ)) - 2 * (maternOriginDatum hd γ hγ).tailConst) *
        Real.log (1 / s)
      ≤ ∫ ξ in Metric.closedBall (0 : Rd d) (1 / s), (1 + ‖ξ‖ ^ 2) ^ (-γ) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  have h := origin_transform_ball_log hd _ ha hcd _ hlaw hs
  simpa only [charFun_gammaGaussLaw_re hd hγ] using h

/-! ## `lem:threshold-asymptotic` (Q-0427) -/

/-- `lem:threshold-asymptotic`(3) reads the value `π`: `d w_d² → π` along the real parameter. A
limit with another constant (`√(π/2)`, the limit of `√m w_d`, in place of `√π`) stops this. Lean
core. -/
theorem probe_threshold_sq_limit :
    Tendsto (fun d : ℝ => d * threshold d ^ 2) atTop (𝓝 Real.pi) := by
  have h := (threshold_asymptotic.2.pow 2)
  rw [Real.sq_sqrt Real.pi_pos.le] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with d hd
  rw [mul_pow, Real.sq_sqrt hd]

/-- `lem:threshold-asymptotic`(3) along the integers: `√n w_n → √π` over the dimensions. A limit
stated along a sequence other than the real parameter would not give this by composition. Lean
core. -/
theorem probe_threshold_nat :
    Tendsto (fun n : ℕ => Real.sqrt n * threshold n) atTop (𝓝 (Real.sqrt Real.pi)) :=
  threshold_asymptotic.2.comp tendsto_natCast_atTop_atTop

/-- `lem:threshold-asymptotic`(2), the lower bound at `d = 1`, where `m = 1` and `S_1 = e`:
`w_1 ≥ e/2`. A lower bound holding only for large `d`, or with another power of `m` in `S_m`,
stops this. Lean core. -/
theorem probe_threshold_one : Real.exp 1 / 2 ≤ threshold 1 := by
  have h := (threshold_asymptotic_bounds 1 le_rfl).1
  have e : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
  rw [e] at h
  simpa [stirlingRatio] using h

/-- `lem:threshold-asymptotic`(2), the upper bound at `d = 3`, where `m = 2`, at the witness
`ε_3 < 1`: `√2 w_3 ≤ S_2/(2(1-ε_3))`. Lean core. -/
theorem probe_threshold_three :
    Real.sqrt 2 * threshold 3 ≤ stirlingRatio 2 / (2 * (1 - thresholdEps 3)) := by
  have h := (threshold_asymptotic_bounds 3 witness_threshold_asymptotic.1).2
    witness_threshold_asymptotic.2
  have e : ((3 : ℝ) + 1) / 2 = 2 := by norm_num
  rwa [e] at h

/-- `S_n = √2 · n!/(√(2n) (n/e)^n)` at a positive integer `n`: the ratio `stirlingRatio` at the
integers is `√2` times Mathlib's `Stirling.stirlingSeq`. It pins the definition of `S_m` to the
object of the factorial formula. -/
theorem stirlingRatio_natCast {n : ℕ} (hn : n ≠ 0) :
    stirlingRatio n = Real.sqrt 2 * Stirling.stirlingSeq n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hG : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
    rw [Nat.cast_succ]; exact Real.Gamma_nat_eq_factorial k
  rw [stirlingRatio_eq hn0, hG, Stirling.stirlingSeq, Nat.factorial_succ, Real.rpow_natCast,
    Real.exp_neg, div_pow, ← Real.exp_nat_mul 1 (k + 1), mul_one, Real.sqrt_mul (by norm_num)]
  have hs : Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) :=
    Real.mul_self_sqrt hn0.le
  have hs0 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hn0
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  push_cast at hs hs0 hn0 ⊢
  field_simp
  nlinarith [hs]

/-- `lem:threshold-asymptotic`(1) gives Mathlib's Stirling formula for the factorial back:
`n!/(√(2n) (n/e)^n) → √π`, which is `Stirling.tendsto_stirlingSeq_sqrt_pi`, here derived from
`tendsto_stirlingRatio` along the integers. A limit of `S_m` other than `√(2π)` would contradict
Mathlib's theorem through this. Lean core. -/
theorem probe_stirling_factorial :
    Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) := by
  have h := (tendsto_stirlingRatio.comp tendsto_natCast_atTop_atTop).const_mul (Real.sqrt 2)⁻¹
  rw [Real.sqrt_mul (by norm_num), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [Function.comp_apply]
  rw [stirlingRatio_natCast hn, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## `prop:isotropic-exponent-profile` and `prop:origin-rate-profile-d` (Q-0427) -/

/-- `prop:isotropic-exponent-profile`(3) read at the step datum on the line, where `c = 1`,
`K ≡ 1`, `C_k = 0`, `λ_1 = 0` and the exponent is `Cin`: the clause gives the expansion
`Cin(ρ) - log ρ → g_∞` of the shared library back, with its constant. A limit with another
constant than `c ϰ_d` stops this. Lean core. -/
theorem probe_exponent_profile_step :
    Tendsto (fun ρ : ℝ => ScaleSpace.cin ρ - Real.log ρ) atTop (𝓝 ScaleSpace.cinConst) := by
  obtain ⟨ha, hc, -, hK, -, e, he⟩ := witness_exponent_profile
  have h := (exponent_profile_asymptotic le_rfl stepDatum ha hc he).1
  rw [stepDatum_toReal, one_mul, exponentConst, sphereLogMean_one, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with ρ hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  rw [hK ρ⁻¹ ⟨inv_pos.2 hρ0, inv_le_one_of_one_le₀ hρ⟩, Real.log_one, stepDatum_tailConst,
    one_mul, stepDatum_exponent he hρ0.le]
  ring

/-- `prop:isotropic-exponent-profile`(3), the two-sided bound, at the step datum on the line: it
is `eq:cin-log`, `-3 ≤ Cin(ρ) - log ρ ≤ 13/4` for every `ρ ≥ 1`, not only for large `ρ`. Lean
core. -/
theorem probe_exponent_profile_bounds_step {ρ : ℝ} (hρ : 1 ≤ ρ) :
    -3 ≤ ScaleSpace.cin ρ - Real.log ρ ∧ ScaleSpace.cin ρ - Real.log ρ ≤ 13 / 4 := by
  obtain ⟨ha, hc, -, hK, -, e, he⟩ := witness_exponent_profile
  have h := (exponent_profile_bounds le_rfl stepDatum ha hc he).2.2 ρ hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  rw [stepDatum_toReal, sphereLogMean_one, hK ρ⁻¹ ⟨inv_pos.2 hρ0, inv_le_one_of_one_le₀ hρ⟩,
    Real.log_one, stepDatum_tailConst, stepDatum_exponent he hρ0.le] at h
  constructor
  · linarith [h.1]
  · linarith [h.2]

/-- `prop:origin-rate-profile-d`(3), the bounds on `𝓛`, at the step datum, where `K ≡ 1`: the two
bounds coincide and `𝓛(s) = log(1/s)` at every `0 < s ≤ 1`. Lean core. -/
theorem probe_slowLog_step {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    stepDatum.slowLog s = Real.log (1 / s) := by
  obtain ⟨-, hc, -, hK, -, -⟩ := witness_exponent_profile
  have h := slowLog_bounds stepDatum hc hs
  rw [hK s hs, one_mul] at h
  exact le_antisymm h.2 h.1

/-- `prop:isotropic-exponent-profile`(4), the criterion, at the Matérn datum of index `γ`, whose
transform is `(1 + |ξ|²)^{-γ}`: `|ξ|^{2γ}(1 + |ξ|²)^{-γ} ≤ 1`, so the criterion gives that
`(2γ - k_d(u))/u` is integrable on `(0,1]`. An equivalence stated in one direction only stops
this. Lean core. -/
theorem probe_matern_profile_integrable (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun u => ((maternOriginDatum hd γ hγ).profileAtOrigin.toReal -
      (maternOriginDatum hd γ hγ).k u) / u) (Ioc 0 1) := by
  obtain ⟨ha, -, hc, -, -⟩ := witness_origin_boundedness hd hγ
  refine (transform_power_bounded_iff hd _ ha hc).1 ⟨1, fun ξ hξ => ?_⟩
  rw [maternOriginDatum_profileAtOrigin_toReal hd hγ, maternOriginDatum_exponent]
  have hξ0 : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hξ
  rw [Real.rpow_def_of_pos hξ0, ← Real.exp_add, Real.exp_le_one_iff]
  have h1 : Real.log (‖ξ‖ ^ 2) ≤ Real.log (1 + ‖ξ‖ ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow] at h1
  push_cast at h1
  nlinarith [mul_le_mul_of_nonneg_left h1 hγ.le]

/-- `prop:isotropic-exponent-profile`(4), the limit, at the Matérn datum: the limit of
`|ξ|^{2γ}(1 + |ξ|²)^{-γ}` is `1`, so `e^{-C_k - cϰ_d} K(0+) = 1` for that datum, in every
dimension. A wrong constant in the clause stops this. Lean core. -/
theorem probe_matern_profile_constant (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (maternOriginDatum hd γ hγ).profileConst * (maternOriginDatum hd γ hγ).slowFactorZero = 1 := by
  obtain ⟨ha, -, hc, -, -⟩ := witness_origin_boundedness hd hγ
  have hI := probe_matern_profile_integrable hd hγ
  haveI : NeZero d := ⟨by omega⟩
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have he0 : (ebasis (0 : Fin d) : Rd d) ≠ 0 := by
    rw [← norm_ne_zero_iff, he]; exact one_ne_zero
  have h := (transform_power_limit hd _ ha hc hI).comp (tendsto_smul_cocompact he0)
  have h1 : Tendsto (fun ρ : ℝ => Real.exp (-(γ * Real.log (1 + (ρ ^ 2)⁻¹)))) atTop (𝓝 1) := by
    have h2 : Tendsto (fun ρ : ℝ => (ρ ^ 2)⁻¹) atTop (𝓝 0) :=
      (tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
    have h3 : Tendsto (fun ρ : ℝ => -(γ * Real.log (1 + (ρ ^ 2)⁻¹))) atTop
        (𝓝 (-(γ * Real.log (1 + 0)))) :=
      ((((tendsto_const_nhds (x := (1 : ℝ))).add h2).log (by norm_num)).const_mul γ).neg
    have h4 := (Real.continuous_exp.tendsto _).comp h3
    rw [add_zero, Real.log_one, mul_zero, neg_zero, Real.exp_zero] at h4
    exact h4
  refine tendsto_nhds_unique (h.congr' ?_) h1
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  simp only [Function.comp_apply]
  rw [maternOriginDatum_profileAtOrigin_toReal hd hγ, maternOriginDatum_exponent, norm_smul, he,
    mul_one, Real.norm_of_nonneg hρ.le, Real.rpow_def_of_pos hρ, ← Real.exp_add]
  congr 1
  have hp : (0 : ℝ) < ρ ^ 2 := by positivity
  have e1 : 1 + (ρ ^ 2)⁻¹ = (1 + ρ ^ 2) / ρ ^ 2 := by field_simp; ring
  rw [e1, Real.log_div (by positivity) hp.ne', Real.log_pow]
  push_cast
  ring

/-- `prop:origin-rate-profile-d`(2), **the constant**, at the Matérn law with `2γ < d`: every
nonincreasing radial density `q` of it has `q(s) s^{d-2γ} → Q K(0+) = R(d,2γ)`, the constant that
`prop:origin-rate-d` gives through the transform (`probe_origin_density_rate_matern`) and the
leading coefficient of the closed form of the density. Here it comes through the profile:
`Q K(0+) = R(d,2γ) A K(0+)` and `A K(0+) = 1`. Spends A11. -/
theorem probe_origin_density_power_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - 2 * γ)) (𝓝[>] 0) (𝓝 (rateConst d (2 * γ))) := by
  obtain ⟨ha, hc, hcd, hlaw, -⟩ := witness_origin_rate hd hγ hγd
  have h := (origin_density_power_of_integrable hd _ ha hc hcd _ hlaw hq hμq
    (probe_matern_profile_integrable hd hγ)).1
  rw [mul_assoc, probe_matern_profile_constant hd hγ, mul_one,
    maternOriginDatum_profileAtOrigin_toReal hd hγ] at h
  exact h

/-- `prop:origin-rate-profile-d`(1)–(2), the bundle, at the Matérn law with `2γ < d`: it has a
nonincreasing radial density `q` with `q(s) s^{d-2γ} → R(d,2γ)` and `q(s) ≤ C s^{2γ-d}` at every
radius. Under the trust base (A11, and A8, A2, A3(iii) for the existence of the density). -/
theorem probe_origin_rate_profile (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s * s ^ ((d : ℝ) - 2 * γ)) (𝓝[>] 0) (𝓝 (rateConst d (2 * γ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 0 < s → q s ≤ C * s ^ (2 * γ - d) := by
  obtain ⟨ha, hc, hcd, hlaw, -⟩ := witness_origin_rate hd hγ hγd
  obtain ⟨q, -, hq, hμq, -, -, hconv, -⟩ := origin_rate_profile hd _ ha hc hcd _ hlaw
  obtain ⟨-, -, C, hC⟩ := hconv (probe_matern_profile_integrable hd hγ)
  refine ⟨q, hq, hμq, probe_origin_density_power_matern hd hγ hγd q hq hμq, C, ?_⟩
  simpa only [maternOriginDatum_profileAtOrigin_toReal hd hγ] using hC

/-- `prop:origin-rate-profile-d`(3), **the constant at the threshold**, at the Matérn law of index
`γ = d/2`: every nonincreasing radial density `q` of it has
`q(s)/log(1/s) → B K(0+) = (2π)^{-d} |S^{d-1}|`, which is `2(4π)^{-d/2}/Γ(d/2)`, the coefficient
of `log(1/|x|)` in the closed form of the density. Spends A11. -/
theorem probe_origin_density_log_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d)
    (q : ℝ → ℝ) (hq : AntitoneOn q (Ioi 0))
    (hμq : gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖))) :
    Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi) ^ (-(d : ℝ)) * sphereArea d)) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  have h := (origin_density_log_of_integrable hd _ ha hcd _ hlaw hq hμq
    (probe_matern_profile_integrable hd hγ)).1
  rwa [mul_assoc, probe_matern_profile_constant hd hγ, mul_one] at h

/-- `prop:origin-rate-profile-d`(3), the bundle, at the Matérn law of index `γ = d/2`: it has a
nonincreasing radial density `q` with `q(s)/log(1/s) → (2π)^{-d} |S^{d-1}|`. Under the trust base
(A11, and A8, A2, A3(iii) for the existence of the density). -/
theorem probe_origin_rate_profile_critical (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d) :
    ∃ q : ℝ → ℝ, AntitoneOn q (Ioi 0) ∧
      gammaGaussLaw d γ = volume.withDensity (fun x => ENNReal.ofReal (q ‖x‖)) ∧
      Tendsto (fun s : ℝ => q s / Real.log (1 / s)) (𝓝[>] 0)
        (𝓝 ((2 * Real.pi) ^ (-(d : ℝ)) * sphereArea d)) := by
  obtain ⟨ha, hcd, hlaw⟩ := witness_origin_rate_critical hd hγ hγd
  obtain ⟨q, -, hq, hμq, -, -, -, -, -⟩ := origin_rate_profile_critical hd _ ha hcd _ hlaw
  exact ⟨q, hq, hμq, probe_origin_density_log_matern hd hγ hγd q hq hμq⟩

/-! ## `thm:separating-family-critical-values` (Q-0429) -/

/-- `thm:separating-family-critical-values`(3) reads the value `π`: `D w_D² → π` along the
integers. A limit with another constant, or along another sequence, stops this. Lean core. -/
theorem probe_criticalValues_sq_limit :
    Tendsto (fun D : ℕ => (D : ℝ) * threshold D ^ 2) atTop (𝓝 Real.pi) := by
  have h := criticalValues_tendsto.pow 2
  rw [Real.sq_sqrt Real.pi_pos.le] at h
  refine h.congr fun D => ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg D)]

/-- `w_3 < 4`: `M_3 ≥ h_3(1) = e^{-1} - 2^{-3/2} e^{-1/2} > 1/8` and `Γ(2) = 1`. (The computed
value is `w_3 = 3.206`.) Lean core. -/
theorem threshold_three_lt : threshold 3 < 4 := by
  have hM := thresholdFun_le_thresholdSup (d := 3) (by norm_num) (z := 1) (by norm_num)
  have he1 : (367 / 1000 : ℝ) < Real.exp (-1) := by
    have h := Real.exp_one_lt_d9
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    norm_num
    linarith
  have he2 : Real.exp (-(1 / 2 : ℝ)) < 61 / 100 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : (100 / 61 : ℝ) < Real.exp (1 / 2 : ℝ) := by
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  have hp : (2 : ℝ) ^ (-(3 : ℝ) / 2) < 36 / 100 := by
    have h32 : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by norm_num), h32,
      inv_lt_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  have hh : (1 / 8 : ℝ) < thresholdFun 3 1 := by
    unfold thresholdFun
    rw [Real.one_rpow, one_mul, show -(1 : ℝ) / 2 = -(1 / 2) by ring]
    have hprod : (2 : ℝ) ^ (-(3 : ℝ) / 2) * Real.exp (-(1 / 2)) < 36 / 100 * (61 / 100) :=
      mul_lt_mul'' hp he2 (by positivity) (by positivity)
    linarith
  have hMpos : (1 / 8 : ℝ) < thresholdSup 3 := lt_of_lt_of_le hh hM
  unfold threshold
  rw [show ((3 : ℝ) + 1) / 2 = 2 by norm_num, Real.Gamma_two, div_lt_iff₀ (by linarith)]
  linarith

/-- `thm:separating-family-critical-values`(1) at a concrete parameter and concrete dimensions:
`F^{(4)}` is in no `𝒜_D` with `D ≥ 3`, because `w_3 < 4`. This is half of the parameter point of
[B, Lem. 4.12(3)] (`w = 4` is admitted in dimensions `1` and `2` only). The other half,
`4 ≤ w_2`, needs an upper bound of `M_2 = sup h_2`, which the library does not have (it has
`w_2 < 6 + 4√2` and the lower bounds of `lem:threshold-asymptotic`(2), which give `w_2 ≥ 1.08`):
it is not decided here. A criterion with the inequality reversed stops this. -/
theorem probe_witness_four {D : ℕ} (hD : 3 ≤ D) : ¬ classA D (witnessF 4) := by
  have h3 : threshold ((3 : ℕ) : ℝ) < 4 := by rw [Nat.cast_ofNat]; exact threshold_three_lt
  rw [witness_classA_iff (by omega) (by norm_num), not_le]
  exact (threshold_natCast_le (i := 3) (by norm_num) hD).trans_lt h3

/-- `thm:separating-family-critical-values`(4) at the right end of each window: for every integer
`d ≥ 1` the member `F^{(w_d)}` is admitted in the dimensions `1, …, d` and in no other, and `d`
is the only index whose window holds `w_d`. A clause (4) with the window open on the right, or
without uniqueness, stops this. -/
theorem probe_window_endpoint (hd : 1 ≤ d) :
    (∀ D : ℕ, 1 ≤ D → (classA D (witnessF (threshold d)) ↔ D ≤ d)) ∧
      ∀ d' : ℕ, 1 ≤ d' → threshold ((d' + 1 : ℕ) : ℝ) < threshold d →
        threshold (d : ℝ) ≤ threshold d' → d' = d := by
  obtain ⟨-, -, -, hwin, -, huniq, -⟩ := separating_family_critical_values
  have hw := (witness_separating_family hd).1
  refine ⟨fun D hD => hwin d hd _ hw.1 hw.2 D hD, fun d' hd' h1 h2 => ?_⟩
  have hpos : (0 : ℝ) < threshold d := criticalValues_strictAnti.2 d hd
  have hle : threshold (d : ℝ) ≤ threshold ((1 : ℕ) : ℝ) := threshold_natCast_le le_rfl hd
  exact (huniq _ hpos hle).unique ⟨hd', h1, h2⟩ ⟨hd, hw.1, hw.2⟩

/-! ## `lem:shadow-polar-profile` (Q-0429) -/

/-- `|S^0| = 2`: the two points of the sphere of the line. -/
theorem sphereArea_one : sphereArea 1 = 2 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold sphereArea
  rw [Nat.cast_one, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  field_simp

/-- `|S^1| = 2π`: the length of the circle. -/
theorem sphereArea_two : sphereArea 2 = 2 * Real.pi := by
  unfold sphereArea
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Real.Gamma_one, div_one]

/-- `lem:shadow-polar-profile`(1) reads the constant at `d = 1`: `C_1 = |S^0|/|S^1| = 1/π`, so
the normalisation says `∫ (1+u²)^{-1} du = π`. A normalisation with another constant, or with
the two sphere areas exchanged, stops this. Lean core. -/
theorem probe_shadow_normalisation_line :
    ∫ u : ℝ, (1 + u ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1) / 2) = Real.pi := by
  have h := (shadow_profile_mean (d := 1) le_rfl).1
  rw [sphereArea_one, sphereArea_two] at h
  have hpi := Real.pi_pos
  field_simp at h
  linarith

/-- The same integral from Mathlib alone (`integral_univ_inv_one_add_sq`), which does not read
the lemma: the two values agree, so the constant `C_1` of the lemma is the right one. -/
theorem probe_shadow_normalisation_mathlib :
    ∫ u : ℝ, (1 + u ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1) / 2) = Real.pi := by
  rw [← integral_univ_inv_one_add_sq]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [show (-(((1 : ℕ) : ℝ) + 1) / 2) = -1 by norm_num, Real.rpow_neg_one]

/-- `lem:shadow-polar-profile`(2) at the step datum: the profile `b 1_{(0,τ)}` of dimension
`d + 1` has a discontinuity, the profile of its shadow is continuous on `(0,∞)`, and the two have
the same value `b` at the origin. So the continuity of clause (2) is not inherited from `k'`, and
a clause (2) without the limit at the origin stops this. Lean core. -/
theorem probe_shadow_step (hd : 1 ≤ d) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ¬ ContinuousOn (stepOriginDatum (d + 1) hτ hb).k (Ioi 0) ∧
      ContinuousOn ((stepOriginDatum (d + 1) hτ hb).shadow hd).k (Ioi 0) ∧
      Tendsto (fun r => ENNReal.ofReal (((stepOriginDatum (d + 1) hτ hb).shadow hd).k r))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal b)) := by
  obtain ⟨-, hc, hlim⟩ := shadow_profile_regular hd (stepOriginDatum (d + 1) hτ hb)
  rw [stepOriginDatum_profileAtOrigin] at hlim
  exact ⟨stepOriginDatum_not_continuousOn (d + 1) hτ hb, hc, hlim⟩

/-- `lem:shadow-polar-profile`(3) applied twice: the shadow of the shadow of a datum of dimension
`d + 2` has the Gaussian coefficient of the datum and the exponent `ξ ↦ F''((ξ,0,0))`. A clause
(3) that returned a pair of numbers and not a datum, or lost the Gaussian coefficient, stops
this. Lean core. -/
theorem probe_shadow_twice (hd : 1 ≤ d) (D'' : OriginDatum (d + 2)) (ξ : Rd d) :
    ((D''.shadow (show 1 ≤ d + 1 by omega)).shadow hd).a = D''.a ∧
      ((D''.shadow (show 1 ≤ d + 1 by omega)).shadow hd).exponent ξ
        = D''.exponent (padZero (d + 1) (padZero d ξ)) := by
  obtain ⟨ha, -, -, -, -, hexp, -⟩ := shadow_datum hd (D''.shadow (show 1 ≤ d + 1 by omega))
  obtain ⟨ha', -, -, -, -, hexp', -⟩ := shadow_datum (show 1 ≤ d + 1 by omega) D''
  exact ⟨ha.trans ha', (hexp ξ).trans (hexp' _)⟩

/-! ## `prop:profile-one-dimension-down` (Q-0429) -/

/-- The step profile `b 1_{(0,τ)}` on the line is continuous at every `r > 0` other than `τ`:
it is continuous almost everywhere on `(0,∞)`. -/
theorem probe_step_continuous_off_edge {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) {r : ℝ} (hr : 0 < r)
    (hrτ : r ≠ τ) : ContinuousAt (cinDatum hτ hb).k r := by
  have hk : ∀ u : ℝ, (cinDatum hτ hb).k u = (Ioo (0 : ℝ) τ).indicator (fun _ => b) u :=
    fun u => stepOriginDatum_k 1 hτ hb u
  rcases lt_or_gt_of_ne hrτ with hlt | hgt
  · refine (continuousAt_const (y := b)).congr ?_
    filter_upwards [Ioo_mem_nhds hr hlt] with u hu
    rw [hk u, indicator_of_mem hu]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hgt] with u hu
    rw [hk u, indicator_of_notMem (fun h : u ∈ Ioo (0 : ℝ) τ => lt_asymm h.2 hu)]

/-- `prop:profile-one-dimension-down`(1) says "continuous" at every point of `(0,∞)`. The step
datum on the line has a profile continuous at every point but `τ`
(`probe_step_continuous_off_edge`), so a clause that gave continuity almost everywhere only
would not exclude it. With continuity at every point it is excluded: no isotropic origin datum
in the plane has the radial exponent `b Cin(τ|·|)`. This probe fails to build if "continuous" in
clause (1) is weakened to "continuous almost everywhere". -/
theorem probe_step_not_a_shadow {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ¬ ∃ D' : OriginDatum 2, ∀ ζ : Rd 2, b * ScaleSpace.cin (τ * ‖ζ‖) = D'.exponent ζ := by
  rintro ⟨D', hD'⟩
  have h := (profile_one_dimension_down (d := 1) le_rfl
    (F := fun r => b * ScaleSpace.cin (τ * |r|)) D'
    (fun ζ => by simp only [abs_norm]; exact hD' ζ)).2 (cinDatum hτ hb)
    (witness_profile_discontinuous hτ hb).1
  exact (witness_profile_discontinuous hτ hb).2 h.2.2

/-- `prop:profile-one-dimension-down`(2) at `d = 1` and clause (3): the function `G` of the step
datum on the line is the `Cin` ray `b Cin(τ ·)`, which is in `𝒜_1` and not in `𝒜_2`. A clause
(2) that asserted the exclusion without the membership stops this. -/
theorem probe_step_datum_line {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    classA 1 (fun ω => b * ScaleSpace.cin (τ * |ω|)) ∧
      ¬ classA 2 (fun ω => b * ScaleSpace.cin (τ * |ω|)) :=
  (step_datum_separates (d := 1) le_rfl hτ hb).2.1 _ fun ξ => by
    simp only [abs_norm]
    exact ((cin_ray_not_classA hτ hb).1 ξ).symm

/-- `prop:profile-one-dimension-down`(3) is in the type of `thm:no-cin-ray-in-the-plane`: the
proposition `b Cin(τ|·|) ∉ 𝒜_D` for `D ≥ 2` is proved by the two routes, the nesting on data
from the step datum on the line, and the projection from `ℝ^D` to the line in one step. -/
theorem probe_cin_ray_two_routes {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) {D : ℕ} (hD : 2 ≤ D) :
    ¬ classA D (fun ω => b * ScaleSpace.cin (τ * |ω|)) ∧
      ¬ classA D (fun ω => b * ScaleSpace.cin (τ * |ω|)) :=
  ⟨(cin_ray_not_classA hτ hb).2 D hD, (no_cin_ray_in_the_plane hD hτ hb).2⟩

/-! ## Two facts the blind check of Q-0427 could not see (its notes N2.2 and N3.1) -/

/-- Note N3.1 of `records/formalization/blind-check-q0427-report.md`: every isotropic origin
datum has a law, a probability measure with characteristic function `e^{-F_d}`. It is the `⟸`
step of `prop:isotropic-polar-reading` (`polar_reading_converse`), which rests on A3(iii), the
existence part of the theorem of Lévy and Khintchine (and, for the self-decomposability it also
asserts, on A2). So the statements of `prop:origin-rate-d` and `prop:origin-rate-profile-d`,
which are made for every `μ` with `IsLawOf D μ`, are about a class that is inhabited for every
datum, on the trust base. At the Matérn data it is inhabited on Lean core
(`witness_origin_rate`, `witness_origin_rate_critical`). -/
theorem probe_exists_isLawOf (hd : 1 ≤ d) (D : OriginDatum d) :
    ∃ μ : Measure (Rd d), IsLawOf D μ := by
  obtain ⟨μ, hprob, -, -, hchar⟩ := polar_reading_converse hd D
  exact ⟨μ, hprob, hchar⟩

/-- Note N2.2 of the same report: the closed form `sphereArea d = 2π^{d/2}/Γ(d/2)`, which the
Lévy measure and the mean `λ_d` are normalised by, is the total mass of Mathlib's surface measure
`volume.toSphere` on the unit sphere of `ℝ^d`. The library's lemma is `sphereArea_eq_toSphere`
(`def:isotropic-origin-datum`); this is its form in real numbers. Lean core. -/
theorem probe_sphereArea_total_mass (hd : 1 ≤ d) :
    ((volume : Measure (Rd d)).toSphere univ).toReal = sphereArea d := by
  obtain ⟨h, hpos⟩ := sphereArea_eq_toSphere hd
  rw [← h, ENNReal.toReal_ofReal hpos.le]

/-! ## `cor:isotropic-scale-zero-kernels` (Q-0434) -/

/-- `cor:isotropic-scale-zero-kernels`(1), from a family to its kernel, at the heat family: the
standard Gaussian law in dimension `d` is rotation invariant, self-decomposable and not `δ₀`,
because it is the kernel from scale zero to scale `1` of an isotropic cascade family. The witness
proves the same three properties from the transforms; this is the corollary's route. -/
theorem probe_scale_zero_heat (hd : 1 ≤ d) :
    IsRotationInvariant (heatFamily d 0 1) ∧ ScaleSpace.IsSelfDecomposable (heatFamily d 0 1) ∧
      heatFamily d 0 1 ≠ Measure.dirac 0 := by
  obtain ⟨hprob, hfam, -⟩ := witness_isotropic_classification (d := d) hd
  haveI := hprob 0 1 le_rfl zero_le_one
  exact (scale_zero_kernels hd (heatFamily d 0 1)).1 ⟨heatFamily d, _, 1, hfam, one_pos, rfl⟩

/-- `cor:isotropic-scale-zero-kernels`(1), the exclusion of the point mass: `δ₀` is the kernel
from scale zero to no positive scale of any isotropic cascade family. So the clause `μ ≠ δ₀` of
(S) and the positivity of the scale are read. -/
theorem probe_scale_zero_dirac (hd : 1 ≤ d) :
    ¬ ∃ (ν : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ) (t : ℝ),
      IsIsotropicCascadeFamily ν S ∧ 0 < t ∧ ν 0 t = Measure.dirac 0 :=
  fun h => ((scale_zero_kernels hd (Measure.dirac 0)).1 h).2.2 rfl

/-- `cor:isotropic-scale-zero-kernels`(2) at the Gaussian law: there is an isotropic cascade
measurement family one of whose operators from scale zero is convolution by the standard
Gaussian law. The direction from the law to the operators, at the witness. -/
theorem probe_scale_zero_operators_heat (hd : 1 ≤ d) :
    ∃ _ : IsProbabilityMeasure (heatFamily d 0 1),
      ∃ (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (S : ℝ → ℝ → ℝ) (t : ℝ),
        IsIsotropicOperatorFamily Φ S ∧ 0 < t ∧
          Φ 0 t = ScaleSpace.mconvL1E (heatFamily d 0 1) := by
  obtain ⟨hprob, hS⟩ := witness_scale_zero_kernels (d := d) hd
  exact ⟨hprob, (scale_zero_operators hd (heatFamily d 0 1)).2 hS⟩

/-- `cor:isotropic-scale-zero-kernels`(3) at the Gaussian law and the heat family: the exponent
that the clause gives is the heat exponent on `[0,∞)`, the heat family has the display with it
and the gauge `id`, which takes the value `1` at `t₁ = 1`, and so its kernels from scale zero
are the dilations of the standard Gaussian law, `μ_{0,t} = (tI)_* μ_{0,1}`. -/
theorem probe_scale_zero_families_heat (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    heatFamily d 0 t = push (t • (1 : Mat d)) (heatFamily d 0 1) := by
  obtain ⟨hprob, hfam, hχ, hF, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  obtain ⟨hprob1, hrot, hsd, hne⟩ := witness_scale_zero_kernels (d := d) hd
  obtain ⟨F, -, -, -, huniq, hall⟩ := scale_zero_families hd (heatFamily d 0 1) hrot hsd hne
  have hheat : ∀ ξ : Rd d, charFun (heatFamily d 0 1) ξ = ((Real.exp (-heatF ‖ξ‖) : ℝ) : ℂ) := by
    intro ξ
    rw [hrep 0 1 le_rfl zero_le_one ξ]
    simp only [id, zero_mul, one_mul, classA_zero hF, sub_zero]
  have hFF : ∀ r : ℝ, 0 ≤ r → heatF r = F r := huniq heatF hheat
  have hrepF : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
      ((Real.exp (-(F (id t * ‖ξ‖) - F (id s * ‖ξ‖))) : ℝ) : ℂ) := by
    intro s t hs hst ξ
    rw [hrep s t hs hst ξ, hFF (id t * ‖ξ‖) (mul_nonneg (hs.trans hst) (norm_nonneg ξ)),
      hFF (id s * ‖ξ‖) (mul_nonneg hs (norm_nonneg ξ))]
  exact ((hall 1 one_pos).1 (heatFamily d) hprob).2.2.2 id hχ hrepF t ht

/-- `cor:isotropic-scale-zero-kernels`(4) at the heat family (added after the blind check of
Q-0434, with the clause): the heat family run at the scales `t²`, `μ'_{s,t} = μ_{s²,t²}`, has
the display of the gauge `t ↦ t²`, which takes the value `1` at `t₁ = 1` as `id` does. The
clause gives a gauge `θ` with `θ(1) = 1` that relabels the heat family into it, and
`χ ∘ θ = χ'` with `χ = id` forces `θ(t) = t²` on `[0,∞)`: the relabelling is not the identity. -/
theorem probe_scale_zero_relabelling_heat (hd : 1 ≤ d) :
    ∃ θ : ℝ → ℝ, IsGauge θ ∧ θ 1 = 1 ∧ (∀ t : ℝ, 0 ≤ t → θ t = t ^ 2) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        heatFamily d (s ^ 2) (t ^ 2) = heatFamily d (θ s) (θ t) := by
  obtain ⟨hprob, hfam, hχ, hF, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  obtain ⟨hprob1, hrot, hsd, hne⟩ := witness_scale_zero_kernels (d := d) hd
  obtain ⟨F, -, -, -, huniq, hall⟩ := scale_zero_families hd (heatFamily d 0 1) hrot hsd hne
  have hheat : ∀ ξ : Rd d, charFun (heatFamily d 0 1) ξ = ((Real.exp (-heatF ‖ξ‖) : ℝ) : ℂ) := by
    intro ξ
    rw [hrep 0 1 le_rfl zero_le_one ξ]
    simp only [id, zero_mul, one_mul, classA_zero hF, sub_zero]
  have hFF : ∀ r : ℝ, 0 ≤ r → heatF r = F r := huniq heatF hheat
  have hrepF : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
      ((Real.exp (-(F (id t * ‖ξ‖) - F (id s * ‖ξ‖))) : ℝ) : ℂ) := by
    intro s t hs hst ξ
    rw [hrep s t hs hst ξ, hFF (id t * ‖ξ‖) (mul_nonneg (hs.trans hst) (norm_nonneg ξ)),
      hFF (id s * ‖ξ‖) (mul_nonneg hs (norm_nonneg ξ))]
  have hsq : IsGauge fun t : ℝ => t ^ 2 := by
    refine ⟨by simp, fun a ha b _ hab => ?_, fun y hy => ⟨Real.sqrt y, Real.sqrt_nonneg y, ?_⟩⟩
    · have ha0 : (0 : ℝ) ≤ a := ha
      show a ^ 2 < b ^ 2
      nlinarith
    · exact Real.sq_sqrt hy
  have hsqle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → s ^ 2 ≤ t ^ 2 := fun s t hs hst => by nlinarith
  obtain ⟨θ, hθ, hθ1, hθχ, heq⟩ := (hall 1 one_pos).2.2 id (fun t => t ^ 2) (heatFamily d)
    (fun s t => heatFamily d (s ^ 2) (t ^ 2)) hχ hsq rfl (by norm_num) hprob
    (fun s t hs hst => hprob _ _ (sq_nonneg s) (hsqle s t hs hst)) hrepF
    (fun s t hs hst ξ => hrepF (s ^ 2) (t ^ 2) (sq_nonneg s) (hsqle s t hs hst) ξ)
  exact ⟨θ, hθ, hθ1, fun t ht => hθχ t ht, heq⟩

/-- `cor:isotropic-scale-zero-kernels`(4) in its first sentence, at the heat family: the heat
family run at the scales `t²` is an isotropic cascade family, by the equivalence of clause (3),
its display being that of the gauge `t ↦ t²`, and it has the same kernel from scale zero to
scale `1` as the heat family. So the clause gives a gauge `θ` fixing `1` that relabels one into
the other. This probe uses the declaration for two families, `scale_zero_relabelling`; the
previous one uses the conjunct that names `θ`. -/
theorem probe_scale_zero_relabelling_families (hd : 1 ≤ d) :
    ∃ θ : ℝ → ℝ, IsGauge θ ∧ θ 1 = 1 ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      heatFamily d (s ^ 2) (t ^ 2) = heatFamily d (θ s) (θ t) := by
  obtain ⟨hprob, hfam, hχ, hF, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  obtain ⟨hprob1, hrot, hsd, hne⟩ := witness_scale_zero_kernels (d := d) hd
  obtain ⟨F, -, -, -, huniq, hall⟩ := scale_zero_families hd (heatFamily d 0 1) hrot hsd hne
  have hheat : ∀ ξ : Rd d, charFun (heatFamily d 0 1) ξ = ((Real.exp (-heatF ‖ξ‖) : ℝ) : ℂ) := by
    intro ξ
    rw [hrep 0 1 le_rfl zero_le_one ξ]
    simp only [id, zero_mul, one_mul, classA_zero hF, sub_zero]
  have hFF : ∀ r : ℝ, 0 ≤ r → heatF r = F r := huniq heatF hheat
  have hrepF : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
      ((Real.exp (-(F (id t * ‖ξ‖) - F (id s * ‖ξ‖))) : ℝ) : ℂ) := by
    intro s t hs hst ξ
    rw [hrep s t hs hst ξ, hFF (id t * ‖ξ‖) (mul_nonneg (hs.trans hst) (norm_nonneg ξ)),
      hFF (id s * ‖ξ‖) (mul_nonneg hs (norm_nonneg ξ))]
  have hsq : IsGauge fun t : ℝ => t ^ 2 := by
    refine ⟨by simp, fun a ha b _ hab => ?_, fun y hy => ⟨Real.sqrt y, Real.sqrt_nonneg y, ?_⟩⟩
    · have ha0 : (0 : ℝ) ≤ a := ha
      show a ^ 2 < b ^ 2
      nlinarith
    · exact Real.sq_sqrt hy
  have hsqle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → s ^ 2 ≤ t ^ 2 := fun s t hs hst => by nlinarith
  have hprob' : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      IsProbabilityMeasure ((fun s t : ℝ => heatFamily d (s ^ 2) (t ^ 2)) s t) :=
    fun s t hs hst => hprob _ _ (sq_nonneg s) (hsqle s t hs hst)
  obtain ⟨⟨S', hν'⟩, h1⟩ := ((hall 1 one_pos).1 _ hprob').1.2
    ⟨fun t => t ^ 2, hsq, by norm_num,
      fun s t hs hst ξ => hrepF (s ^ 2) (t ^ 2) (sq_nonneg s) (hsqle s t hs hst) ξ⟩
  exact scale_zero_relabelling hd hfam hν' one_pos h1

/-! ## The stages of a cascade (Q-0447) -/

/-- `lem:isotropic-stage-levy-measure`(3) at the Matérn datum of index `γ`: the Lévy measure of
the dilation difference has the mass `2γ log(L/ℓ)`, finite and positive. So the clause is read at
a datum with a finite positive `c`. -/
theorem probe_stage_mass_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ < L) :
    (maternOriginDatum hd γ hγ).stageMeasure ℓ L univ
      = ENNReal.ofReal (2 * γ * Real.log (L / ℓ)) := by
  rw [OriginDatum.stageMeasure_univ hd _ hℓ hL, maternOriginDatum_profileAtOrigin,
    ← ENNReal.ofReal_mul (by positivity)]

/-- `lem:isotropic-stage-levy-measure`(3) at a datum with `c = ∞`: the mass is infinite. So the
clause is read in `[0,∞]`, at its value `∞`. -/
theorem probe_stage_mass_steep (hd : 1 ≤ d) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : ℓ < L) :
    (steepDatum d).stageMeasure ℓ L univ = ⊤ := by
  rw [OriginDatum.stageMeasure_univ hd _ hℓ hL, steepDatum_profileAtOrigin, ENNReal.top_mul]
  simpa using Real.log_pos ((one_lt_div hℓ).mpr hL)

/-- `prop:isotropic-stage-atom`(2) at the Matérn kernels of index `γ` with the gauge
`χ(t) = t`: every family of probability measures with that display gives the origin the mass
`(s/t)^{2γ}` at a stage `0 < s < t`. -/
theorem probe_stage_atom_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
      ((Real.exp (-(γ * Real.log (1 + (t * ‖ξ‖) ^ 2) - γ * Real.log (1 + (s * ‖ξ‖) ^ 2))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    μ s t {0} = ENNReal.ofReal ((s / t) ^ (2 * γ)) ∧ (s / t) ^ (2 * γ) < 1 ∧
      ¬ μ s t ≪ volume ∧ ¬ ScaleSpace.IsSelfDecomposable (μ s t) := by
  have hD : ∀ ξ : Rd d, (fun r : ℝ => γ * Real.log (1 + r ^ 2)) ‖ξ‖
      = (maternOriginDatum hd γ hγ).exponent ξ := fun ξ =>
    (maternOriginDatum_exponent hd hγ ξ).symm
  have hFne : ∃ r : ℝ, 0 ≤ r ∧ (fun r : ℝ => γ * Real.log (1 + r ^ 2)) r ≠ 0 := by
    have h2 : (1 : ℝ) < 1 + 1 ^ 2 := by norm_num
    exact ⟨1, zero_le_one, (mul_pos hγ (Real.log_pos h2)).ne'⟩
  have hc : (maternOriginDatum hd γ hγ).profileAtOrigin ≠ ⊤ := by
    rw [maternOriginDatum_profileAtOrigin]
    exact ENNReal.ofReal_ne_top
  have hcr : (maternOriginDatum hd γ hγ).profileAtOrigin.toReal = 2 * γ := by
    rw [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨η, -, -, -, -, h0, -, hlt, hnac, -⟩ := isotropic_stage_atom hd (maternOriginDatum hd γ hγ)
    rfl hc isGauge_id hD hFne μ hprob hrep hs hst
  rw [hcr] at h0 hlt
  exact ⟨h0, hlt, hnac, isotropic_stage_not_selfDecomposable hd (maternOriginDatum hd γ hγ) rfl hc
    isGauge_id hD hFne μ hprob hrep hs hst⟩

/-- `prop:isotropic-stage-atom`(2) at the Matérn kernels of index `1` with the gauge
`χ(t) = t`: the point mass of the stage from `s` to `t` has the weight `(s/t)²`, a quarter for one
octave. The number of the annotation, and of the cone paper's (7.2) on the line. -/
theorem probe_stage_atom_matern_one (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
      ((Real.exp (-(1 * Real.log (1 + (t * ‖ξ‖) ^ 2) - 1 * Real.log (1 + (s * ‖ξ‖) ^ 2))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    μ s t {0} = ENNReal.ofReal ((s / t) ^ 2) ∧ μ 1 2 {0} = ENNReal.ofReal (1 / 4) := by
  have h := fun (a b : ℝ) (ha : 0 < a) (hab : a < b) =>
    (probe_stage_atom_matern hd one_pos μ hprob hrep ha hab).1
  have e : ∀ x : ℝ, x ^ ((2 : ℝ) * 1) = x ^ 2 := fun x => by rw [mul_one, Real.rpow_two]
  refine ⟨by rw [h s t hs hst, e], ?_⟩
  rw [h 1 2 one_pos one_lt_two, e]
  norm_num

/-- `prop:isotropic-stage-density`, the last sentence, at the heat family: a stage of the heat
family, whose datum has a Gaussian part, is absolutely continuous and gives the origin no mass.
The other side of the dichotomy from `probe_stage_atom_matern`. -/
theorem probe_stage_heat (hd : 1 ≤ d) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    heatFamily d s t ≪ volume ∧ heatFamily d s t {0} = 0 := by
  obtain ⟨hprob, -, hχ, -, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  have hD : ∀ ξ : Rd d, heatF ‖ξ‖ = (heatDatum d).exponent ξ := fun ξ => by
    rw [heatDatum_exponent, heatF, heatCausal_exponent (by positivity)]
  have h := isotropic_stage_dichotomy hd (heatDatum d) hχ hD (heatFamily d) hprob hrep hs hst
  have hna : ¬ ((heatDatum d).a = 0 ∧ (heatDatum d).profileAtOrigin ≠ ⊤) := fun h0 =>
    one_ne_zero h0.1
  refine ⟨h.2 hna, ?_⟩
  by_contra hne
  exact hna (h.1.mp (pos_iff_ne_zero.mpr hne))

/-- `prop:isotropic-stage-density`(3) at the heat family: a stage has a nonnegative density that
is `C^n` for every `n`. The clause is read at a datum with a Gaussian part and no jumps. -/
theorem probe_stage_heat_smooth (hd : 1 ≤ d) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ p : Rd d → ℝ, (∀ x, 0 ≤ p x) ∧ (∀ n : ℕ, ContDiff ℝ n p) ∧
      heatFamily d s t = volume.withDensity fun x => ENNReal.ofReal (p x) := by
  obtain ⟨hprob, -, hχ, -, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  have hD : ∀ ξ : Rd d, heatF ‖ξ‖ = (heatDatum d).exponent ξ := fun ξ => by
    rw [heatDatum_exponent, heatF, heatCausal_exponent (by positivity)]
  obtain ⟨p, hp0, hpC, -, hp⟩ := isotropic_stage_smooth_density hd (heatDatum d) zero_lt_one hχ hD
    (heatFamily d) hprob hrep hs hst
  exact ⟨p, hp0, hpC, hp⟩

/-- `prop:isotropic-stage-density`(1) and (2) at a datum with `a = 0` and `c = ∞`: every family
of probability measures with the display of `steepDatum` at a gauge has stages that are
infinitely divisible, absolutely continuous, and give no point a mass. -/
theorem probe_stage_steep (hd : 1 ≤ d) {F χ : ℝ → ℝ} (hχ : IsGauge χ)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = (steepDatum d).exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IsInfinitelyDivisible (μ s t) ∧ μ s t ≪ volume ∧ ∀ x : Rd d, μ s t {x} = 0 :=
  ⟨(isotropic_stage_triplet hd (steepDatum d) hχ hD μ hprob hrep hs hst).1,
    isotropic_stage_absolutelyContinuous hd (steepDatum d) rfl steepDatum_profileAtOrigin
      hχ hD μ hprob hrep hs hst,
    isotropic_stage_no_point_mass hd (steepDatum d) rfl steepDatum_profileAtOrigin
      hχ hD μ hprob hrep hs hst⟩

/-- `prop:isotropic-stage-atom`(1) and `lem:isotropic-stage-levy-measure` at the Matérn kernels
of index `γ` with the gauge `χ(t) = t`: a stage is the compound Poisson law of its Lévy measure,
and its transform is `exp[-∫ (1 - cos⟨ξ,x⟩) ν_{s,t}(dx)]`. -/
theorem probe_stage_compoundPoisson_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ)
    (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
      ((Real.exp (-(γ * Real.log (1 + (t * ‖ξ‖) ^ 2) - γ * Real.log (1 + (s * ‖ξ‖) ^ 2))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    μ s t = cpLaw ((maternOriginDatum hd γ hγ).stageMeasure s t) ∧
      ∀ ξ : Rd d, charFun (μ s t) ξ = ((Real.exp (-(0 / 2 * (t ^ 2 - s ^ 2) * ‖ξ‖ ^ 2
        + ∫ x, (1 - Real.cos (inner ℝ ξ x)) ∂((maternOriginDatum hd γ hγ).stageMeasure s t))) :
          ℝ) : ℂ) := by
  have hD : ∀ ξ : Rd d, (fun r : ℝ => γ * Real.log (1 + r ^ 2)) ‖ξ‖
      = (maternOriginDatum hd γ hγ).exponent ξ := fun ξ =>
    (maternOriginDatum_exponent hd hγ ξ).symm
  have hc : (maternOriginDatum hd γ hγ).profileAtOrigin ≠ ⊤ := by
    rw [maternOriginDatum_profileAtOrigin]
    exact ENNReal.ofReal_ne_top
  have ht := isotropic_stage_transform hd (maternOriginDatum hd γ hγ)
    (F := fun r : ℝ => γ * Real.log (1 + r ^ 2)) isGauge_id hD μ hrep hs hst
  exact ⟨(isotropic_stage_compoundPoisson hd (maternOriginDatum hd γ hγ) rfl hc
    (F := fun r : ℝ => γ * Real.log (1 + r ^ 2)) isGauge_id hD μ hprob hrep hs hst).2,
    fun ξ => ht ξ⟩

/-- `prop:isotropic-stage-atom`(4), the general fact, and the kernels from scale zero: the
standard Gaussian law is self-decomposable, so it is not a point mass of weight in `(0,1)` at the
origin plus an absolutely continuous measure. The general fact is read at a law that is
self-decomposable. -/
theorem probe_stage_atom_gaussian (hd : 1 ≤ d) (η : Measure (Rd d)) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hη : η ≪ volume) :
    heatFamily d 0 1 ≠ ENNReal.ofReal p • Measure.dirac 0 + η := by
  obtain ⟨hprob, -, hsd, -⟩ := witness_scale_zero_kernels (d := d) hd
  haveI := hprob
  exact fun h => not_selfDecomposable_of_atom hd (heatFamily d 0 1) η hp0 hp1 hη h hsd

/-- `prop:isotropic-stage-atom`(3) at the Matérn kernels of index `γ` with the gauge
`χ(t) = t`: for every family of probability measures with that display there is a density
`p ≥ 0`, integrable, of integral `1 - (s/t)^{2γ}`, with
`μ_{s,t} ∗ f = (s/t)^{2γ} f + p ∗ f` almost everywhere for every `f ∈ L¹(ℝ^d)`. Added after the
blind check of Q-0447 (F-2). -/
theorem probe_stage_operator_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
      ((Real.exp (-(γ * Real.log (1 + (t * ‖ξ‖) ^ 2) - γ * Real.log (1 + (s * ‖ξ‖) ^ 2))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ p : Rd d → ℝ, (∀ x, 0 ≤ p x) ∧ Integrable p ∧ ∫ x, p x = 1 - (s / t) ^ (2 * γ) ∧
      ∀ f : L1 d,
        (((haveI := hprob s t hs.le hst.le; ScaleSpace.mconvL1E (μ s t)) f : L1 d) : Rd d → ℝ)
          =ᵐ[volume] fun x => (s / t) ^ (2 * γ) * (f : Rd d → ℝ) x
            + ∫ y, p y * (f : Rd d → ℝ) (x - y) := by
  have hD : ∀ ξ : Rd d, (fun r : ℝ => γ * Real.log (1 + r ^ 2)) ‖ξ‖
      = (maternOriginDatum hd γ hγ).exponent ξ := fun ξ =>
    (maternOriginDatum_exponent hd hγ ξ).symm
  have hc : (maternOriginDatum hd γ hγ).profileAtOrigin ≠ ⊤ := by
    rw [maternOriginDatum_profileAtOrigin]
    exact ENNReal.ofReal_ne_top
  have hcr : (maternOriginDatum hd γ hγ).profileAtOrigin.toReal = 2 * γ := by
    rw [maternOriginDatum_profileAtOrigin, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨p, hp0, hpi, hpint, -, -, hop⟩ := isotropic_stage_operator hd (maternOriginDatum hd γ hγ)
    rfl hc (F := fun r : ℝ => γ * Real.log (1 + r ^ 2)) isGauge_id hD μ hprob hrep hs hst
  rw [hcr] at hpint hop
  exact ⟨p, hp0, hpi, hpint, hop⟩

end AffineHemigroup
