/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KernelsOperators
import AffineHemigroup.IsotropicClassification

/-!
# `cor:isotropic-classification-operators`: the isotropic classification on operators

Blueprint: `blueprint/src/parts/03-isotropic.tex`. Q-0407.

`thm:isotropic-classification` read on the operator axioms of `def:isotropic-operator-family`, by
assembly, as `AffineHemigroup.RigidityOperators` reads `thm:affine-rigidity` on the operator axioms
of the case `(GL(d), Loewner)`:

* **necessity**: the representing measures exist by `lem:operators-to-kernels`(1)
  (`operators_to_kernels_repr`), they form an isotropic cascade family by
  `lem:operators-to-kernels-families`(5) (`operators_to_kernels_isotropic`), and the necessity
  direction of the theorem gives the pair;
* **sufficiency**: the sufficiency direction of the theorem makes the measures an isotropic cascade
  family, and `lem:kernels-to-operators`(3) (`kernels_to_operators_isotropic`) makes the operators
  an isotropic cascade measurement family;
* **uniqueness**: two families of probability measures representing the same operators agree on
  `{0 ≤ s ≤ t}` (`eq_of_mconvL1E_eq`, the uniqueness clause of `lem:operators-to-kernels`(1)), so
  the second pair satisfies the display for the first family and the theorem's uniqueness clause
  applies.

## Trust

`isotropic_classification_operators` prints what `isotropic_classification` prints, ledger
A3(ii)–(iii) at `d = 1` through the necessity direction, and nothing else; the sufficiency direction
and the uniqueness clause are Lean core. All four declarations are listed in `CIAxiomGuard.lean`.

## Reading

As everywhere in the operator form (`AffineHemigroup.Defs.Operators`): (A1) is the type of
`Φ s t`, a bounded linear operator; the families `Φ` and `μ` are totalised and read on
`{0 ≤ s ≤ t}` only; `Φ s t = mconvL1E (μ s t)` is the equation of operators
`Φ_{s,t} f = μ_{s,t} ∗ f` for every `f ∈ L¹(ℝ^d)`; and (A8)'s family `(S_λ)` is the `S` under the
existential quantifier.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder
open ScaleSpace (mconvL1E)

variable {d : ℕ}

/-- The operators of an isotropic cascade measurement family are convolutions by probability
measures (`lem:operators-to-kernels`(1) at each pair): a representing family, chosen at every pair
of reals and constrained on `{0 ≤ s ≤ t}` only. -/
theorem exists_kernels_of_isotropicOperatorFamily (hd : 1 ≤ d)
    {Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)} {S : ℝ → ℝ → ℝ} (hΦ : IsIsotropicOperatorFamily Φ S) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t) := by
  have hex : ∀ s t : ℝ, ∃ μ : Measure (Rd d),
      0 ≤ s → s ≤ t → ∃ _ : IsProbabilityMeasure μ, Φ s t = mconvL1E μ := by
    intro s t
    by_cases h : 0 ≤ s ∧ s ≤ t
    · obtain ⟨μ, hμ, -⟩ := operators_to_kernels_repr hd (Φ s t) (hΦ.single s t h.1 h.2)
      exact ⟨μ, fun _ _ => hμ⟩
    · exact ⟨0, fun h0 h1 => absurd ⟨h0, h1⟩ h⟩
  choose μ hμ using hex
  exact ⟨μ, hμ⟩

/-- Every family of probability measures on `{0 ≤ s ≤ t}` is represented by operators on
`L¹(ℝ^d)`: convolution by the family, extended by `δ₀` off the pairs. -/
theorem exists_operators_of_kernels (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) :
    ∃ Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d), ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t) := by
  haveI := isProbabilityMeasure_extendOnScales hμ
  refine ⟨fun s t => mconvL1E (extendOnScales μ (s, t)), fun s t hs hst => ?_⟩
  haveI := hμ s t hs hst
  refine ⟨inferInstance, ScaleSpace.mconvL1E_congr ?_⟩
  simp only [extendOnScales, if_pos (show (0 : ℝ) ≤ s ∧ s ≤ t from ⟨hs, hst⟩)]

/-- **`cor:isotropic-classification-operators`, necessity**: the operators of an isotropic cascade
measurement family are convolutions by probability measures with the display, for a normalised
gauge and an `F ∈ 𝒜_d`, `F ≢ 0`. Spends ledger A3 at `d = 1`, through
`isotropic_classification_necessity`, and nothing else. -/
theorem isotropic_classification_operators_necessity (hd : 1 ≤ d)
    {Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)} {S : ℝ → ℝ → ℝ} (hΦ : IsIsotropicOperatorFamily Φ S) :
    ∃ (χ F : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d)),
      IsGauge χ ∧ χ 1 = 1 ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨μ, hμ⟩ := exists_kernels_of_isotropicOperatorFamily hd hΦ
  obtain ⟨χ, F, hχ, hχ1, hF, hFne, hrep⟩ :=
    isotropic_classification_necessity hd (operators_to_kernels_isotropic hd Φ S hΦ μ hμ)
  exact ⟨χ, F, μ, hχ, hχ1, hF, hFne, hμ, hrep⟩

/-- **`cor:isotropic-classification-operators`, sufficiency**: operators that are convolution by
probability measures with the display, for a gauge `χ` and an `F ∈ 𝒜_d` with `F ≢ 0`, form an
isotropic cascade measurement family, with the dilation action `S_λ = χ^{-1}(λχ(·))`. Lean core. -/
theorem isotropic_classification_operators_sufficiency (hd : 1 ≤ d)
    (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (χ F : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d))
    (hχ : IsGauge χ) (hF : classA d F) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∃ S : ℝ → ℝ → ℝ, IsIsotropicOperatorFamily Φ S := by
  obtain ⟨S, hμ⟩ := isotropic_classification_sufficiency hd μ
    (fun s t hs hst => (hΦ s t hs hst).1) χ F hχ hF hFne hrep
  exact ⟨S, (kernels_to_operators_isotropic hd μ S hμ Φ hΦ).1⟩

/-- **`cor:isotropic-classification-operators`**: a family `(Φ_{s,t})_{0 ≤ s ≤ t}` of linear
operators on `L¹(ℝ^d)` is an isotropic cascade measurement family if and only if there are a gauge
`χ`, an `F ∈ 𝒜_d` with `F ≢ 0`, and probability measures `μ_{s,t}` with
`μ̂_{s,t}(ξ) = exp[-(F(χ(t)|ξ|) - F(χ(s)|ξ|))]` such that `Φ_{s,t} f = μ_{s,t} ∗ f` for every pair
and every `f ∈ L¹(ℝ^d)`. -/
theorem isotropic_classification_operators (hd : 1 ≤ d) (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) :
    (∃ S : ℝ → ℝ → ℝ, IsIsotropicOperatorFamily Φ S) ↔
      ∃ (χ F : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d)),
        IsGauge χ ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t →
          ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t)) ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
          charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨S, hΦ⟩
    obtain ⟨χ, F, μ, hχ, -, hF, hFne, hμ, hrep⟩ :=
      isotropic_classification_operators_necessity hd hΦ
    exact ⟨χ, F, μ, hχ, hF, hFne, hμ, hrep⟩
  · rintro ⟨χ, F, μ, hχ, hF, hFne, hμ, hrep⟩
    exact isotropic_classification_operators_sufficiency hd Φ χ F μ hχ hF hFne hμ hrep

/-- **`cor:isotropic-classification-operators`**, uniqueness: if a gauge `χ'`, a real function
`F'` on `[0,∞)` with `F'(0) = 0` and probability measures `μ'_{s,t}` with the display for
`(χ', F')` also represent the operators, `Φ_{s,t} f = μ'_{s,t} ∗ f`, then `μ'_{s,t} = μ_{s,t}` for
every pair, `χ' = cχ` and `F' = F(c⁻¹ ·)` for some `c > 0`, and `c = 1` when
`χ(1) = χ'(1) = 1`. Lean core. -/
theorem isotropic_classification_operators_unique (hd : 1 ≤ d)
    (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (χ F : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d))
    (hχ : IsGauge χ) (hF : classA d F) (hF0 : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ s t), Φ s t = mconvL1E (μ s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (μ' : ℝ → ℝ → Measure (Rd d)) (hχ' : IsGauge χ') (hF'0 : F' 0 = 0)
    (hΦ' : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∃ _ : IsProbabilityMeasure (μ' s t), Φ s t = mconvL1E (μ' s t))
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ' s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ)) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ s t) ∧
      ∃ c : ℝ, 0 < c ∧ (∀ t : ℝ, 0 ≤ t → χ' t = c * χ t) ∧
        (∀ r : ℝ, 0 ≤ r → F' r = F (c⁻¹ * r)) ∧ (χ 1 = 1 → χ' 1 = 1 → c = 1) := by
  have hμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ s t := by
    intro s t hs hst
    obtain ⟨_, h⟩ := hΦ s t hs hst
    obtain ⟨_, h'⟩ := hΦ' s t hs hst
    exact eq_of_mconvL1E_eq (h'.symm.trans h)
  refine ⟨hμ, ?_⟩
  exact isotropic_classification_unique hd μ (fun s t hs hst => (hΦ s t hs hst).1) χ F hχ hF hF0
    hrep χ' F' hχ' hF'0 (fun s t hs hst ξ => by rw [← hμ s t hs hst]; exact hrep' s t hs hst ξ)

end AffineHemigroup
