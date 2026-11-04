/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.IsotropicOperators
import AffineHemigroup.PolarClassification
import AffineHemigroup.RadialTransform
import AffineHemigroup.GaugeFacts

/-!
# `cor:isotropic-scale-zero-kernels`: the kernels from scale zero

Blueprint: `blueprint/src/parts/03-isotropic.tex`. Q-0434.

The main result of the isotropic paper as one statement: a probability measure on `ℝ^d` is the
kernel from scale zero to some scale `t > 0` of an isotropic cascade family if and only if it is
rotation invariant, self-decomposable and not `δ₀`; the same on operators; and the families with
a given such kernel at a given scale `t₁ > 0` are those of the pairs `(χ, F)`, `F` the exponent
of the law and `χ` a gauge with `χ(t₁) = 1`, one family for each such gauge.

An assembly. What it reads:

* **the exponent of the law** (`scale_zero_exponent`): the transform of a self-decomposable law
  has no zero (`selfDecomposable_charFun_ne_zero`, the shared library's doubling inequality, Lean
  core), a rotation-invariant law with such a transform has `μ̂ = e^{-g(|ξ|²)}` with `g ≥ 0`
  (`exists_exp_of_rotationInvariant`, Lean core), and `F(r) := g(r²)` is admissible by
  `polar_reading_admissible`, which spends A2, A3, A4;
* **from a family to its kernel** (`scale_zero_kernel_of_family`): the necessity direction of
  `thm:isotropic-classification` (A3 at `d = 1`) and the image of a self-decomposable law under
  a dilation;
* **from the law to a family**: `isotropic_realisation` (Lean core) at the gauge `id`;
* **the operators**: `operators_to_kernels_isotropic`, `kernels_to_operators_isotropic` and the
  uniqueness of the representing measure, as in `AffineHemigroup.IsotropicOperators`;
* **the families with this kernel** (`scale_zero_families`): the two directions of the theorem,
  its uniqueness clause, and `isotropic_realisation`.

## Trust

`scale_zero_exponent`, the two equivalences and `scale_zero_families` print A2, A3(i)–(iii) and
A4, through `polar_reading_admissible`; `scale_zero_kernel_of_family` prints A3(ii)–(iii);
`scale_zero_exponent_unique`, `scale_zero_dilation`, `scale_zero_gauge_unique` and
`scale_zero_family_unique` are Lean core.
The printed proof takes "the transform has no zero" from A4 and A3(i); the Lean takes it from the
shared library's elementary lemma, and the cited facts of the node are the same either way.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder
open ScaleSpace (IsSelfDecomposable mconvL1E)

variable {d : ℕ}

/-! ## The exponent of a rotation-invariant self-decomposable law -/

/-- **`cor:isotropic-scale-zero-kernels`(3), the exponent**: a rotation-invariant
self-decomposable probability measure on `ℝ^d` other than `δ₀` has `μ̂(ξ) = e^{-F(|ξ|)}` with
`F ∈ 𝒜_d`, `F ≢ 0`. -/
theorem scale_zero_exponent (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hrot : IsRotationInvariant μ) (hsd : IsSelfDecomposable μ) (hne : μ ≠ Measure.dirac 0) :
    ∃ F : ℝ → ℝ, classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨g, -, hgnn, -, hg⟩ :=
    exists_exp_of_rotationInvariant μ hrot (selfDecomposable_charFun_ne_zero μ hsd).1
  have hchar : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-(fun r : ℝ => g (r ^ 2)) ‖ξ‖) : ℝ) : ℂ) :=
    fun ξ => hg ξ
  have hFnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ (fun r : ℝ => g (r ^ 2)) r := fun r _ => hgnn _ (sq_nonneg r)
  have hex : ∃ ν : Measure (Rd d), IsProbabilityMeasure ν ∧ IsSelfDecomposable ν ∧
      ∀ ξ : Rd d, charFun ν ξ = ((Real.exp (-(fun r : ℝ => g (r ^ 2)) ‖ξ‖) : ℝ) : ℂ) :=
    ⟨μ, inferInstance, hsd, hchar⟩
  obtain ⟨⟨D₁, hD₁⟩, hP⟩ := polar_reading_admissible hd _ hFnn hex
  obtain ⟨P, -, -, hPF⟩ := hP D₁ hD₁
  refine ⟨fun r => g (r ^ 2), ⟨⟨P, hPF⟩, hex⟩, ?_, hchar⟩
  by_contra hall
  have hzero : ∀ r : ℝ, 0 ≤ r → g (r ^ 2) = 0 := fun r hr =>
    by_contra fun h => hall ⟨r, hr, h⟩
  apply hne
  apply eq_of_charFun_eq
  intro ξ
  rw [hchar, charFun_dirac]
  simp [hzero ‖ξ‖ (norm_nonneg ξ)]

/-- **`cor:isotropic-scale-zero-kernels`(3)**: the law determines its exponent on `[0,∞)`. -/
theorem scale_zero_exponent_unique (hd : 1 ≤ d) (μ : Measure (Rd d)) {F F' : ℝ → ℝ}
    (hF : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ))
    (hF' : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F' ‖ξ‖) : ℝ) : ℂ)) :
    ∀ r : ℝ, 0 ≤ r → F' r = F r := by
  intro r hr
  obtain ⟨ξ, hξ⟩ := exists_norm_eq hd hr
  have h := (hF ξ).symm.trans (hF' ξ)
  rw [hξ] at h
  have h2 := Real.exp_injective (Complex.ofReal_injective h)
  linarith

/-! ## From a family to its kernels from scale zero -/

/-- **`cor:isotropic-scale-zero-kernels`(1), "only if"**: a kernel from scale zero to a scale
`t > 0` of an isotropic cascade family is rotation invariant, self-decomposable and not `δ₀`. -/
theorem scale_zero_kernel_of_family (hd : 1 ≤ d) {ν : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hν : IsIsotropicCascadeFamily ν S) {t : ℝ} (ht : 0 < t) :
    IsRotationInvariant (ν 0 t) ∧ IsSelfDecomposable (ν 0 t) ∧ ν 0 t ≠ Measure.dirac 0 := by
  refine ⟨fun Q hQ => hν.rotation Q hQ 0 t le_rfl ht.le, ?_, hν.nondegenerate 0 t le_rfl ht⟩
  obtain ⟨χ, F, hχ, -, hF, -, hrep⟩ := isotropic_classification_necessity hd hν
  have hF0 := classA_zero hF
  obtain ⟨-, μ', hμ', hsd', hchar'⟩ := hF
  haveI := hμ'
  haveI := hν.isProbability 0 t le_rfl ht.le
  have heq : ν 0 t = push (χ t • (1 : Mat d)) μ' := by
    apply eq_of_charFun_eq
    intro ξ
    rw [hrep 0 t le_rfl ht.le ξ, hχ.1, zero_mul, hF0, sub_zero, charFun_push_smul_one, hchar',
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ.nonneg ht.le)]
  rw [heq]
  exact (selfDecomposable_charFun_ne_zero μ' hsd').2 _

/-- **`cor:isotropic-scale-zero-kernels`(3), the dilations**: the kernels from scale zero of a
family with the display for `(χ, F)`, `F` the exponent of `μ`, are the dilations
`μ_{0,t} = (χ(t)I)_* μ`. Stated for every `t ≥ 0`; at `t = 0` the image is that under the zero
map, `δ₀`. -/
theorem scale_zero_dilation (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {F : ℝ → ℝ}
    (hF0 : F 0 = 0) (hchar : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ))
    (ν : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) {χ : ℝ → ℝ}
    (hχ : IsGauge χ)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∀ t : ℝ, 0 ≤ t → ν 0 t = push (χ t • (1 : Mat d)) μ := by
  intro t ht
  haveI := hprob 0 t le_rfl ht
  apply eq_of_charFun_eq
  intro ξ
  rw [hrep 0 t le_rfl ht ξ, hχ.1, zero_mul, hF0, sub_zero, charFun_push_smul_one, hchar,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ.nonneg ht)]

/-! ## The families with a given kernel from scale zero -/

/-- **`cor:isotropic-scale-zero-kernels`(3), the equivalence**: let `F ∈ 𝒜_d`, `F ≢ 0`, be the
exponent of `μ` and `t₁ > 0`. A family of probability measures is an isotropic cascade family
with `μ_{0,t₁} = μ` if and only if it has the display with this `F` and a gauge `χ` with
`χ(t₁) = 1`. -/
theorem scale_zero_family_iff (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hF : classA d F) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hchar : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ))
    (ν : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ((∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily ν S) ∧ ν 0 t₁ = μ) ↔
      ∃ χ : ℝ → ℝ, IsGauge χ ∧ χ t₁ = 1 ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
          charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨⟨S, hν⟩, hμ⟩
    obtain ⟨χ', F', hχ', -, hF', -, hrep⟩ := isotropic_classification_necessity hd hν
    have hF'0 := classA_zero hF'
    have hc : 0 < χ' t₁ := hχ'.pos ht₁
    -- `F(r) = F'(χ'(t₁) r)` on `[0,∞)`, read at the scale `t₁`
    have hFF' : ∀ r : ℝ, 0 ≤ r → F' (χ' t₁ * r) = F r := by
      intro r hr
      obtain ⟨ξ, hξ⟩ := exists_norm_eq hd hr
      have h := (hrep 0 t₁ le_rfl ht₁.le ξ).symm.trans (hμ ▸ hchar ξ)
      rw [hχ'.1, zero_mul, hF'0, sub_zero, hξ] at h
      have h2 := Real.exp_injective (Complex.ofReal_injective h)
      linarith
    refine ⟨fun t => χ' t / χ' t₁, ⟨?_, ?_, ?_⟩, div_self hc.ne', fun s t hs hst ξ => ?_⟩
    · simp [hχ'.1]
    · intro a ha b hb hab
      exact div_lt_div_of_pos_right (hχ'.2.1 ha hb hab) hc
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hχ'.2.2 (show χ' t₁ * y ∈ Ici 0 from mul_nonneg hc.le hy)
      refine ⟨x, hx, ?_⟩
      simp only [hxy]
      field_simp
    · have key : ∀ u : ℝ, 0 ≤ u → F (χ' u / χ' t₁ * ‖ξ‖) = F' (χ' u * ‖ξ‖) := by
        intro u hu
        rw [← hFF' _ (mul_nonneg (div_nonneg (hχ'.nonneg hu) hc.le) (norm_nonneg ξ))]
        congr 1
        field_simp
      rw [hrep s t hs hst ξ, key t (hs.trans hst), key s hs]
  · rintro ⟨χ, hχ, hχ1, hrep⟩
    refine ⟨isotropic_classification_sufficiency hd ν hprob χ F hχ hF hFne hrep, ?_⟩
    haveI := hprob 0 t₁ le_rfl ht₁.le
    apply eq_of_charFun_eq
    intro ξ
    rw [hrep 0 t₁ le_rfl ht₁.le ξ, hχ.1, hχ1, zero_mul, one_mul, classA_zero hF, sub_zero, hchar]

/-- **`cor:isotropic-scale-zero-kernels`(3), the gauge is unique**: two gauges with the value `1`
at the same scale `t₁`, each giving the display of one family with the same `F ≢ 0`, agree on
`[0,∞)`. The uniqueness clause of `thm:isotropic-classification`, normalised at `t₁`. -/
theorem scale_zero_gauge_unique (hd : 1 ≤ d) {F : ℝ → ℝ} (hF : classA d F)
    (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) (ν : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) {t₁ : ℝ} (ht₁ : 0 < t₁)
    {χ χ' : ℝ → ℝ} (hχ : IsGauge χ) (hχ' : IsGauge χ') (h1 : χ t₁ = 1) (h1' : χ' t₁ = 1)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν s t) ξ = ((Real.exp (-(F (χ' t * ‖ξ‖) - F (χ' s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∀ t : ℝ, 0 ≤ t → χ' t = χ t := by
  obtain ⟨c, -, hχc, -, -⟩ := isotropic_classification_unique hd ν hprob χ F hχ hF hFne hrep χ' F
    hχ' (classA_zero hF) hrep'
  have hc1 : c = 1 := by
    have h := hχc t₁ ht₁.le
    rw [h1, h1', mul_one] at h
    exact h.symm
  intro t ht
  rw [hχc t ht, hc1, one_mul]

/-- **`cor:isotropic-scale-zero-kernels`(4), the relabelling of the scales, on the displays**:
two families of probability measures with the displays of one `F` and of two gauges `χ`, `χ'`
that take the value `1` at `t₁` are carried to each other by `θ = χ⁻¹ ∘ χ'`: there is a gauge
`θ` with `θ(t₁) = t₁` and `χ ∘ θ = χ'` on `[0,∞)` such that `μ'_{s,t} = μ_{θ(s),θ(t)}` on the
pairs. `θ` is chosen pointwise from the surjectivity of `χ`. The scale `t₁` is positive: at
`t₁ = 0` the premises `χ 0 = χ' 0 = 1` are false for a gauge. Lean core. -/
theorem scale_zero_relabelling_display {F : ℝ → ℝ} {t₁ : ℝ} (ht₁ : 0 < t₁) {χ χ' : ℝ → ℝ}
    (hχ : IsGauge χ) (hχ' : IsGauge χ') (h1 : χ t₁ = 1) (h1' : χ' t₁ = 1)
    (ν ν' : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t))
    (hprob' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν' s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν' s t) ξ = ((Real.exp (-(F (χ' t * ‖ξ‖) - F (χ' s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∃ θ : ℝ → ℝ, IsGauge θ ∧ θ t₁ = t₁ ∧ (∀ t : ℝ, 0 ≤ t → χ (θ t) = χ' t) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν' s t = ν (θ s) (θ t) := by
  have hex : ∀ t : ℝ, ∃ u : ℝ, 0 ≤ t → 0 ≤ u ∧ χ u = χ' t := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨u, hu, hu'⟩ := hχ.2.2 (mem_Ici.2 (hχ'.nonneg ht))
      exact ⟨u, fun _ => ⟨mem_Ici.1 hu, hu'⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose θ hθ using hex
  have hinj := hχ.2.1.injOn
  have hmono : StrictMonoOn θ (Ici 0) := by
    intro a ha b hb hab
    obtain ⟨ha0, hae⟩ := hθ a (mem_Ici.1 ha)
    obtain ⟨hb0, hbe⟩ := hθ b (mem_Ici.1 hb)
    by_contra hcon
    have h := hχ.2.1.monotoneOn (mem_Ici.2 hb0) (mem_Ici.2 ha0) (not_lt.1 hcon)
    rw [hae, hbe] at h
    exact absurd (hχ'.2.1 ha hb hab) (not_lt.2 h)
  refine ⟨θ, ⟨?_, hmono, ?_⟩, ?_, fun t ht => (hθ t ht).2, fun s t hs hst => ?_⟩
  · obtain ⟨h0, h⟩ := hθ 0 le_rfl
    exact hinj (mem_Ici.2 h0) (mem_Ici.2 le_rfl) (h.trans (hχ'.1.trans hχ.1.symm))
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hχ'.2.2 (mem_Ici.2 (hχ.nonneg (mem_Ici.1 hy)))
    obtain ⟨h0, h⟩ := hθ x (mem_Ici.1 hx)
    exact ⟨x, hx, hinj (mem_Ici.2 h0) hy (h.trans hxy)⟩
  · obtain ⟨h0, h⟩ := hθ t₁ ht₁.le
    exact hinj (mem_Ici.2 h0) (mem_Ici.2 ht₁.le) (h.trans (h1'.trans h1.symm))
  · obtain ⟨hs0, hse⟩ := hθ s hs
    obtain ⟨-, hte⟩ := hθ t (hs.trans hst)
    have hle : θ s ≤ θ t :=
      hmono.monotoneOn (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst
    haveI := hprob (θ s) (θ t) hs0 hle
    haveI := hprob' s t hs hst
    apply eq_of_charFun_eq
    intro ξ
    rw [hrep' s t hs hst ξ, hrep (θ s) (θ t) hs0 hle ξ, hse, hte]

/-- **`cor:isotropic-scale-zero-kernels`(3), "exactly one such family"**: two families of
probability measures with the display of the same pair agree at every pair `0 ≤ s ≤ t`. -/
theorem scale_zero_family_unique {F χ : ℝ → ℝ} (ν ν' : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t))
    (hprob' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν' s t))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (ν' s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν' s t = ν s t := by
  intro s t hs hst
  haveI := hprob s t hs hst
  haveI := hprob' s t hs hst
  exact eq_of_charFun_eq fun ξ => (hrep' s t hs hst ξ).trans (hrep s t hs hst ξ).symm

/-! ## The node -/

/-- **`cor:isotropic-scale-zero-kernels`(1), on kernels**: a probability measure `μ` on `ℝ^d` is
the kernel from scale zero to some scale `t > 0` of an isotropic cascade family in dimension `d`
if and only if it is rotation invariant, self-decomposable and not `δ₀`. -/
theorem scale_zero_kernels (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    (∃ (ν : ℝ → ℝ → Measure (Rd d)) (S : ℝ → ℝ → ℝ) (t : ℝ),
        IsIsotropicCascadeFamily ν S ∧ 0 < t ∧ ν 0 t = μ) ↔
      IsRotationInvariant μ ∧ IsSelfDecomposable μ ∧ μ ≠ Measure.dirac 0 := by
  constructor
  · rintro ⟨ν, S, t, hν, ht, rfl⟩
    exact scale_zero_kernel_of_family hd hν ht
  · rintro ⟨hrot, hsd, hne⟩
    obtain ⟨F, hF, hFne, hchar⟩ := scale_zero_exponent hd μ hrot hsd hne
    have hid : IsGauge id := ⟨rfl, strictMonoOn_id, fun y hy => ⟨y, hy, rfl⟩⟩
    obtain ⟨ν, hprob, ⟨S, hν⟩, hrep⟩ := isotropic_realisation hd id F hid hF hFne
    refine ⟨ν, S, 1, hν, one_pos, ?_⟩
    have h := scale_zero_dilation μ (classA_zero hF) hchar ν hprob hid hrep 1 zero_le_one
    rw [h, id, one_smul, push_one]

/-- **`cor:isotropic-scale-zero-kernels`(2), on operators**: a probability measure `μ` on `ℝ^d`
is the kernel of the operator from scale zero to some scale `t > 0` of an isotropic cascade
measurement family, `Φ_{0,t} f = μ ∗ f` for every `f ∈ L¹(ℝ^d)`, if and only if it is rotation
invariant, self-decomposable and not `δ₀`. -/
theorem scale_zero_operators (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    (∃ (Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d)) (S : ℝ → ℝ → ℝ) (t : ℝ),
        IsIsotropicOperatorFamily Φ S ∧ 0 < t ∧ Φ 0 t = mconvL1E μ) ↔
      IsRotationInvariant μ ∧ IsSelfDecomposable μ ∧ μ ≠ Measure.dirac 0 := by
  rw [← scale_zero_kernels hd μ]
  constructor
  · rintro ⟨Φ, S, t, hΦ, ht, hμ⟩
    obtain ⟨ν, hν⟩ := exists_kernels_of_isotropicOperatorFamily hd hΦ
    refine ⟨ν, S, t, operators_to_kernels_isotropic hd Φ S hΦ ν hν, ht, ?_⟩
    obtain ⟨_, h⟩ := hν 0 t le_rfl ht.le
    exact eq_of_mconvL1E_eq (h.symm.trans hμ)
  · rintro ⟨ν, S, t, hν, ht, rfl⟩
    obtain ⟨Φ, hΦ⟩ := exists_operators_of_kernels ν hν.isProbability
    exact ⟨Φ, S, t, (kernels_to_operators_isotropic hd ν S hν Φ hΦ).1, ht,
      (hΦ 0 t le_rfl ht.le).2⟩

/-- **`cor:isotropic-scale-zero-kernels`(3), the families with this kernel, and the second
sentence of (4)**: let `μ` be
rotation invariant, self-decomposable and not `δ₀`. There is an `F ∈ 𝒜_d`, `F ≢ 0`, with
`μ̂(ξ) = e^{-F(|ξ|)}`, determined by `μ` on `[0,∞)`, such that for every `t₁ > 0`: a family of
probability measures is an isotropic cascade family with `μ_{0,t₁} = μ` if and only if it has
the display with `F` and a gauge `χ` with `χ(t₁) = 1`; that gauge is unique on `[0,∞)`; two
families with the display of one gauge agree at every pair; every gauge with `χ(t₁) = 1` has such
a family; the kernels from scale zero of a family with the display for a gauge `χ` and `F`
are the dilations `(χ(t)I)_* μ`; and two families with the displays of two gauges `χ`, `χ'` with
the value `1` at `t₁` are carried to each other by the gauge `θ` with `χ ∘ θ = χ'` on `[0,∞)`,
which fixes `t₁`. -/
theorem scale_zero_families (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hrot : IsRotationInvariant μ) (hsd : IsSelfDecomposable μ) (hne : μ ≠ Measure.dirac 0) :
    ∃ F : ℝ → ℝ, classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) ∧
      (∀ F' : ℝ → ℝ, (∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F' ‖ξ‖) : ℝ) : ℂ)) →
        ∀ r : ℝ, 0 ≤ r → F' r = F r) ∧
      ∀ t₁ : ℝ, 0 < t₁ →
        (∀ ν : ℝ → ℝ → Measure (Rd d), (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) →
          (((∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily ν S) ∧ ν 0 t₁ = μ) ↔
            ∃ χ : ℝ → ℝ, IsGauge χ ∧ χ t₁ = 1 ∧
              ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
                charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) ∧
          (∀ χ χ' : ℝ → ℝ, IsGauge χ → IsGauge χ' → χ t₁ = 1 → χ' t₁ = 1 →
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) →
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν s t) ξ = ((Real.exp (-(F (χ' t * ‖ξ‖) - F (χ' s * ‖ξ‖))) : ℝ) : ℂ)) →
            ∀ t : ℝ, 0 ≤ t → χ' t = χ t) ∧
          (∀ (χ : ℝ → ℝ) (ν' : ℝ → ℝ → Measure (Rd d)),
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν' s t)) →
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) →
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν' s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) →
            ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν' s t = ν s t) ∧
          (∀ χ : ℝ → ℝ, IsGauge χ →
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) →
            ∀ t : ℝ, 0 ≤ t → ν 0 t = push (χ t • (1 : Mat d)) μ)) ∧
        (∀ χ : ℝ → ℝ, IsGauge χ → χ t₁ = 1 →
          ∃ ν : ℝ → ℝ → Measure (Rd d),
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) ∧
            ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
              charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) ∧
        ∀ (χ χ' : ℝ → ℝ) (ν ν' : ℝ → ℝ → Measure (Rd d)),
          IsGauge χ → IsGauge χ' → χ t₁ = 1 → χ' t₁ = 1 →
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν s t)) →
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ν' s t)) →
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
            charFun (ν s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ)) →
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
            charFun (ν' s t) ξ = ((Real.exp (-(F (χ' t * ‖ξ‖) - F (χ' s * ‖ξ‖))) : ℝ) : ℂ)) →
          ∃ θ : ℝ → ℝ, IsGauge θ ∧ θ t₁ = t₁ ∧ (∀ t : ℝ, 0 ≤ t → χ (θ t) = χ' t) ∧
            ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν' s t = ν (θ s) (θ t) := by
  obtain ⟨F, hF, hFne, hchar⟩ := scale_zero_exponent hd μ hrot hsd hne
  refine ⟨F, hF, hFne, hchar, fun F' hF' => scale_zero_exponent_unique hd μ hchar hF',
    fun t₁ ht₁ => ⟨fun ν hprob => ⟨scale_zero_family_iff hd μ hF hFne hchar ν hprob ht₁,
      fun χ χ' hχ hχ' h1 h1' hrep hrep' =>
        scale_zero_gauge_unique hd hF hFne ν hprob ht₁ hχ hχ' h1 h1' hrep hrep',
      fun χ ν' hprob' hrep hrep' => scale_zero_family_unique ν ν' hprob hprob' hrep hrep',
      fun χ hχ hrep => scale_zero_dilation μ (classA_zero hF) hchar ν hprob hχ hrep⟩,
      fun χ hχ _ => ?_,
      fun χ χ' ν ν' hχ hχ' h1 h1' hprob hprob' hrep hrep' =>
        scale_zero_relabelling_display ht₁ hχ hχ' h1 h1' ν ν' hprob hprob' hrep hrep'⟩⟩
  obtain ⟨ν, hprob, -, hrep⟩ := isotropic_realisation hd χ F hχ hF hFne
  exact ⟨ν, hprob, hrep⟩

/-- **`cor:isotropic-scale-zero-kernels`(4), up to the relabelling of the scales**: two isotropic
cascade families with the same kernel from scale zero to a scale `t₁ > 0` are carried to each
other by an increasing bijection `θ` of `[0,∞)` that fixes `t₁`: `μ'_{s,t} = μ_{θ(s),θ(t)}` for
all `0 ≤ s ≤ t`. The gauges are those of clause (3) for the law `μ_{0,t₁}`, and `θ = χ⁻¹ ∘ χ'`
(`scale_zero_relabelling_display`, which the last conjunct of `scale_zero_families` states). -/
theorem scale_zero_relabelling (hd : 1 ≤ d) {ν ν' : ℝ → ℝ → Measure (Rd d)} {S S' : ℝ → ℝ → ℝ}
    (hν : IsIsotropicCascadeFamily ν S) (hν' : IsIsotropicCascadeFamily ν' S') {t₁ : ℝ}
    (ht₁ : 0 < t₁) (h : ν' 0 t₁ = ν 0 t₁) :
    ∃ θ : ℝ → ℝ, IsGauge θ ∧ θ t₁ = t₁ ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ν' s t = ν (θ s) (θ t) := by
  haveI := hν.isProbability 0 t₁ le_rfl ht₁.le
  obtain ⟨hrot, hsd, hne⟩ := scale_zero_kernel_of_family hd hν ht₁
  obtain ⟨F, hF, hFne, hchar⟩ := scale_zero_exponent hd (ν 0 t₁) hrot hsd hne
  obtain ⟨χ, hχ, h1, hrep⟩ :=
    (scale_zero_family_iff hd (ν 0 t₁) hF hFne hchar ν hν.isProbability ht₁).1 ⟨⟨S, hν⟩, rfl⟩
  obtain ⟨χ', hχ', h1', hrep'⟩ :=
    (scale_zero_family_iff hd (ν 0 t₁) hF hFne hchar ν' hν'.isProbability ht₁).1 ⟨⟨S', hν'⟩, h⟩
  obtain ⟨θ, hθ, hθ1, -, heq⟩ := scale_zero_relabelling_display ht₁ hχ hχ' h1 h1' ν ν'
    hν.isProbability hν'.isProbability hrep hrep'
  exact ⟨θ, hθ, hθ1, heq⟩

end AffineHemigroup
