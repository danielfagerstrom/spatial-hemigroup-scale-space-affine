/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarReading
import AffineHemigroup.IsotropicClassification
import AffineHemigroup.ExponentLog

/-!
# `prop:isotropic-polar-classification`: the class `𝒜_d` and the classification in polar form

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:isotropic-polar-classification`
(`prop:isotropic-polar-reading`(2)–(3)). Wave 2, group A (Q-0281).

The blueprint's route. (2): the marginal of the law on a line is self-decomposable, with transform
`e^{-F(|ω|)}`; the polar reading at `d = 1` gives a datum `(a', k_1)`, and on the line the sphere is
`{±1}`, where the cosine profile is even, so `F_1(ω) = ½a'ω² + φ_{k_1}(ω)`, which is
`eq:admissible-line` with `a_V = a'/2` (Paper V's `SDProfile`). (3): `thm:isotropic-classification`
with clause (2), the trivial datum being the one with exponent `0` (the uniqueness of clause (1)).
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The line -/

/-- On the line, `|⟨u, η⟩| = 1` for a unit `η`, `u` the basis vector. -/
theorem abs_inner_ebasis_sphere_one (η : sphere (0 : Rd 1) 1) :
    |⟪ebasis (0 : Fin 1), (η : Rd 1)⟫| = 1 := by
  have h1 := norm_eq_of_mem_sphere η
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] at h1
  simpa [ebasis, EuclideanSpace.inner_single_left] using h1

/-- On the line, `|ω| = |⟨u, ω⟩|`. -/
theorem norm_eq_abs_inner_ebasis_one (ω : Rd 1) : ‖ω‖ = |⟪ebasis (0 : Fin 1), ω⟫| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  simp [ebasis, EuclideanSpace.inner_single_left]

/-- **The exponent of a datum on the line**: `F_1(r u) = ½a r² + φ_{k_1}(r)`. -/
theorem OriginDatum.exponentL_line (D : OriginDatum 1) (r : ℝ) :
    D.exponentL (r • ebasis (0 : Fin 1)) =
      ENNReal.ofReal (D.a * r ^ 2 / 2) + cosProfileL D.k r := by
  have hA := (sphereArea_eq_toSphere (d := 1) le_rfl)
  have hu : ‖ebasis (0 : Fin 1)‖ = 1 := by simp [ebasis]
  rw [D.exponentL_eq_sphere le_rfl, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  congr 1
  have hconst : ∀ η : sphere (0 : Rd 1) 1,
      cosProfileL D.k ⟪r • ebasis (0 : Fin 1), (η : Rd 1)⟫ = cosProfileL D.k r := by
    intro η
    rw [real_inner_smul_left]
    have h := abs_inner_ebasis_sphere_one η
    rcases abs_eq (zero_le_one) |>.mp h with h1 | h1
    · rw [h1, mul_one]
    · rw [h1, mul_neg_one, cosProfileL_neg]
  simp_rw [hconst]
  rw [lintegral_const, ← hA.1, mul_comm (cosProfileL D.k r), ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp [hA.2]) ENNReal.ofReal_ne_top, one_mul]

/-- **A datum on the line is an admissible exponent** (`eq:admissible-line`) with `a_V = a'/2` and
the same profile. -/
theorem OriginDatum.toSDProfile (D : OriginDatum 1) :
    ∃ P : ScaleSpace.SDProfile, P.a = D.a / 2 ∧ (∀ x ∈ Ioi (0 : ℝ), P.k x = D.k x) ∧
      ∀ r : ℝ, P.exponent r = D.exponent (r • ebasis (0 : Fin 1)) := by
  set k' : ℝ → ℝ := fun x => if 0 < x then D.k x else 0 with hk'
  have hk'pos : ∀ x, 0 < x → k' x = D.k x := fun x hx => by simp [hk', hx]
  let P : ScaleSpace.SDProfile := {
    a := D.a / 2
    k := k'
    a_nonneg := by have := D.a_nonneg; positivity
    k_nonneg := fun x hx => by rw [hk'pos x hx]; exact D.k_nonneg x hx
    k_antitone := fun x hx y hy hxy => by
      rw [hk'pos x hx, hk'pos y hy]; exact D.k_antitone hx hy hxy
    k_zero := by simp [hk']
    integrable_near_zero := by
      refine ne_top_of_le_ne_top D.integrable_near_zero
        (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_))
      rw [hk'pos x hx.1, mul_comm]
    integrable_at_top := by
      refine ne_top_of_le_ne_top D.integrable_at_top
        (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => ?_))
      rw [hk'pos x (by linarith)] }
  refine ⟨P, rfl, fun x hx => hk'pos x hx, fun r => ?_⟩
  rw [ScaleSpace.SDProfile.exponent, OriginDatum.exponent, D.exponentL_line]
  congr 1
  rw [ScaleSpace.SDProfile.exponentL, cosProfileL]
  congr 1
  · show ENNReal.ofReal (D.a / 2 * r ^ 2) = _
    ring_nf
  · refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
    show ENNReal.ofReal ((1 - Real.cos (r * x)) * k' x / x) = _
    rw [hk'pos x hx, mul_div_assoc, ENNReal.ofReal_mul (by linarith [Real.cos_le_one (r * x)]),
      mul_comm r x]

/-! ## Clause (2) -/

/-- The projection on the first axis, as a map into the line `ℝ¹`. -/
noncomputable def toLine (d : ℕ) [NeZero d] (x : Rd d) : Rd 1 :=
  ⟪ebasis (0 : Fin d), x⟫ • ebasis (0 : Fin 1)

theorem continuous_toLine [NeZero d] : Continuous (toLine d) := by
  unfold toLine; fun_prop

/-- `\widehat{π_*μ}(ω) = μ̂(⟨u,ω⟩ e₁)`. -/
theorem charFun_map_toLine [NeZero d] (μ : Measure (Rd d)) (ω : Rd 1) :
    charFun (μ.map (toLine d)) ω = charFun μ (⟪ebasis (0 : Fin 1), ω⟫ • ebasis (0 : Fin d)) := by
  rw [charFun_apply, charFun_apply, integral_map continuous_toLine.measurable.aemeasurable
    (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [toLine, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (ebasis (0 : Fin d)) x]
  ring_nf

/-- **`prop:isotropic-polar-classification`** (`prop:isotropic-polar-reading`(2)): if (1) holds, `F`
has a datum `(a', k_1)` in dimension `1`, and for any such datum `F` is admissible, of the form
`eq:admissible-line` with `a_V = a'/2` and `k = k_1`. -/
theorem polar_reading_admissible (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r)
    (h : ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
      ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) :
    (∃ D₁ : OriginDatum 1, ∀ ξ : Rd 1, F ‖ξ‖ = D₁.exponent ξ) ∧
      ∀ D₁ : OriginDatum 1, (∀ ξ : Rd 1, F ‖ξ‖ = D₁.exponent ξ) →
        ∃ P : ScaleSpace.SDProfile, P.a = D₁.a / 2 ∧ (∀ x ∈ Ioi (0 : ℝ), P.k x = D₁.k x) ∧
          ∀ r : ℝ, 0 ≤ r → F r = P.exponent r := by
  haveI : NeZero d := ⟨by omega⟩
  set e₁ : Rd d := ebasis (0 : Fin d) with he₁
  have he₁1 : ‖e₁‖ = 1 := by simp [he₁, ebasis]
  set u : Rd 1 := ebasis (0 : Fin 1) with hu
  have hu1 : ‖u‖ = 1 := by simp [hu, ebasis]
  refine ⟨?_, fun D₁ hD₁ => ?_⟩
  · obtain ⟨μ, hprob, hsd, hchar⟩ := h
    haveI := hprob
    haveI : IsProbabilityMeasure (μ.map (toLine d)) :=
      Measure.isProbabilityMeasure_map continuous_toLine.measurable.aemeasurable
    have hnorm : ∀ ω : Rd 1, ‖⟪u, ω⟫ • e₁‖ = ‖ω‖ := by
      intro ω
      rw [norm_smul, he₁1, mul_one, Real.norm_eq_abs, norm_eq_abs_inner_ebasis_one]
    refine (polar_reading le_rfl F hF).mp ⟨μ.map (toLine d), inferInstance, ?_, fun ω => ?_⟩
    · rw [isSelfDecomposable_iff_charFun]
      intro c hc0 hc1
      obtain ⟨ρ, hρ, hfac⟩ := (isSelfDecomposable_iff_charFun μ).1 hsd c hc0 hc1
      haveI := hρ
      refine ⟨ρ.map (toLine d),
        Measure.isProbabilityMeasure_map continuous_toLine.measurable.aemeasurable, fun ω => ?_⟩
      rw [charFun_map_toLine, charFun_map_toLine, charFun_map_toLine, hfac, real_inner_smul_right,
        smul_smul]
    · rw [charFun_map_toLine, hchar, hnorm]
  · obtain ⟨P, hPa, hPk, hPexp⟩ := D₁.toSDProfile
    refine ⟨P, hPa, hPk, fun r hr => ?_⟩
    rw [hPexp, ← hD₁]
    congr 1
    rw [norm_smul, hu1, mul_one, Real.norm_of_nonneg hr]

/-- **`prop:isotropic-polar-classification`** (`prop:isotropic-polar-reading`(2)), so: `𝒜_d` is the
set of `F` for which `F(|·|)` is the exponent of an isotropic origin datum in dimension `d`. -/
theorem classA_iff_originDatum (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r) :
    classA d F ↔ ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ := by
  constructor
  · rintro ⟨-, μ, hprob, hsd, hchar⟩
    exact (polar_reading hd F hF).mp ⟨μ, hprob, hsd, hchar⟩
  · intro hD
    have h := (polar_reading hd F hF).mpr hD
    obtain ⟨⟨D₁, hD₁⟩, hP⟩ := polar_reading_admissible hd F hF h
    obtain ⟨P, -, -, hPF⟩ := hP D₁ hD₁
    exact ⟨⟨P, hPF⟩, h⟩

/-! ## Clause (3) -/

/-- The trivial datum `(0, 0)`. -/
noncomputable def zeroDatum (d : ℕ) : OriginDatum d where
  a := 0
  k := fun _ => 0
  a_nonneg := le_rfl
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

theorem zeroDatum_exponent (ξ : Rd d) : (zeroDatum d).exponent ξ = 0 := by
  simp [OriginDatum.exponent, OriginDatum.exponentL, OriginDatum.levyMeasure, zeroDatum]

/-- A trivial datum (`a = 0`, `k_d = 0` a.e.) has exponent `0`. -/
theorem OriginDatum.exponent_eq_zero_of_trivial (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hk : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0) (ξ : Rd d) : D.exponent ξ = 0 := by
  rw [OriginDatum.exponent, OriginDatum.exponentL, ha, zero_mul, zero_div, ENNReal.ofReal_zero,
    zero_add, D.polar_decomposition_any hd _ (by fun_prop)]
  have : ∀ η : sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (1 - Real.cos ⟪ξ, r • (η : Rd d)⟫) * ENNReal.ofReal (D.k r / r) = 0 := by
    intro η
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hk] with r hr
    rw [hr, zero_div, ENNReal.ofReal_zero, mul_zero]
  simp_rw [this]
  simp

/-- A datum whose exponent vanishes is trivial (the uniqueness of `prop:isotropic-polar-reading`(1)). -/
theorem OriginDatum.trivial_of_exponent_eq_zero (hd : 1 ≤ d) (D : OriginDatum d)
    (h0 : ∀ ξ : Rd d, D.exponent ξ = 0) :
    D.a = 0 ∧ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0 := by
  have h := polar_reading_unique hd (fun _ => 0) (fun _ _ => le_rfl) D (zeroDatum d)
    (fun ξ => (h0 ξ).symm) (fun ξ => (zeroDatum_exponent ξ).symm)
  exact ⟨h.1, h.2⟩

/-- **`prop:isotropic-polar-classification`** (`prop:isotropic-polar-reading`(3)): a family of
probability measures is an isotropic cascade family if and only if there are a gauge `χ` and a datum
`(a, k_d)`, not both trivial, with `eq:isotropic-classification` for
`F(r) = ½ar² + ∫ (1 - cos(r⟨e₁,x⟩)) k_d(|x|)/(|S^{d-1}||x|^d) dx = F_d(r e₁)`. -/
theorem polar_classification (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) :
    (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S) ↔
      ∃ (χ : ℝ → ℝ) (D : OriginDatum d), IsGauge χ ∧
        (0 < D.a ∨ ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D.k r = 0) ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ s t) ξ =
          ((Real.exp (-(D.exponent ((χ t * ‖ξ‖) • ebasis (⟨0, hd⟩ : Fin d))
            - D.exponent ((χ s * ‖ξ‖) • ebasis (⟨0, hd⟩ : Fin d)))) : ℝ) : ℂ) := by
  set e₁ : Rd d := ebasis (⟨0, hd⟩ : Fin d) with he₁
  have he₁1 : ‖e₁‖ = 1 := by simp [he₁, ebasis]
  have hnorm : ∀ {c : ℝ}, 0 ≤ c → ‖c • e₁‖ = c := fun hc => by
    rw [norm_smul, he₁1, mul_one, Real.norm_of_nonneg hc]
  rw [isotropic_classification hd μ hprob]
  constructor
  · rintro ⟨χ, F, hχ, hFA, hFne, hrep⟩
    have hF0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := by
      obtain ⟨⟨P, hP⟩, -⟩ := hFA
      intro r hr; rw [hP r hr]; exact ENNReal.toReal_nonneg
    obtain ⟨D, hD⟩ := (classA_iff_originDatum hd F hF0).mp hFA
    refine ⟨χ, D, hχ, ?_, fun s t hs hst ξ => ?_⟩
    · by_contra hcon
      push Not at hcon
      have ha : D.a = 0 := le_antisymm hcon.1 D.a_nonneg
      obtain ⟨r, hr, hFr⟩ := hFne
      apply hFr
      rw [← hnorm hr, hD, D.exponent_eq_zero_of_trivial hd ha hcon.2]
    · have ht := hχ.nonneg (le_trans hs hst)
      have hs' := hχ.nonneg hs
      rw [hrep s t hs hst ξ, ← hD, ← hD, hnorm (by positivity), hnorm (by positivity)]
  · rintro ⟨χ, D, hχ, hnt, hrep⟩
    set F : ℝ → ℝ := fun r => D.exponent (r • e₁) with hF
    have hF0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := fun r _ => D.exponent_nonneg _
    have hFD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ := fun ξ =>
      D.exponent_eq_of_norm_eq (by rw [hnorm (norm_nonneg ξ)])
    refine ⟨χ, F, hχ, (classA_iff_originDatum hd F hF0).mpr ⟨D, hFD⟩, ?_, hrep⟩
    by_contra hcon
    push Not at hcon
    have h0 : ∀ ξ : Rd d, D.exponent ξ = 0 := fun ξ => by
      rw [← hFD]; exact hcon _ (norm_nonneg ξ)
    obtain ⟨ha, hk⟩ := D.trivial_of_exponent_eq_zero hd h0
    rcases hnt with h | h
    · linarith
    · exact h hk

end AffineHemigroup
