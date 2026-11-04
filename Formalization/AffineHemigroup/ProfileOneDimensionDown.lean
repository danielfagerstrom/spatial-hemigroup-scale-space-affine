/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ShadowProfile
import AffineHemigroup.NoCinRay

/-!
# `prop:profile-one-dimension-down`: the profile one dimension down is continuous

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `prop:profile-one-dimension-down` (Q-0429):
the statements on data that follow from `lem:shadow-polar-profile`, the polar form of the classes
(`prop:isotropic-polar-classification`(2), `classA_iff_originDatum`) and the uniqueness of a
datum (`prop:isotropic-polar-reading`(1), `polar_reading_unique`). No law, no characteristic
function and no dictionary is named. The cited facts A2, A3, A4 enter through those two
statements only.

* Clause (1), `profile_one_dimension_down`: for a datum `(a', k')` in dimension `d + 1` with
  exponent `ζ ↦ F(|ζ|)`, `F ∈ 𝒜_d`, and every datum `(a, k_d)` in dimension `d` with exponent
  `ξ ↦ F(|ξ|)` has `a = a'` and `k_d(r) = k̄(r)` at every `r > 0`, so `k_d` is continuous on
  `(0,∞)`. The uniqueness gives the equality almost everywhere; a nonincreasing function equal
  almost everywhere to a continuous one equals it everywhere
  (`eq_of_ae_eq_of_antitoneOn_of_continuousOn`). Its contrapositive,
  `not_classA_succ_of_profile_discontinuous`: a datum of dimension `d` whose profile is not
  continuous on `(0,∞)` has its exponent outside `𝒜_{d+1}`.
* Clause (2), `step_datum_separates`: the step datum `(0, b 1_{(0,τ)})` in dimension `d`
  (`stepOriginDatum`), its radial exponent `G`, `G ∈ 𝒜_d ∖ 𝒜_{d+1}`, and
  `𝒜_{d+1} ⊊ 𝒜_d`.
* Clause (3), `cin_ray_not_classA`: at `d = 1` the exponent is `b Cin(τ|ω|)`, and no `Cin` ray is
  in `𝒜_D` for `D ≥ 2`. The conclusion is in the type of `no_cin_ray_in_the_plane`, which proves
  it by a projection from `ℝ^D` to the line in one step.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## A nonincreasing function equal almost everywhere to a continuous one -/

/-- A function nonincreasing on `(0,∞)` that equals a function continuous on `(0,∞)` almost
everywhere there equals it at every point: at `r > 0` it lies between the values at points of
agreement on either side, and those tend to the value of the continuous function at `r`.
Mathlib types only. -/
theorem eq_of_ae_eq_of_antitoneOn_of_continuousOn {f g : ℝ → ℝ} (hf : AntitoneOn f (Ioi 0))
    (hg : ContinuousOn g (Ioi 0)) (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), f r = g r) {r : ℝ}
    (hr : 0 < r) : f r = g r := by
  have hgc : ContinuousAt g r := hg.continuousAt (Ioi_mem_nhds hr)
  refine le_antisymm ?_ ?_
  · -- points of agreement below `r`
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 (hgc.eventually_lt_const hcon)
    set a := max (r - ε) (r / 2) with ha
    have ha0 : 0 ≤ a := le_trans (by linarith) (le_max_right _ _)
    have har : a < r := max_lt (by linarith) (by linarith)
    obtain ⟨u, hu, hfu⟩ := exists_ae_eq_mem_Ioo h ha0 har
    have hu0 : 0 < u := lt_of_le_of_lt ha0 hu.1
    have hua : r - ε < u := lt_of_le_of_lt (le_max_left _ _) hu.1
    have h1 : g u < f r := hb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.2])
    have h2 : f r ≤ f u := hf hu0 hr hu.2.le
    linarith
  · -- points of agreement above `r`
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 (hgc.eventually_const_lt hcon)
    obtain ⟨u, hu, hfu⟩ := exists_ae_eq_mem_Ioo h hr.le (show r < r + ε by linarith)
    have hu0 : 0 < u := lt_trans hr hu.1
    have h1 : f r < g u := hb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
    have h2 : f u ≤ f r := hf hr hu0 hu.1.le
    linarith

/-! ## Clause (1) -/

/-- A function that is the radial exponent of an origin datum in dimension `d ≥ 1` is nonnegative
on `[0,∞)`: every `r ≥ 0` is a norm. -/
theorem nonneg_of_radial_exponent (hd : 1 ≤ d) {F : ℝ → ℝ} (D : OriginDatum d)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ F r := by
  have hn : ‖r • (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Rd d)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr]
    simp
  rw [← hn, hD]
  exact D.exponent_nonneg _

/-- The exponent of an isotropic origin datum in dimension `d ≥ 1` is radial: it is `ξ ↦ G(|ξ|)`
for a function `G`, which the datum determines on `[0,∞)`. The invariance under rotations is
`OriginDatum.exponent_eq_of_norm_eq`. -/
theorem exists_radial_exponent (hd : 1 ≤ d) (D : OriginDatum d) :
    ∃ G : ℝ → ℝ, ∀ ξ : Rd d, G ‖ξ‖ = D.exponent ξ := by
  set e : Rd d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  exact ⟨fun r => D.exponent (r • e), fun ξ =>
    D.exponent_eq_of_norm_eq (by rw [norm_smul, hen, mul_one, norm_norm])⟩

/-- **`prop:profile-one-dimension-down`(1)**: let `(a', k')` be an isotropic origin datum in
dimension `d + 1` with exponent `ζ ↦ F(|ζ|)`. Then `F ∈ 𝒜_d`, and every isotropic origin datum
`(a, k_d)` in dimension `d` with exponent `ξ ↦ F(|ξ|)` has `a = a'` and
`k_d(r) = C_d ∫ k'(r√(1+u²)) (1+u²)^{-(d+1)/2} du` for every `r > 0`; in particular `k_d` is
continuous on `(0,∞)`. Spends A2, A3, A4 through the polar form of the classes and the uniqueness
of a datum. -/
theorem profile_one_dimension_down (hd : 1 ≤ d) {F : ℝ → ℝ} (D' : OriginDatum (d + 1))
    (hD' : ∀ ζ : Rd (d + 1), F ‖ζ‖ = D'.exponent ζ) :
    classA d F ∧ ∀ D : OriginDatum d, (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) →
      D.a = D'.a ∧ (∀ r : ℝ, 0 < r → D.k r = shadowProfile d D'.k r) ∧
        ContinuousOn D.k (Ioi 0) := by
  have hS : ∀ ξ : Rd d, F ‖ξ‖ = (D'.shadow hd).exponent ξ :=
    fun ξ => D'.shadow_exponent_radial hd hD' ξ
  have hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := nonneg_of_radial_exponent hd (D'.shadow hd) hS
  have hcont := shadowProfile_continuousOn hd D'.k_nonneg D'.k_antitone
  refine ⟨(classA_iff_originDatum hd F hF).2 ⟨D'.shadow hd, hS⟩, fun D hD => ?_⟩
  obtain ⟨ha, hk⟩ := polar_reading_unique hd F hF D (D'.shadow hd) hD hS
  have hpt : ∀ r : ℝ, 0 < r → D.k r = shadowProfile d D'.k r := fun r hr =>
    eq_of_ae_eq_of_antitoneOn_of_continuousOn D.k_antitone hcont hk hr
  exact ⟨ha, hpt, hcont.congr fun r hr => hpt r hr⟩

/-- **`prop:profile-one-dimension-down`(1), with the class as the hypothesis**: if
`F ∈ 𝒜_{d+1}`, there is an isotropic origin datum `(a', k')` in dimension `d + 1` with exponent
`ζ ↦ F(|ζ|)` (`prop:isotropic-polar-classification`(2)), and the conclusions hold for it. -/
theorem profile_one_dimension_down_of_classA (hd : 1 ≤ d) {F : ℝ → ℝ} (h : classA (d + 1) F) :
    ∃ D' : OriginDatum (d + 1), (∀ ζ : Rd (d + 1), F ‖ζ‖ = D'.exponent ζ) ∧ classA d F ∧
      ∀ D : OriginDatum d, (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) →
        D.a = D'.a ∧ (∀ r : ℝ, 0 < r → D.k r = shadowProfile d D'.k r) ∧
          ContinuousOn D.k (Ioi 0) := by
  have hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := by
    obtain ⟨⟨P, hP⟩, -⟩ := h
    intro r hr
    rw [hP r hr]
    exact ENNReal.toReal_nonneg
  obtain ⟨D', hD'⟩ := (classA_iff_originDatum (d := d + 1) (by omega) F hF).1 h
  exact ⟨D', hD', profile_one_dimension_down hd D' hD'⟩

/-- The nesting `𝒜_{d+1} ⊆ 𝒜_d` on data, from clause (1). (`classA_of_succ` proves it by the
image of the law.) -/
theorem classA_of_classA_succ (hd : 1 ≤ d) {F : ℝ → ℝ} (h : classA (d + 1) F) : classA d F := by
  obtain ⟨D', -, h', -⟩ := profile_one_dimension_down_of_classA hd h
  exact h'

/-- **`prop:profile-one-dimension-down`(1), the last sentence**: if an isotropic origin datum in
dimension `d` with exponent `ξ ↦ F(|ξ|)` has a polar profile with a discontinuity in `(0,∞)`,
then `F ∉ 𝒜_{d+1}`. (That `F ∈ 𝒜_d` follows from the datum.) -/
theorem not_classA_succ_of_profile_discontinuous (hd : 1 ≤ d) {F : ℝ → ℝ} (D : OriginDatum d)
    (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (hdisc : ¬ ContinuousOn D.k (Ioi 0)) :
    ¬ classA (d + 1) F := by
  intro h
  obtain ⟨D', -, -, hall⟩ := profile_one_dimension_down_of_classA hd h
  exact hdisc (hall D hD).2.2

/-! ## Clause (2): the step datum -/

/-- **The step datum in dimension `d`** (`prop:profile-one-dimension-down`(2)):
`(0, b 1_{(0,τ)})`. The conditions of `def:isotropic-origin-datum` do not read the dimension, and
`cinDatum` is this datum at `d = 1`. -/
noncomputable def stepOriginDatum (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) : OriginDatum d where
  a := 0
  k := fun r => b * ScaleSpace.cinProfile τ r
  a_nonneg := le_rfl
  k_nonneg := (cinDatum hτ hb).k_nonneg
  k_antitone := (cinDatum hτ hb).k_antitone
  integrable_near_zero := (cinDatum hτ hb).integrable_near_zero
  integrable_at_top := (cinDatum hτ hb).integrable_at_top

theorem stepOriginDatum_a (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (stepOriginDatum d hτ hb).a = 0 := rfl

/-- The profile of the step datum is `b 1_{(0,τ)}`. -/
theorem stepOriginDatum_k (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) (r : ℝ) :
    (stepOriginDatum d hτ hb).k r = (Ioo (0 : ℝ) τ).indicator (fun _ => b) r := by
  by_cases hr : r ∈ Ioo (0 : ℝ) τ
  · simp [stepOriginDatum, ScaleSpace.cinProfile, hr]
  · simp [stepOriginDatum, ScaleSpace.cinProfile, hr]

theorem stepOriginDatum_one {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    stepOriginDatum 1 hτ hb = cinDatum hτ hb := rfl

/-- The profile of the step datum has a discontinuity at `τ`: it is `b` on the left and `0` at
`τ`. -/
theorem stepOriginDatum_not_continuousOn (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ¬ ContinuousOn (stepOriginDatum d hτ hb).k (Ioi 0) := by
  intro hc
  have hcτ : ContinuousAt (stepOriginDatum d hτ hb).k τ := hc.continuousAt (Ioi_mem_nhds hτ)
  have h0 : (stepOriginDatum d hτ hb).k τ = 0 := by
    rw [stepOriginDatum_k, indicator_of_notMem (fun h : τ ∈ Ioo (0 : ℝ) τ => lt_irrefl τ h.2)]
  have hlt : (stepOriginDatum d hτ hb).k τ < b := by rw [h0]; exact hb
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcτ.eventually_lt_const hlt)
  set u := max (τ - ε / 2) (τ / 2) with hu
  have hu1 : u < τ := max_lt (by linarith) (by linarith)
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hu2 : τ - ε / 2 ≤ u := le_max_left _ _
  have h1 := hball (show dist u τ < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [stepOriginDatum_k, indicator_of_mem (show u ∈ Ioo (0 : ℝ) τ from ⟨hu0, hu1⟩)] at h1
  exact lt_irrefl b h1

/-- **`prop:profile-one-dimension-down`(2)**: for `b, τ > 0` the pair `(0, b 1_{(0,τ)})` is an
isotropic origin datum in dimension `d` (`stepOriginDatum`); its exponent is radial, `ξ ↦ G(|ξ|)`
for a function `G`; every such `G` is in `𝒜_d` and not in `𝒜_{d+1}`; and
`𝒜_{d+1} ⊊ 𝒜_d`. -/
theorem step_datum_separates (hd : 1 ≤ d) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (∃ G : ℝ → ℝ, ∀ ξ : Rd d, G ‖ξ‖ = (stepOriginDatum d hτ hb).exponent ξ) ∧
      (∀ G : ℝ → ℝ, (∀ ξ : Rd d, G ‖ξ‖ = (stepOriginDatum d hτ hb).exponent ξ) →
        classA d G ∧ ¬ classA (d + 1) G) ∧
      {F : ℝ → ℝ | classA (d + 1) F} ⊂ {F | classA d F} := by
  have hex := exists_radial_exponent hd (stepOriginDatum d hτ hb)
  have hall : ∀ G : ℝ → ℝ, (∀ ξ : Rd d, G ‖ξ‖ = (stepOriginDatum d hτ hb).exponent ξ) →
      classA d G ∧ ¬ classA (d + 1) G := fun G hG =>
    ⟨(classA_iff_originDatum hd G (nonneg_of_radial_exponent hd _ hG)).2 ⟨_, hG⟩,
      not_classA_succ_of_profile_discontinuous hd _ hG
        (stepOriginDatum_not_continuousOn d hτ hb)⟩
  refine ⟨hex, hall, fun F hF => classA_of_classA_succ hd hF, fun hsub => ?_⟩
  obtain ⟨G, hG⟩ := hex
  exact (hall G hG).2 (hsub (hall G hG).1)

/-! ## Clause (3): the `Cin` rays -/

/-- The nesting over several steps, from clause (1): `𝒜_D ⊆ 𝒜_2` for `D ≥ 2`. -/
theorem classA_two_of_classA {F : ℝ → ℝ} {D : ℕ} (hD : 2 ≤ D) (h : classA D F) : classA 2 F := by
  induction D, hD using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact ih (classA_of_classA_succ (by omega) h)

/-- **`prop:profile-one-dimension-down`(3)**: at `d = 1` the exponent of the step datum is
`ω ↦ b Cin(τ|ω|)`, so `G(r) = b Cin(τ r)`; and no `Cin` ray belongs to `𝒜_D` for `D ≥ 2`. -/
theorem cin_ray_not_classA {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (∀ ω : Rd 1, (stepOriginDatum 1 hτ hb).exponent ω = b * ScaleSpace.cin (τ * ‖ω‖)) ∧
      ∀ D : ℕ, 2 ≤ D → ¬ classA D (fun ω => b * ScaleSpace.cin (τ * |ω|)) := by
  have hexp : ∀ ω : Rd 1, (stepOriginDatum 1 hτ hb).exponent ω = b * ScaleSpace.cin (τ * ‖ω‖) :=
    fun ω => by rw [stepOriginDatum_one]; exact cinDatum_exponent hτ hb ω
  refine ⟨hexp, fun D hD h => ?_⟩
  have h2 := classA_two_of_classA hD h
  refine ((step_datum_separates (d := 1) le_rfl hτ hb).2.1 _ fun ξ => ?_).2 h2
  rw [hexp ξ, abs_norm]

end AffineHemigroup
