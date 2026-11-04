/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ScaleZeroKernels
import AffineHemigroup.FiltrationTop
import AffineHemigroup.ExponentLog

/-!
# `lem:isotropic-stage-levy-measure`: the Lévy measure of a stage

Blueprint: `blueprint/src/parts/03-isotropic.tex`. Q-0447 (the statements were typed in Q-0434).

For an isotropic origin datum `(a, k_d)` and two numbers `0 < ℓ < L` the function
`κ(r) = k_d(r/L) - k_d(r/ℓ)` is nonnegative, and the measure `ν` on `ℝ^d` with the density
`κ(|x|)/(|S^{d-1}||x|^d)` off the origin is rotation invariant, integrates `|x|² ∧ 1`, has

  `F_d(Lξ) - F_d(ℓξ) = ½a(L² - ℓ²)|ξ|² + ∫ (1 - cos⟨ξ,x⟩) ν(dx)`,

and the total mass `c log(L/ℓ)` in `[0,∞]`, `c = k_d(0+)`. For a family of probability measures
with the display of a gauge `χ` and the exponent of the datum, `ℓ = χ(s)` and `L = χ(t)` give the
transform of the stage `μ_{s,t}`.

## The route

* **The image of `ν_d` under a dilation** (`OriginDatum.map_smul_levyMeasure`): for `β > 0` the
  image of `ν_d` under `x ↦ βx` has the density `k_d(|x|/β)/(|S^{d-1}||x|^d)`, an identity of
  measures (the library had the inequality `OriginDatum.map_smul_levyMeasure_le`). This image is
  the blueprint's `ν^{(β)}`; the Lean does not make `(aβ², k_d(·/β))` a datum, it reads the
  exponent of the image from `OriginDatum.exponent_smul_eq_lkForm`.
* **The sum** (`OriginDatum.stageMeasure_add`): `ν + ν^{(ℓ)} = ν^{(L)}`, the densities adding
  pointwise. Clauses (1) and (2) are read from it.
* **The mass** (`OriginDatum.stageMeasure_univ`): polar coordinates give
  `ν(ℝ^d) = ∫_0^∞ κ(r) dr/r`, and the substitution `r = ℓu` makes it
  `∫_0^∞ (k_d(u/b) - k_d(u)) du/u` with `b = L/ℓ`. For `c < ∞` this is `OriginDatum.lintegral_hb`,
  the identity behind `lem:isotropic-exponent-log`(2). For `c = ∞` the same identity is applied to
  the capped profiles `min(k_d, M)` (`OriginDatum.cap`), whose integrand is below that of `k_d`,
  and `M → ∞`.

## Trust

Every declaration of this file prints Lean's three logical axioms and nothing else.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- The image of a measure with a density against Lebesgue measure on `ℝ^d` under a linear
isometry that preserves the density is the measure itself. No measurability of the density is
asked. -/
theorem map_withDensity_of_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (f : Rd d → ℝ≥0∞)
    (hfQ : ∀ x, f (Q x) = f x) :
    ((volume : Measure (Rd d)).withDensity f).map Q = (volume : Measure (Rd d)).withDensity f := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply Q.continuous.measurable hB,
    withDensity_apply _ (Q.continuous.measurable hB), withDensity_apply _ hB,
    ← lintegral_indicator (Q.continuous.measurable hB), ← lintegral_indicator hB]
  have h := (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding
    (B.indicator f)
  rw [← h]
  refine lintegral_congr fun x => ?_
  by_cases hx : Q x ∈ B
  · rw [indicator_of_mem (show x ∈ Q ⁻¹' B from hx), indicator_of_mem hx]
    exact (hfQ x).symm
  · rw [indicator_of_notMem (show x ∉ Q ⁻¹' B from hx), indicator_of_notMem hx]

namespace OriginDatum

/-! ## The image of the Lévy measure of a datum under a dilation -/

/-- The density `k_d(|x|/β)/(|S^{d-1}||x|^d)` off the origin: that of the image of `ν_d` under
`x ↦ βx`, the blueprint's `ν^{(β)}`. -/
noncomputable def dilDensity (D : OriginDatum d) (β : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ({0}ᶜ : Set (Rd d)).indicator
    (fun x => ENNReal.ofReal (D.k (‖x‖ / β) / (sphereArea d * ‖x‖ ^ d))) x

/-- `β^{-d} ρ(x/β)`, with `ρ` the density of `ν_d`, is the density `dilDensity`. -/
theorem smul_levyDensity_eq (D : OriginDatum d) {β : ℝ} (hβ : 0 < β) (y : Rd d) :
    ENNReal.ofReal |(β ^ Module.finrank ℝ (Rd d))⁻¹| *
        ({0}ᶜ : Set (Rd d)).indicator
          (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) (β⁻¹ • y)
      = D.dilDensity β y := by
  have hβd : (0 : ℝ) < β ^ d := pow_pos hβ d
  rw [finrank_Rd, abs_of_pos (inv_pos.mpr hβd), dilDensity]
  by_cases hy : y = 0
  · subst hy
    simp
  · have hy' : β⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hβ.ne') hy
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [indicator_of_mem (show β⁻¹ • y ∈ ({0}ᶜ : Set (Rd d)) from hy'),
      indicator_of_mem (show y ∈ ({0}ᶜ : Set (Rd d)) from hy),
      ← ENNReal.ofReal_mul (by positivity),
      norm_smul, Real.norm_of_nonneg (inv_pos.mpr hβ).le]
    have hk : β⁻¹ * ‖y‖ = ‖y‖ / β := inv_mul_eq_div _ _
    rw [hk, div_pow]
    congr 1
    field_simp

theorem measurable_dilDensity (D : OriginDatum d) {β : ℝ} (hβ : 0 < β) :
    Measurable (D.dilDensity β) := by
  have h : D.dilDensity β = fun y => ENNReal.ofReal |(β ^ Module.finrank ℝ (Rd d))⁻¹| *
      ({0}ᶜ : Set (Rd d)).indicator
        (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) (β⁻¹ • y) :=
    funext fun y => (D.smul_levyDensity_eq hβ y).symm
  rw [h]
  exact (D.measurable_levyDensity.comp (measurable_const_smul β⁻¹)).const_mul _

/-- **The image of `ν_d` under the dilation `x ↦ βx`**, `β > 0`, has the density
`k_d(|x|/β)/(|S^{d-1}||x|^d)` off the origin. -/
theorem map_smul_levyMeasure (D : OriginDatum d) {β : ℝ} (hβ : 0 < β) :
    Measure.map (fun x : Rd d => β • x) D.levyMeasure = volume.withDensity (D.dilDensity β) := by
  set ρ : Rd d → ℝ≥0∞ := fun x => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x with hρ
  have hρm : Measurable ρ := D.measurable_levyDensity
  have hsm : Measurable fun x : Rd d => β • x := measurable_const_smul β
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hsm hs, OriginDatum.levyMeasure, withDensity_apply _ (hsm hs),
    withDensity_apply _ hs]
  calc ∫⁻ x in (fun x : Rd d => β • x) ⁻¹' s, ρ x
      = ∫⁻ x, s.indicator (fun y => ρ (β⁻¹ • y)) (β • x) := by
        rw [← lintegral_indicator (hsm hs)]
        refine lintegral_congr fun x => ?_
        by_cases hx : β • x ∈ s
        · rw [indicator_of_mem (show x ∈ (fun x : Rd d => β • x) ⁻¹' s from hx),
            indicator_of_mem hx, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
        · rw [indicator_of_notMem (show x ∉ (fun x : Rd d => β • x) ⁻¹' s from hx),
            indicator_of_notMem hx]
    _ = ∫⁻ y, s.indicator (fun y => ρ (β⁻¹ • y)) y
          ∂(Measure.map (fun x : Rd d => β • x) volume) := by
        exact (lintegral_map (f := s.indicator fun y => ρ (β⁻¹ • y))
          ((hρm.comp (measurable_const_smul _)).indicator hs) hsm).symm
    _ = ∫⁻ y in s, ENNReal.ofReal |(β ^ Module.finrank ℝ (Rd d))⁻¹| * ρ (β⁻¹ • y) := by
        rw [Measure.map_addHaar_smul _ hβ.ne', lintegral_smul_measure,
          lintegral_indicator hs, smul_eq_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ y in s, D.dilDensity β y := lintegral_congr fun y => D.smul_levyDensity_eq hβ y

/-! ## The profile and the measure of the dilation difference -/

/-- The profile `κ(r) = k_d(r/L) - k_d(r/ℓ)` of the dilation difference. A total function, read
at `r > 0` and for `0 < ℓ < L`. -/
noncomputable def stageProfile (D : OriginDatum d) (ℓ L r : ℝ) : ℝ := D.k (r / L) - D.k (r / ℓ)

/-- The measure `ν` with the density `κ(|x|)/(|S^{d-1}||x|^d)` off the origin, written as
`OriginDatum.levyMeasure` is. -/
noncomputable def stageMeasure (D : OriginDatum d) (ℓ L : ℝ) : Measure (Rd d) :=
  volume.withDensity fun x =>
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.stageProfile ℓ L ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x

/-- **`lem:isotropic-stage-levy-measure`(1)**, `κ ≥ 0`. -/
theorem stageProfile_nonneg (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : ℓ ≤ L) {r : ℝ}
    (hr : 0 < r) : 0 ≤ D.stageProfile ℓ L r :=
  sub_nonneg.mpr (D.k_antitone (div_pos hr (hℓ.trans_le hL)) (div_pos hr hℓ)
    (div_le_div_of_nonneg_left hr.le hℓ hL))

/-- **`lem:isotropic-stage-levy-measure`(1)**: `ν` gives the origin no mass. -/
theorem stageMeasure_zero (D : OriginDatum d) (ℓ L : ℝ) : D.stageMeasure ℓ L {0} = 0 := by
  rw [stageMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  refine setLIntegral_eq_zero (measurableSet_singleton 0) fun x hx => ?_
  rw [mem_singleton_iff] at hx
  subst hx
  simp

/-- **`lem:isotropic-stage-levy-measure`(1)**: `ν` has a density. -/
theorem stageMeasure_absolutelyContinuous (D : OriginDatum d) (ℓ L : ℝ) :
    D.stageMeasure ℓ L ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- `ν` is invariant under every linear isometry of `ℝ^d`. -/
theorem stageMeasure_map_isometry (D : OriginDatum d) (ℓ L : ℝ) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (D.stageMeasure ℓ L).map Q = D.stageMeasure ℓ L := by
  refine map_withDensity_of_isometry Q _ fun x => ?_
  by_cases hx : x = 0
  · subst hx
    simp
  · have hQx : Q x ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
    rw [indicator_of_mem (show Q x ∈ ({0}ᶜ : Set (Rd d)) from hQx),
      indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), LinearIsometryEquiv.norm_map]

/-- **`lem:isotropic-stage-levy-measure`(1)**: `ν` is rotation invariant. -/
theorem stageMeasure_rotation (D : OriginDatum d) (ℓ L : ℝ) :
    ∀ Q ∈ orthSet d, push Q (D.stageMeasure ℓ L) = D.stageMeasure ℓ L := by
  intro Q hQ
  have hnorm : ∀ x : Rd d, ‖lin Q x‖ = ‖x‖ := fun x => by
    have h := norm_lin_transpose_of_orth (transpose_mem_orthSet hQ) x
    rwa [transpose_transpose] at h
  let e : Rd d ≃ₗᵢ[ℝ] Rd d := LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (lin Q : Rd d →L[ℝ] Rd d).toLinearMap, norm_map' := hnorm } rfl
  exact D.stageMeasure_map_isometry ℓ L e

/-- `ν` is symmetric. -/
theorem stageMeasure_neg (D : OriginDatum d) (ℓ L : ℝ) :
    (D.stageMeasure ℓ L).map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = D.stageMeasure ℓ L :=
  D.stageMeasure_map_isometry ℓ L _

/-- **`eq:stage-measure-sum`**: `ν + ν^{(ℓ)} = ν^{(L)}`, with `ν^{(β)}` the image of `ν_d` under
`x ↦ βx`. -/
theorem stageMeasure_add (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : ℓ ≤ L) :
    D.stageMeasure ℓ L + Measure.map (fun x : Rd d => ℓ • x) D.levyMeasure
      = Measure.map (fun x : Rd d => L • x) D.levyMeasure := by
  have hA := (sphereArea_eq_toSphere hd).2
  rw [D.map_smul_levyMeasure hℓ, D.map_smul_levyMeasure (hℓ.trans_le hL), stageMeasure,
    ← withDensity_add_right _ (D.measurable_dilDensity hℓ)]
  congr 1
  funext x
  rw [Pi.add_apply, dilDensity, dilDensity]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hden : 0 ≤ sphereArea d * ‖x‖ ^ d := by positivity
    rw [indicator_of_mem hx', indicator_of_mem hx', indicator_of_mem hx',
      ← ENNReal.ofReal_add (div_nonneg (D.stageProfile_nonneg hℓ hL hn) hden)
        (div_nonneg (D.k_nonneg _ (div_pos hn hℓ)) hden), stageProfile]
    congr 1
    ring

/-- **`lem:isotropic-stage-levy-measure`(1)**: `∫ (|x|² ∧ 1) dν < ∞`, in the form of the field of
`LevyTriplet`. -/
theorem stageMeasure_integrable (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ < L) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(D.stageMeasure ℓ L) ≠ ⊤ := by
  have hle : D.stageMeasure ℓ L ≤ Measure.map (fun x : Rd d => L • x) D.levyMeasure := by
    rw [← D.stageMeasure_add hd hℓ hL.le]
    exact Measure.le_add_right le_rfl
  have hpt : ∀ x : Rd d, min (‖L • x‖ ^ 2) 1 ≤ max (L ^ 2) 1 * min (‖x‖ ^ 2) 1 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hx : 0 ≤ ‖x‖ ^ 2 := by positivity
    rcases le_total (‖x‖ ^ 2) 1 with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)
    · rw [min_eq_right h, mul_one]
      exact (min_le_right _ _).trans (le_max_right _ _)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono' hle le_rfl)
  rw [lintegral_map (by fun_prop) (measurable_const_smul L)]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := max (L ^ 2) 1))
    (D.lintegral_min_levyMeasure_ne_top hd)) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right _ _))]
  exact ENNReal.ofReal_le_ofReal (hpt x)

/-- **`lem:isotropic-stage-levy-measure`(2)**:
`F_d(Lξ) - F_d(ℓξ) = ½a(L² - ℓ²)|ξ|² + ∫ (1 - cos⟨ξ,x⟩) ν(dx)`, with the integrand integrable. -/
theorem exponent_smul_sub_smul (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ < L) (ξ : Rd d) :
    Integrable (fun x : Rd d => 1 - Real.cos ⟪ξ, x⟫) (D.stageMeasure ℓ L) ∧
      D.exponent (L • ξ) - D.exponent (ℓ • ξ) =
        D.a / 2 * (L ^ 2 - ℓ ^ 2) * ‖ξ‖ ^ 2
          + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂(D.stageMeasure ℓ L) := by
  have hfin : ∀ β : ℝ, levyExpL (Measure.map (fun x : Rd d => β • x) D.levyMeasure) ξ ≠ ⊤ :=
    fun β => by rw [levyExpL_map_smul]; exact D.levyExpL_ne_top hd _
  have hsum : levyExpL (D.stageMeasure ℓ L) ξ
      + levyExpL (Measure.map (fun x : Rd d => ℓ • x) D.levyMeasure) ξ
      = levyExpL (Measure.map (fun x : Rd d => L • x) D.levyMeasure) ξ := by
    unfold levyExpL
    rw [← lintegral_add_measure, D.stageMeasure_add hd hℓ hL.le]
  have hstage : levyExpL (D.stageMeasure ℓ L) ξ ≠ ⊤ := fun h => by
    rw [h, top_add] at hsum
    exact hfin L hsum.symm
  refine ⟨integrable_one_sub_cos_of_levyExpL hstage, ?_⟩
  rw [D.exponent_smul_eq_lkForm hd L ξ, D.exponent_smul_eq_lkForm hd ℓ ξ, lkForm, lkForm, ← hsum,
    ENNReal.toReal_add hstage (hfin ℓ), levyExpL_toReal_eq]
  ring

/-! ## The total mass -/

/-- The total mass through polar coordinates: `ν(ℝ^d) = ∫_0^∞ κ(r) dr/r`. -/
theorem stageMeasure_univ_eq_lintegral (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ ≤ L) :
    D.stageMeasure ℓ L univ
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D.stageProfile ℓ L r / r) := by
  have hA := sphereArea_eq_toSphere hd
  have hAinv : (ENNReal.ofReal (sphereArea d))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (by simp [hA.2])
  set f : Rd d → ℝ≥0∞ := fun x => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.stageProfile ℓ L ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x with hf
  -- the density is the difference of two measurable densities
  have hfm : Measurable f := by
    have h : f = fun x => D.dilDensity L x - D.dilDensity ℓ x := by
      funext x
      rw [hf, dilDensity, dilDensity]
      by_cases hx : x = 0
      · subst hx
        simp
      · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
        have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hden : 0 ≤ sphereArea d * ‖x‖ ^ d := by have := hA.2; positivity
        simp only
        rw [indicator_of_mem hx', indicator_of_mem hx', indicator_of_mem hx',
          ← ENNReal.ofReal_sub _ (div_nonneg (D.k_nonneg _ (div_pos hn hℓ)) hden), stageProfile,
          sub_div]
    rw [h]
    exact (D.measurable_dilDensity (hℓ.trans_le hL)).sub (D.measurable_dilDensity hℓ)
  rw [stageMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_polar hd f hfm]
  have hinner : ∀ η : Metric.sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))
      = (ENNReal.ofReal (sphereArea d))⁻¹ *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D.stageProfile ℓ L r / r) := by
    intro η
    rw [← lintegral_const_mul' _ _ hAinv]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
    have hnorm : ‖r • (η : Rd d)‖ = r := by
      rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr.le]
    have hne : r • (η : Rd d) ≠ 0 := by
      rw [← norm_ne_zero_iff, hnorm]; exact hr.ne'
    have hκ := D.stageProfile_nonneg hℓ hL hr
    have hrd : r ^ d = r * r ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hrd1 : 0 < r ^ (d - 1) := pow_pos hr _
    have hApos := hA.2
    simp only [hf]
    rw [indicator_of_mem (show r • (η : Rd d) ∈ ({0}ᶜ : Set (Rd d)) from hne), hnorm,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos hApos,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hrd]
    field_simp
  simp_rw [hinner]
  rw [lintegral_const, ← hA.1, mul_right_comm, ENNReal.inv_mul_cancel (by simp [hA.2])
    ENNReal.ofReal_ne_top, one_mul]

/-- The substitution `r = ℓu`: `∫_0^∞ κ(r) dr/r = ∫_0^∞ (k_d(u/b) - k_d(u)) du/u`, `b = L/ℓ`. -/
theorem lintegral_stageProfile (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : ℓ ≤ L) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D.stageProfile ℓ L r / r)
      = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((D.k (u / (L / ℓ)) - D.k u) / u) := by
  have himg : (fun u : ℝ => ℓ * u) '' Ioi 0 = Ioi 0 := by
    ext r; constructor
    · rintro ⟨u, hu, rfl⟩; exact mul_pos hℓ hu
    · intro hr; exact ⟨r / ℓ, div_pos hr hℓ, by field_simp⟩
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => ℓ * u) ℓ (Ioi 0) u :=
    fun u _ => ((hasDerivAt_id u).const_mul ℓ).hasDerivWithinAt.congr_deriv (by simp)
  have hinj : InjOn (fun u : ℝ => ℓ * u) (Ioi 0) := fun u _ v _ h =>
    mul_left_cancel₀ hℓ.ne' h
  conv_lhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  have hκ := D.stageProfile_nonneg hℓ hL (mul_pos hℓ hu)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos hℓ, stageProfile]
  congr 1
  have h1 : ℓ * u / L = u / (L / ℓ) := by field_simp
  have h2 : ℓ * u / ℓ = u := by field_simp
  rw [h1, h2]
  field_simp

/-- **The capped datum** `(a, min(k_d, M))`, `M ≥ 0`. -/
noncomputable def cap (D : OriginDatum d) (M : ℝ) (hM : 0 ≤ M) : OriginDatum d where
  a := D.a
  k := fun r => min (D.k r) M
  a_nonneg := D.a_nonneg
  k_nonneg := fun r hr => le_min (D.k_nonneg r hr) hM
  k_antitone := fun r hr s hs hrs => min_le_min (D.k_antitone hr hs hrs) le_rfl
  integrable_near_zero := by
    refine ne_top_of_le_ne_top D.integrable_near_zero (setLIntegral_mono' measurableSet_Ioo
      fun r hr => ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hr.1.le
  integrable_at_top := by
    refine ne_top_of_le_ne_top D.integrable_at_top (setLIntegral_mono' measurableSet_Ioi
      fun r (hr : 1 < r) => ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by linarith)

/-- The capped datum has the profile `M` at the origin when `c = ∞`. -/
theorem profileAtOrigin_cap (D : OriginDatum d) (hc : D.profileAtOrigin = ⊤) {M : ℝ}
    (hM : 0 ≤ M) : (D.cap M hM).profileAtOrigin = ENNReal.ofReal M := by
  refine le_antisymm (iSup_le fun r => ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
  obtain ⟨rβ, hrβ, hk⟩ := D.exists_le_k (β := M) (by rw [hc]; exact ENNReal.ofReal_lt_top)
  have hr : (0 : ℝ) < rβ / 2 := by have := hrβ.1; positivity
  have h := (D.cap M hM).ofReal_k_le hr
  have hval : (D.cap M hM).k (rβ / 2) = M :=
    min_eq_right (hk (rβ / 2) ⟨hr, by have := hrβ.1; linarith⟩)
  rwa [hval] at h

/-- The Frullani integral of a profile that is infinite at the origin is infinite. -/
theorem lintegral_hb_top (D : OriginDatum d) (hc : D.profileAtOrigin = ⊤) {b : ℝ} (hb : 1 < b) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((D.k (u / b) - D.k u) / u) = ⊤ := by
  have hb0 : 0 < b := lt_trans one_pos hb
  have hlog : 0 < Real.log b := Real.log_pos hb
  refine ENNReal.eq_top_of_forall_nnreal_le fun q => ?_
  have hM : (0 : ℝ) ≤ q / Real.log b := div_nonneg q.2 hlog.le
  have hcap := D.profileAtOrigin_cap hc hM
  have h := (D.cap _ hM).lintegral_hb (by rw [hcap]; exact ENNReal.ofReal_ne_top) hb.le
  rw [hcap, ENNReal.toReal_ofReal hM, div_mul_cancel₀ _ hlog.ne', ENNReal.ofReal_coe_nnreal] at h
  rw [← h]
  refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 0 < u) => ENNReal.ofReal_le_ofReal ?_
  refine div_le_div_of_nonneg_right ?_ hu.le
  have hle : D.k u ≤ D.k (u / b) := D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb.le)
  change min (D.k (u / b)) (q / Real.log b) - min (D.k u) (q / Real.log b) ≤ D.k (u / b) - D.k u
  rcases le_total (D.k (u / b)) (q / Real.log b) with h1 | h1
  · rw [min_eq_left h1, min_eq_left (hle.trans h1)]
  · rcases le_total (D.k u) (q / Real.log b) with h2 | h2
    · rw [min_eq_right h1, min_eq_left h2]; linarith
    · rw [min_eq_right h1, min_eq_right h2]; linarith

/-- **`lem:isotropic-stage-levy-measure`(3)**: the total mass of `ν` is `c log(L/ℓ)`, in
`[0,∞]`. -/
theorem stageMeasure_univ (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : ℓ < L) :
    D.stageMeasure ℓ L univ = D.profileAtOrigin * ENNReal.ofReal (Real.log (L / ℓ)) := by
  have hb : 1 < L / ℓ := (one_lt_div hℓ).mpr hL
  have hlog : 0 < Real.log (L / ℓ) := Real.log_pos hb
  rw [D.stageMeasure_univ_eq_lintegral hd hℓ hL.le, D.lintegral_stageProfile hℓ hL.le]
  by_cases hc : D.profileAtOrigin = ⊤
  · rw [D.lintegral_hb_top hc hb, hc, ENNReal.top_mul (by simpa using hlog)]
  · rw [D.lintegral_hb hc hb.le, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]

/-- **`lem:isotropic-stage-levy-measure`(3)**, "so": `ν` is a finite measure exactly when `c` is
finite. -/
theorem stageMeasure_univ_ne_top_iff (hd : 1 ≤ d) (D : OriginDatum d) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hL : ℓ < L) : D.stageMeasure ℓ L univ ≠ ⊤ ↔ D.profileAtOrigin ≠ ⊤ := by
  have hlog : 0 < Real.log (L / ℓ) := Real.log_pos ((one_lt_div hℓ).mpr hL)
  rw [D.stageMeasure_univ hd hℓ hL]
  constructor
  · intro h hc
    rw [hc, ENNReal.top_mul (by simpa using hlog)] at h
    exact h rfl
  · intro hc
    exact ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top

end OriginDatum

/-! ## The stage of a family -/

/-- **`lem:isotropic-stage-levy-measure`**, the last sentence: the transform of a stage of a
family with the display, through the Lévy measure of the stage. -/
theorem isotropic_stage_transform (hd : 1 ≤ d) (D : OriginDatum d) {F χ : ℝ → ℝ}
    (hχ : IsGauge χ) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) (μ : ℝ → ℝ → Measure (Rd d))
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ξ : Rd d) :
    charFun (μ s t) ξ = ((Real.exp (-(D.a / 2 * (χ t ^ 2 - χ s ^ 2) * ‖ξ‖ ^ 2
      + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂(D.stageMeasure (χ s) (χ t)))) : ℝ) : ℂ) := by
  have hℓ : 0 < χ s := hχ.pos hs
  have hL : χ s < χ t := hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst
  have key : ∀ u : ℝ, 0 ≤ χ u → F (χ u * ‖ξ‖) = D.exponent (χ u • ξ) := fun u hu => by
    rw [← hD, norm_smul, Real.norm_of_nonneg hu]
  rw [hrep s t hs.le hst.le ξ, key t (hℓ.le.trans hL.le), key s hℓ.le,
    (D.exponent_smul_sub_smul hd hℓ hL ξ).2]

/-- **`lem:isotropic-stage-levy-measure`**, the last sentence: the mass of the Lévy measure of
the stage is `c log(χ(t)/χ(s))`. -/
theorem isotropic_stage_mass (hd : 1 ≤ d) (D : OriginDatum d) {χ : ℝ → ℝ} (hχ : IsGauge χ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    D.stageMeasure (χ s) (χ t) univ
      = D.profileAtOrigin * ENNReal.ofReal (Real.log (χ t / χ s)) :=
  D.stageMeasure_univ hd (hχ.pos hs)
    (hχ.2.1 (mem_Ici.2 hs.le) (mem_Ici.2 (hs.le.trans hst.le)) hst)

end AffineHemigroup
