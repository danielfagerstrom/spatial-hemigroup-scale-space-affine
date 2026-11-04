/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableOrder
import AffineHemigroup.OrderedSpectrum
import AffineHemigroup.Orbits
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# `lem:elliptical-stable-density`(1): the exponent is the Lévy integral of the density

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:elliptical-stable-density` (wave 1, group D,
Q-0281), clause (1): `ψ_H(ω) = ∫_{ℝ^d∖{0}} (1 - cos⟨ω,x⟩) n_H(x) dx` and
`∫ (|x|² ∧ 1) n_H(x) dx < ∞`.

The route is the blueprint's: `J(ω) := ∫ (1 - cos⟨ω,y⟩)|y|^{-d-α} dy` is invariant under the
orthogonal group (Mathlib's `LinearIsometryEquiv.measurePreserving`) and homogeneous of degree `α`
(the change of variables `y = z/s`, through `map_linearMap_addHaar_eq_smul_addHaar`), so
`J(ω) = c_{d,α}|ω|^α` (a reflection takes `e₁` to `ω/|ω|`); the substitution `x = H^{1/2}y` then
gives clause (1). Integrals are `ℝ≥0∞`-valued, as the statement's are. Lean core only.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real
open scoped MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ### Linear changes of variables -/

/-- The determinant of the linear map of a matrix is the matrix's determinant. -/
theorem det_lin (B : Mat d) :
    LinearMap.det ((lin B : Rd d →L[ℝ] Rd d) : Rd d →ₗ[ℝ] Rd d) = B.det := by
  change LinearMap.det (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis B) = _
  exact LinearMap.det_toLin _ _

/-- **The linear change of variables** `∫ G(By) dy = |det B|⁻¹ ∫ G`. -/
theorem lintegral_comp_lin {B : Mat d} (hB : B.det ≠ 0) {G : Rd d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (lin B y) = ENNReal.ofReal |B.det|⁻¹ * ∫⁻ y, G y := by
  have hdet : LinearMap.det ((lin B : Rd d →L[ℝ] Rd d) : Rd d →ₗ[ℝ] Rd d) ≠ 0 := by
    rw [det_lin]; exact hB
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Rd d)) hdet
  rw [det_lin, abs_inv] at hmap
  rw [← lintegral_map hG (lin B).continuous.measurable]
  change ∫⁻ y, G y ∂(Measure.map (((lin B : Rd d →L[ℝ] Rd d) : Rd d →ₗ[ℝ] Rd d)) volume) = _
  rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-! ### The integral `J(ω) = ∫ (1 - cos⟨ω,y⟩)|y|^{-d-α} dy` -/

/-- The integrand of `J`. -/
noncomputable def stableJIntegrand (d : ℕ) (α : ℝ) (ω y : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - Real.cos ⟪ω, y⟫) * ‖y‖ ^ (-(d : ℝ) - α))

theorem measurable_stableJIntegrand (α : ℝ) (ω : Rd d) :
    Measurable (stableJIntegrand d α ω) := by
  unfold stableJIntegrand
  fun_prop

/-- `J(Qω) = J(ω)` for a linear isometry `Q`. -/
theorem stableJ_isometry (α : ℝ) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (ω : Rd d) :
    ∫⁻ y, stableJIntegrand d α (Q ω) y = ∫⁻ y, stableJIntegrand d α ω y := by
  rw [← (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding]
  congr 1
  funext z
  simp only [stableJIntegrand, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]

/-- `J(sω) = s^α J(ω)` for `s > 0`. -/
theorem stableJ_smul [NeZero d] {α : ℝ} {s : ℝ} (hs : 0 < s) (ω : Rd d) :
    ∫⁻ y, stableJIntegrand d α (s • ω) y =
      ENNReal.ofReal (s ^ α) * ∫⁻ y, stableJIntegrand d α ω y := by
  have hB : (s⁻¹ • (1 : Mat d)).det ≠ 0 := by
    rw [det_smul_one]; exact pow_ne_zero _ (inv_ne_zero hs.ne')
  have h := lintegral_comp_lin hB (measurable_stableJIntegrand α (s • ω))
  rw [det_smul_one, abs_of_pos (by positivity), inv_pow, inv_inv] at h
  have hpt : ∀ z : Rd d, stableJIntegrand d α (s • ω) (lin (s⁻¹ • (1 : Mat d)) z) =
      ENNReal.ofReal (s ^ ((d : ℝ) + α)) * stableJIntegrand d α ω z := by
    intro z
    have hz : lin (s⁻¹ • (1 : Mat d)) z = s⁻¹ • z := by
      rw [lin_smul, lin_one]; rfl
    rw [hz, stableJIntegrand, stableJIntegrand, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inner_smul_left, inner_smul_right, norm_smul, Real.norm_of_nonneg (by positivity),
      mul_rpow (by positivity) (norm_nonneg _)]
    simp only [RCLike.conj_to_real]
    rw [show s * (s⁻¹ * ⟪ω, z⟫) = ⟪ω, z⟫ by field_simp, inv_rpow hs.le, ← rpow_neg hs.le]
    ring_nf
  simp_rw [hpt] at h
  rw [lintegral_const_mul _ (measurable_stableJIntegrand α ω)] at h
  -- `s^{d+α} J(ω) = s^d J(sω)`
  have hsd : ENNReal.ofReal (s ^ d) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsd' : ENNReal.ofReal (s ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (s ^ ((d : ℝ) + α)) =
      ENNReal.ofReal (s ^ d) * ENNReal.ofReal (s ^ α) := by
    rw [← ENNReal.ofReal_mul (by positivity), rpow_add hs, rpow_natCast]
  rw [hsplit, mul_assoc] at h
  exact (ENNReal.mul_right_inj hsd hsd').1 h.symm

/-- `J(e₁) = c_{d,α}`. -/
theorem stableJ_single [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∫⁻ y, stableJIntegrand d α (EuclideanSpace.single 0 1) y =
      ENNReal.ofReal (stableConst (d := d) α) := by
  have hint := (stableConst_pos_finite (d := d) hα0 hα2).1
  rw [stableConst, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => stableConst_integrand_nonneg α y)]
  congr 1
  funext y
  simp [stableJIntegrand, EuclideanSpace.inner_single_left]

/-- **`J(ω) = c_{d,α}|ω|^α`**, by rotation invariance and homogeneity. -/
theorem stableJ_eq [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (ω : Rd d) :
    ∫⁻ y, stableJIntegrand d α ω y = ENNReal.ofReal (stableConst (d := d) α * ‖ω‖ ^ α) := by
  have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
  rcases eq_or_ne ω 0 with rfl | hω
  · simp [stableJIntegrand, zero_rpow hα0.ne']
  have hn : 0 < ‖ω‖ := norm_pos_iff.2 hω
  set e : Rd d := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  set u : Rd d := ‖ω‖⁻¹ • ω with hu
  have hun : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  set R := Submodule.reflection (ℝ ∙ (e - u))ᗮ
  have hR : R e = u := Submodule.reflection_sub (by rw [he, hun])
  have hωu : ω = ‖ω‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hωu, stableJ_smul hn, ← hR, stableJ_isometry, stableJ_single hα0 hα2,
    ← ENNReal.ofReal_mul (by positivity), mul_comm]
  congr 1
  rw [norm_smul, norm_norm, hR, hun, mul_one]

/-! ### Clause (1) -/

/-- `(|y|² ∧ 1)|y|^{-d-α}` is at most twice the radial bound of `stableConst_pos_finite`. -/
theorem min_sq_mul_rpow_le_stableConstBound (α : ℝ) (y : Rd d) :
    min (‖y‖ ^ 2) 1 * ‖y‖ ^ (-(d : ℝ) - α) ≤ 2 * stableConstBound d α ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [stableConstBound]
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hp : 0 < ‖y‖ ^ (-(d : ℝ) - α) := rpow_pos_of_pos hn _
  rcases le_or_gt ‖y‖ 1 with h1 | h1
  · simp only [stableConstBound, indicator_of_mem (show ‖y‖ ∈ Ioc 0 1 from ⟨hn, h1⟩),
      indicator_of_notMem (show ‖y‖ ∉ Ioi 1 from not_lt.2 h1), add_zero]
    have hsq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    rw [min_eq_left hsq, show (2 - (d : ℝ) - α) = (2 : ℕ) + (-(d : ℝ) - α) by push_cast; ring,
      rpow_add hn, rpow_natCast]
    linarith
  · simp only [stableConstBound, indicator_of_mem (show ‖y‖ ∈ Ioi 1 from h1),
      indicator_of_notMem (show ‖y‖ ∉ Ioc 0 1 from fun h => not_le.2 h1 h.2), zero_add]
    have hsq : 1 ≤ ‖y‖ ^ 2 := by nlinarith
    rw [min_eq_right hsq]
    linarith

/-- `(|y|²)^{-(d+α)/2} = |y|^{-d-α}`. -/
theorem norm_sq_rpow_neg (α : ℝ) (y : Rd d) :
    (‖y‖ ^ 2) ^ (-((d : ℝ) + α) / 2) = ‖y‖ ^ (-(d : ℝ) - α) := by
  rw [← rpow_natCast, ← rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- `|det H^{1/2}| = (det H)^{1/2}` on `PD(d)`. -/
theorem abs_det_msqrt {H : Mat d} (hH : H.PosDef) :
    |(msqrt H).det| = H.det ^ ((1 : ℝ) / 2) := by
  have h2 : (msqrt H).det * (msqrt H).det = H.det := by
    rw [← det_mul, msqrt_mul_self hH.posSemidef]
  rw [← Real.sqrt_eq_rpow, ← h2, Real.sqrt_mul_self_eq_abs]

/-- The density of `x = H^{1/2}y`: `n_H(H^{1/2}y) = c⁻¹(det H)^{-1/2}|y|^{-d-α}`. -/
theorem stableDensity_lin_msqrt {α : ℝ} [NeZero d] {H : Mat d} (hH : H.PosDef) (y : Rd d) :
    stableDensity α H (lin (msqrt H) y) =
      (stableConst (d := d) α)⁻¹ * H.det ^ (-(1 : ℝ) / 2) * ‖y‖ ^ (-(d : ℝ) - α) := by
  unfold stableDensity
  rw [quad_inv_lin_msqrt hH, norm_sq_rpow_neg]

/-- **`lem:elliptical-stable-density`(1)**: `ψ_H(ω) = ∫_{ℝ^d∖{0}} (1 - cos⟨ω,x⟩) n_H(x) dx` and
`∫_{ℝ^d∖{0}} (|x|² ∧ 1) n_H(x) dx < ∞`, for every `H ∈ PD(d)` and `ω`. -/
theorem stableExp_eq_lintegral [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) :
    (∀ ω : Rd d, ENNReal.ofReal (stableExp α H ω) =
        ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * stableDensity α H x)) ∧
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * stableDensity α H x) ≠ ⊤ := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
  set A := msqrt H with hA
  have hdA : A.det ≠ 0 := (msqrt_mem_glSet hH).ne_zero
  have hdH := hH.det_pos
  -- `∫ G = |det A| ∫ G(Ay) dy`
  have hcov : ∀ G : Rd d → ℝ≥0∞, Measurable G →
      ∫⁻ x, G x = ENNReal.ofReal (H.det ^ ((1 : ℝ) / 2)) * ∫⁻ y, G (lin A y) := by
    intro G hG
    rw [lintegral_comp_lin hdA hG, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      abs_det_msqrt hH, mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  have hK : H.det ^ ((1 : ℝ) / 2) * ((stableConst (d := d) α)⁻¹ * H.det ^ (-(1 : ℝ) / 2)) =
      (stableConst (d := d) α)⁻¹ := by
    rw [mul_left_comm, ← rpow_add hdH]; norm_num
  have hq : Continuous fun x : Rd d => quad H⁻¹ x := by unfold quad; fun_prop
  have hmeasD : Measurable (stableDensity α H) := by
    unfold stableDensity
    exact measurable_const.mul (hq.measurable.pow_const _)
  refine ⟨fun ω => ?_, ?_⟩
  · rw [restrict_compl_singleton, hcov _ (Measurable.ennreal_ofReal
      ((by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).measurable.mul hmeasD))]
    have hpt : ∀ y : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, lin A y⟫) *
        stableDensity α H (lin A y)) = ENNReal.ofReal ((stableConst (d := d) α)⁻¹ *
          H.det ^ (-(1 : ℝ) / 2)) * stableJIntegrand d α (lin A ω) y := by
      intro y
      rw [stableDensity_lin_msqrt hH, stableJIntegrand, ← ENNReal.ofReal_mul (by positivity),
        real_inner_comm, inner_lin_left, hA, msqrt_transpose, real_inner_comm]
      congr 1
      ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ (measurable_stableJIntegrand α _), stableJ_eq hα0 hα2, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      hK, inv_mul_cancel₀ hc.ne', one_mul]
    congr 1
    rw [stableExp, ← norm_sq_lin_msqrt hH.posSemidef, ← hA, ← rpow_natCast,
      ← rpow_mul (norm_nonneg _)]
    congr 2
    push_cast
    ring
  · rw [restrict_compl_singleton, hcov _ (Measurable.ennreal_ofReal
      ((by fun_prop : Continuous fun x : Rd d => min (‖x‖ ^ 2) 1).measurable.mul hmeasD))]
    set K0 := (stableConst (d := d) α)⁻¹ * H.det ^ (-(1 : ℝ) / 2) with hK0
    have hK0pos : 0 < K0 := by positivity
    set L := max (lamMax H) 1 with hLdef
    have hL1 : 1 ≤ L := le_max_right _ _
    have hlam : ∀ y : Rd d, quad H y ≤ lamMax H * ‖y‖ ^ 2 := fun y => by
      have h := quad_nonneg ((posSemidef_smul_one_sub_iff hH.isHermitian
        (eigUp H (Fin.rev 0))).2 le_rfl) y
      rw [quad_sub, quad_smul, quad_one] at h
      rw [lamMax_eq_eigUp_last hH.isHermitian]
      linarith
    have hbound : ∀ y : Rd d,
        ENNReal.ofReal (min (‖lin A y‖ ^ 2) 1 * stableDensity α H (lin A y)) ≤
          ENNReal.ofReal ((L * K0) * (2 * stableConstBound d α ‖y‖)) := by
      intro y
      apply ENNReal.ofReal_le_ofReal
      rw [stableDensity_lin_msqrt hH, ← hK0]
      have hr : 0 ≤ ‖y‖ ^ (-(d : ℝ) - α) := rpow_nonneg (norm_nonneg _) _
      have h1 : min (‖lin A y‖ ^ 2) 1 ≤ L * min (‖y‖ ^ 2) 1 := by
        rw [hA, norm_sq_lin_msqrt hH.posSemidef]
        rcases le_or_gt (‖y‖ ^ 2) 1 with hy | hy
        · rw [min_eq_left hy]
          calc min (quad H y) 1 ≤ quad H y := min_le_left _ _
            _ ≤ lamMax H * ‖y‖ ^ 2 := hlam y
            _ ≤ L * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
        · rw [min_eq_right hy.le, mul_one]
          exact (min_le_right _ _).trans hL1
      have h2 := min_sq_mul_rpow_le_stableConstBound (d := d) α y
      calc min (‖lin A y‖ ^ 2) 1 * (K0 * ‖y‖ ^ (-(d : ℝ) - α))
          = K0 * (min (‖lin A y‖ ^ 2) 1 * ‖y‖ ^ (-(d : ℝ) - α)) := by ring
        _ ≤ K0 * (L * min (‖y‖ ^ 2) 1 * ‖y‖ ^ (-(d : ℝ) - α)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hr) hK0pos.le
        _ = K0 * L * (min (‖y‖ ^ 2) 1 * ‖y‖ ^ (-(d : ℝ) - α)) := by ring
        _ ≤ K0 * L * (2 * stableConstBound d α ‖y‖) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = L * K0 * (2 * stableConstBound d α ‖y‖) := by ring
    have hint : Integrable (fun y : Rd d => (L * K0) * (2 * stableConstBound d α ‖y‖)) :=
      ((integrable_stableConstBound hα0 hα2).const_mul 2).const_mul _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top hint.lintegral_lt_top.ne (lintegral_mono hbound))

end AffineHemigroup
