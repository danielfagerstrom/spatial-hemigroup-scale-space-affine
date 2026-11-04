/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarReading
import ScaleSpaceCore.LineInterfaces

/-!
# `prop:line-levy-unique` — the uniqueness of the symmetric Lévy pair on the line, from A3

Blueprint: `blueprint/src/parts/02-cited-facts.tex`, `prop:line-levy-unique`. Q-0365.

The shared library's line classification `ScaleSpace.main_analysis` takes the uniqueness clause of
the symmetric Lévy–Khintchine representation on `ℝ` as a hypothesis, `ScaleSpace.SymLevyUnique`
(`ScaleSpaceCore.LineInterfaces`): two symmetric Lévy pairs `(a, ν)`, `ν` folded onto `(0,∞)`,
with the same exponent `a ω² + ∫ (1 - cos ωx) ν(dx)` are equal. Paper V discharges it with its
own interface `SpatialLine.fourier_toolbox_levy_unique`; this module discharges it from this
module's ledger entry **A3** (Sato Thm. 8.1 on `ℝ^d`) at `d = 1`, so that the necessity direction
of `thm:isotropic-classification` no longer rests on Paper V's interface. Spends A3(ii)
(`levy_khintchine_unique`) and A3(iii) (`levy_khintchine_converse`), nothing else.

## The route

The folding reduction the trunk's docstring describes, supplied here.

* **The lift.** A folded measure `ν` on `(0,∞)` is carried to the symmetric measure
  `ν_s = ½(e_*ν + (-e)_*ν)` on `ℝ¹`, `e(x) = x e₀` (`symLift`). Against an even integrand it
  integrates as `ν` does (`lintegral_symLift`), so `∫ (1 ∧ |y|²) ν_s(dy) = ∫ (1 ∧ x²) ν(dx)`, and
  `ν_s{0} = 0` because `ν` does not charge `(-∞, 0]`. The triplet of a pair is
  `(2a, ν_s, 0)` (`symLevyTriplet`), whose Lévy–Khintchine exponent is minus the pair's exponent
  (`lkExponent_symLevyTriplet`; the imaginary part vanishes by the symmetry of `ν_s`, as in
  `LevyTriplet.lkExponent_of_symm`).
* **A3.** A3(iii) gives an infinitely divisible law with the triplet of `P`; when `P` and `Q` have
  the same exponent it has the triplet of `Q` too, and A3(ii) identifies the two triplets. The
  covariances give `a = a'`, and the Lévy measures give `ν = ν'`: `ν(B) = 2 ν_s{y : y₀ ∈ B ∩ (0,∞)}`
  for a folded `ν` (`symLift_apply_pos`).

`LevyTriplet.lkExponent_of_symm` moved here from `AffineHemigroup.FiltrationStrict`, unchanged, so
that the necessity direction can read it below `IsotropicClassification`.
-/

namespace AffineHemigroup

open MeasureTheory Set Complex
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The exponent of a symmetric triplet -/

/-- **The exponent of a symmetric triplet** `(aI, ν, 0)`:
`-(½a|z|² + ∫ (1 - cos⟨z,x⟩) ν(dx))`. -/
theorem LevyTriplet.lkExponent_of_symm (T : LevyTriplet d) {a : ℝ}
    (hA : T.A = a • (1 : Mat d)) (hγ : T.γ = 0)
    (hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν) (z : Rd d) :
    T.lkExponent z = -(((a * ‖z‖ ^ 2 / 2 + ∫ x, (1 - Real.cos ⟪z, x⟫) ∂T.ν : ℝ)) : ℂ) := by
  have hsymI : ∫ x, (lkIntegrand z x).im ∂T.ν = 0 := by
    have h1 : ∫ x, (lkIntegrand z x).im ∂T.ν = ∫ x, (lkIntegrand z (-x)).im ∂T.ν := by
      conv_lhs => rw [← hsym]
      exact integral_map (f := fun x => (lkIntegrand z x).im)
        (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
        ((Complex.measurable_im.comp (measurable_lkIntegrand z)).aestronglyMeasurable)
    simp_rw [im_lkIntegrand_neg, integral_neg] at h1
    linarith
  have hint := T.integrable_lkIntegrand z
  apply Complex.ext
  · rw [T.re_lkExponent, hA, quad_smul, quad_one, Complex.neg_re, Complex.ofReal_re]
    ring
  · rw [T.lkExponent_eq, Complex.add_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.ofReal_im, ← RCLike.im_to_complex, ← integral_im hint]
    simp_rw [RCLike.im_to_complex, hsymI]
    simp [hγ]

/-! ## The line inside `ℝ¹` -/

/-- **The line inside `ℝ¹`**: `e(x) = x e₀`. -/
noncomputable def lineEmb (x : ℝ) : Rd 1 := x • ebasis (0 : Fin 1)

theorem continuous_lineEmb : Continuous lineEmb := by
  unfold lineEmb; fun_prop

theorem lineEmb_apply_zero (x : ℝ) : lineEmb x 0 = x := by
  simp [lineEmb, ebasis]

theorem lineEmb_neg (x : ℝ) : lineEmb (-x) = -lineEmb x := by
  simp [lineEmb, neg_smul]

theorem inner_lineEmb (z : Rd 1) (x : ℝ) : ⟪z, lineEmb x⟫ = z 0 * x := by
  rw [lineEmb, real_inner_smul_right]
  simp [ebasis, EuclideanSpace.inner_single_right]
  ring

theorem norm_sq_rd1 (z : Rd 1) : ‖z‖ ^ 2 = z 0 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sq_sqrt (by positivity), Real.norm_eq_abs,
    sq_abs]

theorem norm_sq_lineEmb (x : ℝ) : ‖lineEmb x‖ ^ 2 = x ^ 2 := by
  rw [norm_sq_rd1, lineEmb_apply_zero]

/-! ## The symmetric lift of a folded measure -/

/-- **The symmetric lift** `ν_s = ½(e_*ν + (-e)_*ν)` of a measure `ν` on the line to `ℝ¹`. -/
noncomputable def symLift (ν : Measure ℝ) : Measure (Rd 1) :=
  (2 : ℝ≥0∞)⁻¹ • (ν.map lineEmb + ν.map fun x => lineEmb (-x))

theorem measurable_lineEmb_neg : Measurable fun x : ℝ => lineEmb (-x) :=
  (continuous_lineEmb.comp continuous_neg).measurable

/-- Against an even integrand the lift integrates as the measure does. -/
theorem lintegral_symLift (ν : Measure ℝ) {g : Rd 1 → ℝ≥0∞} (hg : Measurable g)
    (heven : ∀ x : ℝ, g (lineEmb (-x)) = g (lineEmb x)) :
    ∫⁻ y, g y ∂symLift ν = ∫⁻ x, g (lineEmb x) ∂ν := by
  rw [symLift, lintegral_smul_measure, lintegral_add_measure,
    lintegral_map hg continuous_lineEmb.measurable, lintegral_map hg measurable_lineEmb_neg]
  simp_rw [heven]
  rw [smul_eq_mul, ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
    one_mul]

/-- The lift is symmetric. -/
theorem symLift_map_neg (ν : Measure ℝ) :
    (symLift ν).map (LinearIsometryEquiv.neg ℝ (E := Rd 1)) = symLift ν := by
  have hn := (LinearIsometryEquiv.neg ℝ (E := Rd 1)).continuous.measurable
  rw [symLift, Measure.map_smul, Measure.map_add _ _ hn,
    Measure.map_map hn continuous_lineEmb.measurable, Measure.map_map hn measurable_lineEmb_neg,
    add_comm]
  congr 3
  · funext x
    simp [lineEmb_neg]
  · funext x
    simp [lineEmb_neg]

/-- For a folded `ν` and a measurable `B`, `ν_s{y : y₀ ∈ B ∩ (0,∞)} = ½ ν(B)`. -/
theorem symLift_apply_pos {ν : Measure ℝ} (hν : ScaleSpace.IsFolded ν) {B : Set ℝ}
    (hB : MeasurableSet B) :
    symLift ν ((fun y : Rd 1 => y 0) ⁻¹' (B ∩ Ioi 0)) = (2 : ℝ≥0∞)⁻¹ * ν B := by
  have hC : MeasurableSet ((fun y : Rd 1 => y 0) ⁻¹' (B ∩ Ioi 0)) :=
    (measurable_pi_apply (0 : Fin 1)).comp (PiLp.continuous_ofLp 2 _).measurable
      (hB.inter measurableSet_Ioi)
  rw [symLift, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply continuous_lineEmb.measurable hC, Measure.map_apply measurable_lineEmb_neg hC,
    smul_eq_mul]
  have h1 : lineEmb ⁻¹' ((fun y : Rd 1 => y 0) ⁻¹' (B ∩ Ioi 0)) = B ∩ Ioi 0 := by
    ext x; simp [lineEmb_apply_zero]
  have h2 : ν ((fun x => lineEmb (-x)) ⁻¹' ((fun y : Rd 1 => y 0) ⁻¹' (B ∩ Ioi 0))) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hν
    simp only [mem_preimage, lineEmb_apply_zero, mem_inter_iff, mem_Ioi] at hx
    exact mem_Iic.2 (by linarith [hx.2])
  have h3 : ν (B ∩ Ioi 0) = ν B := by
    have hd : ν (B \ Ioi 0) = 0 :=
      measure_mono_null (fun x hx => mem_Iic.2 (not_lt.1 hx.2)) hν
    rw [← measure_inter_add_sdiff B measurableSet_Ioi, hd, add_zero]
  rw [h1, h2, add_zero, h3]

/-- A folded measure is determined by its lift. -/
theorem eq_of_symLift_eq {ν ν' : Measure ℝ} (hν : ScaleSpace.IsFolded ν)
    (hν' : ScaleSpace.IsFolded ν') (h : symLift ν = symLift ν') : ν = ν' := by
  ext B hB
  have h1 := symLift_apply_pos hν hB
  rw [h, symLift_apply_pos hν' hB] at h1
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h1.symm

/-! ## The triplet of a symmetric Lévy pair -/

/-- **The triplet of a symmetric Lévy pair** `(a, ν)` on `ℝ¹`: `(2a, ν_s, 0)`. -/
noncomputable def symLevyTriplet (P : ScaleSpace.SymLevyPair) : LevyTriplet 1 where
  A := (2 * P.a) • (1 : Mat 1)
  ν := symLift P.ν
  γ := 0
  A_posSemidef := Matrix.PosSemidef.one.smul (by linarith [P.a_nonneg])
  ν_zero := by
    rw [symLift, Measure.smul_apply, Measure.add_apply,
      Measure.map_apply continuous_lineEmb.measurable (measurableSet_singleton 0),
      Measure.map_apply measurable_lineEmb_neg (measurableSet_singleton 0)]
    have h0 : ∀ s : Set ℝ, (∀ x ∈ s, x = 0) → P.ν s = 0 := fun s hs =>
      measure_mono_null (fun x hx => mem_Iic.2 (hs x hx).le) P.ν_folded
    rw [h0 _ fun x hx => by simpa [lineEmb_apply_zero] using congrArg (· 0) hx,
      h0 _ fun x hx => by simpa [lineEmb_apply_zero] using congrArg (· 0) hx]
    simp
  ν_integrable := by
    rw [lintegral_symLift P.ν (by fun_prop) fun x => by rw [lineEmb_neg, norm_neg]]
    simp_rw [norm_sq_lineEmb, min_comm _ (1 : ℝ)]
    exact P.ν_integrable

/-- **The exponent of the triplet** is minus the pair's exponent. -/
theorem lkExponent_symLevyTriplet (P : ScaleSpace.SymLevyPair) (z : Rd 1) :
    (symLevyTriplet P).lkExponent z = -((P.exponent (z 0) : ℝ) : ℂ) := by
  rw [(symLevyTriplet P).lkExponent_of_symm (a := 2 * P.a) rfl rfl (symLift_map_neg P.ν) z]
  congr 2
  have hint : ∫ y, (1 - Real.cos ⟪z, y⟫) ∂(symLevyTriplet P).ν
      = (∫⁻ x, ENNReal.ofReal (1 - Real.cos (z 0 * x)) ∂P.ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun y => sub_nonneg.2 (Real.cos_le_one _)) (by fun_prop)]
    congr 1
    refine (lintegral_symLift P.ν (by fun_prop) fun x => ?_).trans ?_
    · rw [inner_lineEmb, inner_lineEmb, mul_neg, Real.cos_neg]
    · simp_rw [inner_lineEmb]
  have hfin := P.exponentL_ne_top (z 0)
  rw [ScaleSpace.SymLevyPair.exponentL] at hfin
  rw [hint, ScaleSpace.SymLevyPair.exponent, ScaleSpace.SymLevyPair.exponentL,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.add_ne_top.1 hfin).2,
    ENNReal.toReal_ofReal (mul_nonneg P.a_nonneg (sq_nonneg _)), norm_sq_rd1]
  ring

/-! ## The discharge -/

/-- **`prop:line-levy-unique`**: two symmetric Lévy pairs on the line with the same exponent are
equal, the trunk's hypothesis `ScaleSpace.SymLevyUnique` discharged from ledger A3 at `d = 1`
(A3(iii) for a law with the first pair's triplet, A3(ii) to identify the two triplets). -/
theorem line_levy_unique : ScaleSpace.SymLevyUnique := by
  intro P Q hPQ
  obtain ⟨μ, hprob, hID, hT⟩ := levy_khintchine_converse (symLevyTriplet P)
  haveI := hprob
  have hTQ : HasTriplet μ (symLevyTriplet Q) := fun z => by
    rw [hT z, lkExponent_symLevyTriplet, lkExponent_symLevyTriplet, hPQ]
  obtain ⟨hA, hν, -⟩ := levy_khintchine_unique μ hID _ _ hT hTQ
  refine ⟨?_, eq_of_symLift_eq P.ν_folded Q.ν_folded hν⟩
  have h := congrFun (congrFun hA 0) 0
  change ((2 * P.a) • (1 : Mat 1)) 0 0 = ((2 * Q.a) • (1 : Mat 1)) 0 0 at h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  linarith

end AffineHemigroup
