/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.GaussMixture
import AffineHemigroup.OriginBoundedness
import AffineHemigroup.RadialTransform
import AffineHemigroup.ThresholdLimit
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `lem:delay-polar-profile`: the polar profile of a delay datum, without monotonicity

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:delay-polar-profile`. Wave 2, group A
(Q-0281).

The blueprint's route, with the mixture density `f(x) = ∫_0^∞ g_u(x) k_I(u) du/u` carried as the
radial function `delayRadialL k |x|` in `ℝ≥0∞`:

* `1 - e^{-u|ξ|²/2} = ∫ (1 - cos⟨ξ,x⟩) g_u(x) dx` (`lintegral_one_sub_cos_heatKernel`, the real part
  of the transform of `g^{(d)}_u`, which has the density `g_u`);
* Tonelli exchanges the integrals (`delay_exponent_eq_lintegral`);
* the substitution `u = r²/2v` turns `f(x)` into `π^{-d/2} r^{-d} ∫_0^∞ v^{d/2-1} e^{-v} k_I(r²/2v) dv`
  (`delayRadialL_eq`), through Mathlib's one-dimensional change of variables;
* `f(x) < ∞` for `x ≠ 0` splits at `u = 1` (`delayRadialL_ne_top`);
* the integrability conditions are `∫ (|x|² ∧ 1) f(x) dx < ∞`, from the second moment
  `∫ |x|² g_u = K₂ u` of the Gaussian (`lintegral_norm_sq_heatKernel`) and polar coordinates.

The profile `k_I` is a.e.-measurable only, so its composition with `v ↦ r²/2v` is read through the
quasi-measure-preservation of that map on `(0,∞)` (`quasiMeasurePreserving_div_Ioi`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The Gaussian's `1 - cos` and its second moment -/

/-- `∫ (1 - cos⟨ξ,x⟩) g_u(x) dx = 1 - e^{-u|ξ|²/2}` for `u > 0`. -/
theorem lintegral_one_sub_cos_heatKernel {u : ℝ} (hu : 0 < u) (ξ : Rd d) :
    ∫⁻ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) * ENNReal.ofReal (heatKernel d u x)
      = ENNReal.ofReal (1 - Real.exp (-(u * ‖ξ‖ ^ 2) / 2)) := by
  have hint := integrable_heatKernel (d := d) hu
  have hcos : ∫ x : Rd d, Real.cos ⟪ξ, x⟫ * heatKernel d u x = Real.exp (-(u * ‖ξ‖ ^ 2) / 2) := by
    have h := ScaleSpace.re_charFun_eq_integral_cos (gaussVar d u) ξ
    rw [charFun_gaussVar hu.le, Complex.ofReal_re, gaussVar_eq_withDensity hu] at h
    rw [h]
    have hdens : (fun x : Rd d => ENNReal.ofReal (heatKernel d u x))
        = fun x => ((Real.toNNReal (heatKernel d u x) : ℝ≥0) : ℝ≥0∞) := by
      funext x; rfl
    rw [hdens, integral_withDensity_eq_integral_smul
      ((continuous_heatKernel.measurable).real_toNNReal)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (heatKernel_nonneg hu x), smul_eq_mul,
      real_inner_comm, mul_comm]
  have hint2 : Integrable (fun x : Rd d => (1 - Real.cos ⟪ξ, x⟫) * heatKernel d u x) := by
    refine Integrable.mono' (hint.const_mul 2) (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [Real.cos_le_one ⟪ξ, x⟫])
      (heatKernel_nonneg hu x))]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.neg_one_le_cos ⟪ξ, x⟫])
      (heatKernel_nonneg hu x)
  have hnn : ∀ x : Rd d, 0 ≤ (1 - Real.cos ⟪ξ, x⟫) * heatKernel d u x := fun x =>
    mul_nonneg (by linarith [Real.cos_le_one ⟪ξ, x⟫]) (heatKernel_nonneg hu x)
  have hcongr : ∀ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) * ENNReal.ofReal (heatKernel d u x)
      = ENNReal.ofReal ((1 - Real.cos ⟪ξ, x⟫) * heatKernel d u x) := fun x =>
    (ENNReal.ofReal_mul (by linarith [Real.cos_le_one ⟪ξ, x⟫])).symm
  simp_rw [hcongr]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ hnn)]
  congr 1
  have hsplit : ∀ x : Rd d, (1 - Real.cos ⟪ξ, x⟫) * heatKernel d u x
      = heatKernel d u x - Real.cos ⟪ξ, x⟫ * heatKernel d u x := fun x => by ring
  simp_rw [hsplit]
  rw [integral_sub hint (hint.bdd_mul (c := 1) (by fun_prop)
      (ae_of_all _ fun x => by simpa using Real.abs_cos_le_one ⟪ξ, x⟫)),
    integral_heatKernel_volume hu, hcos]

/-! ## The mixture density, radially -/

/-- **The radial heat kernel** `(2πu)^{-d/2} e^{-r²/2u}`, so that `g_u(x)` is its value at `|x|`. -/
noncomputable def radialHeat (d : ℕ) (u r : ℝ) : ℝ :=
  (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (2 * u))

theorem heatKernel_eq_radialHeat (u : ℝ) (x : Rd d) : heatKernel d u x = radialHeat d u ‖x‖ := rfl

theorem measurable_radialHeat_uncurry (d : ℕ) :
    Measurable fun p : ℝ × ℝ => radialHeat d p.1 p.2 := by
  unfold radialHeat
  fun_prop

theorem radialHeat_nonneg {u : ℝ} (hu : 0 < u) (r : ℝ) : 0 ≤ radialHeat d u r := by
  unfold radialHeat
  have : 0 < 2 * Real.pi * u := by positivity
  positivity

/-- **The mixture density of the Lévy measure, radially**:
`F(r) = ∫_0^∞ g_u(r) k(u) du/u` (`ℝ≥0∞`-valued), so that `f(x) = F(|x|)`. -/
noncomputable def delayRadialL (d : ℕ) (k : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (radialHeat d u r) * ENNReal.ofReal (k u / u)

/-- **The exponent through the mixture density** (the first display of the proof of
`lem:delay-polar-profile`): `F_I(|ξ|²/2) = ½b₀|ξ|² + ∫ (1 - cos⟨ξ,x⟩) f(x) dx`, by Tonelli. -/
theorem delay_exponent_eq_lintegral (D : DelayDatum) (ξ : Rd d) :
    D.exponentL (‖ξ‖ ^ 2 / 2) = ENNReal.ofReal (D.b₀ * ‖ξ‖ ^ 2 / 2) +
      ∫⁻ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) * delayRadialL d D.k ‖x‖ := by
  rw [DelayDatum.exponentL, show D.b₀ * (‖ξ‖ ^ 2 / 2) = D.b₀ * ‖ξ‖ ^ 2 / 2 by ring]
  congr 1
  have hkm : AEMeasurable (fun u : ℝ => ENNReal.ofReal (D.k u / u)) (volume.restrict (Ioi 0)) :=
    (D.k_aemeasurable.div aemeasurable_id).ennreal_ofReal
  have hjoint : AEMeasurable (Function.uncurry fun (x : Rd d) (u : ℝ) =>
      ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) * (ENNReal.ofReal (radialHeat d u ‖x‖) *
        ENNReal.ofReal (D.k u / u))) (volume.prod (volume.restrict (Ioi 0))) := by
    refine AEMeasurable.mul (by fun_prop) (AEMeasurable.mul ?_ ?_)
    · exact ((measurable_radialHeat_uncurry d).comp
        (measurable_snd.prodMk (continuous_norm.measurable.comp measurable_fst))).ennreal_ofReal
        |>.aemeasurable
    · exact hkm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(‖ξ‖ ^ 2 / 2 * u))) * D.k u / u)
      = ∫⁻ u in Ioi (0 : ℝ), (∫⁻ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) *
          ENNReal.ofReal (radialHeat d u ‖x‖)) * ENNReal.ofReal (D.k u / u) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
        simp_rw [← heatKernel_eq_radialHeat]
        rw [lintegral_one_sub_cos_heatKernel hu ξ, ← ENNReal.ofReal_mul (by
          have : Real.exp (-(u * ‖ξ‖ ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
            have : 0 ≤ u * ‖ξ‖ ^ 2 := by positivity
            linarith)
          linarith)]
        congr 1
        rw [show -(u * ‖ξ‖ ^ 2) / 2 = -(‖ξ‖ ^ 2 / 2 * u) by ring]
        ring
    _ = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) *
          (ENNReal.ofReal (radialHeat d u ‖x‖) * ENNReal.ofReal (D.k u / u)) := by
        refine lintegral_congr fun u => ?_
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        ring
    _ = ∫⁻ x : Rd d, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) *
          (ENNReal.ofReal (radialHeat d u ‖x‖) * ENNReal.ofReal (D.k u / u)) :=
        (lintegral_lintegral_swap hjoint).symm
    _ = ∫⁻ x : Rd d, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) * delayRadialL d D.k ‖x‖ := by
        refine lintegral_congr fun x => ?_
        rw [delayRadialL, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ## The substitution `u = c/v` on `(0,∞)` -/

theorem hasDerivWithinAt_div_Ioi (c : ℝ) {v : ℝ} (hv : v ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => c / v) (c * -(v ^ 2)⁻¹) (Ioi 0) v := by
  have h := ((hasDerivAt_inv (ne_of_gt hv)).const_mul c).hasDerivWithinAt (s := Ioi 0)
  simpa [div_eq_mul_inv] using h

theorem injOn_div_Ioi {c : ℝ} (hc : 0 < c) : InjOn (fun v : ℝ => c / v) (Ioi 0) := by
  intro v hv w hw h
  simp only at h
  rw [div_eq_div_iff (ne_of_gt hv) (ne_of_gt hw)] at h
  have := mul_left_cancel₀ hc.ne' h
  linarith

theorem image_div_Ioi {c : ℝ} (hc : 0 < c) (s : Set ℝ) :
    (fun v : ℝ => c / v) '' (s ∩ Ioi 0) = (fun v : ℝ => c / v) ⁻¹' s ∩ Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, ⟨hys, hy⟩, rfl⟩
    have hy0 : (0 : ℝ) < y := hy
    refine ⟨?_, show (0 : ℝ) < c / y from div_pos hc hy0⟩
    show c / (c / y) ∈ s
    rwa [div_div_cancel₀ hc.ne']
  · rintro ⟨hxs, hx⟩
    have hx0 : (0 : ℝ) < x := hx
    refine ⟨c / x, ⟨hxs, show (0 : ℝ) < c / x from div_pos hc hx0⟩, ?_⟩
    show c / (c / x) = x
    rw [div_div_cancel₀ hc.ne']

/-- **`v ↦ c/v` preserves Lebesgue-null subsets of `(0,∞)`**, `c > 0`: the image of a null set is
null by the change of variables, and the map is its own inverse there. Mathlib types only. -/
theorem quasiMeasurePreserving_div_Ioi {c : ℝ} (hc : 0 < c) :
    Measure.QuasiMeasurePreserving (fun v : ℝ => c / v) (volume.restrict (Ioi 0))
      (volume.restrict (Ioi 0)) := by
  have hm : Measurable fun v : ℝ => c / v := measurable_const.div measurable_id
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs), ← image_div_Ioi hc]
  rw [Measure.restrict_apply hs] at hs0
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (hs.inter measurableSet_Ioi)
    (fun v hv => (hasDerivWithinAt_div_Ioi c hv.2).mono inter_subset_right)
    ((injOn_div_Ioi hc).mono inter_subset_right) (fun _ => (1 : ℝ≥0∞))
  rw [setLIntegral_one] at h
  rw [h]
  exact setLIntegral_measure_zero _ _ hs0

/-! ## The substitution `u = r²/2v` in the mixture density -/

/-- **The substitution** of the proof of `lem:delay-polar-profile`: for `r > 0`,
`F(r) = π^{-d/2} r^{-d} ∫_0^∞ v^{d/2-1} e^{-v} k(r²/2v) dv`. -/
theorem delayRadialL_eq (k : ℝ → ℝ) (hk : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u) {r : ℝ} (hr : 0 < r) :
    delayRadialL d k r = ENNReal.ofReal (Real.pi ^ (-((d : ℝ) / 2)) * r ^ (-(d : ℝ))) *
      ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) *
        k (r ^ 2 / (2 * v))) := by
  set c := r ^ 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  have himg : (fun v : ℝ => c / v) '' Ioi 0 = Ioi 0 := by
    have := image_div_Ioi hc0 univ
    rwa [univ_inter, preimage_univ, univ_inter] at this
  have hsub : delayRadialL d k r = ∫⁻ u in (fun v : ℝ => c / v) '' Ioi 0,
      ENNReal.ofReal (radialHeat d u r) * ENNReal.ofReal (k u / u) := by
    rw [himg]; rfl
  rw [hsub, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun v hv => hasDerivWithinAt_div_Ioi c hv) (injOn_div_Ioi hc0),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  have hcv : 0 < c / v := div_pos hc0 hv
  have hkv := hk (c / v) hcv
  have hk' : k (r ^ 2 / (2 * v)) = k (c / v) := by rw [hc]; congr 1; field_simp
  rw [hk', ← ENNReal.ofReal_mul (radialHeat_nonneg hcv r),
    ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  -- the real identity
  set a := (d : ℝ) / 2 with ha
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : 2 * Real.pi * (c / v) = Real.pi * r ^ 2 / v := by rw [hc]; field_simp
  have h3 : -r ^ 2 / (2 * (c / v)) = -v := by rw [hc]; field_simp
  have h4 : (Real.pi * r ^ 2 / v) ^ (-a) = Real.pi ^ (-a) * r ^ (-(d : ℝ)) * v ^ a := by
    rw [Real.div_rpow (by positivity) hv.le, Real.mul_rpow hpi.le (by positivity),
      Real.rpow_neg hv.le, div_inv_eq_mul]
    congr 2
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ha]
    push_cast; ring_nf
  have h5 : v ^ (a - 1) = v ^ a / v := Real.rpow_sub_one hv.ne' a
  rw [abs_of_neg (by have : 0 < (v ^ 2)⁻¹ := by positivity
                     nlinarith : c * -(v ^ 2)⁻¹ < 0),
    radialHeat, h2, h3, show -(d : ℝ) / 2 = -a by rw [ha]; ring, h4, h5]
  field_simp

/-! ## Finiteness of the mixture density off the origin -/

/-- `u^{-m} e^{-r²/2u} ≤ (2m/r²)^m e^{-m}` for `u, r, m > 0`: the Gaussian's flatness at `u = 0`. -/
theorem rpow_neg_mul_exp_le {m r u : ℝ} (hm : 0 < m) (hr : 0 < r) (hu : 0 < u) :
    u ^ (-m) * Real.exp (-r ^ 2 / (2 * u)) ≤ (2 * m / r ^ 2) ^ m * Real.exp (-m) := by
  set z := r ^ 2 / (2 * u) with hz
  have hz0 : 0 < z := by positivity
  have hzu : u ^ (-m) = (2 / r ^ 2) ^ m * z ^ m := by
    rw [← Real.mul_rpow (by positivity) hz0.le, hz, Real.rpow_neg hu.le, ← Real.inv_rpow hu.le]
    congr 1; field_simp
  have hexp : -r ^ 2 / (2 * u) = -z := by rw [hz]; ring
  rw [hzu, hexp, mul_assoc]
  have h := rpow_mul_exp_neg_le hm hz0
  calc (2 / r ^ 2) ^ m * (z ^ m * Real.exp (-z)) ≤ (2 / r ^ 2) ^ m * (m ^ m * Real.exp (-m)) := by
        gcongr
    _ = (2 * m / r ^ 2) ^ m * Real.exp (-m) := by
        rw [← mul_assoc, ← Real.mul_rpow (by positivity) hm.le]; congr 2; ring

/-- **The mixture density is finite off the origin** (the proof's "The value `k_d(r)` is finite"):
on `(0,1)` the factor `g_u/u` is bounded, on `[1,∞)` `g_u ≤ (2π)^{-d/2}`, and the two conditions on
`k_I` bound the two pieces. -/
theorem delayRadialL_ne_top (D : DelayDatum) {r : ℝ} (hr : 0 < r) : delayRadialL d D.k r ≠ ⊤ := by
  set a := (d : ℝ) / 2 with ha
  have hpi : 0 < 2 * Real.pi := by positivity
  set B := (2 * Real.pi) ^ (-a) * ((2 * (a + 1) / r ^ 2) ^ (a + 1) * Real.exp (-(a + 1))) with hB
  rw [delayRadialL, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B))
      D.integrable_near_zero) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hk := D.k_nonneg u hu0
    rw [← ENNReal.ofReal_mul (radialHeat_nonneg hu0 r), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hbound : radialHeat d u r / u ≤ B := by
      rw [radialHeat, hB, show -(d : ℝ) / 2 = -a by rw [ha]; ring,
        Real.mul_rpow hpi.le hu0.le, mul_assoc, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hpi.le _)
      have h := rpow_neg_mul_exp_le (m := a + 1) (by positivity) hr hu0
      calc u ^ (-a) * Real.exp (-r ^ 2 / (2 * u)) / u
          = u ^ (-(a + 1)) * Real.exp (-r ^ 2 / (2 * u)) := by
            rw [show -(a + 1) = -a - 1 by ring, Real.rpow_sub_one hu0.ne']; ring
        _ ≤ _ := h
    calc radialHeat d u r * (D.k u / u) = radialHeat d u r / u * D.k u := by ring
      _ ≤ B * D.k u := mul_le_mul_of_nonneg_right hbound hk
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top
      (r := (2 * Real.pi) ^ (-a))) D.integrable_at_top) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 1 < u) => ?_
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [radialHeat]
    calc (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (2 * u))
        ≤ (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by
            have : 0 ≤ r ^ 2 / (2 * u) := by positivity
            rw [neg_div]; linarith)
      _ ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
          rw [mul_one]
          refine Real.rpow_le_rpow_of_nonpos hpi (by nlinarith) ?_
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith
      _ = (2 * Real.pi) ^ (-a) := by rw [ha]; ring_nf

/-! ## The polar profile from the mixture density -/

/-- The integrand of `eq:polar-profile-d` is a.e.-measurable on `(0,∞)`, for `r ≠ 0`. -/
theorem aestronglyMeasurable_polarIntegrand (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    AEStronglyMeasurable (fun v : ℝ => v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) *
      D.k (r ^ 2 / (2 * v))) (volume.restrict (Ioi 0)) := by
  have hc : 0 < r ^ 2 / 2 := by positivity
  have hk : AEMeasurable (fun v : ℝ => D.k (r ^ 2 / 2 / v)) (volume.restrict (Ioi 0)) :=
    D.k_aemeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_div_Ioi hc)
  refine (((by fun_prop : Measurable fun v : ℝ => v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v)).aemeasurable.mul
    hk).aestronglyMeasurable).congr (ae_of_all _ fun v => ?_)
  simp only [div_div]

/-- The lower integral `J(r) = ∫_0^∞ v^{d/2-1} e^{-v} k(r²/2v) dv` is finite for `r > 0`. -/
theorem lintegral_polarIntegrand_ne_top (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) *
      D.k (r ^ 2 / (2 * v))) ≠ ⊤ := by
  have h := delayRadialL_eq (d := d) D.k D.k_nonneg hr
  have hfin := delayRadialL_ne_top (d := d) D hr
  have hpos : 0 < Real.pi ^ (-((d : ℝ) / 2)) * r ^ (-(d : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.rpow_pos_of_pos hr _)
  intro htop
  rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hpos)] at h
  exact hfin h

/-- **`k_d` is finite**: the integrand of `eq:polar-profile-d` is integrable for `r > 0`. -/
theorem integrableOn_polarIntegrand (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * D.k (r ^ 2 / (2 * v)))
      (Ioi 0) := by
  refine ⟨aestronglyMeasurable_polarIntegrand D hr, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq ?_)
    (lt_top_iff_ne_top.mpr (lintegral_polarIntegrand_ne_top (d := d) D hr))
  refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  have hk := D.k_nonneg (r ^ 2 / (2 * v)) (show (0 : ℝ) < r ^ 2 / (2 * v) by positivity)
  rw [Real.enorm_eq_ofReal (mul_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _)
    (Real.exp_pos _).le) hk)]

/-- **The polar profile through the mixture density**: for `r > 0`,
`k_d(r) / (|S^{d-1}| r^d) = f(r)`, i.e. `F(r) = ofReal (k_d(r)/(|S^{d-1}| r^d))`. -/
theorem delayRadialL_eq_polarProfile (hd : 1 ≤ d) (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    delayRadialL d D.k r = ENNReal.ofReal (polarProfileOf D.k d r / (sphereArea d * r ^ d)) := by
  have hA := (sphereArea_eq_toSphere hd).2
  set J := ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) *
      D.k (r ^ 2 / (2 * v))) with hJ
  have hJfin : J ≠ ⊤ := lintegral_polarIntegrand_ne_top D hr
  have hint := integrableOn_polarIntegrand (d := d) D hr
  have hBoch : (∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * D.k (r ^ 2 / (2 * v)))
      = J.toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_ hint.aestronglyMeasurable
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v (hv : 0 < v) => ?_)
    have hk := D.k_nonneg (r ^ 2 / (2 * v)) (show (0 : ℝ) < r ^ 2 / (2 * v) by positivity)
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.exp_pos _).le) hk
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity)
  have hL : delayRadialL d D.k r = ENNReal.ofReal (Real.pi ^ (-((d : ℝ) / 2)) * r ^ (-(d : ℝ))
      * J.toReal) := by
    rw [delayRadialL_eq D.k D.k_nonneg hr,
      ENNReal.ofReal_mul (p := Real.pi ^ (-((d : ℝ) / 2)) * r ^ (-(d : ℝ))) (by positivity),
      ENNReal.ofReal_toReal hJfin]
  rw [hL, polarProfileOf, hBoch]
  congr 1
  rw [sphereArea]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.rpow_neg hpi.le, Real.rpow_neg hr.le, Real.rpow_natCast]
  field_simp

theorem polarProfileOf_nonneg (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    0 ≤ polarProfileOf D.k d r := by
  rw [polarProfileOf]
  refine mul_nonneg (div_nonneg zero_le_two (Real.Gamma_nonneg_of_nonneg (by positivity)))
    (setIntegral_nonneg measurableSet_Ioi fun v (hv : 0 < v) => ?_)
  have hk := D.k_nonneg (r ^ 2 / (2 * v)) (show (0 : ℝ) < r ^ 2 / (2 * v) by positivity)
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.exp_pos _).le) hk

/-! ## The second moment of the Gaussian, and the integrability conditions -/

/-- **The second moment of `g_u`**: `∫ |x|² g_u(x) dx = K₂ u` with
`K₂ = |S^{d-1}| π^{-d/2} Γ(d/2 + 1)` (which is `d`), by polar coordinates and the Gamma integral. -/
theorem lintegral_norm_sq_heatKernel (hd : 1 ≤ d) {u : ℝ} (hu : 0 < u) :
    ∫⁻ x : Rd d, ENNReal.ofReal (‖x‖ ^ 2) * ENNReal.ofReal (heatKernel d u x) =
      ENNReal.ofReal (sphereArea d * Real.pi ^ (-((d : ℝ) / 2)) * Real.Gamma ((d : ℝ) / 2 + 1) * u) := by
  have hA := (sphereArea_eq_toSphere hd).2
  set a := (d : ℝ) / 2 with ha
  have hb : 0 < 1 / (2 * u) := by positivity
  have hq : (-1 : ℝ) < (d : ℝ) + 1 := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow hq one_le_two hb).const_mul
    ((2 * Real.pi * u) ^ (-a))
  have hval := integral_rpow_mul_exp_neg_mul_rpow two_pos hq hb
  set f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (radialHeat d u r) with hf
  have hfm : Measurable f := by
    rw [hf]
    exact (measurable_id.pow_const 2).ennreal_ofReal.mul
      ((measurable_radialHeat_uncurry d).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have heq : (∫⁻ x : Rd d, ENNReal.ofReal (‖x‖ ^ 2) * ENNReal.ofReal (heatKernel d u x))
      = ∫⁻ x : Rd d, f ‖x‖ := rfl
  rw [heq, lintegral_radial hd f hfm]
  have hinner : ∫⁻ r in Ioi (0 : ℝ), f r * ENNReal.ofReal (r ^ (d - 1))
      = ENNReal.ofReal (∫ r in Ioi (0 : ℝ), (2 * Real.pi * u) ^ (-a) *
          (r ^ ((d : ℝ) + 1) * Real.exp (-(1 / (2 * u)) * r ^ (2 : ℝ)))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r (hr : 0 < r) => by positivity))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf]
    beta_reduce
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
      exact mul_nonneg (by positivity) (radialHeat_nonneg hu r)), pow_pred_eq_rpow hd hr]
    congr 1
    rw [radialHeat, show -(d : ℝ) / 2 = -a by rw [ha]; ring, Real.rpow_two]
    have h1 : r ^ 2 * r ^ ((d : ℝ) - 1) = r ^ ((d : ℝ) + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]; congr 1; push_cast; ring
    have h2 : -r ^ 2 / (2 * u) = -(1 / (2 * u)) * r ^ 2 := by ring
    rw [h2, ← h1]
    ring
  rw [hinner, integral_const_mul, hval, ← ENNReal.ofReal_mul hA.le]
  congr 1
  -- `(2πu)^{-a} (1/(2u))^{-(d+2)/2} Γ(a+1)/2 = π^{-a} Γ(a+1) u`
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2u : 0 < 2 * u := by positivity
  have e1 : (2 * Real.pi * u) ^ (-a) = Real.pi ^ (-a) * (2 * u) ^ (-a) := by
    rw [show 2 * Real.pi * u = Real.pi * (2 * u) by ring, Real.mul_rpow hpi.le h2u.le]
  have e2 : (1 / (2 * u)) ^ (-((d : ℝ) + 1 + 1) / 2) = (2 * u) ^ a * (2 * u) := by
    rw [one_div, Real.inv_rpow h2u.le, ← Real.rpow_neg h2u.le,
      show -(-((d : ℝ) + 1 + 1) / 2) = a + 1 by rw [ha]; ring, Real.rpow_add h2u, Real.rpow_one]
  have e3 : ((d : ℝ) + 1 + 1) / 2 = a + 1 := by rw [ha]; ring
  rw [e1, e2, e3, show -((d : ℝ) / 2) = -a by rw [ha]]
  have e4 : (2 * u) ^ (-a) * (2 * u) ^ a = 1 := by
    rw [← Real.rpow_add h2u, neg_add_cancel, Real.rpow_zero]
  calc sphereArea d * (Real.pi ^ (-a) * (2 * u) ^ (-a) * ((2 * u) ^ a * (2 * u) * (1 / 2) *
        Real.Gamma (a + 1)))
      = sphereArea d * (Real.pi ^ (-a) * ((2 * u) ^ (-a) * (2 * u) ^ a) * u *
        Real.Gamma (a + 1)) := by ring
    _ = sphereArea d * Real.pi ^ (-a) * Real.Gamma (a + 1) * u := by rw [e4]; ring

/-- **The integrability conditions through the mixture density**: `∫ (|x|² ∧ 1) f(x) dx < ∞`. -/
theorem lintegral_min_delayRadialL_ne_top (hd : 1 ≤ d) (D : DelayDatum) :
    ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) * delayRadialL d D.k ‖x‖ ≠ ⊤ := by
  set K₂ := sphereArea d * Real.pi ^ (-((d : ℝ) / 2)) * Real.Gamma ((d : ℝ) / 2 + 1) with hK₂
  have hkm : AEMeasurable (fun u : ℝ => ENNReal.ofReal (D.k u / u)) (volume.restrict (Ioi 0)) :=
    (D.k_aemeasurable.div aemeasurable_id).ennreal_ofReal
  have hjoint : AEMeasurable (Function.uncurry fun (x : Rd d) (u : ℝ) =>
      ENNReal.ofReal (min (‖x‖ ^ 2) 1) * (ENNReal.ofReal (radialHeat d u ‖x‖) *
        ENNReal.ofReal (D.k u / u))) (volume.prod (volume.restrict (Ioi 0))) := by
    refine AEMeasurable.mul (by fun_prop) (AEMeasurable.mul ?_ ?_)
    · exact ((measurable_radialHeat_uncurry d).comp
        (measurable_snd.prodMk (continuous_norm.measurable.comp measurable_fst))).ennreal_ofReal
        |>.aemeasurable
    · exact hkm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hswap : ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) * delayRadialL d D.k ‖x‖
      = ∫⁻ u in Ioi (0 : ℝ), (∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) *
          ENNReal.ofReal (heatKernel d u x)) * ENNReal.ofReal (D.k u / u) := by
    calc ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) * delayRadialL d D.k ‖x‖
        = ∫⁻ x : Rd d, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min (‖x‖ ^ 2) 1) *
            (ENNReal.ofReal (radialHeat d u ‖x‖) * ENNReal.ofReal (D.k u / u)) := by
          refine lintegral_congr fun x => ?_
          rw [delayRadialL, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) *
            (ENNReal.ofReal (radialHeat d u ‖x‖) * ENNReal.ofReal (D.k u / u)) :=
          lintegral_lintegral_swap hjoint
      _ = _ := by
          refine lintegral_congr fun u => ?_
          rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [heatKernel_eq_radialHeat]; ring
  rw [hswap, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- `u < 1`: the second moment
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := K₂))
      D.integrable_near_zero) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hk := D.k_nonneg u hu0
    calc (∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) * ENNReal.ofReal (heatKernel d u x)) *
          ENNReal.ofReal (D.k u / u)
        ≤ (∫⁻ x : Rd d, ENNReal.ofReal (‖x‖ ^ 2) * ENNReal.ofReal (heatKernel d u x)) *
          ENNReal.ofReal (D.k u / u) := by
          refine mul_le_mul' (lintegral_mono fun x => ?_) le_rfl
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_rfl
      _ = ENNReal.ofReal (K₂ * u) * ENNReal.ofReal (D.k u / u) := by
          rw [lintegral_norm_sq_heatKernel hd hu0]
      _ = ENNReal.ofReal K₂ * ENNReal.ofReal (D.k u) := by
          rw [← ENNReal.ofReal_mul (by
              have : 0 ≤ K₂ := by
                rw [hK₂]
                have := (sphereArea_eq_toSphere hd).2
                have : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
                positivity
              positivity), ← ENNReal.ofReal_mul (by
              rw [hK₂]
              have := (sphereArea_eq_toSphere hd).2
              have : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
              positivity)]
          congr 1
          field_simp
  · -- `u ≥ 1`: the total mass
    refine ne_top_of_le_ne_top D.integrable_at_top ?_
    rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 1 < u) => ?_
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    calc (∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) * ENNReal.ofReal (heatKernel d u x)) *
          ENNReal.ofReal (D.k u / u)
        ≤ (∫⁻ x : Rd d, ENNReal.ofReal (heatKernel d u x)) * ENNReal.ofReal (D.k u / u) := by
          refine mul_le_mul' (lintegral_mono fun x => ?_) le_rfl
          calc ENNReal.ofReal (min (‖x‖ ^ 2) 1) * ENNReal.ofReal (heatKernel d u x)
              ≤ 1 * ENNReal.ofReal (heatKernel d u x) :=
                mul_le_mul' (ENNReal.ofReal_le_one.mpr (min_le_right _ _)) le_rfl
            _ = _ := one_mul _
      _ = ENNReal.ofReal (D.k u / u) := by rw [lintegral_heatKernel_volume hu0, one_mul]

/-! ## `lem:delay-polar-profile` -/

/-- The mixture density is a measurable function of the radius: it is unchanged when `k_I` is
replaced by a measurable modification on `(0,∞)`. -/
theorem measurable_delayRadialL (D : DelayDatum) : Measurable (delayRadialL d D.k) := by
  set k' := D.k_aemeasurable.mk D.k with hk'
  have hkk' : D.k =ᵐ[volume.restrict (Ioi 0)] k' := D.k_aemeasurable.ae_eq_mk
  have heq : delayRadialL d D.k = delayRadialL d k' := by
    funext r
    refine lintegral_congr_ae ?_
    filter_upwards [hkk'] with u hu
    rw [hu]
  rw [heq]
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (radialHeat d p.2 p.1) * ENNReal.ofReal (k' p.2 / p.2) := by
    refine Measurable.mul ?_ ?_
    · exact ((measurable_radialHeat_uncurry d).comp (measurable_snd.prodMk measurable_fst)).ennreal_ofReal
    · exact ((D.k_aemeasurable.measurable_mk.comp measurable_snd).div measurable_snd).ennreal_ofReal
  exact hm.lintegral_prod_right'

/-- `k_d(r) = |S^{d-1}| r^d F(r)` for `r > 0`. -/
theorem polarProfileOf_eq_delayRadialL (hd : 1 ≤ d) (D : DelayDatum) {r : ℝ} (hr : 0 < r) :
    polarProfileOf D.k d r = sphereArea d * r ^ d * (delayRadialL d D.k r).toReal := by
  have hA := (sphereArea_eq_toSphere hd).2
  rw [delayRadialL_eq_polarProfile hd D hr, ENNReal.toReal_ofReal (div_nonneg
    (polarProfileOf_nonneg D hr) (by positivity))]
  field_simp

/-- **`lem:delay-polar-profile`**: for a delay datum `(b₀, k_I)` (not necessarily monotone), its
polar profile `k_d` is finite (its integrand integrable at every `r > 0`) and measurable on
`(0,∞)` (its restriction there is measurable: blind review N3-1), satisfies `∫₀¹ k_d(r) r dr < ∞` and `∫₁^∞ k_d(r) dr/r < ∞`, and
`F_I(|ξ|²/2) = ½ b₀|ξ|² + ∫ (1 - cos⟨ξ,x⟩) k_d(|x|)/(|S^{d-1}||x|^d) dx`. -/
theorem delay_polar_profile (hd : 1 ≤ d) (D : DelayDatum) :
    (∀ r ∈ Ioi (0 : ℝ), IntegrableOn
        (fun v => v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * D.k (r ^ 2 / (2 * v))) (Ioi 0)) ∧
      Measurable ((Ioi (0 : ℝ)).restrict (polarProfileOf D.k d)) ∧
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (polarProfileOf D.k d r * r) ≠ ⊤ ∧
      ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (polarProfileOf D.k d r / r) ≠ ⊤ ∧
      ∀ ξ : Rd d, D.exponentL (‖ξ‖ ^ 2 / 2) = ENNReal.ofReal (D.b₀ * ‖ξ‖ ^ 2 / 2) +
        ∫⁻ x, ENNReal.ofReal ((1 - Real.cos (inner ℝ ξ x)) *
          (polarProfileOf D.k d ‖x‖ / (sphereArea d * ‖x‖ ^ d))) := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hFm := measurable_delayRadialL (d := d) D
  -- (ii)
  have hmeas : Measurable ((Ioi (0 : ℝ)).restrict (polarProfileOf D.k d)) := by
    have hm : Measurable fun r : ℝ => sphereArea d * r ^ d * (delayRadialL d D.k r).toReal :=
      (measurable_const.mul (measurable_id.pow_const d)).mul hFm.ennreal_toReal
    have heq : (Ioi (0 : ℝ)).restrict (polarProfileOf D.k d) =
        (Ioi (0 : ℝ)).restrict fun r : ℝ => sphereArea d * r ^ d * (delayRadialL d D.k r).toReal := by
      funext r
      exact polarProfileOf_eq_delayRadialL hd D r.2
    rw [heq]
    exact hm.comp measurable_subtype_coe
  -- the integrability conditions through `∫ (|x|² ∧ 1) f(x) dx`
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (min (r ^ 2) 1) * delayRadialL d D.k r with hg
  have hgm : Measurable g := (by fun_prop : Measurable fun r : ℝ => min (r ^ 2) 1).ennreal_ofReal.mul hFm
  have htot : ENNReal.ofReal (sphereArea d) * ∫⁻ r in Ioi (0 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1))
      ≠ ⊤ := by
    rw [← lintegral_radial hd g hgm]
    exact lintegral_min_delayRadialL_ne_top hd D
  have hpt : ∀ r : ℝ, 0 < r → ENNReal.ofReal (sphereArea d) * (g r * ENNReal.ofReal (r ^ (d - 1)))
      = ENNReal.ofReal (min (r ^ 2) 1 * polarProfileOf D.k d r / r) := by
    intro r hr
    rw [hg]
    beta_reduce
    rw [delayRadialL_eq_polarProfile hd D hr, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by
        exact mul_nonneg (by positivity) (div_nonneg (polarProfileOf_nonneg D hr) (by positivity))),
      ← ENNReal.ofReal_mul hA.le]
    congr 1
    rw [pow_pred_eq_rpow hd hr]
    have hrd : r ^ d = r ^ ((d : ℝ) - 1) * r := by
      rw [← Real.rpow_natCast, ← Real.rpow_add_one hr.ne']; ring_nf
    rw [hrd]
    field_simp
  have hbound : ∀ s : Set ℝ, s ⊆ Ioi 0 → MeasurableSet s →
      ∫⁻ r in s, ENNReal.ofReal (min (r ^ 2) 1 * polarProfileOf D.k d r / r) ≠ ⊤ := by
    intro s hs hsm
    refine ne_top_of_le_ne_top htot ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (le_of_eq ?_) (lintegral_mono_set hs)
    refine setLIntegral_congr_fun hsm fun r hr => (hpt r (hs hr)).symm
  refine ⟨fun r hr => integrableOn_polarIntegrand D hr, hmeas, ?_, ?_, ?_⟩
  · refine ne_top_of_le_ne_top (hbound (Ioo 0 1) Ioo_subset_Ioi_self measurableSet_Ioo)
      (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_))
    have h2 : min (r ^ 2) 1 = r ^ 2 := min_eq_left (by nlinarith [hr.1, hr.2])
    rw [h2]
    congr 1
    field_simp
  · refine ne_top_of_le_ne_top (hbound (Ioi 1) (Ioi_subset_Ioi zero_le_one) measurableSet_Ioi)
      (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_))
    have h2 : min (r ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    rw [h2, one_mul]
  · intro ξ
    rw [delay_exponent_eq_lintegral D ξ]
    congr 1
    refine lintegral_congr fun x => ?_
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [delayRadialL_eq_polarProfile hd D hn, ← ENNReal.ofReal_mul (by
        linarith [Real.cos_le_one ⟪ξ, x⟫])]

/-- **`lem:delay-polar-profile`**, the last sentence: if `k_d` is nonincreasing, `(b₀, k_d)` is an
isotropic origin datum in dimension `d` whose exponent is `ξ ↦ F_I(|ξ|²/2)`. -/
theorem delay_polar_profile_datum (hd : 1 ≤ d) (D : DelayDatum)
    (hmono : AntitoneOn (polarProfileOf D.k d) (Ioi 0)) :
    ∃ O : OriginDatum d, O.a = D.b₀ ∧ (∀ r ∈ Ioi (0 : ℝ), O.k r = polarProfileOf D.k d r) ∧
      ∀ ξ : Rd d, O.exponentL ξ = D.exponentL (‖ξ‖ ^ 2 / 2) := by
  obtain ⟨-, -, h0, h1, hid⟩ := delay_polar_profile hd D
  let O : OriginDatum d := ⟨D.b₀, polarProfileOf D.k d, D.b₀_nonneg,
    fun r hr => polarProfileOf_nonneg D hr, hmono, h0, h1⟩
  refine ⟨O, rfl, fun r _ => rfl, fun ξ => ?_⟩
  rw [hid ξ, OriginDatum.exponentL]
  congr 1
  rw [OriginDatum.levyMeasure, lintegral_withDensity_eq_lintegral_mul _ O.measurable_levyDensity
    (by fun_prop)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), mul_comm,
      ← ENNReal.ofReal_mul (by linarith [Real.cos_le_one ⟪ξ, x⟫])]

end AffineHemigroup
