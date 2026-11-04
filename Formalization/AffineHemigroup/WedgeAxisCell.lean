/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.WedgeAxisProfiles
import AffineHemigroup.PolarReading
import AffineHemigroup.SimilarityLine

/-!
# `prop:wedge-axis-profiles`(2): the whole cell

Blueprint: `blueprint/src/parts/05-table.tex`, `prop:wedge-axis-profiles`, clause (2); clause (1) is
`AffineHemigroup.WedgeAxisProfiles`.

## The route

The node's: a law `μ_I` of `𝔉(C)` is rotation invariant, self-decomposable and not `δ₀` (the rays),
and infinitely divisible (the chain `s ↦ sI`, A6). A3(i) gives it a triplet and A2 the polar form of
the Lévy measure. **The mean over the sphere** (`polar_mean_form`) then replaces the triplet by a
radial one: the left side of `F(|ω|) = ½⟨ω, Aω⟩ + ∫(1 - cos⟨ω, x⟩) ν(dx)` depends on `ω` only
through `|ω|`, so it is its own mean against the normalised surface measure `σ̄`. Neither ledger
A3(ii) nor the determination of a rotation-invariant measure by its radial image is read, and A4,
which the forward direction of `prop:isotropic-polar-reading`(1) spends to make `μ_I` infinitely divisible, is
not needed.

The measure `ν` enters the mean only through `∫ c(|x|) ν(dx)`, so `map_norm_eq_of_polar`, its radial
image `k̄(r) dr/r`, is all that is read of A2's formula; that is why `T.ν` needs only to be σ-finite
(`LevyTriplet.sigmaFinite`) for the exchange of the integrals.

**Right-continuity** is not proved of the mean `k̄` itself: the profile is replaced by its
right-continuous modification (`RadialProfile.rightMod`), which has the same law.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable)

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology ENNReal

variable {d : ℕ}

/-! ## Two facts on the sphere and on Lévy measures -/

/-- **A Lévy measure is σ-finite**: it is finite off every ball about the origin, and `ν{0} = 0`. -/
theorem LevyTriplet.sigmaFinite (T : LevyTriplet d) : SigmaFinite T.ν := by
  have hsets : T.ν.FiniteSpanningSetsIn univ :=
    { set := fun n : ℕ => {x : Rd d | ((n : ℝ) + 1)⁻¹ < ‖x‖} ∪ {0}
      set_mem := fun _ => mem_univ _
      finite := fun n => by
        refine (measure_union_le _ _).trans_lt ?_
        rw [T.ν_zero, add_zero]
        exact lt_top_iff_ne_top.2 (T.measure_norm_gt_ne_top (by positivity))
      spanning := by
        refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
        rcases eq_or_ne x 0 with rfl | hx
        · exact ⟨0, Or.inr rfl⟩
        · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx)
          exact ⟨n, Or.inl (by simpa [one_div] using hn)⟩ }
  exact hsets.sigmaFinite

/-- **The mean of a quadratic form over the sphere**: `∫ ⟨u, Au⟩ σ̄(du) = tr A/d`. -/
theorem integral_quad_normSphere (hd : 1 ≤ d) (A : Mat d) :
    ∫ u, quad A u ∂normSphere d = A.trace / d := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  simp_rw [quad_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_normSphere hd (by fun_prop)]
  have hij : ∀ i j : Fin d, ∫ u : Rd d, (u i * u j) * A i j ∂normSphere d =
      if i = j then A i i * (1 / d) else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [integral_mul_const, ← integral_coord_sq hd i, mul_comm]
      congr 2
      funext u
      ring
    · refine integral_normSphere_eq_zero_of_odd i fun u => ?_
      rw [flipIso_apply, flipIso_apply, if_pos rfl, if_neg (Ne.symm h)]
      ring
  simp_rw [fun i => integral_finsetSum (μ := normSphere d) (Finset.univ : Finset (Fin d))
    (f := fun j u => (u i * u j) * A i j)
    (fun j _ => integrable_normSphere hd (by fun_prop)), hij, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Matrix.trace, ← Finset.sum_mul]
  simp [div_eq_mul_inv]

/-- The surface measure is `|S^{d-1}|` times the normalised one. -/
theorem lintegral_toSphere_eq (hd : 1 ≤ d) {h : Rd d → ℝ≥0∞} (hm : Measurable h) :
    ∫⁻ η : Metric.sphere (0 : Rd d) 1, h η ∂((volume : Measure (Rd d)).toSphere) =
      ENNReal.ofReal (sphereArea d) * ∫⁻ u, h u ∂normSphere d := by
  obtain ⟨hA, hA0⟩ := sphereArea_eq_toSphere (d := d) hd
  rw [normSphere, lintegral_smul_measure, lintegral_map hm measurable_subtype_coe, hA, smul_eq_mul,
    ENNReal.mul_inv_cancel_left]
  · rw [← hA]; simpa using hA0
  · exact measure_ne_top _ _

/-- **The mean of `1 - cos⟨y, u⟩` over the sphere depends on `y` only through `|y|`.** -/
theorem lintegral_one_sub_cos_normSphere_radial {y y' : Rd d} (h : ‖y‖ = ‖y'‖) :
    ∫⁻ u, ENNReal.ofReal (1 - Real.cos ⟪y, u⟫) ∂normSphere d =
      ∫⁻ u, ENNReal.ofReal (1 - Real.cos ⟪y', u⟫) ∂normSphere d := by
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (y - y'))ᗮ with hQ
  have hQy : Q y = y' := Submodule.reflection_sub h
  rw [← lintegral_normSphere_isometry Q (f := fun u => ENNReal.ofReal (1 - Real.cos ⟪y', u⟫))
    (by fun_prop)]
  refine lintegral_congr fun u => ?_
  rw [← hQy, LinearIsometryEquiv.inner_map_map]

/-! ## The polar form, by the mean over the sphere -/

/-- **The form of an infinitely divisible self-decomposable law with radial transform** (the node's
paragraph "(2), the form of `μ_I`"): for `μ̂(ξ) = e^{-g(|ξ|²)}`, there are `a ≥ 0` and a
nonincreasing `k ≥ 0` with `∫ (|x|² ∧ 1) k(|x|) |x|^{-d} dx < ∞` and
`g(|ω|²) = ½ a|ω|² + ∫ (1 - cos⟨ω, x⟩) k(|x|) |x|^{-d} dx`. Spends A3(i) and A2; neither A3(ii)
nor A4. -/
theorem polar_mean_form (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsato : IsSelfDecomposableSato μ) (hID : IsInfinitelyDivisible μ) (g : ℝ → ℝ)
    (hchar : ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-g (‖ξ‖ ^ 2)) : ℝ) : ℂ)) :
    ∃ (a : ℝ) (k : ℝ → ℝ), 0 ≤ a ∧ Measurable k ∧ (∀ r, 0 ≤ k r) ∧ AntitoneOn k (Ioi 0) ∧
      (∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (k ‖x‖ / ‖x‖ ^ d))) ≠ ⊤ ∧
      ∀ ω : Rd d, ENNReal.ofReal (g (‖ω‖ ^ 2)) = ENNReal.ofReal (a * ‖ω‖ ^ 2 / 2) +
        ∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d)) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  obtain ⟨T, hT⟩ := levy_khintchine_exists μ hID
  haveI := T.sigmaFinite
  have hnn1 : ∀ ξ x : Rd d, 0 ≤ 1 - Real.cos ⟪ξ, x⟫ := fun ξ x => by
    linarith [Real.cos_le_one ⟪ξ, x⟫]
  /- The display for `F`, in `[0,∞]`. -/
  have hFe : ∀ ξ : Rd d, ENNReal.ofReal (g (‖ξ‖ ^ 2)) = ENNReal.ofReal (quad T.A ξ / 2) +
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) ∂T.ν := by
    intro ξ
    have h1 : ‖charFun μ ξ‖ = Real.exp (-g (‖ξ‖ ^ 2)) := by
      rw [hchar, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hT ξ, Complex.norm_exp, T.re_lkExponent] at h1
    have h2 := Real.exp_injective h1
    have h3 : g (‖ξ‖ ^ 2) = quad T.A ξ / 2 + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂T.ν := by linarith
    rw [h3, ENNReal.ofReal_add (by have := quad_nonneg T.A_posSemidef ξ; positivity)
      (integral_nonneg fun x => hnn1 ξ x),
      ofReal_integral_eq_lintegral_ofReal (T.integrable_one_sub_cos ξ) (ae_of_all _ (hnn1 ξ))]
  /- The polar form (A2), through its radial image. -/
  obtain ⟨lam, k₀, hlamfin, hk0, hkm₀, hka, hν⟩ := (sato_polar_criterion μ hID T hT).mp hsato
  haveI := hlamfin
  have hmap := map_norm_eq_of_polar T.ν lam k₀ hk0 hkm₀ hka hν
  set K : ℝ → ℝ≥0∞ := fun r => ∫⁻ ξ, rightLim k₀ ξ r ∂lam with hK
  have hKanti : Antitone K := fun r s hrs => lintegral_mono fun ξ => rightLim_antitone k₀ ξ hrs
  have hKm : Measurable K := hKanti.measurable
  have hdens : Measurable fun r : ℝ => K r * ENNReal.ofReal r⁻¹ :=
    hKm.mul measurable_inv.ennreal_ofReal
  have hrad : ∀ h : ℝ → ℝ≥0∞, Measurable h → ∫⁻ x, h ‖x‖ ∂T.ν =
      ∫⁻ r in Ioi (0 : ℝ), (K r * ENNReal.ofReal r⁻¹) * h r := by
    intro h hh
    rw [← lintegral_map hh continuous_norm.measurable, hmap,
      lintegral_withDensity_eq_lintegral_mul _ hdens hh]
    rfl
  have hrint : ∫⁻ r in Ioi (0 : ℝ), (K r * ENNReal.ofReal r⁻¹) * ENNReal.ofReal (min (r ^ 2) 1)
      ≠ ⊤ := by
    have h := T.ν_integrable
    rwa [hrad (fun r => ENNReal.ofReal (min (r ^ 2) 1)) (by fun_prop)] at h
  have hKfin : ∀ r : ℝ, 0 < r → K r ≠ ⊤ := by
    intro r₀ hr₀ htop
    have hpos : 0 < volume (Ioo (r₀ / 2) r₀) := by
      rw [Real.volume_Ioo]; simp; linarith
    refine hrint (eq_top_iff.mpr ?_)
    calc (⊤ : ℝ≥0∞) = ∫⁻ _r in Ioo (r₀ / 2) r₀, ⊤ := by
          rw [setLIntegral_const, ENNReal.top_mul hpos.ne']
      _ ≤ ∫⁻ r in Ioo (r₀ / 2) r₀, (K r * ENNReal.ofReal r⁻¹) * ENNReal.ofReal (min (r ^ 2) 1) := by
          refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
          have hr0 : 0 < r := lt_trans (by linarith) hr.1
          have hKr : K r = ⊤ := top_le_iff.mp (htop ▸ hKanti hr.2.le)
          rw [hKr, ENNReal.top_mul (by simp [hr0]), ENNReal.top_mul (by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            exact lt_min (by positivity) one_pos)]
      _ ≤ _ := lintegral_mono_set (fun r hr => lt_trans (by linarith) hr.1)
  /- The profile `k = k̄/|S^{d-1}|`. -/
  have hA0 := (sphereArea_eq_toSphere (d := d) hd).2
  set A := sphereArea d with hA
  set k : ℝ → ℝ := fun r => (K r).toReal / A with hk
  have hkm : Measurable k := hKm.ennreal_toReal.div_const A
  have hknn : ∀ r, 0 ≤ k r := fun r => div_nonneg ENNReal.toReal_nonneg hA0.le
  have hkanti : AntitoneOn k (Ioi 0) := fun r hr s _ hrs =>
    div_le_div_of_nonneg_right (ENNReal.toReal_mono (hKfin r hr) (hKanti hrs)) hA0.le
  have hpt : ∀ r : ℝ, 0 < r → ENNReal.ofReal A * ENNReal.ofReal (k r / r) =
      K r * ENNReal.ofReal r⁻¹ := by
    intro r hr
    have he : A * (k r / r) = (K r).toReal * r⁻¹ := by
      simp only [hk]; field_simp
    rw [← ENNReal.ofReal_mul hA0.le, he, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hKfin r hr)]
  have hpow : ∀ r : ℝ, 0 < r → r ^ d = r ^ (d - 1) * r := fun r _ => by
    rw [← pow_succ]; congr 1; omega
  have hkdiv : ∀ r : ℝ, 0 < r → k r / r ^ d * r ^ (d - 1) = k r / r := fun r hr => by
    rw [hpow r hr]; field_simp
  have hint : (∫⁻ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (k ‖x‖ / ‖x‖ ^ d))) ≠ ⊤ := by
    have hf : Measurable fun r : ℝ => ENNReal.ofReal (min (r ^ 2) 1 * (k r / r ^ d)) :=
      ((by fun_prop : Measurable fun r : ℝ => min (r ^ 2) 1).mul
        (hkm.div (measurable_id.pow_const d))).ennreal_ofReal
    rw [lintegral_radial hd _ hf, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ne_top_of_le_ne_top hrint
      (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_))
    have hr0 : (0 : ℝ) < r := hr
    rw [← hA, ← hpt r hr0, ← ENNReal.ofReal_mul (p := min (r ^ 2) 1 * (k r / r ^ d))
      (q := r ^ (d - 1)) (by have := hknn r; positivity)]
    have he : min (r ^ 2) 1 * (k r / r ^ d) * r ^ (d - 1) = min (r ^ 2) 1 * (k r / r) := by
      rw [mul_assoc, hkdiv r hr0]
    rw [he, ENNReal.ofReal_mul (by positivity)]
    ring
  /- The mean of the Gaussian term. -/
  have hT0 : 0 ≤ T.A.trace / (d : ℝ) := by
    rw [← integral_quad_normSphere hd]
    exact integral_nonneg fun u => quad_nonneg T.A_posSemidef u
  refine ⟨T.A.trace / d, k, hT0, hkm, hknn, hkanti, hint, fun ω => ?_⟩
  set s := ‖ω‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg ω
  set e₀ : Rd d := ebasis (0 : Fin d) with he₀
  have he₀1 : ‖e₀‖ = 1 := by simp [he₀, ebasis]
  set c : ℝ → ℝ≥0∞ := fun r =>
    ∫⁻ u, ENNReal.ofReal (1 - Real.cos ⟪(s * r) • e₀, u⟫) ∂normSphere d with hc
  have hcm : Measurable c := by
    have hj : Measurable fun p : ℝ × Rd d => ENNReal.ofReal (1 - Real.cos ⟪(s * p.1) • e₀, p.2⟫) :=
      (by fun_prop : Continuous fun p : ℝ × Rd d =>
        1 - Real.cos ⟪(s * p.1) • e₀, p.2⟫).measurable.ennreal_ofReal
    exact hj.lintegral_prod_right'
  have hcrad : ∀ y : Rd d, ∀ r : ℝ, 0 ≤ r → ‖y‖ = s * r →
      ∫⁻ u, ENNReal.ofReal (1 - Real.cos ⟪y, u⟫) ∂normSphere d = c r := by
    intro y r hr hy
    refine lintegral_one_sub_cos_normSphere_radial ?_
    rw [hy, norm_smul, he₀1, mul_one, Real.norm_of_nonneg (by positivity)]
  /- The mean of the left side and of the right side. -/
  have h1 : ∀ᵐ u ∂normSphere d, ENNReal.ofReal (g (s ^ 2)) =
      ENNReal.ofReal (s ^ 2 * (quad T.A u / 2)) +
        ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪s • u, x⟫) ∂T.ν := by
    filter_upwards [ae_normSphere_norm] with u hu
    have h := hFe (s • u)
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hs0, quad_smul_vec] at h
    rw [h]
    congr 2
    ring
  have hqm : Continuous fun u : Rd d => s ^ 2 * (quad T.A u / 2) := by
    unfold quad; fun_prop
  have hqnn : ∀ u : Rd d, 0 ≤ s ^ 2 * (quad T.A u / 2) := fun u => by
    have := quad_nonneg T.A_posSemidef u; positivity
  have h2 := lintegral_congr_ae h1
  rw [lintegral_const, measure_univ, mul_one, lintegral_add_left hqm.measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_normSphere hd hqm) (ae_of_all _ hqnn),
    integral_const_mul, integral_div, integral_quad_normSphere hd] at h2
  have hswap : ∫⁻ u, ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪s • u, x⟫) ∂T.ν ∂normSphere d =
      ∫⁻ r in Ioi (0 : ℝ), (K r * ENNReal.ofReal r⁻¹) * c r := by
    have hjoint : Measurable (Function.uncurry fun (u x : Rd d) =>
        ENNReal.ofReal (1 - Real.cos ⟪s • u, x⟫)) :=
      (by fun_prop : Continuous fun p : Rd d × Rd d =>
        1 - Real.cos ⟪s • p.1, p.2⟫).measurable.ennreal_ofReal
    rw [lintegral_lintegral_swap hjoint.aemeasurable, ← hrad c hcm]
    refine lintegral_congr fun x => ?_
    have he : ∀ u : Rd d, ⟪s • u, x⟫ = ⟪s • x, u⟫ := fun u => by
      rw [real_inner_smul_left, real_inner_smul_left, real_inner_comm]
    simp_rw [he]
    exact hcrad _ _ (norm_nonneg x) (by rw [norm_smul, Real.norm_of_nonneg hs0])
  have hf : Measurable fun x : Rd d =>
      ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d)) :=
    ((by fun_prop : Measurable fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).mul
      ((hkm.comp continuous_norm.measurable).div
        (continuous_norm.measurable.pow_const d))).ennreal_ofReal
  have htarget : ∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d)) =
      ∫⁻ r in Ioi (0 : ℝ), (K r * ENNReal.ofReal r⁻¹) * c r := by
    rw [lintegral_polar hd _ hf]
    have hjoint : Measurable (Function.uncurry fun (η : Metric.sphere (0 : Rd d) 1) (r : ℝ) =>
        ENNReal.ofReal ((1 - Real.cos ⟪ω, r • (η : Rd d)⟫) *
          (k ‖r • (η : Rd d)‖ / ‖r • (η : Rd d)‖ ^ d)) * ENNReal.ofReal (r ^ (d - 1))) :=
      (hf.comp (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst))).mul
        (measurable_snd.pow_const _).ennreal_ofReal
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hstep : ∀ η : Metric.sphere (0 : Rd d) 1,
        ENNReal.ofReal ((1 - Real.cos ⟪ω, r • (η : Rd d)⟫) *
          (k ‖r • (η : Rd d)‖ / ‖r • (η : Rd d)‖ ^ d)) * ENNReal.ofReal (r ^ (d - 1)) =
        ENNReal.ofReal (1 - Real.cos ⟪r • ω, (η : Rd d)⟫) * ENNReal.ofReal (k r / r) := by
      intro η
      have hn : ‖r • (η : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr0.le]
      have hin : ⟪ω, r • (η : Rd d)⟫ = ⟪r • ω, (η : Rd d)⟫ := by
        rw [real_inner_smul_left, real_inner_smul_right]
      rw [hn, hin, ← ENNReal.ofReal_mul (mul_nonneg (hnn1 _ _) (by have := hknn r; positivity)),
        ← ENNReal.ofReal_mul (hnn1 _ _), mul_assoc, hkdiv r hr0]
    simp_rw [hstep]
    have hm1 : Measurable fun u : Rd d => ENNReal.ofReal (1 - Real.cos ⟪r • ω, u⟫) := by fun_prop
    have hm2 : Measurable fun η : Metric.sphere (0 : Rd d) 1 =>
        ENNReal.ofReal (1 - Real.cos ⟪r • ω, (η : Rd d)⟫) := hm1.comp measurable_subtype_coe
    rw [lintegral_mul_const _ hm2, lintegral_toSphere_eq hd hm1, ← hA,
      hcrad (r • ω) r hr0.le (by rw [norm_smul, Real.norm_of_nonneg hr0.le, mul_comm]),
      mul_right_comm, hpt r hr0]
  rw [htarget, ← hswap]
  refine h2.trans ?_
  congr 2
  ring

/-! ## The form of `μ_I` -/

/-- **(2), the form of `μ_I`**: a rotation-invariant, self-decomposable, infinitely divisible law
other than `δ₀` is `N(0, aI)`, `a > 0`, or `N(0, aI) * ν_I`, `a ≥ 0`, for a right-continuous
profile. Spends A3(i), A2 and, for the law of the profile, A3(iii). -/
theorem law_form (hd : 1 ≤ d) {μI : Measure (Rd d)} [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI) (hID : IsInfinitelyDivisible μI)
    (hne : μI ≠ Measure.dirac 0) :
    (∃ a : ℝ, 0 < a ∧ μI = multivariateGaussian 0 (a • (1 : Mat d))) ∨
      ∃ a : ℝ, 0 ≤ a ∧ ∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
        (∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) ∧
        μI = multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨g, -, hgnn, -, -, hg⟩ := radial_exponent μI hrot hsd hne
  obtain ⟨a, k, ha, hkm, hknn, hka, hint, hF⟩ :=
    polar_mean_form hd μI ((isSelfDecomposable_iff_sato μI).1 hsd) hID g hg
  have hreal : ∀ ω : Rd d, g (‖ω‖ ^ 2) = a * ‖ω‖ ^ 2 / 2 +
      (∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d))).toReal := by
    intro ω
    have h := hF ω
    have hfin : (∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d))) ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at h
      exact ENNReal.ofReal_ne_top h
    have h' := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_ofReal (hgnn _ (sq_nonneg _)),
      ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
      ENNReal.toReal_ofReal (by positivity)] at h'
  by_cases hk0 : ∀ r ∈ Ioi (0 : ℝ), k r = 0
  · /- `k ≡ 0`: the Gaussian law. -/
    left
    have hzero : ∀ ω : Rd d, g (‖ω‖ ^ 2) = a * ‖ω‖ ^ 2 / 2 := by
      intro ω
      have h0 : (∫⁻ x : Rd d, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * (k ‖x‖ / ‖x‖ ^ d))) = 0 := by
        rw [lintegral_eq_zero_iff' (by
          exact (Measurable.ennreal_ofReal (((by fun_prop : Measurable fun x : Rd d =>
            1 - Real.cos ⟪ω, x⟫).mul
            ((hkm.comp continuous_norm.measurable).div
              (continuous_norm.measurable.pow_const d))))).aemeasurable)]
        have hx0 : ∀ᵐ x : Rd d ∂volume, x ≠ 0 := by
          rw [ae_iff]
          simp
        filter_upwards [hx0] with x hx
        simp [hk0 ‖x‖ (norm_pos_iff.2 hx)]
      rw [hreal ω, h0, ENNReal.toReal_zero, add_zero]
    have hPa : (a • (1 : Mat d)).PosSemidef := PosSemidef.one.smul ha
    have hμ : μI = multivariateGaussian 0 (a • (1 : Mat d)) := by
      refine eq_of_charFun_eq fun ω => ?_
      rw [hg, hzero, charFun_multivariateGaussian_zero hPa, quad_smul, quad_one]
    refine ⟨a, lt_of_le_of_ne ha fun h => hne ?_, hμ⟩
    rw [hμ, ← h, zero_smul]
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_multivariateGaussian_zero PosSemidef.zero, quad_zero, charFun_dirac]
    simp
  · /- Otherwise a right-continuous profile. -/
    right
    push Not at hk0
    obtain ⟨r₀, hr₀, hkr₀⟩ := hk0
    let K : RadialProfile d :=
      { k := k
        k_nonneg := fun r _ => hknn r
        k_antitone := hka
        k_ne_zero := ⟨r₀, hr₀, hkr₀⟩
        integrable := hint }
    obtain ⟨ν, hν⟩ := (exists_profileLaw hd K.rightMod).imp fun _ h => h.1
    haveI := hν.1
    refine ⟨a, ha, K.rightMod, ν, hν, fun r hr => K.rightLimK_rightCont hr, ?_⟩
    refine eq_of_charFun_eq fun ω => ?_
    rw [hg, charFun_gaussian_conv ha, hν.2, K.rightMod_exponent hd, hreal ω, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    rw [neg_add]
    rfl

/-- **The laws of `𝔉(C)` have the form of `law_form`**: restricted to the rays, the family makes
`μ_I` rotation invariant, self-decomposable and not `δ₀`, and the chain `s ↦ sI` makes it infinitely
divisible. Spends A6, A3(i), A2 and A3(iii). -/
theorem law_form_of_mem_coneLaws (hd : 1 ≤ d) {C : Set (Mat d)} {m : Measure (Rd d)}
    (hm : m ∈ coneLaws C) :
    (∃ a : ℝ, 0 < a ∧ m = multivariateGaussian 0 (a • (1 : Mat d))) ∨
      ∃ a : ℝ, 0 ≤ a ∧ ∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
        (∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) ∧
        m = multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨μ, hμ, rfl⟩ := hm
  obtain ⟨hp, hrot, hsd, hne, -⟩ :=
    gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ
  haveI := hp
  have hμr : IsGWCascadeFamily (glSet d) rayLE μ :=
    gw_family_restrict_of_le subset_rfl (fun S S' _ _ h => causalPlusLE_of_rayLE h) μ hμ
  have hW : IsWedgeDatum (glSet d) rayLE :=
    isWedgeDatum_ray glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  have hpo : IsPartialOrderOn (psdSet d) rayLE :=
    ⟨fun S hS => hW.refl S hS, fun S hS S' hS' h h' => hW.antisymm S S' hS hS' h h',
      fun S hS S' hS' S'' hS'' h h' => hW.trans S S' S'' hS hS' hS'' h h'⟩
  have hID : IsInfinitelyDivisible (μ 0 1) :=
    chain_infinitelyDivisible hd (psdSet d) subset_rfl rayLE hpo μ
      (fun S hS S' hS' h => hμr.isProbability (S, S') ⟨hS, hS', h⟩) (fun S hS => hμr.diag S hS)
      (fun S hS S' hS' S'' hS'' h h' => hμr.cascade S S' S'' hS hS' hS'' h h')
      (fun ω => hμr.continuous ω) 0 1 _ (chain_ray_zero 1 PosSemidef.one)
  exact law_form hd hrot hsd hID hne

/-! ## The Gaussian laws in `𝔉(C)` -/

/-- **`N(0, aI) ∈ 𝔉(C)`** for `a > 0` and `C ⊆ PSD(d)`: it is the law at `I` of the affine Gaussian
scale space with constant `a/2`, restricted to the pairs of `≼⁺_C`, which are Loewner pairs. -/
theorem gaussian_mem_coneLaws (hd : 2 ≤ d) {C : Set (Mat d)} (hpsd : C ⊆ psdSet d) {a : ℝ}
    (ha : 0 < a) : multivariateGaussian 0 (a • (1 : Mat d)) ∈ coneLaws C := by
  have hν : IsAffineCascadeFamily (affineGaussian (d := d) (a / 2)) :=
    (affine_rigidity hd _).2 ⟨a / 2, by positivity, fun _ _ => rfl⟩
  refine ⟨affineGaussian (a / 2), gw_family_restrict_of_le subset_rfl
    (fun S S' _ hS' h => causalPlusLE_loewner hpsd hS' h) _ hν, ?_⟩
  rw [affineGaussian, sub_zero, mul_div_cancel₀ _ two_ne_zero]

/-! ## `prop:wedge-axis-profiles`(2) -/

/-- **`prop:wedge-axis-profiles`(2)**, the whole cell: for `0 < α < ∞`, `𝔉_α` consists of the laws
`N(0, aI)`, `a > 0`, and the laws `N(0, aI) * ν_I`, `a ≥ 0`, of the right-continuous profiles `k`
with `β₋(k) ≥ α`; for `α ≥ 2` there is no such profile (`wedge_axis_cell_gaussian`). Spends A6,
A3(i)–(iii) and A2; not A4, not A5. -/
theorem wedge_axis_cell (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) :
    rowLaws d (α : WithTop ℝ) = {m : Measure (Rd d) |
      (∃ a : ℝ, 0 < a ∧ m = multivariateGaussian 0 (a • (1 : Mat d))) ∨
        ∃ a : ℝ, 0 ≤ a ∧ ∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
          (∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) ∧ α ≤ lowerExp K.k ∧
          m = multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν} := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 hα0.le
  have hidx := coneIndex_stableGenCone hd hα0.le
  have hprof := fun (K : RadialProfile d) (ν : Measure (Rd d)) (hν : IsProfileLaw K ν) {a : ℝ}
      (ha : 0 ≤ a) => wedge_axis_profiles hd hCsym hC hO hI hpt (fun X hX => hX.1)
    (stableGenCone_det_ne_zero hd1 hα0.le) (by rwa [hidx]) K ν hν ha
  rw [rowLaws_coe_eq_coneLaws]
  ext m
  constructor
  · intro hm
    rcases law_form_of_mem_coneLaws hd1 hm with h | ⟨a, ha, K, ν, hν, hrc, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, ha, K, ν, hν, hrc, ?_, rfl⟩
      rw [← hidx]
      exact (hprof K ν hν ha).1 hm
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, K, ν, hν, -, hle, rfl⟩)
    · exact gaussian_mem_coneLaws hd (fun X hX => hX.1) ha
    · exact (hprof K ν hν ha).2 (by rwa [hidx])

/-- **`prop:wedge-axis-profiles`(2)**, from `α = 2` on: no profile has `β₋(k) ≥ α`, as `β₋(k) < 2`,
so `𝔉_α` is the set of the laws `N(0, aI)`, `a > 0`. This is the set of laws of
`thm:wedge-axis`(3)(d) for finite `α`, here without A5 (`wedge_axis_row` spends it). -/
theorem wedge_axis_cell_gaussian (hd : 2 ≤ d) {α : ℝ} (hα2 : 2 ≤ α) :
    rowLaws d (α : WithTop ℝ) = {m : Measure (Rd d) |
      ∃ a : ℝ, 0 < a ∧ m = multivariateGaussian 0 (a • (1 : Mat d))} := by
  have hd1 : 1 ≤ d := by omega
  rw [wedge_axis_cell hd (by linarith : (0 : ℝ) < α)]
  ext m
  constructor
  · rintro (h | ⟨a, -, K, ν, -, -, hle, -⟩)
    · exact h
    · have hlt : lowerExp K.k < 2 := (dilRatio_exponents hd1 K).2.2.2.2.2.1
      exact absurd hle (not_le.2 (hlt.trans_le hα2))
  · exact Or.inl

/-- **`prop:wedge-axis-profiles`(2)**, the cones: for a cone `C` of the case (2)(c) of
`thm:wedge-axis`, `𝔉(C) = 𝔉_{β(C)}`: the laws `μ_I` of the families along `≼⁺_C` depend on `C` only
through `β(C)`. Spends A6, A3(i)–(iii) and A2; not A4, not A5. -/
theorem wedge_axis_cone_laws (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) :
    coneLaws C = rowLaws d (coneIndex C : WithTop ℝ) := by
  have hd1 : 1 ≤ d := by omega
  have hidx := wedge_axis_index hd hCsym hC hO hI hpt hpsd hdef
  have hsub : C ⊆ stableGenCone d (coneIndex C) := hidx.2.2.2.1.2
  rw [rowLaws_coe_eq_coneLaws]
  rcases hidx.2.2.1.eq_or_lt with h0 | hβ0
  · /- `β(C) = 0`: then `C = C_0`. -/
    have hC0 : C = stableGenCone d 0 := by
      refine subset_antisymm (h0 ▸ hsub) fun X hX => ?_
      rw [(stable_order_zero hd1).1] at hX
      obtain ⟨c, hc, rfl⟩ := hX
      exact hC.2.2.2 c hc 1 hI
    rw [← h0, ← hC0]
  · obtain ⟨hCsym', hO', hC', hI', hpt'⟩ := stableGenCone_props hd1 hβ0.le
    have hidx' := coneIndex_stableGenCone hd hβ0.le
    ext m
    constructor
    · intro hm
      rcases law_form_of_mem_coneLaws hd1 hm with ⟨a, ha, rfl⟩ | ⟨a, ha, K, ν, hν, -, rfl⟩
      · exact gaussian_mem_coneLaws hd (fun X hX => hX.1) ha
      · have hle := (wedge_axis_profiles hd hCsym hC hO hI hpt hpsd hdef hβ0 K ν hν ha).1 hm
        exact (wedge_axis_profiles hd hCsym' hC' hO' hI' hpt' (fun X hX => hX.1)
          (stableGenCone_det_ne_zero hd1 hβ0.le) (by rwa [hidx']) K ν hν ha).2 (by rwa [hidx'])
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, gw_family_restrict_of_le subset_rfl
        (fun S S' _ _ h => causalPlusLE_mono hsub h) μ hμ, rfl⟩

/-- **`prop:wedge-axis-profiles`(2)**, the cones from `β(C) = 2` on: `𝔉(C)` is the set of the laws
`N(0, aI)`, `a > 0`. This is the set of laws of the last sentence of `thm:wedge-axis`(2)(c), here
without A5. The family of each is then the end of that theorem's (2)(b), which spends nothing;
`wedge_axis_non_gaussian` states it, on its own route through A5. -/
theorem wedge_axis_cone_laws_gaussian (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) (hβ2 : 2 ≤ coneIndex C) :
    coneLaws C = {m : Measure (Rd d) |
      ∃ a : ℝ, 0 < a ∧ m = multivariateGaussian 0 (a • (1 : Mat d))} := by
  rw [wedge_axis_cone_laws hd hCsym hC hO hI hpt hpsd hdef, wedge_axis_cell_gaussian hd hβ2]

end AffineHemigroup
