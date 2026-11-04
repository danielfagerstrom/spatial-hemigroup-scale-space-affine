/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityIndexZero

/-!
# `prop:similarity-line-family`: a part laid along lines

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-line-family`. Wave 2,
group I (Q-0281).

(1) `L_Σ` is a symmetric Lévy measure with its defining identity, its polar form for `Σ ∈ PD(d)`,
similarity covariance and Loewner monotonicity (`line_family_levy`, spends nothing); the laws
`N(0, 2bΣ) * ν_Σ` have infinitely divisible increments forming a family with (K1), (K2), (K4) and
(K3) for every similarity (`line_family_cascade`, A3(iii)). (2) `es(ψ_Σ) ≤ 4d(d+2)`,
`cond 𝓜_s(L_Σ) ≤ d+2`, `rs(L_{Σ_ε}) → ∞`, and the rank-one limit is at least the polar image of
`2k(s/|u₁|)` and charges every open cone (`line_family_functionals`, spends nothing). (3) `L_Σ`
(`line_family_levy_not_shape_blind`, spends nothing) and `ν_Σ` (`line_family_not_shape_blind`,
A3(ii)–(iii)) are not rotation invariant unless `Σ` is a multiple of `I`.

## Routes

* **`ℓ` on `(0,∞)`.** `∫ g dℓ = ∫_0^∞ (g(r) + g(-r)) k(r) dr/r` (`lintegral_lineProfile`), and
  `∫ g(r√q) ℓ(dr) = ∫_0^∞ (g(s) + g(-s)) k(s/√q) ds/s` by `s = r√q` (`lintegral_lineProfile_scale`,
  through `Real.map_volume_mul_left`). `k` is not assumed measurable: it is read through
  `(0,∞).indicator k`, measurable as an antitone function, wherever a joint measurability is needed.
* **The moments of `σ̄`** (`integral_inner_sq`, `integral_fourth_moments`,
  `integral_inner_sq_mul_inner_sq`) from rotation invariance alone, in place of the blueprint's
  Gaussian computation: coordinate swaps and sign changes, `∑ u_j² = 1`, and a reflection taking `e₁`
  to `(e₁ + e₂)/√2`, which gives `∫ u₁⁴ = 3 ∫ u₁²u₂²`.
* **Clause (2), the exponent and the moments, without the sandwich.** With `t := λ_max(Σ)` and `v` a
  unit eigenvector, `t⟨v,u⟩² ≤ q_Σ(u) ≤ t` on the sphere (`quad_ge_top`); `ψ_Σ(Rω) ≤ ψ_ℓ(√t|ω|)` and
  `ψ_Σ(ω) ≥ ψ_ℓ(√t|ω|)/(4d(d+2))` by `ψ_ℓ(aτ) ≥ (a²/4)ψ_ℓ(τ)`; likewise
  `G_s(t)|x|²/(d(d+2)) ≤ ⟨x, 𝓜_s x⟩ ≤ G_s(t)|x|²/d`. No law and no rank-one limit is read, so the
  clause spends nothing.
* **The rotational spread** through two fixed caps exchanged by the swap of the first two coordinates,
  their size chosen from the decay `k(r) → 0` at `∞` (`lineProfile_eventually_lt`).
* **The rank-one limit**: the polar image of `2k(s/|u₁|)` lies below every `L_{Σ_ε}`, `ε ∈ (0,1]`
  (`q_{Σ_ε}(u) ≥ u₁²`), so below `L_*` on sets bounded away from `0`; an open cone contains a sector
  whose `L_{Σ_ε}`-mass is bounded below uniformly in `ε` (`lineLevy_sector_ge`).
* **Clause (3)**: the open set `U = {q_Σ > m', q_Σ ∘ R < m''}`, `R` the reflection exchanging unit
  eigenvectors of `λ_min` and `λ_max`, is symmetric; rotation invariance gives, sector by sector,
  `∫_a^b k(s/√m') ds/s ≤ ∫_a^b k(s/√m'') ds/s`, so `k(s/√m') = k(s/√m'')` a.e.; iterating at
  almost-every points gives `k ≥ k(r₀) > 0` on `(0,∞)` against `∫_1^∞ k dr/r < ∞`
  (`lineProfile_dilation_contra`), in place of the blueprint's right limits.
* **The increments** (`exists_levy_sub`): the Lévy measure `D` with `D + L_Σ = L_{Σ'}`, built on the
  disjointed shells `{|x| > 1/(n+1)}`, where both are finite, and symmetrized; A3(iii) gives the law
  with triplet `(2b(Σ' - Σ), D, 0)`. The family is `simCascade_of_exponent`, generic in the exponent
  (also read by `prop:similarity-degenerate-family`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The profile on the line -/

/-- The weight `r ↦ k(|r|)/|r|` of `ℓ` is measurable when `k` is antitone on `(0,∞)`. -/
theorem measurable_lineWeight {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) :
    Measurable fun r : ℝ => ENNReal.ofReal (k |r| / |r|) := by
  have hm := measurable_indicator_Ioi_of_antitoneOn hk
  have heq : (fun r : ℝ => ENNReal.ofReal (k |r| / |r|)) =
      fun r : ℝ => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator k |r| / |r|) := by
    funext r
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · rw [indicator_of_mem (show |r| ∈ Ioi (0 : ℝ) from abs_pos.2 hr)]
  rw [heq]
  exact ((hm.comp measurable_abs).div measurable_abs).ennreal_ofReal

/-- **`ℓ` in polar form**: `∫ g dℓ = ∫_0^∞ (g(r) + g(-r)) k(r)/r dr`. -/
theorem lintegral_lineProfile {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ r, g r ∂(lineProfileMeasure k) =
      ∫⁻ r in Ioi (0 : ℝ), (g r + g (-r)) * ENNReal.ofReal (k r / r) := by
  set w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (k |r| / |r|) with hw
  have hwm : Measurable w := measurable_lineWeight hk
  rw [lineProfileMeasure, lintegral_withDensity_eq_lintegral_mul _ hwm hg]
  have hsplit : ({0}ᶜ : Set ℝ) = Iio 0 ∪ Ioi 0 := by
    ext r
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Iio, mem_Ioi]
    exact ne_iff_lt_or_gt
  rw [hsplit, lintegral_union measurableSet_Ioi (Iio_disjoint_Ioi_of_le le_rfl)]
  have hneg : ∫⁻ r in Iio (0 : ℝ), (w * g) r = ∫⁻ r in Ioi (0 : ℝ), (w * g) (-r) := by
    rw [← lintegral_indicator measurableSet_Iio, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_neg_eq_self]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr, indicator_of_mem (show -r ∈ Iio (0 : ℝ) from neg_lt_zero.2 (show 0 < r from hr))]
    · rw [indicator_of_notMem hr, indicator_of_notMem]
      simp only [mem_Iio, Left.neg_neg_iff]
      exact hr
  rw [hneg, add_comm, ← lintegral_add_left (f := w * g) (hwm.mul hg)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 < r := hr
  simp only [Pi.mul_apply, hw, abs_neg, abs_of_pos hr0]
  ring

/-- **`ℓ` scaled by `√q`**: for `q > 0`, `∫ g(r√q) ℓ(dr) = ∫_0^∞ (g(s) + g(-s)) k(s/√q)/s ds`. -/
theorem lintegral_lineProfile_scale {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {q : ℝ} (hq : 0 < q)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r, g (r * Real.sqrt q) ∂(lineProfileMeasure k) =
      ∫⁻ s in Ioi (0 : ℝ), (g s + g (-s)) * ENNReal.ofReal (k (s / Real.sqrt q) / s) := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [lintegral_lineProfile hk (g := fun r => g (r * Real.sqrt q))
    (hg.comp (measurable_id.mul_const _))]
  set H : ℝ → ℝ≥0∞ := fun s =>
    (g s + g (-s)) * ENNReal.ofReal (Real.sqrt q * k (s / Real.sqrt q) / s) with hH
  have h1 : ∀ r ∈ Ioi (0 : ℝ), (g (r * Real.sqrt q) + g (-r * Real.sqrt q)) *
      ENNReal.ofReal (k r / r) = H (Real.sqrt q * r) := by
    intro r hr
    have hr0 : 0 < r := hr
    simp only [hH]
    rw [neg_mul, mul_comm r, mul_div_cancel_left₀ _ hsq.ne']
    congr 2
    field_simp
  -- the substitution `s = √q r`: the shared library's `setLIntegral_Ioi_comp_mul`, solved for
  -- `∫_0^∞ H(√q r) dr`
  have hsub : ∫⁻ r in Ioi (0 : ℝ), H (Real.sqrt q * r)
      = ENNReal.ofReal (Real.sqrt q)⁻¹ * ∫⁻ s in Ioi (0 : ℝ), H s := by
    rw [ScaleSpace.setLIntegral_Ioi_comp_mul hsq H, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_pos.2 hsq).le, inv_mul_cancel₀ hsq.ne', ENNReal.ofReal_one, one_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, hsub,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  simp only [hH]
  rw [mul_left_comm, ← ENNReal.ofReal_mul (inv_pos.2 hsq).le]
  congr 2
  field_simp

/-! ## The normalised surface measure `σ̄` -/

theorem normSphere_univ (hd : 1 ≤ d) : normSphere d univ = 1 := by
  have hA := sphereArea_eq_toSphere hd
  rw [normSphere_apply hd MeasurableSet.univ, preimage_univ, ← hA.1,
    ENNReal.inv_mul_cancel (by simp [hA.2]) ENNReal.ofReal_ne_top]

theorem isProbabilityMeasure_normSphere (hd : 1 ≤ d) : IsProbabilityMeasure (normSphere d) :=
  ⟨normSphere_univ hd⟩

/-- `σ̄` is carried by the unit sphere. -/
theorem ae_normSphere_norm : ∀ᵐ u ∂normSphere d, ‖u‖ = 1 := by
  rw [normSphere]
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)]
  exact ae_of_all _ fun η => norm_eq_of_mem_sphere η

/-- **`σ̄` is invariant under linear isometries.** -/
theorem normSphere_map_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : (normSphere d).map Q = normSphere d := by
  rw [normSphere, Measure.map_smul, Measure.map_map Q.continuous.measurable measurable_subtype_coe]
  have h : ((Q : Rd d → Rd d) ∘ Subtype.val : Metric.sphere (0 : Rd d) 1 → Rd d) =
      Subtype.val ∘ sphereMap Q := by
    funext η; rfl
  rw [h, ← Measure.map_map measurable_subtype_coe (measurable_sphereMap Q), toSphere_map_isometry]

theorem lintegral_normSphere_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) {f : Rd d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f (Q u) ∂normSphere d = ∫⁻ u, f u ∂normSphere d := by
  conv_rhs => rw [← normSphere_map_isometry Q]
  rw [lintegral_map hf Q.continuous.measurable]

theorem integral_normSphere_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (f : Rd d → ℝ) :
    ∫ u, f (Q u) ∂normSphere d = ∫ u, f u ∂normSphere d := by
  conv_rhs => rw [← normSphere_map_isometry Q]
  exact (integral_map_equiv Q.toHomeomorph.toMeasurableEquiv f).symm

/-- **The linear isometry of an orthogonal matrix.** -/
noncomputable def orthIsometry {Q : Mat d} (hQ : Q ∈ orthSet d) : Rd d ≃ₗᵢ[ℝ] Rd d :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (lin Q : Rd d →L[ℝ] Rd d).toLinearMap
      norm_map' := norm_lin_of_orth hQ } rfl

@[simp] theorem orthIsometry_apply {Q : Mat d} (hQ : Q ∈ orthSet d) (x : Rd d) :
    orthIsometry hQ x = lin Q x := rfl

theorem lintegral_normSphere_orth {Q : Mat d} (hQ : Q ∈ orthSet d) {f : Rd d → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ u, f (lin Q u) ∂normSphere d = ∫⁻ u, f u ∂normSphere d :=
  lintegral_normSphere_isometry (orthIsometry hQ) hf

theorem normSphere_map_orth {Q : Mat d} (hQ : Q ∈ orthSet d) :
    (normSphere d).map (lin Q) = normSphere d :=
  normSphere_map_isometry (orthIsometry hQ)

/-- **`σ̄` charges every open set meeting the sphere.** -/
theorem normSphere_pos_of_isOpen (hd : 1 ≤ d) {V : Set (Rd d)} (hV : IsOpen V) {u₀ : Rd d}
    (hu₀ : ‖u₀‖ = 1) (hu₀V : u₀ ∈ V) : 0 < normSphere d V := by
  rw [normSphere_apply hd hV.measurableSet]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) ?_
  rw [Measure.toSphere_apply' _ (measurable_subtype_coe hV.measurableSet)]
  refine mul_ne_zero ?_ ?_
  · rw [finrank_Rd]; exact Nat.cast_ne_zero.2 (by omega)
  set W : Set (Rd d) := {x | 0 < ‖x‖ ∧ ‖x‖ < 1} ∩ (fun x : Rd d => ‖x‖⁻¹ • x) ⁻¹' V with hW
  have hWo : IsOpen W := by
    refine ContinuousOn.isOpen_inter_preimage ?_
      ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
      hV
    exact (continuous_norm.continuousOn.inv₀ fun x hx => hx.1.ne').smul continuousOn_id
  have hWne : ((1 / 2 : ℝ) • u₀) ∈ W := by
    have hn : ‖(1 / 2 : ℝ) • u₀‖ = 1 / 2 := by rw [norm_smul, hu₀]; norm_num
    refine ⟨⟨by rw [hn]; norm_num, by rw [hn]; norm_num⟩, ?_⟩
    simp only [mem_preimage]
    rw [hn, smul_smul]
    norm_num
    exact hu₀V
  refine ne_of_gt (lt_of_lt_of_le (hWo.measure_pos volume ⟨_, hWne⟩) (measure_mono ?_))
  intro x hx
  have hx0 : 0 < ‖x‖ := hx.1.1
  have hx1 : ‖x‖ < 1 := hx.1.2
  have hxs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Rd d) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
  refine ⟨‖x‖, ⟨hx0, hx1⟩, ‖x‖⁻¹ • x, ⟨⟨_, hxs⟩, hx.2, rfl⟩, ?_⟩
  simp only
  rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]

/-- **A coordinate hyperplane is `σ̄`-null.** -/
theorem normSphere_coord_null (hd : 1 ≤ d) (i : Fin d) : normSphere d {u | u i = 0} = 0 := by
  have hmeas : MeasurableSet {u : Rd d | u i = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [normSphere_apply hd hmeas]
  have he : (ebasis i : Rd d) ≠ 0 := by
    intro h
    have := congrArg (fun x : Rd d => x i) h
    simp [ebasis] at this
  have h0 := toSphere_inner_eq_zero he
  have hset : (Subtype.val ⁻¹' {u : Rd d | u i = 0} : Set (Metric.sphere (0 : Rd d) 1)) =
      {η : Metric.sphere (0 : Rd d) 1 | ⟪ebasis i, (η : Rd d)⟫ = 0} := by
    ext η
    simp [ebasis, EuclideanSpace.inner_single_left]
  rw [hset, h0, mul_zero]

/-! ## The second and fourth moments of `σ̄` -/

theorem integrable_normSphere (hd : 1 ≤ d) {f : Rd d → ℝ} (hf : Continuous f) :
    Integrable f (normSphere d) := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Rd d) 1).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_normSphere_norm] with u hu
  exact hC u (mem_sphere_zero_iff_norm.2 hu)

/-- The sign change of the `j`-th coordinate, as a linear isometry. -/
noncomputable def flipIso (j : Fin d) : Rd d ≃ₗᵢ[ℝ] Rd d := orthIsometry (signFlipMat_mem j)

theorem flipIso_apply (j : Fin d) (u : Rd d) (i : Fin d) :
    flipIso j u i = if i = j then -u i else u i := by
  rw [flipIso, orthIsometry_apply, signFlipMat, lin_diagonal_apply]
  split_ifs <;> ring

/-- The exchange of two coordinates, as a linear isometry. -/
noncomputable def swapIso (i j : Fin d) : Rd d ≃ₗᵢ[ℝ] Rd d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem swapIso_apply (i j : Fin d) (u : Rd d) (k : Fin d) :
    swapIso i j u k = u (Equiv.swap i j k) := by
  simp [swapIso, Equiv.piCongrLeft'_apply, Equiv.symm_swap]

/-- An integrand odd in one coordinate integrates to `0` against `σ̄`. -/
theorem integral_normSphere_eq_zero_of_odd (j : Fin d) {f : Rd d → ℝ}
    (hf : ∀ u, f (flipIso j u) = -f u) : ∫ u, f u ∂normSphere d = 0 := by
  have h := integral_normSphere_isometry (flipIso j) f
  simp_rw [hf, integral_neg] at h
  linarith

theorem integral_coord_sq (hd : 1 ≤ d) (i : Fin d) : ∫ u, u i ^ 2 ∂normSphere d = 1 / d := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  have hall : ∀ k : Fin d, ∫ u, u k ^ 2 ∂normSphere d = ∫ u, u 0 ^ 2 ∂normSphere d := by
    intro k
    rw [← integral_normSphere_isometry (swapIso 0 k)]
    simp_rw [swapIso_apply, Equiv.swap_apply_right]
  have hsum : ∑ k : Fin d, ∫ u, u k ^ 2 ∂normSphere d = 1 := by
    rw [← integral_finsetSum _ fun k _ => integrable_normSphere hd (by fun_prop)]
    have h1 : ∫ u, ∑ k : Fin d, u k ^ 2 ∂normSphere d = ∫ _u, (1 : ℝ) ∂normSphere d := by
      refine integral_congr_ae ?_
      filter_upwards [ae_normSphere_norm] with u hu
      have := EuclideanSpace.norm_sq_eq u
      simp only [Real.norm_eq_abs, sq_abs] at this
      rw [← this, hu, one_pow]
    rw [h1, integral_const, smul_eq_mul, mul_one, probReal_univ]
  simp_rw [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hall i]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  linarith

/-- **The second moments of `σ̄`**: `∫ ⟨x,u⟩² σ̄(du) = |x|²/d`. -/
theorem integral_inner_sq (hd : 1 ≤ d) (x : Rd d) :
    ∫ u, ⟪x, u⟫ ^ 2 ∂normSphere d = ‖x‖ ^ 2 / d := by
  have hexp : ∀ u : Rd d, ⟪x, u⟫ ^ 2 = ∑ i, ∑ j, x i * x j * (u i * u j) := by
    intro u
    rw [inner_eq_sum, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_normSphere hd (by fun_prop)]
  have hij : ∀ i j : Fin d, ∫ u, x i * x j * (u i * u j) ∂normSphere d =
      if i = j then x i ^ 2 * (1 / d) else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [integral_const_mul, ← integral_coord_sq hd i]
      congr 1
      · ring
      · congr 1; funext u; ring
    · refine integral_normSphere_eq_zero_of_odd i fun u => ?_
      rw [flipIso_apply, flipIso_apply, if_pos rfl, if_neg (Ne.symm h)]
      ring
  simp_rw [fun i => integral_finsetSum (μ := normSphere d) (Finset.univ : Finset (Fin d))
    (f := fun j u => x i * x j * (u i * u j))
    (fun j _ => integrable_normSphere hd (by fun_prop)), hij, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_mul, div_eq_mul_one_div]
  simp [Real.norm_eq_abs, sq_abs, div_eq_mul_inv]

theorem inner_ebasis_left (i : Fin d) (x : Rd d) : ⟪ebasis i, x⟫ = x i := by
  simp [ebasis, EuclideanSpace.inner_single_left]

/-- `⟨eᵢ, Meⱼ⟩ = Mᵢⱼ`. -/
theorem inner_ebasis_lin (M : Mat d) (i j : Fin d) : ⟪ebasis i, lin M (ebasis j)⟫ = M i j := by
  rw [inner_ebasis_left, lin_apply_coord]
  simp [ebasis]

/-- `∫ u₁² u_j² σ̄(du)` does not depend on `j ≠ 1` (indices from `0` in Lean). -/
theorem integral_sq_mul_sq_eq (hd : 2 ≤ d) [NeZero d] (j : Fin d) (hj : j ≠ 0) :
    ∫ u, u 0 ^ 2 * u j ^ 2 ∂normSphere d =
      ∫ u, u 0 ^ 2 * u ⟨1, by omega⟩ ^ 2 ∂normSphere d := by
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [i1] at this
  rw [← integral_normSphere_isometry (swapIso i1 j) (fun u => u 0 ^ 2 * u i1 ^ 2)]
  simp_rw [swapIso_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm h10) (Ne.symm hj)]

/-- **The fourth moments of `σ̄`**: `∫ u₁⁴ = 3/(d(d+2))`, `∫ u₁²u_j² = 1/(d(d+2))` for `j ≠ 1`
(indices from `0` in Lean). Rotation invariance alone: a rotation by `π/4` in the plane of
`e₁, e₂` gives `∫ u₁⁴ = 3∫ u₁²u₂²`, and `∑_j u_j² = 1` gives the rest. -/
theorem integral_fourth_moments (hd : 2 ≤ d) [NeZero d] :
    ∫ u, u 0 ^ 4 ∂normSphere d = 3 / (d * (d + 2)) ∧
      ∀ j : Fin d, j ≠ 0 → ∫ u, u 0 ^ 2 * u j ^ 2 ∂normSphere d = 1 / (d * (d + 2)) := by
  have hd1 : 1 ≤ d := by omega
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h10 : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [i1] at this
  set a := ∫ u, u 0 ^ 4 ∂normSphere d with ha
  set b := ∫ u, u 0 ^ 2 * u i1 ^ 2 ∂normSphere d with hb
  have hI : ∀ f : Rd d → ℝ, Continuous f → Integrable f (normSphere d) :=
    fun f hf => integrable_normSphere hd1 hf
  /- `∫ u₂⁴ = ∫ u₁⁴`. -/
  have ha1 : ∫ u, u i1 ^ 4 ∂normSphere d = a := by
    rw [ha, ← integral_normSphere_isometry (swapIso 0 i1) (fun u => u 0 ^ 4)]
    simp_rw [swapIso_apply, Equiv.swap_apply_left]
  /- The rotation by `π/4`: `a = (2a + 6b)/4`. -/
  have hrot : a = 3 * b := by
    set e0 : Rd d := ebasis 0
    set e1 : Rd d := ebasis i1
    set w : Rd d := (Real.sqrt 2)⁻¹ • (e0 + e1) with hw
    have he0 : ‖e0‖ = 1 := by simp [e0, ebasis]
    have he1 : ‖e1‖ = 1 := by simp [e1, ebasis]
    have h01 : ⟪e0, e1⟫ = 0 := by
      rw [inner_ebasis_left]; simp [e1, ebasis, Ne.symm h10]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2p : 0 < Real.sqrt 2 := by positivity
    have hwn : ‖w‖ = 1 := by
      have h2 : ‖e0 + e1‖ ^ 2 = 2 := by
        rw [norm_add_sq_real, he0, he1, h01]; norm_num
      have h3 : ‖e0 + e1‖ = Real.sqrt 2 := by
        rw [← Real.sqrt_sq (norm_nonneg _), h2]
      rw [hw, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs2p, h3, inv_mul_cancel₀ hs2p.ne']
    set R := (ℝ ∙ (e0 - w))ᗮ.reflection with hR
    have hRe : R e0 = w := Submodule.reflection_sub (he0.trans hwn.symm)
    have hcoord : ∀ u : Rd d, R u 0 = (Real.sqrt 2)⁻¹ * (u 0 + u i1) := by
      intro u
      rw [← inner_ebasis_left, show (ebasis 0 : Rd d) = e0 from rfl]
      rw [show ⟪e0, R u⟫ = ⟪R e0, u⟫ from by
        rw [← R.inner_map_map e0 (R u), hR, Submodule.reflection_reflection]]
      rw [hRe, hw, real_inner_smul_left, inner_add_left, inner_ebasis_left, inner_ebasis_left]
    have h1 := integral_normSphere_isometry R (fun u => u 0 ^ 4)
    simp only [hcoord] at h1
    have hpow : ∀ u : Rd d, ((Real.sqrt 2)⁻¹ * (u 0 + u i1)) ^ 4 =
        (1 / 4) * ((u 0 ^ 4 + u i1 ^ 4 + 6 * (u 0 ^ 2 * u i1 ^ 2)) +
          (4 * (u 0 ^ 3 * u i1) + 4 * (u 0 * u i1 ^ 3))) := by
      intro u
      have : (Real.sqrt 2)⁻¹ ^ 4 = 1 / 4 := by
        rw [inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]; norm_num
      rw [mul_pow, this]
      ring
    simp_rw [hpow] at h1
    rw [integral_const_mul, integral_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
      integral_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
      integral_add (hI _ (by fun_prop)) (hI _ (by fun_prop)), integral_const_mul,
      ha1] at h1
    have hodd : ∫ u, 4 * (u 0 ^ 3 * u i1) + 4 * (u 0 * u i1 ^ 3) ∂normSphere d = 0 := by
      refine integral_normSphere_eq_zero_of_odd 0 fun u => ?_
      rw [flipIso_apply, flipIso_apply, if_pos rfl, if_neg h10]
      ring
    rw [hodd] at h1
    linarith
  /- `a + (d-1)b = 1/d`. -/
  have hsum : a + ((d : ℝ) - 1) * b = 1 / d := by
    have h1 : ∫ u, ∑ j : Fin d, u 0 ^ 2 * u j ^ 2 ∂normSphere d = 1 / d := by
      rw [← integral_coord_sq hd1 0]
      refine integral_congr_ae ?_
      filter_upwards [ae_normSphere_norm] with u hu
      have := EuclideanSpace.norm_sq_eq u
      simp only [Real.norm_eq_abs, sq_abs] at this
      rw [← Finset.mul_sum, ← this, hu]
      ring
    rw [integral_finsetSum _ fun j _ => hI _ (by fun_prop)] at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at h1
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin d)).erase 0,
        ∫ u, u 0 ^ 2 * u j ^ 2 ∂normSphere d = b :=
      fun j hj => integral_sq_mul_sq_eq hd j (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h3 : ∫ u, u 0 ^ 2 * u 0 ^ 2 ∂normSphere d = a := by
      rw [ha]; congr 1; funext u; ring
    rw [h3] at h1
    rw [← h1, Nat.cast_sub hd1, Nat.cast_one]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hb' : b = 1 / (d * (d + 2)) := by
    rw [hrot] at hsum
    have h4 : b * ((d : ℝ) + 2) = 1 / d := by linear_combination hsum
    calc b = (b * ((d : ℝ) + 2)) / ((d : ℝ) + 2) := by field_simp
      _ = 1 / (d * (d + 2)) := by rw [h4, div_div]
  refine ⟨by rw [hrot, hb']; ring, fun j hj => ?_⟩
  rw [integral_sq_mul_sq_eq hd j hj]
  exact hb'

/-- **The mixed fourth moments of `σ̄`**: for a unit `v`,
`∫ ⟨v,u⟩²⟨x,u⟩² σ̄(du) = (|x|² + 2⟨v,x⟩²)/(d(d+2))`. -/
theorem integral_inner_sq_mul_inner_sq (hd : 2 ≤ d) {v : Rd d} (hv : ‖v‖ = 1) (x : Rd d) :
    ∫ u, ⟪v, u⟫ ^ 2 * ⟪x, u⟫ ^ 2 ∂normSphere d =
      (‖x‖ ^ 2 + 2 * ⟪v, x⟫ ^ 2) / (d * (d + 2)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha, hb⟩ := integral_fourth_moments (d := d) hd
  /- The case `v = e₁`. -/
  have hcase : ∀ y : Rd d, ∫ u, u 0 ^ 2 * ⟪y, u⟫ ^ 2 ∂normSphere d =
      (‖y‖ ^ 2 + 2 * y 0 ^ 2) / (d * (d + 2)) := by
    intro y
    have hexp : ∀ u : Rd d, u 0 ^ 2 * ⟪y, u⟫ ^ 2 =
        ∑ i, ∑ j, y i * y j * (u 0 ^ 2 * (u i * u j)) := by
      intro u
      rw [inner_eq_sum, sq (∑ i, y i * u i), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hexp]
    have hI : ∀ i j : Fin d, Integrable (fun u : Rd d => y i * y j * (u 0 ^ 2 * (u i * u j)))
        (normSphere d) := fun i j => integrable_normSphere hd1 (by fun_prop)
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    have hij : ∀ i j : Fin d, ∫ u, y i * y j * (u 0 ^ 2 * (u i * u j)) ∂normSphere d =
        if i = j then y i ^ 2 * (if i = 0 then (3 : ℝ) / ((d : ℝ) * (d + 2))
          else (1 : ℝ) / ((d : ℝ) * (d + 2)))
        else 0 := by
      intro i j
      split_ifs with h h0
      · subst h; subst h0
        rw [integral_const_mul, ← ha]
        congr 1
        · ring
        · congr 1; funext u; ring
      · subst h
        rw [integral_const_mul, ← hb i h0]
        congr 1
        · ring
        · congr 1; funext u; ring
      · by_cases hi0 : i = 0
        · have hj0 : j ≠ 0 := fun hj => h (hi0.trans hj.symm)
          refine integral_normSphere_eq_zero_of_odd j fun u => ?_
          rw [flipIso_apply, flipIso_apply, flipIso_apply, if_pos rfl, if_neg h,
            if_neg (Ne.symm hj0)]
          ring
        · refine integral_normSphere_eq_zero_of_odd i fun u => ?_
          rw [flipIso_apply, flipIso_apply, flipIso_apply, if_pos rfl, if_neg (Ne.symm h),
            if_neg (Ne.symm hi0)]
          ring
    simp_rw [fun i => integral_finsetSum (μ := normSphere d) (Finset.univ : Finset (Fin d))
      (f := fun j u => y i * y j * (u 0 ^ 2 * (u i * u j))) (fun j _ => hI i j), hij,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), if_pos rfl,
      EuclideanSpace.norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin d)).erase 0,
        y i ^ 2 * (if i = 0 then 3 / ((d : ℝ) * (d + 2)) else 1 / (d * (d + 2))) =
          ‖y i‖ ^ 2 / (d * (d + 2)) := by
      intro i hi
      rw [if_neg (Finset.ne_of_mem_erase hi), Real.norm_eq_abs, sq_abs]
      ring
    rw [Finset.sum_congr rfl h2, ← Finset.sum_div, Real.norm_eq_abs, sq_abs]
    ring
  /- A reflection taking `v` to `e₁`. -/
  have he0 : ‖(ebasis 0 : Rd d)‖ = 1 := by simp [ebasis]
  set R := (ℝ ∙ (v - ebasis 0))ᗮ.reflection with hR
  have hRv : R v = ebasis 0 := Submodule.reflection_sub (hv.trans he0.symm)
  have hself : ∀ a b : Rd d, ⟪a, R b⟫ = ⟪R a, b⟫ := fun a b => by
    rw [← R.inner_map_map a (R b), hR, Submodule.reflection_reflection]
  rw [← integral_normSphere_isometry R (fun u => ⟪v, u⟫ ^ 2 * ⟪x, u⟫ ^ 2)]
  simp only [hself, hRv, inner_ebasis_left]
  rw [hcase, LinearIsometryEquiv.norm_map, ← inner_ebasis_left, ← hRv, ← hself,
    Submodule.reflection_reflection]

/-! ## The measures `L_Σ` -/

theorem continuous_quad_vec (S : Mat d) : Continuous fun u : Rd d => quad S u := by
  unfold quad
  fun_prop

/-- `ℓ` and `L_Σ` read `k` on `(0,∞)` only. -/
theorem lineProfileMeasure_congr {k k' : ℝ → ℝ} (h : ∀ r : ℝ, 0 < r → k r = k' r) :
    lineProfileMeasure k = lineProfileMeasure k' := by
  unfold lineProfileMeasure
  congr 1
  funext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [h |r| (abs_pos.2 hr)]

theorem lineLevy_congr {k k' : ℝ → ℝ} (h : ∀ r : ℝ, 0 < r → k r = k' r) (S : Mat d) :
    lineLevy k S = lineLevy k' S := by
  unfold lineLevy
  rw [lineProfileMeasure_congr h]

instance (k : ℝ → ℝ) : SFinite (lineProfileMeasure k) := by
  unfold lineProfileMeasure
  infer_instance

/-- The kernel `u ↦ (r ↦ r q_Σ(u)^{1/2} u)_*ℓ` is measurable. -/
theorem measurable_lineKernel (k : ℝ → ℝ) (S : Mat d) :
    Measurable fun u : Rd d =>
      (lineProfileMeasure k).map fun r => (r * Real.sqrt (quad S u)) • u := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have hg : ∀ u : Rd d, Measurable fun r : ℝ => (r * Real.sqrt (quad S u)) • u := fun u => by
    fun_prop
  have h : ∀ u : Rd d, ((lineProfileMeasure k).map fun r => (r * Real.sqrt (quad S u)) • u) B =
      ∫⁻ r, B.indicator 1 ((r * Real.sqrt (quad S u)) • u) ∂(lineProfileMeasure k) := by
    intro u
    rw [Measure.map_apply (hg u) hB, ← lintegral_indicator_one ((hg u) hB)]
    rfl
  simp_rw [h]
  refine Measurable.lintegral_prod_right' (f := fun p : Rd d × ℝ =>
    B.indicator 1 ((p.2 * Real.sqrt (quad S p.1)) • p.1)) ?_
  refine (measurable_one.indicator hB).comp ?_
  have hq := (continuous_quad_vec S).measurable
  fun_prop

/-- **The defining identity of `L_Σ`**: `∫ f dL_Σ = ∫ σ̄(du) ∫ f(r q_Σ(u)^{1/2} u) ℓ(dr)` for
measurable `f ≥ 0` with `f(0) = 0`. -/
theorem lintegral_lineLevy (k : ℝ → ℝ) (S : Mat d) {f : Rd d → ℝ≥0∞} (hf : Measurable f)
    (hf0 : f 0 = 0) :
    ∫⁻ x, f x ∂(lineLevy k S) =
      ∫⁻ u, ∫⁻ r, f ((r * Real.sqrt (quad S u)) • u) ∂(lineProfileMeasure k) ∂(normSphere d) := by
  have hind : ({0}ᶜ : Set (Rd d)).indicator f = f := by
    funext x
    by_cases hx : x = 0
    · subst hx; simp [hf0]
    · rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx)]
  rw [lineLevy, ← lintegral_indicator (measurableSet_singleton _).compl, hind,
    Measure.lintegral_bind (measurable_lineKernel k S).aemeasurable hf.aemeasurable]
  refine lintegral_congr fun u => ?_
  exact lintegral_map hf (by fun_prop)

theorem lineLevy_apply (k : ℝ → ℝ) (S : Mat d) {B : Set (Rd d)} (hB : MeasurableSet B) :
    lineLevy k S B = ∫⁻ u, ∫⁻ r, (B \ {0}).indicator 1 ((r * Real.sqrt (quad S u)) • u)
      ∂(lineProfileMeasure k) ∂(normSphere d) := by
  have hB' : MeasurableSet (B \ {0}) := hB.diff (measurableSet_singleton _)
  rw [← lintegral_lineLevy k S (measurable_one.indicator hB') (by simp),
    lintegral_indicator_one hB', lineLevy, Measure.restrict_apply hB',
    Measure.restrict_apply hB, sdiff_eq, inter_assoc, inter_self]

theorem lineLevy_zero_set (k : ℝ → ℝ) (S : Mat d) : lineLevy k S {0} = 0 := by
  rw [lineLevy, Measure.restrict_apply (measurableSet_singleton _)]
  simp

/-- `ℓ` is symmetric. -/
theorem lintegral_lineProfile_neg {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ r, g (-r) ∂(lineProfileMeasure k) = ∫⁻ r, g r ∂(lineProfileMeasure k) := by
  rw [lintegral_lineProfile hk (g := fun r => g (-r)) (hg.comp measurable_neg),
    lintegral_lineProfile hk hg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [neg_neg]
  ring

/-- **The polar form along one direction**: for `‖u‖ = 1` and `q_Σ(u) > 0`,
`∫ F(r q^{1/2} u) ℓ(dr) = ∫_0^∞ (F(su) + F(-su)) k(s q^{-1/2}) ds/s`. -/
theorem lintegral_lineDir {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {q : ℝ} (hq : 0 < q)
    (u : Rd d) {F : Rd d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ r, F ((r * Real.sqrt q) • u) ∂(lineProfileMeasure k) =
      ∫⁻ s in Ioi (0 : ℝ), (F (s • u) + F (-(s • u))) *
        ENNReal.ofReal (k (s / Real.sqrt q) / s) := by
  have h := lintegral_lineProfile_scale hk hq (g := fun t => F (t • u)) (hF.comp (by fun_prop))
  simp only [neg_smul] at h
  exact h

theorem measurable_lineInner (k : ℝ → ℝ) (S : Mat d) {F : Rd d → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun u : Rd d =>
      ∫⁻ r, F ((r * Real.sqrt (quad S u)) • u) ∂(lineProfileMeasure k) := by
  refine Measurable.lintegral_prod_right' (f := fun p : Rd d × ℝ =>
    F ((p.2 * Real.sqrt (quad S p.1)) • p.1)) (hF.comp ?_)
  have hq := (continuous_quad_vec S).measurable
  fun_prop

theorem quad_neg_vec (S : Mat d) (u : Rd d) : quad S (-u) = quad S u := by
  rw [← neg_one_smul ℝ u, quad_smul_vec]
  ring

/-- **`L_Σ` is a Lévy measure.** -/
theorem lineProfile_min_ne_top {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1) ∂(lineProfileMeasure k) ≠ ⊤ := by
  rw [lintegral_lineProfile hk (by fun_prop)]
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext r
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro h; by_cases h1 : r < 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_lt.1 h1)
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit, lintegral_union measurableSet_Ici
    (Set.disjoint_left.2 fun x hx hx' => absurd (show (1 : ℝ) ≤ x from hx') (not_le.2 hx.2))]
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun r => 2 * ENNReal.ofReal (r * k r))
      fun r hr => ?_, lintegral_const_mul' _ _ (by norm_num)]
    · exact ENNReal.mul_ne_top (by norm_num) hk0
    · have hr0 : 0 < r := hr.1
      have hr1 : r ^ 2 ≤ 1 := by nlinarith [hr.2]
      simp only [neg_sq, min_eq_left hr1]
      rw [← two_mul, mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 2
      field_simp
  · rw [setLIntegral_congr_fun measurableSet_Ici (g := fun r => 2 * ENNReal.ofReal (k r / r))
      fun r hr => ?_, lintegral_const_mul' _ _ (by norm_num),
      setLIntegral_congr Ioi_ae_eq_Ici.symm]
    · exact ENNReal.mul_ne_top (by norm_num) hk1
    · have hr1 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [show (1 : ℝ) ≤ r from hr]
      simp only [neg_sq, min_eq_right hr1, ENNReal.ofReal_one]
      ring

theorem isLevyMeasure_lineLevy {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {S : Mat d}
    (hS : S.PosSemidef) : IsLevyMeasure (lineLevy k S) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    refine ⟨lineLevy_zero_set k S, ?_⟩
    have h : lineLevy k S = 0 := by
      rw [lineLevy]
      have : ({0}ᶜ : Set (Rd 0)) = ∅ := by
        ext x; simp [Subsingleton.elim x 0]
      rw [this, Measure.restrict_empty]
    simp [h]
  haveI : NeZero d := ⟨hdpos.ne'⟩
  refine ⟨lineLevy_zero_set k S, ?_⟩
  rw [lintegral_lineLevy k S (by fun_prop) (by simp)]
  set C := max 1 (lamMax S) with hC
  have hbound : ∀ᵐ u ∂normSphere d, ∫⁻ r, ENNReal.ofReal (min (‖(r * Real.sqrt (quad S u)) • u‖ ^ 2) 1)
      ∂(lineProfileMeasure k) ≤ ENNReal.ofReal C * ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1)
        ∂(lineProfileMeasure k) := by
    filter_upwards [ae_normSphere_norm] with u hu
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun r => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq0 := quad_nonneg hS u
    have hq : quad S u ≤ C := (quad_le_lamMax hS.isHermitian hu).trans (le_max_right _ _)
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hq0]
    calc min (r ^ 2 * quad S u) 1 ≤ min (r ^ 2 * C) (C * 1) := by
          refine min_le_min (mul_le_mul_of_nonneg_left hq (sq_nonneg r)) ?_
          rw [mul_one]; exact le_max_left _ _
      _ = C * min (r ^ 2) 1 := by
          rw [mul_comm (r ^ 2) C, mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ C)]
  haveI := isProbabilityMeasure_normSphere (d := d) (by omega)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lineProfile_min_ne_top hk hk0 hk1)

/-- The indicator of `f⁻¹(B) ∖ {0}` for an `f` vanishing only at `0`. -/
theorem indicator_preimage_sdiff_zero {f : Rd d → Rd d} (hf : ∀ y, f y = 0 ↔ y = 0)
    (B : Set (Rd d)) (y : Rd d) :
    (f ⁻¹' B \ {0}).indicator (1 : Rd d → ℝ≥0∞) y = (B \ {0}).indicator 1 (f y) := by
  have hset : f ⁻¹' B \ {0} = f ⁻¹' (B \ {0}) := by
    ext z
    simp only [Set.mem_sdiff, mem_preimage, mem_singleton_iff, hf]
  rw [hset]
  by_cases h : f y ∈ B \ {0}
  · rw [indicator_of_mem h, indicator_of_mem (show y ∈ f ⁻¹' (B \ {0}) from h)]
    rfl
  · rw [indicator_of_notMem h, indicator_of_notMem (show y ∉ f ⁻¹' (B \ {0}) from h)]

/-- **`L_Σ` is symmetric.** -/
theorem lineLevy_symm {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) (S : Mat d) :
    push (-1) (lineLevy k S) = lineLevy k S := by
  ext B hB
  have hB' : MeasurableSet (lin (-1 : Mat d) ⁻¹' B) := (lin (-1 : Mat d)).continuous.measurable hB
  rw [push, Measure.map_apply (lin (-1 : Mat d)).continuous.measurable hB, lineLevy_apply k S hB',
    lineLevy_apply k S hB]
  refine lintegral_congr fun u => ?_
  have hm : Measurable fun r : ℝ =>
      (B \ {0}).indicator (1 : Rd d → ℝ≥0∞) ((r * Real.sqrt (quad S u)) • u) :=
    ((measurable_one.indicator (hB.diff (measurableSet_singleton _)))).comp (by fun_prop)
  rw [← lintegral_lineProfile_neg hk hm]
  have key : ∀ y : Rd d, (lin (-1 : Mat d) ⁻¹' B \ {0}).indicator (1 : Rd d → ℝ≥0∞) y =
      (B \ {0}).indicator 1 (-y) := by
    intro y
    rw [indicator_preimage_sdiff_zero (f := lin (-1 : Mat d)) (fun y => by
      rw [lin_neg_one_apply, neg_eq_zero]), lin_neg_one_apply]
  refine lintegral_congr fun r => ?_
  simp only [neg_mul, neg_smul]
  exact key _

/-- **Covariance**: `L_{cQΣQᵀ} = (√c Q)_*L_Σ`. -/
theorem lineLevy_sim (k : ℝ → ℝ) (S : Mat d) {c : ℝ} (hc : 0 < c) {Q : Mat d}
    (hQ : Q ∈ orthSet d) : lineLevy k (c • (Q * S * Qᵀ)) = push (Real.sqrt c • Q) (lineLevy k S) := by
  ext B hB
  set A := Real.sqrt c • Q with hA
  have hlinA : ∀ y : Rd d, lin A y = Real.sqrt c • lin Q y := fun y => by
    rw [hA, lin_smul]; rfl
  have hinj : ∀ y : Rd d, lin A y = 0 ↔ y = 0 := by
    intro y
    rw [hlinA, smul_eq_zero, or_iff_right (Real.sqrt_pos.2 hc).ne']
    constructor
    · intro h
      have := norm_lin_of_orth hQ y
      rw [h, norm_zero] at this
      exact norm_eq_zero.1 this.symm
    · rintro rfl; simp
  have hB' : MeasurableSet (lin A ⁻¹' B) := (lin A).continuous.measurable hB
  rw [push, Measure.map_apply (lin A).continuous.measurable hB, lineLevy_apply k _ hB,
    lineLevy_apply k S hB']
  have hF : Measurable fun u : Rd d => ∫⁻ r, (B \ {0}).indicator 1
      ((r * Real.sqrt (quad (c • (Q * S * Qᵀ)) u)) • u) ∂(lineProfileMeasure k) :=
    measurable_lineInner k _ (measurable_one.indicator (hB.diff (measurableSet_singleton _)))
  rw [← lintegral_normSphere_orth hQ hF]
  refine lintegral_congr fun v => ?_
  refine lintegral_congr fun r => ?_
  have hq : quad (c • (Q * S * Qᵀ)) (lin Q v) = c * quad S v := by
    rw [quad_smul, show Q * S * Qᵀ = act Q S from rfl, quad_act, lin_transpose_lin_of_orth hQ]
  rw [hq, Real.sqrt_mul hc.le]
  have hpt : (r * (Real.sqrt c * Real.sqrt (quad S v))) • lin Q v =
      lin A ((r * Real.sqrt (quad S v)) • v) := by
    rw [hlinA, map_smul, smul_smul]
    congr 1
    ring
  rw [hpt]
  exact (indicator_preimage_sdiff_zero hinj B _).symm

/-- **Monotonicity**: `L_Σ ≤ L_{Σ'}` for `Σ ≤ Σ'` in `PSD(d)`. -/
theorem lineLevy_mono {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S S' : Mat d} (hS : S.PosSemidef) (hle : loewnerLE S S') :
    lineLevy k S ≤ lineLevy k S' := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [lineLevy_apply k S hB, lineLevy_apply k S' hB]
  refine lintegral_mono fun u => ?_
  have hF : Measurable ((B \ {0}).indicator (1 : Rd d → ℝ≥0∞)) :=
    measurable_one.indicator (hB.diff (measurableSet_singleton _))
  have hq0 := quad_nonneg hS u
  have hqq : quad S u ≤ quad S' u := by
    have := quad_nonneg hle u
    rw [quad_sub] at this
    linarith
  rcases hq0.eq_or_lt with hq | hq
  · rw [← hq, Real.sqrt_zero]
    simp
  · rw [lintegral_lineDir hk hq u hF, lintegral_lineDir hk (hq.trans_le hqq) u hF]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))
    have hs0 : 0 < s := hs
    gcongr _ * ENNReal.ofReal ?_
    refine div_le_div_of_nonneg_right ?_ hs0.le
    have h1 : 0 < Real.sqrt (quad S u) := Real.sqrt_pos.2 hq
    have h2 : Real.sqrt (quad S u) ≤ Real.sqrt (quad S' u) := Real.sqrt_le_sqrt hqq
    refine hk (div_pos hs0 (h1.trans_le h2)) (div_pos hs0 h1) ?_
    exact div_le_div_of_nonneg_left hs0.le h1 h2

/-- **The polar form of `L_Σ`**, `Σ ∈ PD(d)`, for a measurable `k`: `L_Σ` is the image of
`σ̄(du) 2k(s q_Σ(u)^{-1/2}) ds/s` under `(u, s) ↦ su`. -/
theorem lineLevy_polar_of_measurable {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) (hkm : Measurable k)
    {S : Mat d} (hS : S.PosDef) :
    lineLevy k S = (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
        fun p => ENNReal.ofReal (2 * k (p.2 / Real.sqrt (quad S p.1)) / p.2)).map
      (fun p => p.2 • p.1) := by
  have hq := (continuous_quad_vec S).measurable
  have hm : Measurable fun p : Rd d × ℝ => p.2 • p.1 := by fun_prop
  set D : Rd d × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (2 * k (p.2 / Real.sqrt (quad S p.1)) / p.2)
    with hDdef
  have hD : Measurable D := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul (hkm.comp (by fun_prop))).div measurable_snd
  ext B hB
  have hB0 : MeasurableSet (B \ {0}) := hB.diff (measurableSet_singleton _)
  set w : Rd d → ℝ → ℝ≥0∞ := fun u s => ENNReal.ofReal (k (s / Real.sqrt (quad S u)) / s) with hw
  have hwm : Measurable fun p : Rd d × ℝ => w p.1 p.2 := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (hkm.comp (by fun_prop)).div measurable_snd
  set G : Rd d → ℝ≥0∞ := fun u =>
    ∫⁻ s in Ioi (0 : ℝ), (B \ {0}).indicator 1 (s • u) * w u s with hG
  set G' : Rd d → ℝ≥0∞ := fun u =>
    ∫⁻ s in Ioi (0 : ℝ), (B \ {0}).indicator 1 (-(s • u)) * w u s with hG'
  have hGm : Measurable G :=
    Measurable.lintegral_prod_right' (f := fun p : Rd d × ℝ =>
      (B \ {0}).indicator 1 (p.2 • p.1) * w p.1 p.2) ((measurable_one.indicator hB0).comp hm |>.mul hwm)
  have hG'm : Measurable G' :=
    Measurable.lintegral_prod_right' (f := fun p : Rd d × ℝ =>
      (B \ {0}).indicator 1 (-(p.2 • p.1)) * w p.1 p.2)
      ((measurable_one.indicator hB0).comp hm.neg |>.mul hwm)
  /- The left side is `∫ (G + G') dσ̄`. -/
  have hL : lineLevy k S B = ∫⁻ u, (G u + G' u) ∂(normSphere d) := by
    rw [lineLevy_apply k S hB]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_normSphere_norm] with u hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    rw [lintegral_lineDir hk (quad_pos hS hu0) u (measurable_one.indicator hB0)]
    simp only [hG, hG', add_mul]
    exact lintegral_add_left (((measurable_one.indicator hB0).comp (by fun_prop)).mul
      (hwm.comp (by fun_prop : Measurable fun s : ℝ => (u, s)))) _
  /- `∫ G' dσ̄ = ∫ G dσ̄` by `u ↦ -u`. -/
  have hsym : ∫⁻ u, G' u ∂(normSphere d) = ∫⁻ u, G u ∂(normSphere d) := by
    rw [← lintegral_normSphere_isometry (LinearIsometryEquiv.neg ℝ) hG'm]
    refine lintegral_congr fun u => ?_
    simp only [hG, hG', LinearIsometryEquiv.coe_neg, smul_neg, neg_neg, hw,
      quad_neg_vec]
  /- The right side. -/
  have hR : (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity D).map
      (fun p => p.2 • p.1) B = ∫⁻ u, 2 * G u ∂(normSphere d) := by
    rw [Measure.map_apply hm hB, withDensity_apply _ (hm hB), ← lintegral_indicator (hm hB),
      lintegral_prod _ ((hD.indicator (hm hB)).aemeasurable)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_normSphere_norm] with u hu
    show _ = 2 * ∫⁻ s in Ioi (0 : ℝ), (B \ {0}).indicator 1 (s • u) * w u s
    rw [← lintegral_const_mul _ (f := fun s => (B \ {0}).indicator 1 (s • u) * w u s)
      (((measurable_one.indicator hB0).comp (measurable_id.smul_const u)).mul
        (hwm.comp (measurable_const.prodMk measurable_id)))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    have hsu : s • u ≠ 0 := by
      rw [ne_eq, smul_eq_zero, not_or]
      exact ⟨hs0.ne', by rintro rfl; simp at hu⟩
    by_cases hBs : s • u ∈ B
    · rw [indicator_of_mem (show (u, s) ∈ (fun p : Rd d × ℝ => p.2 • p.1) ⁻¹' B from hBs),
        indicator_of_mem (show s • u ∈ B \ {0} from ⟨hBs, hsu⟩), Pi.one_apply, one_mul, hDdef, hw]
      simp only
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), mul_div_assoc]
    · rw [indicator_of_notMem (show (u, s) ∉ (fun p : Rd d × ℝ => p.2 • p.1) ⁻¹' B from hBs),
        indicator_of_notMem (show s • u ∉ B \ {0} from fun h => hBs h.1), zero_mul, mul_zero]
  rw [hL, hR, lintegral_add_left hGm, hsym, ← lintegral_add_left hGm]
  refine lintegral_congr fun u => ?_
  ring

theorem normSphere_zero : normSphere d {0} = 0 :=
  measure_mono_null (fun u (hu : u = 0) => by simp [hu]) (ae_iff.1 (ae_normSphere_norm (d := d)))

/-- `k` cut off to `0` off `(0,∞)`: measurable, and equal to `k` where the node reads it. -/
theorem indicator_Ioi_props {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) :
    Measurable ((Ioi (0 : ℝ)).indicator k) ∧ AntitoneOn ((Ioi (0 : ℝ)).indicator k) (Ioi 0) ∧
      ∀ r : ℝ, 0 < r → (Ioi (0 : ℝ)).indicator k r = k r := by
  refine ⟨measurable_indicator_Ioi_of_antitoneOn hk, fun a ha b hb hab => ?_,
    fun r hr => indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr) k⟩
  rw [indicator_of_mem ha, indicator_of_mem hb]
  exact hk ha hb hab

/-- **`prop:similarity-line-family`(1)**, the measures (blind review R4-1: from the hypotheses on
`k` alone): `L_Σ` is a symmetric Lévy measure with the defining identity
`∫ f dL_Σ = ∫ σ̄(du) ∫ f(r q_Σ(u)^{1/2} u) ℓ(dr)`; for `Σ ∈ PD(d)` it is the image of
`σ̄(du) 2k(s q_Σ(u)^{-1/2}) ds/s` under `(u, s) ↦ su`, a polar profile nonincreasing in `s` and at
most `2k(0+)`; `L_{cQΣQᵀ} = (√c Q)_*L_Σ`; `L_Σ ≤ L_{Σ'}` for `Σ ≤ Σ'`. Spends nothing. -/
theorem line_family_levy (_hd : 2 ≤ d) (k : ℝ → ℝ) (_hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk_anti : AntitoneOn k (Ioi 0)) (_hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    (∀ S : Mat d, S.PosSemidef →
      IsLevyMeasure (lineLevy k S) ∧ push (-1) (lineLevy k S) = lineLevy k S ∧
      ∀ f : Rd d → ℝ≥0∞, Measurable f → f 0 = 0 →
        ∫⁻ x, f x ∂(lineLevy k S) =
          ∫⁻ u, ∫⁻ r, f ((r * Real.sqrt (quad S u)) • u) ∂(lineProfileMeasure k) ∂(normSphere d)) ∧
    (∀ S : Mat d, S.PosDef →
      lineLevy k S = (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
          fun p => ENNReal.ofReal (2 * k (p.2 / Real.sqrt (quad S p.1)) / p.2)).map
        (fun p => p.2 • p.1) ∧
      (∀ u ∈ Metric.sphere (0 : Rd d) 1,
        AntitoneOn (fun s => 2 * k (s / Real.sqrt (quad S u))) (Ioi 0) ∧
        ∀ s : ℝ, 0 < s → ENNReal.ofReal (2 * k (s / Real.sqrt (quad S u))) ≤
          2 * ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (k r))) ∧
    (∀ S : Mat d, S.PosSemidef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      lineLevy k (c • (Q * S * Qᵀ)) = push (Real.sqrt c • Q) (lineLevy k S)) ∧
    (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      lineLevy k S ≤ lineLevy k S') := by
  obtain ⟨hkIm, hkIa, hkIe⟩ := indicator_Ioi_props hk_anti
  set kI := (Ioi (0 : ℝ)).indicator k with hkI
  refine ⟨fun S hS => ⟨isLevyMeasure_lineLevy hk_anti hk0 hk1 hS, lineLevy_symm hk_anti S,
    fun f hf hf0 => lintegral_lineLevy k S hf hf0⟩, fun S hS => ⟨?_, fun u hu => ⟨?_, ?_⟩⟩,
    fun S _ c hc Q hQ => lineLevy_sim k S hc hQ, fun S S' hS _ hle => lineLevy_mono hk_anti hS hle⟩
  · rw [lineLevy_congr (fun r hr => (hkIe r hr).symm) S, lineLevy_polar_of_measurable hkIa hkIm hS]
    congr 1
    refine withDensity_congr_ae (ae_iff.2 (measure_mono_null ?_ (measure_union_null
      (s := {0} ×ˢ univ) (t := univ ×ˢ Iic 0) ?_ ?_)))
    · intro p hp
      simp only [mem_setOf_eq] at hp
      by_contra hcon
      simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, true_and, mem_Iic,
        not_or, not_le] at hcon
      have hq : 0 < quad S p.1 := quad_pos hS hcon.1
      exact hp (by rw [hkIe _ (div_pos hcon.2 (Real.sqrt_pos.2 hq))])
    · rw [Measure.prod_prod, normSphere_zero, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Iic,
        show Iic (0 : ℝ) ∩ Ioi 0 = ∅ from by ext x; simp, measure_empty, mul_zero]
  · have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu
    have hq : 0 < Real.sqrt (quad S u) := Real.sqrt_pos.2 (quad_pos hS hu0)
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (hk_anti (div_pos ha hq) (div_pos hb hq)
      (div_le_div_of_nonneg_right hab hq.le)) (by norm_num)
  · have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu
    have hq : 0 < Real.sqrt (quad S u) := Real.sqrt_pos.2 (quad_pos hS hu0)
    intro s hs
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    exact le_iSup_of_le (⟨s / Real.sqrt (quad S u), div_pos hs hq⟩ : Ioi (0 : ℝ)) le_rfl

/-! ## Clause (3): not shape-blind -/

/-- The polar sector `{x : a < |x| < b, x/|x| ∈ U}`. -/
def lineSector (U : Set (Rd d)) (a b : ℝ) : Set (Rd d) :=
  {x | a < ‖x‖ ∧ ‖x‖ < b ∧ ‖x‖⁻¹ • x ∈ U}

theorem measurableSet_lineSector {U : Set (Rd d)} (hU : MeasurableSet U) (a b : ℝ) :
    MeasurableSet (lineSector U a b) := by
  refine (measurableSet_lt measurable_const measurable_norm).inter
    ((measurableSet_lt measurable_norm measurable_const).inter ?_)
  exact (measurable_norm.inv.smul measurable_id) hU

/-- **`L_Σ` of a symmetric sector**, along one direction: for `‖u‖ = 1`, `q > 0`, `0 ≤ a`, and
`U = -U`, `∫ 1_{E∖0}(r q^{1/2} u) ℓ(dr) = 2·1_U(u) ∫_a^b k(s q^{-1/2}) ds/s`. -/
theorem lintegral_lineDir_sector {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {q : ℝ} (hq : 0 < q)
    {u : Rd d} (hu : ‖u‖ = 1) {U : Set (Rd d)} (hU : MeasurableSet U) (hUs : ∀ v, -v ∈ U ↔ v ∈ U)
    {a b : ℝ} (ha : 0 ≤ a) :
    ∫⁻ r, (lineSector U a b \ {0}).indicator 1 ((r * Real.sqrt q) • u) ∂(lineProfileMeasure k) =
      2 * U.indicator (fun _ => ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s)) u := by
  have hE : MeasurableSet (lineSector U a b \ {0}) :=
    (measurableSet_lineSector hU a b).diff (measurableSet_singleton _)
  rw [lintegral_lineDir hk hq u (measurable_one.indicator hE)]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hpt : ∀ s : ℝ, 0 < s → (lineSector U a b \ {0}).indicator (1 : Rd d → ℝ≥0∞) (s • u) =
      ((Ioo a b).indicator 1 s) * U.indicator 1 u ∧
      (lineSector U a b \ {0}).indicator (1 : Rd d → ℝ≥0∞) (-(s • u)) =
      ((Ioo a b).indicator 1 s) * U.indicator 1 u := by
    intro s hs
    have hn : ‖s • u‖ = s := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hs]
    have hn' : ‖-(s • u)‖ = s := by rw [norm_neg, hn]
    have hdir : ‖s • u‖⁻¹ • (s • u) = u := by rw [hn, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    have hdir' : ‖-(s • u)‖⁻¹ • (-(s • u)) = -u := by
      rw [hn', smul_neg, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    have hne : s • u ≠ 0 := by rw [ne_eq, smul_eq_zero, not_or]; exact ⟨hs.ne', hu0⟩
    have hne' : -(s • u) ≠ 0 := neg_ne_zero.2 hne
    constructor
    · by_cases h : s ∈ Ioo a b ∧ u ∈ U
      · rw [indicator_of_mem (show s • u ∈ lineSector U a b \ {0} from
          ⟨⟨by rw [hn]; exact h.1.1, by rw [hn]; exact h.1.2, by rw [hdir]; exact h.2⟩, hne⟩),
          indicator_of_mem h.1, indicator_of_mem h.2]
        simp
      · rw [indicator_of_notMem (show s • u ∉ lineSector U a b \ {0} from fun h' => h
          ⟨⟨by rw [← hn]; exact h'.1.1, by rw [← hn]; exact h'.1.2.1⟩,
            by rw [← hdir]; exact h'.1.2.2⟩)]
        by_cases h1 : s ∈ Ioo a b
        · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => h ⟨h1, h2⟩), mul_zero]
        · rw [indicator_of_notMem h1, zero_mul]
    · by_cases h : s ∈ Ioo a b ∧ u ∈ U
      · rw [indicator_of_mem (show -(s • u) ∈ lineSector U a b \ {0} from
          ⟨⟨by rw [hn']; exact h.1.1, by rw [hn']; exact h.1.2, by rw [hdir', hUs]; exact h.2⟩,
            hne'⟩), indicator_of_mem h.1, indicator_of_mem h.2]
        simp
      · rw [indicator_of_notMem (show -(s • u) ∉ lineSector U a b \ {0} from fun h' => h
          ⟨⟨by rw [← hn']; exact h'.1.1, by rw [← hn']; exact h'.1.2.1⟩,
            by rw [← hUs, ← hdir']; exact h'.1.2.2⟩)]
        by_cases h1 : s ∈ Ioo a b
        · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => h ⟨h1, h2⟩), mul_zero]
        · rw [indicator_of_notMem h1, zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun s => 2 * (U.indicator 1 u *
      ((Ioo a b).indicator (fun s => ENNReal.ofReal (k (s / Real.sqrt q) / s)) s))) fun s hs => ?_]
  · rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by
      by_cases hU' : u ∈ U <;> simp [hU']),
      lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.2 (show Ioo a b ⊆ Ioi (0 : ℝ) from fun s hs => ha.trans_lt hs.1)]
    by_cases hU' : u ∈ U
    · rw [indicator_of_mem hU', indicator_of_mem hU', Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hU', indicator_of_notMem hU', zero_mul]
  · obtain ⟨h1, h2⟩ := hpt s hs
    rw [h1, h2, ← two_mul]
    beta_reduce
    by_cases hs' : s ∈ Ioo a b
    · simp only [indicator_of_mem hs', Pi.one_apply]
      ring
    · simp only [indicator_of_notMem hs']
      ring

/-- **`L_Σ` of a symmetric sector**: `L_Σ(E) = 2 ∫_U σ̄(du) ∫_a^b k(s q_Σ(u)^{-1/2}) ds/s`. -/
theorem lineLevy_sector {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S : Mat d} (hS : S.PosDef)
    {U : Set (Rd d)} (hU : MeasurableSet U) (hUs : ∀ v, -v ∈ U ↔ v ∈ U) {a b : ℝ} (ha : 0 ≤ a) :
    lineLevy k S (lineSector U a b) = ∫⁻ u, 2 * U.indicator (fun u =>
      ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt (quad S u)) / s)) u ∂(normSphere d) := by
  rw [lineLevy_apply k S (measurableSet_lineSector hU a b)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_normSphere_norm] with u hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [lintegral_lineDir_sector hk (quad_pos hS hu0) hu hU hUs ha]
  by_cases hU' : u ∈ U
  · rw [indicator_of_mem hU', indicator_of_mem hU']
  · rw [indicator_of_notMem hU', indicator_of_notMem hU']

/-- The image of a sector under a linear isometry. -/
theorem preimage_lineSector (R : Rd d ≃ₗᵢ[ℝ] Rd d) (U : Set (Rd d)) (a b : ℝ) :
    R ⁻¹' lineSector U a b = lineSector (R ⁻¹' U) a b := by
  ext x
  simp only [lineSector, mem_preimage, mem_setOf_eq, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.map_smul]

/-- An eigenvector of the largest and of the least eigenvalue, distinct when `Σ` is not a
multiple of `I`. -/
theorem exists_quad_lt_of_not_scalar [NeZero d] {S : Mat d} (hS : S.IsHermitian)
    (hns : ¬ ∃ c : ℝ, S = c • (1 : Mat d)) :
    ∃ u v : Rd d, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ quad S v < quad S u := by
  obtain ⟨u, hu1, hSu⟩ := exists_unit_eigvec_eigUp hS (Fin.rev 0)
  obtain ⟨v, hv1, hSv⟩ := exists_unit_eigvec_eigUp hS 0
  rw [← lamMax_eq_eigUp_last hS] at hSu
  rw [← lamMin_eq_eigUp_zero hS] at hSv
  have hqu : quad S u = lamMax S := by
    rw [quad, hSu, real_inner_smul_right, real_inner_self_eq_norm_sq, hu1]; ring
  have hqv : quad S v = lamMin S := by
    rw [quad, hSv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv1]; ring
  refine ⟨u, v, hu1, hv1, ?_⟩
  rw [hqu, hqv]
  refine lt_of_le_of_ne (lamMin_le_lamMax hS) fun heq => hns ⟨lamMin S, ?_⟩
  refine eq_of_quad_eq hS (isHermitian_one.smul (IsSelfAdjoint.all _)) fun x => ?_
  have h1 : lamMin S * ‖x‖ ^ 2 ≤ quad S x := lamMin_mul_norm_sq_le hS x
  have h2 : quad S x ≤ lamMin S * ‖x‖ ^ 2 := by rw [heq]; exact quad_le_lamMax_mul hS x
  rw [quad_smul, quad_one]
  linarith

/-- `∫_1^∞ dr/r = ∞`. Mathlib types only. -/
theorem lintegral_Ioi_one_inv : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal r⁻¹ = ⊤ := by
  by_contra h
  refine not_integrableOn_Ioi_inv (a := (1 : ℝ)) ⟨measurable_inv.aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal ?_).2 (lt_top_iff_ne_top.2 h)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact inv_nonneg.2 (zero_le_one.trans (le_of_lt hr))

/-- **A profile with `k(λr) = k(r)` almost everywhere, `λ > 1`, vanishes**: the step of
`prop:similarity-line-family`(3). Stated with the a.e. equality on every bounded interval, in the
form the sectors give it: `k(s/√m') = k(s/√m'')` for a.e. `s`, `m' > m'' > 0`. -/
theorem lineProfile_dilation_contra {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk_anti : AntitoneOn k (Ioi 0)) (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {m' m'' : ℝ} (hm'' : 0 < m'')
    (hm : m'' < m')
    (key : ∀ a b : ℝ, 0 < a → a < b →
      ∀ᵐ s ∂(volume.restrict (Ioo a b)), k (s / Real.sqrt m') = k (s / Real.sqrt m'')) : False := by
  obtain ⟨r₀, hr₀, hkr₀⟩ := hk_ne
  have hκ : 0 < k r₀ := lt_of_le_of_ne (hk_nonneg r₀ hr₀) (Ne.symm hkr₀)
  set a' := Real.sqrt m' with ha'
  set a'' := Real.sqrt m'' with ha''
  have ha''0 : 0 < a'' := Real.sqrt_pos.2 hm''
  have ha'0 : 0 < a' := Real.sqrt_pos.2 (hm''.trans hm)
  set ρ := a' / a'' with hρ
  have hρ1 : 1 < ρ := by
    rw [hρ, one_lt_div ha''0]
    exact Real.sqrt_lt_sqrt hm''.le hm
  set μ := Real.sqrt ρ with hμ
  have hμ1 : 1 < μ := by rw [hμ, Real.lt_sqrt zero_le_one]; simpa using hρ1
  have hμ0 : 0 < μ := zero_lt_one.trans hμ1
  have hμμ : μ * μ = ρ := Real.mul_self_sqrt (zero_le_one.trans hρ1.le)
  /- The step: `k(t) ≥ κ` gives `k(μt) ≥ κ`. -/
  have hstep : ∀ t : ℝ, 0 < t → k r₀ ≤ k t → k r₀ ≤ k (μ * t) := by
    intro t ht hkt
    set a := t * a' / μ
    set b := t * a'
    have ha : 0 < a := div_pos (mul_pos ht ha'0) hμ0
    have hab : a < b := by
      rw [div_lt_iff₀ hμ0]
      exact lt_mul_of_one_lt_right (by positivity) hμ1
    haveI : (ae (volume.restrict (Ioo a b))).NeBot := by
      rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
      linarith
    obtain ⟨s, hs, hsI⟩ := ((key a b ha hab).and (ae_restrict_mem measurableSet_Ioo)).exists
    have hs0 : 0 < s := ha.trans hsI.1
    have h1 : s / a' < t := by rw [div_lt_iff₀ ha'0]; exact hsI.2
    have h2 : t / μ < s / a' := by
      rw [div_lt_div_iff₀ hμ0 ha'0]
      have := hsI.1
      rw [div_lt_iff₀ hμ0] at this
      linarith
    have hk1' : k t ≤ k (s / a') := hk_anti (div_pos hs0 ha'0) ht h1.le
    have hsa : s / a'' = ρ * (s / a') := by
      rw [hρ]; field_simp
    have h3 : μ * t ≤ s / a'' := by
      rw [hsa, ← hμμ, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hμ0.le
      rw [div_lt_iff₀ hμ0] at h2
      linarith
    calc k r₀ ≤ k t := hkt
      _ ≤ k (s / a') := hk1'
      _ = k (s / a'') := hs
      _ ≤ k (μ * t) := hk_anti (show (0 : ℝ) < μ * t from mul_pos hμ0 ht) (div_pos hs0 ha''0) h3
  have hall : ∀ n : ℕ, k r₀ ≤ k (μ ^ n * r₀) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_comm (μ ^ n) μ, mul_assoc]
      exact hstep _ (by positivity) ih
  have hlow : ∀ r : ℝ, 0 < r → k r₀ ≤ k r := by
    intro r hr
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / r₀) hμ1
    have hle : r ≤ μ ^ n * r₀ := by
      rw [div_lt_iff₀ hr₀] at hn
      exact hn.le
    exact (hall n).trans (hk_anti hr (show (0 : ℝ) < μ ^ n * r₀ by positivity) hle)
  refine hk1 (eq_top_iff.2 ?_)
  calc ⊤ = ENNReal.ofReal (k r₀) * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal r⁻¹ := by
        rw [lintegral_Ioi_one_inv, ENNReal.mul_top (by simp [hκ])]
    _ = ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r₀ / r) := by
        rw [← lintegral_const_mul _ measurable_inv.ennreal_ofReal]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        rw [← ENNReal.ofReal_mul hκ.le, div_eq_mul_inv]
    _ ≤ ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_))
        have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hlow r hr0) hr0.le)

/-- **`prop:similarity-line-family`(3)**, not shape-blind at index `0`, the measures (blind review
R4-1: from the hypotheses on `k` alone): if `Σ ∈ PD(d)` is not a multiple of `I`, `L_Σ` is not
rotation invariant (in particular when `k(0+) < ∞`). -/
theorem line_family_levy_not_shape_blind (hd : 2 ≤ d) (k : ℝ → ℝ)
    (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk_anti : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) (_hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    ∀ S : Mat d, S.PosDef → (¬ ∃ c : ℝ, S = c • (1 : Mat d)) →
      ¬ IsRotationInvariant (lineLevy k S) := by
  haveI : NeZero d := ⟨by omega⟩
  intro S hS hns hrot
  obtain ⟨hkIm, -, hkIe⟩ := indicator_Ioi_props hk_anti
  obtain ⟨up, um, hup, hum, hlt⟩ := exists_quad_lt_of_not_scalar hS.isHermitian hns
  have hum0 : um ≠ 0 := by rintro rfl; simp at hum
  have hlm : 0 < quad S um := quad_pos hS hum0
  set m' := (2 * quad S up + quad S um) / 3 with hm'
  set m'' := (quad S up + 2 * quad S um) / 3 with hm''
  have hm''0 : 0 < m'' := by rw [hm'']; linarith
  have hmm : m'' < m' := by rw [hm', hm'']; linarith
  set R : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (up - um))ᗮ.reflection with hR
  have hRup : R up = um := Submodule.reflection_sub (hup.trans hum.symm)
  have hRR : ∀ x, R (R x) = x := fun x => Submodule.reflection_reflection _ x
  set U : Set (Rd d) := {u | m' < quad S u ∧ quad S (R u) < m''} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_quad_vec S)).inter
      (isOpen_lt ((continuous_quad_vec S).comp R.continuous) continuous_const)
  have hUs : ∀ v, -v ∈ U ↔ v ∈ U := fun v => by
    simp only [hU, mem_setOf_eq, quad_neg_vec, map_neg]
  have hupU : up ∈ U := ⟨by rw [hm']; linarith, by rw [hRup, hm'']; linarith⟩
  have hσU : 0 < normSphere d U := normSphere_pos_of_isOpen (by omega) hUo hup hupU
  have hσU' : normSphere d U ≠ ⊤ := normSphere_ne_top (by omega) U
  have hRU : normSphere d (R ⁻¹' U) = normSphere d U := by
    conv_rhs => rw [← normSphere_map_isometry R]
    rw [Measure.map_apply R.continuous.measurable hUo.measurableSet]
  have hRUo : IsOpen (R ⁻¹' U) := hUo.preimage R.continuous
  have hRUs : ∀ v, -v ∈ R ⁻¹' U ↔ v ∈ R ⁻¹' U := fun v => by
    simp only [mem_preimage, map_neg, hUs]
  /- The key: `k(s/√m') = k(s/√m'')` for almost every `s`. -/
  refine lineProfile_dilation_contra hk_nonneg hk_anti hk_ne hk1 hm''0 hmm fun a b ha hab => ?_
  set I : ℝ → ℝ≥0∞ := fun q => ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s) with hI
  have hImono : ∀ q q' : ℝ, 0 < q → q ≤ q' → I q ≤ I q' := by
    intro q q' hq hqq
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => ?_))
    have hs0 : 0 < s := ha.trans hs.1
    have h1 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
    have h2 : Real.sqrt q ≤ Real.sqrt q' := Real.sqrt_le_sqrt hqq
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hs0.le)
    exact hk_anti (div_pos hs0 (h1.trans_le h2)) (div_pos hs0 h1)
      (div_le_div_of_nonneg_left hs0.le h1 h2)
  have hconst : ∀ (V : Set (Rd d)), MeasurableSet V → ∀ c : ℝ≥0∞,
      ∫⁻ u, 2 * V.indicator (fun _ => c) u ∂(normSphere d) = 2 * normSphere d V * c := by
    intro V hV c
    rw [lintegral_const_mul _ (measurable_const.indicator hV), lintegral_indicator_const hV,
      mul_assoc, mul_comm c]
  have hlow : 2 * normSphere d U * I m' ≤ lineLevy k S (lineSector U a b) := by
    rw [lineLevy_sector hk_anti hS hUo.measurableSet hUs ha.le, ← hconst U hUo.measurableSet]
    refine lintegral_mono fun u => ?_
    by_cases hu : u ∈ U
    · rw [indicator_of_mem hu, indicator_of_mem hu]
      exact mul_le_mul_right (hImono _ _ (hm''0.trans hmm) hu.1.le) _
    · rw [indicator_of_notMem hu, indicator_of_notMem hu]
  have hRE : lineLevy k S (lineSector (R ⁻¹' U) a b) = lineLevy k S (lineSector U a b) := by
    have h := hrot (isoMat R) (isoMat_mem_orthSet R)
    rw [← preimage_lineSector]
    conv_rhs => rw [← h]
    rw [push, Measure.map_apply (lin (isoMat R)).continuous.measurable
      (measurableSet_lineSector hUo.measurableSet a b), lin_isoMat]
    rfl
  have hup2 : lineLevy k S (lineSector (R ⁻¹' U) a b) ≤ 2 * normSphere d U * I m'' := by
    rw [lineLevy_sector hk_anti hS hRUo.measurableSet hRUs ha.le, ← hRU,
      ← hconst _ hRUo.measurableSet]
    refine lintegral_mono fun u => ?_
    by_cases hu : u ∈ R ⁻¹' U
    · rw [indicator_of_mem hu, indicator_of_mem hu]
      have hq : quad S u < m'' := by
        have := hu.2
        rwa [hRR] at this
      have hu0 : u ≠ 0 := by
        rintro rfl
        have h0 := hu.1
        simp only [map_zero] at h0
        rw [show quad S 0 = 0 by simp [quad]] at h0
        linarith [hm''0, hmm]
      exact mul_le_mul_right (hImono _ _ (quad_pos hS hu0) hq.le) _
    · rw [indicator_of_notMem hu, indicator_of_notMem hu]
  have hfin : I m'' ≠ ⊤ := by
    have hb : ∀ s ∈ Ioo a b, ENNReal.ofReal (k (s / Real.sqrt m'') / s) ≤
        ENNReal.ofReal (k (a / Real.sqrt m'') / a) := by
      intro s hs
      have hs0 : 0 < s := ha.trans hs.1
      have h1 : 0 < Real.sqrt m'' := Real.sqrt_pos.2 hm''0
      refine ENNReal.ofReal_le_ofReal ?_
      have hk' : k (s / Real.sqrt m'') ≤ k (a / Real.sqrt m'') :=
        hk_anti (div_pos ha h1) (div_pos hs0 h1) (div_le_div_of_nonneg_right hs.1.le h1.le)
      have hk0' : 0 ≤ k (s / Real.sqrt m'') := hk_nonneg _ (div_pos hs0 h1)
      calc k (s / Real.sqrt m'') / s ≤ k (a / Real.sqrt m'') / s :=
            div_le_div_of_nonneg_right hk' hs0.le
        _ ≤ k (a / Real.sqrt m'') / a :=
            div_le_div_of_nonneg_left (hk0'.trans hk') ha hs.1.le
    refine ne_top_of_le_ne_top (b := ∫⁻ _s in Ioo a b, ENNReal.ofReal (k (a / Real.sqrt m'') / a))
      ?_ (setLIntegral_mono measurable_const hb)
    rw [setLIntegral_const, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hle : I m' ≤ I m'' := by
    have h := hlow.trans (hRE ▸ hup2)
    have hc0 : 2 * normSphere d U ≠ 0 := mul_ne_zero (by norm_num) hσU.ne'
    have hct : 2 * normSphere d U ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hσU'
    exact (ENNReal.mul_le_mul_iff_right hc0 hct).1 h
  /- The two integrands: pointwise `≥`, integrals `≤`. -/
  have h1 : 0 < Real.sqrt m'' := Real.sqrt_pos.2 hm''0
  have h2 : Real.sqrt m'' ≤ Real.sqrt m' := Real.sqrt_le_sqrt hmm.le
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ENNReal.ofReal (k (s / Real.sqrt m'') / s) ≤
      ENNReal.ofReal (k (s / Real.sqrt m') / s) := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => ?_)
    have hs0 : 0 < s := ha.trans hs.1
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hk_anti (div_pos hs0 (h1.trans_le h2))
      (div_pos hs0 h1) (div_le_div_of_nonneg_left hs0.le h1 h2)) hs0.le)
  have hmeas : AEMeasurable (fun s => ENNReal.ofReal (k (s / Real.sqrt m') / s))
      (volume.restrict (Ioo a b)) := by
    have hmI : Measurable fun s : ℝ =>
        ENNReal.ofReal ((Ioi (0 : ℝ)).indicator k (s / Real.sqrt m') / s) :=
      ((hkIm.comp (measurable_id.div_const (Real.sqrt m'))).div measurable_id).ennreal_ofReal
    refine hmI.aemeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => ?_)
    have hs0 : 0 < s := ha.trans hs.1
    simp only
    rw [hkIe _ (div_pos hs0 (h1.trans_le h2))]
  have heq := ae_eq_of_ae_le_of_lintegral_le hpt hfin hmeas hle
  filter_upwards [heq, ae_restrict_mem measurableSet_Ioo] with s hs hsI
  have hs0 : 0 < s := ha.trans hsI.1
  have hn1 : 0 ≤ k (s / Real.sqrt m'') / s := div_nonneg (hk_nonneg _ (div_pos hs0 h1)) hs0.le
  have hn2 : 0 ≤ k (s / Real.sqrt m') / s :=
    div_nonneg (hk_nonneg _ (div_pos hs0 (h1.trans_le h2))) hs0.le
  have := (ENNReal.ofReal_eq_ofReal_iff hn1 hn2).1 hs
  field_simp at this
  exact this.symm

/-! ## The exponent `ψ_Σ(ω) = ∫ σ̄(du) ψ_ℓ(q_Σ(u)^{1/2}⟨ω,u⟩)` -/

/-- **`ψ_ℓ(τ) := ∫ (1 - cos τr) ℓ(dr)`**, `ℝ≥0∞`-valued. -/
noncomputable def linePsi (k : ℝ → ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r, ENNReal.ofReal (1 - Real.cos (r * τ)) ∂(lineProfileMeasure k)

theorem linePsi_le {k : ℝ → ℝ} (τ : ℝ) :
    linePsi k τ ≤ ENNReal.ofReal (2 + τ ^ 2) *
      ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1) ∂(lineProfileMeasure k) := by
  rw [linePsi, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  -- `1 - cos(rτ) ≤ (2 + τ²)(r² ∧ 1)`: the shared library's `one_sub_cos_le` at `(τ, r)`
  rw [mul_comm r τ, min_comm]
  exact ENNReal.ofReal_le_ofReal (ScaleSpace.one_sub_cos_le τ r)

theorem linePsi_ne_top {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (τ : ℝ) : linePsi k τ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lineProfile_min_ne_top hk hk0 hk1)) (linePsi_le τ)

theorem linePsi_neg (k : ℝ → ℝ) (τ : ℝ) : linePsi k (-τ) = linePsi k τ := by
  unfold linePsi
  simp_rw [mul_neg, Real.cos_neg]

/-- **`ψ_ℓ` along a ray**: `ψ_ℓ(τ) = ∫_0^∞ 2(1 - cos s) k(s/τ) ds/s` for `τ > 0`. -/
theorem linePsi_eq {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {τ : ℝ} (hτ : 0 < τ) :
    linePsi k τ = ∫⁻ s in Ioi (0 : ℝ), 2 * ENNReal.ofReal (1 - Real.cos s) *
      ENNReal.ofReal (k (s / τ) / s) := by
  have h := lintegral_lineProfile_scale hk (pow_pos hτ 2) (g := fun x => ENNReal.ofReal
    (1 - Real.cos x)) (by fun_prop)
  rw [Real.sqrt_sq hτ.le] at h
  rw [linePsi, h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [Real.cos_neg, ← two_mul]

/-- **`ψ_ℓ` is nondecreasing on `[0,∞)`.** -/
theorem linePsi_mono {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {τ τ' : ℝ} (hτ : 0 ≤ τ)
    (hττ : τ ≤ τ') : linePsi k τ ≤ linePsi k τ' := by
  rcases hτ.eq_or_lt with rfl | hτ0
  · rw [linePsi]
    simp
  rw [linePsi_eq hk hτ0, linePsi_eq hk (hτ0.trans_le hττ)]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))
  have hs0 : 0 < s := hs
  gcongr _ * ENNReal.ofReal ?_
  refine div_le_div_of_nonneg_right ?_ hs0.le
  exact hk (div_pos hs0 (hτ0.trans_le hττ)) (div_pos hs0 hτ0)
    (div_le_div_of_nonneg_left hs0.le hτ0 hττ)

theorem linePsi_mono_abs {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {τ τ' : ℝ} (h : |τ| ≤ |τ'|) :
    linePsi k τ ≤ linePsi k τ' := by
  have h1 : linePsi k τ = linePsi k |τ| := by
    rcases abs_choice τ with h' | h' <;> rw [h']
    rw [linePsi_neg]
  have h2 : linePsi k τ' = linePsi k |τ'| := by
    rcases abs_choice τ' with h' | h' <;> rw [h']
    rw [linePsi_neg]
  rw [h1, h2]
  exact linePsi_mono hk (abs_nonneg τ) h

/-- **Doubling**: `ψ_ℓ(2τ) ≤ 4ψ_ℓ(τ)`. -/
theorem linePsi_two_mul (k : ℝ → ℝ) (τ : ℝ) : linePsi k (2 * τ) ≤ 4 * linePsi k τ := by
  rw [linePsi, linePsi, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun r => ?_
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
    show r * (2 * τ) = 2 * (r * τ) by ring]
  exact ENNReal.ofReal_le_ofReal (one_sub_cos_two_mul_le (r * τ))

/-- **`ψ_ℓ(aτ) ≥ (a²/4) ψ_ℓ(τ)`** for `0 < a ≤ 1`, `τ ≥ 0`: with `2^{-n} < a ≤ 2^{1-n}`,
`ψ_ℓ(τ) ≤ 4ⁿψ_ℓ(2^{-n}τ) ≤ 4a^{-2}ψ_ℓ(aτ)`. -/
theorem linePsi_mul_ge {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {a τ : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hτ : 0 ≤ τ) :
    ENNReal.ofReal (a ^ 2 / 4) * linePsi k τ ≤ linePsi k (a * τ) := by
  have hpow : ∀ n : ℕ, linePsi k τ ≤ 4 ^ n * linePsi k ((2 : ℝ)⁻¹ ^ n * τ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [pow_succ, mul_assoc]
      refine mul_le_mul_right ?_ _
      have h2 := linePsi_two_mul k ((2 : ℝ)⁻¹ ^ (n + 1) * τ)
      have he : 2 * ((2 : ℝ)⁻¹ ^ (n + 1) * τ) = (2 : ℝ)⁻¹ ^ n * τ := by
        rw [pow_succ]; field_simp
      rwa [he] at h2
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, (2 : ℝ)⁻¹ ^ n < a ∧ a ≤ 2 * (2 : ℝ)⁻¹ ^ n := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha (by norm_num : (2 : ℝ)⁻¹ < 1)
    classical
    let P : ℕ → Prop := fun m => (2 : ℝ)⁻¹ ^ m < a
    have hP : ∃ m, P m := ⟨n, hn⟩
    refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
    by_cases h0 : Nat.find hP = 0
    · rw [h0, pow_zero, mul_one]; linarith
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have := Nat.find_min hP (show m < Nat.find hP by omega)
      simp only [P, not_lt] at this
      rw [hm, pow_succ, mul_comm _ (2 : ℝ)⁻¹, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
        one_mul]
      exact this
  have hmono : linePsi k ((2 : ℝ)⁻¹ ^ n * τ) ≤ linePsi k (a * τ) :=
    linePsi_mono hk (by positivity) (mul_le_mul_of_nonneg_right hn1.le hτ)
  have h4 : ENNReal.ofReal (a ^ 2 / 4) * 4 ^ n ≤ 1 := by
    have h2n : a * 2 ^ n ≤ 2 := by
      have := hn2
      rw [inv_pow] at this
      rw [← le_div_iff₀ (by positivity)]
      calc a ≤ 2 * (2 ^ n)⁻¹ := this
        _ = 2 / 2 ^ n := by ring
    rw [show (4 : ℝ≥0∞) ^ n = ENNReal.ofReal (4 ^ n) by simp, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ a * 2 ^ n := by positivity
    nlinarith
  calc ENNReal.ofReal (a ^ 2 / 4) * linePsi k τ
      ≤ ENNReal.ofReal (a ^ 2 / 4) * (4 ^ n * linePsi k ((2 : ℝ)⁻¹ ^ n * τ)) :=
        mul_le_mul_right (hpow n) _
    _ = (ENNReal.ofReal (a ^ 2 / 4) * 4 ^ n) * linePsi k ((2 : ℝ)⁻¹ ^ n * τ) := by ring
    _ ≤ 1 * linePsi k (a * τ) := mul_le_mul' h4 hmono
    _ = linePsi k (a * τ) := one_mul _

/-- **The exponent of `L_Σ`**: `ψ_Σ(ω) = ∫ σ̄(du) ψ_ℓ(q_Σ(u)^{1/2}⟨ω,u⟩)`. -/
theorem levyExpL_lineLevy (k : ℝ → ℝ) (S : Mat d) (ω : Rd d) :
    levyExpL (lineLevy k S) ω =
      ∫⁻ u, linePsi k (Real.sqrt (quad S u) * ⟪ω, u⟫) ∂(normSphere d) := by
  rw [levyExpL, lintegral_lineLevy k S (by fun_prop) (by simp)]
  refine lintegral_congr fun u => ?_
  rw [linePsi]
  refine lintegral_congr fun r => ?_
  rw [real_inner_smul_right]
  ring_nf

/-- `q_Σ(u) ≥ λ_max(Σ)⟨v,u⟩²` for a unit eigenvector `v` of `λ_max(Σ)`, `Σ ∈ PSD(d)`. -/
theorem quad_ge_top {S : Mat d} (hS : S.PosSemidef) {v : Rd d} (hv : ‖v‖ = 1) {t : ℝ}
    (hSv : lin S v = t • v) (u : Rd d) : t * ⟪v, u⟫ ^ 2 ≤ quad S u := by
  set c := ⟪v, u⟫
  set w := u - c • v with hw
  have hu : u = c • v + w := by rw [hw]; abel
  have hvw : ⟪v, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]; ring
  have hcross : ⟪c • v, lin S w⟫ = 0 := by
    have hT : Sᵀ = S := by
      have := hS.isHermitian.eq
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [real_inner_smul_left, ← hT, ← inner_lin_left, hSv, real_inner_smul_left, hvw]; ring
  have hqv : quad S (c • v) = t * c ^ 2 := by
    rw [quad_smul_vec, quad, hSv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]; ring
  rw [hu, quad_add_vec hS.isHermitian, hcross, hqv]
  have := quad_nonneg hS w
  linarith

/-- **`prop:similarity-line-family`(2), the exponent spread**: `es(ψ_Σ) ≤ 4d(d+2)` for
`Σ ∈ PD(d)`. With `t := λ_max(Σ)` and `v` a unit eigenvector, `t⟨v,u⟩² ≤ q_Σ(u) ≤ t` on the sphere,
so `ψ_Σ(Rω) ≤ ψ_ℓ(√t|ω|)` and, by `ψ_ℓ(aτ) ≥ (a²/4)ψ_ℓ(τ)` and the fourth moments of `σ̄`,
`ψ_Σ(ω) ≥ ψ_ℓ(√t|ω|)/(4d(d+2))`. -/
theorem lineLevy_expSpread_le (hd : 2 ≤ d) {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {S : Mat d} (hS : S.PosDef) :
    expSpread (levyExp (lineLevy k S)) ≤ ENNReal.ofReal (4 * d * ((d : ℝ) + 2)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := isProbabilityMeasure_normSphere (d := d) hd1
  have hL := isLevyMeasure_lineLevy hk hk0 hk1 hS.posSemidef
  obtain ⟨v, hv, hSv⟩ := exists_unit_eigvec_eigUp hS.isHermitian (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hS.isHermitian] at hSv
  set t := lamMax S with ht
  have ht0 : 0 < t := lamMax_pos hS
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set K : ℝ := 4 * d * ((d : ℝ) + 2) with hK
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  /- The upper bound. -/
  have hup : ∀ ω : Rd d, levyExpL (lineLevy k S) ω ≤ linePsi k (Real.sqrt t * ‖ω‖) := by
    intro ω
    rw [levyExpL_lineLevy]
    calc ∫⁻ u, linePsi k (Real.sqrt (quad S u) * ⟪ω, u⟫) ∂normSphere d
        ≤ ∫⁻ _u, linePsi k (Real.sqrt t * ‖ω‖) ∂normSphere d := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_normSphere_norm] with u hu
          refine linePsi_mono_abs hk ?_
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
          refine mul_le_mul (Real.sqrt_le_sqrt (quad_le_lamMax hS.isHermitian hu)) ?_
            (abs_nonneg _) (Real.sqrt_nonneg _)
          have := abs_real_inner_le_norm ω u
          rwa [hu, mul_one] at this
      _ = linePsi k (Real.sqrt t * ‖ω‖) := by rw [lintegral_const, measure_univ, mul_one]
  /- The lower bound. -/
  have hlow : ∀ ω : Rd d, ENNReal.ofReal K⁻¹ * linePsi k (Real.sqrt t * ‖ω‖) ≤
      levyExpL (lineLevy k S) ω := by
    intro ω
    rcases eq_or_ne ω 0 with rfl | hω
    · simp [linePsi]
    have hω0 : 0 < ‖ω‖ := norm_pos_iff.2 hω
    set w := ‖ω‖⁻¹ • ω with hwdef
    have hwn : ‖w‖ = 1 := by
      rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hω0.ne']
    set T := Real.sqrt t * ‖ω‖ with hT
    have hT0 : 0 ≤ T := by positivity
    rw [levyExpL_lineLevy]
    have hpt : ∀ᵐ u ∂normSphere d, ENNReal.ofReal ((⟪v, u⟫ ^ 2 * ⟪w, u⟫ ^ 2) / 4) * linePsi k T ≤
        linePsi k (Real.sqrt (quad S u) * ⟪ω, u⟫) := by
      filter_upwards [ae_normSphere_norm] with u hu
      have hvu : |⟪v, u⟫| ≤ 1 := by
        have := abs_real_inner_le_norm v u; rwa [hv, hu, one_mul] at this
      have hwu : |⟪w, u⟫| ≤ 1 := by
        have := abs_real_inner_le_norm w u; rwa [hwn, hu, one_mul] at this
      set a := |⟪v, u⟫| * |⟪w, u⟫| with ha
      have ha0 : 0 ≤ a := by positivity
      have ha1 : a ≤ 1 := by
        calc a ≤ 1 * 1 := mul_le_mul hvu hwu (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hsq : a ^ 2 = ⟪v, u⟫ ^ 2 * ⟪w, u⟫ ^ 2 := by rw [ha, mul_pow, sq_abs, sq_abs]
      have hmono : linePsi k (a * T) ≤ linePsi k (Real.sqrt (quad S u) * ⟪ω, u⟫) := by
        refine linePsi_mono_abs hk ?_
        rw [abs_of_nonneg (mul_nonneg ha0 hT0), abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hq : Real.sqrt t * |⟪v, u⟫| ≤ Real.sqrt (quad S u) := by
          rw [← Real.sqrt_sq (abs_nonneg ⟪v, u⟫), ← Real.sqrt_mul ht0.le, sq_abs]
          exact Real.sqrt_le_sqrt (quad_ge_top hS.posSemidef hv hSv u)
        have hωu : ‖ω‖ * |⟪w, u⟫| = |⟪ω, u⟫| := by
          rw [hwdef, real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.2 hω0), ← mul_assoc,
            mul_inv_cancel₀ hω0.ne', one_mul]
        calc a * T = (Real.sqrt t * |⟪v, u⟫|) * (‖ω‖ * |⟪w, u⟫|) := by rw [ha, hT]; ring
          _ ≤ Real.sqrt (quad S u) * (‖ω‖ * |⟪w, u⟫|) :=
            mul_le_mul_of_nonneg_right hq (by positivity)
          _ = Real.sqrt (quad S u) * |⟪ω, u⟫| := by rw [hωu]
      rcases ha0.eq_or_lt with ha' | ha'
      · rw [← hsq, ← ha', zero_pow two_ne_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
        exact bot_le
      · rw [← hsq]
        exact (linePsi_mul_ge hk ha' ha1 hT0).trans hmono
    refine le_trans ?_ (lintegral_mono_ae hpt)
    rw [lintegral_mul_const _ (by fun_prop)]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_normSphere hd1 (by fun_prop)).div_const 4)
      (ae_of_all _ fun u => by positivity), integral_div,
      integral_inner_sq_mul_inner_sq hd hv w, hwn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hK, inv_eq_one_div, div_div]
    have hpos : (0 : ℝ) < d * (d + 2) * 4 := by positivity
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith [sq_nonneg ⟪v, w⟫]
  refine expSpread_le hK1 fun R hR ω => ?_
  have hR' : levyExpL (lineLevy k S) (lin R ω) ≤ ENNReal.ofReal K * levyExpL (lineLevy k S) ω := by
    calc levyExpL (lineLevy k S) (lin R ω) ≤ linePsi k (Real.sqrt t * ‖lin R ω‖) := hup _
      _ = linePsi k (Real.sqrt t * ‖ω‖) := by rw [norm_lin_of_orth hR]
      _ = ENNReal.ofReal K * (ENNReal.ofReal K⁻¹ * linePsi k (Real.sqrt t * ‖ω‖)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal K * levyExpL (lineLevy k S) ω := mul_le_mul_right (hlow ω) _
  unfold levyExp
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hL.levyExpL_ne_top ω)) hR'
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

/-! ## The moment matrices -/

/-- **`G_s(τ) := ∫ (τr² ∧ s²) ℓ(dr)`**. -/
noncomputable def lineG (k : ℝ → ℝ) (s τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r, ENNReal.ofReal (min (r ^ 2 * τ) (s ^ 2)) ∂(lineProfileMeasure k)

theorem lineG_mono (k : ℝ → ℝ) (s : ℝ) {τ τ' : ℝ} (h : τ ≤ τ') : lineG k s τ ≤ lineG k s τ' :=
  lintegral_mono fun r => ENNReal.ofReal_le_ofReal
    (min_le_min (mul_le_mul_of_nonneg_left h (sq_nonneg r)) le_rfl)

theorem lineG_mul_ge (k : ℝ → ℝ) (s : ℝ) {a τ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (_hτ : 0 ≤ τ) :
    ENNReal.ofReal a * lineG k s τ ≤ lineG k s (a * τ) := by
  rw [lineG, lineG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  rw [← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_min_of_nonneg _ _ ha]
  refine min_le_min (le_of_eq (by ring)) ?_
  calc a * s ^ 2 ≤ 1 * s ^ 2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)
    _ = s ^ 2 := one_mul _

theorem lineG_ne_top {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (s : ℝ) {τ : ℝ} (_hτ : 0 ≤ τ) :
    lineG k s τ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := max τ (s ^ 2)))
    (lineProfile_min_ne_top hk hk0 hk1)) ?_
  rw [lineG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  rw [← ENNReal.ofReal_mul (le_max_of_le_right (sq_nonneg s))]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_or_gt (r ^ 2) 1 with h | h
  · rw [min_eq_left h]
    calc min (r ^ 2 * τ) (s ^ 2) ≤ r ^ 2 * τ := min_le_left _ _
      _ ≤ r ^ 2 * max τ (s ^ 2) := mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg r)
      _ = max τ (s ^ 2) * r ^ 2 := mul_comm _ _
  · rw [min_eq_right h.le, mul_one]
    exact (min_le_right _ _).trans (le_max_right _ _)

theorem lineG_pos {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) :
    0 < lineG k s τ := by
  obtain ⟨r₀, hr₀, hkr₀⟩ := hk_ne
  have hκ : 0 < k r₀ := lt_of_le_of_ne (hk_nonneg r₀ hr₀) (Ne.symm hkr₀)
  set m : ℝ := min ((r₀ / 2) ^ 2 * τ) (s ^ 2) with hm
  have hm0 : 0 < m := by positivity
  rw [lineG, lintegral_lineProfile hk (by fun_prop)]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (m * (k r₀ / r₀)) * volume (Ioo (r₀ / 2) r₀) := by
        rw [Real.volume_Ioo]
        refine ENNReal.mul_pos (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ?_
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
    _ = ∫⁻ _r in Ioo (r₀ / 2) r₀, ENNReal.ofReal (m * (k r₀ / r₀)) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo (r₀ / 2) r₀, (ENNReal.ofReal (min (r ^ 2 * τ) (s ^ 2)) +
          ENNReal.ofReal (min ((-r) ^ 2 * τ) (s ^ 2))) * ENNReal.ofReal (k r / r) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => ?_))
        have hr0 : 0 < r := by linarith [hr.1]
        rw [ENNReal.ofReal_mul hm0.le]
        refine mul_le_mul' (le_add_right (ENNReal.ofReal_le_ofReal ?_)) (ENNReal.ofReal_le_ofReal ?_)
        · refine min_le_min (mul_le_mul_of_nonneg_right ?_ hτ.le) le_rfl
          exact pow_le_pow_left₀ (by positivity) hr.1.le 2
        · calc k r₀ / r₀ ≤ k r₀ / r := div_le_div_of_nonneg_left hκ.le hr0 hr.2.le
            _ ≤ k r / r := div_le_div_of_nonneg_right (hk hr0 hr₀ hr.2.le) hr0.le
    _ ≤ _ := lintegral_mono_set (fun r hr => (show (0 : ℝ) < r by linarith [hr.1]))

/-- **The moment matrices of `L_Σ`**: `⟨x, 𝓜_s(L_Σ)x⟩ = ∫ σ̄(du) ⟨x,u⟩² G_s(q_Σ(u))`. -/
theorem ofReal_quad_momentMatrix_lineLevy {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {S : Mat d} (hS : S.PosSemidef)
    (s : ℝ) (x : Rd d) :
    ENNReal.ofReal (quad (momentMatrix s (lineLevy k S)) x) =
      ∫⁻ u, ENNReal.ofReal (⟪x, u⟫ ^ 2) * lineG k s (quad S u) ∂normSphere d := by
  have hL := isLevyMeasure_lineLevy hk hk0 hk1 hS
  rw [quad_momentMatrix hL, ofReal_integral_eq_lintegral_ofReal (integrable_moment_quad hL s x)
    (ae_of_all _ fun y => by positivity),
    lintegral_lineLevy k S (Measurable.div (by fun_prop) (by fun_prop)).ennreal_ofReal (by simp)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_normSphere_norm] with u hu
  rw [lineG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hq := quad_nonneg hS u
  have hn : ‖(r * Real.sqrt (quad S u)) • u‖ ^ 2 = r ^ 2 * quad S u := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hq]
  rw [hn, real_inner_smul_right, mul_pow, mul_pow, Real.sq_sqrt hq]
  rcases eq_or_ne (r ^ 2 * quad S u) 0 with h0 | h0
  · rw [h0, min_eq_left (sq_nonneg s)]
    simp
  · have hr : r ≠ 0 := fun h => h0 (by rw [h]; ring)
    have hq0 : quad S u ≠ 0 := fun h => h0 (by rw [h]; ring)
    field_simp

/-- **`prop:similarity-line-family`(2), the moments**: `cond 𝓜_s(L_Σ) ≤ d + 2` for `Σ ∈ PD(d)`
and `s > 0`: with `t := λ_max(Σ)`, `G_s(t)⟨v,u⟩² ≤ G_s(q_Σ(u)) ≤ G_s(t)` on the sphere, and the
second and fourth moments of `σ̄` give `G_s(t)|x|²/(d(d+2)) ≤ ⟨x, 𝓜_s x⟩ ≤ G_s(t)|x|²/d`. -/
theorem lineLevy_condNum_le (hd : 2 ≤ d) {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {S : Mat d} (hS : S.PosDef)
    {s : ℝ} (hs : 0 < s) :
    condNum (momentMatrix s (lineLevy k S)) ≤ ENNReal.ofReal ((d : ℝ) + 2) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := isProbabilityMeasure_normSphere (d := d) hd1
  have hL := isLevyMeasure_lineLevy hk hk0 hk1 hS.posSemidef
  obtain ⟨v, hv, hSv⟩ := exists_unit_eigvec_eigUp hS.isHermitian (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hS.isHermitian] at hSv
  set t := lamMax S with ht
  have ht0 : 0 < t := lamMax_pos hS
  set G := lineG k s t with hG
  have hGt : G ≠ ⊤ := lineG_ne_top hk hk0 hk1 s ht0.le
  have hG0 : 0 < G := lineG_pos hk_nonneg hk hk_ne hs ht0
  set g := G.toReal with hg
  have hg0 : 0 < g := ENNReal.toReal_pos hG0.ne' hGt
  have hGg : G = ENNReal.ofReal g := (ENNReal.ofReal_toReal hGt).symm
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set M := momentMatrix s (lineLevy k S) with hM
  have hMh : M.IsHermitian := momentMatrix_isHermitian s _
  have hMpsd : M.PosSemidef := momentMatrix_posSemidef hL s
  have hup : ∀ x : Rd d, quad M x ≤ g / d * ‖x‖ ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal (quad M x) ≤ ENNReal.ofReal (g / d * ‖x‖ ^ 2) := by
      rw [hM, ofReal_quad_momentMatrix_lineLevy hk hk0 hk1 hS.posSemidef]
      calc ∫⁻ u, ENNReal.ofReal (⟪x, u⟫ ^ 2) * lineG k s (quad S u) ∂normSphere d
          ≤ ∫⁻ u, ENNReal.ofReal (⟪x, u⟫ ^ 2) * G ∂normSphere d := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_normSphere_norm] with u hu
            exact mul_le_mul_right (lineG_mono k s (quad_le_lamMax hS.isHermitian hu)) _
        _ = ENNReal.ofReal (g / d * ‖x‖ ^ 2) := by
            rw [lintegral_mul_const _ (by fun_prop), ← ofReal_integral_eq_lintegral_ofReal
              (integrable_normSphere hd1 (by fun_prop)) (ae_of_all _ fun u => by positivity),
              integral_inner_sq hd1, hGg, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hlow : ∀ x : Rd d, g / (d * (d + 2)) * ‖x‖ ^ 2 ≤ quad M x := by
    intro x
    have h1 : ENNReal.ofReal (g / (d * (d + 2)) * ‖x‖ ^ 2) ≤ ENNReal.ofReal (quad M x) := by
      rw [hM, ofReal_quad_momentMatrix_lineLevy hk hk0 hk1 hS.posSemidef]
      calc ENNReal.ofReal (g / (d * (d + 2)) * ‖x‖ ^ 2)
          ≤ ENNReal.ofReal (g * ((‖x‖ ^ 2 + 2 * ⟪v, x⟫ ^ 2) / (d * (d + 2)))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_div_assoc', div_mul_eq_mul_div]
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            nlinarith [sq_nonneg ⟪v, x⟫]
        _ = ∫⁻ u, ENNReal.ofReal (⟪x, u⟫ ^ 2) * (ENNReal.ofReal (⟪v, u⟫ ^ 2) * G)
              ∂normSphere d := by
            rw [← integral_inner_sq_mul_inner_sq hd hv x, ENNReal.ofReal_mul hg0.le,
              ofReal_integral_eq_lintegral_ofReal (integrable_normSphere hd1 (by fun_prop))
                (ae_of_all _ fun u => by positivity), ← hGg, mul_comm G,
              ← lintegral_mul_const _ (by fun_prop)]
            refine lintegral_congr fun u => ?_
            rw [ENNReal.ofReal_mul (sq_nonneg _)]
            ring
        _ ≤ ∫⁻ u, ENNReal.ofReal (⟪x, u⟫ ^ 2) * lineG k s (quad S u) ∂normSphere d := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_normSphere_norm] with u hu
            refine mul_le_mul_right ?_ _
            have hvu : ⟪v, u⟫ ^ 2 ≤ 1 := by
              have := abs_real_inner_le_norm v u
              rw [hv, hu, one_mul] at this
              rw [← sq_abs]
              exact pow_le_one₀ (abs_nonneg _) this
            calc ENNReal.ofReal (⟪v, u⟫ ^ 2) * G ≤ lineG k s (⟪v, u⟫ ^ 2 * t) :=
                  lineG_mul_ge k s (sq_nonneg _) hvu ht0.le
              _ ≤ lineG k s (quad S u) := by
                  refine lineG_mono k s ?_
                  rw [mul_comm]
                  exact quad_ge_top hS.posSemidef hv hSv u
    exact (ENNReal.ofReal_le_ofReal_iff (quad_nonneg hMpsd x)).1 h1
  have ha : 0 < g / (d * (d + 2)) := by positivity
  have h1 : loewnerLE ((g / (d * (d + 2))) • (1 : Mat d)) M := by
    unfold loewnerLE
    refine posSemidef_of_quad_nonneg (hMh.sub (isHermitian_one.smul (IsSelfAdjoint.all _)))
      fun x => ?_
    rw [quad_sub, quad_smul, quad_one]
    linarith [hlow x]
  have h2 : loewnerLE M ((g / d) • (1 : Mat d)) := by
    unfold loewnerLE
    refine posSemidef_of_quad_nonneg ((isHermitian_one.smul (IsSelfAdjoint.all _)).sub hMh)
      fun x => ?_
    rw [quad_sub, quad_smul, quad_one]
    linarith [hup x]
  refine (condNum_le_of_sandwich hMh ha (by positivity) h1 h2).trans_eq ?_
  congr 1
  field_simp

/-! ## Clause (2): the rotational spread and the rank-one limit -/

/-- A profile bounded below by `c > 0` on `(0,∞)` has `∫_1^∞ k(r) dr/r = ∞`. -/
theorem lintegral_Ioi_one_div_eq_top {k : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hall : ∀ r : ℝ, 0 < r → c ≤ k r) : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) = ⊤ := by
  refine eq_top_iff.2 ?_
  calc ⊤ = ENNReal.ofReal c * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal r⁻¹ := by
        rw [lintegral_Ioi_one_inv, ENNReal.mul_top (by simp [hc])]
    _ = ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (c / r) := by
        rw [← lintegral_const_mul _ measurable_inv.ennreal_ofReal]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        rw [← ENNReal.ofReal_mul hc.le, div_eq_mul_inv]
    _ ≤ ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_))
        have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hall r hr0) hr0.le)

/-- **`k(r) → 0` as `r → ∞`.** -/
theorem lineProfile_eventually_lt {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → k r < c := by
  by_contra h
  push Not at h
  refine hk1 (lintegral_Ioi_one_div_eq_top hc fun r hr => ?_)
  obtain ⟨r', hr', hcr'⟩ := h r hr
  exact hcr'.trans (hk hr (hr.trans_le hr') hr')

theorem lineSector_union (U V : Set (Rd d)) (a b : ℝ) :
    lineSector (U ∪ V) a b = lineSector U a b ∪ lineSector V a b := by
  ext x
  simp only [lineSector, mem_union, mem_setOf_eq]
  tauto

/-- **A lower bound on a sector, symmetric or not**: if `J ≤ ∫_a^b k(s q_Σ(u)^{-1/2}) ds/s` for
the unit `u` of `V ∪ -V`, then `σ̄(V) J ≤ L_Σ(E_V)`. -/
theorem lineLevy_sector_ge {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S : Mat d} (hS : S.PosDef)
    {V : Set (Rd d)} (hV : MeasurableSet V) {a b : ℝ} (ha : 0 ≤ a) {J : ℝ≥0∞}
    (hJ : ∀ u : Rd d, ‖u‖ = 1 → u ∈ V ∪ (-·) ⁻¹' V →
      J ≤ ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt (quad S u)) / s)) :
    normSphere d V * J ≤ lineLevy k S (lineSector V a b) := by
  set W := V ∪ (-·) ⁻¹' V with hW
  have hWm : MeasurableSet W := hV.union (measurable_neg hV)
  have hWs : ∀ v, -v ∈ W ↔ v ∈ W := fun v => by
    simp only [hW, mem_union, mem_preimage, neg_neg]
    tauto
  have hneg : lineLevy k S (lineSector ((-·) ⁻¹' V) a b) = lineLevy k S (lineSector V a b) := by
    have h := preimage_lineSector (LinearIsometryEquiv.neg ℝ (E := Rd d)) V a b
    have hc : ((LinearIsometryEquiv.neg ℝ (E := Rd d)) : Rd d → Rd d) = (-·) := rfl
    rw [hc] at h
    rw [← h]
    conv_rhs => rw [← lineLevy_symm hk S]
    rw [push, Measure.map_apply (lin (-1 : Mat d)).continuous.measurable
      (measurableSet_lineSector hV a b)]
    congr 1
    ext x
    simp [lin_neg_one_apply]
  have h1 : 2 * (normSphere d V * J) ≤ lineLevy k S (lineSector W a b) := by
    rw [lineLevy_sector hk hS hWm hWs ha]
    calc 2 * (normSphere d V * J) ≤ 2 * (normSphere d W * J) := by
          exact mul_le_mul_right (mul_le_mul_left
            (measure_mono (μ := normSphere d) (show V ⊆ W from subset_union_left)) J) 2
      _ = ∫⁻ u, 2 * W.indicator (fun _ => J) u ∂normSphere d := by
          rw [lintegral_const_mul _ (measurable_const.indicator hWm), lintegral_indicator_const hWm,
            mul_comm J]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_normSphere_norm] with u hu
          by_cases huW : u ∈ W
          · rw [indicator_of_mem huW, indicator_of_mem huW]
            exact mul_le_mul_right (hJ u hu huW) _
          · rw [indicator_of_notMem huW, indicator_of_notMem huW]
  have h2 : lineLevy k S (lineSector W a b) ≤ 2 * lineLevy k S (lineSector V a b) := by
    rw [hW, lineSector_union]
    refine (measure_union_le _ _).trans ?_
    rw [hneg, two_mul]
  have h3 := h1.trans h2
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h3

/-- `I(q) := ∫_a^b k(s q^{-1/2}) ds/s` is nondecreasing in `q > 0`. -/
theorem sectorI_mono {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {a b : ℝ} (ha : 0 ≤ a) {q q' : ℝ}
    (hq : 0 < q) (hqq : q ≤ q') :
    ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s) ≤
      ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q') / s) := by
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => ?_))
  have hs0 : 0 < s := ha.trans_lt hs.1
  have h1 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have h2 : Real.sqrt q ≤ Real.sqrt q' := Real.sqrt_le_sqrt hqq
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hs0.le)
  exact hk (div_pos hs0 (h1.trans_le h2)) (div_pos hs0 h1) (div_le_div_of_nonneg_left hs0.le h1 h2)

/-- `I(q) ≤ k(a q^{-1/2}) (b - a)/a`. -/
theorem sectorI_le {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk : AntitoneOn k (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) {q : ℝ} (hq : 0 < q) :
    ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s) ≤
      ENNReal.ofReal (k (a / Real.sqrt q) * ((b - a) / a)) := by
  have h1 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  calc ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s)
      ≤ ∫⁻ _s in Ioo a b, ENNReal.ofReal (k (a / Real.sqrt q) / a) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => ?_))
        have hs0 : 0 < s := ha.trans hs.1
        refine ENNReal.ofReal_le_ofReal ?_
        have hk' : k (s / Real.sqrt q) ≤ k (a / Real.sqrt q) :=
          hk (div_pos ha h1) (div_pos hs0 h1) (div_le_div_of_nonneg_right hs.1.le h1.le)
        have hk0' : 0 ≤ k (s / Real.sqrt q) := hk_nonneg _ (div_pos hs0 h1)
        calc k (s / Real.sqrt q) / s ≤ k (a / Real.sqrt q) / s :=
              div_le_div_of_nonneg_right hk' hs0.le
          _ ≤ k (a / Real.sqrt q) / a := div_le_div_of_nonneg_left (hk0'.trans hk') ha hs.1.le
    _ = ENNReal.ofReal (k (a / Real.sqrt q) * ((b - a) / a)) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by
          have := hk_nonneg _ (div_pos ha h1); positivity)]
        congr 1
        ring

theorem quad_sigmaEps_unit [NeZero d] (ε : ℝ) {u : Rd d} (hu : ‖u‖ = 1) :
    quad (sigmaEps d ε) u = ε + (1 - ε) * u 0 ^ 2 := by
  rw [quad_sigmaEps, hu]; ring

theorem coord_sq_le_one {u : Rd d} (hu : ‖u‖ = 1) (i : Fin d) : u i ^ 2 ≤ 1 := by
  have := sq_apply_le_norm_sq u i
  rwa [hu, one_pow] at this

/-- Upper bound on a symmetric sector. -/
theorem lineLevy_sector_le_of {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S : Mat d} (hS : S.PosDef)
    {U : Set (Rd d)} (hU : MeasurableSet U) (hUs : ∀ v, -v ∈ U ↔ v ∈ U) {a b : ℝ} (ha : 0 ≤ a)
    {J : ℝ≥0∞} (hJ : ∀ u : Rd d, ‖u‖ = 1 → u ∈ U →
      ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt (quad S u)) / s) ≤ J) :
    lineLevy k S (lineSector U a b) ≤ 2 * normSphere d U * J := by
  rw [lineLevy_sector hk hS hU hUs ha, mul_assoc, mul_comm (normSphere d U),
    ← lintegral_indicator_const hU, ← lintegral_const_mul _ (measurable_const.indicator hU)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_normSphere_norm] with u hu
  by_cases huU : u ∈ U
  · rw [indicator_of_mem huU, indicator_of_mem huU]
    exact mul_le_mul_right (hJ u hu huU) _
  · rw [indicator_of_notMem huU, indicator_of_notMem huU]

/-- Lower bound on a symmetric sector. -/
theorem lineLevy_sector_ge_of {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S : Mat d} (hS : S.PosDef)
    {U : Set (Rd d)} (hU : MeasurableSet U) (hUs : ∀ v, -v ∈ U ↔ v ∈ U) {a b : ℝ} (ha : 0 ≤ a)
    {J : ℝ≥0∞} (hJ : ∀ u : Rd d, ‖u‖ = 1 → u ∈ U →
      J ≤ ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt (quad S u)) / s)) :
    2 * normSphere d U * J ≤ lineLevy k S (lineSector U a b) := by
  rw [lineLevy_sector hk hS hU hUs ha, mul_assoc, mul_comm (normSphere d U),
    ← lintegral_indicator_const hU, ← lintegral_const_mul _ (measurable_const.indicator hU)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_normSphere_norm] with u hu
  by_cases huU : u ∈ U
  · rw [indicator_of_mem huU, indicator_of_mem huU]
    exact mul_le_mul_right (hJ u hu huU) _
  · rw [indicator_of_notMem huU, indicator_of_notMem huU]

theorem quad_sigmaEps_ge [NeZero d] {ε : ℝ} (hε0 : 0 ≤ ε) (_hε1 : ε ≤ 1) (u : Rd d) :
    u 0 ^ 2 ≤ quad (sigmaEps d ε) u := by
  rw [quad_sigmaEps]
  have := sq_apply_le_norm_sq u 0
  nlinarith

/-- **`prop:similarity-line-family`(2), the rotational spread**: `rs(L_{Σ_ε}) → ∞` as `ε ↓ 0`.
Two caps, about `e₂` and about `e₁` (indices from `0` in Lean), exchanged by the swap of the two
coordinates: on the first `q_{Σ_ε} < q₂`, on the second `q_{Σ_ε} > 1/4`, and `k(r) → 0` at `∞`. -/
theorem lineLevy_rotSpread_tendsto (hd : 2 ≤ d) {k : ℝ → ℝ}
    (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    Tendsto (fun ε => rotSpread (lineLevy k (sigmaEps d ε))) (𝓝[>] 0) (𝓝 ⊤) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h10 : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [i1] at this
  obtain ⟨r₀, hr₀, hkr₀⟩ := hk_ne
  have hκ : 0 < k r₀ := lt_of_le_of_ne (hk_nonneg r₀ hr₀) (Ne.symm hkr₀)
  set a := r₀ / 4 with ha
  set b := r₀ / 2 with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by rw [ha, hb]; linarith
  set I : ℝ → ℝ≥0∞ := fun q => ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt q) / s) with hI
  have hsq4 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hI4pos : 0 < I (1 / 4) := by
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (k r₀ / r₀) * volume (Ioo a b) := by
          rw [Real.volume_Ioo]
          refine ENNReal.mul_pos (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ?_
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, ha, hb]
          linarith
      _ = ∫⁻ _s in Ioo a b, ENNReal.ofReal (k r₀ / r₀) := (setLIntegral_const _ _).symm
      _ ≤ I (1 / 4) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
            (ae_of_all _ fun s hs => ?_))
          have hs0 : 0 < s := ha0.trans hs.1
          rw [hsq4]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2s : s / (1 / 2) = 2 * s := by field_simp
          rw [h2s]
          have hk2 : k r₀ ≤ k (2 * s) := hk (show (0 : ℝ) < 2 * s by positivity) hr₀ (by rw [hb] at hs; linarith [hs.2])
          calc k r₀ / r₀ ≤ k r₀ / s := div_le_div_of_nonneg_left hκ.le hs0
                (by rw [hb] at hs; linarith [hs.2])
            _ ≤ k (2 * s) / s := div_le_div_of_nonneg_right hk2 hs0.le
  have hI4fin : I (1 / 4) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sectorI_le hk_nonneg hk ha0 hab (by norm_num))
  have hI4r : 0 < (I (1 / 4)).toReal := ENNReal.toReal_pos hI4pos.ne' hI4fin
  rw [ENNReal.tendsto_nhds_top_iff_nat]
  intro n
  set η : ℝ := (I (1 / 4)).toReal / ((n : ℝ) + 2) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨R₁, hR₁, hR₁k⟩ := lineProfile_eventually_lt hk hk1 hη0
  set q₂ : ℝ := min (1 / 4) ((a / R₁) ^ 2) with hq₂
  have hq₂0 : 0 < q₂ := by positivity
  have hq₂1 : q₂ ≤ 1 / 4 := min_le_left _ _
  have hkq : k (a / Real.sqrt q₂) < η := by
    refine hR₁k _ ?_
    have hs : Real.sqrt q₂ ≤ a / R₁ := by
      rw [Real.sqrt_le_left (by positivity)]
      exact min_le_right _ _
    rw [le_div_iff₀ (Real.sqrt_pos.2 hq₂0)]
    rw [le_div_iff₀ hR₁] at hs
    linarith
  have hIq : ∀ q : ℝ, 0 < q → q ≤ q₂ → I q ≤ ENNReal.ofReal η := by
    intro q hq hqq
    refine (sectorI_mono hk ha0.le hq hqq).trans ((sectorI_le hk_nonneg hk ha0 hab hq₂0).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hba : (b - a) / a = 1 := by rw [ha, hb]; field_simp; ring
    rw [hba, mul_one]
    exact hkq.le
  set U : Set (Rd d) := {u | u 0 ^ 2 < q₂ / 2 ∧ 1 / 4 < u i1 ^ 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (f := fun u : Rd d => u 0 ^ 2) (by fun_prop) continuous_const).inter
      (isOpen_lt (g := fun u : Rd d => u i1 ^ 2) continuous_const (by fun_prop))
  have hUs : ∀ v, -v ∈ U ↔ v ∈ U := fun v => by
    simp only [hU, mem_setOf_eq, PiLp.neg_apply, neg_sq]
  have he1 : ‖(ebasis i1 : Rd d)‖ = 1 := by simp [ebasis]
  have he1U : (ebasis i1 : Rd d) ∈ U := by
    simp only [hU, mem_setOf_eq]
    constructor
    · simp [ebasis, Ne.symm h10]; positivity
    · simp [ebasis]; norm_num
  have hσU : 0 < normSphere d U := normSphere_pos_of_isOpen hd1 hUo he1 he1U
  have hσU' : normSphere d U ≠ ⊤ := normSphere_ne_top hd1 U
  set R : Rd d ≃ₗᵢ[ℝ] Rd d := swapIso 0 i1 with hR
  have hRU : normSphere d (R ⁻¹' U) = normSphere d U := by
    conv_rhs => rw [← normSphere_map_isometry R]
    rw [Measure.map_apply R.continuous.measurable hUo.measurableSet]
  have hRUo : IsOpen (R ⁻¹' U) := hUo.preimage R.continuous
  have hRUs : ∀ v, -v ∈ R ⁻¹' U ↔ v ∈ R ⁻¹' U := fun v => by
    simp only [mem_preimage, map_neg, hUs]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < q₂ / 2 by positivity)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := by linarith [hε.2]
  have hSε : (sigmaEps d ε).PosDef := sigmaEps_posDef hε0
  have hlt : ((n : ℝ≥0∞)) < (n : ℝ≥0∞) + 1 := ENNReal.lt_add_right (by simp) one_ne_zero
  refine lt_of_lt_of_le hlt (le_rotSpread fun K hK1 hK => ?_)
  by_contra hKlt
  push Not at hKlt
  /- The two sectors. -/
  have hup : lineLevy k (sigmaEps d ε) (lineSector U a b) ≤
      2 * normSphere d U * ENNReal.ofReal η := by
    refine lineLevy_sector_le_of hk hSε hUo.measurableSet hUs ha0.le fun u hu huU => ?_
    have hq0 : 0 < quad (sigmaEps d ε) u := quad_pos hSε (by rintro rfl; simp at hu)
    refine hIq _ hq0 ?_
    rw [quad_sigmaEps_unit ε hu]
    have h0 := huU.1
    have h1 : (1 - ε) * u 0 ^ 2 ≤ u 0 ^ 2 := by nlinarith [sq_nonneg (u 0)]
    linarith [hε.2]
  have hlow : 2 * normSphere d U * I (1 / 4) ≤
      lineLevy k (sigmaEps d ε) (lineSector (R ⁻¹' U) a b) := by
    rw [← hRU]
    refine lineLevy_sector_ge_of hk hSε hRUo.measurableSet hRUs ha0.le fun u hu huU => ?_
    refine sectorI_mono hk ha0.le (by norm_num) ?_
    have h1 : 1 / 4 < u 0 ^ 2 := by
      have := huU.2
      have h2 : (R u) i1 = u 0 := by rw [hR, swapIso_apply, Equiv.swap_apply_right]
      rw [h2] at this
      exact this
    linarith [quad_sigmaEps_ge hε0.le hε1 u]
  have hpush : lineLevy k (sigmaEps d ε) (lineSector (R ⁻¹' U) a b) ≤
      K * lineLevy k (sigmaEps d ε) (lineSector U a b) := by
    have h := hK (isoMat R) (isoMat_mem_orthSet R)
    have h' := h (lineSector U a b)
    rw [push, Measure.map_apply (lin (isoMat R)).continuous.measurable
      (measurableSet_lineSector hUo.measurableSet a b), Measure.smul_apply, smul_eq_mul,
      lin_isoMat] at h'
    rw [← preimage_lineSector]
    exact h'
  have hchain := hlow.trans (hpush.trans (mul_le_mul_right hup K))
  rw [show K * (2 * normSphere d U * ENNReal.ofReal η) = 2 * normSphere d U * (K * ENNReal.ofReal η)
    by ring] at hchain
  have hc0 : 2 * normSphere d U ≠ 0 := mul_ne_zero (by norm_num) hσU.ne'
  have hct : 2 * normSphere d U ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hσU'
  have h4 := (ENNReal.mul_le_mul_iff_right hc0 hct).1 hchain
  have h5 : K * ENNReal.ofReal η ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal η :=
    mul_le_mul_left hKlt.le _
  have h6 : ((n : ℝ≥0∞) + 1) * ENNReal.ofReal η < I (1 / 4) := by
    rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one],
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hI4fin]
    refine (ENNReal.ofReal_lt_ofReal_iff hI4r).2 ?_
    rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact absurd (h4.trans h5) (not_le.2 h6)

/-- **`prop:similarity-line-family`(2), the rank-one limit**: every rank-one limit `L_*` is at least
the image of `σ̄(du) 2k(s/|u₁|) ds/s` (indices from `0` in Lean; `u₁ = 0` is `σ̄`-null), and
charges every nonempty open cone. -/
theorem lineLevy_rankOne (hd : 2 ≤ d) {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (Lstar : Measure (Rd d))
    (hLs : IsRankOneLimit (lineLevy k) Lstar) :
    (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
        fun p => ENNReal.ofReal (2 * k (p.2 / |p.1 ⟨0, by omega⟩|) / p.2)).map
      (fun p => p.2 • p.1) ≤ Lstar ∧
    ∀ U : Set (Rd d), IsOpen U → U.Nonempty → (∀ x ∈ U, ∀ t : ℝ, 0 < t → t • x ∈ U) →
      0 < Lstar U := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have h0 : (⟨0, by omega⟩ : Fin d) = 0 := fin_zero_eq hd1
  rw [h0]
  have hm : Measurable fun p : Rd d × ℝ => p.2 • p.1 := by fun_prop
  set P := (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
        fun p => ENNReal.ofReal (2 * k (p.2 / |p.1 0|) / p.2)).map (fun p => p.2 • p.1) with hP
  have hlevy := line_family_levy hd k hk_nonneg hk hk_ne hk0 hk1
  /- `P ≤ L_{Σ_ε}` for `ε ∈ (0,1]`. -/
  have hPle : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → P ≤ lineLevy k (sigmaEps d ε) := by
    intro ε hε0 hε1
    rw [(hlevy.2.1 _ (sigmaEps_posDef hε0)).1, hP]
    refine Measure.map_mono (withDensity_mono ?_) hm
    refine ae_iff.2 (measure_mono_null ?_ (measure_union_null
      (s := {u : Rd d | u 0 = 0} ×ˢ univ) (t := univ ×ˢ Iic 0) ?_ ?_))
    · intro p hp
      simp only [mem_setOf_eq, not_le] at hp
      by_contra hcon
      simp only [mem_union, mem_prod, mem_setOf_eq, mem_univ, and_true, true_and, mem_Iic,
        not_or, not_le] at hcon
      refine hp.not_ge (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hcon.2.le))
      have hu0 : 0 < |p.1 0| := abs_pos.2 hcon.1
      have hq : |p.1 0| ≤ Real.sqrt (quad (sigmaEps d ε) p.1) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (quad_sigmaEps_ge hε0.le hε1 p.1)
      refine mul_le_mul_of_nonneg_left (hk (div_pos hcon.2 (hu0.trans_le hq)) (div_pos hcon.2 hu0)
        (div_le_div_of_nonneg_left hcon.2.le hu0 hq)) (by norm_num)
    · rw [Measure.prod_prod, normSphere_coord_null hd1 0, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Iic,
        show Iic (0 : ℝ) ∩ Ioi 0 = ∅ from by ext x; simp, measure_empty, mul_zero]
  /- `P{0} = 0`. -/
  have hP0 : P {0} = 0 := by
    rw [hP, Measure.map_apply hm (measurableSet_singleton _)]
    refine withDensity_absolutelyContinuous _ _ (measure_mono_null ?_ (measure_union_null
      (s := {0} ×ˢ univ) (t := univ ×ˢ Iic 0) ?_ ?_))
    · intro p hp
      simp only [mem_preimage, mem_singleton_iff, smul_eq_zero] at hp
      rcases hp with h | h
      · exact Or.inr ⟨mem_univ _, by simp [h]⟩
      · exact Or.inl ⟨h, mem_univ _⟩
    · rw [Measure.prod_prod, normSphere_zero, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Iic,
        show Iic (0 : ℝ) ∩ Ioi 0 = ∅ from by ext x; simp, measure_empty, mul_zero]
  have hPL : P ≤ Lstar := by
    refine measure_le_of_boundedAway hP0 fun B hB hBa => ?_
    refine ge_of_tendsto (hLs.2 B hB hBa) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hPle ε hε.1 hε.2.le B
  refine ⟨hPL, fun U hU hUne hUc => ?_⟩
  /- A direction of `U` off the hyperplane `u₁ = 0`. -/
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set y : Rd d := if x 0 = 0 then x + (r / 2) • ebasis 0 else x with hy
  have hyU : y ∈ U := by
    rw [hy]
    split_ifs with h
    · refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      simp [ebasis]
      linarith
    · exact hx
  have hy0 : y 0 ≠ 0 := by
    rw [hy]
    split_ifs with h
    · simp [ebasis, h]; positivity
    · exact h
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 fun h => hy0 (by simp [h])
  set u₀ := ‖y‖⁻¹ • y with hu₀
  have hu₀n : ‖u₀‖ = 1 := by rw [hu₀, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
  have hu₀U : u₀ ∈ U := hUc y hyU _ (inv_pos.2 hyn)
  have hu₀0 : u₀ 0 ≠ 0 := by
    rw [hu₀, PiLp.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hyn.ne') hy0
  set c := |u₀ 0| / 2 with hc
  have hc0 : 0 < c := by positivity
  set V : Set (Rd d) := U ∩ {u | c < |u 0|} with hV
  have hVo : IsOpen V := hU.inter (isOpen_lt continuous_const (by fun_prop))
  have hu₀V : u₀ ∈ V := ⟨hu₀U, show c < |u₀ 0| by rw [hc]; linarith [abs_pos.2 hu₀0]⟩
  have hσV : 0 < normSphere d V := normSphere_pos_of_isOpen hd1 hVo hu₀n hu₀V
  obtain ⟨r₀, hr₀, hkr₀⟩ := hk_ne
  have hκ : 0 < k r₀ := lt_of_le_of_ne (hk_nonneg r₀ hr₀) (Ne.symm hkr₀)
  set a := c * r₀ / 2 with ha
  set b := c * r₀ with hb
  have ha0 : 0 < a := by positivity
  set J : ℝ≥0∞ := ENNReal.ofReal (k r₀ / b) * volume (Ioo a b) with hJ
  have hJ0 : 0 < J := by
    rw [hJ, Real.volume_Ioo]
    refine ENNReal.mul_pos (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, ha, hb]
    nlinarith
  have hE : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      normSphere d V * J ≤ lineLevy k (sigmaEps d ε) (lineSector V a b) := by
    intro ε hε0 hε1
    refine lineLevy_sector_ge hk (sigmaEps_posDef hε0) hVo.measurableSet ha0.le fun u hu huV => ?_
    have hcu : c < |u 0| := by
      rcases huV with h | h
      · exact h.2
      · have h2 : c < |(-u) 0| := h.2
        rwa [PiLp.neg_apply, abs_neg] at h2
    have hq : c ^ 2 ≤ quad (sigmaEps d ε) u := by
      have := quad_sigmaEps_ge hε0.le hε1 u
      have h2 : c ^ 2 ≤ u 0 ^ 2 := by
        rw [← sq_abs (u 0)]
        exact pow_le_pow_left₀ hc0.le hcu.le 2
      linarith
    calc J = ∫⁻ _s in Ioo a b, ENNReal.ofReal (k r₀ / b) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in Ioo a b, ENNReal.ofReal (k (s / Real.sqrt (quad (sigmaEps d ε) u)) / s) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
            (ae_of_all _ fun s hs => ?_))
          have hs0 : 0 < s := ha0.trans hs.1
          have hsq : c ≤ Real.sqrt (quad (sigmaEps d ε) u) := by
            rw [← Real.sqrt_sq hc0.le]
            exact Real.sqrt_le_sqrt hq
          refine ENNReal.ofReal_le_ofReal ?_
          have hkk : k r₀ ≤ k (s / Real.sqrt (quad (sigmaEps d ε) u)) := by
            refine hk (div_pos hs0 (hc0.trans_le hsq)) hr₀ ?_
            rw [div_le_iff₀ (hc0.trans_le hsq)]
            have : s < c * r₀ := hs.2
            nlinarith
          calc k r₀ / b ≤ k r₀ / s := div_le_div_of_nonneg_left hκ.le hs0 hs.2.le
            _ ≤ _ := div_le_div_of_nonneg_right hkk hs0.le
  have hEsub : lineSector V a b ⊆ U := by
    intro z hz
    have hz0 : 0 < ‖z‖ := ha0.trans hz.1
    have := hUc _ hz.2.2.1 ‖z‖ hz0
    rwa [smul_smul, mul_inv_cancel₀ hz0.ne', one_smul] at this
  have hEm : MeasurableSet (lineSector V a b) := measurableSet_lineSector hVo.measurableSet a b
  have hEa : IsBoundedAway (lineSector V a b) := ⟨a, ha0, fun z hz => hz.1.le⟩
  have hlim : normSphere d V * J ≤ Lstar (lineSector V a b) := by
    refine ge_of_tendsto (hLs.2 _ hEm hEa) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hE ε hε.1 hε.2.le
  exact lt_of_lt_of_le (ENNReal.mul_pos hσV.ne' hJ0.ne') (hlim.trans (measure_mono hEsub))

/-- **`prop:similarity-line-family`(2)**, three functionals: for `Σ ∈ PD(d)` and `s > 0`,
`es(ψ_Σ) ≤ 4d(d+2)` and `cond 𝓜_s(L_Σ) ≤ d + 2`, while `rs(L_{Σ_ε}) → ∞` as `ε ↓ 0`; the rank-one
limit `L_*` is at least the image of `σ̄(du) 2k(s/|u₁|) ds/s`, and charges every open cone. Spends
nothing. -/
theorem line_family_functionals (hd : 2 ≤ d) (k : ℝ → ℝ) (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk_anti : AntitoneOn k (Ioi 0)) (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    (∀ S : Mat d, S.PosDef → ∀ s : ℝ, 0 < s →
      expSpread (levyExp (lineLevy k S)) ≤ ENNReal.ofReal (4 * d * ((d : ℝ) + 2)) ∧
      condNum (momentMatrix s (lineLevy k S)) ≤ ENNReal.ofReal ((d : ℝ) + 2)) ∧
    Tendsto (fun ε => rotSpread (lineLevy k (sigmaEps d ε))) (𝓝[>] 0) (𝓝 ⊤) ∧
    ∀ Lstar : Measure (Rd d), IsRankOneLimit (lineLevy k) Lstar →
      (((normSphere d).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
          fun p => ENNReal.ofReal (2 * k (p.2 / |p.1 ⟨0, by omega⟩|) / p.2)).map
        (fun p => p.2 • p.1) ≤ Lstar ∧
      ∀ U : Set (Rd d), IsOpen U → U.Nonempty → (∀ x ∈ U, ∀ t : ℝ, 0 < t → t • x ∈ U) →
        0 < Lstar U :=
  ⟨fun _S hS _s hs => ⟨lineLevy_expSpread_le hd hk_anti hk0 hk1 hS,
      lineLevy_condNum_le hd hk_nonneg hk_anti hk_ne hk0 hk1 hS hs⟩,
    lineLevy_rotSpread_tendsto hd hk_nonneg hk_anti hk_ne hk1,
    fun Lstar hLs => lineLevy_rankOne hd hk_nonneg hk_anti hk_ne hk0 hk1 Lstar hLs⟩

/-! ## Clause (1): the cascade -/

/-- **The difference of two Lévy measures** `L ≤ L'`, symmetric when both are: a symmetric Lévy
measure `D` with `D + L = L'`, built shell by shell (each shell has finite `L'`-mass). -/
theorem exists_levy_sub {L L' : Measure (Rd d)} (hL' : IsLevyMeasure L') (hle : L ≤ L')
    (hs : push (-1) L = L) (hs' : push (-1) L' = L') :
    ∃ D : Measure (Rd d), IsLevyMeasure D ∧ push (-1) D = D ∧ D + L = L' := by
  set A : ℕ → Set (Rd d) := disjointed (awaySet (d := d)) with hA
  have hAm : ∀ n, MeasurableSet (A n) := MeasurableSet.disjointed fun n => measurableSet_awaySet n
  have hAd : Pairwise (Function.onFun Disjoint A) := disjoint_disjointed _
  have hAU : ⋃ n, A n = ({0}ᶜ : Set (Rd d)) := by rw [hA, iUnion_disjointed, iUnion_awaySet]
  have hfin : ∀ n, IsFiniteMeasure (L.restrict (A n)) := fun n => by
    refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top (hL'.awaySet_ne_top n) ?_)
    exact (hle _).trans (measure_mono (disjointed_le _ n))
  have hL0 : L {0} = 0 := le_antisymm ((hle _).trans hL'.1.le) bot_le
  have hres : ∀ M : Measure (Rd d), M {0} = 0 → M = Measure.sum fun n => M.restrict (A n) := by
    intro M hM
    rw [← Measure.restrict_iUnion hAd hAm, hAU]
    exact (Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hM)).symm
  set D₀ : Measure (Rd d) := Measure.sum fun n => L'.restrict (A n) - L.restrict (A n) with hD₀
  have hD₀L : D₀ + L = L' := by
    conv_rhs => rw [hres L' hL'.1]
    conv_lhs => rw [hres L hL0]
    rw [hD₀, Measure.sum_add_sum]
    congr 1
    funext n
    haveI := hfin n
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl hle)
  have hneg : Measurable (lin (-1 : Mat d)) := (lin (-1 : Mat d)).continuous.measurable
  have hpp : ∀ M : Measure (Rd d), push (-1) (push (-1) M) = M := by
    intro M
    rw [push, push, Measure.map_map hneg hneg]
    have : (lin (-1 : Mat d)) ∘ (lin (-1 : Mat d)) = id := by
      funext x; simp [lin_neg_one_apply]
    rw [this, Measure.map_id]
  have hpadd : ∀ M N : Measure (Rd d), push (-1) (M + N) = push (-1) M + push (-1) N :=
    fun M N => Measure.map_add M N hneg
  have hD₀L' : push (-1) D₀ + L = L' := by
    have := congrArg (push (-1)) hD₀L
    rwa [hpadd, hs, hs'] at this
  set D : Measure (Rd d) := (2 : ℝ≥0∞)⁻¹ • (D₀ + push (-1) D₀) with hD
  have hDL : D + L = L' := by
    have hhalf : L = (2 : ℝ≥0∞)⁻¹ • L + (2 : ℝ≥0∞)⁻¹ • L := by
      rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
    calc D + L = (2 : ℝ≥0∞)⁻¹ • (D₀ + L) + (2 : ℝ≥0∞)⁻¹ • (push (-1) D₀ + L) := by
          rw [hD, smul_add, smul_add, smul_add]
          conv_lhs => rw [hhalf]
          abel
      _ = L' := by rw [hD₀L, hD₀L', ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
  have hDle : D ≤ L' := by
    rw [← hDL]
    exact Measure.le_add_right le_rfl
  refine ⟨D, ⟨le_antisymm ((hDle _).trans hL'.1.le) bot_le,
    ne_top_of_le_ne_top hL'.2 (lintegral_mono' hDle le_rfl)⟩, ?_, hDL⟩
  rw [hD, push_smul_measure, hpadd, hpp, add_comm]

/-- **A similarity cascade from an exponent.** If `Φ(Σ, ·)`, `Σ ∈ PSD(d)`, is continuous in `Σ`,
similarity-covariant (`Φ(A·Σ, ω) = Φ(Σ, Aᵀω)`), moves between `0` and `I`, and every Loewner step
has an infinitely divisible probability increment with transform `e^{-(Φ(Σ') - Φ(Σ))}`, then the
laws `m_Σ` with transform `e^{-Φ(Σ)}` have such increments forming a family with (K1), (K2), (K4)
and (K3) for every similarity. Spends nothing. -/
theorem simCascade_of_exponent (Φ : Mat d → Rd d → ℝ)
    (hcont : ∀ ω : Rd d, ContinuousOn (fun S => Φ S ω) (psdSet d))
    (hcov : ∀ A ∈ simSet d, ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      Φ (act A S) ω = Φ S (lin Aᵀ ω))
    (hnd : ∃ ω : Rd d, Φ 1 ω ≠ Φ 0 ω)
    (hinc : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
        ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(Φ S' ω - Φ S ω)) : ℝ) : ℂ))
    (m : Mat d → Measure (Rd d))
    (hm : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S) ∧
      ∀ ω : Rd d, charFun (m S) ω = ((Real.exp (-Φ S ω) : ℝ) : ℂ)) :
    ∃ ρ : Mat d → Mat d → Measure (Rd d),
      (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
        IsProbabilityMeasure (ρ S S') ∧ IsInfinitelyDivisible (ρ S S') ∧ m S' = m S ∗ ρ S S') ∧
      IsGWCascadeFamily (simSet d) loewnerLE ρ := by
  classical
  let ρ : Mat d → Mat d → Measure (Rd d) := fun S S' =>
    if h : S.PosSemidef ∧ S'.PosSemidef ∧ loewnerLE S S' then
      Classical.choose (hinc S S' h.1 h.2.1 h.2.2)
    else Measure.dirac 0
  have hρ : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      IsProbabilityMeasure (ρ S S') ∧ IsInfinitelyDivisible (ρ S S') ∧
        ∀ ω : Rd d, charFun (ρ S S') ω = ((Real.exp (-(Φ S' ω - Φ S ω)) : ℝ) : ℂ) := by
    intro S S' hS hS' hle
    have h : S.PosSemidef ∧ S'.PosSemidef ∧ loewnerLE S S' := ⟨hS, hS', hle⟩
    simp only [ρ, dif_pos h]
    exact Classical.choose_spec (hinc S S' hS hS' hle)
  have hrefl : ∀ S : Mat d, loewnerLE S S := fun S => by
    unfold loewnerLE; rw [sub_self]; exact PosSemidef.zero
  refine ⟨ρ, fun S S' hS hS' hle => ⟨(hρ S S' hS hS' hle).1, (hρ S S' hS hS' hle).2.1, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · haveI := (hρ S S' hS hS' hle).1
    haveI := (hm S hS).1
    haveI := (hm S' hS').1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, (hρ S S' hS hS' hle).2.2, (hm S hS).2, (hm S' hS').2, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    ring
  · exact fun p hp => (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).1
  · intro S hS
    haveI := (hρ S S hS hS (hrefl S)).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [(hρ S S hS hS (hrefl S)).2.2, charFun_dirac, sub_self, neg_zero, Real.exp_zero]
    simp
  · intro S S' S'' hS hS' hS'' h h'
    have h'' := loewnerLE_trans' h h'
    haveI := (hρ S S'' hS hS'' h'').1
    haveI := (hρ S' S'' hS' hS'' h').1
    haveI := (hρ S S' hS hS' h).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, (hρ S S'' hS hS'' h'').2.2, (hρ S' S'' hS' hS'' h').2.2,
      (hρ S S' hS hS' h).2.2, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · intro ω
    have hc : ContinuousOn (fun p : Mat d × Mat d =>
        ((Real.exp (-(Φ p.2 ω - Φ p.1 ω)) : ℝ) : ℂ)) (wedgePairs (loewnerLE (d := d))) := by
      refine Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
        (((hcont ω).comp continuousOn_snd ?_).sub ((hcont ω).comp continuousOn_fst ?_)).neg)
      · exact fun p hp => hp.2.1
      · exact fun p hp => hp.1
    refine hc.congr fun p hp => ?_
    exact (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).2.2 ω
  · intro A hA p hp
    have hp' : (act A p.1, act A p.2) ∈ wedgePairs (loewnerLE (d := d)) :=
      ⟨posSemidef_act A hp.1, posSemidef_act A hp.2.1, loewnerLE_act A hp.2.2⟩
    haveI := (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).1
    haveI := (hρ _ _ hp'.1 hp'.2.1 hp'.2.2).1
    refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, (hρ p.1 p.2 hp.1 hp.2.1 hp.2.2).2.2,
      (hρ _ _ hp'.1 hp'.2.1 hp'.2.2).2.2, hcov A hA _ hp.1, hcov A hA _ hp.2.1]
  · intro h0
    obtain ⟨ω, hω⟩ := hnd
    have hpair : (0 : Mat d).PosSemidef ∧ (1 : Mat d).PosSemidef ∧ loewnerLE (0 : Mat d) 1 :=
      ⟨PosSemidef.zero, PosSemidef.one, by unfold loewnerLE; rw [sub_zero]; exact PosSemidef.one⟩
    have h1 := congrArg (fun m => charFun m ω) h0
    rw [(hρ 0 1 hpair.1 hpair.2.1 hpair.2.2).2.2, charFun_dirac] at h1
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
    have h2 : Real.exp (-(Φ 1 ω - Φ 0 ω)) = 1 := by exact_mod_cast h1
    rw [Real.exp_eq_one_iff] at h2
    exact hω (by linarith)

theorem measurable_linePsi (k : ℝ → ℝ) : Measurable (linePsi k) :=
  Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => ENNReal.ofReal (1 - Real.cos (p.2 * p.1)))
    (by fun_prop)

theorem integrable_min_lineProfile {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    Integrable (fun r : ℝ => min (r ^ 2) 1) (lineProfileMeasure k) :=
  ⟨(by fun_prop : Measurable fun r : ℝ => min (r ^ 2) 1).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun r => by positivity)).2
      (lt_top_iff_ne_top.2 (lineProfile_min_ne_top hk hk0 hk1))⟩

/-- **`ψ_ℓ` is continuous** (real-valued). -/
theorem continuous_linePsi_toReal {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    Continuous fun τ => (linePsi k τ).toReal := by
  have heq : ∀ τ, (linePsi k τ).toReal = ∫ r, (1 - Real.cos (r * τ)) ∂(lineProfileMeasure k) := by
    intro τ
    rw [linePsi, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun r => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (r * τ)])
      (by fun_prop)]
  simp_rw [heq]
  rw [continuous_iff_continuousAt]
  intro τ₀
  refine tendsto_integral_filter_of_dominated_convergence
    (fun r => (2 + (|τ₀| + 1) ^ 2) * min (r ^ 2) 1)
    (Eventually.of_forall fun τ => (by fun_prop : Continuous fun r : ℝ =>
      1 - Real.cos (r * τ)).aestronglyMeasurable) ?_
    ((integrable_min_lineProfile hk hk0 hk1).const_mul _)
    (ae_of_all _ fun r => (by fun_prop : Continuous fun τ : ℝ => 1 - Real.cos (r * τ)).continuousAt)
  filter_upwards [Metric.ball_mem_nhds τ₀ zero_lt_one] with τ hτ
  refine ae_of_all _ fun r => ?_
  have hτ' : |τ| ≤ |τ₀| + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hτ
    have := abs_sub_abs_le_abs_sub τ τ₀
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one (r * τ)])]
  rw [mul_comm r τ, min_comm (r ^ 2) 1]
  refine (ScaleSpace.one_sub_cos_le τ r).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have : τ ^ 2 ≤ (|τ₀| + 1) ^ 2 := by
    rw [← sq_abs τ]
    exact pow_le_pow_left₀ (abs_nonneg _) hτ' 2
  linarith

/-- **`ψ_ℓ(τ) > 0` for `τ ≠ 0`.** -/
theorem linePsi_pos {k : ℝ → ℝ} (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) {τ : ℝ} (hτ : τ ≠ 0) : 0 < linePsi k τ := by
  obtain ⟨r₀, hr₀, hkr₀⟩ := hk_ne
  have hκ : 0 < k r₀ := lt_of_le_of_ne (hk_nonneg r₀ hr₀) (Ne.symm hkr₀)
  have hτ0 : 0 < |τ| := abs_pos.2 hτ
  set b := min r₀ (Real.pi / |τ|) with hb
  have hb0 : 0 < b := lt_min hr₀ (div_pos Real.pi_pos hτ0)
  have hbτ : b * |τ| ≤ Real.pi := by
    have : b ≤ Real.pi / |τ| := min_le_right _ _
    rwa [le_div_iff₀ hτ0] at this
  set c₁ := 1 - Real.cos (b * |τ| / 2) with hc₁
  have hc₁0 : 0 < c₁ := by
    have hx0 : 0 < b * |τ| / 2 := by positivity
    have hne : Real.cos (b * |τ| / 2) ≠ 1 := by
      intro h
      have := (Real.cos_eq_one_iff_of_lt_of_lt (x := b * |τ| / 2) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).1 h
      linarith
    have := Real.cos_le_one (b * |τ| / 2)
    rw [hc₁]
    exact sub_pos.2 (lt_of_le_of_ne this hne)
  rw [linePsi, lintegral_lineProfile hk (by fun_prop)]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (c₁ * (k r₀ / b)) * volume (Ioo (b / 2) b) := by
        rw [Real.volume_Ioo]
        refine ENNReal.mul_pos (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ?_
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
    _ = ∫⁻ _r in Ioo (b / 2) b, ENNReal.ofReal (c₁ * (k r₀ / b)) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo (b / 2) b, (ENNReal.ofReal (1 - Real.cos (r * τ)) +
          ENNReal.ofReal (1 - Real.cos (-r * τ))) * ENNReal.ofReal (k r / r) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => ?_))
        have hr0 : 0 < r := by linarith [hr.1]
        rw [ENNReal.ofReal_mul hc₁0.le]
        refine mul_le_mul' (le_add_right (ENNReal.ofReal_le_ofReal ?_)) (ENNReal.ofReal_le_ofReal ?_)
        · have hcos : Real.cos (r * τ) ≤ Real.cos (b * |τ| / 2) := by
            rw [← Real.cos_abs (r * τ), abs_mul, abs_of_pos hr0]
            refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
            · calc r * |τ| ≤ b * |τ| := mul_le_mul_of_nonneg_right hr.2.le hτ0.le
                _ ≤ Real.pi := hbτ
            · have := hr.1
              nlinarith
          rw [hc₁]
          linarith
        · have hrb : r ≤ r₀ := hr.2.le.trans (min_le_left _ _)
          calc k r₀ / b ≤ k r₀ / r := div_le_div_of_nonneg_left hκ.le hr0 hr.2.le
            _ ≤ k r / r := div_le_div_of_nonneg_right (hk hr0 hr₀ hrb) hr0.le
    _ ≤ _ := lintegral_mono_set (show Ioo (b / 2) b ⊆ Ioi 0 from
        fun r hr => (show (0 : ℝ) < r by linarith [hr.1]))

theorem levyExp_lineLevy_eq_integral {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (S : Mat d) (ω : Rd d) :
    levyExp (lineLevy k S) ω =
      ∫ u, (linePsi k (Real.sqrt (quad S u) * ⟪ω, u⟫)).toReal ∂normSphere d := by
  rw [levyExp, levyExpL_lineLevy, integral_toReal]
  · exact ((measurable_linePsi k).comp (by
      have := (continuous_quad_vec S).measurable
      fun_prop)).aemeasurable
  · exact ae_of_all _ fun u => lt_top_iff_ne_top.2 (linePsi_ne_top hk hk0 hk1 _)

/-- **`Σ ↦ ψ_Σ(ω)` is continuous on `PSD(d)`** (dominated convergence: on `tr Σ < tr Σ₀ + 1`,
`q_Σ(u) < tr Σ₀ + 1` on the sphere and `ψ_ℓ` is nondecreasing in `|τ|`). -/
theorem continuousOn_levyExp_lineLevy (hd : 1 ≤ d) {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (ω : Rd d) :
    ContinuousOn (fun S : Mat d => levyExp (lineLevy k S) ω) (psdSet d) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  simp_rw [levyExp_lineLevy_eq_integral hk hk0 hk1]
  intro S₀ _
  set T := S₀.trace + 1 with hT
  have hcont := continuous_linePsi_toReal hk hk0 hk1
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => (linePsi k (Real.sqrt T * ‖ω‖)).toReal) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun S => ?_
    exact (hcont.comp (((continuous_quad_vec S).sqrt).mul (continuous_const.inner continuous_id))
      ).aestronglyMeasurable
  · have hev : ∀ᶠ S in 𝓝[psdSet d] S₀, S ∈ psdSet d ∧ S.trace < T := by
      refine eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds ?_)
      have htc : Continuous fun S : Mat d => S.trace := continuous_id.matrix_trace
      exact htc.continuousAt.eventually (gt_mem_nhds (by rw [hT]; linarith : S₀.trace < T))
    filter_upwards [hev] with S hS
    filter_upwards [ae_normSphere_norm] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_mono (linePsi_ne_top hk hk0 hk1 _) (linePsi_mono_abs hk ?_)
    have hq : quad S u ≤ T :=
      ((quad_le_lamMax hS.1.isHermitian hu).trans (lamMax_le_trace hS.1)).trans hS.2.le
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    refine mul_le_mul (Real.sqrt_le_sqrt hq) ?_ (abs_nonneg _) (Real.sqrt_nonneg _)
    have := abs_real_inner_le_norm ω u
    rwa [hu, mul_one] at this
  · refine ae_of_all _ fun u => ?_
    exact ((hcont.comp (((continuous_quad u).sqrt).mul continuous_const)).tendsto S₀).mono_left
      nhdsWithin_le_nhds

/-- `ψ_I(e₁) > 0`. -/
theorem levyExp_lineLevy_one_pos (hd : 1 ≤ d) [NeZero d] {k : ℝ → ℝ}
    (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) :
    0 < levyExp (lineLevy k 1) (ebasis (0 : Fin d)) := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  have hL := isLevyMeasure_lineLevy hk hk0 hk1 (S := (1 : Mat d)) PosSemidef.one
  refine ENNReal.toReal_pos ?_ (hL.levyExpL_ne_top _)
  rw [levyExpL_lineLevy]
  intro h0
  have hm : Measurable fun u : Rd d =>
      linePsi k (Real.sqrt (quad 1 u) * ⟪ebasis (0 : Fin d), u⟫) :=
    (measurable_linePsi k).comp (by
      have := (continuous_quad_vec (1 : Mat d)).measurable
      fun_prop)
  have hae := (lintegral_eq_zero_iff hm).1 h0
  have hnull := normSphere_coord_null (d := d) hd 0
  have hall : ∀ᵐ u ∂normSphere d, False := by
    filter_upwards [hae, ae_normSphere_norm, compl_mem_ae_iff.2 hnull] with u hu hu1 hu0
    have hu0' : u 0 ≠ 0 := hu0
    rw [quad_one, hu1, one_pow, Real.sqrt_one, one_mul, inner_ebasis_left] at hu
    exact (linePsi_pos hk_nonneg hk hk_ne hu0').ne' hu
  rw [ae_iff] at hall
  simp only [not_false_eq_true, setOf_true, measure_univ] at hall
  exact one_ne_zero hall

/-- The transform of a law with triplet `(0, L_Σ, 0)`: `e^{-ψ_Σ}`. -/
theorem charFun_of_lineTriplet {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) {S : Mat d}
    {ν : Measure (Rd d)} {T : LevyTriplet d} (hA : T.A = 0) (hTν : T.ν = lineLevy k S)
    (hγ : T.γ = 0) (hT : HasTriplet ν T) (ω : Rd d) :
    charFun ν ω = ((Real.exp (-levyExp (lineLevy k S) ω) : ℝ) : ℂ) := by
  have hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν := by
    rw [hTν, ← push_neg_one_eq_map_neg, lineLevy_symm hk]
  rw [hT ω, T.lkExponent_symm hγ hsym ω, hA, hTν, quad_zero, zero_div, zero_add,
    Complex.ofReal_exp, Complex.ofReal_neg]

theorem levyExp_lineLevy_zero (k : ℝ → ℝ) (ω : Rd d) : levyExp (lineLevy k (0 : Mat d)) ω = 0 := by
  rw [levyExp, levyExpL_lineLevy]
  simp [quad_zero, linePsi]

/-- **`prop:similarity-line-family`(1)**, a cascade: for the laws `ν_Σ` with triplet
`(0, L_Σ, 0)` and `b ≥ 0`, every Loewner step in `PSD(d)` has an infinitely divisible increment,
and the increments satisfy (K1), (K2), (K4) and (K3) for every similarity. The measure-level
claims of (1) are `line_family_levy`. Spends A3(iii). -/
theorem line_family_cascade (hd : 2 ≤ d) (k : ℝ → ℝ) (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r)
    (hk_anti : AntitoneOn k (Ioi 0)) (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0)
    (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (b : ℝ) (hb : 0 ≤ b)
    (ν : Mat d → Measure (Rd d))
    (hν : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (ν S) ∧
      ∃ T : LevyTriplet d, T.A = 0 ∧ T.ν = lineLevy k S ∧ T.γ = 0 ∧ HasTriplet (ν S) T) :
    ∃ ρ : Mat d → Mat d → Measure (Rd d),
      (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
        IsProbabilityMeasure (ρ S S') ∧ IsInfinitelyDivisible (ρ S S') ∧
        multivariateGaussian 0 ((2 * b) • S') ∗ ν S' =
          (multivariateGaussian 0 ((2 * b) • S) ∗ ν S) ∗ ρ S S') ∧
      IsGWCascadeFamily (simSet d) loewnerLE ρ := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  set Φ : Mat d → Rd d → ℝ := fun S ω => b * quad S ω + levyExp (lineLevy k S) ω with hΦ
  refine simCascade_of_exponent Φ (fun ω => ?_) ?_ ?_ ?_
    (fun S => multivariateGaussian 0 ((2 * b) • S) ∗ ν S) fun S hS => ?_
  · exact ((continuous_const.mul (continuous_quad ω)).continuousOn).add
      (continuousOn_levyExp_lineLevy hd1 hk_anti hk0 hk1 ω)
  · rintro A ⟨c, hc, Q, hQ, rfl⟩ S _ ω
    simp only [hΦ]
    rw [quad_act, act_smul_left, lineLevy_sim k S (pow_pos hc 2) hQ, Real.sqrt_sq hc.le,
      levyExp_push]
  · refine ⟨ebasis 0, ?_⟩
    simp only [hΦ, quad_zero, mul_zero, levyExp_lineLevy_zero, add_zero]
    have h1 := levyExp_lineLevy_one_pos hd1 hk_nonneg hk_anti hk_ne hk0 hk1
    have h2 : 0 ≤ b * quad 1 (ebasis (0 : Fin d)) := mul_nonneg hb (quad_nonneg PosSemidef.one _)
    linarith
  · intro S S' hS hS' hle
    have hL' := isLevyMeasure_lineLevy hk_anti hk0 hk1 hS'
    have hL := isLevyMeasure_lineLevy hk_anti hk0 hk1 hS
    obtain ⟨D, hD, hDs, hDL⟩ := exists_levy_sub hL' (lineLevy_mono hk_anti hS hle)
      (lineLevy_symm hk_anti S) (lineLevy_symm hk_anti S')
    let T : LevyTriplet d :=
      { A := (2 * b) • (S' - S), ν := D, γ := 0, A_posSemidef := hle.smul (by positivity),
        ν_zero := hD.1, ν_integrable := hD.2 }
    obtain ⟨ρ, hρ, hρid, hρT⟩ := levy_khintchine_converse T
    refine ⟨ρ, hρ, hρid, fun ω => ?_⟩
    have hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν := by
      show D.map _ = D
      rw [← push_neg_one_eq_map_neg, hDs]
    have hadd : levyExp (lineLevy k S') ω = levyExp D ω + levyExp (lineLevy k S) ω := by
      have h := lintegral_add_measure (fun x : Rd d => ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫))
        D (lineLevy k S)
      rw [← hDL, levyExp, levyExp, levyExp, levyExpL, h, ← levyExpL, ← levyExpL,
        ENNReal.toReal_add (hD.levyExpL_ne_top ω) (hL.levyExpL_ne_top ω)]
    rw [hρT ω, T.lkExponent_symm rfl hsym ω, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    congr 2
    show -(quad ((2 * b) • (S' - S)) ω / 2 + levyExp D ω) = -(Φ S' ω - Φ S ω)
    simp only [hΦ, quad_smul, quad_sub, hadd]
    ring
  · obtain ⟨hνp, T, hA, hTν, hγ, hT⟩ := hν S hS
    haveI := hνp
    refine ⟨inferInstance, fun ω => ?_⟩
    rw [charFun_conv, charFun_multivariateGaussian_zero (hS.smul (by positivity)),
      charFun_of_lineTriplet hk_anti hA hTν hγ hT, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    simp only [hΦ, quad_smul]
    ring

/-- **`prop:similarity-line-family`(3)**, not shape-blind at index `0`, the laws: if `Σ ∈ PD(d)` is
not a multiple of `I`, the law `ν_Σ` with triplet `(0, L_Σ, 0)` is not rotation invariant (in
particular when `k(0+) < ∞`). The measure-level half is `line_family_levy_not_shape_blind`. Spends
A3(ii), with A3(iii) for the infinite divisibility of `ν_Σ`. -/
theorem line_family_not_shape_blind (hd : 2 ≤ d) (k : ℝ → ℝ)
    (hk_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ k r) (hk_anti : AntitoneOn k (Ioi 0))
    (hk_ne : ∃ r : ℝ, 0 < r ∧ k r ≠ 0) (hk0 : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * k r) ≠ ⊤)
    (hk1 : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤) (ν : Mat d → Measure (Rd d))
    (hν : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (ν S) ∧
      ∃ T : LevyTriplet d, T.A = 0 ∧ T.ν = lineLevy k S ∧ T.γ = 0 ∧ HasTriplet (ν S) T) :
    ∀ S : Mat d, S.PosDef → (¬ ∃ c : ℝ, S = c • (1 : Mat d)) →
      ¬ IsRotationInvariant (ν S) := by
  intro S hS hns hrot
  refine line_family_levy_not_shape_blind hd k hk_nonneg hk_anti hk_ne hk0 hk1 S hS hns ?_
  obtain ⟨hνp, T, hA, hTν, hγ, hT⟩ := hν S hS.posSemidef
  haveI := hνp
  /- `ν_Σ` is infinitely divisible: it is the law A3(iii) gives for its triplet. -/
  obtain ⟨μ', hμ', hμ'id, hμ'T⟩ := levy_khintchine_converse T
  have hνμ : ν S = μ' := by
    refine eq_of_charFun_eq fun ω => ?_
    rw [hT ω, hμ'T ω]
  have hid : IsInfinitelyDivisible (ν S) := hνμ ▸ hμ'id
  intro Q hQ
  set e := orthIsometry hQ with he
  have hesymm : ∀ z, e.symm z = lin Qᵀ z := by
    intro z
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply, he, orthIsometry_apply,
      show lin Q (lin Qᵀ z) = lin (Q * Qᵀ) z by rw [lin_mul]; rfl, orth_mul_transpose hQ, lin_one]
    rfl
  have hT' : HasTriplet (ν S) (T.pushIso e) := fun z => by
    rw [T.lkExponent_pushIso, ← hT, hesymm, ← charFun_map_lin, ← push, hrot Q hQ]
  have huniq := (levy_khintchine_unique (ν S) hid T _ hT hT').2.1
  rw [← hTν, push]
  conv_rhs => rw [huniq]
  rfl

end AffineHemigroup
