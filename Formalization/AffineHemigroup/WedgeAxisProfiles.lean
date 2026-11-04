/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.WedgeAxis
import AffineHemigroup.SimilarityOrbit
import AffineHemigroup.CascadeDivisible
import AffineHemigroup.InvariantOrders
import AffineHemigroup.StableExponentCone

/-!
# `prop:wedge-axis-profiles`(1): the profiles along a cone order

Blueprint: `blueprint/src/parts/05-table.tex`, `prop:wedge-axis-profiles`, clause (1); clause (2) is
`AffineHemigroup.WedgeAxisCell`. The route is the node's, paragraph by paragraph.

* **The chain** `s ↦ e^{sX}` (`mexp_infinitelyDivisible`) makes the increment `μ_{I,e^X}` infinitely
  divisible through `chain_infinitelyDivisible`, spending A6. That lemma asks for a partial order;
  for `C ⊆ PSD(d)` the antisymmetry of `≼⁺_C` is read from the Loewner order, so the entry A9 stays
  unspent, as in `AffineHemigroup.WedgeAxisChain`.
* **The Gaussian part**: `N(0, aΣ) * (Σ^{1/2})_*ν_I` is the orbit `(Σ^{1/2})_*(N(0, aI) * ν_I)`
  (`affineOrbit_gaussian_conv`), so (a)–(c) of `lem:gw-kernels-from-origin`(2) are those of an orbit
  of a rotation-invariant law, and only (d) reads the two factors.
* **The right-continuous modification** `k̃(r) = sup_{s > r} k(s)` (`RadialProfile.rightMod`) has
  the same exponent, off the spheres of the countably many radii of discontinuity, and the same
  lower exponent, by the two comparisons of the node's proof.

Ledger: A6 (`chain_infinitelyDivisible`), A3(i)–(ii) (`sim_orbit_id_increment`), A3(iii)
(`stable_order_gl_row`). Neither A2, nor A4, nor A5.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology ENNReal

variable {d : ℕ}

/-! ## The law `N(0, aI) * ν_I` and its orbit -/

/-- `\widehat{N(0, aI) * ν}(ω) = e^{-a|ω|²/2} ν̂(ω)`. -/
theorem charFun_gaussian_conv {a : ℝ} (ha : 0 ≤ a) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (ω : Rd d) :
    charFun (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν) ω =
      ((Real.exp (-(a * ‖ω‖ ^ 2 / 2)) : ℝ) : ℂ) * charFun ν ω := by
  rw [charFun_conv, charFun_multivariateGaussian_zero (PosSemidef.one.smul ha), quad_smul, quad_one]

/-- **The orbit of `N(0, aI) * ν`** is `N(0, aΣ) * (Σ^{1/2})_*ν`, `Σ ∈ PSD(d)`. -/
theorem affineOrbit_gaussian_conv {a : ℝ} (ha : 0 ≤ a) (ν : Measure (Rd d))
    [IsProbabilityMeasure ν] {S : Mat d} (hS : S.PosSemidef) :
    affineOrbit (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν) S =
      multivariateGaussian 0 (a • S) ∗ affineOrbit ν S := by
  refine eq_of_charFun_eq fun ω => ?_
  rw [affineOrbit, push, charFun_map_lin, charFun_gaussian_conv ha, charFun_conv,
    charFun_multivariateGaussian_zero (hS.smul ha), affineOrbit, push, charFun_map_lin, quad_smul,
    ← quad_one, ← quad_act, act_msqrt_one hS]

/-- `N(0, aI) * ν` is rotation invariant when `ν` is. -/
theorem isRotationInvariant_gaussian_conv {a : ℝ} (ha : 0 ≤ a) {ν : Measure (Rd d)}
    [IsProbabilityMeasure ν] (hν : IsRotationInvariant ν) :
    IsRotationInvariant (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν) := by
  intro Q hQ
  have hν' := hν Q hQ
  refine eq_of_charFun_eq fun ω => ?_
  rw [push, charFun_map_lin, charFun_gaussian_conv ha, charFun_gaussian_conv ha]
  have h1 : charFun ν (lin Qᵀ ω) = charFun ν ω := by
    conv_rhs => rw [← hν', push, charFun_map_lin]
  have h2 : ‖lin Qᵀ ω‖ ^ 2 = ‖ω‖ ^ 2 := by
    rw [← quad_one, ← quad_act, act_orth_one hQ, quad_one]
  rw [h1, h2]

/-- `N(0, aI) * ν_I ≠ δ₀` for the law `ν_I` of a profile. -/
theorem gaussian_conv_profileLaw_ne_dirac (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (K : RadialProfile d)
    {ν : Measure (Rd d)} (hν : IsProfileLaw K ν) :
    multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ≠ Measure.dirac 0 := by
  haveI := hν.1
  intro h
  obtain ⟨ω, hω⟩ := K.exists_exponent_ne_zero hd
  have h1 := charFun_gaussian_conv ha ν ω
  rw [h, charFun_dirac, hν.2 ω, ← Complex.ofReal_mul, ← Real.exp_add] at h1
  simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
  have h2 : Real.exp (-(a * ‖ω‖ ^ 2 / 2) + -K.exponent ω) = 1 := by exact_mod_cast h1.symm
  rw [Real.exp_eq_one_iff] at h2
  have hψ : 0 ≤ K.exponent ω := ENNReal.toReal_nonneg
  have hq : 0 ≤ a * ‖ω‖ ^ 2 / 2 := by positivity
  exact hω (by linarith)

/-! ## (1), sufficiency -/

/-- **The orbit of `N(0, aI) * ν_I` along the stable order**: for a profile with `R(λ) ≥ λ^γ`,
`Σ ↦ (Σ^{1/2})_*(N(0, aI) * ν_I)` is the family of kernels from the origin of a
`(GL(d), ≤_γ)`-cascade family (the node's sufficiency, through
`lem:gw-kernels-from-origin`(3)). Spends A3(iii). -/
theorem gaussian_orbit_kernels (hd : 2 ≤ d) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (K : RadialProfile d) (hR : ∀ lam : ℝ, 1 ≤ lam → lam ^ γ ≤ dilRatio K.k lam)
    {ν : Measure (Rd d)} (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a) :
    IsKernelsFromOrigin (glSet d) (stablePlusLE γ)
      (affineOrbit (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := hν.1
  have hrot := isRotationInvariant_gaussian_conv ha (profileLaw_props hd1 K ν hν).1
  have hne := gaussian_conv_profileLaw_ne_dirac hd1 ha K hν
  have hord := stablePlusLE_order (d := d) hd hγ0 hγ2
  have hW : IsWedgeDatum (glSet d) (stablePlusLE γ) :=
    hord.2.2.2.2.2.1 _ glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  have hm := affineOrbit_isOriginKernels hrot hne
  have hz : HasNoZeros (affineOrbit (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν)) :=
    fun S hS ω => by
      rw [charFun_affineOrbit hrot hS, charFun_gaussian_conv ha, hν.2, ← Complex.ofReal_mul]
      exact_mod_cast (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  obtain ⟨n, hn, hnm⟩ := stable_order_gl_row hd hγ0 hγ2 K hR ν hν
  refine (gw_kernels_from_origin_converse hW _ hm hz ?_).1
  intro S S' hS hS' hle
  obtain ⟨hp, hc⟩ := (gw_kernels_from_origin hW n hn).2 S S' hS hS' hle
  have hL : (S' - S).PosSemidef := hord.2.2.2.1 S S' hS hS' hle
  have hP : (a • (S' - S)).PosSemidef := hL.smul ha
  refine ⟨multivariateGaussian 0 (a • (S' - S)) ∗ n S S', inferInstance, ?_⟩
  rw [affineOrbit_gaussian_conv ha ν hS', affineOrbit_gaussian_conv ha ν hS]
  rw [hnm S' hS', hnm S hS] at hc
  refine eq_of_charFun_eq fun ω => ?_
  rw [hc]
  simp only [charFun_conv]
  rw [charFun_multivariateGaussian_zero (hS'.smul ha),
    charFun_multivariateGaussian_zero (hS.smul ha),
    charFun_multivariateGaussian_zero hP, smul_sub, quad_sub]
  have he : ((Real.exp (-((quad (a • S') ω) / 2)) : ℝ) : ℂ) =
      ((Real.exp (-(quad (a • S) ω / 2)) : ℝ) : ℂ) *
        ((Real.exp (-((quad (a • S') ω - quad (a • S) ω) / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  ring

/-- **(1), sufficiency, along the cone**: `β(C) ≤ β₋(k)` puts `N(0, aI) * ν_I` in `𝔉(C)`, by the
restriction from `≤_{β(C)}`. -/
theorem gaussian_conv_mem_coneLaws (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) (hβ : 0 < coneIndex C)
    (K : RadialProfile d) {ν : Measure (Rd d)} (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a)
    (hle : coneIndex C ≤ lowerExp K.k) :
    multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈ coneLaws C := by
  have hd1 : 1 ≤ d := by omega
  have hexp := dilRatio_exponents hd1 K
  have hγ2 : coneIndex C < 2 := lt_of_le_of_lt hle hexp.2.2.2.2.2.1
  have hR := (hexp.2.2.2.2.2.2.2 _ hβ.le).2 hle
  obtain ⟨n, hn, hnm⟩ := gaussian_orbit_kernels hd hβ hγ2 K hR hν ha
  have hsub := (wedge_axis_index hd hCsym hC hO hI hpt hpsd hdef).2.2.2.1.2
  exact ⟨n, gw_family_restrict_of_le subset_rfl
    (fun S S' _ _ h => causalPlusLE_stablePlusLE hd1 hβ hsub h) n hn,
    by rw [hnm 1 PosSemidef.one, affineOrbit_one]⟩

/-! ## (1), the right-continuous modification -/

namespace RadialProfile

variable (K : RadialProfile d)

/-- The set of values of `k` to the right of `r > 0` is bounded above, by `k(r)`. -/
theorem bddAbove_image_Ioi {r : ℝ} (hr : 0 < r) : BddAbove (K.k '' Ioi r) :=
  ⟨K.k r, by
    rintro _ ⟨s, hs, rfl⟩
    exact K.k_antitone hr (hr.trans hs) (le_of_lt hs)⟩

/-- `k̃(r) := k(r+) = sup_{s > r} k(s)`, the right limit of a nonincreasing `k`. -/
noncomputable def rightLimK (r : ℝ) : ℝ := sSup (K.k '' Ioi r)

theorem nonempty_image_Ioi (r : ℝ) : (K.k '' Ioi r).Nonempty := ⟨_, r + 1, by simp, rfl⟩

theorem k_le_rightLimK {r s : ℝ} (hr : 0 < r) (hs : r < s) : K.k s ≤ K.rightLimK r :=
  le_csSup (K.bddAbove_image_Ioi hr) ⟨s, hs, rfl⟩

theorem rightLimK_le {r : ℝ} (hr : 0 < r) : K.rightLimK r ≤ K.k r :=
  csSup_le (K.nonempty_image_Ioi r) fun _ ⟨_, hs, h⟩ =>
    h ▸ K.k_antitone hr (hr.trans hs) (le_of_lt hs)

theorem rightLimK_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ K.rightLimK r :=
  (K.k_nonneg (r + 1) (by simp only [mem_Ioi]; linarith)).trans
    (K.k_le_rightLimK hr (by linarith))

theorem rightLimK_antitone : AntitoneOn K.rightLimK (Ioi 0) := by
  intro r hr s hs hrs
  refine csSup_le (K.nonempty_image_Ioi s) fun _ ⟨t, ht, h⟩ => ?_
  exact h ▸ K.k_le_rightLimK hr (lt_of_le_of_lt hrs ht)

/-- `k̃` is right-continuous. -/
theorem rightLimK_rightCont {r : ℝ} (hr : 0 < r) :
    ContinuousWithinAt K.rightLimK (Ici r) r := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨_, ⟨s, hs, rfl⟩, hcs⟩ := exists_lt_of_lt_csSup (K.nonempty_image_Ioi r) hc
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with t ht hts
    exact hcs.trans_le (K.k_le_rightLimK (lt_of_lt_of_le hr ht) hts)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_of_le_of_lt (K.rightLimK_antitone hr (lt_of_lt_of_le hr ht) ht) hc

/-- `k̃ = k` where `k` is continuous. -/
theorem rightLimK_eq {r : ℝ} (hr : 0 < r) (hc : ContinuousWithinAt K.k (Ioi 0) r) :
    K.rightLimK r = K.k r := by
  refine le_antisymm (K.rightLimK_le hr) ?_
  have hlim : Tendsto K.k (𝓝[>] r) (𝓝 (K.k r)) := (hc.mono (Ioi_subset_Ioi hr.le)).tendsto
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact K.k_le_rightLimK hr hs

/-- **The right-continuous modification** `r ↦ k(r+)` of a profile: `k̃ ≤ k` gives the
integrability, and `k̃ ≥ k(r₀) > 0` on `(0, r₀)`. -/
noncomputable def rightMod : RadialProfile d where
  k := K.rightLimK
  k_nonneg := fun _ hr => K.rightLimK_nonneg hr
  k_antitone := K.rightLimK_antitone
  k_ne_zero := by
    obtain ⟨r, hr, hk⟩ := K.exists_pos
    refine ⟨r / 2, by simp only [mem_Ioi]; linarith, ne_of_gt ?_⟩
    exact hk.trans_le (K.k_le_rightLimK (by linarith) (by linarith))
  integrable := by
    refine ne_top_of_le_ne_top K.integrable (lintegral_mono fun x => ?_)
    rcases (norm_nonneg x).eq_or_lt with h | h
    · simp [← h]
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact div_le_div_of_nonneg_right (K.rightLimK_le h) (by positivity)

theorem rightMod_k : K.rightMod.k = K.rightLimK := rfl

/-- **The two profiles have the same exponent**: they differ only on the spheres of countably many
radii, a null set. -/
theorem rightMod_exponentL (hd : 1 ≤ d) (ω : Rd d) : K.rightMod.exponentL ω = K.exponentL ω := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hc := K.k_antitone.countable_not_continuousWithinAt
  set D : Set ℝ := {r ∈ Ioi (0 : ℝ) | ¬ContinuousWithinAt K.k (Ioi 0) r} with hD
  have hnull : (volume : Measure (Rd d)) (⋃ r ∈ D, Metric.sphere (0 : Rd d) r) = 0 :=
    (measure_biUnion_null_iff hc).2 fun r _ => Measure.addHaar_sphere volume 0 r
  refine lintegral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
  rcases (norm_nonneg x).eq_or_lt with h | h
  · simp [m, ← h, zero_pow (by omega : d ≠ 0)]
  · have hcx : ContinuousWithinAt K.k (Ioi 0) ‖x‖ := by
      by_contra hcon
      exact hx (mem_biUnion (show ‖x‖ ∈ D from ⟨h, hcon⟩) (by simp))
    simp only [m, rightMod_k, K.rightLimK_eq h hcx]

theorem rightMod_exponent (hd : 1 ≤ d) (ω : Rd d) : K.rightMod.exponent ω = K.exponent ω := by
  rw [exponent, exponent, K.rightMod_exponentL hd]

/-- The modification has the same law. -/
theorem rightMod_isProfileLaw (hd : 1 ≤ d) {ν : Measure (Rd d)} (hν : IsProfileLaw K ν) :
    IsProfileLaw K.rightMod ν :=
  ⟨hν.1, fun ω => by rw [hν.2, K.rightMod_exponent hd]⟩

/-- `R̃ ≥ R`: `k(s/λ) ≥ R(λ)k(s)`, and `s` decreases to `r`. -/
theorem dilRatio_le_rightMod (hd : 1 ≤ d) {lam : ℝ} (hlam : 1 ≤ lam) :
    dilRatio K.k lam ≤ dilRatio K.rightMod.k lam := by
  have hl0 : 0 < lam := by linarith
  have hR1 := (dilRatio_mem hd K lam hlam).2
  refine le_dilRatio K.rightMod fun r hr _ => ?_
  change dilRatio K.k lam * K.rightLimK r ≤ K.rightLimK (r / lam)
  rw [← le_div_iff₀' (by linarith)]
  refine csSup_le (K.nonempty_image_Ioi r) fun _ ⟨s, hs, h⟩ => ?_
  have hs' : r < s := hs
  subst h
  have hs0 : 0 < s := hr.trans hs'
  rw [le_div_iff₀' (by linarith)]
  have hlt : r / lam < s / lam := div_lt_div_of_pos_right hs' hl0
  refine le_trans ?_ (K.k_le_rightLimK (div_pos hr hl0) hlt)
  rcases (K.k_nonneg s hs0).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact K.k_nonneg _ (div_pos hs0 hl0)
  · exact dilRatio_le hd K hlam hs0 h0

/-- `R̃(τ) ≥ τ^α` for `τ ≥ 1` gives `R(λ) ≥ λ^α`: for `r/λ < s < r`,
`k(r/λ) ≥ k̃(s/τ) ≥ τ^α k̃(s) ≥ (sλ/r)^α k(r)` with `τ = sλ/r`, and `s` increases to `r`. -/
theorem rpow_le_dilRatio_of_rightMod (hd : 1 ≤ d) {α : ℝ} (_hα : 0 ≤ α)
    (h : ∀ τ : ℝ, 1 ≤ τ → τ ^ α ≤ dilRatio K.rightMod.k τ) {lam : ℝ} (hlam : 1 ≤ lam) :
    lam ^ α ≤ dilRatio K.k lam := by
  rcases hlam.eq_or_lt with rfl | hlam1
  · rw [Real.one_rpow, dilRatio_one]
  have hl0 : 0 < lam := by linarith
  refine le_dilRatio K fun r hr hk => ?_
  have hr' : 0 < r / lam := div_pos hr hl0
  have hrl : r / lam < r := div_lt_self hr hlam1
  have hkey : ∀ s ∈ Ioo (r / lam) r, (s * lam / r) ^ α * K.k r ≤ K.k (r / lam) := by
    intro s hs
    have hs0 : 0 < s := hr'.trans hs.1
    have hτ : 1 < s * lam / r := by
      rw [one_lt_div hr]
      have := hs.1
      rwa [div_lt_iff₀ hl0] at this
    have hτ0 : 0 < s * lam / r := by linarith
    have hks : K.k r ≤ K.rightLimK s := K.k_le_rightLimK hs0 hs.2
    have hks0 : 0 < K.rightMod.k s := lt_of_lt_of_le hk hks
    have h1 := dilRatio_le hd K.rightMod hτ.le hs0 hks0
    have heq : s / (s * lam / r) = r / lam := by
      field_simp
    rw [heq] at h1
    calc (s * lam / r) ^ α * K.k r ≤ (s * lam / r) ^ α * K.rightLimK s :=
          mul_le_mul_of_nonneg_left hks (by positivity)
      _ ≤ dilRatio K.rightMod.k (s * lam / r) * K.rightMod.k s :=
          mul_le_mul_of_nonneg_right (h _ hτ.le) hks0.le
      _ ≤ K.rightLimK (r / lam) := h1
      _ ≤ K.k (r / lam) := K.rightLimK_le hr'
  have hcont : ContinuousAt (fun s : ℝ => (s * lam / r) ^ α * K.k r) r := by
    refine ContinuousAt.mul ?_ continuousAt_const
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
    rw [mul_div_cancel_left₀ _ hr.ne']
    exact hl0.ne'
  have hlim : Tendsto (fun s : ℝ => (s * lam / r) ^ α * K.k r) (𝓝[<] r)
      (𝓝 ((r * lam / r) ^ α * K.k r)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [mul_div_cancel_left₀ _ hr.ne'] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hrl] with s hs
  exact hkey s hs

/-- **The two profiles have the same lower exponent.** -/
theorem lowerExp_rightMod (hd : 1 ≤ d) : lowerExp K.rightMod.k = lowerExp K.k := by
  have h1 := dilRatio_exponents hd K
  have h2 := dilRatio_exponents hd K.rightMod
  refine le_antisymm ?_ ?_
  · refine (h1.2.2.2.2.2.2.2 _ h2.2.2.1).1 fun lam hlam => ?_
    exact K.rpow_le_dilRatio_of_rightMod hd h2.2.2.1
      (fun τ hτ => (h2.2.2.2.2.2.2.1 τ hτ).1) hlam
  · refine (h2.2.2.2.2.2.2.2 _ h1.2.2.1).1 fun lam hlam => ?_
    exact (h1.2.2.2.2.2.2.1 lam hlam).1.trans (K.dilRatio_le_rightMod hd hlam)

end RadialProfile

/-! ## The chain, and (1), necessity -/

/-- **The increment of a step `I → e^X`, `X ∈ C`, is infinitely divisible**: the curve
`s ↦ e^{sX}` is a chain for `≼⁺_C`, as `A = e^{sX/2}` carries `I ≼⁺_C e^{(s'-s)X}` to
`e^{sX} ≼⁺_C e^{s'X}` (the node's first paragraph). Spends A6. -/
theorem mexp_infinitelyDivisible (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpsd : C ⊆ psdSet d) {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : IsGWCascadeFamily (glSet d) (causalPlusLE C) μ) {X : Mat d} (hX : X ∈ C) :
    IsInfinitelyDivisible (μ 1 (mexp X)) := by
  have hXs : X.IsSymm := hCsym hX
  have hpo : IsPartialOrderOn (psdSet d) (causalPlusLE C) :=
    ⟨fun S _ => causalPlusLE_refl S,
      fun S _ S' hS' h h' => le_antisymm
        ((loewnerLE_iff_le _ _).1 (causalPlusLE_loewner hpsd hS' h))
        ((loewnerLE_iff_le _ _).1 (causalPlusLE_loewner hpsd ‹_› h')),
      fun S _ S' _ S'' _ h h' => causalPlusLE_trans_of_cone hd hCsym hC hO hI h h'⟩
  have hsym : ∀ s : ℝ, (s • X).IsSymm := fun s => hXs.smul s
  have hmono : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      causalPlusLE C (mexp (s • X)) (mexp (t • X)) := by
    intro s _ t _ hst
    have hδ : (t - s) • X ∈ C := hC.2.2.2 _ (by linarith) X hX
    have h1 := causalPlusLE_one_mexp hCsym hO hδ
    set A := mexp ((s / 2) • X) with hA
    have hApd : A.PosDef := posDef_mexp (hsym _)
    have hAgl : A ∈ glSet d := (isUnit_iff_isUnit_det A).1 hApd.isUnit
    have hAT : Aᵀ = A := by
      have := hApd.isHermitian
      rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    have h2 := causalPlusLE_act_of_cone hO hAgl h1
    have he1 : act A 1 = mexp (s • X) := by
      rw [act, hAT, Matrix.mul_one, hA, ← mexp_add_smul]
      congr 2
      ring
    have he2 : act A (mexp ((t - s) • X)) = mexp (t • X) := by
      rw [act, hAT, hA, ← mexp_add_smul, ← mexp_add_smul]
      congr 2
      ring
    rwa [he1, he2] at h2
  have hγ : IsWChain (psdSet d) (causalPlusLE C) (fun s : ℝ => mexp (s • X)) 1 (mexp X) :=
    ⟨(continuous_mexp.comp (by fun_prop)).continuousOn,
      fun s _ => (posDef_mexp (hsym s)).posSemidef, hmono,
      by simp [mexp_zero], by simp⟩
  exact chain_infinitelyDivisible hd (psdSet d) subset_rfl (causalPlusLE C) hpo μ
    (fun S hS S' hS' h => hμ.isProbability (S, S') ⟨hS, hS', h⟩) (fun S hS => hμ.diag S hS)
    (fun S hS S' hS' S'' hS'' h h' => hμ.cascade S S' S'' hS hS' hS'' h h')
    (fun ω => hμ.continuous ω) 1 (mexp X) _ hγ

/-- **(1), necessity, for a right-continuous profile**: a law `N(0, aI) * ν_I` in `𝔉(C)` has
`β(C) ≤ β₋(k)`. Spends A6 (the chain) and A3(i)–(ii) (`sim_orbit_id_increment` at `h = id`,
`C(Σ) = aΣ`). -/
theorem le_lowerExp_of_mem_coneLaws (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r)
    {ν : Measure (Rd d)} (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a)
    (hmem : multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈ coneLaws C) :
    coneIndex C ≤ lowerExp K.k := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := hν.1
  obtain ⟨μ, hμ, hμ1⟩ := hmem
  have hidx := wedge_axis_index hd hCsym hC hO hI hpt hpsd hdef
  have hβ0 := hidx.2.2.1
  obtain ⟨hpdC, ⟨⟨X, ⟨hXC, hX0⟩, hfX⟩, -⟩, -, -⟩ := hidx
  have hfX' : X.trace / lamMin X - d = coneIndex C := hfX
  have hl : 0 < lamMin X := lamMin_pos (hpdC X hXC hX0)
  have htr : X.trace = ((d : ℝ) + coneIndex C) * lamMin X := by
    rw [← hfX']
    field_simp
    ring
  have horb := (gl_kernels_of_rays (fun S S' _ _ h => causalPlusLE_of_rayLE h) hμ).2.2.2.2.1
  refine ((dilRatio_exponents hd1 K).2.2.2.2.2.2.2 _ hβ0).1 fun lam hlam => ?_
  rcases hlam.eq_or_lt with rfl | hlam1
  · rw [Real.one_rpow, dilRatio_one]
  have hl0 : 0 < lam := by linarith
  have hlog := Real.log_pos hlam1
  set t := 2 * Real.log lam / lamMin X with ht
  have ht0 : 0 < t := by positivity
  have htl : t * lamMin X = 2 * Real.log lam := by
    rw [ht]; field_simp
  have hY : t • X ∈ C := hC.2.2.2 t ht0.le X hXC
  have hYs : (t • X).IsSymm := hCsym hY
  set M := mexp (t • X) with hMdef
  have hM : M.PosDef := posDef_mexp hYs
  have h1M := causalPlusLE_one_mexp hCsym hO hY
  haveI hρ := hμ.isProbability (1, M) ⟨PosSemidef.one, hM.posSemidef, h1M⟩
  have hid := mexp_infinitelyDivisible hd1 hCsym hC hO hI hpsd hμ hY
  have hcasc := hμ.cascade 0 1 M PosSemidef.zero PosSemidef.one hM.posSemidef
    (causalPlusLE_zero_left 1) h1M
  rw [horb M hM.posSemidef, hμ1, affineOrbit_gaussian_conv ha ν hM.posSemidef] at hcasc
  have hstep : multivariateGaussian 0 (a • id M) ∗ affineOrbit ν (id M) =
      (multivariateGaussian 0 (a • id (1 : Mat d)) ∗ affineOrbit ν (id 1)) ∗ μ 1 M := by
    simp only [id, affineOrbit_one]
    rw [hcasc, Measure.conv_comm]
  have hdet := (sim_orbit_id_increment hd K hrc ν hν id (fun S => a • S) (fun _ h => h)
    (fun _ h => h.posSemidef.smul ha) 1 M PosDef.one hM (μ 1 M) hρ hid hstep).2.2.2
  simp only [id, relStep_one_left] at hdet
  have hlM : lamMin M = lam ^ 2 := by
    rw [hMdef, lamMin_eq_eigUp_zero hM.isHermitian, eigUp_mexp (isHermitian_of_isSymm hYs)]
    beta_reduce
    rw [← lamMin_eq_eigUp_zero (isHermitian_of_isSymm hYs), lamMin_smul ht0.le, htl, two_mul,
      Real.exp_add, Real.exp_log hl0, sq]
  have hdM : M.det = (lam ^ 2) ^ ((d : ℝ) + coneIndex C) := by
    rw [hMdef, det_mexp_smul, htr, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    push_cast
    linear_combination ((d : ℝ) + coneIndex C) * htl
  rw [hlM, hdM, Real.sqrt_sq hl0.le, ← pow_mul_sqrt_rpow_sq (by positivity : (0 : ℝ) < lam ^ 2),
    Real.sqrt_sq hl0.le] at hdet
  have h' : (lam ^ coneIndex C) ^ 2 ≤ dilRatio K.k lam ^ 2 :=
    le_of_mul_le_mul_left hdet (by positivity)
  exact (pow_le_pow_iff_left₀ (by positivity) (by linarith [(dilRatio_mem hd1 K lam hlam).2])
    two_ne_zero).1 h'

/-! ## `prop:wedge-axis-profiles`(1) -/

/-- **`prop:wedge-axis-profiles`(1)**, the cone statement: for a cone `C` of the case (2)(c) of
`thm:wedge-axis` with `β(C) > 0`, a profile `k` (no right-continuity asked), its law `ν_I` and
`a ≥ 0`, `N(0, aI) * ν_I ∈ 𝔉(C)` if and only if `β(C) ≤ β₋(k)`. Spends A6 and A3(i)–(iii). -/
theorem wedge_axis_profiles (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) (hβ : 0 < coneIndex C)
    (K : RadialProfile d) (ν : Measure (Rd d)) (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a) :
    multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈ coneLaws C ↔ coneIndex C ≤ lowerExp K.k := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨fun h => ?_, gaussian_conv_mem_coneLaws hd hCsym hC hO hI hpt hpsd hdef hβ K hν ha⟩
  rw [← K.lowerExp_rightMod hd1]
  exact le_lowerExp_of_mem_coneLaws hd hCsym hC hO hI hpt hpsd hdef K.rightMod
    (fun r hr => K.rightLimK_rightCont hr) (K.rightMod_isProfileLaw hd1 hν) ha h

/-- `𝔉_α = 𝔉(C_α)` for finite `α`. -/
theorem rowLaws_coe_eq_coneLaws (α : ℝ) :
    rowLaws d (α : WithTop ℝ) = coneLaws (stableGenCone d α) := rfl

/-- **`prop:wedge-axis-profiles`(1)**, "in particular": for `0 < α < 2`, `N(0, aI) * ν_I ∈ 𝔉_α` if
and only if `R(λ) ≥ λ^α` for every `λ ≥ 1`, and then `Σ ↦ N(0, aΣ) * (Σ^{1/2})_*ν_I`, `Σ ∈ PSD(d)`,
is the family of kernels from the origin of a `(GL(d), ≼⁺_{C_α})`-cascade family. -/
theorem wedge_axis_profiles_stable (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (K : RadialProfile d) (ν : Measure (Rd d)) (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a) :
    (multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈ rowLaws d (α : WithTop ℝ) ↔
        ∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam) ∧
      ((∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam) →
        IsKernelsFromOrigin (glSet d) (causalPlusLE (stableGenCone d α))
          fun S => multivariateGaussian 0 (a • S) ∗ affineOrbit ν S) := by
  have hd1 : 1 ≤ d := by omega
  haveI := hν.1
  obtain ⟨hCsym, hO, hC, hI, hpt⟩ := stableGenCone_props hd1 hα0.le
  have hidx := coneIndex_stableGenCone hd hα0.le
  refine ⟨?_, fun hR => ?_⟩
  · rw [rowLaws_coe_eq_coneLaws, wedge_axis_profiles hd hCsym hC hO hI hpt (fun X hX => hX.1)
      (stableGenCone_det_ne_zero hd1 hα0.le) (by rwa [hidx]) K ν hν ha, hidx]
    exact ((dilRatio_exponents hd1 K).2.2.2.2.2.2.2 α hα0.le).symm
  · obtain ⟨n, hn, hnm⟩ := gaussian_orbit_kernels hd hα0 hα2 K hR hν ha
    exact ⟨n, gw_family_restrict_of_le subset_rfl
      (fun S S' _ _ h => causalPlusLE_stablePlusLE hd1 hα0 subset_rfl h) n hn,
      fun S hS => by rw [hnm S hS, affineOrbit_gaussian_conv ha ν hS]⟩

end AffineHemigroup
