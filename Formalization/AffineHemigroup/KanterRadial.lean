/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Kanter
import AffineHemigroup.ConcaveDensity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The radial part of one uniform law of Kanter's

Blueprint: `prop:isotropic-radial-monotone`, the paragraph *the radial part of one uniform law*
(`blueprint/src/parts/03-isotropic.tex`). Wave 2, group B (Q-0281).

Write `ω_d` for the volume of the unit ball of `ℝ^d` and `φ(x) := ω_d |x|^d` for the *volume
coordinate*: `φ⁻¹((0,v])` is the punctured closed ball `B(v)` of volume `v`. The statement here
(`concaveENN_kanterUniform`) is that for a nonempty compact convex symmetric `K ⊆ ℝ^d` the function
`v ↦ u_K(B(v))` is concave on `[0,∞)`.

**The route, and how it differs from the blueprint's.** The blueprint writes `u_K(B(v))` through
the fraction `φ_K(r)` of the sphere of radius `r` in `V = span K` that lies in `K`, and substitutes
`w = ω_d r^d`. The Lean takes polar coordinates in `V` (Mathlib's `homeomorphUnitSphereProd`, for
any finite-dimensional inner product space, `lintegral_polar_addHaar`) and reads each ray: for a
unit `θ ∈ V` the set `{s > 0 : sθ ∈ K}` is an interval `(0, ρ_θ)` or `(0, ρ_θ]`, because `K` is
convex and contains `0`, so the ray contributes
`∫_0^{min(ρ_θ, r_v)} s^{k-1} ds = min(ρ_θ^k, (v/ω_d)^{k/d})/k`, `k = dim V ≤ d`. That is the minimum
of a constant and a concave power of `v` (`k/d ≤ 1`), so it is concave in `v`, and so is its
integral over the sphere of `V`. No derivative and no surface measure of `K ∩ ∂B` is formed. At
`k = 0`, `K = {0}` and `B(v)` misses the origin, so the function is `0`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ProbabilityTheory
open scoped ENNReal Topology

variable {d : ℕ}

/-! ## Polar coordinates in a finite-dimensional inner product space -/

/-- **Polar coordinates for a nonnegative function** on a nontrivial finite-dimensional inner
product space `E` with an additive Haar measure `μ`: `∫ f dμ = ∫_{S} σ(dη) ∫_0^∞ f(rη) r^{n-1} dr`,
`σ = μ.toSphere`, `n = dim E`. `lintegral_polar` is the case `E = ℝ^d`. Mathlib types only. -/
theorem lintegral_polar_addHaar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ η : sphere (0 : E) 1, (∫⁻ r in Ioi (0 : ℝ),
      f (r • (η : E)) * ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1))) ∂μ.toSphere := by
  have h1 : ∫⁻ x, f x ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f (x : E) ∂(μ.comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
      MeasureTheory.restrict_compl_singleton]
  have hF : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((p.2 : ℝ) • (p.1 : E)) :=
    hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))
  have h2 : ∫⁻ x : ({(0 : E)}ᶜ : Set E), f (x : E) ∂(μ.comap Subtype.val)
      = ∫⁻ p, f ((p.2 : ℝ) • (p.1 : E))
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← (Measure.measurePreserving_homeomorphUnitSphereProd μ).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _)]
    refine lintegral_congr fun x => ?_
    have hx : (x : E) ≠ 0 := x.2
    simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have h3 : ∀ η : sphere (0 : E) 1,
      ∫⁻ r, f ((r : ℝ) • (η : E)) ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        = ∫⁻ r in Ioi (0 : ℝ), f (r • (η : E)) * ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
    intro η
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _
        ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
        (g := fun r : Ioi (0 : ℝ) => f ((r : ℝ) • (η : E)))
        (hf.comp ((measurable_subtype_coe).smul_const _)),
      ← lintegral_subtype_comap measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  rw [h1, h2, lintegral_prod _ hF.aemeasurable]
  exact lintegral_congr fun η => h3 η

/-! ## One ray -/

/-- `∫_{(0,M]} s^{k-1} ds = M^k/k` for `M ≥ 0`, `k ≥ 1`, as a lower integral. Mathlib types
only. -/
theorem setLIntegral_Ioc_pow (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ s in Ioc (0 : ℝ) M, ENNReal.ofReal (s ^ (k - 1)) = ENNReal.ofReal (M ^ k / k) := by
  have hint : IntegrableOn (fun s : ℝ => s ^ (k - 1)) (Ioc 0 M) :=
    (continuous_pow (k - 1)).integrableOn_Ioc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => pow_nonneg hs.1.le _)),
    ← intervalIntegral.integral_of_le hM, integral_pow]
  congr 1
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hk1' : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast hk1
  rw [hk1, hk1', zero_pow (by omega), sub_zero]

/-- **The lower integral of `s^{k-1}` over a set between `(0,M)` and `(0,M]`** is `M^k/k`.
Mathlib types only. -/
theorem setLIntegral_pow_of_between (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) {A : Set ℝ}
    (h1 : Ioo 0 M ⊆ A) (h2 : A ⊆ Ioc 0 M) :
    ∫⁻ s in A, ENNReal.ofReal (s ^ (k - 1)) = ENNReal.ofReal (M ^ k / k) := by
  refine le_antisymm ((lintegral_mono_set h2).trans (setLIntegral_Ioc_pow k hk hM).le) ?_
  rw [← setLIntegral_Ioc_pow k hk hM, ← setLIntegral_congr Ioo_ae_eq_Ioc]
  exact lintegral_mono_set h1

/-- The real `M^k`-form of the ray integral is concave in the volume `v`: for `ρ ≥ 0`, `ω > 0`,
`1 ≤ k ≤ d`, `v ↦ min(ρ, (v/ω)^{1/d})^k / k` is concave and nonnegative on `[0,∞)`. Mathlib types
only. -/
theorem concaveOn_min_rpow (k d : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) {ρ ω : ℝ} (hρ : 0 ≤ ρ)
    (hω : 0 < ω) :
    ConcaveOn ℝ (Ici 0) (fun v => min ρ ((v / ω) ^ ((d : ℝ)⁻¹)) ^ k / k) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le hk hkd)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set p : ℝ := (k : ℝ) / d with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hd]; exact_mod_cast hkd
  have hpow : ConcaveOn ℝ (Ici 0) (fun v : ℝ => (ω ^ p)⁻¹ • v ^ p) :=
    (Real.concaveOn_rpow hp0 hp1).smul (by positivity)
  have hmin : ConcaveOn ℝ (Ici 0) ((fun _ : ℝ => ρ ^ k) ⊓ fun v : ℝ => (ω ^ p)⁻¹ • v ^ p) :=
    (concaveOn_const (ρ ^ k) (convex_Ici 0)).inf hpow
  have hdiv := hmin.smul (c := (k : ℝ)⁻¹) (by positivity)
  refine hdiv.congr fun v (hv : 0 ≤ v) => ?_
  simp only [Pi.inf_apply, smul_eq_mul]
  have hr : 0 ≤ (v / ω) ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg (div_nonneg hv hω.le) _
  have hrk : ((v / ω) ^ ((d : ℝ)⁻¹)) ^ k = (ω ^ p)⁻¹ * v ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hv hω.le), Real.div_rpow hv hω.le,
      div_eq_inv_mul]
    congr 2 <;> rw [hp] <;> field_simp
  rw [div_eq_inv_mul]
  congr 1
  rcases le_total ρ ((v / ω) ^ ((d : ℝ)⁻¹)) with h | h
  · rw [min_eq_left h, min_eq_left (by rw [← hrk]; exact pow_le_pow_left₀ hρ h k)]
  · rw [min_eq_right h, min_eq_right (by rw [← hrk]; exact pow_le_pow_left₀ hr h k), hrk]

/-! ## The volume coordinate -/

/-- **`ω_d`**, the volume of the unit ball of `ℝ^d` (the blueprint's `ω_d`; `V_d` in
`prop:origin-lower-bound-d`). -/
noncomputable def ballVol (d : ℕ) : ℝ := (volume (ball (0 : Rd d) 1)).toReal

theorem ballVol_pos : 0 < ballVol d :=
  ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

/-- **The volume coordinate** `φ(x) := ω_d |x|^d`, the volume of the ball of radius `|x|`. -/
noncomputable def volCoord (d : ℕ) (x : Rd d) : ℝ := ballVol d * ‖x‖ ^ d

theorem continuous_volCoord : Continuous (volCoord d) := by
  unfold volCoord; fun_prop

theorem measurable_volCoord : Measurable (volCoord d) := continuous_volCoord.measurable

/-- For `s ≥ 0`, `v ≥ 0`: `ω_d s^d ≤ v ↔ s ≤ (v/ω_d)^{1/d}`. -/
theorem volCoord_le_iff (hd : 1 ≤ d) {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) :
    ballVol d * s ^ d ≤ v ↔ s ≤ (v / ballVol d) ^ ((d : ℝ)⁻¹) := by
  have hω := (ballVol_pos (d := d))
  have hd0 : d ≠ 0 := by omega
  rw [← le_div_iff₀' hω]
  constructor
  · intro h
    rw [← Real.pow_rpow_inv_natCast hs hd0]
    exact Real.rpow_le_rpow (pow_nonneg hs _) h (by positivity)
  · intro h
    rw [← Real.rpow_inv_natCast_pow (div_nonneg hv hω.le) hd0]
    exact pow_le_pow_left₀ hs h d

/-- For `s ≥ 0`, `v ≥ 0`: `s < (v/ω_d)^{1/d} → ω_d s^d < v`. -/
theorem volCoord_lt_of_lt (hd : 1 ≤ d) {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v)
    (h : s < (v / ballVol d) ^ ((d : ℝ)⁻¹)) : ballVol d * s ^ d < v := by
  have hω := (ballVol_pos (d := d))
  have hd0 : d ≠ 0 := by omega
  rw [← lt_div_iff₀' hω, ← Real.rpow_inv_natCast_pow (div_nonneg hv hω.le) hd0]
  exact pow_lt_pow_left₀ h hs hd0

/-! ## The radial part of `u_K` is concave in the volume -/

/-- **`prop:isotropic-radial-monotone`, the radial part of one uniform law**: for a nonempty
compact convex symmetric `K ⊆ ℝ^d`, `v ↦ u_K(B(v))` is concave on `[0,∞)`, where
`B(v) = φ⁻¹((0,v])` is the punctured closed ball of volume `v`. -/
theorem concaveENN_kanterUniform (hd : 1 ≤ d) {K : Set (Rd d)} (hKne : K.Nonempty)
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K) :
    ConcaveENN fun v => kanterUniform K (volCoord d ⁻¹' Ioc 0 v) := by
  set V := Submodule.span ℝ K with hV
  set K' : Set V := Subtype.val ⁻¹' K with hK'
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hK'm : MeasurableSet K' := measurable_subtype_coe hKm
  have hTm : ∀ v : ℝ, MeasurableSet (volCoord d ⁻¹' Ioc 0 v) :=
    fun v => measurable_volCoord measurableSet_Ioc
  -- `0 ∈ K`, and `K'` is convex
  obtain ⟨x₀, hx₀⟩ := hKne
  have h0K : (0 : Rd d) ∈ K := by
    have := hKcv hx₀ (hKs x₀ hx₀) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa using this
  have hK'cv : Convex ℝ K' := hKcv.linear_preimage V.subtype
  have h0K' : (0 : V) ∈ K' := by simpa [hK'] using h0K
  -- the uniform law through the conditional measure
  have hform : ∀ v : ℝ, kanterUniform K (volCoord d ⁻¹' Ioc 0 v)
      = ((volume : Measure V) K')⁻¹ *
          (volume : Measure V) (K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v))) := by
    intro v
    rw [kanterUniform, Measure.map_apply measurable_subtype_coe (hTm v), cond_apply hK'm]
  simp_rw [hform]
  refine ConcaveENN.const_mul ?_ _
  -- the zero space
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hempty : ∀ v : ℝ, K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v)) = ∅ := by
      intro v
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have hy0 : y = 0 := Subsingleton.elim y 0
      have := hy.2.1
      rw [hy0] at this
      simp [volCoord, zero_pow (by omega : d ≠ 0)] at this
    intro x y a b _ _ _ _ _
    simp [hempty]
  -- polar coordinates in `V`
  set k := Module.finrank ℝ V with hk
  have hk1 : 1 ≤ k := Module.finrank_pos
  have hkd : k ≤ d := by
    have := Submodule.finrank_le V
    rwa [finrank_euclideanSpace_fin] at this
  have hω := (ballVol_pos (d := d))
  -- the ray through `θ`
  set J : sphere (0 : V) 1 → Set ℝ := fun θ => {s : ℝ | 0 < s ∧ s • (θ : V) ∈ K'} with hJ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).mp hKc.isBounded
  have hJbdd : ∀ θ, BddAbove (J θ) := by
    intro θ
    refine ⟨R, fun s hs => ?_⟩
    have hmem := hR hs.2
    rw [mem_closedBall, dist_zero_right] at hmem
    have hθn : ‖((θ : V) : Rd d)‖ = 1 := norm_eq_of_mem_sphere θ
    have hn : ‖((s • (θ : V) : V) : Rd d)‖ = s := by
      rw [Submodule.coe_smul, norm_smul, hθn, mul_one, Real.norm_of_nonneg hs.1.le]
    rw [hn] at hmem
    exact hmem
  have hJdown : ∀ θ, ∀ s ∈ J θ, ∀ s', 0 < s' → s' ≤ s → s' ∈ J θ := by
    intro θ s hs s' hs' hss'
    refine ⟨hs', ?_⟩
    have h := hK'cv.smul_mem_of_zero_mem h0K' hs.2 ⟨div_nonneg hs'.le hs.1.le,
      (div_le_one hs.1).mpr hss'⟩
    rwa [smul_smul, div_mul_cancel₀ _ hs.1.ne'] at h
  set ρ : sphere (0 : V) 1 → ℝ := fun θ => sSup (J θ) with hρ
  have hρ0 : ∀ θ, 0 ≤ ρ θ := fun θ => Real.sSup_nonneg fun s hs => hs.1.le
  -- the inner integral along the ray
  have hray : ∀ (θ : sphere (0 : V) 1) (v : ℝ), 0 ≤ v →
      ∫⁻ r in Ioi (0 : ℝ), (K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v))).indicator 1
          (r • (θ : V)) * ENNReal.ofReal (r ^ (k - 1))
        = ENNReal.ofReal (min (ρ θ) ((v / ballVol d) ^ ((d : ℝ)⁻¹)) ^ k / k) := by
    intro θ v hv
    set M := min (ρ θ) ((v / ballVol d) ^ ((d : ℝ)⁻¹)) with hM
    have hM0 : 0 ≤ M := le_min (hρ0 θ) (Real.rpow_nonneg (div_nonneg hv hω.le) _)
    set A : Set ℝ := {s : ℝ | s • (θ : V) ∈ K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v))}
      with hA
    have hAm : MeasurableSet A := by
      have hc : Continuous fun s : ℝ => s • (θ : V) := by fun_prop
      exact hc.measurable (hK'm.inter (measurable_subtype_coe (hTm v)))
    have hθn : ‖((θ : V) : Rd d)‖ = 1 := norm_eq_of_mem_sphere θ
    have hnorm : ∀ s : ℝ, 0 < s → ‖((s • (θ : V) : V) : Rd d)‖ = s := fun s hs => by
      rw [Submodule.coe_smul, norm_smul, hθn, mul_one, Real.norm_of_nonneg hs.le]
    have hint : ∫⁻ r in Ioi (0 : ℝ), (K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v))).indicator 1
          (r • (θ : V)) * ENNReal.ofReal (r ^ (k - 1))
        = ∫⁻ r in Ioi (0 : ℝ) ∩ A, ENNReal.ofReal (r ^ (k - 1)) := by
      rw [show Ioi (0 : ℝ) ∩ A = A ∩ Ioi 0 from inter_comm _ _, ← Measure.restrict_restrict hAm,
        ← lintegral_indicator hAm]
      refine lintegral_congr fun r => ?_
      by_cases hr : r ∈ A
      · rw [indicator_of_mem hr, indicator_of_mem (show r • (θ : V) ∈ _ from hr), Pi.one_apply,
          one_mul]
      · rw [indicator_of_notMem hr, indicator_of_notMem (show r • (θ : V) ∉ _ from hr), zero_mul]
    rw [hint]
    refine setLIntegral_pow_of_between k hk1 hM0 ?_ ?_
    · rintro s ⟨hs0, hsM⟩
      refine ⟨hs0, ?_⟩
      have hsρ : s < ρ θ := lt_of_lt_of_le hsM (min_le_left _ _)
      have hsr : s < (v / ballVol d) ^ ((d : ℝ)⁻¹) := lt_of_lt_of_le hsM (min_le_right _ _)
      have hne : (J θ).Nonempty := by
        by_contra hcon
        rw [not_nonempty_iff_eq_empty] at hcon
        have : ρ θ = 0 := by simp only [hρ, hcon, Real.sSup_empty]
        linarith
      obtain ⟨s', hs'J, hss'⟩ := exists_lt_of_lt_csSup hne hsρ
      refine ⟨(hJdown θ s' hs'J s hs0 hss'.le).2, ?_⟩
      show volCoord d ((s • (θ : V) : V) : Rd d) ∈ Ioc 0 v
      rw [volCoord, hnorm s hs0]
      exact ⟨mul_pos hω (pow_pos hs0 d), (volCoord_lt_of_lt hd hs0.le hv hsr).le⟩
    · rintro s ⟨hs0, hsK, hsT⟩
      refine ⟨hs0, le_min ?_ ?_⟩
      · exact le_csSup (hJbdd θ) ⟨hs0, hsK⟩
      · have hT : volCoord d ((s • (θ : V) : V) : Rd d) ∈ Ioc 0 v := hsT
        rw [volCoord, hnorm s hs0] at hT
        exact (volCoord_le_iff hd hs0.le hv).mp hT.2
  -- assemble
  have hpolar : ∀ v : ℝ, 0 ≤ v →
      (volume : Measure V) (K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v)))
        = ∫⁻ θ : sphere (0 : V) 1,
            ENNReal.ofReal (min (ρ θ) ((v / ballVol d) ^ ((d : ℝ)⁻¹)) ^ k / k)
            ∂(volume : Measure V).toSphere := by
    intro v hv
    have hSm : MeasurableSet (K' ∩ (Subtype.val ⁻¹' (volCoord d ⁻¹' Ioc 0 v))) :=
      hK'm.inter (measurable_subtype_coe (hTm v))
    rw [← lintegral_indicator_one hSm, lintegral_polar_addHaar _ _ (measurable_one.indicator hSm)]
    exact lintegral_congr fun θ => hray θ v hv
  have hconc : ConcaveENN fun v => ∫⁻ θ : sphere (0 : V) 1,
      ENNReal.ofReal (min (ρ θ) ((v / ballVol d) ^ ((d : ℝ)⁻¹)) ^ k / k)
        ∂(volume : Measure V).toSphere :=
    ConcaveENN.lintegral (ae_of_all _ fun θ =>
      concaveENN_ofReal (concaveOn_min_rpow k d hk1 hkd (hρ0 θ) hω) fun v hv =>
        div_nonneg (pow_nonneg (le_min (hρ0 θ) (Real.rpow_nonneg (div_nonneg hv hω.le) _)) _)
          (Nat.cast_nonneg k))
  intro x y a b hx hy ha hb hab
  dsimp only
  rw [hpolar x hx, hpolar y hy, hpolar _ (by positivity)]
  exact hconc hx hy ha hb hab

end AffineHemigroup
