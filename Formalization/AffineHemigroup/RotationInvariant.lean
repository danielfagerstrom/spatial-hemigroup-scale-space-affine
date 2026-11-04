/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginExponent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Rotation-invariant measures on `ℝ^d`: the surface measure, and determination by the radial image

Groundwork for `prop:isotropic-polar-reading` (`blueprint/src/parts/03-isotropic.tex`). Wave 2,
group A (Q-0281).

The blueprint's proof of the polar reading averages over the Haar measure of `O(d)`, whose
compactness instance Mathlib lacks (PRICING). The Lean route needs only two facts, both proved here
without a Haar measure on `O(d)`:

* **`σ_{d-1}` is invariant under every linear isometry** (`toSphere_map_isometry`): Mathlib's
  `toSphere` is `d` times Lebesgue measure of cones, and an isometry carries cones to cones and
  preserves Lebesgue measure;
* **a rotation-invariant measure is determined by its image under `x ↦ |x|`**
  (`eq_of_rotationInvariant`), for measures finite off every ball about the origin and null at
  the origin. On each shell `{|x| > 1/(n+1)}` the two restrictions are finite and have the same
  Fourier transform: by rotation invariance `m̂(ξ)` is the `σ_{d-1}`-average of `m̂(|ξ|η)`, which by
  Fubini and the invariance of `σ_{d-1}` is `∫ Φ(|ξ|, |x|) m(dx)`, a functional of the radial image.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace Pointwise

variable {d : ℕ}

/-- A linear isometry, restricted to the unit sphere. -/
noncomputable def sphereMap (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : sphere (0 : Rd d) 1 → sphere (0 : Rd d) 1 :=
  fun η => ⟨Q η, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map,
    norm_eq_of_mem_sphere η]⟩

theorem continuous_sphereMap (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : Continuous (sphereMap Q) := by
  unfold sphereMap
  fun_prop

theorem measurable_sphereMap (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : Measurable (sphereMap Q) :=
  (continuous_sphereMap Q).measurable

/-- **`σ_{d-1}` is invariant under linear isometries**. -/
theorem toSphere_map_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    ((volume : Measure (Rd d)).toSphere).map (sphereMap Q) = (volume : Measure (Rd d)).toSphere := by
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet (sphereMap Q ⁻¹' s) := measurable_sphereMap Q hs
  rw [Measure.map_apply (measurable_sphereMap Q) hs, Measure.toSphere_apply' _ hpre,
    Measure.toSphere_apply' _ hs]
  congr 1
  have himg : Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap Q ⁻¹' s) : Set (Rd d))
      = Q ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set (Rd d))) := by
    ext x
    simp only [Set.mem_smul, mem_image, mem_preimage, exists_exists_and_eq_and]
    constructor
    · rintro ⟨t, ht, η, hη, rfl⟩
      refine ⟨t, ht, sphereMap Q η, hη, ?_⟩
      simp [sphereMap]
    · rintro ⟨t, ht, η, hη, hx⟩
      refine ⟨t, ht, sphereMap Q.symm η, ?_, ?_⟩
      · show sphereMap Q (sphereMap Q.symm η) ∈ s
        convert hη using 1
        ext; simp [sphereMap]
      · simp only [sphereMap]
        rw [← Q.symm_apply_apply x, ← hx, LinearIsometryEquiv.map_smul]
  rw [himg, (Q.measurePreserving).measure_preimage_emb Q.toHomeomorph.measurableEmbedding]

/-- `⟪Qx, y⟫ = ⟪x, Q⁻¹y⟫` for a linear isometry. -/
theorem inner_isometry_symm (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (x y : Rd d) : ⟪Q x, y⟫ = ⟪x, Q.symm y⟫ := by
  conv_lhs => rw [← Q.apply_symm_apply y]
  exact Q.inner_map_map x (Q.symm y)

/-- The transform of the image under a linear isometry: `\widehat{Q_*m}(z) = m̂(Q⁻¹z)`. -/
theorem charFun_map_isometry (m : Measure (Rd d)) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (z : Rd d) :
    charFun (m.map Q) z = charFun m (Q.symm z) := by
  rw [charFun_apply, charFun_apply, integral_map Q.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp_rw [inner_isometry_symm]

/-- A sphere integral of a function of `⟨x, η⟩` depends only on `|x|`, by the invariance of
`σ_{d-1}` under the reflection taking `x` to `x'`. -/
theorem integral_sphere_inner_eq_of_norm_eq {f : ℝ → ℂ} (hf : Continuous f) {x x' : Rd d}
    (h : ‖x‖ = ‖x'‖) :
    ∫ η : sphere (0 : Rd d) 1, f ⟪x, (η : Rd d)⟫ ∂((volume : Measure (Rd d)).toSphere)
      = ∫ η : sphere (0 : Rd d) 1, f ⟪x', (η : Rd d)⟫ ∂((volume : Measure (Rd d)).toSphere) := by
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (x - x'))ᗮ with hQ
  have hQx : Q x = x' := Submodule.reflection_sub h
  have hmeas : AEStronglyMeasurable (fun η : sphere (0 : Rd d) 1 => f ⟪x, (η : Rd d)⟫)
      (((volume : Measure (Rd d)).toSphere).map (sphereMap Q.symm)) :=
    (hf.comp (by fun_prop)).aestronglyMeasurable
  have h1 := integral_map (measurable_sphereMap Q.symm).aemeasurable hmeas
  rw [toSphere_map_isometry] at h1
  rw [h1]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  simp only [sphereMap]
  rw [← hQx, inner_isometry_symm]

/-- The sphere integral `Φ(s, r) = ∫_{S^{d-1}} e^{i s r ⟨e₁, η⟩} σ_{d-1}(dη)`. -/
noncomputable def sphereChar (d : ℕ) (e : Rd d) (s r : ℝ) : ℂ :=
  ∫ η : sphere (0 : Rd d) 1, cexp (((s * r * ⟪e, (η : Rd d)⟫ : ℝ) : ℂ) * I)
    ∂((volume : Measure (Rd d)).toSphere)

theorem measurable_sphereChar (e : Rd d) (s : ℝ) : Measurable (sphereChar d e s) := by
  have hjoint : StronglyMeasurable (Function.uncurry fun (r : ℝ) (η : sphere (0 : Rd d) 1) =>
      cexp (((s * r * ⟪e, (η : Rd d)⟫ : ℝ) : ℂ) * I)) :=
    (Continuous.stronglyMeasurable (by unfold Function.uncurry; fun_prop))
  exact (hjoint.integral_prod_right' (ν := (volume : Measure (Rd d)).toSphere)).measurable

/-- **The transform of a rotation-invariant finite measure is a functional of its radial image**:
`m̂(ξ) = σ_{d-1}(S^{d-1})⁻¹ ∫ Φ(|ξ|, r) (|·|_* m)(dr)`. -/
theorem charFun_eq_radial (hd : 1 ≤ d) (m : Measure (Rd d)) [IsFiniteMeasure m]
    (hm : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, m.map Q = m) {e : Rd d} (he : ‖e‖ = 1) (ξ : Rd d) :
    charFun m ξ = (((volume : Measure (Rd d)).toSphere univ).toReal : ℂ)⁻¹ *
      ∫ r, sphereChar d e ‖ξ‖ r ∂(m.map (fun x => ‖x‖)) := by
  set σ := (volume : Measure (Rd d)).toSphere with hσ
  -- radiality
  have hrad : ∀ η : sphere (0 : Rd d) 1, charFun m ξ = charFun m (‖ξ‖ • (η : Rd d)) := by
    intro η
    have hn : ‖ξ‖ = ‖‖ξ‖ • (η : Rd d)‖ := by
      rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, norm_norm]
    set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (ξ - ‖ξ‖ • (η : Rd d)))ᗮ with hQ
    have hQξ : Q ξ = ‖ξ‖ • (η : Rd d) := Submodule.reflection_sub hn
    have h := charFun_map_isometry m Q.symm ξ
    rw [hm Q.symm, LinearIsometryEquiv.symm_symm, hQξ] at h
    exact h
  have hσpos : (σ univ).toReal ≠ 0 := by
    rw [hσ, ← (sphereArea_eq_toSphere hd).1, ENNReal.toReal_ofReal (sphereArea_eq_toSphere hd).2.le]
    exact (sphereArea_eq_toSphere hd).2.ne'
  have hint : Integrable (Function.uncurry fun (η : sphere (0 : Rd d) 1) (x : Rd d) =>
      cexp (((⟪x, ‖ξ‖ • (η : Rd d)⟫ : ℝ) : ℂ) * I)) (σ.prod m) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by unfold Function.uncurry; fun_prop)) 1
      (ae_of_all _ fun p => by simp only [Function.uncurry, Complex.norm_exp_ofReal_mul_I]; rfl)
  calc charFun m ξ = (((σ univ).toReal : ℂ))⁻¹ * ∫ η : sphere (0 : Rd d) 1,
        charFun m (‖ξ‖ • (η : Rd d)) ∂σ := by
        simp_rw [← hrad]
        rw [integral_const, measureReal_def, Complex.real_smul, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hσpos), one_mul]
    _ = (((σ univ).toReal : ℂ))⁻¹ * ∫ x, ∫ η : sphere (0 : Rd d) 1,
        cexp (((⟪x, ‖ξ‖ • (η : Rd d)⟫ : ℝ) : ℂ) * I) ∂σ ∂m := by
        simp_rw [charFun_apply]
        rw [integral_integral_swap hint]
    _ = (((σ univ).toReal : ℂ))⁻¹ * ∫ x, sphereChar d e ‖ξ‖ ‖x‖ ∂m := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        have hnx : ‖x‖ = ‖‖x‖ • e‖ := by rw [norm_smul, he, mul_one, norm_norm]
        have h1 := integral_sphere_inner_eq_of_norm_eq
          (f := fun t => cexp (((‖ξ‖ * t : ℝ) : ℂ) * I)) (by fun_prop) hnx
        simp only [sphereChar]
        simp_rw [real_inner_smul_right]
        rw [h1]
        refine integral_congr_ae (ae_of_all _ fun η => ?_)
        simp only
        rw [real_inner_smul_left]
        ring_nf
    _ = _ := by
        rw [integral_map continuous_norm.measurable.aemeasurable
          (measurable_sphereChar e ‖ξ‖).aestronglyMeasurable]

/-- **A rotation-invariant measure is determined by its radial image**: two measures on `ℝ^d`,
invariant under every linear isometry, null at the origin and finite off every ball about it, with
the same image under `x ↦ |x|`, are equal. -/
theorem eq_of_rotationInvariant (hd : 1 ≤ d) {ν ν' : Measure (Rd d)}
    (hν : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν) (hν' : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν'.map Q = ν')
    (h0 : ν {0} = 0) (h0' : ν' {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) (hfin' : ∀ ε : ℝ, 0 < ε → ν' {x | ε < ‖x‖} ≠ ⊤)
    (hrad : ν.map (fun x => ‖x‖) = ν'.map (fun x => ‖x‖)) : ν = ν' := by
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he
  have he1 : ‖e‖ = 1 := by simp [he, ebasis]
  set S : ℕ → Set (Rd d) := fun n => {x | 1 / ((n : ℝ) + 1) < ‖x‖} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_const continuous_norm.measurable
  have hSpre : ∀ n, S n = (fun x : Rd d => ‖x‖) ⁻¹' Ioi (1 / ((n : ℝ) + 1)) := fun n => rfl
  have hSQ : ∀ (n : ℕ) (Q : Rd d ≃ₗᵢ[ℝ] Rd d), Q ⁻¹' S n = S n := by
    intro n Q; ext x; simp [hS]
  -- on each shell the restrictions agree
  have hshell : ∀ n, ν.restrict (S n) = ν'.restrict (S n) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    haveI : IsFiniteMeasure (ν.restrict (S n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (hfin _ hpos)⟩
    haveI : IsFiniteMeasure (ν'.restrict (S n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (hfin' _ hpos)⟩
    have hinv : ∀ (μ : Measure (Rd d)), (∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, μ.map Q = μ) →
        ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, (μ.restrict (S n)).map Q = μ.restrict (S n) := by
      intro μ hμ Q
      rw [← hSQ n Q, ← Measure.restrict_map Q.continuous.measurable (hSm n), hμ Q, hSQ n Q]
    have hmapS : ∀ (μ : Measure (Rd d)), (μ.restrict (S n)).map (fun x => ‖x‖)
        = (μ.map (fun x => ‖x‖)).restrict (Ioi (1 / ((n : ℝ) + 1))) := by
      intro μ
      rw [Measure.restrict_map continuous_norm.measurable measurableSet_Ioi, hSpre n]
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [charFun_eq_radial hd _ (hinv ν hν) he1, charFun_eq_radial hd _ (hinv ν' hν') he1,
      hmapS, hmapS, hrad]
  -- the union of the shells is the complement of the origin
  have hmono : Monotone S := by
    intro m n hmn x hx
    simp only [hS, mem_setOf_eq] at hx ⊢
    refine lt_of_le_of_lt ?_ hx
    gcongr
  have hunion : (⋃ n, S n) = {0}ᶜ := by
    ext x
    simp only [mem_iUnion, hS, mem_setOf_eq, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩ hx; subst hx; simp at hn; linarith [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx)
      exact ⟨n, hn⟩
  refine Measure.ext fun B hB => ?_
  have hsplit : ∀ μ : Measure (Rd d), μ {0} = 0 → μ B = ⨆ n, μ.restrict (S n) B := by
    intro μ hμ0
    have h1 : μ B = μ (B ∩ {0}ᶜ) := by
      rw [← measure_inter_add_sdiff B (measurableSet_singleton (0 : Rd d)).compl]
      have : μ (B \ {0}ᶜ) = 0 := measure_mono_null (fun x hx => by
        simpa using hx.2) hμ0
      rw [this, add_zero]
    rw [h1, ← hunion, inter_iUnion, Monotone.measure_iUnion
      (fun m n hmn => inter_subset_inter_right _ (hmono hmn))]
    simp_rw [Measure.restrict_apply hB]
  rw [hsplit ν h0, hsplit ν' h0']
  simp_rw [hshell]

end AffineHemigroup
