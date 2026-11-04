/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Origin
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# `def:isotropic-origin-datum` and `lem:polar-decomposition`: polar coordinates on `ℝ^d`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `def:isotropic-origin-datum` (its two notation
lemmas) and `lem:polar-decomposition` (`eq:polar-decomposition`). Wave 2, group A (Q-0281).

The route is Mathlib's generalized polar coordinates (`Mathlib.MeasureTheory.Constructions.HaarToSphere`):
Lebesgue measure on `ℝ^d ∖ {0}` is carried by `x ↦ (x/|x|, |x|)` to `σ_{d-1} ⊗ r^{d-1} dr`, where
`σ_{d-1}` is `volume.toSphere`. `lintegral_polar` is that statement for nonnegative measurable
functions; the polar decomposition of an origin datum's Lévy measure is it applied to `g` times the
radial density. The profile `k_d` is only antitone on `(0,∞)`, so its measurability is read through
`r ↦ k_d(e^r)`, an antitone function on all of `ℝ` (`measurable_indicator_Ioi_of_antitoneOn`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- `dim ℝ^d = d`. -/
theorem finrank_Rd (d : ℕ) : Module.finrank ℝ (Rd d) = d := finrank_euclideanSpace_fin

/-- A function antitone on `(0,∞)`, cut off to `0` off `(0,∞)`, is measurable: on `(0,∞)` it is
`r ↦ k(e^{log r})`, and `r ↦ k(e^r)` is antitone on all of `ℝ`. Mathlib types only. -/
theorem measurable_indicator_Ioi_of_antitoneOn {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0)) :
    Measurable ((Ioi (0 : ℝ)).indicator k) := by
  have hanti : Antitone fun r : ℝ => k (Real.exp r) := fun a b hab =>
    hk (Real.exp_pos a) (Real.exp_pos b) (Real.exp_le_exp.mpr hab)
  have hm : Measurable fun r : ℝ => k (Real.exp (Real.log r)) :=
    hanti.measurable.comp Real.measurable_log
  have heq : (Ioi (0 : ℝ)).indicator k
      = (Ioi (0 : ℝ)).indicator fun r : ℝ => k (Real.exp (Real.log r)) := by
    funext r
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr, indicator_of_mem hr, Real.exp_log hr]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr]
  rw [heq]
  exact hm.indicator measurableSet_Ioi

/-- **Polar coordinates for a nonnegative function on `ℝ^d`**: for measurable `f ≥ 0`,
`∫ f dx = ∫_{S^{d-1}} σ_{d-1}(dη) ∫_0^∞ f(rη) r^{d-1} dr`. Mathlib types only. -/
theorem lintegral_polar (hd : 1 ≤ d) (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ η : sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
      f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))) ∂((volume : Measure (Rd d)).toSphere) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have h1 : ∫⁻ x, f x = ∫⁻ x : ({(0 : Rd d)}ᶜ : Set (Rd d)), f (x : Rd d) ∂(volume.comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, MeasureTheory.restrict_compl_singleton]
  have hF : Measurable fun p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ) => f ((p.2 : ℝ) • (p.1 : Rd d)) :=
    hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))
  have h2 : ∫⁻ x : ({(0 : Rd d)}ᶜ : Set (Rd d)), f (x : Rd d) ∂(volume.comap Subtype.val)
      = ∫⁻ p, f ((p.2 : ℝ) • (p.1 : Rd d))
          ∂((volume : Measure (Rd d)).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ (Rd d) - 1))) := by
    rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (Rd d))).lintegral_comp_emb (Homeomorph.measurableEmbedding _)]
    refine lintegral_congr fun x => ?_
    have hx : (x : Rd d) ≠ 0 := x.2
    simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have h3 : ∀ η : sphere (0 : Rd d) 1,
      ∫⁻ r, f ((r : ℝ) • (η : Rd d)) ∂(Measure.volumeIoiPow (Module.finrank ℝ (Rd d) - 1))
        = ∫⁻ r in Ioi (0 : ℝ), f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1)) := by
    intro η
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _
        ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
        (g := fun r : Ioi (0 : ℝ) => f ((r : ℝ) • (η : Rd d)))
        (hf.comp ((measurable_subtype_coe).smul_const _)),
      ← lintegral_subtype_comap measurableSet_Ioi, finrank_Rd]
    refine lintegral_congr fun r => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  rw [h1, h2, lintegral_prod _ hF.aemeasurable]
  exact lintegral_congr fun η => h3 η

/-- **`def:isotropic-origin-datum`, the surface area**: `|S^{d-1}| = σ_{d-1}(S^{d-1})`, the total
mass of Mathlib's surface measure `volume.toSphere`, is the formula `2π^{d/2}/Γ(d/2)` that
`sphereArea` is defined by, and is positive. Not a clause: it identifies the Lean definition with
the blueprint's. -/
theorem sphereArea_eq_toSphere (hd : 1 ≤ d) :
    ENNReal.ofReal (sphereArea d) = (volume : Measure (Rd d)).toSphere univ ∧
      0 < sphereArea d := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hpos : 0 < sphereArea d := by
    unfold sphereArea
    have : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  refine ⟨?_, hpos⟩
  rw [Measure.toSphere_apply_univ, finrank_Rd, EuclideanSpace.volume_ball, Fintype.card_fin,
    ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hd0.le]
  congr 1
  have hsq : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  have hΓ : Real.Gamma ((d : ℝ) / 2 + 1) = (d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  rw [hsq, hΓ, sphereArea]
  field_simp

namespace OriginDatum

/-- **`def:isotropic-origin-datum`, the profile at the origin**: `c := k_d(0+)` is the right limit
of the nonincreasing profile at `0`, which `profileAtOrigin` defines as a supremum. Not a clause:
it identifies the Lean definition with the blueprint's `k_d(0+)`. (Declared inside
`namespace OriginDatum`, not as `theorem OriginDatum.…`, so that `linkage`'s declaration scan,
which reads the name after the keyword up to the first dot, sees it.) -/
theorem tendsto_profileAtOrigin (D : OriginDatum d) :
    Tendsto (fun r => ENNReal.ofReal (D.k r)) (𝓝[>] 0) (𝓝 D.profileAtOrigin) := by
  have hA : AntitoneOn (fun r => ENNReal.ofReal (D.k r)) (Ioi 0) := fun a ha b hb hab =>
    ENNReal.ofReal_le_ofReal (D.k_antitone ha hb hab)
  have h := hA.tendsto_nhdsGT (OrderTop.bddAbove _)
  have hs : sSup ((fun r => ENNReal.ofReal (D.k r)) '' Ioi 0) = D.profileAtOrigin := by
    rw [OriginDatum.profileAtOrigin, sSup_image']
  rwa [hs] at h

/-- The radial density of `ν_d` against Lebesgue measure,
`x ↦ 1_{x ≠ 0} k_d(|x|)/(|S^{d-1}||x|^d)`, is measurable. -/
theorem measurable_levyDensity (D : OriginDatum d) :
    Measurable fun x : Rd d => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x := by
  have hk := measurable_indicator_Ioi_of_antitoneOn D.k_antitone
  have heq : (fun x : Rd d => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x)
      = fun x => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d)) := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : ‖x‖ ∈ Ioi (0 : ℝ) := norm_pos_iff.mpr hx
      rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), indicator_of_mem hx']
  rw [heq]
  fun_prop

/-- **`lem:polar-decomposition`** (`eq:polar-decomposition`): for every nonnegative Borel `g`
vanishing at the origin,
`∫ g dν_d = |S^{d-1}|⁻¹ ∫_{S^{d-1}} σ_{d-1}(dη) ∫_0^∞ g(rη) k_d(r) dr/r`. -/
theorem polar_decomposition (hd : 1 ≤ d) (D : OriginDatum d) (g : Rd d → ℝ≥0∞)
    (hg : Measurable g) (_hg0 : g 0 = 0) :
    ∫⁻ x, g x ∂D.levyMeasure = (ENNReal.ofReal (sphereArea d))⁻¹ *
      ∫⁻ η : Metric.sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
        g (r • (η : Rd d)) * ENNReal.ofReal (D.k r / r)) ∂((volume : Measure (Rd d)).toSphere) := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hAinv : (ENNReal.ofReal (sphereArea d))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (by simp [hA])
  rw [OriginDatum.levyMeasure, lintegral_withDensity_eq_lintegral_mul _ D.measurable_levyDensity hg]
  simp only [Pi.mul_apply]
  rw [lintegral_polar hd _ (D.measurable_levyDensity.mul hg), ← lintegral_const_mul' _ _ hAinv]
  refine lintegral_congr fun η => ?_
  rw [← lintegral_const_mul' _ _ hAinv]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
  have hnorm : ‖r • (η : Rd d)‖ = r := by rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr.le]
  have hne : r • (η : Rd d) ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm]; exact hr.ne'
  rw [indicator_of_mem (show r • (η : Rd d) ∈ ({0}ᶜ : Set (Rd d)) from hne), hnorm]
  have hk := D.k_nonneg r hr
  have hrd : r ^ d = r * r ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hrd1 : 0 < r ^ (d - 1) := pow_pos hr _
  rw [mul_comm (ENNReal.ofReal _) (g _), mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_left_comm, ← ENNReal.ofReal_inv_of_pos hA, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [hrd]
  field_simp

end OriginDatum

end AffineHemigroup
