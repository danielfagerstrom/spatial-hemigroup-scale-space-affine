/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic

/-!
# `lem:charfn-one-on-subspace` — a characteristic function equal to `1` on a subspace

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:charfn-one-on-subspace`. Lean core only.

## The route

The blueprint's proof takes a countable dense subset of a ball in `H` and uses the connectedness of
the ball. The Lean proof takes a basis `v₁, …, v_k` of `H` instead, and the countable family
`c_j v_j / (m + 1)`, `m ∈ ℕ`, inside the ball: off a `ρ`-null set, `cos(θ/(m+1)) = 1` for every
`m`, where `θ = c_j⟨x, v_j⟩`, and once `|θ/(m+1)| < 2π` this forces `θ = 0`. So `⟨x, v_j⟩ = 0` for
every `j`, which is `x ∈ H^⊥`. The two statements are the blueprint's.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **The real part of `1 - ρ̂(η)` vanishes only on a `2π`-lattice**: if `ρ̂(η) = 1` then
`cos⟨x, η⟩ = 1` for `ρ`-almost every `x`. Stated on any finite-dimensional real inner product
space (a second-demand candidate: its statement mentions Mathlib types only). -/
theorem ae_cos_inner_eq_one_of_charFun_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (ρ : Measure E)
    [IsProbabilityMeasure ρ] {η : E} (h : charFun ρ η = 1) :
    ∀ᵐ x ∂ρ, Real.cos ⟪x, η⟫ = 1 := by
  have hcont : Continuous fun x : E => Real.cos ⟪x, η⟫ := by fun_prop
  have hint_cos : Integrable (fun x : E => Real.cos ⟪x, η⟫) ρ :=
    Integrable.of_bound hcont.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hintc : Integrable (fun x : E => Complex.exp (⟪x, η⟫ * Complex.I)) ρ :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Filter.Eventually.of_forall fun x => by
        rw [Complex.norm_exp_ofReal_mul_I])
  have hre : ∫ x, Real.cos ⟪x, η⟫ ∂ρ = 1 := by
    have h' := congrArg Complex.re h
    rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hintc] at h'
    simpa [Complex.exp_ofReal_mul_I_re] using h'
  have hnn : 0 ≤ fun x : E => 1 - Real.cos ⟪x, η⟫ := fun x => sub_nonneg.2 (Real.cos_le_one _)
  have hint : Integrable (fun x : E => 1 - Real.cos ⟪x, η⟫) ρ := (integrable_const 1).sub hint_cos
  have h0 : ∫ x, (1 - Real.cos ⟪x, η⟫) ∂ρ = 0 := by
    rw [integral_sub (integrable_const 1) hint_cos, hre]
    simp
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hint).1 h0] with x hx
  simp only [Pi.zero_apply] at hx
  linarith

/-- **A real number all of whose fractions `θ/(m+1)` have cosine `1` is `0`.** -/
theorem eq_zero_of_cos_div_eq_one {θ : ℝ} (h : ∀ m : ℕ, Real.cos (θ / (m + 1)) = 1) : θ = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (|θ| / Real.pi)
  have hpi := Real.pi_pos
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hlt : |θ / (m + 1)| < 2 * Real.pi := by
    rw [abs_div, abs_of_pos hm1, div_lt_iff₀ hm1]
    have : |θ| < Real.pi * m := by
      rw [div_lt_iff₀ hpi] at hm
      linarith
    nlinarith
  have h0 := (Real.cos_eq_one_iff_of_lt_of_lt (neg_lt_of_abs_lt hlt) (lt_of_abs_lt hlt)).1 (h m)
  rcases div_eq_zero_iff.1 h0 with h | h
  · exact h
  · exact absurd h hm1.ne'

/-- **`lem:charfn-one-on-subspace`**: if `ρ̂ = 1` on a neighbourhood of `0` in the subspace `H`,
then `ρ` is carried by `H^⊥` and `ρ̂(ξ + η) = ρ̂(ξ)` for `ξ ∈ ℝ^d`, `η ∈ H`. -/
theorem charFun_one_on_subspace (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (H : Submodule ℝ (Rd d)) (r : ℝ) (hr : 0 < r)
    (h1 : ∀ η ∈ H, ‖η‖ < r → charFun ρ η = 1) :
    ρ ((Hᗮ : Set (Rd d))ᶜ) = 0 ∧ ∀ ξ : Rd d, ∀ η ∈ H, charFun ρ (ξ + η) = charFun ρ ξ := by
  -- a basis of `H` and, for each basis vector, a scale putting its fractions in the ball
  let b := Module.finBasis ℝ H
  let v : Fin (Module.finrank ℝ H) → Rd d := fun j => (b j : Rd d)
  let c : Fin (Module.finrank ℝ H) → ℝ := fun j => r / (2 * (‖v j‖ + 1))
  have hc : ∀ j, 0 < c j := fun j => by positivity
  have hmem : ∀ j (m : ℕ), (c j / (m + 1)) • v j ∈ H := fun j m =>
    H.smul_mem _ (b j).2
  have hsmall : ∀ j (m : ℕ), ‖(c j / (m + 1)) • v j‖ < r := by
    intro j m
    have hm1 : (1 : ℝ) ≤ m + 1 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hc j) (by linarith))]
    have hv : 0 ≤ ‖v j‖ := norm_nonneg _
    have h2 : c j / (m + 1) ≤ c j := div_le_self (hc j).le hm1
    have h3 : c j * ‖v j‖ < r := by
      change r / (2 * (‖v j‖ + 1)) * ‖v j‖ < r
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    calc c j / (m + 1) * ‖v j‖ ≤ c j * ‖v j‖ := mul_le_mul_of_nonneg_right h2 hv
      _ < r := h3
  -- off a null set, every fraction has cosine `1`
  have hae : ∀ᵐ x ∂ρ, ∀ j, ∀ m : ℕ, Real.cos ⟪x, (c j / (m + 1)) • v j⟫ = 1 := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro m
    exact ae_cos_inner_eq_one_of_charFun_eq_one ρ (h1 _ (hmem j m) (hsmall j m))
  -- hence `ρ` is carried by `H^⊥`
  have hperp : ∀ᵐ x ∂ρ, x ∈ Hᗮ := by
    filter_upwards [hae] with x hx
    have hvj : ∀ j, ⟪x, v j⟫ = 0 := by
      intro j
      have hθ : c j * ⟪x, v j⟫ = 0 := by
        apply eq_zero_of_cos_div_eq_one
        intro m
        have := hx j m
        rwa [real_inner_smul_right, div_mul_eq_mul_div] at this
      rcases mul_eq_zero.1 hθ with h | h
      · exact absurd h (hc j).ne'
      · exact h
    have hf : (innerₛₗ ℝ x).comp H.subtype = 0 := by
      apply b.ext
      intro j
      simpa [innerₛₗ_apply_apply] using hvj j
    rw [Submodule.mem_orthogonal]
    intro u hu
    have := LinearMap.congr_fun hf ⟨u, hu⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, innerₛₗ_apply_apply,
      LinearMap.zero_apply] at this
    rw [real_inner_comm]
    exact this
  refine ⟨ae_iff.1 hperp, ?_⟩
  intro ξ η hη
  rw [charFun_apply, charFun_apply]
  apply integral_congr_ae
  filter_upwards [hperp] with x hx
  rw [inner_add_right, Submodule.inner_left_of_mem_orthogonal hη hx, add_zero]

/-- **`lem:charfn-one-on-subspace`**, in particular: if `ρ̂ = 1` near `0` then `ρ = δ₀`. -/
theorem eq_dirac_of_charFun_one_near_zero (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (r : ℝ) (hr : 0 < r) (h1 : ∀ η : Rd d, ‖η‖ < r → charFun ρ η = 1) :
    ρ = Measure.dirac 0 := by
  have h := (charFun_one_on_subspace ρ ⊤ r hr (fun η _ hη => h1 η hη)).2
  apply Measure.ext_of_charFun
  funext η
  have hη := h 0 η Submodule.mem_top
  rw [zero_add] at hη
  rw [hη, charFun_zero, charFun_dirac]
  simp

end AffineHemigroup
