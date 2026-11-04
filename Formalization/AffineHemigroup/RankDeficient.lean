/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Scheme
import AffineHemigroup.CharFunSubspace
import AffineHemigroup.SingleRatio

/-!
# `thm:rank-deficient-step` — one rank-deficient step forces the Gaussian

Blueprint: `blueprint/src/parts/04-classical.tex`, `thm:rank-deficient-step`. Lean core only: the
uniqueness of the transform is Mathlib's `Measure.ext_of_charFun`.

## The route

The blueprint transports `Σ` to the identity and diagonalizes `Σ^{-1/2}PΣ^{-1/2}`. The Lean proof
needs neither: it takes a nonzero `η ∈ ker P` (there is one, `rank P < d`) and a `ξ` with
`⟨ξ, Ση⟩ = 0` and `Pξ ≠ 0` (there is one: otherwise `P` vanishes on the hyperplane `(Ση)^⊥` and on
`η`, which is not in it, so `P = 0`, against `rank P > 0`). On `ker P` the transform of `ρ` is `1`,
so by `lem:charfn-one-on-subspace` it is invariant under translation by `ker P`; reading that
invariance at `tξ + sη`, where the two quadratic forms split (`⟨ξ, Ση⟩ = 0`, `Pη = 0`), is the
single-ratio equation with `a = 1 + ⟨ξ,Pξ⟩/⟨ξ,Σξ⟩`, and `t, s` range over all `(u, w)`.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- **`thm:rank-deficient-step`**: for `d ≥ 2`, `g ≥ 0` on `[0,∞)` continuous at `0` with
`g(0) = 0`, `Σ ∈ PD(d)`, `P ∈ PSD(d)` with `0 < rank P < d`, and a probability measure `ρ` with
`e^{-g(⟨ω,(Σ+P)ω⟩)} = e^{-g(⟨ω,Σω⟩)} ρ̂(ω)`, `g(u) = bu` with `b = g(1) ≥ 0` and `ρ` is the
centred Gaussian law with covariance `2bP`. -/
theorem rank_deficient_step (_hd : 2 ≤ d) (g : ℝ → ℝ) (hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u)
    (hg_cont : ContinuousWithinAt g (Set.Ici 0) 0) (hg_zero : g 0 = 0) (S P : Mat d)
    (hS : S.PosDef) (hP : P.PosSemidef) (hrank_pos : 0 < P.rank) (hrank_lt : P.rank < d)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (hstep : ∀ ω : Rd d, ((Real.exp (-g (quad (S + P) ω)) : ℝ) : ℂ) =
      ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * charFun ρ ω) :
    (∀ u : ℝ, 0 ≤ u → g u = g 1 * u) ∧ 0 ≤ g 1 ∧
      ρ = multivariateGaussian 0 ((2 * g 1) • P) := by
  /- The transform of `ρ`. -/
  have hρ : ∀ ω : Rd d,
      charFun ρ ω = ((Real.exp (-g (quad (S + P) ω) + g (quad S ω)) : ℝ) : ℂ) := by
    intro ω
    have h01 : ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * ((Real.exp (g (quad S ω)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
    rw [Real.exp_add, Complex.ofReal_mul, hstep ω]
    calc charFun ρ ω
        = (((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * ((Real.exp (g (quad S ω)) : ℝ) : ℂ)) *
            charFun ρ ω := by rw [h01, one_mul]
      _ = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * charFun ρ ω *
            ((Real.exp (g (quad S ω)) : ℝ) : ℂ) := by ring
  /- A nonzero `η` in the kernel of `P`. -/
  obtain ⟨η, hη0, hPη⟩ : ∃ η : Rd d, η ≠ 0 ∧ lin P η = 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective P.mulVec := by
      intro x y hxy
      have hz : P *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
      by_contra hne
      have hne' : WithLp.toLp 2 (x - y) ≠ (0 : Rd d) := by
        intro h
        apply hne
        have := congrArg WithLp.ofLp h
        simp only [WithLp.ofLp_zero] at this
        exact sub_eq_zero.1 this
      apply hcon _ hne'
      apply (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).injective
      simp [ofLp_lin, hxy]
    have hunit : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    have := Matrix.rank_of_isUnit P hunit
    rw [Fintype.card_fin] at this
    omega
  /- A `ξ` with `⟨ξ, Ση⟩ = 0` and `Pξ ≠ 0`. -/
  have hqSη : 0 < quad S η := quad_pos hS hη0
  obtain ⟨ξ, hξS, hPξ⟩ : ∃ ξ : Rd d, ⟪ξ, lin S η⟫ = 0 ∧ lin P ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hP0 : lin P = 0 := by
      ext1 ω
      set c : ℝ := ⟪ω, lin S η⟫ / quad S η with hc
      have h1 : ⟪ω - c • η, lin S η⟫ = 0 := by
        rw [inner_sub_left, real_inner_smul_left]
        have : c * ⟪η, lin S η⟫ = ⟪ω, lin S η⟫ := by
          rw [hc]
          change ⟪ω, lin S η⟫ / quad S η * quad S η = ⟪ω, lin S η⟫
          field_simp
        rw [this, sub_self]
      have h2 := hcon _ h1
      rw [map_sub, map_smul, hPη, smul_zero, sub_zero] at h2
      rw [h2]
      rfl
    have hPz : P = 0 := lin_injective (by rw [hP0]; exact (map_zero _).symm)
    rw [hPz, Matrix.rank_zero] at hrank_pos
    exact lt_irrefl _ hrank_pos
  have hξ0 : ξ ≠ 0 := by
    intro h
    apply hPξ
    rw [h, map_zero]
  have hqSξ : 0 < quad S ξ := quad_pos hS hξ0
  have hqPξ : 0 < quad P ξ := lt_of_le_of_ne (quad_nonneg hP ξ)
    (fun h => hPξ ((quad_eq_zero_iff hP ξ).1 h.symm))
  /- The transform of `ρ` is `1` on `ker P`, hence invariant under translation by `ker P`. -/
  set Hk : Submodule ℝ (Rd d) := LinearMap.ker (lin P : Rd d →ₗ[ℝ] Rd d) with hHk
  have hquadker : ∀ ζ ∈ Hk, quad P ζ = 0 := by
    intro ζ hζ
    have : lin P ζ = 0 := LinearMap.mem_ker.1 hζ
    simp [quad, this]
  have hker1 : ∀ ζ ∈ Hk, charFun ρ ζ = 1 := by
    intro ζ hζ
    rw [hρ, quad_add, hquadker ζ hζ, add_zero, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hinv := (charFun_one_on_subspace ρ Hk 1 one_pos (fun ζ hζ _ => hker1 ζ hζ)).2
  /- The single-ratio equation. -/
  set p : ℝ := quad P ξ / quad S ξ with hp
  have hp0 : 0 < p := div_pos hqPξ hqSξ
  have hratio : ∀ u w : ℝ, 0 < u → 0 ≤ w →
      g ((1 + p) * u + w) - g (u + w) = g ((1 + p) * u) - g u := by
    intro u w hu hw
    set t : ℝ := Real.sqrt (u / quad S ξ) with ht
    set s : ℝ := Real.sqrt (w / quad S η) with hs
    have ht2 : t ^ 2 = u / quad S ξ := Real.sq_sqrt (div_nonneg hu.le hqSξ.le)
    have hs2 : s ^ 2 = w / quad S η := Real.sq_sqrt (div_nonneg hw hqSη.le)
    have hηker : s • η ∈ Hk := Hk.smul_mem s (LinearMap.mem_ker.2 hPη)
    have h := hinv (t • ξ) (s • η) hηker
    rw [hρ, hρ] at h
    have hcross : ⟪t • ξ, lin S (s • η)⟫ = 0 := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, hξS, mul_zero, mul_zero]
    have hcrossP : ⟪t • ξ, lin P (s • η)⟫ = 0 := by
      rw [map_smul, hPη, smul_zero, inner_zero_right]
    have hqPη : quad P η = 0 := hquadker η (LinearMap.mem_ker.2 hPη)
    have hq1 : quad S (t • ξ + s • η) = u + w := by
      rw [quad_add_vec hS.isHermitian, quad_smul_vec, quad_smul_vec, hcross, ht2, hs2]
      field_simp
      ring
    have hq2 : quad P (t • ξ + s • η) = p * u := by
      rw [quad_add_vec hP.isHermitian, quad_smul_vec, quad_smul_vec, hcrossP, hqPη, ht2, hp]
      field_simp
      ring
    have hq3 : quad S (t • ξ) = u := by
      rw [quad_smul_vec, ht2]
      field_simp
    have hq4 : quad P (t • ξ) = p * u := by
      rw [quad_smul_vec, ht2, hp]
      field_simp
    rw [quad_add, quad_add, hq1, hq2, hq3, hq4] at h
    have h' := Real.exp_injective (Complex.ofReal_injective h)
    have e1 : (1 + p) * u + w = u + w + p * u := by ring
    have e2 : (1 + p) * u = u + p * u := by ring
    rw [e1, e2]
    linarith
  obtain ⟨hlin, hg1⟩ :=
    single_ratio_cauchy g hg_nonneg hg_cont hg_zero (1 + p) (by linarith) hratio
  refine ⟨hlin, hg1, ?_⟩
  /- The increment is the Gaussian, by uniqueness of the transform. -/
  have hX : ((2 * g 1) • P).PosSemidef := hP.smul (by positivity)
  apply Measure.ext_of_charFun
  funext ω
  rw [hρ, charFun_multivariateGaussian_zero hX,
    hlin _ (quad_nonneg (hS.posSemidef.add hP) ω), hlin _ (quad_nonneg hS.posSemidef ω), quad_add,
    quad_smul]
  congr 2
  ring

/-- **`thm:rank-deficient-step`**, the converse: if `g(u) = bu` with `b ≥ 0`, the one-step
identity holds with the centred Gaussian of covariance `2bP` for every `Σ, P ∈ PSD(d)`. -/
theorem rank_deficient_step_converse (_hd : 2 ≤ d) (g : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hg : ∀ u : ℝ, 0 ≤ u → g u = b * u) (S P : Mat d) (hS : S.PosSemidef) (hP : P.PosSemidef)
    (ω : Rd d) :
    ((Real.exp (-g (quad (S + P) ω)) : ℝ) : ℂ) =
      ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) * charFun (multivariateGaussian 0 ((2 * b) • P)) ω := by
  have hX : ((2 * b) • P).PosSemidef := hP.smul (by positivity)
  rw [charFun_multivariateGaussian_zero hX, hg _ (quad_nonneg (hS.add hP) ω),
    hg _ (quad_nonneg hS ω), quad_add, quad_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

end AffineHemigroup
