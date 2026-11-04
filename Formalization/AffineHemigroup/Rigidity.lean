/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.RankDeficient
import AffineHemigroup.Reduction

/-!
# `thm:affine-rigidity` — affine rigidity: the affine Gaussian scale space

Blueprint: `blueprint/src/parts/04-classical.tex`, `thm:affine-rigidity`. Lean core only.

Necessity is `lem:affine-reduction` followed by `thm:rank-deficient-step` at the one step
`I ≤ I + e₁e₁ᵀ`, written `P = diag(1, 0, …, 0)`; sufficiency checks (K1)–(K4) on the transforms
(`lem:affine-gaussian-transform`, `lem:gw-scheme-claims`(3)) and names each law by uniqueness of
the transform.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- **`thm:affine-rigidity`**: for `d ≥ 2`, a family is an affine cascade family in dimension `d`
if and only if it is the affine Gaussian scale space with some constant `b > 0` (on the Loewner
pairs, which is all a family is read on). -/
theorem affine_rigidity (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d)) :
    IsAffineCascadeFamily μ ↔ ∃ b : ℝ, 0 < b ∧ EqOnPairs loewnerLE μ (affineGaussian b) := by
  have hle0 : ∀ S : Mat d, S.PosSemidef → loewnerLE 0 S := fun S hS => by
    rw [loewnerLE, sub_zero]
    exact hS
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set e₀ : Rd d := EuclideanSpace.single i₀ (1 : ℝ) with he₀def
  constructor
  /- Necessity. -/
  · intro hμ
    obtain ⟨g, hgc, hgnn, hg0, ⟨u₀, hu₀, hgu₀⟩, -, hinc⟩ := affine_reduction μ hμ
    set P : Mat d := diagonal (Pi.single i₀ 1) with hPdef
    have hP : P.PosSemidef := by
      apply PosSemidef.diagonal
      intro i
      by_cases h : i = i₀
      · subst h
        simp
      · simp [h]
    have hrank : P.rank = 1 := by
      classical
      rw [hPdef, rank_diagonal]
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨i₀, by simp⟩, ?_⟩
      rintro ⟨j, hj⟩
      apply Subtype.ext
      by_contra hne
      exact hj (by simp [hne])
    have hIP : loewnerLE (1 : Mat d) (1 + P) := by
      rw [loewnerLE, add_sub_cancel_left]
      exact hP
    have hmem : ((1 : Mat d), 1 + P) ∈ wedgePairs loewnerLE :=
      ⟨PosSemidef.one, PosSemidef.one.add hP, hIP⟩
    haveI := hμ.isProbability _ hmem
    have hstep : ∀ ω : Rd d, ((Real.exp (-g (quad (1 + P) ω)) : ℝ) : ℂ) =
        ((Real.exp (-g (quad 1 ω)) : ℝ) : ℂ) * charFun (μ 1 (1 + P)) ω := by
      intro ω
      rw [hinc 1 (1 + P) PosSemidef.one (PosSemidef.one.add hP) hIP ω, ← Complex.ofReal_mul,
        ← Real.exp_add]
      congr 2
      ring
    obtain ⟨hlin, hb0, -⟩ := rank_deficient_step hd g hgnn (hgc 0 self_mem_Ici) hg0 1 P
      PosDef.one hP (by rw [hrank]; norm_num) (by rw [hrank]; omega) (μ 1 (1 + P)) hstep
    have hb : 0 < g 1 := lt_of_le_of_ne hb0 (fun h => hgu₀ (by rw [hlin u₀ hu₀, ← h, zero_mul]))
    refine ⟨g 1, hb, ?_⟩
    rintro ⟨S, S'⟩ ⟨hS, hS', hle⟩
    haveI := hμ.isProbability (S, S') ⟨hS, hS', hle⟩
    apply Measure.ext_of_charFun
    funext ω
    rw [hinc S S' hS hS' hle ω, charFun_affineGaussian hb hS hS' hle ω,
      hlin _ (quad_nonneg hS' ω), hlin _ (quad_nonneg hS ω), quad_sub]
    congr 2
    ring
  /- Sufficiency. -/
  · rintro ⟨b, hb, hEq⟩
    have hpair : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
        μ S S' = affineGaussian b S S' := fun S S' hS hS' h => hEq (S, S') ⟨hS, hS', h⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- probability measures
      rintro ⟨S, S'⟩ hp
      rw [hEq _ hp]
      infer_instance
    · -- (K1), the diagonal
      intro S hS
      have hSS : loewnerLE S S := by
        rw [loewnerLE, sub_self]
        exact PosSemidef.zero
      rw [hpair S S hS hS hSS]
      apply Measure.ext_of_charFun
      funext ω
      rw [charFun_affineGaussian hb hS hS hSS, charFun_dirac, sub_self, quad_zero]
      simp
    · -- (K1), the cascade
      intro S S' S'' hS hS' hS'' h1 h2
      have h3 : loewnerLE S S'' := by
        have := PosSemidef.add h2 h1
        rwa [loewnerLE, ← sub_add_sub_cancel S'' S' S]
      rw [hpair S S'' hS hS'' h3, hpair S' S'' hS' hS'' h2, hpair S S' hS hS' h1]
      apply Measure.ext_of_charFun
      funext ω
      rw [charFun_conv, charFun_affineGaussian hb hS hS'' h3, charFun_affineGaussian hb hS' hS'' h2,
        charFun_affineGaussian hb hS hS' h1, ← Complex.ofReal_mul, ← Real.exp_add,
        ← sub_add_sub_cancel S'' S' S, quad_add]
      congr 2
      ring
    · -- (K2)
      intro ω
      have hc : Continuous fun p : Mat d × Mat d =>
          ((Real.exp (-(b * quad (p.2 - p.1) ω)) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_const.mul ((continuous_quad ω).comp
            (continuous_snd.sub continuous_fst))).neg))
      refine hc.continuousOn.congr ?_
      rintro ⟨S, S'⟩ ⟨hS, hS', hle⟩
      simp only
      rw [hpair S S' hS hS' hle, charFun_affineGaussian hb hS hS' hle]
    · -- (K3)
      rintro A hA ⟨S, S'⟩ ⟨hS, hS', hle⟩
      simp only
      have hAS := posSemidef_act A hS
      have hAS' := posSemidef_act A hS'
      have hAle := loewnerLE_act A hle
      rw [hpair S S' hS hS' hle, hpair _ _ hAS hAS' hAle]
      haveI : IsProbabilityMeasure (push A (affineGaussian b S S')) := by
        unfold push
        exact Measure.isProbabilityMeasure_map (lin A).continuous.aemeasurable
      apply Measure.ext_of_charFun
      funext ω
      rw [charFun_push A hA, charFun_affineGaussian hb hS hS' hle,
        charFun_affineGaussian hb hAS hAS' hAle, act_sub, quad_act]
    · -- (K4)
      rw [hpair 0 1 PosSemidef.zero PosSemidef.one (hle0 1 PosSemidef.one)]
      intro h
      have h1 := congrArg (fun m => charFun m e₀) h
      rw [charFun_affineGaussian hb PosSemidef.zero PosSemidef.one (hle0 1 PosSemidef.one),
        charFun_dirac, sub_zero, quad_one] at h1
      have he₀ : ‖e₀‖ = 1 := by simp [he₀def]
      rw [he₀, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
      have h2 : Real.exp (-(b * 1 ^ 2)) = 1 := by exact_mod_cast h1
      rw [Real.exp_eq_one_iff] at h2
      nlinarith

/-- **`thm:affine-rigidity`**, in particular: the kernel `μ_I` of an affine cascade family in
dimension `d ≥ 2` is a centred Gaussian law with covariance a positive multiple of `I`, and no
other law is the kernel `μ_I` of one. -/
theorem affine_rigidity_kernel (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsAffineCascadeFamily μ) :
    ∃ b : ℝ, 0 < b ∧ μ 0 1 = multivariateGaussian 0 ((2 * b) • (1 : Mat d)) := by
  obtain ⟨b, hb, h⟩ := (affine_rigidity hd μ).1 hμ
  refine ⟨b, hb, ?_⟩
  have hmem : ((0 : Mat d), (1 : Mat d)) ∈ wedgePairs loewnerLE :=
    ⟨PosSemidef.zero, PosSemidef.one, by rw [loewnerLE, sub_zero]; exact PosSemidef.one⟩
  have := h _ hmem
  simp only at this
  rw [this, affineGaussian, sub_zero]

end AffineHemigroup
