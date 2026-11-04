/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.KernelsOperators
import AffineHemigroup.Rigidity

/-!
# `thm:affine-rigidity-operators`: affine rigidity on operators

Blueprint: `blueprint/src/parts/04-classical.tex`. Q-0281, wave M, phase 2.

`thm:affine-rigidity` read on the operator axioms of the case `(GL(d), Loewner)`, by assembly:
the passage of `lem:operators-to-kernels-families`(4) and its converse
`lem:kernels-to-operators`(2), the representing measures existing by
`lem:operators-to-kernels`(1) (`kernels_operators_correspondence`); the constant `b` is read off
`Φ_{0,I}` through the uniqueness of the representing measure and the transform of the affine
Gaussian law at a unit vector.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder
open ScaleSpace (mconvL1E)

variable {d : ℕ}

/-- `(GL(d), Loewner)` is a wedge datum (`lem:gw-scheme-claims`(2)). -/
theorem isWedgeDatum_gl_loewner : IsWedgeDatum (glSet d) loewnerLE :=
  isWedgeDatum_loewner glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2

/-- The affine Gaussian scale space with constant `b` represents the operators `Φ` on the
Loewner pairs. -/
theorem isConvOnPairs_affineGaussian {Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)} {b : ℝ}
    (h : ∀ p ∈ wedgePairs loewnerLE, Φ p.1 p.2 = mconvL1E (affineGaussian b p.1 p.2)) :
    IsConvOnPairs loewnerLE Φ (affineGaussian b) :=
  fun p hp => ⟨inferInstance, h p hp⟩

/-- **`thm:affine-rigidity-operators`**: for `d ≥ 2`, a family of operators on `L¹(ℝ^d)` is a
`(GL(d), Loewner)`-cascade family of operators if and only if there is `b > 0` with
`Φ_{Σ,Σ'} = μ_{Σ,Σ'} ∗ ·` on every Loewner pair, `μ` the affine Gaussian scale space with constant
`b`; and the constant `b` is then unique. -/
theorem affine_rigidity_operators (hd : 2 ≤ d) (Φ : Mat d → Mat d → (L1 d →L[ℝ] L1 d)) :
    (IsGWOperatorFamily (glSet d) loewnerLE Φ ↔
        ∃ b : ℝ, 0 < b ∧
          ∀ p ∈ wedgePairs loewnerLE, Φ p.1 p.2 = mconvL1E (affineGaussian b p.1 p.2)) ∧
      ∀ b b' : ℝ, 0 < b → 0 < b' →
        (∀ p ∈ wedgePairs loewnerLE, Φ p.1 p.2 = mconvL1E (affineGaussian b p.1 p.2)) →
        (∀ p ∈ wedgePairs loewnerLE, Φ p.1 p.2 = mconvL1E (affineGaussian b' p.1 p.2)) →
          b = b' := by
  have hd1 : 1 ≤ d := by omega
  have hW := isWedgeDatum_gl_loewner (d := d)
  refine ⟨⟨fun hΦ => ?_, fun ⟨b, hb, h⟩ => ?_⟩, fun b b' hb hb' h h' => ?_⟩
  · obtain ⟨μ, hμ⟩ := (kernels_operators_correspondence hd1 hW).2.1 Φ hΦ
    obtain ⟨b, hb, hEq⟩ :=
      (affine_rigidity hd μ).mp (operators_to_kernels_affine hd1 Φ hΦ μ hμ)
    refine ⟨b, hb, fun p hp => ?_⟩
    haveI := hμ.prob hp
    rw [hμ.eq hp]
    exact ScaleSpace.mconvL1E_congr (hEq p hp)
  · have hfam : IsAffineCascadeFamily (affineGaussian (d := d) b) :=
      (affine_rigidity hd _).mpr ⟨b, hb, fun _ _ => rfl⟩
    exact (kernels_to_operators_gw hd1 hW _ hfam Φ (isConvOnPairs_affineGaussian h)).1
  · have hp := wedge_zero_one_mem hW
    have h01 : affineGaussian b (0 : Mat d) 1 = affineGaussian b' 0 1 :=
      eq_of_mconvL1E_eq ((h _ hp).symm.trans (h' _ hp))
    set e : Rd d := EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) with he
    have hle : loewnerLE (0 : Mat d) 1 := hp.2.2
    have hc := congrArg (fun m => charFun m e) h01
    simp only [charFun_affineGaussian hb PosSemidef.zero PosSemidef.one hle,
      charFun_affineGaussian hb' PosSemidef.zero PosSemidef.one hle, sub_zero, quad_one,
      he, PiLp.norm_single, norm_one, one_pow, mul_one, Complex.ofReal_inj,
      Real.exp_eq_exp, neg_inj] at hc
    exact hc

end AffineHemigroup
