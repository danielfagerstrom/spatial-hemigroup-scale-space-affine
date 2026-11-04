/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginLowerBound
import AffineHemigroup.EllipticalStable
import AffineHemigroup.OrbitStepCone
import AffineHemigroup.Orbits

/-!
# Triplets of convolutions, and infinitely divisible increments

The calculus that `prop:similarity-orbit-family`(1), `prop:similarity-general-sandwich`(2) and the
nodes that read them share: the exponents of a convolution add, so the generating triplet of
`μ * ρ` is the sum of the triplets (`HasTriplet.conv`), and an infinitely divisible increment
`μ' = μ * ρ` between two infinitely divisible laws adds a triplet (`triplet_increment`, A3(i) for
`ρ` and the uniqueness A3(ii) for `μ'`). Besides: infinite divisibility is kept by convolution and
by linear images, and centred Gaussian laws are infinitely divisible (Lean core); the Gaussian
triplet `(C, 0, 0)` and the triplet `(0, n_H(x)dx, 0)` of the orbit of a profile.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory Complex
open ScaleSpace (isFiniteMeasure_convPow_Rd)
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## Infinite divisibility is kept -/

/-- A convolution of infinitely divisible finite measures is infinitely divisible. -/
theorem IsInfinitelyDivisible.conv {μ ν : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : IsInfinitelyDivisible μ) (hν : IsInfinitelyDivisible ν) :
    IsInfinitelyDivisible (μ ∗ ν) := by
  intro n hn
  obtain ⟨a, ha, han⟩ := hμ n hn
  obtain ⟨b, hb, hbn⟩ := hν n hn
  refine ⟨a ∗ b, inferInstance, ?_⟩
  haveI := isFiniteMeasure_convPow_Rd (a ∗ b) n
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_convPow, charFun_conv, charFun_conv, ← han, ← hbn, charFun_convPow, charFun_convPow,
    mul_pow]

/-- A linear image of an infinitely divisible finite measure is infinitely divisible. -/
theorem IsInfinitelyDivisible.push {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (A : Mat d) :
    IsInfinitelyDivisible (AffineHemigroup.push A μ) := by
  intro n hn
  obtain ⟨a, ha, han⟩ := hμ n hn
  refine ⟨AffineHemigroup.push A a, inferInstance, ?_⟩
  haveI : IsFiniteMeasure (AffineHemigroup.push A μ) := by
    unfold AffineHemigroup.push; infer_instance
  haveI := isFiniteMeasure_convPow_Rd (AffineHemigroup.push A a) n
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_convPow, AffineHemigroup.push, charFun_map_lin, ← han, AffineHemigroup.push,
    charFun_map_lin, charFun_convPow]

/-- A centred Gaussian law is infinitely divisible. -/
theorem isInfinitelyDivisible_gaussian {C : Mat d} (hC : C.PosSemidef) :
    IsInfinitelyDivisible (multivariateGaussian 0 C) := by
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨multivariateGaussian 0 ((n : ℝ)⁻¹ • C), inferInstance, ?_⟩
  haveI := isFiniteMeasure_convPow_Rd (multivariateGaussian 0 ((n : ℝ)⁻¹ • C)) n
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_convPow, charFun_multivariateGaussian_zero (hC.smul (inv_pos.2 hn').le),
    charFun_multivariateGaussian_zero hC, ← Complex.ofReal_pow, ← Real.exp_nat_mul, quad_smul]
  congr 3
  field_simp

/-! ## Sums of triplets -/

/-- **The sum of two triplets** `(A + A', ν + ν', γ + γ')`. -/
noncomputable def LevyTriplet.add (T T' : LevyTriplet d) : LevyTriplet d where
  A := T.A + T'.A
  ν := T.ν + T'.ν
  γ := T.γ + T'.γ
  A_posSemidef := T.A_posSemidef.add T'.A_posSemidef
  ν_zero := by simp [T.ν_zero, T'.ν_zero]
  ν_integrable := by
    rw [lintegral_add_measure]
    exact ENNReal.add_ne_top.2 ⟨T.ν_integrable, T'.ν_integrable⟩

/-- The exponents of a sum of triplets add. -/
theorem LevyTriplet.lkExponent_add (T T' : LevyTriplet d) (z : Rd d) :
    (T.add T').lkExponent z = T.lkExponent z + T'.lkExponent z := by
  rw [LevyTriplet.lkExponent_eq, LevyTriplet.lkExponent_eq, LevyTriplet.lkExponent_eq]
  have hA : (T.add T').A = T.A + T'.A := rfl
  have hν : (T.add T').ν = T.ν + T'.ν := rfl
  have hγ : (T.add T').γ = T.γ + T'.γ := rfl
  rw [hA, hν, hγ, quad_add, inner_add_left,
    integral_add_measure (T.integrable_lkIntegrand z) (T'.integrable_lkIntegrand z)]
  push_cast
  ring

/-- **The triplet of a convolution** is the sum of the triplets. -/
theorem HasTriplet.conv {μ ρ : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {T T' : LevyTriplet d} (h : HasTriplet μ T) (h' : HasTriplet ρ T') :
    HasTriplet (μ ∗ ρ) (T.add T') := fun z => by
  rw [charFun_conv, h z, h' z, LevyTriplet.lkExponent_add, Complex.exp_add]

/-- **An infinitely divisible increment adds a triplet** (A3(i)–(ii)): if `μ' = μ * ρ` with `ρ` an
infinitely divisible probability measure, `μ` has the triplet `T` and the infinitely divisible
`μ'` has `T'`, then `T' = T + T_ρ` for the triplet `T_ρ` of `ρ`. -/
theorem triplet_increment {μ μ' ρ : Measure (Rd d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ρ] (hρ : IsInfinitelyDivisible ρ)
    (hμ' : IsInfinitelyDivisible μ') {T T' : LevyTriplet d} (hT : HasTriplet μ T)
    (heq : μ' = μ ∗ ρ) (hT' : HasTriplet μ' T') :
    ∃ Tρ : LevyTriplet d, HasTriplet ρ Tρ ∧ T'.A = T.A + Tρ.A ∧ T'.ν = T.ν + Tρ.ν ∧
      T'.γ = T.γ + Tρ.γ := by
  obtain ⟨Tρ, hTρ⟩ := levy_khintchine_exists ρ hρ
  have hsum : HasTriplet μ' (T.add Tρ) := heq ▸ hT.conv hTρ
  obtain ⟨hA, hν, hγ⟩ := levy_khintchine_unique μ' hμ' T' (T.add Tρ) hT' hsum
  exact ⟨Tρ, hTρ, hA, hν, hγ⟩

/-! ## Two triplets -/

/-- **The Gaussian triplet** `(C, 0, 0)`. -/
noncomputable def gaussTriplet (C : Mat d) (hC : C.PosSemidef) : LevyTriplet d where
  A := C
  ν := 0
  γ := 0
  A_posSemidef := hC
  ν_zero := rfl
  ν_integrable := by simp

theorem hasTriplet_gaussian {C : Mat d} (hC : C.PosSemidef) :
    HasTriplet (multivariateGaussian 0 C) (gaussTriplet C hC) := fun z => by
  rw [charFun_multivariateGaussian_zero hC, LevyTriplet.lkExponent_eq]
  simp [gaussTriplet, Complex.ofReal_exp]

/-- The density of the orbit is integrable in the sense of `densTriplet`. -/
theorem orbitDensity_restrict_integrable (hd : 1 ≤ d) (K : RadialProfile d) {H : Mat d}
    (hH : H.PosDef) :
    ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * K.orbitDensity H x) ≠ ⊤ :=
  ne_top_of_le_ne_top (K.orbitDensity_integrable hd hH) (setLIntegral_le_lintegral _ _)

/-- **The triplet of the orbit of a profile**: `(H^{1/2})_*μ_I` has the triplet
`(0, n_H(x)dx, 0)`. -/
theorem hasTriplet_affineOrbit_profile (hd : 1 ≤ d) (K : RadialProfile d) {μI : Measure (Rd d)}
    (hμI : IsProfileLaw K μI) {H : Mat d} (hH : H.PosDef) :
    HasTriplet (affineOrbit μI H) (densTriplet (K.orbitDensity H)
      (K.measurable_orbitDensity hd H) (orbitDensity_restrict_integrable hd K hH)) := fun z => by
  haveI : NeZero d := ⟨by omega⟩
  rw [densTriplet_lkExponent _ _ _ (K.orbitDensity_neg H) z,
    charFun_affineOrbit_profile hd K hμI hH z, restrict_compl_singleton, Complex.ofReal_exp,
    Complex.ofReal_neg]

end AffineHemigroup
