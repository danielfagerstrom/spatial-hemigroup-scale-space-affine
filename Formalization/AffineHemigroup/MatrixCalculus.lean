/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic

/-!
# The calculus of `lin`, `act`, `quad` and `push`

What every chapter reads of the matrix calculus: `lin` is a star algebra map (so `lin Aᵀ` is the
adjoint of `lin A`); the quadratic form `quad` is additive and homogeneous in the matrix,
quadratic in the vector, and transported by `act`; the action preserves `PSD(d)` and the Loewner
order; the transform of an image measure, `charFun_map_lin` and `charFun_push`
(`lem:gw-scheme-claims`(3), which `def:isotropic-kernel-family` reads); two measures with one
transform are equal; an image of a probability measure is one; `Mat d` is first countable.
Lean core only.

Every declaration stood in a file of chapters 4 and 5, named in the heading of its section, and
that file imports this one. They are here unchanged, each with the `open` lines of its file, so
that the files of the isotropic theory can read them without the scheme, the gauge, the orbits
and the invariant orders (Q-0452).
-/

namespace AffineHemigroup

/-! ## From `AffineHemigroup.Scheme`: the matrix calculus and the transform of an image -/

section

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- `lin` is multiplicative. -/
theorem lin_mul (A B : Mat d) : lin (A * B) = lin A * lin B :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) A B

/-- `lin 1` is the identity. -/
theorem lin_one : lin (1 : Mat d) = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))

/-- `lin` is additive. -/
theorem lin_add (A B : Mat d) : lin (A + B) = lin A + lin B :=
  map_add (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) A B

/-- `lin` commutes with subtraction. -/
theorem lin_sub (A B : Mat d) : lin (A - B) = lin A - lin B :=
  map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) A B

/-- `lin` is homogeneous. -/
theorem lin_smul (c : ℝ) (A : Mat d) : lin (c • A) = c • lin A :=
  map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) c A

/-- `lin` is injective. -/
theorem lin_injective : Function.Injective (lin : Mat d → Rd d →L[ℝ] Rd d) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).injective

/-- **`lin Aᵀ` is the adjoint of `lin A`** (`toEuclideanCLM` is a star algebra equivalence). -/
theorem lin_transpose (A : Mat d) : lin Aᵀ = ContinuousLinearMap.adjoint (lin A) := by
  have h := map_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) A
  rw [ContinuousLinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- `⟪lin A x, y⟫ = ⟪x, lin Aᵀ y⟫`. -/
theorem inner_lin_left (A : Mat d) (x y : Rd d) : ⟪lin A x, y⟫ = ⟪x, lin Aᵀ y⟫ := by
  rw [lin_transpose, ContinuousLinearMap.adjoint_inner_right]

/-- The coordinates of `lin A x` are `A *ᵥ x`. -/
theorem ofLp_lin (A : Mat d) (x : Rd d) : (lin A x).ofLp = A *ᵥ x.ofLp := rfl

/-- `quad S ω = ωᵀ S ω`. -/
theorem quad_eq_dotProduct (S : Mat d) (ω : Rd d) : quad S ω = ω.ofLp ⬝ᵥ S *ᵥ ω.ofLp :=
  inner_toEuclideanCLM S ω ω

theorem quad_add (S P : Mat d) (ω : Rd d) : quad (S + P) ω = quad S ω + quad P ω := by
  simp only [quad, lin_add, _root_.add_apply, inner_add_right]

theorem quad_sub (S P : Mat d) (ω : Rd d) : quad (S - P) ω = quad S ω - quad P ω := by
  simp only [quad, lin_sub, _root_.sub_apply, inner_sub_right]

theorem quad_smul (c : ℝ) (S : Mat d) (ω : Rd d) : quad (c • S) ω = c * quad S ω := by
  simp only [quad, lin_smul, _root_.smul_apply, real_inner_smul_right]

theorem quad_zero (ω : Rd d) : quad (0 : Mat d) ω = 0 := by
  simpa using quad_smul 0 (0 : Mat d) ω

/-- `quad S (t ω) = t² quad S ω`. -/
theorem quad_smul_vec (S : Mat d) (t : ℝ) (ω : Rd d) : quad S (t • ω) = t ^ 2 * quad S ω := by
  simp only [quad, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- `quad I ω = ‖ω‖²`. -/
theorem quad_one (ω : Rd d) : quad (1 : Mat d) ω = ‖ω‖ ^ 2 := by
  simp only [quad, lin_one, one_apply_eq_self, real_inner_self_eq_norm_sq]

/-- **`quad` under the action**: `⟨ω, AΣAᵀω⟩ = ⟨Aᵀω, ΣAᵀω⟩`. -/
theorem quad_act (A S : Mat d) (ω : Rd d) : quad (act A S) ω = quad S (lin Aᵀ ω) := by
  simp only [quad, act, lin_mul, mul_apply_eq_comp]
  rw [real_inner_comm, inner_lin_left, real_inner_comm]

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem quad_nonneg {S : Mat d} (hS : S.PosSemidef) (ω : Rd d) : 0 ≤ quad S ω := by
  rw [quad_eq_dotProduct]
  simpa using hS.dotProduct_mulVec_nonneg ω.ofLp

/-- The quadratic form of a positive definite matrix is positive off `0`. -/
theorem quad_pos {S : Mat d} (hS : S.PosDef) {ω : Rd d} (hω : ω ≠ 0) : 0 < quad S ω := by
  rw [quad_eq_dotProduct]
  have h0 : ω.ofLp ≠ 0 := by
    intro h
    exact hω (by simpa using congrArg (WithLp.toLp 2) h)
  simpa using hS.dotProduct_mulVec_pos h0

/-- For a positive semidefinite `S`, `quad S ω = 0` exactly when `S ω = 0`. -/
theorem quad_eq_zero_iff {S : Mat d} (hS : S.PosSemidef) (ω : Rd d) :
    quad S ω = 0 ↔ lin S ω = 0 := by
  rw [quad_eq_dotProduct]
  have h := hS.dotProduct_mulVec_zero_iff ω.ofLp
  simp only [star_trivial] at h
  rw [h]
  constructor
  · intro h'
    have : (lin S ω).ofLp = 0 := h'
    simpa using congrArg (WithLp.toLp 2) this
  · intro h'
    have : (lin S ω).ofLp = 0 := by rw [h']; rfl
    exact this

/-- `Σ ↦ quad Σ ω` is continuous. -/
theorem continuous_quad (ω : Rd d) : Continuous fun S : Mat d => quad S ω := by
  simp_rw [quad_eq_dotProduct]
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- `quad` is symmetric in the two vectors of the polarization for a symmetric matrix:
`quad Σ (ξ + η) = quad Σ ξ + quad Σ η + 2⟨ξ, Σ η⟩`. -/
theorem quad_add_vec {S : Mat d} (hS : S.IsHermitian) (ξ η : Rd d) :
    quad S (ξ + η) = quad S ξ + quad S η + 2 * ⟪ξ, lin S η⟫ := by
  have hT : Sᵀ = S := by
    have := hS.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h : ⟪η, lin S ξ⟫ = ⟪ξ, lin S η⟫ := by
    rw [real_inner_comm, inner_lin_left, hT]
  simp only [quad, map_add, inner_add_left, inner_add_right]
  rw [h]
  ring

/-- `0 ≤ Σ` is `Σ ∈ PSD(d)` under `MatrixOrder`. -/
theorem nonneg_of_posSemidef {S : Mat d} (hS : S.PosSemidef) : 0 ≤ S := by
  rw [← loewnerLE_iff_le, loewnerLE, sub_zero]
  exact hS

/-- The action preserves `PSD(d)`. -/
theorem posSemidef_act (A : Mat d) {S : Mat d} (hS : S.PosSemidef) : (act A S).PosSemidef := by
  have := hS.mul_mul_conjTranspose_same A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- The action is linear: `A · Σ' - A · Σ = A · (Σ' - Σ)`. -/
theorem act_sub (A S S' : Mat d) : act A S' - act A S = act A (S' - S) := by
  simp only [act, Matrix.mul_sub, Matrix.sub_mul]

/-- **The action preserves the Loewner order**, for every matrix `A`. -/
theorem loewnerLE_act (A : Mat d) {S S' : Mat d} (h : loewnerLE S S') :
    loewnerLE (act A S) (act A S') := by
  unfold loewnerLE
  rw [act_sub]
  exact posSemidef_act A h

/-- The transform of an image under `lin A`, for every matrix and every measure. -/
theorem charFun_map_lin (A : Mat d) (μ : Measure (Rd d)) (ω : Rd d) :
    charFun (μ.map (lin A)) ω = charFun μ (lin Aᵀ ω) := by
  rw [charFun_apply, charFun_apply,
    integral_map (lin A).continuous.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  ext x
  rw [inner_lin_left]

/-- **`lem:gw-scheme-claims`(3)**: `\widehat{A_*μ}(ω) = μ̂(Aᵀω)` for every probability measure
`μ` on `ℝ^d` and `A ∈ GL(d)`. -/
theorem charFun_push (A : Mat d) (_hA : A ∈ glSet d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (ω : Rd d) : charFun (push A μ) ω = charFun μ (lin Aᵀ ω) :=
  charFun_map_lin A μ ω

end

/-! ## From `AffineHemigroup.KernelsFromOrigin` -/

section

open MeasureTheory Matrix ProbabilityTheory
open scoped MatrixOrder

variable {d : ℕ}

/-- Two probability measures on `ℝ^d` with the same transform are equal (Mathlib's
`Measure.ext_of_charFun`, pointwise form). -/
theorem eq_of_charFun_eq {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ ω : Rd d, charFun μ ω = charFun ν ω) : μ = ν :=
  Measure.ext_of_charFun (funext h)

/-- The image of a probability measure under a matrix is a probability measure. -/
instance isProbabilityMeasure_push (A : Mat d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (push A μ) :=
  Measure.isProbabilityMeasure_map (lin A).continuous.aemeasurable

/-- `A · 0 = 0`. -/
@[simp] theorem act_zero (A : Mat d) : act A 0 = 0 := by simp [act]

end

/-! ## From `AffineHemigroup.Gauge` -/

section

open Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-- `Q · I = I` for `Q ∈ O(d)`. -/
theorem act_orth_one {Q : Mat d} (hQ : Q ∈ orthSet d) : act Q 1 = 1 := by
  rw [act, mul_one]
  exact (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ

end

/-! ## From `AffineHemigroup.ParameterSpace` -/

section

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- The transpose of an orthogonal matrix is orthogonal. -/
theorem transpose_mem_orthSet {Q : Mat d} (hQ : Q ∈ orthSet d) : Qᵀ ∈ orthSet d := by
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  change Qᵀ ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff]
  change Qᵀ * Qᵀᵀ = 1
  rw [transpose_transpose]; exact mul_eq_one_comm.1 hQQ

end

/-! ## From `AffineHemigroup.Orbits` -/

section

open MeasureTheory Set Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-- The image under the identity. -/
theorem push_one (μ : Measure (Rd d)) : push 1 μ = μ := by
  rw [push, lin_one]
  exact Measure.map_id

/-- `(λ²I)^{1/2} = λI` for `λ ≥ 0`. -/
theorem msqrt_sq_smul_one {c : ℝ} (hc : 0 ≤ c) : msqrt (c ^ 2 • (1 : Mat d)) = c • 1 := by
  have h0 : (0 : Mat d) ≤ c • 1 := nonneg_of_posSemidef (PosSemidef.one.smul hc)
  refine CFC.sqrt_unique ?_ h0
  rw [smul_mul_smul, Matrix.one_mul, sq]

end

/-! ## From `AffineHemigroup.RayFamilies` -/

section

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-- The transform of an image under `aI`: `\widehat{(aI)_*μ}(ω) = μ̂(aω)`. -/
theorem charFun_push_smul_one (a : ℝ) (μ : Measure (Rd d)) (ω : Rd d) :
    charFun (push (a • (1 : Mat d)) μ) ω = charFun μ (a • ω) := by
  rw [push, charFun_map_lin, transpose_smul, transpose_one, lin_smul, lin_one]
  rfl

end

/-! ## From `AffineHemigroup.InvariantOrders` -/

section

open Set Filter Matrix
open scoped Topology MatrixOrder

variable {d : ℕ}

/-- `Mat d` carries the product topology, which is first countable. -/
instance firstCountableTopology_mat : FirstCountableTopology (Mat d) :=
  inferInstanceAs (FirstCountableTopology (Fin d → Fin d → ℝ))

end

end AffineHemigroup
