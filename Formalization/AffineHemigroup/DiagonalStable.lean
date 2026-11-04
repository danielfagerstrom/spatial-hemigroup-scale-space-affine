/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.WedgeAxisChain
import AffineHemigroup.DiagonalRays
import AffineHemigroup.SimilarityStableOrder
import AffineHemigroup.IsotropicCorner
import AffineHemigroup.AnisotropyBudget
import AffineHemigroup.FrameFamilies

/-!
# `prop:diagonal-stable-order-families` — the cell (diagonal, stable order)

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:diagonal-stable-order-families`
(Q-0281 wave 2, group H). Clauses (1), (2), (3)(a) and (4)(a) print Lean core; (3)(b), (4)(b) and
(4)(c) spend A3(iii), through the stable laws and `prop:similarity-stable-order-families`(2).

## The route

The blueprint's. Two Lean forms:

* **(2)** reads the frame through `prop:diagonal-ray-families`(2) after restricting the family to
  the rays (`gw_family_restrict_of_le`), and the `B`-self-decomposability through the frame step
  `I ≤_α e^{2tB}` of (1), `e^{tB}` being the diagonal matrix `D_u`, `uᵢ = e^{tbᵢ}`.
* **(4)(a)** reads the failure of `B`-self-decomposability on one vector,
  `ω = x e₁ + e₂` with `x = -r(2+α)/(2(1+α))`: the quadratic form `f(t) = ⟨e^{-tB}ω, Θ_r e^{-tB}ω⟩`
  is at most `f(0)` for `t > 0` (the residual's transform has modulus at most `1`), so
  `f'(0) ≤ 0`, while `f'(0) = 2(r²(2+α)²/(4(1+α)) - 1) > 0`. This is the blueprint's `2 × 2` minor
  of
  `BΘ_r + Θ_rB` read at its negative direction.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-! ## Diagonal matrices -/

/-- `λ_min(diag b) = minᵢ bᵢ`. -/
theorem lamMin_diagonal [NeZero d] (b : Fin d → ℝ) : lamMin (diagonal b) = ⨅ i, b i := by
  have hh : (diagonal b).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, diagonal_transpose]
  apply le_antisymm
  · refine le_ciInf fun i => (lamMin_le_diag hh i).trans ?_
    simp
  · have h : (diagonal b - (⨅ i, b i) • (1 : Mat d)).PosSemidef := by
      rw [smul_one_eq_diagonal, diagonal_sub]
      exact PosSemidef.diagonal fun i => sub_nonneg.2 (ciInf_le (Finite.bddBelow_range b) i)
    rw [lamMin_eq_eigUp_zero hh]
    exact (posSemidef_sub_smul_one_iff hh _).1 h

/-- `(diag s)⁻¹ = diag(1/s)` for `s > 0`. -/
theorem inv_diagonal_pos {s : Fin d → ℝ} (hs : ∀ i, 0 < s i) :
    (diagonal s)⁻¹ = diagonal fun i => (s i)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hs i).ne'

/-- **The relative step of two frame shapes**: `D_s^{-1} D_{s'}² D_s^{-1} = D_u²`, `u = s'/s`. -/
theorem relStep_diagonal_sq {s s' : Fin d → ℝ} (hs : ∀ i, 0 < s i) :
    relStep (diagonal fun i => s i ^ 2) (diagonal fun i => s' i ^ 2) =
      diagonal fun i => (s' i / s i) ^ 2 := by
  have hsq : msqrt (diagonal fun i => s i ^ 2) = diagonal s := by
    rw [msqrt_diagonal fun i => sq_nonneg _]
    congr 1
    funext i
    exact Real.sqrt_sq (hs i).le
  rw [relStep, hsq, inv_diagonal_pos hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  field_simp

/-- `mexp (diag w) = diag (e^w)`. -/
theorem mexp_diagonal (w : Fin d → ℝ) : mexp (diagonal w) = diagonal fun i => Real.exp (w i) := by
  have h1 : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
  have h := mexp_udiag h1 w
  simpa [udiag] using h

/-! ## Clause (1), the datum -/

/-- **`prop:diagonal-stable-order-families`(1)**, the datum: `(D₊(d), ≤_α)` is a wedge datum (its
orbits in `PD(d)` are those of `prop:diagonal-ray-families`(1), the group being the same); `𝒟_α` is
the set of diagonal matrices of `𝔨_α`; and on the orbit of `I`, `D_s² ≤_α D_{s'}²` if and only if
`u := (s'ᵢ/sᵢ)` has `(min u)^{d+α} ≥ u₁ ⋯ u_d`. -/
theorem diagonal_stable_datum (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    IsWedgeDatum (diagPosSet d) (stablePlusLE α) ∧
      diagStableSet d α = {B | (∃ b : Fin d → ℝ, B = diagonal b) ∧ B ∈ stableExpCone d α} ∧
      ∀ s s' : Fin d → ℝ, (∀ i, 0 < s i) → (∀ i, 0 < s' i) →
        (stablePlusLE α (diagonal fun i => s i ^ 2) (diagonal fun i => s' i ^ 2) ↔
          ∏ i, s' i / s i ≤ (⨅ i, s' i / s i) ^ ((d : ℝ) + α)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hdα : 0 ≤ (d : ℝ) + α := by positivity
  refine ⟨(stablePlusLE_order hd hα0 hα2).2.2.2.2.2.1 _ diagPosSet_isClosedSubgroupGL.1
    diagPosSet_isClosedSubgroupGL.2, ?_, fun s s' hs hs' => ?_⟩
  · have hsym : ∀ b : Fin d → ℝ, symPart (diagonal b) = diagonal b := fun b =>
      symPart_of_isSymm (by rw [Matrix.IsSymm, diagonal_transpose])
    ext B
    constructor
    · rintro ⟨b, rfl, hb⟩
      refine ⟨⟨b, rfl⟩, ?_⟩
      change (diagonal b).trace ≤ ((d : ℝ) + α) * lamMin (symPart (diagonal b))
      rwa [hsym, lamMin_diagonal, trace_diagonal]
    · rintro ⟨⟨b, rfl⟩, hb⟩
      refine ⟨b, rfl, ?_⟩
      have hb' : (diagonal b).trace ≤ ((d : ℝ) + α) * lamMin (symPart (diagonal b)) := hb
      rwa [hsym, lamMin_diagonal, trace_diagonal] at hb'
  · have hpd : ∀ t : Fin d → ℝ, (∀ i, 0 < t i) → (diagonal fun i => t i ^ 2).PosDef := fun t ht =>
      posDef_diagonal_iff.2 fun i => pow_pos (ht i) 2
    set u : Fin d → ℝ := fun i => s' i / s i with hu
    have hupos : ∀ i, 0 < u i := fun i => div_pos (hs' i) (hs i)
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := u)
    have hmin : ∀ i, u i₀ ≤ u i := fun i => hi₀ ▸ ciInf_le (Finite.bddBelow_range u) i
    have hinf2 : (⨅ i, u i ^ 2) = u i₀ ^ 2 := by
      refine le_antisymm (ciInf_le (Finite.bddBelow_range _) i₀) (le_ciInf fun i => ?_)
      exact pow_le_pow_left₀ (hupos i₀).le (hmin i) 2
    rw [stablePlusLE_iff_of_posDef hα0 hα2 (hpd s hs) (hpd s' hs')]
    have hstep : stableLE α (diagonal fun i => s i ^ 2) (diagonal fun i => s' i ^ 2) ↔
        (diagonal fun i => u i ^ 2).det ≤ lamMin (diagonal fun i => u i ^ 2) ^ ((d : ℝ) + α) := by
      constructor
      · rintro ⟨-, -, -, h⟩
        rwa [relStep_diagonal_sq hs] at h
      · intro h
        refine ⟨hpd s hs, hpd s' hs', ?_, ?_⟩ <;> rw [relStep_diagonal_sq hs]
        · exact hpd u hupos
        · exact h
    rw [hstep, det_diagonal, lamMin_diagonal, hinf2, ← hi₀]
    have hprod : (∏ i, u i ^ 2) = (∏ i, u i) ^ 2 := Finset.prod_pow _ _ _
    have hP : 0 ≤ ∏ i, u i := Finset.prod_nonneg fun i _ => (hupos i).le
    have hpow : (u i₀ ^ 2) ^ ((d : ℝ) + α) = (u i₀ ^ ((d : ℝ) + α)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hupos i₀).le, ← Real.rpow_natCast (u i₀ ^ _),
        ← Real.rpow_mul (hupos i₀).le]
      ring_nf
    rw [hprod, hpow]
    exact pow_le_pow_iff_left₀ hP (Real.rpow_nonneg (hupos i₀).le _) two_ne_zero

/-! ## Clause (2), on the frame's shapes -/

/-- **`prop:diagonal-stable-order-families`(2)**, on the frame's shapes: the kernels from the origin
of a `(D₊(d), ≤_α)`-cascade family are `μ_{D_s²} = (D_s)_*μ_I` on the orbit of `I`, with
`μ_I ≠ δ₀` `B`-self-decomposable for every `B ∈ 𝒟_α`; in particular self-decomposable. -/
theorem diagonal_stable_frame (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (diagPosSet d) (stablePlusLE α) μ) :
    (∀ s : Fin d → ℝ, (∀ i, 0 < s i) →
      μ 0 (diagonal fun i => s i ^ 2) = push (diagonal s) (μ 0 1)) ∧
      μ 0 1 ≠ Measure.dirac 0 ∧ (∀ B ∈ diagStableSet d α, IsBSelfDecomposable B (μ 0 1)) ∧
      IsSelfDecomposable (μ 0 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdα : 0 ≤ (d : ℝ) + α := by positivity
  have hdatum := diagonal_stable_datum hd hα0 hα2
  have hμr : IsGWCascadeFamily (diagPosSet d) rayLE μ :=
    gw_family_restrict_of_le subset_rfl (fun S S' _ _ h => h.elim Or.inl fun h => Or.inr (Or.inl h))
      μ hμ
  obtain ⟨hframe, hsd, hne⟩ := (diagonal_ray_frame hd1).1 μ hμr
  refine ⟨hframe, hne, ?_, hsd⟩
  rintro B ⟨b, rfl, hb⟩
  rw [isBSelfDecomposable_iff]
  intro t ht
  set u : Fin d → ℝ := fun i => Real.exp (t * b i) with hu
  have hupos : ∀ i, 0 < u i := fun i => Real.exp_pos _
  have hone : ∀ i : Fin d, (0 : ℝ) < (fun _ => (1 : ℝ)) i := fun _ => one_pos
  have h1 : (diagonal fun i => ((fun _ => (1 : ℝ)) i) ^ 2 : Mat d) = 1 := by
    simp [diagonal_one]
  /- The frame step `I ≤_α D_u²`. -/
  have hstep : stablePlusLE α (1 : Mat d) (diagonal fun i => u i ^ 2) := by
    have h := (hdatum.2.2 (fun _ => 1) u hone hupos).2
    rw [h1] at h
    apply h
    simp only [div_one]
    have hinf : Real.exp (t * ⨅ i, b i) ≤ ⨅ i, u i :=
      le_ciInf fun i => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
        (ciInf_le (Finite.bddBelow_range b) i) ht.le)
    calc ∏ i, u i = Real.exp (t * ∑ i, b i) := by
          rw [hu, ← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (t * ⨅ i, b i) ^ ((d : ℝ) + α) := by
          rw [← Real.exp_mul]
          apply Real.exp_le_exp.2
          nlinarith
      _ ≤ (⨅ i, u i) ^ ((d : ℝ) + α) :=
          Real.rpow_le_rpow (Real.exp_pos _).le hinf hdα
  have hD := (hupos)
  have hcasc := hμ.cascade 0 1 (diagonal fun i => u i ^ 2) PosSemidef.zero PosSemidef.one
    (PosSemidef.diagonal fun i => sq_nonneg _) (Or.inl rfl) hstep
  rw [hframe u hupos] at hcasc
  /- Apply `e^{-tB} = D_u⁻¹`. -/
  have hexp : mexp (-t • diagonal b) = diagonal fun i => (u i)⁻¹ := by
    rw [← diagonal_smul, mexp_diagonal]
    congr 1
    funext i
    simp [hu, Real.exp_neg]
  have hDD : (diagonal fun i => (u i)⁻¹) * diagonal u = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hupos i).ne'
  haveI := hμ.isProbability (1, diagonal fun i => u i ^ 2)
    ⟨PosSemidef.one, PosSemidef.diagonal fun i => sq_nonneg _, hstep⟩
  haveI := hμ.isProbability (0, 1) ⟨PosSemidef.zero, PosSemidef.one, Or.inl rfl⟩
  refine ⟨push (mexp (-t • diagonal b)) (μ 1 (diagonal fun i => u i ^ 2)), inferInstance, ?_⟩
  have h := congrArg (push (mexp (-t • diagonal b))) hcasc
  rw [hexp, push_push, hDD, push_one, push_conv] at h
  rw [hexp]
  conv_rhs => rw [Measure.conv_comm]
  exact h


/-! ## Clause (3), two sources of families -/

/-- **`prop:diagonal-stable-order-families`(3)**, two sources of families: (a) for self-decomposable
`ν₁, …, ν_d` on `ℝ`, not all `δ₀`, `Σ ↦ (Δ(Σ)^{1/2})_*(ν₁ ⊗ ⋯ ⊗ ν_d)`; (b) for a profile with
`R(λ) ≥ λ^α`, `Σ ↦ (Σ^{1/2})_*μ_I`, in particular for `μ_I = S_β(I)`, `α ≤ β < 2`: each is the
family of kernels from the origin of a `(D₊(d), ≤_α)`-cascade family. Spends A3(iii) in (b). -/
theorem diagonal_stable_sources (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    (∀ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) →
      (∃ i, ν i ≠ Measure.dirac 0) →
      IsKernelsFromOrigin (diagPosSet d) (stablePlusLE α)
        fun S => push (msqrt (diagPart S)) (prodLaw ν)) ∧
    (∀ K : RadialProfile d, (∀ lam : ℝ, 1 ≤ lam → lam ^ α ≤ dilRatio K.k lam) →
      ∀ μI : Measure (Rd d), IsProfileLaw K μI →
        IsKernelsFromOrigin (diagPosSet d) (stablePlusLE α) (affineOrbit μI)) ∧
    ∀ β : ℝ, α ≤ β → β < 2 → ∀ μ : Measure (Rd d), IsEllipticalStable β 1 μ →
      IsKernelsFromOrigin (diagPosSet d) (stablePlusLE α) (affineOrbit μ) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  refine ⟨fun ν hν hne => ?_, fun K hR μI hμI => ?_, fun β hαβ hβ2 μ hμ => ?_⟩
  · obtain ⟨μ, hμ, hμm⟩ := (diagonal_loewner_products hd1).2 ν hν hne
    exact ⟨μ, gw_family_restrict_of_le subset_rfl
      (fun S S' hS hS' h => stablePlusLE_loewner hα0 hα2 hS hS' h) μ hμ, hμm⟩
  · obtain ⟨μ, hμ, hμm⟩ := stable_order_gl_row hd hα0 hα2 K hR μI hμI
    exact ⟨μ, gw_family_of_subset diagPosSet_subset_glSet μ hμ, hμm⟩
  · obtain ⟨μ', hμ', hμm⟩ := (stable_order_gl_row_examples hd hα0 hα2).1 β hαβ hβ2 μ hμ
    exact ⟨μ', gw_family_of_subset diagPosSet_subset_glSet μ' hμ', hμm⟩

/-! ## Two coordinates, and `√2^α < 2` -/

/-- `‖t eᵢ‖ = |t|`. -/
theorem norm_smul_ebasis (t : ℝ) (i : Fin d) : ‖t • ebasis i‖ = |t| := by
  simp [ebasis, norm_smul]

/-- `√2^α < 2` for `α < 2`. -/
theorem sqrt_two_rpow_lt_two {α : ℝ} (hα2 : α < 2) : Real.sqrt 2 ^ α < 2 := by
  have h1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  calc Real.sqrt 2 ^ α < Real.sqrt 2 ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt h1 hα2
    _ = 2 := by rw [Real.rpow_two, Real.sq_sqrt (by norm_num)]

/-! ## Clause (4)(b) -/

/-- **`prop:diagonal-stable-order-families`(4)(b)**: `S_α(I)` is not of the form `ν₁ ⊗ ⋯ ⊗ ν_d`, so
the family of (3)(b) with `μ_I = S_α(I)` is the restriction of no `(D₊(d), Loewner)`-family. -/
theorem diagonal_stable_not_product (hd : 2 ≤ d) {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    (μ : Measure (Rd d)) (hμ : IsEllipticalStable α 1 μ) :
    (¬ ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i)) ∧ μ = prodLaw ν) ∧
      ¬ IsKernelsFromOrigin (diagPosSet d) loewnerLE (affineOrbit μ) := by
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hcf := ellipticalStable_one_charFun hμ
  have hnp : ¬ ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i)) ∧ μ = prodLaw ν := by
    rintro ⟨ν, hν, hμν⟩
    have hν0 : ∀ j, charFun (ν j) 0 = 1 := fun j => by haveI := hν j; simp [charFun_zero]
    have hνcf : ∀ i (t : ℝ), charFun (ν i) t = ((Real.exp (-(|t| ^ α)) : ℝ) : ℂ) := by
      intro i t
      have h := hcf (t • ebasis i)
      rw [hμν, charFun_prodLaw _ hν, prod_smul_ebasis (fun j => charFun (ν j)) hν0,
        norm_smul_ebasis] at h
      exact h
    have h := hcf ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1)
    rw [hμν, charFun_prodLaw _ hν, prod_two_ebasis (fun j => charFun (ν j)) hν0 h01, hνcf, hνcf,
      norm_smul_ebasis_add_smul_ebasis h01] at h
    have e1 : |(1 : ℝ)| ^ α = 1 := by simp
    have e2 : Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2) = Real.sqrt 2 := by norm_num
    rw [e1, e2, ← Complex.ofReal_mul, ← Real.exp_add] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    have := sqrt_two_rpow_lt_two hα2
    linarith
  refine ⟨hnp, ?_⟩
  rintro ⟨μ', hμ', hμ'm⟩
  obtain ⟨ν, hν, -, hform⟩ := (diagonal_loewner_products hd1).1 μ' hμ'
  apply hnp
  refine ⟨fun i => dilLine ((1 : Fin d → ℝ) i) (ν i),
    fun i => haveI := (hν i).1; isProbabilityMeasure_dilLine _ _, ?_⟩
  have h1 := hform 1 fun _ => one_pos
  rw [diagonal_one_sq, hμ'm 1 PosSemidef.one, affineOrbit_one] at h1
  exact h1


/-! ## Clause (4)(a), a correlated Gaussian -/

/-- `⟨ω, Eᵢⱼω⟩ = ωᵢωⱼ` for the matrix unit `Eᵢⱼ`. -/
theorem quad_single (i j : Fin d) (ω : Rd d) : quad (Matrix.single i j (1 : ℝ)) ω = ω i * ω j := by
  rw [quad_eq_sum]
  simp [Matrix.single_apply, ite_and]

/-- The coordinates of `a eᵢ + b eⱼ`, `i ≠ j`. -/
theorem two_ebasis_apply_left {i j : Fin d} (hij : i ≠ j) (a b : ℝ) :
    (a • ebasis i + b • ebasis j) i = a := by
  simp [ebasis, hij]

theorem two_ebasis_apply_right {i j : Fin d} (hij : i ≠ j) (a b : ℝ) :
    (a • ebasis i + b • ebasis j) j = b := by
  simp [ebasis, Ne.symm hij]

/-- `D_v(a eᵢ + b eⱼ) = vᵢa eᵢ + vⱼb eⱼ`. -/
theorem lin_diagonal_two (v : Fin d → ℝ) {i j : Fin d} (hij : i ≠ j) (a b : ℝ) :
    lin (diagonal v) (a • ebasis i + b • ebasis j) =
      (v i * a) • ebasis i + (v j * b) • ebasis j := by
  ext k
  rw [lin_diagonal_apply]
  by_cases hki : k = i
  · subst hki; rw [two_ebasis_apply_left hij, two_ebasis_apply_left hij]
  · by_cases hkj : k = j
    · subst hkj; rw [two_ebasis_apply_right hij, two_ebasis_apply_right hij]
    · simp [ebasis, hki, hkj]

/-- **`prop:diagonal-stable-order-families`(4)(a)**: for `|r| < 1` with
`r² > 4(1+α)/(2+α)²` and `Θ_r` the correlation matrix with `(Θ_r)₁₂ = r`, `N(0, Θ_r)` is
self-decomposable and not `B`-self-decomposable for `B := I + αe₁e₁ᵀ ∈ 𝒟_α`; so the
`(D₊(d), rays)`-family of `prop:diagonal-ray-families`(2) with `μ_I = N(0, Θ_r)` is the restriction
of no `(D₊(d), ≤_α)`-family. -/
theorem diagonal_stable_gaussian_excluded (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (r : ℝ) (hr1 : |r| < 1) (hr : 4 * (1 + α) / (2 + α) ^ 2 < r ^ 2) :
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    let Θ : Mat d := 1 + r • (Matrix.single i0 i1 1 + Matrix.single i1 i0 1)
    let B : Mat d := diagonal fun i => if i = i0 then 1 + α else 1
    Θ ∈ corrSet d ∧ IsSelfDecomposable (multivariateGaussian 0 Θ) ∧ B ∈ diagStableSet d α ∧
      ¬ IsBSelfDecomposable B (multivariateGaussian 0 Θ) ∧
      ¬ IsKernelsFromOrigin (diagPosSet d) (stablePlusLE α)
          fun S => push (msqrt (diagPart S)) (multivariateGaussian 0 Θ) := by
  intro i0 i1 Θ B
  haveI : NeZero d := ⟨by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hα1 : 0 < 1 + α := by linarith
  /- The quadratic form of `Θ_r`. -/
  have hq : ∀ ω : Rd d, quad Θ ω = ‖ω‖ ^ 2 + 2 * r * (ω i0 * ω i1) := by
    intro ω
    simp only [Θ]
    rw [quad_add, quad_smul, quad_one, quad_add, quad_single, quad_single]
    ring
  have hq2 : ∀ a b : ℝ,
      quad Θ (a • ebasis i0 + b • ebasis i1) = a ^ 2 + b ^ 2 + 2 * r * (a * b) := by
    intro a b
    rw [hq, norm_smul_ebasis_add_smul_ebasis h01, Real.sq_sqrt (by positivity),
      two_ebasis_apply_left h01, two_ebasis_apply_right h01]
  /- `Θ_r ∈ Corr(d)`. -/
  have hsymm : Θ.IsSymm := by
    simp only [Θ, Matrix.IsSymm, transpose_add, transpose_one, transpose_smul,
      Matrix.transpose_single]
    rw [add_comm (Matrix.single i1 i0 (1 : ℝ))]
  have hdiag : ∀ i, Θ i i = 1 := by
    intro i
    have h1 : ¬(i0 = i ∧ i1 = i) := fun h => h01 (h.1.trans h.2.symm)
    have h2 : ¬(i1 = i ∧ i0 = i) := fun h => h01 (h.2.trans h.1.symm)
    simp only [Θ, Matrix.add_apply, Matrix.smul_apply, one_apply_eq, Matrix.single_apply,
      if_neg h1, if_neg h2, add_zero, smul_zero]
  have hpd : Θ.PosDef := by
    refine posDef_of_quad_sphere hsymm fun x hx => ?_
    have hn : ‖x‖ = 1 := by simpa using hx
    have hsum : x i0 ^ 2 + x i1 ^ 2 ≤ 1 := by
      have h := quad_one_eq_sum x
      rw [quad_one, hn, one_pow] at h
      rw [h]
      calc x i0 ^ 2 + x i1 ^ 2 = ∑ i ∈ {i0, i1}, x i ^ 2 := by rw [Finset.sum_pair h01]
        _ ≤ ∑ i, x i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun i _ _ => sq_nonneg _
    rw [hq, hn]
    obtain ⟨hr1l, hr1r⟩ := abs_lt.1 hr1
    rcases le_total 0 r with hr0 | hr0
    · nlinarith [mul_nonneg hr0 (sq_nonneg (x i0 + x i1))]
    · nlinarith [mul_nonneg (neg_nonneg.2 hr0) (sq_nonneg (x i0 - x i1))]
  have hΘ : Θ ∈ corrSet d := ⟨hpd, hdiag⟩
  /- `r ≠ 0`, so `Θ_r` is not diagonal and `N(0, Θ_r)` is self-decomposable. -/
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : 0 < 4 * (1 + α) / (2 + α) ^ 2 := by positivity
    simp at hr
    linarith
  have hnd : ¬ Θ.IsDiag := fun h => by
    have h' : Θ i0 i1 = 0 := h h01
    have : Θ i0 i1 = r := by
      have h1 : ¬(i1 = i0 ∧ i0 = i1) := fun h => h01 h.2
      simp only [Θ, Matrix.add_apply, Matrix.smul_apply, one_apply_ne h01, Matrix.single_apply,
        if_neg h1, add_zero, smul_eq_mul, zero_add]
      simp
    rw [this] at h'
    exact hr0 h'
  have hsd := (diagonal_rays_no_product hd Θ hΘ hnd).1
  /- `B ∈ 𝒟_α`. -/
  set b : Fin d → ℝ := fun i => if i = i0 then 1 + α else 1 with hb
  have hbinf : 1 ≤ ⨅ i, b i := le_ciInf fun i => by
    simp only [hb]; split_ifs <;> linarith
  have hB : B ∈ diagStableSet d α := by
    refine ⟨b, rfl, ?_⟩
    have hsum : ∑ i, b i = d + α := by
      have : ∀ i, b i = 1 + if i = i0 then α else 0 := fun i => by
        simp only [hb]; split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    have : (0 : ℝ) ≤ d + α := by positivity
    nlinarith
  /- `N(0, Θ_r)` is not `B`-self-decomposable: the derivative at `t = 0` along one vector. -/
  set N := multivariateGaussian 0 Θ with hN
  have hNcf : ∀ ω : Rd d, charFun N ω = ((Real.exp (-(quad Θ ω / 2)) : ℝ) : ℂ) :=
    charFun_multivariateGaussian_zero hpd.posSemidef
  have hnotB : ¬ IsBSelfDecomposable B N := by
    rw [isBSelfDecomposable_iff]
    intro hBsd
    set x : ℝ := -(r * (2 + α)) / (2 * (1 + α)) with hx
    set ω₀ : Rd d := x • ebasis i0 + (1 : ℝ) • ebasis i1 with hω₀
    /- `t ↦ ⟨e^{-tB}ω₀, Θ e^{-tB}ω₀⟩` is largest at `t = 0`. -/
    have hE : ∀ t : ℝ, mexp (-t • B) = diagonal fun i => Real.exp (-t * b i) := by
      intro t
      simp only [B]
      rw [← diagonal_smul, mexp_diagonal]
      rfl
    have hle : ∀ t : ℝ, 0 < t →
        quad Θ (lin (diagonal fun i => Real.exp (-t * b i)) ω₀) ≤ quad Θ ω₀ := by
      intro t ht
      obtain ⟨ρ, hρ, hfac⟩ := hBsd t ht
      have h := congrArg (fun m => charFun m ω₀) hfac
      rw [charFun_conv, push, charFun_map_lin, hE, diagonal_transpose, hNcf, hNcf] at h
      have hn := congrArg (fun z : ℂ => ‖z‖) h
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hn
      have h2 : Real.exp (-(quad Θ ω₀ / 2)) ≤
          Real.exp (-(quad Θ (lin (diagonal fun i => Real.exp (-t * b i)) ω₀) / 2)) := by
        rw [hn]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_charFun_le_one _)
      have := Real.exp_le_exp.1 h2
      linarith
    set g : ℝ → ℝ := fun t => (Real.exp (-t * (1 + α)) * x) ^ 2 + (Real.exp (-t) * 1) ^ 2 +
      2 * r * ((Real.exp (-t * (1 + α)) * x) * (Real.exp (-t) * 1)) with hg
    have hgq : ∀ t : ℝ, g t = quad Θ (lin (diagonal fun i => Real.exp (-t * b i)) ω₀) := by
      intro t
      rw [hω₀, lin_diagonal_two _ h01, hq2]
      have hb0 : b i0 = 1 + α := by simp [hb]
      have hb1 : b i1 = 1 := by simp [hb, Ne.symm h01]
      rw [hb0, hb1, mul_one (-t)]
    have hg0 : g 0 = quad Θ ω₀ := by
      rw [hω₀, hq2]
      simp [hg]
    have he1 : HasDerivAt (fun t : ℝ => Real.exp (-t * (1 + α))) (-(1 + α)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).neg.mul_const (1 + α)).exp
      simpa using this
    have he2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).neg.exp
      simpa using this
    have hgd : HasDerivAt g (-(2 * (1 + α)) * x ^ 2 - 2 - 2 * r * x * (2 + α)) 0 := by
      have h1 := (he1.mul_const x).pow 2
      have h2 := (he2.mul_const 1).pow 2
      have h3 := ((he1.mul_const x).mul (he2.mul_const 1)).const_mul (2 * r)
      have := (h1.add h2).add h3
      refine this.congr_deriv ?_
      simp
      ring
    have hneg := deriv_nonpos_of_right_max hgd fun t ht => by rw [hgq, hg0]; exact hle t ht
    have hval : -(2 * (1 + α)) * x ^ 2 - 2 - 2 * r * x * (2 + α) =
        r ^ 2 * (2 + α) ^ 2 / (2 * (1 + α)) - 2 := by
      rw [hx]
      field_simp
      ring
    rw [hval] at hneg
    have h4 : 4 * (1 + α) < r ^ 2 * (2 + α) ^ 2 := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 + α) ^ 2)).1 hr
      linarith
    have h5 : 2 < r ^ 2 * (2 + α) ^ 2 / (2 * (1 + α)) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    linarith
  refine ⟨hΘ, hsd, hB, hnotB, ?_⟩
  rintro ⟨μ, hμ, hμm⟩
  have hframe := (diagonal_stable_frame hd hα0 hα2 μ hμ).2.2.1 B hB
  rw [hμm 1 PosSemidef.one] at hframe
  dsimp only at hframe
  rw [msqrt_diagPart_one, push_one] at hframe
  exact hnotB hframe


/-! ## Clause (4)(c), a mixed family -/

/-- **`σ_α` is self-decomposable**: `e^{-|τ|^α} = e^{-|cτ|^α} e^{-(1-c^α)|τ|^α}`, the second factor
the transform of the image of `σ_α` under `τ ↦ (1-c^α)^{1/α}τ`. -/
theorem selfDecomposable_stableLine {α : ℝ} (hα0 : 0 < α) {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hσ : ∀ τ : ℝ, charFun σ τ = ((Real.exp (-|τ| ^ α) : ℝ) : ℂ)) : IsSelfDecomposable σ := by
  rw [isSelfDecomposable_iff_charFun]
  intro c hc0 hc1
  have hcα : c ^ α < 1 := Real.rpow_lt_one hc0.le hc1 hα0
  set a : ℝ := (1 - c ^ α) ^ (1 / α) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by linarith) _
  refine ⟨dilLine a σ, isProbabilityMeasure_dilLine a σ, fun ξ => ?_⟩
  rw [charFun_dilLine, hσ, hσ, hσ, smul_eq_mul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  have haα : a ^ α = 1 - c ^ α := by
    rw [ha, ← Real.rpow_mul (by linarith), one_div_mul_cancel hα0.ne', Real.rpow_one]
  rw [abs_mul, abs_mul, abs_of_pos hc0, abs_of_nonneg ha0,
    Real.mul_rpow hc0.le (abs_nonneg _), Real.mul_rpow ha0 (abs_nonneg _), haα]
  ring

/-- **`S_α(I)` is rotation invariant**: its transform `e^{-|ω|^α}` is radial. -/
theorem rotationInvariant_ellipticalStable {α : ℝ} {σ : Measure (Rd d)}
    (hσ : IsEllipticalStable α 1 σ) : IsRotationInvariant σ := by
  haveI := hσ.1
  intro Q hQ
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  refine eq_of_charFun_eq fun ω => ?_
  rw [push, charFun_map_lin, ellipticalStable_one_charFun hσ, ellipticalStable_one_charFun hσ]
  have hn : ‖lin Qᵀ ω‖ = ‖ω‖ := by
    have h1 := quad_act Q 1 ω
    rw [act, Matrix.mul_one, hQQ, quad_one, quad_one] at h1
    have := congrArg Real.sqrt h1
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    exact this.symm
  rw [hn]

/-- Kernels from the origin for a group are kernels from the origin for a subgroup. -/
theorem IsOriginKernels.mono {G G' : Set (Mat d)} (hG : G ⊆ G') {m : Mat d → Measure (Rd d)}
    (h : IsOriginKernels G' m) : IsOriginKernels G m :=
  ⟨h.isProbability, h.zero, h.one_ne, fun A hA S hS => h.covariant A (hG hA) S hS, h.continuous⟩

/-- **The convolution of two maps with (a)–(c)** has (a)–(c), when its value at `I` is not `δ₀`. -/
theorem IsOriginKernels.conv {G : Set (Mat d)} {m₁ m₂ : Mat d → Measure (Rd d)}
    (h₁ : IsOriginKernels G m₁) (h₂ : IsOriginKernels G m₂)
    (hne : m₁ 1 ∗ m₂ 1 ≠ Measure.dirac 0) : IsOriginKernels G fun S => m₁ S ∗ m₂ S := by
  refine ⟨fun S hS => ?_, ?_, hne, fun A hA S hS => ?_, fun ω => ?_⟩
  · haveI := h₁.isProbability S hS
    haveI := h₂.isProbability S hS
    infer_instance
  · rw [h₁.zero, h₂.zero, Measure.dirac_zero_conv]
  · haveI := h₁.isProbability S hS
    haveI := h₂.isProbability S hS
    rw [push_conv, h₁.covariant A hA S hS, h₂.covariant A hA S hS]
  · refine ((h₁.continuous ω).mul (h₂.continuous ω)).congr fun S hS => ?_
    haveI := h₁.isProbability S hS
    haveI := h₂.isProbability S hS
    rw [charFun_conv]
    rfl

/-- **`prop:diagonal-stable-order-families`(4)(c)**: with `σ_α` the law on `ℝ` with transform
`e^{-|τ|^α}`, `Σ ↦ (Σ^{1/2})_*S_α(I) * (Δ(Σ)^{1/2})_*(σ_α ⊗ ⋯ ⊗ σ_α)` is the family of kernels from
the origin of a `(D₊(d), ≤_α)`-cascade family that is the restriction neither of a
`(GL(d), ≤_α)`-family nor of a `(D₊(d), Loewner)`-family. Spends A3(iii). -/
theorem diagonal_stable_mixed (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (σα : Measure ℝ) [IsProbabilityMeasure σα]
    (hσα : ∀ τ : ℝ, charFun σα τ = ((Real.exp (-|τ| ^ α) : ℝ) : ℂ)) (μ : Measure (Rd d))
    (hμ : IsEllipticalStable α 1 μ) :
    let m : Mat d → Measure (Rd d) := fun S =>
      affineOrbit μ S ∗ push (msqrt (diagPart S)) (prodLaw fun _ => σα)
    IsKernelsFromOrigin (diagPosSet d) (stablePlusLE α) m ∧
      ¬ IsKernelsFromOrigin (glSet d) (stablePlusLE α) m ∧
      ¬ IsKernelsFromOrigin (diagPosSet d) loewnerLE m := by
  intro m
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := hμ.1
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set P : Measure (Rd d) := prodLaw fun _ => σα with hP
  have hσprob : ∀ _ : Fin d, IsProbabilityMeasure σα := fun _ => inferInstance
  haveI hPprob : IsProbabilityMeasure P := isProbabilityMeasure_prodLaw _ hσprob
  /- The transforms. -/
  set f : ℝ → ℂ := fun τ => ((Real.exp (-|τ| ^ α) : ℝ) : ℂ) with hf
  have hf0 : f 0 = 1 := by simp [hf, Real.zero_rpow hα0.ne']
  have hfne : ∀ τ, f τ ≠ 0 := fun τ => by
    simp only [hf]; exact_mod_cast (Real.exp_pos _).ne'
  have hμcf : ∀ ω, charFun μ ω = ((Real.exp (-‖ω‖ ^ α) : ℝ) : ℂ) :=
    ellipticalStable_one_charFun hμ
  have hPcf : ∀ ω : Rd d, charFun P ω = ∏ j, f (ω j) := fun ω => by
    rw [hP, charFun_prodLaw _ hσprob]; exact Finset.prod_congr rfl fun j _ => hσα _
  have hm1 : m 1 = μ ∗ P := by
    simp only [m]
    rw [affineOrbit_one, msqrt_diagPart_one, push_one]
  have hm1cf : ∀ ω, charFun (m 1) ω = ((Real.exp (-‖ω‖ ^ α) : ℝ) : ℂ) * ∏ j, f (ω j) := by
    intro ω
    rw [hm1, charFun_conv, hμcf, hPcf]
  have hfe : ∀ (i : Fin d) (t : ℝ), ∏ j, f ((t • ebasis i) j) = f t := fun i t =>
    prod_smul_ebasis (fun _ => f) (fun _ => hf0) t i
  have hfab : ∀ a b : ℝ, ∏ j, f ((a • ebasis i0 + b • ebasis i1) j) = f a * f b := fun a b =>
    prod_two_ebasis (fun _ => f) (fun _ => hf0) h01 a b
  have hone : ‖(1 : ℝ) • ebasis i0‖ = 1 := by rw [norm_smul_ebasis, abs_one]
  /- `μ ≠ δ₀`, `P ≠ δ₀` and `m_I ≠ δ₀`, read at `e₁`. -/
  have hdir : ∀ ν : Measure (Rd d), charFun ν ((1 : ℝ) • ebasis i0) ≠ 1 → ν ≠ Measure.dirac 0 := by
    rintro ν h rfl
    exact h (by rw [charFun_dirac]; simp)
  have hne1 : ∀ x : ℝ, x ≠ 0 → ((Real.exp x : ℝ) : ℂ) ≠ 1 := fun x hx h =>
    hx (Real.exp_eq_one_iff x |>.1 (by exact_mod_cast h))
  have hexp1 : ((Real.exp (-1) : ℝ) : ℂ) ≠ 1 := hne1 (-1) (by norm_num)
  have hμne : μ ≠ Measure.dirac 0 := hdir μ (by
    rw [hμcf, hone, Real.one_rpow]; exact hexp1)
  have hPne : P ≠ Measure.dirac 0 := hdir P (by
    rw [hPcf, hfe]; simp only [hf, abs_one, Real.one_rpow]; exact hexp1)
  have hm1ne : μ ∗ P ≠ Measure.dirac 0 := hdir _ (by
    rw [← hm1, hm1cf, hone, hfe]
    simp only [hf, abs_one, Real.one_rpow]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    exact hne1 _ (by norm_num))
  have hσne : σα ≠ Measure.dirac 0 := by
    intro h
    have h1 := hσα 1
    rw [h, charFun_dirac] at h1
    simp only [abs_one, Real.one_rpow] at h1
    exact hexp1 (by rw [← h1]; simp)
  have hrot := rotationInvariant_ellipticalStable hμ
  /- The family, through `lem:gw-kernels-from-origin`(3). -/
  have hW := (diagonal_stable_datum hd hα0 hα2).1
  have hm : IsOriginKernels (diagPosSet d) m := by
    have h1 := (affineOrbit_isOriginKernels hrot hμne).mono diagPosSet_subset_glSet
    have h2 := diagFrame_isOriginKernels P hPne
    refine IsOriginKernels.conv h1 h2 ?_
    rw [affineOrbit_one, msqrt_diagPart_one, push_one]
    exact hm1ne
  have hz : HasNoZeros m := by
    intro S hS ω
    simp only [m]
    rw [charFun_conv, affineOrbit, push, charFun_map_lin, push, charFun_map_lin, hμcf, hPcf]
    exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne')
      (Finset.prod_ne_zero_iff.2 fun j _ => hfne _)
  have hinc : HasIncrements (stablePlusLE α) m := by
    intro S S' hS hS' h
    obtain ⟨μa, hμa, hma⟩ := (diagonal_stable_sources hd hα0 hα2).2.2 α le_rfl hα2 μ hμ
    obtain ⟨μb, hμb, hmb⟩ := (diagonal_stable_sources hd hα0 hα2).1 (fun _ => σα)
      (fun _ => ⟨inferInstance, selfDecomposable_stableLine hα0 hσα⟩)
      ⟨i0, hσne⟩
    obtain ⟨hp1, hc1⟩ := (gw_kernels_from_origin hW μa hμa).2 S S' hS hS' h
    obtain ⟨hp2, hc2⟩ := (gw_kernels_from_origin hW μb hμb).2 S S' hS hS' h
    rw [hma S hS, hma S' hS'] at hc1
    rw [hmb S hS, hmb S' hS'] at hc2
    dsimp only at hc1 hc2
    haveI := hp1
    haveI := hp2
    refine ⟨μa S S' ∗ μb S S', inferInstance, ?_⟩
    haveI := hm.isProbability S' hS'
    haveI := hm.isProbability S hS
    refine eq_of_charFun_eq fun ω => ?_
    simp only [m]
    rw [charFun_conv, charFun_conv, charFun_conv, hc1, hc2, charFun_conv, charFun_conv,
      charFun_conv]
    ring
  refine ⟨(gw_kernels_from_origin_converse hW m hm hz hinc).1, ?_, ?_⟩
  · /- Not rotation invariant at `I`. -/
    rintro ⟨μ', hμ', hμ'm⟩
    obtain ⟨-, hrot', -⟩ := gl_kernels_of_rays
      (fun S S' _ _ h => h.elim Or.inl fun h => Or.inr (Or.inl h)) hμ'
    rw [hμ'm 1 PosSemidef.one] at hrot'
    set c : ℝ := (Real.sqrt 2)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hcn : ‖c • ebasis i0 + c • ebasis i1‖ = ‖(1 : ℝ) • ebasis i0‖ := by
      rw [norm_smul_ebasis_add_smul_ebasis h01, hone, hc, inv_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have h := charFun_eq_of_norm_eq hrot' hcn
    rw [hm1cf, hm1cf, hcn, hone, hfab, hfe] at h
    simp only [hf, abs_one, Real.one_rpow, abs_of_pos hc0] at h
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    have hcα : c ^ α = (Real.sqrt 2 ^ α)⁻¹ := by
      rw [hc, Real.inv_rpow (Real.sqrt_nonneg _)]
    have hlt := sqrt_two_rpow_lt_two hα2
    have hpos : 0 < Real.sqrt 2 ^ α := Real.rpow_pos_of_pos (by positivity) _
    rw [hcα] at h2
    have : (1 / 2 : ℝ) < (Real.sqrt 2 ^ α)⁻¹ := by
      rw [one_div]; exact (inv_lt_inv₀ two_pos hpos).2 hlt
    linarith
  · /- Not a product at `I`. -/
    rintro ⟨μ', hμ', hμ'm⟩
    obtain ⟨ν, hν, -, hform⟩ := (diagonal_loewner_products hd1).1 μ' hμ'
    have h1 := hform 1 fun _ => one_pos
    rw [diagonal_one_sq, hμ'm 1 PosSemidef.one] at h1
    have hν' : ∀ i, IsProbabilityMeasure (dilLine ((1 : Fin d → ℝ) i) (ν i)) := fun i =>
      haveI := (hν i).1; isProbabilityMeasure_dilLine _ _
    have hν0 : ∀ j, charFun (dilLine ((1 : Fin d → ℝ) j) (ν j)) 0 = 1 := fun j => by
      haveI := hν' j; simp [charFun_zero]
    have hνcf : ∀ i (t : ℝ), charFun (dilLine ((1 : Fin d → ℝ) i) (ν i)) t =
        ((Real.exp (-|t| ^ α) : ℝ) : ℂ) * f t := by
      intro i t
      have h := hm1cf (t • ebasis i)
      rw [h1, charFun_prodLaw _ hν', prod_smul_ebasis _ hν0, norm_smul_ebasis, hfe] at h
      exact h
    have h := hm1cf ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1)
    rw [h1, charFun_prodLaw _ hν', prod_two_ebasis _ hν0 h01, hνcf, hνcf, hfab,
      norm_smul_ebasis_add_smul_ebasis h01] at h
    have e2 : Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2) = Real.sqrt 2 := by norm_num
    simp only [hf, abs_one, Real.one_rpow, e2] at h
    simp only [← Complex.ofReal_mul, ← Real.exp_add] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    have := sqrt_two_rpow_lt_two hα2
    linarith

end AffineHemigroup
