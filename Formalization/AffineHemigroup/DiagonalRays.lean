/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityRays
import AffineHemigroup.FixedFrame
import AffineHemigroup.LogOrbitRays
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# `prop:diagonal-ray-families`: the cell (diagonal, rays)

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:diagonal-ray-families`. Wave 2,
group E, Q-0281. (1) the parameter set: `D₊(d)` is a closed subgroup, the factorization
`Σ = Δ(Σ)^{1/2} Θ Δ(Σ)^{1/2}` with `Θ ∈ Corr(d)`, `Corr(d)` relatively open (through the tube lemma
on the unit sphere), the dimension `d(d-1)/2`; (2) the families on the frame's shapes; (3) the
Loewner order gives products (through `prop:fixed-frame-families`); (4) a correlated Gaussian is not
a product; (5) off the frame's shapes, through `Stab(μ_I) = O(d)`.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix
open scoped Topology MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Diagonal matrices -/

/-- `(diag w)^{1/2} = diag(√w)` for `w ≥ 0`. -/
theorem msqrt_diagonal {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) :
    msqrt (diagonal w) = diagonal fun i => Real.sqrt (w i) := by
  refine CFC.sqrt_unique ?_ (nonneg_of_posSemidef (PosSemidef.diagonal fun i => Real.sqrt_nonneg _))
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (hw i)

/-- `Δ(Σ)^{1/2} = diag(√Σᵢᵢ)` for `Σ ∈ PSD(d)`. -/
theorem msqrt_diagPart {S : Mat d} (hS : S.PosSemidef) :
    msqrt (diagPart S) = diagonal fun i => Real.sqrt (S i i) :=
  msqrt_diagonal fun _ => hS.diag_nonneg

/-- `D₊(d)` lies in `GL(d)`. -/
theorem diagPosSet_subset_glSet : diagPosSet d ⊆ glSet d := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [glSet, mem_setOf_eq, det_diagonal]
  exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (hv i).ne')

/-- **`D₊(d)` is a closed subgroup of `GL(d)` containing the dilations.** -/
theorem diagPosSet_isClosedSubgroupGL :
    IsClosedSubgroupGL (diagPosSet d) ∧ ∀ c : ℝ, 0 < c → c • (1 : Mat d) ∈ diagPosSet d := by
  refine ⟨⟨diagPosSet_subset_glSet, ⟨1, fun _ => one_pos, diagonal_one.symm⟩, ?_, ?_, ?_⟩,
    fun c hc => ⟨fun _ => c, fun _ => hc, by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]⟩⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact ⟨v * w, fun i => mul_pos (hv i) (hw i), diagonal_mul_diagonal' v w⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨v⁻¹, fun i => inv_pos.2 (hv i), ?_⟩
    rw [inv_diagonal]
    congr 1
    have hu : IsUnit v := Pi.isUnit_iff.2 fun i => (hv i).ne'.isUnit
    funext i
    simp [Ring.inverse, hu]
  · intro A hA hdet
    set C : Set (Mat d) := {M | ∀ i j, i ≠ j → M i j = 0} ∩ {M | ∀ i, 0 ≤ M i i} with hC
    have hCc : IsClosed C := by
      refine IsClosed.inter ?_ ?_
      · simp only [setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq (continuous_id.matrix_elem i j) continuous_const
      · simp only [setOf_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_id.matrix_elem i i)
    have hsub : diagPosSet d ⊆ C := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨fun i j hij => diagonal_apply_ne _ hij, fun i => by simp [(hv i).le]⟩
    obtain ⟨hoff, hdiag⟩ := closure_minimal hsub hCc hA
    have hAd : A = diagonal fun i => A i i := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · rw [hoff i j h, diagonal_apply_ne _ h]
    refine ⟨fun i => A i i, fun i => lt_of_le_of_ne (hdiag i) fun h0 => ?_, hAd⟩
    have := isUnit_iff_ne_zero.1 hdet
    rw [hAd, det_diagonal] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h0.symm)

/-- `(D₊(d), W)` is a wedge datum. -/
theorem diagPosSet_isWedgeDatum_ray : IsWedgeDatum (diagPosSet d) rayLE :=
  isWedgeDatum_ray diagPosSet_isClosedSubgroupGL.1 diagPosSet_isClosedSubgroupGL.2

/-- `D Σ D` for diagonal `D`: `(DΣD)ᵢⱼ = vᵢΣᵢⱼvⱼ`. -/
theorem act_diagonal_apply (v : Fin d → ℝ) (S : Mat d) (i j : Fin d) :
    act (diagonal v) S i j = v i * S i j * v j := by
  rw [act, diagonal_transpose, mul_diagonal, diagonal_mul]

/-! ## `Corr(d)` -/

/-- A symmetric matrix whose quadratic form is positive on the unit sphere is positive definite. -/
theorem posDef_of_quad_sphere {R : Mat d} (hR : R.IsSymm)
    (h : ∀ x ∈ Metric.sphere (0 : Rd d) 1, 0 < quad R x) : R.PosDef := by
  have hRh : R.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hR
  refine PosDef.of_dotProduct_mulVec_pos hRh fun x hx => ?_
  set y : Rd d := WithLp.toLp 2 x with hy
  have hy0 : y ≠ 0 := fun h0 => hx (by simpa [hy] using congrArg WithLp.ofLp h0)
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have h1 := h (‖y‖⁻¹ • y) (by simp [norm_smul, hn.ne'])
  rw [quad_smul_vec, quad_eq_dotProduct] at h1
  have h2 : 0 < y.ofLp ⬝ᵥ R *ᵥ y.ofLp := pos_of_mul_pos_right h1 (by positivity)
  simpa [hy] using h2

/-- **`Corr(d)` is relatively open**: `Corr(d) = U ∩ {Θ symmetric, Θᵢᵢ = 1}` with `U` the open set
of matrices whose quadratic form is positive on the unit sphere (the tube lemma). -/
theorem corrSet_eq_open_inter :
    ∃ U : Set (Mat d), IsOpen U ∧ corrSet d = U ∩ unitDiagSym d := by
  set K : Set (Rd d) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  refine ⟨{R | ∀ x ∈ K, 0 < quad R x}, ?_, ?_⟩
  · refine isOpen_iff_mem_nhds.2 fun R₀ hR₀ => ?_
    have hP : ∀ x ∈ K, ∀ᶠ z : Mat d × Rd d in 𝓝 (R₀, x), 0 < quad z.1 z.2 := by
      intro x hx
      have hcont : Continuous fun z : Mat d × Rd d => quad z.1 z.2 := by
        unfold quad
        exact continuous_snd.inner (by
          have : Continuous fun z : Mat d × Rd d => lin z.1 z.2 := by
            have hl : Continuous fun z : Mat d × Rd d => z.2.ofLp := by fun_prop
            have : (fun z : Mat d × Rd d => lin z.1 z.2) =
                fun z => WithLp.toLp 2 (z.1 *ᵥ z.2.ofLp) := by
              funext z
              apply WithLp.ofLp_injective 2
              rw [ofLp_lin]
            rw [this]
            exact (PiLp.continuous_toLp 2 _).comp (continuous_fst.matrix_mulVec hl)
          exact this)
      exact hcont.continuousAt.eventually (lt_mem_nhds (hR₀ x hx))
    exact hKc.eventually_forall_of_forall_eventually hP
  · ext R
    simp only [corrSet, unitDiagSym, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨hpd, hdiag⟩
      refine ⟨fun x hx => quad_pos hpd (by
        rintro rfl
        rw [hK, mem_sphere_zero_iff_norm, norm_zero] at hx
        exact zero_ne_one hx), ?_, hdiag⟩
      have := hpd.isHermitian
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
    · rintro ⟨hpos, hsym, hdiag⟩
      exact ⟨posDef_of_quad_sphere hsym hpos, hdiag⟩

/-- **The symmetric matrices with zero diagonal**, the direction of the affine space of
`Corr(d)`, as a submodule. -/
def zeroDiagSym (d : ℕ) : Submodule ℝ (Mat d) where
  carrier := {X | X.IsSymm ∧ ∀ i, X i i = 0}
  add_mem' := by
    rintro X Y ⟨hX, hX0⟩ ⟨hY, hY0⟩
    exact ⟨hX.add hY, fun i => by simp [hX0 i, hY0 i]⟩
  zero_mem' := ⟨isSymm_zero, fun _ => rfl⟩
  smul_mem' := by
    rintro c X ⟨hX, hX0⟩
    exact ⟨hX.smul c, fun i => by simp [hX0 i]⟩

/-- The strictly upper triangular index pairs. -/
abbrev upperPairs (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

/-- `zeroDiagSym d ≃ (upperPairs d → ℝ)`: a symmetric matrix with zero diagonal is its strictly
upper triangular part. -/
noncomputable def zeroDiagSymEquiv (d : ℕ) : zeroDiagSym d ≃ₗ[ℝ] (upperPairs d → ℝ) where
  toFun X p := (X : Mat d) p.1.1 p.1.2
  map_add' X Y := rfl
  map_smul' c X := rfl
  invFun f := ⟨Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then f ⟨(j, i), h'⟩ else 0, by
    refine ⟨?_, fun i => by simp⟩
    ext i j
    simp only [transpose_apply, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp
    · simp [h, not_lt.2 h.le]⟩
  left_inv X := by
    obtain ⟨X, hX, hX0⟩ := X
    apply Subtype.ext
    ext i j
    simp only [of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp [hX0]
    · simp only [not_lt.2 h.le, h, dite_true, dite_false]
      exact (hX.apply i j).symm ▸ rfl
  right_inv f := by
    funext p
    simp [p.2]

/-- `#{(i, j) : i < j} = d(d-1)/2`. -/
theorem card_upperPairs (d : ℕ) : Fintype.card (upperPairs d) = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2).card =
      ∑ j : Fin d, (Finset.univ.filter fun i : Fin d => i < j).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h]
  have h2 : ∀ j : Fin d, (Finset.univ.filter fun i : Fin d => i < j).card = j := by
    intro j
    rw [show (Finset.univ.filter fun i : Fin d => i < j) = Finset.Iio j by ext; simp]
    exact Fin.card_Iio j
  simp only [h2]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) d, Finset.sum_range_id]

/-! ## Clause (1) -/

/-- **`prop:diagonal-ray-families`(1)**, the parameter set: `(D₊(d), W)` is a wedge datum; every
`Σ ∈ PD(d)` has trivial stabilizer in `D₊(d)` and is `DRD` for exactly one pair
`D ∈ D₊(d)`, `Θ ∈ Corr(d)`, namely `D = Δ(Σ)^{1/2}`; `Corr(d)` is a nonempty open subset of the
affine space of symmetric matrices with unit diagonal, whose direction has dimension `d(d-1)/2`;
and the orbit of `I` is the set of positive definite diagonal matrices. -/
theorem diagonal_ray_parameter (_hd : 1 ≤ d) :
    IsWedgeDatum (diagPosSet d) rayLE ∧
      (∀ S : Mat d, S.PosDef → ∀ D ∈ diagPosSet d, act D S = S → D = 1) ∧
      (∀ S : Mat d, S.PosDef →
        ∃! DR : Mat d × Mat d, DR.1 ∈ diagPosSet d ∧ DR.2 ∈ corrSet d ∧ act DR.1 DR.2 = S) ∧
      (∀ S : Mat d, S.PosDef → msqrt (diagPart S) ∈ diagPosSet d ∧
        ∃ R ∈ corrSet d, act (msqrt (diagPart S)) R = S) ∧
      (1 : Mat d) ∈ corrSet d ∧ (∃ U : Set (Mat d), IsOpen U ∧ corrSet d = U ∩ unitDiagSym d) ∧
      (∃ V : Submodule ℝ (Mat d), (V : Set (Mat d)) = {X | X.IsSymm ∧ ∀ i, X i i = 0} ∧
        Module.finrank ℝ V = d * (d - 1) / 2) ∧
      {S : Mat d | ∃ D ∈ diagPosSet d, S = act D 1} = diagPosSet d := by
  -- the factorization
  have hfac : ∀ S : Mat d, S.PosDef → msqrt (diagPart S) ∈ diagPosSet d ∧
      ∃ R ∈ corrSet d, act (msqrt (diagPart S)) R = S := by
    intro S hS
    have hpos : ∀ i, 0 < S i i := fun i => hS.diag_pos
    have hsq : ∀ i, 0 < Real.sqrt (S i i) := fun i => Real.sqrt_pos.2 (hpos i)
    rw [msqrt_diagPart hS.posSemidef]
    refine ⟨⟨_, hsq, rfl⟩, act (diagonal fun i => (Real.sqrt (S i i))⁻¹) S, ⟨?_, fun i => ?_⟩, ?_⟩
    · have hU : IsUnit (diagonal fun i => (Real.sqrt (S i i))⁻¹) :=
        (diagPosSet_subset_glSet ⟨_, fun i => inv_pos.2 (hsq i), rfl⟩ :
          IsUnit (diagonal fun i => (Real.sqrt (S i i))⁻¹).det) |> (Matrix.isUnit_iff_isUnit_det _).2
      have := (hU.posDef_star_left_conjugate_iff (x := S)).2 hS
      simpa [act, Matrix.star_eq_conjTranspose] using this
    · rw [act_diagonal_apply]
      have := hsq i
      field_simp
      rw [Real.sq_sqrt (hpos i).le]
    · ext i j
      rw [act_diagonal_apply, act_diagonal_apply]
      have := (hsq i).ne'
      have := (hsq j).ne'
      field_simp
  refine ⟨diagPosSet_isWedgeDatum_ray, ?_, fun S hS => ?_, hfac, ⟨PosDef.one, fun _ => one_apply_eq _⟩,
    corrSet_eq_open_inter, ⟨zeroDiagSym d, rfl, ?_⟩, ?_⟩
  · rintro S hS _ ⟨v, hv, rfl⟩ h
    have hv1 : ∀ i, v i = 1 := by
      intro i
      have hi := congrFun (congrFun h i) i
      rw [act_diagonal_apply] at hi
      have hpos : 0 < S i i := hS.diag_pos
      have : v i * v i = 1 := by
        have := mul_right_cancel₀ hpos.ne' (by linarith [hi] : v i * v i * S i i = 1 * S i i)
        exact this
      nlinarith [hv i]
    rw [← diagonal_one]
    congr 1
    funext i
    exact hv1 i
  · obtain ⟨hD, R, hR, hRS⟩ := hfac S hS
    refine ⟨(msqrt (diagPart S), R), ⟨hD, hR, hRS⟩, ?_⟩
    rintro ⟨D', R'⟩ ⟨⟨v, hv, hD'⟩, hR', hact⟩
    simp only at hD' hact ⊢
    subst hD'
    -- the diagonals give `v = √Σᵢᵢ`, then `R' = R`
    have hvi : ∀ i, v i = Real.sqrt (S i i) := by
      intro i
      have hi := congrFun (congrFun hact i) i
      have hRi : R' i i = 1 := (show R' ∈ corrSet d from hR').2 i
      rw [act_diagonal_apply, hRi, mul_one] at hi
      rw [← hi, Real.sqrt_mul_self (hv i).le]
    have hv' : v = fun i => Real.sqrt (S i i) := funext hvi
    have hDeq : diagonal v = msqrt (diagPart S) := by rw [msqrt_diagPart hS.posSemidef, hv']
    refine Prod.ext hDeq ?_
    have hU : diagonal v ∈ glSet d := diagPosSet_subset_glSet ⟨v, hv, rfl⟩
    simp only
    rw [← act_inv_act hU R', hact, ← act_inv_act hU R, hDeq, hRS]
  · rw [show (zeroDiagSym d : Submodule ℝ (Mat d)) = zeroDiagSym d from rfl,
      (zeroDiagSymEquiv d).finrank_eq, Module.finrank_fintype_fun_eq_card, card_upperPairs]
  · ext S
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨fun i => v i * v i, fun i => mul_pos (hv i) (hv i), ?_⟩
      rw [act, diagonal_transpose, Matrix.mul_one, diagonal_mul_diagonal]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨diagonal fun i => Real.sqrt (v i), ⟨_, fun i => Real.sqrt_pos.2 (hv i), rfl⟩, ?_⟩
      rw [act, diagonal_transpose, Matrix.mul_one, diagonal_mul_diagonal]
      congr 1
      funext i
      exact (Real.mul_self_sqrt (hv i).le).symm

/-! ## Products of laws on the line -/

/-- `D_a(ν₁ ⊗ ⋯ ⊗ ν_d) = (a₁)_*ν₁ ⊗ ⋯ ⊗ (a_d)_*ν_d`. -/
theorem push_diagonal_prodLaw (a : Fin d → ℝ) (ν : Fin d → Measure ℝ)
    (hν : ∀ i, IsProbabilityMeasure (ν i)) :
    push (diagonal a) (prodLaw ν) = prodLaw fun i => dilLine (a i) (ν i) := by
  have hν' : ∀ i, IsProbabilityMeasure (dilLine (a i) (ν i)) := fun i =>
    haveI := hν i; isProbabilityMeasure_dilLine (a i) (ν i)
  haveI := isProbabilityMeasure_prodLaw ν hν
  haveI := isProbabilityMeasure_prodLaw _ hν'
  refine eq_of_charFun_eq fun ω => ?_
  rw [push, charFun_map_lin, diagonal_transpose, charFun_prodLaw _ hν, charFun_prodLaw _ hν']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lin_diagonal_apply, charFun_dilLine]

/-- A product of convolutions is the convolution of the products. -/
theorem prodLaw_conv (f g : Fin d → Measure ℝ) (hf : ∀ i, IsProbabilityMeasure (f i))
    (hg : ∀ i, IsProbabilityMeasure (g i)) :
    prodLaw (fun i => f i ∗ g i) = prodLaw f ∗ prodLaw g := by
  have hfg : ∀ i, IsProbabilityMeasure (f i ∗ g i) := fun i => by
    haveI := hf i; haveI := hg i; infer_instance
  haveI := isProbabilityMeasure_prodLaw _ hfg
  haveI := isProbabilityMeasure_prodLaw _ hf
  haveI := isProbabilityMeasure_prodLaw _ hg
  refine eq_of_charFun_eq fun ω => ?_
  rw [charFun_conv, charFun_prodLaw _ hfg, charFun_prodLaw _ hf, charFun_prodLaw _ hg,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  haveI := hf i; haveI := hg i
  rw [charFun_conv]

/-- **A product of self-decomposable laws is self-decomposable.** -/
theorem prodLaw_selfDecomposable (ν : Fin d → Measure ℝ)
    (hν : ∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) :
    IsSelfDecomposable (prodLaw ν) := by
  haveI := isProbabilityMeasure_prodLaw ν fun i => (hν i).1
  rw [isSelfDecomposable_iff_charFun]
  intro c hc0 hc1
  choose ρ hρ hfac using fun i =>
    haveI := (hν i).1
    (isSelfDecomposable_iff_charFun (ν i)).1 (hν i).2 c hc0 hc1
  refine ⟨prodLaw ρ, isProbabilityMeasure_prodLaw ρ hρ, fun ξ => ?_⟩
  rw [charFun_prodLaw _ fun i => (hν i).1, charFun_prodLaw _ fun i => (hν i).1,
    charFun_prodLaw _ hρ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hfac i (ξ i), PiLp.smul_apply, smul_eq_mul]

/-- **Dilated increments on the line**: for `0 ≤ a ≤ b` and a self-decomposable `ν`,
`(b)_*ν = (a)_*ν * ρ` for a probability measure `ρ`. -/
theorem exists_dilLine_increment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsd : IsSelfDecomposable ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ dilLine b ν = dilLine a ν ∗ ρ := by
  haveI := isProbabilityMeasure_dilLine b ν
  haveI := isProbabilityMeasure_dilLine a ν
  rcases ha.eq_or_lt with rfl | ha0
  · refine ⟨dilLine b ν, inferInstance, Measure.ext_of_charFun (funext fun t => ?_)⟩
    rw [charFun_conv, charFun_dilLine, charFun_dilLine, zero_mul, charFun_zero]
    simp
  rcases hab.eq_or_lt with rfl | hab'
  · refine ⟨Measure.dirac 0, inferInstance, Measure.ext_of_charFun (funext fun t => ?_)⟩
    rw [charFun_conv, charFun_dirac]
    simp
  have hb : 0 < b := ha0.trans hab'
  obtain ⟨ρ, hρ, hfac⟩ := (isSelfDecomposable_iff_charFun _).1 hsd (a / b) (div_pos ha0 hb)
    ((div_lt_one hb).2 hab')
  haveI := hρ
  haveI := isProbabilityMeasure_dilLine b ρ
  refine ⟨dilLine b ρ, inferInstance, Measure.ext_of_charFun (funext fun t => ?_)⟩
  rw [charFun_conv, charFun_dilLine, charFun_dilLine, charFun_dilLine, hfac (b * t), smul_eq_mul]
  have hab2 : a / b * (b * t) = a * t := by field_simp
  rw [hab2]

/-- A product of laws on the line is `δ₀` only if every factor is. -/
theorem eq_dirac_of_prodLaw_eq_dirac (ν : Fin d → Measure ℝ)
    (hν : ∀ i, IsProbabilityMeasure (ν i)) (h : prodLaw ν = Measure.dirac 0) (i : Fin d) :
    ν i = Measure.dirac 0 := by
  haveI := hν i
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h1 := congrArg (fun m => charFun m (t • ebasis i)) h
  rw [charFun_prodLaw _ hν, prod_smul_ebasis (fun j => charFun (ν j))
    (fun j => by haveI := hν j; simp [charFun_zero])] at h1
  rw [h1, charFun_dirac, charFun_dirac]
  simp

/-! ## Clause (2) -/

/-- **`prop:diagonal-ray-families`(2)**: the kernels from the origin of the
`(D₊(d), W)`-cascade families are the maps of `prop:gw-ray-families`(2) with `G = D₊(d)`. -/
theorem diagonal_ray_families (_hd : 1 ≤ d) (m : Mat d → Measure (Rd d))
    (hprob : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S)) :
    IsKernelsFromOrigin (diagPosSet d) rayLE m ↔
      IsOriginKernels (diagPosSet d) m ∧ ∀ S : Mat d, S.PosSemidef → IsSelfDecomposable (m S) :=
  gw_ray_families diagPosSet_isWedgeDatum_ray m hprob

/-- `Δ(DΣD)^{1/2} = D Δ(Σ)^{1/2}` for `D ∈ D₊(d)` and `Σ ∈ PSD(d)`. -/
theorem msqrt_diagPart_act {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) {S : Mat d} (hS : S.PosSemidef) :
    msqrt (diagPart (act (diagonal v) S)) = diagonal v * msqrt (diagPart S) := by
  rw [msqrt_diagPart (posSemidef_act _ hS), msqrt_diagPart hS, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [act_diagonal_apply, show v i * S i i * v i = v i ^ 2 * S i i by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hv i).le]

/-- `Δ(I)^{1/2} = I`. -/
theorem msqrt_diagPart_one : msqrt (diagPart (1 : Mat d)) = 1 := by
  rw [msqrt_diagPart PosSemidef.one, ← diagonal_one]
  congr 1
  funext i
  simp

/-- **The frame kernels** `Σ ↦ (Δ(Σ)^{1/2})_*μ_I` have properties (a)–(c) for `D₊(d)`. -/
theorem diagFrame_isOriginKernels (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hne : μI ≠ Measure.dirac 0) :
    IsOriginKernels (diagPosSet d) fun S => push (msqrt (diagPart S)) μI := by
  refine ⟨fun S _ => isProbabilityMeasure_push _ _, ?_, ?_, ?_, fun ω => ?_⟩
  · have h0 : msqrt (diagPart (0 : Mat d)) = 0 := by
      rw [msqrt_diagPart PosSemidef.zero, ← diagonal_zero]
      congr 1
      funext i
      simp
    simp only [h0, push_zero_mat]
  · simp only [msqrt_diagPart_one, push_one]
    exact hne
  · rintro _ ⟨v, hv, rfl⟩ S hS
    rw [push_push, msqrt_diagPart_act hv hS]
  · have hc : Continuous fun S : Mat d =>
        charFun μI (WithLp.toLp 2 fun i => Real.sqrt (S i i) * ω i) :=
      continuous_charFun.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
        (Real.continuous_sqrt.comp (continuous_id.matrix_elem i i)).mul continuous_const))
    refine hc.continuousOn.congr fun S hS => ?_
    simp only
    rw [push, charFun_map_lin, msqrt_diagPart hS, diagonal_transpose]
    congr 1
    ext i
    rw [lin_diagonal_apply]

/-- **`prop:diagonal-ray-families`(2)**, on the frame's shapes: on the orbit of `I` the kernels of a
`(D₊(d), W)`-cascade family are `μ_{D_s²} = (D_s)_*μ_I`, with `μ_I` self-decomposable and not `δ₀`;
conversely, for every self-decomposable `μ_I ≠ δ₀`, `Σ ↦ (Δ(Σ)^{1/2})_*μ_I` is the family of kernels
from the origin of a `(D₊(d), W)`-cascade family. -/
theorem diagonal_ray_frame (_hd : 1 ≤ d) :
    (∀ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (diagPosSet d) rayLE μ →
      (∀ s : Fin d → ℝ, (∀ i, 0 < s i) →
        μ 0 (diagonal fun i => s i ^ 2) = push (diagonal s) (μ 0 1)) ∧
      IsSelfDecomposable (μ 0 1) ∧ μ 0 1 ≠ Measure.dirac 0) ∧
    ∀ μI : Measure (Rd d), IsProbabilityMeasure μI → IsSelfDecomposable μI →
      μI ≠ Measure.dirac 0 →
      IsKernelsFromOrigin (diagPosSet d) rayLE fun S => push (msqrt (diagPart S)) μI := by
  have hW : IsWedgeDatum (diagPosSet d) rayLE := diagPosSet_isWedgeDatum_ray
  refine ⟨fun μ hμ => ⟨fun s hs => ?_, gw_kernels_selfDecomposable hW μ hμ 1 PosSemidef.one,
    hμ.nondegenerate⟩, fun μI hprob hsd hne => ?_⟩
  · have h := hμ.covariant (diagonal s) ⟨s, hs, rfl⟩ _ (wedge_zero_one_mem hW)
    dsimp only at h
    rw [h, act_zero]
    congr 1
    rw [act, Matrix.mul_one, diagonal_transpose, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  · haveI := hprob
    exact (gw_ray_families hW _ fun S _ => isProbabilityMeasure_push _ _).2
      ⟨diagFrame_isOriginKernels μI hne, fun S _ => (selfDecomposable_charFun_ne_zero μI hsd).2 _⟩

/-! ## Clause (3): the Loewner order gives products -/

/-- `(D₊(d), Loewner)` is a wedge datum. -/
theorem diagPosSet_isWedgeDatum_loewner : IsWedgeDatum (diagPosSet d) loewnerLE :=
  isWedgeDatum_loewner diagPosSet_isClosedSubgroupGL.1 diagPosSet_isClosedSubgroupGL.2

/-- `diag(𝟏²) = I`. -/
theorem diagonal_one_sq : (diagonal fun i => (1 : Fin d → ℝ) i ^ 2) = 1 := by
  rw [← diagonal_one]
  congr 1
  funext i
  simp

/-- **`prop:diagonal-ray-families`(3)**, the Loewner order gives products: on the orbit of `I` the
kernels from the origin of a `(D₊(d), Loewner)`-cascade family are
`μ_{D_s²} = (s₁)_*ν₁ ⊗ ⋯ ⊗ (s_d)_*ν_d` with self-decomposable `νᵢ` on `ℝ`, not all `δ₀`;
conversely, for such laws `Σ ↦ (Δ(Σ)^{1/2})_*(ν₁ ⊗ ⋯ ⊗ ν_d)` is the family of kernels from the
origin of a `(D₊(d), Loewner)`-cascade family. -/
theorem diagonal_loewner_products (hd : 1 ≤ d) :
    (∀ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily (diagPosSet d) loewnerLE μ →
      ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) ∧
        (∃ i, ν i ≠ Measure.dirac 0) ∧
        ∀ s : Fin d → ℝ, (∀ i, 0 < s i) →
          μ 0 (diagonal fun i => s i ^ 2) = prodLaw fun i => dilLine (s i) (ν i)) ∧
    ∀ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) →
      (∃ i, ν i ≠ Measure.dirac 0) →
      IsKernelsFromOrigin (diagPosSet d) loewnerLE
        fun S => push (msqrt (diagPart S)) (prodLaw ν) := by
  have hWL : IsWedgeDatum (diagPosSet d) loewnerLE := diagPosSet_isWedgeDatum_loewner
  have hdpsd : ∀ s : Fin d → ℝ, (diagonal fun i => s i ^ 2).PosSemidef :=
    fun s => PosSemidef.diagonal fun i => sq_nonneg (s i)
  have hloew0 : ∀ S : Mat d, S.PosSemidef → loewnerLE 0 S := fun S hS => by
    simpa [loewnerLE] using hS
  refine ⟨fun μ hμ => ?_, fun ν hν hne => ?_⟩
  · set μ' : (Fin d → ℝ) → Measure (Rd d) := fun s => μ 0 (diagonal fun i => s i ^ 2) with hμ'
    have hprob : ∀ s : Fin d → ℝ, (∀ i, 0 < s i) → IsProbabilityMeasure (μ' s) :=
      fun s _ => (hμ.isProbability ((0 : Mat d), diagonal fun i => s i ^ 2)
        ⟨PosSemidef.zero, hdpsd s, hloew0 _ (hdpsd s)⟩ :
        IsProbabilityMeasure (μ 0 (diagonal fun i => s i ^ 2)))
    have hD1 : ∀ δ s : Fin d → ℝ, (∀ i, 0 < δ i) → (∀ i, 0 < s i) →
        push (diagonal δ) (μ' s) = μ' (δ * s) := by
      intro δ s hδ _
      have h := hμ.covariant (diagonal δ) ⟨δ, hδ, rfl⟩ _
        (⟨PosSemidef.zero, hdpsd s, hloew0 _ (hdpsd s)⟩ :
          ((0 : Mat d), diagonal fun i => s i ^ 2) ∈ wedgePairs loewnerLE)
      dsimp only at h
      simp only [hμ']
      rw [h, act_zero]
      congr 1
      rw [act, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.mul_apply]
      ring
    have hD2 : ∀ i : Fin d, ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
        μ' (Function.update (1 : Fin d → ℝ) i lam) = μ' 1 ∗ ρ := by
      intro i lam hlam
      set u := Function.update (1 : Fin d → ℝ) i lam with hu
      have hle : loewnerLE 1 (diagonal fun j => u j ^ 2) := by
        rw [loewnerLE, ← diagonal_one, diagonal_sub]
        refine PosSemidef.diagonal fun j => ?_
        by_cases hj : j = i
        · subst hj
          simp only [hu, Function.update_self, Pi.zero_apply]
          nlinarith
        · simp [hu, hj]
      have hp : IsProbabilityMeasure (μ 1 (diagonal fun j => u j ^ 2)) :=
        hμ.isProbability ((1 : Mat d), diagonal fun j => u j ^ 2) ⟨PosSemidef.one, hdpsd u, hle⟩
      refine ⟨μ 1 (diagonal fun j => u j ^ 2), hp, ?_⟩
      have hc := hμ.cascade 0 1 _ PosSemidef.zero PosSemidef.one (hdpsd u)
        (hloew0 1 PosSemidef.one) hle
      haveI := hp
      haveI : IsProbabilityMeasure (μ 0 1) := hμ.isProbability _ (wedge_zero_one_mem hWL)
      simp only [hμ', diagonal_one_sq]
      rw [hc, Measure.conv_comm]
    obtain ⟨ν, hν, hform⟩ := fixed_frame_families hd μ' hprob hD1 hD2
    refine ⟨ν, hν, ?_, hform⟩
    by_contra hall
    push Not at hall
    apply hμ.nondegenerate
    have h1 := hform 1 fun _ => one_pos
    simp only [hμ', diagonal_one_sq] at h1
    rw [h1]
    have hp1 : ∀ i, IsProbabilityMeasure (dilLine ((1 : Fin d → ℝ) i) (ν i)) := fun i =>
      haveI := (hν i).1; isProbabilityMeasure_dilLine _ (ν i)
    haveI := isProbabilityMeasure_prodLaw _ hp1
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_prodLaw _ hp1, charFun_dirac]
    simp [hall, charFun_dilLine, charFun_dirac]
  · have hprobν : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).1
    haveI := isProbabilityMeasure_prodLaw ν hprobν
    have hne' : prodLaw ν ≠ Measure.dirac 0 := by
      obtain ⟨i, hi⟩ := hne
      exact fun h => hi (eq_dirac_of_prodLaw_eq_dirac ν hprobν h i)
    have hsdP := prodLaw_selfDecomposable ν hν
    have hz : HasNoZeros fun S => push (msqrt (diagPart S)) (prodLaw ν) := fun S _ ω =>
      (selfDecomposable_charFun_ne_zero _
        ((selfDecomposable_charFun_ne_zero (prodLaw ν) hsdP).2 (msqrt (diagPart S)))).1 ω
    have hinc : HasIncrements loewnerLE fun S => push (msqrt (diagPart S)) (prodLaw ν) := by
      intro S S' hS hS' hle
      have hii : ∀ i, S i i ≤ S' i i := fun i => by
        have := (show (S' - S).PosSemidef from hle).diag_nonneg (i := i)
        simp only [Matrix.sub_apply] at this
        linarith
      have hinc1 : ∀ i, ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
          dilLine (Real.sqrt (S' i i)) (ν i) = dilLine (Real.sqrt (S i i)) (ν i) ∗ ρ := fun i =>
        haveI := hprobν i
        exists_dilLine_increment (ν i) (hν i).2 (Real.sqrt_nonneg _)
          (Real.sqrt_le_sqrt (hii i))
      choose ρ hρ hρeq using hinc1
      refine ⟨prodLaw ρ, isProbabilityMeasure_prodLaw ρ hρ, ?_⟩
      simp only
      rw [msqrt_diagPart hS, msqrt_diagPart hS', push_diagonal_prodLaw _ _ hprobν,
        push_diagonal_prodLaw _ _ hprobν]
      simp only [hρeq]
      exact prodLaw_conv _ _ (fun i => haveI := hprobν i; isProbabilityMeasure_dilLine _ _) hρ
    exact (gw_kernels_from_origin_converse hWL _ (diagFrame_isOriginKernels (prodLaw ν) hne') hz
      hinc).1

/-! ## Clause (4): rays only, no product -/

/-- `⟨eᵢ, R eᵢ⟩ = Rᵢᵢ`. -/
theorem quad_ebasis (R : Mat d) (i : Fin d) : quad R (ebasis i) = R i i := by
  rw [quad_eq_dotProduct]
  simp [ebasis, dotProduct, mulVec, Finset.sum_ite_eq']

/-- `⟨ξ, ξ⟩ = ∑ᵢ ξᵢ²` in the form `quad 1`. -/
theorem quad_one_eq_sum (ξ : Rd d) : quad 1 ξ = ∑ i, ξ i ^ 2 := by
  rw [quad_eq_dotProduct, one_mulVec]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq]

/-- **`prop:diagonal-ray-families`(4)**, rays only: no product: for `d ≥ 2` and `Θ ∈ Corr(d)` not
diagonal, `N(0, R)` is self-decomposable and not a product `ν₁ ⊗ ⋯ ⊗ ν_d`; so the
`(D₊(d), W)`-family of (2) with `μ_I = N(0, R)` is the restriction of no
`(D₊(d), Loewner)`-family. -/
theorem diagonal_rays_no_product (hd : 2 ≤ d) (R : Mat d) (hR : R ∈ corrSet d)
    (hdiag : ¬ R.IsDiag) :
    IsSelfDecomposable (ProbabilityTheory.multivariateGaussian 0 R) ∧
      (¬ ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i)) ∧
        ProbabilityTheory.multivariateGaussian 0 R = prodLaw ν) ∧
      ¬ IsKernelsFromOrigin (diagPosSet d) loewnerLE
          fun S => push (msqrt (diagPart S)) (ProbabilityTheory.multivariateGaussian 0 R) := by
  have hRp : R.PosSemidef := hR.1.posSemidef
  set N := ProbabilityTheory.multivariateGaussian 0 R with hN
  have hNcf : ∀ ξ : Rd d, charFun N ξ = ((Real.exp (-(quad R ξ / 2)) : ℝ) : ℂ) :=
    charFun_multivariateGaussian_zero hRp
  have hnp : ¬ ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i)) ∧ N = prodLaw ν := by
    rintro ⟨ν, hν, hNν⟩
    have hνcf : ∀ i (t : ℝ), charFun (ν i) t = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      intro i t
      have h := hNcf (t • ebasis i)
      rw [hNν, charFun_prodLaw _ hν, prod_smul_ebasis (fun j => charFun (ν j))
        (fun j => by haveI := hν j; simp [charFun_zero]), quad_smul_vec, quad_ebasis, hR.2 i,
        mul_one] at h
      exact h
    have hq : ∀ ξ : Rd d, quad R ξ = quad 1 ξ := by
      intro ξ
      have h := hNcf ξ
      rw [hNν, charFun_prodLaw _ hν] at h
      simp only [hνcf] at h
      rw [← Complex.ofReal_prod, ← Real.exp_sum] at h
      have h2 := Real.exp_injective (Complex.ofReal_injective h)
      rw [quad_one_eq_sum]
      have h3 : ∑ i, -(ξ i ^ 2 / 2) = -((∑ i, ξ i ^ 2) / 2) := by
        rw [Finset.sum_neg_distrib, Finset.sum_div]
      linarith [h2, h3]
    have hR1 : R = 1 := eq_of_quad_eq hR.1.isHermitian isHermitian_one hq
    exact hdiag (hR1 ▸ isDiag_one)
  refine ⟨(isSelfDecomposable_iff_charFun N).2 fun c hc0 hc1 => ?_, hnp, ?_⟩
  · have hpsd : ((1 - c ^ 2) • R).PosSemidef := hRp.smul (by nlinarith)
    refine ⟨ProbabilityTheory.multivariateGaussian 0 ((1 - c ^ 2) • R), inferInstance,
      fun ξ => ?_⟩
    rw [hNcf, hNcf, charFun_multivariateGaussian_zero hpsd, quad_smul_vec, quad_smul,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · rintro ⟨μ, hμ, hμm⟩
    obtain ⟨ν, hν, -, hform⟩ := (diagonal_loewner_products (by omega)).1 μ hμ
    apply hnp
    refine ⟨fun i => dilLine ((1 : Fin d → ℝ) i) (ν i),
      fun i => haveI := (hν i).1; isProbabilityMeasure_dilLine _ _, ?_⟩
    have h1 := hform 1 fun _ => one_pos
    rw [diagonal_one_sq, hμm 1 PosSemidef.one] at h1
    dsimp only at h1
    rw [msqrt_diagPart_one, push_one] at h1
    exact h1

/-! ## Clause (5): off the frame's shapes -/

/-- **`prop:diagonal-ray-families`(5)**, off the frame's shapes: for `d ≥ 2` and a
rotation-invariant self-decomposable `μ_I ≠ δ₀`, `Σ ↦ (Δ(Σ)^{1/2})_*μ_I` and `Σ ↦ (Σ^{1/2})_*μ_I`
are the kernels from the origin of two `(D₊(d), W)`-cascade families with the same isotropic
member, and they differ at every `Σ ∈ PD(d)` that is not diagonal. -/
theorem diagonal_rays_off_frame (hd : 2 ≤ d) (μI : Measure (Rd d)) [IsProbabilityMeasure μI]
    (hrot : IsRotationInvariant μI) (hsd : IsSelfDecomposable μI) (hne : μI ≠ Measure.dirac 0) :
    IsKernelsFromOrigin (diagPosSet d) rayLE (fun S => push (msqrt (diagPart S)) μI) ∧
      IsKernelsFromOrigin (diagPosSet d) rayLE (affineOrbit μI) ∧
      push (msqrt (diagPart 1)) μI = μI ∧ affineOrbit μI 1 = μI ∧
      ∀ S : Mat d, S.PosDef → ¬ S.IsDiag → push (msqrt (diagPart S)) μI ≠ affineOrbit μI S := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨⟨ν₁, hν₁gl, hν₁1⟩, -⟩ := gw_ray_families_gl_converse μI hrot hsd hne
  have hk₁ := (gw_ray_families_gl ν₁ hν₁gl).1
  refine ⟨(diagonal_ray_frame (by omega)).2 μI inferInstance hsd hne,
    ⟨ν₁, gw_family_of_subset diagPosSet_subset_glSet ν₁ hν₁gl, fun S hS => by rw [hk₁ S hS, hν₁1]⟩,
    by rw [msqrt_diagPart_one, push_one], affineOrbit_one μI, fun S hS hnd h => ?_⟩
  have hpos : ∀ i, 0 < Real.sqrt (S i i) := fun i => Real.sqrt_pos.2 hS.diag_pos
  set D : Mat d := diagonal fun i => Real.sqrt (S i i) with hD
  set E : Mat d := diagonal fun i => (Real.sqrt (S i i))⁻¹ with hE
  have hED : E * D = 1 := by
    rw [hE, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hpos i).ne'
  have hDE : D * E = 1 := by
    rw [hE, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hpos i).ne'
  rw [msqrt_diagPart hS.posSemidef, ← hD] at h
  have hstab := (isFull_of_isRotationInvariant (by omega) μI hrot hne).2
  have hP : E * msqrt S ∈ stab μI := by
    refine ⟨?_, ?_⟩
    · change IsUnit (E * msqrt S).det
      rw [det_mul]
      refine IsUnit.mul ?_ (msqrt_mem_glSet hS)
      exact diagPosSet_subset_glSet ⟨_, fun i => inv_pos.2 (hpos i), rfl⟩
    · rw [← push_push]
      change push E (affineOrbit μI S) = μI
      rw [← h, push_push, hED, push_one]
  rw [hstab] at hP
  have hPP : (E * msqrt S) * (E * msqrt S)ᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
  rw [Matrix.transpose_mul, msqrt_transpose, hE, diagonal_transpose, ← hE] at hPP
  have hSE : E * S * E = 1 := by
    rw [← msqrt_mul_self hS.posSemidef]
    calc E * (msqrt S * msqrt S) * E = E * msqrt S * (msqrt S * E) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := hPP
  apply hnd
  have hSD : S = D * D := by
    calc S = (D * E) * S * (E * D) := by rw [hDE, hED, Matrix.one_mul, Matrix.mul_one]
      _ = D * (E * S * E) * D := by simp only [Matrix.mul_assoc]
      _ = D * D := by rw [hSE, Matrix.mul_one]
  rw [hSD, hD, diagonal_mul_diagonal]
  exact isDiag_diagonal _

end AffineHemigroup
