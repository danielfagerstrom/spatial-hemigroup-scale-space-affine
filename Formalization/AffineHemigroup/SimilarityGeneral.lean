/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityOrbit

/-!
# `prop:similarity-general-sandwich`: the sandwich for a general similarity-covariant part

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-general-sandwich`.

For a family of symmetric infinitely divisible laws `μ_Σ` with triplets `(C(Σ), L_Σ, 0)`, covariant
under the similarities (`IsSimGeneralFamily`): (1) `C`, `L` and `ψ` are covariant; (2) an infinitely
divisible increment orders `C`, `L` and `ψ`; (3) without a Gaussian part, a positive finite
increment is a probability measure with transform `e^{-(ψ_{Σ'} - ψ_Σ)}`; (4) along
`Σ_ε = diag(1, ε, …, ε)` the
Lévy measures decrease to a Lévy measure `L_*` on the sets bounded away from the origin, and the
exponents to `ψ_*`, both invariant under the `R ∈ O(d)` with `Re₁ = ±e₁`; (5) the sandwich
`Q_*L_* ≤ L_Σ ≤ L_I`, `ψ_*(Qᵀω) ≤ ψ_Σ(ω) ≤ ψ_I(ω)` at `λ_max(Σ) = 1`.

## Routes

* **The triplet of a linear image** of a symmetric law with drift `0`
  (`LevyTriplet.pushSym`, `hasTriplet_pushSym`) is read in the cosine form of the exponent
  (`LevyTriplet.lkExponent_symm`), so the truncation `1_D` never moves; this is the blueprint's
  "the same collapse read backwards".
* **The rank-one limit is constructed** (`exists_decreasing_limit`) as
  `L_*(B) = sup_n inf_k L_{Σ_{1/(k+1)}}(B ∩ {|x| > 1/(n+1)})`, a measure by
  `Measure.ofMeasurable`: countable additivity is the exchange of a decreasing limit with a sum
  (monotone convergence for the counting measure, `lintegral_iInf`, the first sum finite because a
  Lévy measure is finite off each ball) and of an increasing one (`lintegral_iSup`). On a set
  bounded away from the origin `L_*(B) = inf_k L_{Σ_{1/(k+1)}}(B)`, which the monotone family
  reaches as `ε ↓ 0`. Two measures null at the origin that agree on the sets bounded away from it are equal
  (`eq_of_boundedAway`), which gives the invariance.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The exponent of a Lévy measure -/

theorem IsLevyMeasure.levyExpL_ne_top {L : Measure (Rd d)} (hL : IsLevyMeasure L) (z : Rd d) :
    levyExpL L z ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 + ‖z‖ ^ 2)) hL.2) ?_
  rw [levyExpL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (one_sub_cos_le_min z x)

/-- `ψ_L(z) = ∫ (1 - cos⟨z,x⟩) L(dx)`, the Bochner integral. -/
theorem levyExp_eq_integral (L : Measure (Rd d)) (z : Rd d) :
    levyExp L z = ∫ x, (1 - Real.cos ⟪z, x⟫) ∂L := by
  rw [levyExp, levyExpL, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one ⟪z, x⟫])
    (by fun_prop)]

theorem levyExp_nonneg (L : Measure (Rd d)) (z : Rd d) : 0 ≤ levyExp L z := ENNReal.toReal_nonneg

theorem levyExp_mono {L L' : Measure (Rd d)} (h : L ≤ L') (hL' : IsLevyMeasure L') (z : Rd d) :
    levyExp L z ≤ levyExp L' z :=
  ENNReal.toReal_mono (hL'.levyExpL_ne_top z) (lintegral_mono' h le_rfl)

/-- `ψ_{A_*L}(z) = ψ_L(Aᵀz)`. -/
theorem levyExp_push (A : Mat d) (L : Measure (Rd d)) (z : Rd d) :
    levyExp (push A L) z = levyExp L (lin Aᵀ z) := by
  unfold levyExp levyExpL push
  rw [lintegral_map (by fun_prop) (lin A).continuous.measurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [real_inner_comm, inner_lin_left, real_inner_comm]

/-! ## Symmetric triplets -/

/-- **The exponent of a symmetric triplet** `(A, ν, 0)`: `-(½⟨z, Az⟩ + ψ_ν(z))`. -/
theorem LevyTriplet.lkExponent_symm (T : LevyTriplet d) (hγ : T.γ = 0)
    (hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν) (z : Rd d) :
    T.lkExponent z = -(((quad T.A z / 2 + levyExp T.ν z : ℝ)) : ℂ) := by
  have hsymI : ∫ x, (lkIntegrand z x).im ∂T.ν = 0 := by
    have h1 : ∫ x, (lkIntegrand z x).im ∂T.ν = ∫ x, (lkIntegrand z (-x)).im ∂T.ν := by
      conv_lhs => rw [← hsym]
      exact integral_map (f := fun x => (lkIntegrand z x).im)
        (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
        ((Complex.measurable_im.comp (measurable_lkIntegrand z)).aestronglyMeasurable)
    simp_rw [im_lkIntegrand_neg, integral_neg] at h1
    linarith
  have hint := T.integrable_lkIntegrand z
  apply Complex.ext
  · rw [T.re_lkExponent, Complex.neg_re, Complex.ofReal_re, levyExp_eq_integral]
    ring
  · rw [T.lkExponent_eq, Complex.add_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.ofReal_im, ← RCLike.im_to_complex, ← integral_im hint]
    simp_rw [RCLike.im_to_complex, hsymI]
    simp [hγ]

/-- **The Lévy measure of a symmetric infinitely divisible law is symmetric** (A3(ii)). -/
theorem levy_symm_of_symm {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hs : push (-1) μ = μ) {T : LevyTriplet d}
    (hT : HasTriplet μ T) : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν := by
  have hT' : HasTriplet μ (T.pushIso (LinearIsometryEquiv.neg ℝ)) := fun z => by
    rw [T.lkExponent_pushIso, ← hT]
    have h := charFun_map_lin (-1 : Mat d) μ z
    rw [← push, hs, transpose_neg, transpose_one, lin_neg_one_apply] at h
    rw [h]
    rfl
  exact (levy_khintchine_unique μ hid T _ hT hT').2.1.symm

/-! ## The triplet of a linear image -/

/-- **The triplet `(AΣAᵀ, A_*ν, 0)`** of the image of a symmetric law with drift `0`. -/
noncomputable def LevyTriplet.pushSym (T : LevyTriplet d) {A : Mat d} (hA : A ∈ glSet d) :
    LevyTriplet d where
  A := act A T.A
  ν := push A T.ν
  γ := 0
  A_posSemidef := posSemidef_act A T.A_posSemidef
  ν_zero := by
    rw [push, Measure.map_apply (lin A).continuous.measurable (measurableSet_singleton 0)]
    have : (lin A : Rd d → Rd d) ⁻¹' {0} = {0} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        rw [← lin_inv_mul_apply hA x, h, map_zero]
      · rintro rfl
        exact map_zero _
    rw [this]
    exact T.ν_zero
  ν_integrable := by
    rw [push, lintegral_map (by fun_prop) (lin A).continuous.measurable]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.ofReal_ne_top (r := max (‖lin A‖ ^ 2) 1)) T.ν_integrable) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖lin A x‖ ^ 2 ≤ ‖lin A‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((lin A).le_opNorm x) 2
    rcases le_or_gt (‖x‖ ^ 2) 1 with h | h
    · rw [min_eq_left h]
      calc min (‖lin A x‖ ^ 2) 1 ≤ ‖lin A x‖ ^ 2 := min_le_left _ _
        _ ≤ ‖lin A‖ ^ 2 * ‖x‖ ^ 2 := h1
        _ ≤ max (‖lin A‖ ^ 2) 1 * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · rw [min_eq_right h.le, mul_one]
      exact (min_le_right _ _).trans (le_max_right _ _)

/-- **The image of a symmetric law with drift `0`** has the triplet `(AΣAᵀ, A_*ν, 0)`. -/
theorem LevyTriplet.hasTriplet_pushSym {μ : Measure (Rd d)} {T : LevyTriplet d}
    (hT : HasTriplet μ T) (hγ : T.γ = 0)
    (hsym : T.ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = T.ν) {A : Mat d}
    (hA : A ∈ glSet d) : HasTriplet (push A μ) (T.pushSym hA) := fun z => by
  have hsym' : (T.pushSym hA).ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = (T.pushSym hA).ν := by
    change (push A T.ν).map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = push A T.ν
    unfold push
    rw [Measure.map_map (LinearIsometryEquiv.neg ℝ).continuous.measurable
      (lin A).continuous.measurable]
    conv_rhs => rw [← hsym]
    rw [Measure.map_map (lin A).continuous.measurable
      (LinearIsometryEquiv.neg ℝ).continuous.measurable]
    congr 1
    funext x
    simp
  rw [push, charFun_map_lin, hT, T.lkExponent_symm hγ hsym,
    (T.pushSym hA).lkExponent_symm rfl hsym']
  change Complex.exp (-(((quad T.A (lin Aᵀ z) / 2 + levyExp T.ν (lin Aᵀ z) : ℝ)) : ℂ)) =
    Complex.exp (-(((quad (act A T.A) z / 2 + levyExp (push A T.ν) z : ℝ)) : ℂ))
  rw [quad_act, levyExp_push]

/-! ## The standing hypotheses -/

namespace IsSimGeneralFamily

variable {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d} {L : Mat d → Measure (Rd d)}

theorem levy_symm (hfam : IsSimGeneralFamily μ C L) {S : Mat d} (hS : S.PosDef) :
    (L S).map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = L S := by
  haveI := hfam.isProbability S hS
  obtain ⟨T, -, hν, -, hT⟩ := hfam.triplet S hS
  rw [← hν]
  exact levy_symm_of_symm (hfam.infinitelyDivisible S hS) (hfam.symmetric S hS) hT

theorem isLevy (hfam : IsSimGeneralFamily μ C L) {S : Mat d} (hS : S.PosDef) :
    IsLevyMeasure (L S) := by
  obtain ⟨T, -, hν, -, -⟩ := hfam.triplet S hS
  rw [← hν]
  exact ⟨T.ν_zero, T.ν_integrable⟩

theorem C_psd (hfam : IsSimGeneralFamily μ C L) {S : Mat d} (hS : S.PosDef) :
    (C S).PosSemidef := by
  obtain ⟨T, hA, -, -, -⟩ := hfam.triplet S hS
  rw [← hA]
  exact T.A_posSemidef

/-- `μ̂_Σ(ω) = exp(-½⟨ω, C(Σ)ω⟩ - ψ_Σ(ω))`. -/
theorem charFun_eq (hfam : IsSimGeneralFamily μ C L) {S : Mat d} (hS : S.PosDef) (ω : Rd d) :
    charFun (μ S) ω = ((Real.exp (-(quad (C S) ω / 2 + levyExp (L S) ω)) : ℝ) : ℂ) := by
  obtain ⟨T, hA, hν, hγ, hT⟩ := hfam.triplet S hS
  have hsym := hfam.levy_symm hS
  rw [← hν] at hsym
  rw [hT, T.lkExponent_symm hγ hsym, hA, hν, Complex.ofReal_exp, Complex.ofReal_neg]

end IsSimGeneralFamily

/-! ## Clauses (1)–(3) -/

/-- `(√c Q) Σ (√c Q)ᵀ = c QΣQᵀ`. -/
theorem act_sqrt_smul (c : ℝ) (hc : 0 ≤ c) (Q S : Mat d) :
    act (Real.sqrt c • Q) S = c • (Q * S * Qᵀ) := by
  simp only [act, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← sq, Real.sq_sqrt hc]

theorem sqrt_smul_mem_glSet {c : ℝ} (hc : 0 < c) {Q : Mat d} (hQ : Q ∈ orthSet d) :
    Real.sqrt c • Q ∈ glSet d := by
  change IsUnit (Real.sqrt c • Q).det
  rw [det_smul]
  exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (Real.sqrt_pos.2 hc).ne')).mul
    (orthSet_subset_glSet hQ)

/-- **`prop:similarity-general-sandwich`(1)**, covariance: `C(cQΣQᵀ) = cQC(Σ)Qᵀ`,
`L_{cQΣQᵀ} = (√c Q)_*L_Σ` and `ψ_{cQΣQᵀ}(ω) = ψ_Σ(√c Qᵀω)`; in particular `L_I` and `ψ_I` are
rotation invariant. Spends A3(i)–(ii). -/
theorem sim_general_covariance (_hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) :
    (∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      C (c • (Q * S * Qᵀ)) = c • (Q * C S * Qᵀ) ∧
      L (c • (Q * S * Qᵀ)) = push (Real.sqrt c • Q) (L S) ∧
      ∀ ω : Rd d, levyExp (L (c • (Q * S * Qᵀ))) ω = levyExp (L S) (Real.sqrt c • lin Qᵀ ω)) ∧
    IsRotationInvariant (L 1) ∧
      ∀ Q ∈ orthSet d, ∀ ω : Rd d, levyExp (L 1) (lin Q ω) = levyExp (L 1) ω := by
  have hcov : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      C (c • (Q * S * Qᵀ)) = c • (Q * C S * Qᵀ) ∧
      L (c • (Q * S * Qᵀ)) = push (Real.sqrt c • Q) (L S) := by
    intro S hS c hc Q hQ
    set A := Real.sqrt c • Q with hAdef
    have hA : A ∈ glSet d := sqrt_smul_mem_glSet hc hQ
    have hS' : (c • (Q * S * Qᵀ)).PosDef := by
      rw [← act_sqrt_smul c hc.le]
      exact (posDef_act_iff hA S).2 hS
    haveI := hfam.isProbability S hS
    obtain ⟨T, hTA, hTν, hTγ, hT⟩ := hfam.triplet S hS
    obtain ⟨T', hTA', hTν', -, hT'⟩ := hfam.triplet _ hS'
    have hsym := hfam.levy_symm hS
    rw [← hTν] at hsym
    have hpush := T.hasTriplet_pushSym hT hTγ hsym hA
    rw [hfam.covariant S hS c hc Q hQ] at hpush
    haveI := hfam.isProbability _ hS'
    obtain ⟨h1, h2, -⟩ := levy_khintchine_unique _ (hfam.infinitelyDivisible _ hS') T' _ hT' hpush
    refine ⟨?_, ?_⟩
    · rw [← hTA', h1, ← hTA]
      exact act_sqrt_smul c hc.le Q (T.A)
    · rw [← hTν', h2, ← hTν]
      rfl
  have h1o : (1 : Mat d) ∈ orthSet d := (Matrix.orthogonalGroup (Fin d) ℝ).one_mem
  refine ⟨fun S hS c hc Q hQ => ⟨(hcov S hS c hc Q hQ).1, (hcov S hS c hc Q hQ).2, fun ω => ?_⟩,
    fun Q hQ => ?_, fun Q hQ ω => ?_⟩
  · rw [(hcov S hS c hc Q hQ).2, levyExp_push, Matrix.transpose_smul, lin_smul]
    rfl
  · have h := (hcov 1 PosDef.one 1 one_pos Q hQ).2
    rw [Matrix.mul_one, orth_mul_transpose hQ, one_smul, Real.sqrt_one, one_smul] at h
    exact h.symm
  · have hQt := transpose_mem_orthSet hQ
    have h := (hcov 1 PosDef.one 1 one_pos Qᵀ hQt).2
    rw [Matrix.mul_one, transpose_transpose, orth_transpose_mul hQ, one_smul, Real.sqrt_one,
      one_smul] at h
    rw [show levyExp (L 1) ω = levyExp (push Qᵀ (L 1)) ω by rw [← h], levyExp_push,
      transpose_transpose]

/-- **`prop:similarity-general-sandwich`(2)**, infinitely divisible increments: if
`μ_{Σ'} = μ_Σ * ρ` with `ρ` infinitely divisible, then `C(Σ) ≤ C(Σ')`, `L_Σ ≤ L_{Σ'}` and
`ψ_Σ ≤ ψ_{Σ'}`. Spends A3(i)–(ii). -/
theorem sim_general_id_increment (_hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
      IsInfinitelyDivisible ρ → μ S' = μ S ∗ ρ →
      loewnerLE (C S) (C S') ∧ L S ≤ L S' ∧ ∀ ω : Rd d, levyExp (L S) ω ≤ levyExp (L S') ω := by
  intro S S' hS hS' ρ hρ hρid heq
  haveI := hfam.isProbability S hS
  haveI := hfam.isProbability S' hS'
  obtain ⟨T, hTA, hTν, -, hT⟩ := hfam.triplet S hS
  obtain ⟨T', hTA', hTν', -, hT'⟩ := hfam.triplet S' hS'
  obtain ⟨Tρ, -, hA, hν, -⟩ :=
    triplet_increment hρid (hfam.infinitelyDivisible S' hS') hT heq hT'
  have hLle : L S ≤ L S' := by
    rw [← hTν, ← hTν', hν]
    exact Measure.le_add_right le_rfl
  refine ⟨?_, hLle, fun ω => levyExp_mono hLle (hfam.isLevy hS') ω⟩
  unfold loewnerLE
  rw [← hTA, ← hTA', hA, add_sub_cancel_left]
  exact Tρ.A_posSemidef

/-- **`prop:similarity-general-sandwich`(3)**, positive increments without a Gaussian part: if
`C ≡ 0` and `μ_{Σ'} = μ_Σ * ρ` with `ρ` a positive finite measure, then `ρ` is a probability
measure, `ρ̂ = e^{-(ψ_{Σ'} - ψ_Σ)}`, and `ψ_Σ ≤ ψ_{Σ'}`. -/
theorem sim_general_finite_increment (_hd : 2 ≤ d) (μ : Mat d → Measure (Rd d))
    (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hC : ∀ S : Mat d, S.PosDef → C S = 0) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
      μ S' = μ S ∗ ρ →
      IsProbabilityMeasure ρ ∧
        (∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(levyExp (L S') ω - levyExp (L S) ω)) : ℝ) : ℂ)) ∧
        ∀ ω : Rd d, levyExp (L S) ω ≤ levyExp (L S') ω := by
  intro S S' hS hS' ρ hρ heq
  haveI := hρ
  haveI := hfam.isProbability S hS
  have hchar : ∀ ω : Rd d,
      charFun ρ ω = ((Real.exp (-(levyExp (L S') ω - levyExp (L S) ω)) : ℝ) : ℂ) := by
    intro ω
    have h2 := congrArg (fun m => charFun m ω) heq
    simp only [charFun_conv, hfam.charFun_eq hS, hfam.charFun_eq hS', hC S hS, hC S' hS',
      quad_zero, zero_div, zero_add] at h2
    have hne : ((Real.exp (-levyExp (L S) ω) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    apply mul_left_cancel₀ hne
    rw [← h2, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hprob : IsProbabilityMeasure ρ := by
    have h0 := hchar 0
    rw [charFun_zero] at h0
    have hψ0 : ∀ L' : Measure (Rd d), levyExp L' 0 = 0 := fun L' => by
      rw [levyExp_eq_integral]; simp
    rw [hψ0, hψ0, sub_zero, neg_zero, Real.exp_zero, Complex.ofReal_one] at h0
    constructor
    have h1 : ρ.real univ = 1 := by exact_mod_cast h0
    rw [measureReal_def] at h1
    exact (ENNReal.toReal_eq_one_iff _).1 h1
  refine ⟨hprob, hchar, fun ω => ?_⟩
  have hle := norm_charFun_le_one (μ := ρ) ω
  rw [hchar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.exp_le_one_iff] at hle
  linarith

/-! ## Sets bounded away from the origin -/

/-- `A_n := {x : 1/(n+1) < |x|}`. -/
def awaySet (n : ℕ) : Set (Rd d) := {x | 1 / ((n : ℝ) + 1) < ‖x‖}

theorem measurableSet_awaySet (n : ℕ) : MeasurableSet (awaySet (d := d) n) :=
  measurableSet_lt measurable_const continuous_norm.measurable

theorem awaySet_mono : Monotone (awaySet (d := d)) := by
  intro n m hnm x hx
  refine lt_of_le_of_lt ?_ (show 1 / ((n : ℝ) + 1) < ‖x‖ from hx)
  have : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem iUnion_awaySet : ⋃ n, awaySet (d := d) n = {0}ᶜ := by
  ext x
  simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨n, hn⟩ rfl
    have : 1 / ((n : ℝ) + 1) < ‖(0 : Rd d)‖ := hn
    rw [norm_zero] at this
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx)
    exact ⟨n, hn⟩

theorem IsBoundedAway.exists_subset {B : Set (Rd d)} (hB : IsBoundedAway B) :
    ∃ n, B ⊆ awaySet n := by
  obtain ⟨δ, hδ, hB⟩ := hB
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  exact ⟨n, fun x hx => lt_of_lt_of_le hn (hB x hx)⟩

theorem isBoundedAway_inter_awaySet (B : Set (Rd d)) (n : ℕ) : IsBoundedAway (B ∩ awaySet n) :=
  ⟨1 / ((n : ℝ) + 1), by positivity, fun x hx => le_of_lt hx.2⟩

/-- A Lévy measure is finite off each ball about the origin. -/
theorem IsLevyMeasure.awaySet_ne_top {L : Measure (Rd d)} (hL : IsLevyMeasure L) (n : ℕ) :
    L (awaySet n) ≠ ⊤ := by
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hc : 0 < min (ε ^ 2) 1 := lt_min (by positivity) one_pos
  have hle : ENNReal.ofReal (min (ε ^ 2) 1) * L (awaySet n)
      ≤ ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂L := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono' (measurableSet_awaySet n) fun x (hx : ε < ‖x‖) =>
      ENNReal.ofReal_le_ofReal ?_).trans (setLIntegral_le_lintegral _ _)
    exact min_le_min (pow_le_pow_left₀ hε0.le hx.le 2) le_rfl
  intro htop
  rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc)] at hle
  exact hL.2 (top_le_iff.mp hle)

/-- **Two measures null at the origin compare on the sets bounded away from it.** -/
theorem measure_le_of_boundedAway {M M' : Measure (Rd d)} (h0 : M {0} = 0)
    (h : ∀ B : Set (Rd d), MeasurableSet B → IsBoundedAway B → M B ≤ M' B) : M ≤ M' := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [← measure_sdiff_null h0, sdiff_eq, ← iUnion_awaySet, inter_iUnion,
    Monotone.measure_iUnion (fun n m hnm => inter_subset_inter_right _ (awaySet_mono hnm))]
  exact iSup_le fun n => (h _ (hB.inter (measurableSet_awaySet n))
    (isBoundedAway_inter_awaySet B n)).trans (measure_mono inter_subset_left)

theorem eq_of_boundedAway {M M' : Measure (Rd d)} (h0 : M {0} = 0) (h0' : M' {0} = 0)
    (h : ∀ B : Set (Rd d), MeasurableSet B → IsBoundedAway B → M B = M' B) : M = M' :=
  le_antisymm (measure_le_of_boundedAway h0 fun B hB hB' => (h B hB hB').le)
    (measure_le_of_boundedAway h0' fun B hB hB' => (h B hB hB').ge)

/-! ## The limit of a decreasing family of measures -/

/-- A decreasing limit commutes with a sum whose first term is finite. -/
theorem tsum_iInf_of_antitone (g : ℕ → ℕ → ℝ≥0∞) (hg : Antitone g) (h0 : ∑' i, g 0 i ≠ ⊤) :
    ∑' i, ⨅ k, g k i = ⨅ k, ∑' i, g k i := by
  have h := lintegral_iInf (μ := (Measure.count : Measure ℕ))
    (fun k => measurable_of_countable (g k))
    hg (by rwa [lintegral_count])
  simp only [lintegral_count] at h
  simpa only [iInf_apply] using h

/-- An increasing limit commutes with a sum. -/
theorem tsum_iSup_of_monotone (g : ℕ → ℕ → ℝ≥0∞) (hg : Monotone g) :
    ∑' i, ⨆ n, g n i = ⨆ n, ∑' i, g n i := by
  have h := lintegral_iSup (μ := (Measure.count : Measure ℕ))
    (fun n => measurable_of_countable (g n))
    hg
  simp only [lintegral_count] at h
  simpa only [iSup_apply] using h

/-- **The limit of a decreasing sequence of measures on the sets bounded away from the origin**:
`M(B) = sup_n inf_k L_k(B ∩ A_n)` is a measure, null at the origin, below every `L_k`, and equal to
`inf_k L_k(B)` on the measurable sets bounded away from the origin. -/
theorem exists_decreasing_limit (Lf : ℕ → Measure (Rd d)) (hanti : Antitone Lf)
    (hfin : ∀ n, Lf 0 (awaySet n) ≠ ⊤) :
    ∃ M : Measure (Rd d), M {0} = 0 ∧
      (∀ B : Set (Rd d), MeasurableSet B → IsBoundedAway B → M B = ⨅ k, Lf k B) ∧
      ∀ k, M ≤ Lf k := by
  set m : ∀ B : Set (Rd d), MeasurableSet B → ℝ≥0∞ :=
    fun B _ => ⨆ n, ⨅ k, Lf k (B ∩ awaySet n) with hmdef
  have hm0 : m ∅ MeasurableSet.empty = 0 := by simp [hmdef]
  have hmadd : ∀ ⦃f : ℕ → Set (Rd d)⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (Function.onFun Disjoint f) →
      m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i) := by
    intro f hf hdisj
    simp only [hmdef]
    -- the decreasing limit and the sum, at each `n`
    have hdec : ∀ n, ⨅ k, Lf k ((⋃ i, f i) ∩ awaySet n) =
        ∑' i, ⨅ k, Lf k (f i ∩ awaySet n) := by
      intro n
      have hdisj' : Pairwise (Function.onFun Disjoint fun i => f i ∩ awaySet n) := fun i j hij =>
        (hdisj hij).mono inter_subset_left inter_subset_left
      have hmeas : ∀ i, MeasurableSet (f i ∩ awaySet n) := fun i =>
        (hf i).inter (measurableSet_awaySet n)
      have hsum : ∀ k, Lf k ((⋃ i, f i) ∩ awaySet n) = ∑' i, Lf k (f i ∩ awaySet n) := by
        intro k
        rw [iUnion_inter, measure_iUnion hdisj' hmeas]
      simp_rw [hsum]
      refine (tsum_iInf_of_antitone (fun k i => Lf k (f i ∩ awaySet n))
        (fun k k' hkk' i => hanti hkk' _) ?_).symm
      rw [← measure_iUnion hdisj' hmeas]
      exact ne_top_of_le_ne_top (hfin n) (measure_mono (iUnion_subset fun i => inter_subset_right))
    simp_rw [hdec]
    -- the increasing limit and the sum
    have hmono : Monotone fun n i => ⨅ k, Lf k (f i ∩ awaySet n) := by
      intro n n' hnn' i
      exact iInf_mono fun k => measure_mono (inter_subset_inter_right _ (awaySet_mono hnn'))
    exact (tsum_iSup_of_monotone _ hmono).symm
  set M := Measure.ofMeasurable m hm0 hmadd with hMdef
  have hMapp : ∀ B (hB : MeasurableSet B), M B = ⨆ n, ⨅ k, Lf k (B ∩ awaySet n) :=
    fun B hB => Measure.ofMeasurable_apply B hB
  refine ⟨M, ?_, fun B hB hBa => ?_, fun k => Measure.le_iff.2 fun B hB => ?_⟩
  · rw [hMapp _ (measurableSet_singleton 0)]
    refine le_antisymm (iSup_le fun n => ?_) bot_le
    have : ({0} : Set (Rd d)) ∩ awaySet n = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      change ¬ (1 / ((n : ℝ) + 1) < ‖(0 : Rd d)‖)
      rw [norm_zero, not_lt]
      positivity
    rw [this]
    exact (iInf_le _ 0).trans (by simp)
  · rw [hMapp B hB]
    obtain ⟨n0, hn0⟩ := hBa.exists_subset
    refine le_antisymm (iSup_le fun n => iInf_mono fun k => measure_mono inter_subset_left) ?_
    refine le_trans ?_ (le_iSup _ n0)
    rw [inter_eq_left.2 hn0]
  · rw [hMapp B hB]
    exact iSup_le fun n => (iInf_le _ k).trans (measure_mono inter_subset_left)

/-- **A monotone family on `(0,∞)` tends, as `ε ↓ 0`, to its infimum along `1/(k+1)`.** -/
theorem tendsto_nhdsGT_of_monotone_ennreal {f : ℝ → ℝ≥0∞}
    (hmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → f ε ≤ f ε') :
    Tendsto f (𝓝[>] 0) (𝓝 (⨅ k : ℕ, f (1 / ((k : ℝ) + 1)))) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε'
    exact lt_of_lt_of_le hb ((iInf_le _ k).trans (hmono _ _ (by positivity) hk.le))
  · obtain ⟨k, hk⟩ := iInf_lt_iff.1 hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (hmono _ _ hε.1 hε.2.le) hk

/-- The same for a real function bounded below by `0`. -/
theorem tendsto_nhdsGT_of_monotone_real {f : ℝ → ℝ} (h0 : ∀ ε, 0 ≤ f ε)
    (hmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → f ε ≤ f ε') :
    Tendsto f (𝓝[>] 0) (𝓝 (⨅ k : ℕ, f (1 / ((k : ℝ) + 1)))) := by
  have hbdd : BddBelow (range fun k : ℕ => f (1 / ((k : ℝ) + 1))) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact h0 _⟩
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε'
    exact lt_of_lt_of_le hb ((ciInf_le hbdd k).trans (hmono _ _ (by positivity) hk.le))
  · obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (hmono _ _ hε.1 hε.2.le) hk

/-! ## `Σ_ε` -/

theorem sq_apply_le_norm_sq (y : Rd d) (i : Fin d) : y i ^ 2 ≤ ‖y‖ ^ 2 := by
  have := PiLp.norm_apply_le y i
  rw [Real.norm_eq_abs] at this
  nlinarith [abs_nonneg (y i), sq_abs (y i), norm_nonneg y]

theorem sigmaEps_one : sigmaEps d 1 = 1 := by
  unfold sigmaEps
  rw [← diagonal_one]
  congr 1
  funext i
  split_ifs <;> rfl

/-- `Σ_ε ≤ Σ_{ε'}` for `ε ≤ ε'`. -/
theorem sigmaEps_le [NeZero d] {ε ε' : ℝ} (h : ε ≤ ε') :
    loewnerLE (sigmaEps d ε) (sigmaEps d ε') := by
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg ?_ fun y => ?_
  · unfold sigmaEps
    exact (isHermitian_diagonal _).sub (isHermitian_diagonal _)
  rw [quad_sub, quad_sigmaEps, quad_sigmaEps]
  have := sq_apply_le_norm_sq y 0
  nlinarith

/-- `RΣ_εRᵀ = Σ_ε` when `Re₁ = ±e₁`. -/
theorem act_sigmaEps_of_fix [NeZero d] {R : Mat d} (hR : R ∈ orthSet d)
    (hRe : lin R (ebasis 0) = ebasis 0 ∨ lin R (ebasis 0) = -ebasis 0) (ε : ℝ) :
    act R (sigmaEps d ε) = sigmaEps d ε := by
  have hh : (sigmaEps d ε).IsHermitian := by unfold sigmaEps; exact isHermitian_diagonal _
  have hT : (sigmaEps d ε)ᵀ = sigmaEps d ε := by unfold sigmaEps; exact diagonal_transpose _
  have hRh : (act R (sigmaEps d ε)).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, act, transpose_mul, transpose_mul,
      transpose_transpose, hT, Matrix.mul_assoc]
  refine eq_of_quad_eq hRh hh fun x => ?_
  rw [quad_act, quad_sigmaEps, quad_sigmaEps, norm_lin_transpose_of_orth hR]
  have h0 : (lin Rᵀ x) 0 = ⟪lin R (ebasis 0), x⟫ := by
    have h1 : ⟪(ebasis 0 : Rd d), lin Rᵀ x⟫ = (lin Rᵀ x) 0 := by
      simp [ebasis, EuclideanSpace.inner_single_left]
    rw [← h1, inner_lin_left]
  have hx0 : ⟪(ebasis 0 : Rd d), x⟫ = x 0 := by simp [ebasis, EuclideanSpace.inner_single_left]
  rw [h0]
  rcases hRe with h | h <;> rw [h]
  · rw [hx0]
  · rw [inner_neg_left, hx0, neg_sq]

/-- `‖Rx‖ = ‖x‖` for `R ∈ O(d)`. -/
theorem norm_lin_of_orth {R : Mat d} (hR : R ∈ orthSet d) (x : Rd d) : ‖lin R x‖ = ‖x‖ := by
  have := norm_lin_transpose_of_orth (transpose_mem_orthSet hR) x
  rwa [transpose_transpose] at this

theorem lin_transpose_lin_of_orth {R : Mat d} (hR : R ∈ orthSet d) (x : Rd d) :
    lin Rᵀ (lin R x) = x := by
  rw [show lin Rᵀ (lin R x) = lin (Rᵀ * R) x by rw [lin_mul]; rfl, orth_transpose_mul hR, lin_one]
  rfl

theorem preimage_lin_orth_boundedAway {R : Mat d} (hR : R ∈ orthSet d) {B : Set (Rd d)}
    (hB : IsBoundedAway B) : IsBoundedAway ((lin R : Rd d → Rd d) ⁻¹' B) := by
  obtain ⟨δ, hδ, hB⟩ := hB
  exact ⟨δ, hδ, fun x hx => by rw [← norm_lin_of_orth hR x]; exact hB _ hx⟩

theorem push_orth_zero {R : Mat d} (hR : R ∈ orthSet d) {M : Measure (Rd d)} (h0 : M {0} = 0) :
    push R M {0} = 0 := by
  rw [push, Measure.map_apply (lin R).continuous.measurable (measurableSet_singleton 0)]
  have : (lin R : Rd d → Rd d) ⁻¹' {0} = {0} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      rw [← norm_eq_zero, ← norm_lin_of_orth hR x, h, norm_zero]
    · rintro rfl
      exact map_zero _
  rw [this, h0]

/-! ## Clause (4) -/

theorem fin_zero_eq (hd : 1 ≤ d) [NeZero d] : (⟨0, by omega⟩ : Fin d) = 0 := Fin.ext (by simp)

/-- **The exponents are monotone along the Loewner order** under either hypothesis of (4). -/
theorem sim_general_mono (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hle : loewnerLE S S') (ω : Rd d) :
    levyExp (L S) ω ≤ levyExp (L S') ω := by
  rcases hinc with hID | ⟨hC, hfin⟩
  · obtain ⟨ρ, hρ, hρid, heq⟩ := hID S S' hS hS' hle
    exact (sim_general_id_increment hd μ C L hfam S S' hS hS' ρ hρ hρid heq).2.2 ω
  · obtain ⟨ρ, hρ, heq⟩ := hfin S S' hS hS' hle
    exact (sim_general_finite_increment hd μ C L hfam hC S S' hS hS' ρ hρ heq).2.2 ω

/-- `L_{QΣQᵀ} = Q_*L_Σ` and `ψ_{QΣQᵀ}(ω) = ψ_Σ(Qᵀω)` (clause (1) at `c = 1`). -/
theorem sim_general_conj (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L) {S Q : Mat d}
    (hS : S.PosDef) (hQ : Q ∈ orthSet d) :
    L (act Q S) = push Q (L S) ∧
      ∀ ω : Rd d, levyExp (L (act Q S)) ω = levyExp (L S) (lin Qᵀ ω) := by
  have h := (sim_general_covariance hd μ C L hfam).1 S hS 1 one_pos Q hQ
  simp only [one_smul, Real.sqrt_one] at h
  exact ⟨h.2.1, fun ω => h.2.2 ω⟩

/-- **`prop:similarity-general-sandwich`(4)**, the rank-one limit under infinitely divisible
increments: `L_*(B) = lim_{ε↓0} L_{Σ_ε}(B)` exists on the Borel sets bounded away from the origin
and extends to a Lévy measure with `L_* ≤ L_{Σ_ε}` for `ε ∈ (0,1]`; `ψ_* = lim ψ_{Σ_ε}` exists; both
are invariant under every `R ∈ O(d)` with `Re₁ = ±e₁`. -/
theorem sim_general_rank_one_limit (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d))
    (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hID : HasIDLoewnerIncrements μ) :
    (∃ Lstar : Measure (Rd d), IsRankOneLimit L Lstar ∧ IsLevyMeasure Lstar ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → Lstar ≤ L (sigmaEps d ε)) ∧
      ∀ R ∈ orthSet d, (lin R (ebasis ⟨0, by omega⟩) = ebasis ⟨0, by omega⟩ ∨
          lin R (ebasis ⟨0, by omega⟩) = -ebasis ⟨0, by omega⟩) →
        push R Lstar = Lstar) ∧
    ∃ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar ∧
      ∀ R ∈ orthSet d, (lin R (ebasis ⟨0, by omega⟩) = ebasis ⟨0, by omega⟩ ∨
          lin R (ebasis ⟨0, by omega⟩) = -ebasis ⟨0, by omega⟩) →
        ∀ ω : Rd d, ψstar (lin R ω) = ψstar ω := by
  haveI : NeZero d := ⟨by omega⟩
  rw [fin_zero_eq (by omega)]
  have hmonoL : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → L (sigmaEps d ε) ≤ L (sigmaEps d ε') := by
    intro ε ε' hε hεε'
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ _ (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) (sigmaEps_le hεε')
    exact (sim_general_id_increment hd μ C L hfam _ _ (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) ρ hρ hρid heq).2.1
  have hmonoψ : ∀ ω : Rd d, ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' →
      levyExp (L (sigmaEps d ε)) ω ≤ levyExp (L (sigmaEps d ε')) ω := fun ω ε ε' hε hεε' =>
    sim_general_mono hd hfam (Or.inl hID) (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) (sigmaEps_le hεε') ω
  -- invariance along `Σ_ε`
  have hinvL : ∀ R ∈ orthSet d, (lin R (ebasis 0) = ebasis 0 ∨ lin R (ebasis 0) = -ebasis 0) →
      ∀ ε : ℝ, 0 < ε → push R (L (sigmaEps d ε)) = L (sigmaEps d ε) := by
    intro R hR hRe ε hε
    have h := (sim_general_conj hd hfam (sigmaEps_posDef hε) hR).1
    rw [act_sigmaEps_of_fix hR hRe] at h
    exact h.symm
  set Lf : ℕ → Measure (Rd d) := fun k => L (sigmaEps d (1 / ((k : ℝ) + 1))) with hLf
  have hanti : Antitone Lf := fun k k' hkk' => hmonoL _ _ (by positivity)
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkk' 1))
  have hL1 : Lf 0 = L 1 := by simp [hLf, sigmaEps_one]
  have hfin : ∀ n, Lf 0 (awaySet n) ≠ ⊤ := fun n => by
    rw [hL1]; exact (hfam.isLevy PosDef.one).awaySet_ne_top n
  obtain ⟨M, hM0, hMB, hMle⟩ := exists_decreasing_limit Lf hanti hfin
  have hlim : IsRankOneLimit L M := ⟨hM0, fun B hB hBa => by
    rw [hMB B hB hBa]
    exact tendsto_nhdsGT_of_monotone_ennreal fun ε ε' hε h =>
      Measure.le_iff'.1 (hmonoL ε ε' hε h) B⟩
  refine ⟨⟨M, hlim, ⟨hM0, ?_⟩, fun ε hε hε1 => ?_, fun R hR hRe => ?_⟩, ?_⟩
  · refine ne_top_of_le_ne_top (hfam.isLevy PosDef.one).2 (lintegral_mono' ?_ le_rfl)
    rw [← hL1]; exact hMle 0
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact (hMle k).trans (hmonoL _ _ (by positivity) hk.le)
  · refine eq_of_boundedAway (push_orth_zero hR hM0) hM0 fun B hB hBa => ?_
    have hB' : MeasurableSet ((lin R : Rd d → Rd d) ⁻¹' B) := (lin R).continuous.measurable hB
    rw [push, Measure.map_apply (lin R).continuous.measurable hB,
      hMB _ hB' (preimage_lin_orth_boundedAway hR hBa), hMB B hB hBa]
    congr 1
    funext k
    have := hinvL R hR hRe _ (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
    show (L (sigmaEps d (1 / ((k : ℝ) + 1)))) ((lin R : Rd d → Rd d) ⁻¹' B) =
      (L (sigmaEps d (1 / ((k : ℝ) + 1)))) B
    conv_rhs => rw [← this]
    rw [push, Measure.map_apply (lin R).continuous.measurable hB]
  · refine ⟨fun ω => ⨅ k : ℕ, levyExp (Lf k) ω, fun ω =>
      tendsto_nhdsGT_of_monotone_real (fun ε => levyExp_nonneg _ ω) (hmonoψ ω),
      fun R hR hRe ω => ?_⟩
    show (⨅ k : ℕ, levyExp (L (sigmaEps d (1 / ((k : ℝ) + 1)))) (lin R ω)) =
      ⨅ k : ℕ, levyExp (L (sigmaEps d (1 / ((k : ℝ) + 1)))) ω
    congr 1
    funext k
    have := hinvL R hR hRe _ (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
    conv_lhs => rw [← this]
    rw [levyExp_push, lin_transpose_lin_of_orth hR]

/-- **`prop:similarity-general-sandwich`(4)**, the second hypothesis: if `C ≡ 0` and every Loewner
step has a positive finite increment, `ψ_*` exists and has the same invariance. -/
theorem sim_general_rank_one_exp_limit (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d))
    (C : Mat d → Mat d) (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hC : ∀ S : Mat d, S.PosDef → C S = 0) (hfin : HasFiniteLoewnerIncrements μ) :
    ∃ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar ∧
      ∀ R ∈ orthSet d, (lin R (ebasis ⟨0, by omega⟩) = ebasis ⟨0, by omega⟩ ∨
          lin R (ebasis ⟨0, by omega⟩) = -ebasis ⟨0, by omega⟩) →
        ∀ ω : Rd d, ψstar (lin R ω) = ψstar ω := by
  haveI : NeZero d := ⟨by omega⟩
  rw [fin_zero_eq (by omega)]
  have hmonoψ : ∀ ω : Rd d, ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' →
      levyExp (L (sigmaEps d ε)) ω ≤ levyExp (L (sigmaEps d ε')) ω := fun ω ε ε' hε hεε' =>
    sim_general_mono hd hfam (Or.inr ⟨hC, hfin⟩) (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) (sigmaEps_le hεε') ω
  refine ⟨fun ω => ⨅ k : ℕ, levyExp (L (sigmaEps d (1 / ((k : ℝ) + 1)))) ω, fun ω =>
    tendsto_nhdsGT_of_monotone_real (fun ε => levyExp_nonneg _ ω) (hmonoψ ω),
    fun R hR hRe ω => ?_⟩
  show (⨅ k : ℕ, levyExp (L (sigmaEps d (1 / ((k : ℝ) + 1)))) (lin R ω)) =
    ⨅ k : ℕ, levyExp (L (sigmaEps d (1 / ((k : ℝ) + 1)))) ω
  congr 1
  funext k
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have h := (sim_general_conj hd hfam (sigmaEps_posDef hk) hR).1
  rw [act_sigmaEps_of_fix hR hRe] at h
  conv_lhs => rw [h]
  rw [levyExp_push, lin_transpose_lin_of_orth hR]

/-! ## Clause (5) -/

/-- **`prop:similarity-general-sandwich`(5)**, the sandwich: for `Σ ∈ PD(d)` with
`λ_max(Σ) = 1` and `Q ∈ O(d)` whose first column is a unit eigenvector of `Σ` for `1`, under the
first hypothesis of (4) `Q_*L_* ≤ L_Σ ≤ L_I` and `ψ_*(Qᵀω) ≤ ψ_Σ(ω) ≤ ψ_I(ω)`; under the second,
the inequalities between the exponents hold. -/
theorem sim_general_sandwich (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L) (S : Mat d) (hS : S.PosDef)
    (hmax : lamMax S = 1) (Q : Mat d) (hQ : Q ∈ orthSet d)
    (hQv : lin S (lin Q (ebasis ⟨0, by omega⟩)) = lin Q (ebasis ⟨0, by omega⟩)) :
    (HasIDLoewnerIncrements μ →
      (∀ Lstar : Measure (Rd d), IsRankOneLimit L Lstar → push Q Lstar ≤ L S ∧ L S ≤ L 1) ∧
      ∀ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar → ∀ ω : Rd d,
        ψstar (lin Qᵀ ω) ≤ levyExp (L S) ω ∧ levyExp (L S) ω ≤ levyExp (L 1) ω) ∧
    ((∀ S : Mat d, S.PosDef → C S = 0) → HasFiniteLoewnerIncrements μ →
      ∀ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar → ∀ ω : Rd d,
        ψstar (lin Qᵀ ω) ≤ levyExp (L S) ω ∧ levyExp (L S) ω ≤ levyExp (L 1) ω) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [fin_zero_eq (by omega)] at hQv
  have hSh := hS.isHermitian
  have hSI := loewnerLE_one_of_lamMax hSh hmax
  have hl := lamMin_pos hS
  -- the steps `QΣ_εQᵀ ≤ Σ`
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ lamMin S → ε ≤ 1 →
      (act Q (sigmaEps d ε)).PosDef ∧ loewnerLE (act Q (sigmaEps d ε)) S := fun ε hε hεl hε1 =>
    ⟨(posDef_act_iff (orthSet_subset_glSet hQ) _).2 (sigmaEps_posDef hε),
      sigmaEps_conj_le hSh hQ hQv hε hεl hε1⟩
  -- the exponents, under either hypothesis
  have hψ : ∀ hinc : (HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ)),
      ∀ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar → ∀ ω : Rd d,
        ψstar (lin Qᵀ ω) ≤ levyExp (L S) ω ∧ levyExp (L S) ω ≤ levyExp (L 1) ω := by
    intro hinc ψstar hψstar ω
    refine ⟨le_of_tendsto (hψstar (lin Qᵀ ω)) ?_,
      sim_general_mono hd hfam hinc hS PosDef.one hSI ω⟩
    filter_upwards [Ioo_mem_nhdsGT (lt_min hl one_pos)] with ε hε
    obtain ⟨hpd, hle⟩ := hstep ε hε.1 (hε.2.le.trans (min_le_left _ _))
      (hε.2.le.trans (min_le_right _ _))
    have h1 := sim_general_mono hd hfam hinc hpd hS hle ω
    rwa [(sim_general_conj hd hfam (sigmaEps_posDef hε.1) hQ).2] at h1
  refine ⟨fun hID => ⟨fun Lstar hLstar => ⟨?_, ?_⟩, hψ (Or.inl hID)⟩,
    fun hC hfin => hψ (Or.inr ⟨hC, hfin⟩)⟩
  · refine measure_le_of_boundedAway (push_orth_zero hQ hLstar.1) fun B hB hBa => ?_
    have hB' : MeasurableSet ((lin Q : Rd d → Rd d) ⁻¹' B) := (lin Q).continuous.measurable hB
    rw [push, Measure.map_apply (lin Q).continuous.measurable hB]
    refine le_of_tendsto (hLstar.2 _ hB' (preimage_lin_orth_boundedAway hQ hBa)) ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hl one_pos)] with ε hε
    obtain ⟨hpd, hle⟩ := hstep ε hε.1 (hε.2.le.trans (min_le_left _ _))
      (hε.2.le.trans (min_le_right _ _))
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ _ hpd hS hle
    have h1 := (sim_general_id_increment hd μ C L hfam _ _ hpd hS ρ hρ hρid heq).2.1
    rw [(sim_general_conj hd hfam (sigmaEps_posDef hε.1) hQ).1] at h1
    have h2 := Measure.le_iff'.1 h1 B
    rwa [push, Measure.map_apply (lin Q).continuous.measurable hB] at h2
  · obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ _ hS PosDef.one hSI
    exact (sim_general_id_increment hd μ C L hfam _ _ hS PosDef.one ρ hρ hρid heq).2.1

end AffineHemigroup
