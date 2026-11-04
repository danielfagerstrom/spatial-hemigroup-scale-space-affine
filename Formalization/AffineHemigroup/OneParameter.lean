/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.DiagonalRays
import AffineHemigroup.StableExponentCone
import AffineHemigroup.InvariantOrders

/-!
# `prop:one-parameter-families`: the families of one linear flow

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:one-parameter-families` and its child
`prop:one-parameter-stable-member`. Wave 2, group E, Q-0281. (1) the characterization by
`B`-self-decomposability; (2) the origin, by dominated convergence; (3) the curve of apertures,
through the derivative of `t ↦ ⟨ω, Σ(t)ω⟩`; (4) the Gaussian rides exactly the monotone curves;
(5) the products of self-decomposable laws on the axes, and the stable member.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace BoundedContinuousFunction

variable {d : ℕ}

/-! ## The flow -/

/-- `e^{-uB}e^{uB} = I`. -/
theorem mexp_neg_mul_mexp (B : Mat d) (u : ℝ) : mexp ((-u) • B) * mexp (u • B) = 1 := by
  rw [← mexp_add_smul, neg_add_cancel, zero_smul, mexp_zero]

/-- `e^{tBᵀ} = (e^{tB})ᵀ`. -/
theorem mexp_smul_transpose (B : Mat d) (t : ℝ) : mexp (t • Bᵀ) = (mexp (t • B))ᵀ := by
  unfold mexp
  rw [← transpose_smul, Matrix.exp_transpose]

/-! ## Clause (1) -/

/-- **`prop:one-parameter-families`(1)**, the characterization: probability measures `(μ_t)` with
(F1) `(e^{sB})_*μ_t = μ_{t+s}` and (F2) `μ_u = μ_0 * ρ_u` for `u > 0` have `μ_0`
`B`-self-decomposable, `μ_t = (e^{tB})_*μ_0`, and `μ_t = μ_s * (e^{sB})_*ρ_{t-s}` for `s < t`. -/
theorem one_parameter_families (_hd : 1 ≤ d) (B : Mat d) (μ : ℝ → Measure (Rd d))
    (hprob : ∀ t, IsProbabilityMeasure (μ t))
    (hF1 : ∀ s t : ℝ, push (mexp (s • B)) (μ t) = μ (t + s))
    (hF2 : ∀ u : ℝ, 0 < u → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ μ u = μ 0 ∗ ρ) :
    IsBSelfDecomposable B (μ 0) ∧ (∀ t : ℝ, μ t = push (mexp (t • B)) (μ 0)) ∧
      ∀ s t : ℝ, s < t → ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ → μ (t - s) = μ 0 ∗ ρ →
        μ t = μ s ∗ push (mexp (s • B)) ρ := by
  have hform : ∀ t : ℝ, μ t = push (mexp (t • B)) (μ 0) := fun t => by
    rw [hF1 t 0, zero_add]
  refine ⟨(isBSelfDecomposable_iff B _).2 fun u hu => ?_, hform, fun s t _ ρ hρ h => ?_⟩
  · obtain ⟨ρ, hρ, h⟩ := hF2 u hu
    haveI := hprob 0
    refine ⟨push (mexp ((-u) • B)) ρ, inferInstance, ?_⟩
    have h2 := congrArg (push (mexp ((-u) • B))) h
    rw [hform u, push_push, mexp_neg_mul_mexp, push_one, push_conv] at h2
    rw [neg_smul] at h2 ⊢
    exact h2
  · haveI := hprob 0
    have h1 := hF1 s (t - s)
    rw [sub_add_cancel] at h1
    rw [← h1, h, push_conv, hform s]

/-- **`prop:one-parameter-families`(1)**, the converse: for every `B`-self-decomposable law `μ_0`
the family `μ_t := (e^{tB})_*μ_0` satisfies (F1) and (F2). -/
theorem one_parameter_families_converse (_hd : 1 ≤ d) (B : Mat d) (μ0 : Measure (Rd d))
    [IsProbabilityMeasure μ0] (hsd : IsBSelfDecomposable B μ0) :
    let μ : ℝ → Measure (Rd d) := fun t => push (mexp (t • B)) μ0
    (∀ s t : ℝ, push (mexp (s • B)) (μ t) = μ (t + s)) ∧
      ∀ u : ℝ, 0 < u → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ μ u = μ 0 ∗ ρ := by
  intro μ
  refine ⟨fun s t => ?_, fun u hu => ?_⟩
  · simp only [μ]
    rw [push_push, ← mexp_add_smul, add_comm]
  · obtain ⟨ρ, hρ, h⟩ := (isBSelfDecomposable_iff B μ0).1 hsd u hu
    refine ⟨push (mexp (u • B)) ρ, inferInstance, ?_⟩
    simp only [μ]
    rw [zero_smul, mexp_zero, push_one]
    conv_lhs => rw [h]
    rw [push_conv, push_push, ← mexp_add_smul, add_neg_cancel, zero_smul, mexp_zero, push_one]

/-! ## Clause (2): the origin -/

/-- **`prop:one-parameter-families`(2)**, the origin: if `e^{tB} → 0` as `t → -∞` (that is,
`e^{-tB} → 0` as `t → ∞`, `IsExpContracting B`), then `μ_t → δ₀` weakly as `t → -∞`. -/
theorem one_parameter_origin (hd : 1 ≤ d) (B : Mat d) (μ : ℝ → Measure (Rd d))
    (hprob : ∀ t, IsProbabilityMeasure (μ t))
    (hF1 : ∀ s t : ℝ, push (mexp (s • B)) (μ t) = μ (t + s))
    (hF2 : ∀ u : ℝ, 0 < u → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ μ u = μ 0 ∗ ρ)
    (hB : IsExpContracting B) :
    ∀ f : Rd d →ᵇ ℝ, Tendsto (fun t => ∫ x, f x ∂(μ t)) atBot (𝓝 (f 0)) := by
  intro f
  haveI := hprob 0
  have hform := (one_parameter_families hd B μ hprob hF1 hF2).2.1
  -- `e^{tB} → 0` as `t → -∞`
  have hE : Tendsto (fun t : ℝ => mexp (t • B)) atBot (𝓝 0) := by
    have := hB.comp tendsto_neg_atBot_atTop
    refine this.congr fun t => ?_
    simp [Function.comp_apply, neg_neg]
  have hint : ∀ t, ∫ x, f x ∂(μ t) = ∫ x, f (lin (mexp (t • B)) x) ∂(μ 0) := by
    intro t
    rw [hform t, push, integral_map (lin _).continuous.aemeasurable
      f.continuous.aestronglyMeasurable]
  simp_rw [hint]
  have h0 : f 0 = ∫ _x, f 0 ∂(μ 0) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun t =>
      (f.continuous.comp (lin _).continuous).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun x => f.norm_coe_le_norm _
  · refine Eventually.of_forall fun x => ?_
    have hl : Continuous fun M : Mat d => lin M x := by
      have : (fun M : Mat d => lin M x) = fun M => WithLp.toLp 2 (M *ᵥ x.ofLp) := by
        funext M
        apply WithLp.ofLp_injective 2
        rw [ofLp_lin]
      rw [this]
      exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)
    have h := (f.continuous.comp hl).tendsto 0 |>.comp hE
    simp only [Function.comp_apply] at h
    have hz : lin (0 : Mat d) x = 0 := by
      apply WithLp.ofLp_injective 2
      rw [ofLp_lin]
      simp
    rwa [hz] at h

/-! ## Clause (3): the curve of apertures -/

/-- `t ↦ e^{tA}ω` has derivative `A e^{tA}ω` in `ℝ^d`. -/
theorem hasDerivAt_lin_mexp (A : Mat d) (ω : Rd d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => lin (mexp (u • A)) ω) (lin A (lin (mexp (t • A)) ω)) t := by
  have h := hasDerivAt_mexp_smul_mulVec A ω.ofLp t
  have hL := (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ).symm.hasFDerivAt.comp_hasDerivAt
    t h
  have e1 : (fun u : ℝ => lin (mexp (u • A)) ω) =
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ).symm ∘
        fun u => mexp (u • A) *ᵥ ω.ofLp := by
    funext u
    rfl
  have e2 : lin A (lin (mexp (t • A)) ω) =
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ).symm (A *ᵥ (mexp (t • A) *ᵥ ω.ofLp)) :=
    rfl
  rw [e1, e2]
  exact hL

/-- `⟨ω, Σ(t)ω⟩ = ⟨e^{tBᵀ}ω, Σ₀e^{tBᵀ}ω⟩` has derivative `⟨e^{tBᵀ}ω, Ce^{tBᵀ}ω⟩` with
`C = BΣ₀ + Σ₀Bᵀ`. -/
theorem hasDerivAt_quad_curve (B S0 : Mat d) (ω : Rd d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => quad (mexp (u • B) * S0 * mexp (u • Bᵀ)) ω)
      (quad (B * S0 + S0 * Bᵀ) (lin (mexp (t • Bᵀ)) ω)) t := by
  have hform : (fun u : ℝ => quad (mexp (u • B) * S0 * mexp (u • Bᵀ)) ω) =
      fun u => ⟪lin (mexp (u • Bᵀ)) ω, lin S0 (lin (mexp (u • Bᵀ)) ω)⟫ := by
    funext u
    have := quad_act (mexp (u • B)) S0 ω
    rw [act, ← mexp_smul_transpose] at this
    rw [this, quad]
  rw [hform]
  have hv := hasDerivAt_lin_mexp Bᵀ ω t
  have hSv := (lin S0).hasFDerivAt.comp_hasDerivAt t hv
  have h := hv.inner ℝ hSv
  set v := lin (mexp (t • Bᵀ)) ω
  have hval : ⟪v, lin S0 (lin Bᵀ v)⟫ + ⟪lin Bᵀ v, lin S0 v⟫ = quad (B * S0 + S0 * Bᵀ) v := by
    have h1 : ⟪lin Bᵀ v, lin S0 v⟫ = ⟪v, lin B (lin S0 v)⟫ := by
      rw [inner_lin_left, transpose_transpose]
    have h2 : quad (B * S0 + S0 * Bᵀ) v = ⟪v, lin B (lin S0 v)⟫ + ⟪v, lin S0 (lin Bᵀ v)⟫ := by
      unfold quad
      rw [lin_add, lin_mul, lin_mul]
      rw [ContinuousLinearMap.add_apply, inner_add_right]
      rfl
    rw [h1, h2, add_comm]
  exact h.congr_deriv hval

/-- **`prop:one-parameter-families`(3)**, the curve of apertures: for `Σ₀ ∈ PD(d)` and
`Σ(t) := e^{tB}Σ₀e^{tBᵀ}`, `Σ(s) ≤ Σ(t)` for all `s ≤ t` if and only if `BΣ₀ + Σ₀Bᵀ ∈ PSD(d)`; and
`Σ(t) → 0` as `t → -∞` if and only if `e^{tB} → 0`. -/
theorem one_parameter_curve (_hd : 1 ≤ d) (B S0 : Mat d) (hS0 : S0.PosDef) :
    let Sig : ℝ → Mat d := fun t => mexp (t • B) * S0 * mexp (t • Bᵀ)
    ((∀ s t : ℝ, s ≤ t → loewnerLE (Sig s) (Sig t)) ↔ (B * S0 + S0 * Bᵀ).PosSemidef) ∧
      (Tendsto Sig atBot (𝓝 0) ↔ Tendsto (fun t : ℝ => mexp (t • B)) atBot (𝓝 0)) := by
  intro Sig
  have hS0t : S0ᵀ = S0 := by
    have := hS0.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hSigsym : ∀ t, (Sig t)ᵀ = Sig t := by
    intro t
    simp only [Sig, Matrix.transpose_mul, hS0t, mexp_smul_transpose, transpose_transpose,
      Matrix.mul_assoc]
  have hCsym : (B * S0 + S0 * Bᵀ)ᵀ = B * S0 + S0 * Bᵀ := by
    rw [transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hS0t, transpose_transpose,
      add_comm]
  have hherm : ∀ M : Mat d, Mᵀ = M → M.IsHermitian := fun M h => by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h
  have hpsd_of : ∀ M : Mat d, Mᵀ = M → (∀ ω : Rd d, 0 ≤ quad M ω) → M.PosSemidef := by
    intro M hM h
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hherm M hM) fun x => ?_
    have := h (WithLp.toLp 2 x)
    rw [quad_eq_dotProduct] at this
    simpa using this
  refine ⟨⟨fun hmono => ?_, fun hC s t hst => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine hpsd_of _ hCsym fun ω => ?_
    have hd := hasDerivAt_quad_curve B S0 ω 0
    rw [zero_smul, mexp_zero, lin_one] at hd
    refine hd.nonneg_of_monotone fun s t hst => ?_
    have := quad_nonneg (hmono s t hst) ω
    rw [quad_sub] at this
    linarith
  · -- the quadratic form is monotone along the curve
    refine hpsd_of _ (by rw [transpose_sub, hSigsym, hSigsym]) fun ω => ?_
    rw [quad_sub, sub_nonneg]
    have hmon : Monotone fun u : ℝ => quad (Sig u) ω := by
      refine monotone_of_deriv_nonneg (fun u => (hasDerivAt_quad_curve B S0 ω u).differentiableAt)
        fun u => ?_
      rw [(hasDerivAt_quad_curve B S0 ω u).deriv]
      exact quad_nonneg hC _
    exact hmon hst
  · -- `e^{tB} = (e^{tB}Σ₀^{1/2})Σ₀^{-1/2}` and `Σ(t) = MMᵀ` with `M = e^{tB}Σ₀^{1/2}`
    set R := msqrt S0 with hR
    have hRR : R * R = S0 := msqrt_mul_self hS0.posSemidef
    have hRt : Rᵀ = R := msqrt_transpose S0
    have hRu : IsUnit R := isUnit_msqrt hS0
    set M : ℝ → Mat d := fun t => mexp (t • B) * R with hMdef
    have hM : Tendsto M atBot (𝓝 0) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      -- `(MMᵀ)ᵢᵢ = ∑ₖ Mᵢₖ² → 0`
      have hii : Tendsto (fun t => Sig t i i) atBot (𝓝 0) := by
        have hc : Continuous fun N : Mat d => N i i := continuous_id.matrix_elem i i
        have h1 : Tendsto (fun t => Sig t i i) atBot (𝓝 ((0 : Mat d) i i)) := (hc.tendsto 0).comp h
        simpa using h1
      have heq : ∀ t, Sig t i i = ∑ k, M t i k ^ 2 := by
        intro t
        have hS : Sig t = M t * (M t)ᵀ := by
          simp only [Sig, hMdef, mexp_smul_transpose, Matrix.transpose_mul, hRt]
          rw [← hRR]
          simp only [Matrix.mul_assoc]
        rw [hS, Matrix.mul_apply]
        simp only [transpose_apply, sq]
      have hle : ∀ t, M t i j ^ 2 ≤ Sig t i i := by
        intro t
        rw [heq]
        exact Finset.single_le_sum (f := fun k => M t i k ^ 2) (fun k _ => sq_nonneg _)
          (Finset.mem_univ j)
      have hsq : Tendsto (fun t => M t i j ^ 2) atBot (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hii
          (fun t => sq_nonneg _) hle
      have habs : Tendsto (fun t => |M t i j|) atBot (𝓝 0) := by
        have := hsq.sqrt
        simpa [Real.sqrt_sq_eq_abs] using this
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
    have hcont : Continuous fun M : Mat d => M * R⁻¹ := continuous_id.matrix_mul continuous_const
    have := (hcont.tendsto 0).comp hM
    rw [Matrix.zero_mul] at this
    refine this.congr fun t => ?_
    show mexp (t • B) * R * R⁻¹ = mexp (t • B)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hRu),
      Matrix.mul_one]
  · have hT : Tendsto (fun t : ℝ => mexp (t • Bᵀ)) atBot (𝓝 0) := by
      have hc : Continuous fun M : Mat d => Mᵀ := continuous_id.matrix_transpose
      have h1 : Tendsto (fun t => (mexp (t • B))ᵀ) atBot (𝓝 ((0 : Mat d)ᵀ)) := (hc.tendsto 0).comp h
      rw [transpose_zero] at h1
      exact h1.congr fun t => (mexp_smul_transpose B t).symm
    have hcont : Continuous fun p : Mat d × Mat d => p.1 * S0 * p.2 :=
      (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd
    have := (hcont.tendsto ((0 : Mat d), (0 : Mat d))).comp (h.prodMk_nhds hT)
    have h0 : (0 : Mat d) * S0 * 0 = 0 := by simp
    rw [h0] at this
    exact this

/-! ## Clause (4): the Gaussian -/

/-- `A · (B · Σ) = (AB) · Σ`. -/
theorem act_act_mul (A B S : Mat d) : act A (act B S) = act (A * B) S := by
  simp only [act, Matrix.transpose_mul, Matrix.mul_assoc]

/-- **`prop:one-parameter-families`(4)**, the Gaussian rides exactly the monotone curves: for
`b > 0`, `μ_t := N(0, 2bΣ(t))` satisfies (F1), and it satisfies (F2) if and only if
`BΣ₀ + Σ₀Bᵀ ∈ PSD(d)`. -/
theorem one_parameter_gaussian (hd : 1 ≤ d) (B S0 : Mat d) (hS0 : S0.PosDef) (b : ℝ) (hb : 0 < b) :
    let Sig : ℝ → Mat d := fun t => mexp (t • B) * S0 * mexp (t • Bᵀ)
    let μ : ℝ → Measure (Rd d) := fun t => multivariateGaussian 0 ((2 * b) • Sig t)
    (∀ s t : ℝ, push (mexp (s • B)) (μ t) = μ (t + s)) ∧
      ((∀ u : ℝ, 0 < u → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ μ u = μ 0 ∗ ρ) ↔
        (B * S0 + S0 * Bᵀ).PosSemidef) := by
  intro Sig μ
  have hSig : ∀ t, Sig t = act (mexp (t • B)) S0 := fun t => by
    simp only [Sig, act, mexp_smul_transpose]
  have hSigpsd : ∀ t, (Sig t).PosSemidef := fun t => by
    rw [hSig]; exact posSemidef_act _ hS0.posSemidef
  have hpsd : ∀ t, ((2 * b) • Sig t).PosSemidef := fun t => (hSigpsd t).smul (by positivity)
  have hcf : ∀ t ω, charFun (μ t) ω = ((Real.exp (-(quad ((2 * b) • Sig t) ω / 2)) : ℝ) : ℂ) :=
    fun t ω => charFun_multivariateGaussian_zero (hpsd t) ω
  have hSigadd : ∀ s t, act (mexp (s • B)) (Sig t) = Sig (t + s) := by
    intro s t
    rw [hSig, hSig, act_act_mul, ← mexp_add_smul, add_comm]
  have hF1 : ∀ s t : ℝ, push (mexp (s • B)) (μ t) = μ (t + s) := by
    intro s t
    refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, hcf, hcf, quad_smul, quad_smul, ← quad_act, hSigadd]
  have hcurve := (one_parameter_curve hd B S0 hS0).1
  refine ⟨hF1, ⟨fun hF2 => ?_, fun hC u hu => ?_⟩⟩
  · refine hcurve.1 fun s t hst => ?_
    rcases hst.eq_or_lt with rfl | hlt
    · simp [loewnerLE, PosSemidef.zero]
    -- `Σ(t-s) - Σ₀ ⪰ 0` from `|ρ̂| ≤ 1`
    obtain ⟨ρ, hρ, h⟩ := hF2 (t - s) (sub_pos.2 hlt)
    have hge : (Sig (t - s) - Sig 0).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
      · have h1 := (hSigpsd (t - s)).isHermitian
        have h2 := (hSigpsd 0).isHermitian
        exact h1.sub h2
      · by_contra hneg
        push Not at hneg
        set ω : Rd d := WithLp.toLp 2 x with hω
        have hq : quad (Sig (t - s) - Sig 0) ω < 0 := by
          rw [quad_eq_dotProduct]; simpa [hω] using hneg
        have h2 := congrArg (fun m => charFun m ω) h
        rw [charFun_conv, hcf, hcf] at h2
        have hne : ((Real.exp (-(quad ((2 * b) • Sig 0) ω / 2)) : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.exp_pos _).ne'
        have hρω : charFun ρ ω = ((Real.exp (-(quad ((2 * b) • Sig (t - s)) ω / 2) +
            quad ((2 * b) • Sig 0) ω / 2) : ℝ) : ℂ) := by
          set q1 := quad ((2 * b) • Sig (t - s)) ω
          set q0 := quad ((2 * b) • Sig 0) ω
          have hE0 : ((Real.exp (q0 / 2) : ℝ) : ℂ) * ((Real.exp (-(q0 / 2)) : ℝ) : ℂ) = 1 := by
            rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
              Complex.ofReal_one]
          rw [Real.exp_add, Complex.ofReal_mul]
          calc charFun ρ ω = ((Real.exp (q0 / 2) : ℝ) : ℂ) *
                (((Real.exp (-(q0 / 2)) : ℝ) : ℂ) * charFun ρ ω) := by
                rw [← mul_assoc, hE0, one_mul]
            _ = _ := by rw [← h2]; ring
        have hn := norm_charFun_le_one (μ := ρ) ω
        rw [hρω, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff,
          quad_smul, quad_smul] at hn
        rw [quad_sub] at hq
        nlinarith
    have heq : Sig t - Sig s = act (mexp (s • B)) (Sig (t - s) - Sig 0) := by
      rw [← act_sub, hSigadd, hSigadd, sub_add_cancel, zero_add]
    rw [loewnerLE, heq]
    exact posSemidef_act _ hge
  · have hmono := hcurve.2 hC 0 u hu.le
    have hρpsd : ((2 * b) • (Sig u - Sig 0)).PosSemidef := hmono.smul (by positivity)
    refine ⟨multivariateGaussian 0 ((2 * b) • (Sig u - Sig 0)), inferInstance, ?_⟩
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, hcf, hcf, charFun_multivariateGaussian_zero hρpsd, ← Complex.ofReal_mul,
      ← Real.exp_add, quad_smul, quad_smul, quad_smul, quad_sub]
    congr 2
    ring

/-! ## Clause (5): two kinds of member -/

/-- **`prop:one-parameter-families`(5)**, first sentence: if `B = diag(b₁, …, b_d)` with every
`bᵢ > 0`, every product `ν₁ ⊗ ⋯ ⊗ ν_d` of self-decomposable laws on `ℝ` is
`B`-self-decomposable. -/
theorem one_parameter_products (_hd : 1 ≤ d) (b : Fin d → ℝ) (hb : ∀ i, 0 < b i)
    (ν : Fin d → Measure ℝ) (hν : ∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) :
    IsBSelfDecomposable (diagonal b) (prodLaw ν) := by
  rw [isBSelfDecomposable_iff]
  intro t ht
  have hprob : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).1
  set c : Fin d → ℝ := fun i => Real.exp (-t * b i) with hc
  have hc0 : ∀ i, 0 < c i := fun i => Real.exp_pos _
  have hc1 : ∀ i, c i < 1 := fun i => by
    rw [hc, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith [hb i])
  have hexp : mexp (-t • diagonal b) = diagonal c := by
    unfold mexp
    rw [← diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext i
    simp [hc, Real.exp_eq_exp_ℝ, smul_eq_mul]
  choose ρ hρ hfac using fun i =>
    haveI := (hν i).1
    (isSelfDecomposable_iff_charFun (ν i)).1 (hν i).2 (c i) (hc0 i) (hc1 i)
  refine ⟨prodLaw ρ, isProbabilityMeasure_prodLaw ρ hρ, ?_⟩
  rw [hexp, push_diagonal_prodLaw _ _ hprob, ← prodLaw_conv _ _
    (fun i => haveI := hprob i; isProbabilityMeasure_dilLine _ _) hρ]
  congr 1
  funext i
  haveI := hprob i
  haveI := hρ i
  haveI := isProbabilityMeasure_dilLine (c i) (ν i)
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_conv, charFun_dilLine, hfac i ξ, smul_eq_mul]

/-- `S_α(I)` is rotation invariant: its transform `e^{-|ω|^α}` is radial. -/
theorem ellipticalStable_one_charFun {α : ℝ} {μ : Measure (Rd d)} (hμ : IsEllipticalStable α 1 μ)
    (ω : Rd d) : charFun μ ω = ((Real.exp (-(‖ω‖ ^ α)) : ℝ) : ℂ) := by
  rw [hμ.2, stableExp, quad_one, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  push_cast
  rw [show (2 : ℝ) * (α / 2) = α by ring]

/-- **`prop:one-parameter-stable-member`** (`prop:one-parameter-families`(5), second sentence): if
`d ≥ 2`, `0 < α < 2` and `(d+α) λ_min(sym B) ≥ tr B`, then `S_α(I)` is `B`-self-decomposable and is
not a product law in any orthonormal frame. -/
theorem one_parameter_stable_member (hd : 2 ≤ d) (B : Mat d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hK : B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B)) (μ : Measure (Rd d))
    (hμ : IsEllipticalStable α 1 μ) :
    IsBSelfDecomposable B μ ∧
      ¬ ∃ Q ∈ orthSet d, ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i)) ∧
        μ = push Q (prodLaw ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := hμ.1
  refine ⟨(stable_exponent_cone hα0 hα2 B μ hμ).2 hK, ?_⟩
  rintro ⟨Q, hQ, ν, hν, hμQ⟩
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  haveI := isProbabilityMeasure_prodLaw ν hν
  -- `μ` is rotation invariant, so the product law is `μ` itself
  have hrot : IsRotationInvariant μ := by
    intro P hP
    have hPP : P * Pᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hP
    refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, ellipticalStable_one_charFun hμ, ellipticalStable_one_charFun hμ]
    have hn : ‖lin Pᵀ ω‖ = ‖ω‖ := by
      have h1 := quad_act P 1 ω
      rw [act, Matrix.mul_one, hPP, quad_one, quad_one] at h1
      have := congrArg Real.sqrt h1
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
      exact this.symm
    rw [hn]
  have hP : prodLaw ν = μ := by
    have h := congrArg (push Qᵀ) hμQ
    rw [push_push, transpose_mul_self_of_mul_transpose hQQ, push_one] at h
    rw [← h, hrot _ (transpose_mem_orthSet hQ)]
  -- read the transforms at `eᵢ` and at `e₀ + e₁`
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have hφ0 : ∀ j, charFun (ν j) 0 = 1 := fun j => by haveI := hν j; simp [charFun_zero]
  have hνi : ∀ j, charFun (ν j) 1 = ((Real.exp (-1)) : ℂ) := by
    intro j
    have h := ellipticalStable_one_charFun hμ ((1 : ℝ) • ebasis j)
    rw [← hP, charFun_prodLaw _ hν, prod_smul_ebasis (fun j => charFun (ν j)) hφ0] at h
    rw [h]
    simp [ebasis]
  have h2 := ellipticalStable_one_charFun hμ ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1)
  rw [← hP, charFun_prodLaw _ hν, Finset.prod_eq_mul i0 i1 h01] at h2
  · have e0 : ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1) i0 = 1 := by
      simp [ebasis, Ne.symm h01]
    have e1 : ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1) i1 = 1 := by
      simp [ebasis, h01]
    rw [e0, e1, hνi, hνi, norm_smul_ebasis_add_smul_ebasis h01,
      show (1 : ℝ) ^ 2 + 1 ^ 2 = 2 by norm_num, ← Complex.ofReal_mul] at h2
    have h3 := Complex.ofReal_injective h2
    rw [← Real.exp_add] at h3
    have h4 := Real.exp_injective h3
    have h5 : Real.sqrt 2 ^ α = 2 := by linarith
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)] at h5
    have h6 : (1 / 2 * α) * Real.log 2 = Real.log 2 := by
      rw [← Real.log_rpow (by norm_num), h5]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 1 / 2 * α = 1 := by
      have := mul_right_cancel₀ hlog.ne' (h6.trans (one_mul _).symm)
      exact this
    linarith
  · intro c _ hc
    have : ((1 : ℝ) • ebasis i0 + (1 : ℝ) • ebasis i1) c = 0 := by
      simp [ebasis, hc.1, hc.2]
    rw [this, hφ0]
  · exact fun h => absurd (Finset.mem_univ _) h
  · exact fun h => absurd (Finset.mem_univ _) h

end AffineHemigroup
