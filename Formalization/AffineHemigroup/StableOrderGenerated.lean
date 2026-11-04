/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ConeOrders
import AffineHemigroup.ConeOrdersPSD
import AffineHemigroup.AnisotropyConverse

/-!
# `prop:stable-order-generated`: the stable step cone is the order of the cone field `C_α`

Blueprint: `blueprint/src/parts/05-wedges.tex`, `prop:stable-order-generated` (wave 2, group F,
Q-0281), by the entry-free route of the author's decision of 2026-10-05: no declaration here reads
`thm:cone-orders`(1)'s converse, so none spends ledger A9.

* **The map `Φ_α(Σ) = (det Σ)^{-1/(d+α)}Σ` along a curve.** If `γ` is absolutely continuous in
  `PD(d)`, so is `Φ_α ∘ γ` (`det ∘ γ` is a polynomial in the entries, bounded away from `0` on
  `[0,1]`), and where the entries of `γ` are differentiable, `(Φ_α ∘ γ)' = (det γ)^s γ^{1/2}(Y +
  s (tr Y) I)γ^{1/2}` with `s = -1/(d+α)` and `Y = γ^{-1/2}γ'γ^{-1/2}` (Jacobi's formula at a point, by
  the Leibniz expansion of `det(γ(t)⁻¹γ(u))` around `u = t`). For `Y ∈ C_α` this is positive
  semidefinite, and for `Y ∈ C₀ = {cI}`, at `α = 0`, it is `0`.
* **A curve with positive semidefinite derivative is Loewner-monotone**: each `⟨x, η(t)x⟩` is
  absolutely continuous with nonnegative derivative almost everywhere (Mathlib's
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`); a curve with derivative `0` almost
  everywhere is constant (`const_of_ae_hasDerivAt_zero`).
* So a `C_α`-causal curve has `Φ_α(γ(0)) ≤ Φ_α(γ(1))`, which is `λ_min(M)^{d+α} ≥ det M`; at
  `α = 0` the shape is constant along it; a `PSD(d)`-causal curve is Loewner-monotone. The
  converses are the geodesic of `thm:cone-orders`(1), which spends nothing. Clause (2) reads
  `ψ_α(e^{tB}) = e^{t(B + s tr B I)}` and the tangent wedge `{B : B + Bᵀ ≥ 0}` of `{A : AAᵀ ≥ I}`.
-/

namespace AffineHemigroup

open Matrix Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace MatrixOrder

variable {d : ℕ}

/-! ## Absolute continuity: linear combinations, products, and `x ↦ x^s` -/

/-- A linear combination of absolutely continuous functions is absolutely continuous. -/
theorem AbsolutelyContinuousOnInterval.linear_comb {ι : Type*} [Fintype ι] {fs : ι → ℝ → ℝ}
    {a b : ℝ} (c : ι → ℝ) (hfs : ∀ j, AbsolutelyContinuousOnInterval (fs j) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ j, c j * fs j t) a b := by
  refine AbsolutelyContinuousOnInterval.of_dominated hfs (K := ∑ j, |c j|) fun s _ t _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun k => |c k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ j)) (abs_nonneg _)

/-- A finite product of absolutely continuous functions is absolutely continuous. -/
theorem AbsolutelyContinuousOnInterval.finset_prod {ι : Type*} (s : Finset ι)
    {fs : ι → ℝ → ℝ} {a b : ℝ} (hfs : ∀ j ∈ s, AbsolutelyContinuousOnInterval (fs j) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∏ j ∈ s, fs j t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
      (LipschitzWith.const (α := ℝ) (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    simpa using hc
  | insert x s hx ih =>
    have h1 := hfs x (Finset.mem_insert_self x s)
    have h2 := ih fun j hj => hfs j (Finset.mem_insert_of_mem hj)
    have h3 := h1.fun_mul h2
    have he : (fun t => ∏ j ∈ insert x s, fs j t) = fun t => fs x t * ∏ j ∈ s, fs j t := by
      funext t
      rw [Finset.prod_insert hx]
    rw [he]
    exact h3

/-- `x ↦ x^s` is Lipschitz on `[m, M]`, `0 < m`. -/
theorem abs_rpow_sub_rpow_le {m M x y : ℝ} (s : ℝ) (hm : 0 < m) (hx : x ∈ Icc m M)
    (hy : y ∈ Icc m M) :
    |x ^ s - y ^ s| ≤ |s| * (m ^ (s - 1) + M ^ (s - 1)) * |x - y| := by
  have hder : ∀ z ∈ Icc m M, HasDerivWithinAt (fun z : ℝ => z ^ s) (s * z ^ (s - 1)) (Icc m M) z :=
    fun z hz => (Real.hasDerivAt_rpow_const (Or.inl (hm.trans_le hz.1).ne')).hasDerivWithinAt
  have hbound : ∀ z ∈ Icc m M, ‖s * z ^ (s - 1)‖ ≤ |s| * (m ^ (s - 1) + M ^ (s - 1)) := by
    intro z hz
    have hz0 : 0 < z := hm.trans_le hz.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases le_total 0 (s - 1) with h | h
    · have := Real.rpow_le_rpow hz0.le hz.2 h
      have := Real.rpow_nonneg hm.le (s - 1)
      linarith
    · have := Real.rpow_le_rpow_of_nonpos hm hz.1 h
      have := Real.rpow_nonneg (hm.le.trans (hz.1.trans hz.2)) (s - 1)
      linarith
  have := (convex_Icc m M).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound hy hx
  simpa [Real.norm_eq_abs] using this

/-! ## Jacobi's formula at a point -/

/-- **The derivative of `det` at a curve through `I`**: if `N(t) = I` and the entries of `N` have
derivatives `N'` at `t`, then `det ∘ N` has derivative `tr N'` there (the Leibniz expansion). -/
theorem hasDerivAt_det_of_eq_one {N : ℝ → Mat d} {N' : Mat d} {t : ℝ} (h1 : N t = 1)
    (hN : ∀ i j, HasDerivAt (fun u => N u i j) (N' i j) t) :
    HasDerivAt (fun u => (N u).det) N'.trace t := by
  have hfun : (fun u => (N u).det) = fun u => ∑ σ : Equiv.Perm (Fin d),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, N u (σ i) i := by
    funext u; rw [det_apply']
  rw [hfun]
  have hprod : ∀ σ : Equiv.Perm (Fin d), HasDerivAt (fun u => ∏ i, N u (σ i) i)
      (∑ i, (∏ j ∈ Finset.univ.erase i, N t (σ j) j) • N' (σ i) i) t := fun σ =>
    HasDerivAt.fun_finsetProd fun i _ => hN (σ i) i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => (hprod σ).const_mul
    (Equiv.Perm.sign σ : ℝ)
  refine hsum.congr_deriv ?_
  simp only [h1, prod_erase_one_perm, smul_eq_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin d))]
  · simp [trace]
  · intro σ _ hσ
    simp [hσ]
  · simp

/-- **Jacobi's formula at a point**: `(det γ)'(t) = det γ(t) · tr(γ(t)⁻¹γ'(t))`. -/
theorem hasDerivAt_det_curve {γ : ℝ → Mat d} {γ' : Mat d} {t : ℝ} (ht : IsUnit (γ t).det)
    (hder : ∀ i j, HasDerivAt (fun u => γ u i j) (γ' i j) t) :
    HasDerivAt (fun u => (γ u).det) ((γ t).det * ((γ t)⁻¹ * γ').trace) t := by
  set N : ℝ → Mat d := fun u => (γ t)⁻¹ * γ u with hN
  have hN1 : N t = 1 := Matrix.nonsing_inv_mul _ ht
  have hNd : ∀ i j, HasDerivAt (fun u => N u i j) (((γ t)⁻¹ * γ') i j) t := by
    intro i j
    simp only [hN, Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hder k j).const_mul _
  have hdet := hasDerivAt_det_of_eq_one hN1 hNd
  have hfun : (fun u => (γ u).det) = fun u => (γ t).det * (N u).det := by
    funext u
    simp only [hN]
    rw [← det_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
  rw [hfun]
  exact hdet.const_mul _

/-- `tr(Σ⁻¹ Σ^{1/2}YΣ^{1/2}) = tr Y`. -/
theorem trace_inv_mul_msqrt_conj {S : Mat d} (hS : S.PosDef) (Y : Mat d) :
    (S⁻¹ * (msqrt S * Y * msqrt S)).trace = Y.trace := by
  have hinv : S⁻¹ = (msqrt S)⁻¹ * (msqrt S)⁻¹ := by
    conv_lhs => rw [← msqrt_mul_self hS.posSemidef]
    exact Matrix.mul_inv_rev _ _
  have h : msqrt S * S⁻¹ * msqrt S = 1 := by
    rw [hinv, ← Matrix.mul_assoc, msqrt_mul_inv hS, Matrix.one_mul, msqrt_inv_mul hS]
  rw [show S⁻¹ * (msqrt S * Y * msqrt S) = (S⁻¹ * msqrt S * Y) * msqrt S by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    h, Matrix.one_mul]

/-! ## `Φ_s(Σ) = (det Σ)^s Σ` along a curve -/

/-- **The derivative of `Φ_s ∘ γ`** where the entries of `γ` are differentiable:
`(det γ)^s (γ' + s tr(γ⁻¹γ') γ)`. -/
theorem hasDerivAt_phi_curve {γ : ℝ → Mat d} {γ' : Mat d} {t : ℝ} (hpd : (γ t).PosDef)
    (hder : ∀ i j, HasDerivAt (fun u => γ u i j) (γ' i j) t) (s : ℝ) (i j : Fin d) :
    HasDerivAt (fun u => ((γ u).det ^ s • γ u) i j)
      ((γ t).det ^ s * (γ' i j + s * ((γ t)⁻¹ * γ').trace * γ t i j)) t := by
  have hU : IsUnit (γ t).det := (isUnit_iff_isUnit_det _).1 hpd.isUnit
  have hD := hasDerivAt_det_curve hU hder
  have hpos := hpd.det_pos
  have hR := (hD.rpow_const (p := s) (Or.inl hpos.ne')).mul (hder i j)
  have hfun : (fun u => ((γ u).det ^ s • γ u) i j) = fun u => (γ u).det ^ s * γ u i j := by
    funext u
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  refine hR.congr_deriv ?_
  rw [Real.rpow_sub_one hpos.ne']
  field_simp
  ring

/-- Entries of `Φ_s ∘ γ` are absolutely continuous on `[0,1]` when those of `γ` are and `γ` is
positive definite there. -/
theorem absolutelyContinuous_phi_curve {γ : ℝ → Mat d}
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun t => γ t i j) 0 1)
    (hpd : ∀ t ∈ Icc (0 : ℝ) 1, (γ t).PosDef) (s : ℝ) (i j : Fin d) :
    AbsolutelyContinuousOnInterval (fun u => ((γ u).det ^ s • γ u) i j) 0 1 := by
  -- `det ∘ γ` is a polynomial in the entries
  have hdet : AbsolutelyContinuousOnInterval (fun u => (γ u).det) 0 1 := by
    have hfun : (fun u => (γ u).det) = fun u => ∑ σ : Equiv.Perm (Fin d),
        (Equiv.Perm.sign σ : ℝ) * ∏ k, γ u (σ k) k := by
      funext u; rw [det_apply']
    rw [hfun]
    exact AbsolutelyContinuousOnInterval.linear_comb (fun σ => (Equiv.Perm.sign σ : ℝ))
      fun σ => AbsolutelyContinuousOnInterval.finset_prod _ fun k _ => hac (σ k) k
  have hcont : ContinuousOn (fun u => (γ u).det) (Icc 0 1) := by
    have := hdet.continuousOn
    rwa [uIcc_of_le zero_le_one] at this
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  obtain ⟨u₁, hu₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hcont
  set m := (γ u₀).det
  set M := (γ u₁).det
  have hm : 0 < m := (hpd u₀ hu₀).det_pos
  have hrange : ∀ u ∈ Icc (0 : ℝ) 1, (γ u).det ∈ Icc m M := fun u hu => ⟨hmin hu, hmax hu⟩
  have hpow : AbsolutelyContinuousOnInterval (fun u => (γ u).det ^ s) 0 1 := by
    refine AbsolutelyContinuousOnInterval.of_dominated (fs := fun _ : Unit => fun u => (γ u).det)
      (K := |s| * (m ^ (s - 1) + M ^ (s - 1))) (fun _ => hdet) fun u hu v hv => ?_
    rw [uIcc_of_le zero_le_one] at hu hv
    simpa using abs_rpow_sub_rpow_le s hm (hrange u hu) (hrange v hv)
  have hfun : (fun u => ((γ u).det ^ s • γ u) i j) = fun u => (γ u).det ^ s * γ u i j := by
    funext u
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  exact hpow.fun_mul (hac i j)

/-! ## Monotone and constant curves -/

theorem quad_eq_sum (A : Mat d) (ω : Rd d) : quad A ω = ∑ a, ∑ b, (ω a * ω b) * A a b := by
  rw [quad_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem posSemidef_of_quad_nonneg {A : Mat d} (hA : A.IsHermitian) (h : ∀ ω : Rd d, 0 ≤ quad A ω) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
  have := h (WithLp.toLp 2 x)
  rw [quad_eq_dotProduct] at this
  simpa using this

/-- **A curve with positive semidefinite derivative almost everywhere is Loewner-monotone.** -/
theorem loewnerLE_of_ae_deriv {η : ℝ → Mat d}
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun t => η t i j) 0 1)
    (h0 : (η 0).IsHermitian) (h1 : (η 1).IsHermitian)
    (hder : ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (∀ i j, DifferentiableAt ℝ (fun s => η s i j) t) →
      (mderiv η t).PosSemidef) :
    loewnerLE (η 0) (η 1) := by
  refine posSemidef_of_quad_nonneg (h1.sub h0) fun ω => ?_
  have hfsum : (fun t => quad (η t) ω) =
      fun t => ∑ p : Fin d × Fin d, (ω p.1 * ω p.2) * η t p.1 p.2 := by
    funext t
    rw [quad_eq_sum, Fintype.sum_prod_type]
  have hlc := AbsolutelyContinuousOnInterval.linear_comb (ι := Fin d × Fin d) (a := 0) (b := 1)
    (fs := fun p t => η t p.1 p.2) (fun p => ω p.1 * ω p.2) (fun p => hac p.1 p.2)
  have hac' : AbsolutelyContinuousOnInterval (fun t => quad (η t) ω) 0 1 := by
    rw [hfsum]
    exact hlc
  have hint := hac'.integral_deriv_eq_sub
  have hdiffs : ∀ᵐ s : ℝ, ∀ p : Fin d × Fin d, s ∈ uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun u => η u p.1 p.2) s :=
    ae_all_iff.2 fun p => (hac p.1 p.2).ae_differentiableAt
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..1, deriv (fun t => quad (η t) ω) s := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hdiffs, hder] with s hs1 hs2 hsI
    have hd : ∀ i j, DifferentiableAt ℝ (fun u => η u i j) s := fun i j =>
      hs1 (i, j) (by rw [uIcc_of_le zero_le_one]; exact hsI)
    have hpsd := hs2 hsI hd
    have hD : HasDerivAt (fun t => quad (η t) ω) (quad (mderiv η s) ω) s := by
      rw [hfsum, quad_eq_sum, ← Fintype.sum_prod_type']
      exact HasDerivAt.fun_sum fun p _ => ((hd p.1 p.2).hasDerivAt).const_mul _
    rw [Pi.zero_apply, hD.deriv]
    exact quad_nonneg hpsd ω
  have : quad (η 1) ω - quad (η 0) ω ≥ 0 := by rw [← hint]; exact hnonneg
  rw [quad_sub]
  linarith

/-- **A curve with derivative `0` almost everywhere is constant.** -/
theorem eq_of_ae_deriv_zero {η : ℝ → Mat d}
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun t => η t i j) 0 1)
    (hder : ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ i j, HasDerivAt (fun s => η s i j) 0 t) :
    η 0 = η 1 := by
  ext i j
  have hae : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (fun t => η t i j) 0 x := by
    filter_upwards [hder] with x hx hxI
    exact hx (by rwa [uIcc_of_le zero_le_one] at hxI) i j
  obtain ⟨c, hc⟩ := (hac i j).const_of_ae_hasDerivAt_zero hae
  rw [hc 0 (by simp), hc 1 (by simp)]

/-! ## The cones `C_α` -/

theorem lamMin_add_ge [NeZero d] {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    lamMin X + lamMin Y ≤ lamMin (X + Y) := by
  refine (le_lamMin_iff (hX.add hY) _).2 fun x hx => ?_
  rw [quad_add]
  exact add_le_add (lamMin_le_inner hX hx) (lamMin_le_inner hY hx)

theorem lamMin_conj_orth [NeZero d] {Q : Mat d} (hQ : Q ∈ orthSet d) {X : Mat d}
    (hX : X.IsHermitian) : lamMin (Q * X * Qᵀ) = lamMin X := by
  have hQX : (Q * X * Qᵀ).IsHermitian := by
    have := isHermitian_of_isSymm (d := d) (X := Q * X * Qᵀ) (by
      rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose,
        (isSymm_of_isHermitian hX).eq, Matrix.mul_assoc])
    exact this
  rw [lamMin_eq_eigUp_zero hQX, lamMin_eq_eigUp_zero hX, eigUp_conj_orth (orth_mul_transpose hQ)]

theorem trace_conj_orth {Q : Mat d} (hQ : Q ∈ orthSet d) (X : Mat d) :
    (Q * X * Qᵀ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, orth_transpose_mul hQ, Matrix.one_mul]

theorem posSemidef_conj_orth {Q : Mat d} {X : Mat d} (hX : X.PosSemidef) :
    (Q * X * Qᵀ).PosSemidef := by
  have := hX.mul_mul_conjTranspose_same Q
  rwa [conjTranspose_eq_transpose_of_trivial] at this

theorem eq_zero_of_posSemidef_neg {X : Mat d} (h : X.PosSemidef) (hn : (-X).PosSemidef) :
    X = 0 :=
  le_antisymm (neg_nonneg.1 (nonneg_of_posSemidef hn)) (nonneg_of_posSemidef h)

/-- The cone condition `tr X ≤ c λ_min(X)` passes to limits of symmetric matrices. -/
theorem isClosed_trace_le_lamMin [NeZero d] (c : ℝ) :
    IsClosed {X : Mat d | X.PosSemidef ∧ X.trace ≤ c * lamMin X} := by
  refine isClosed_of_closure_subset fun X hX => ?_
  obtain ⟨Xs, hXs, hlim⟩ := mem_closure_iff_seq_limit.1 hX
  have hXp : X.PosSemidef := isClosed_psdSet.mem_of_tendsto hlim
    (Eventually.of_forall fun n => (hXs n).1)
  refine ⟨hXp, ?_⟩
  have he := tendsto_eigUp (fun n => isSymm_of_isHermitian (hXs n).1.isHermitian)
    (isSymm_of_isHermitian hXp.isHermitian) hlim
  have he0 : Tendsto (fun n => lamMin (Xs n)) atTop (𝓝 (lamMin X)) := by
    rw [lamMin_eq_eigUp_zero hXp.isHermitian]
    refine (((continuous_apply (0 : Fin d)).tendsto _).comp he).congr fun n => ?_
    exact (lamMin_eq_eigUp_zero (hXs n).1.isHermitian).symm
  have htr : Tendsto (fun n => (Xs n).trace) atTop (𝓝 X.trace) :=
    (continuous_id.matrix_trace.tendsto X).comp hlim
  exact le_of_tendsto_of_tendsto' htr (he0.const_mul c) fun n => (hXs n).2

/-- **`prop:stable-order-generated`**, the cones: for `0 ≤ α < ∞`, `C_α` is an `O(d)`-invariant
closed convex cone in `Sym(d)` containing `I`, with `C_α ∩ (-C_α) = {0}`. -/
theorem stableGenCone_props (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) :
    stableGenCone d α ⊆ symSet d ∧ IsOrthInvariant (stableGenCone d α) ∧
      IsClosedConvexCone (stableGenCone d α) ∧ (1 : Mat d) ∈ stableGenCone d α ∧
      ∀ X ∈ stableGenCone d α, -X ∈ stableGenCone d α → X = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hdα : 0 ≤ (d : ℝ) + α := by positivity
  refine ⟨fun X hX => isSymm_of_isHermitian hX.1.isHermitian, fun Q hQ X hX => ?_,
    ⟨isClosed_trace_le_lamMin _, ?_, ?_, ?_⟩, ?_, fun X hX hnX => eq_zero_of_posSemidef_neg hX.1 hnX.1⟩
  · refine ⟨posSemidef_conj_orth hX.1, ?_⟩
    rw [trace_conj_orth hQ, lamMin_conj_orth hQ hX.1.isHermitian]
    exact hX.2
  · intro X hX Y hY a b ha hb _
    refine ⟨(hX.1.smul ha).add (hY.1.smul hb), ?_⟩
    have h1 := lamMin_add_ge (hX.1.smul ha).isHermitian (hY.1.smul hb).isHermitian
    rw [lamMin_smul ha, lamMin_smul hb] at h1
    rw [trace_add, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
    have h2 := mul_le_mul_of_nonneg_left hX.2 ha
    have h3 := mul_le_mul_of_nonneg_left hY.2 hb
    calc a * X.trace + b * Y.trace ≤ a * (((d : ℝ) + α) * lamMin X) +
          b * (((d : ℝ) + α) * lamMin Y) := add_le_add h2 h3
      _ = ((d : ℝ) + α) * (a * lamMin X + b * lamMin Y) := by ring
      _ ≤ ((d : ℝ) + α) * lamMin (a • X + b • Y) := mul_le_mul_of_nonneg_left h1 hdα
  · refine ⟨Matrix.PosSemidef.zero, ?_⟩
    rw [trace_zero, lamMin_zero_mat, mul_zero]
  · intro c hc X hX
    refine ⟨hX.1.smul hc, ?_⟩
    rw [trace_smul, lamMin_smul hc, smul_eq_mul]
    nlinarith [hX.2]
  · refine ⟨Matrix.PosSemidef.one, ?_⟩
    rw [trace_one, Fintype.card_fin, lamMin_one]
    linarith

/-- **`prop:stable-order-generated`**, the cones: `C_∞ = PSD(d)` is an `O(d)`-invariant closed
convex cone in `Sym(d)` containing `I`, with `C_∞ ∩ (-C_∞) = {0}`. -/
theorem psdSet_cone_props (_hd : 1 ≤ d) :
    psdSet d ⊆ symSet d ∧ IsOrthInvariant (psdSet d) ∧ IsClosedConvexCone (psdSet d) ∧
      (1 : Mat d) ∈ psdSet d ∧ ∀ X ∈ psdSet d, -X ∈ psdSet d → X = 0 :=
  ⟨fun _ hX => isSymm_of_isHermitian hX.isHermitian, fun _ _ _ hX => posSemidef_conj_orth hX,
    ⟨isClosed_psdSet, fun _ hX _ hY _ _ ha hb _ => (hX.smul ha).add (hY.smul hb),
      Matrix.PosSemidef.zero, fun _ hc _ hX => hX.smul hc⟩, Matrix.PosSemidef.one,
    fun _ hX hnX => eq_zero_of_posSemidef_neg hX hnX⟩

/-- `C₀ = {cI : c ≥ 0}`. -/
theorem stableGenCone_zero (hd : 1 ≤ d) :
    stableGenCone d 0 = {X : Mat d | ∃ c : ℝ, 0 ≤ c ∧ X = c • 1} := by
  haveI : NeZero d := ⟨by omega⟩
  ext X
  constructor
  · rintro ⟨hX, htr⟩
    have hXh := hX.isHermitian
    obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hXh
    set x := eigUp X
    have hmono := eigUp_monotone hXh
    have hsum : ∑ i, (x i - x 0) = 0 := by
      have h1 : ∑ i, x i = X.trace := sum_eigUp hXh
      rw [add_zero, lamMin_eq_eigUp_zero hXh] at htr
      have h2 : (d : ℝ) * x 0 ≤ ∑ i, x i := by
        calc (d : ℝ) * x 0 = ∑ _i : Fin d, x 0 := by simp
          _ ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hmono (Fin.zero_le i)
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith
    have hall : ∀ i, x i = x 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hmono (Fin.zero_le j))).1
        hsum i (Finset.mem_univ i)
      linarith
    refine ⟨x 0, eigUp_nonneg hX 0, ?_⟩
    rw [hXV, show x = fun _ => x 0 from funext hall, udiag_const hV]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨Matrix.PosSemidef.one.smul hc, ?_⟩
    rw [trace_smul, trace_one, Fintype.card_fin, lamMin_smul hc, lamMin_one, smul_eq_mul]
    exact le_of_eq (by ring)

/-- A causal curve of a smaller cone is causal for a larger one. -/
theorem IsCausalCurve.mono {C C' : Set (Mat d)} (h : C ⊆ C') {γ : ℝ → Mat d}
    (hγ : IsCausalCurve C γ) : IsCausalCurve C' γ :=
  ⟨hγ.mem_pd, hγ.absolutelyContinuous, hγ.causal.mono fun _ ht => h ht⟩

/-! ## Causal curves of `C_α` through `Φ_α` -/

/-- `Φ_α` along a curve, in the form of the derivative of the blueprint's clause (3): where the
entries of `γ` are differentiable, `(Φ_α ∘ γ)'_{ij}` is the `(i,j)` entry of
`(det γ)^s γ^{1/2}(Y + s (tr Y) I)γ^{1/2}`, `Y = γ^{-1/2}γ'γ^{-1/2}`, `s = -1/(d+α)`. -/
theorem hasDerivAt_phiAlpha_curve (α : ℝ) {γ : ℝ → Mat d} {t : ℝ} (hpd : (γ t).PosDef)
    (hder : ∀ i j, HasDerivAt (fun u => γ u i j) (mderiv γ t i j) t) (i j : Fin d) :
    HasDerivAt (fun u => phiAlpha d α (γ u) i j)
      (((γ t).det ^ (-(1 : ℝ) / ((d : ℝ) + α)) •
        (msqrt (γ t) * (relStep (γ t) (mderiv γ t) +
          ((-(1 : ℝ) / ((d : ℝ) + α)) * (relStep (γ t) (mderiv γ t)).trace) • 1) *
          msqrt (γ t))) i j) t := by
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  set Y := relStep (γ t) (mderiv γ t)
  have h := hasDerivAt_phi_curve hpd hder s i j
  have hγ' : mderiv γ t = msqrt (γ t) * Y * msqrt (γ t) := (msqrt_mul_relStep hpd _).symm
  have htr : ((γ t)⁻¹ * mderiv γ t).trace = Y.trace := by
    rw [hγ']; exact trace_inv_mul_msqrt_conj hpd Y
  refine h.congr_deriv ?_
  rw [htr]
  have hmat : msqrt (γ t) * (Y + (s * Y.trace) • (1 : Mat d)) * msqrt (γ t) =
      mderiv γ t + (s * Y.trace) • γ t := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      msqrt_mul_self hpd.posSemidef, ← hγ']
  rw [hmat]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

/-- For `Y ∈ C_α`, `Y - (tr Y/(d+α)) I ⪰ 0`. -/
theorem stableGenCone_shift_posSemidef [NeZero d] {α : ℝ} (hα : 0 ≤ α) {Y : Mat d}
    (hY : Y ∈ stableGenCone d α) :
    (Y + ((-(1 : ℝ) / ((d : ℝ) + α)) * Y.trace) • (1 : Mat d)).PosSemidef := by
  have hdα : 0 < (d : ℝ) + α := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    linarith
  have hYh := hY.1.isHermitian
  have hc : Y.trace / ((d : ℝ) + α) ≤ eigUp Y 0 := by
    rw [div_le_iff₀ hdα, ← lamMin_eq_eigUp_zero hYh, mul_comm]
    exact hY.2
  have := (posSemidef_sub_smul_one_iff hYh _).2 hc
  have e : Y + ((-(1 : ℝ) / ((d : ℝ) + α)) * Y.trace) • (1 : Mat d) =
      Y - (Y.trace / ((d : ℝ) + α)) • (1 : Mat d) := by
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  rw [e]
  exact this

/-- **`Φ_α` is monotone along a `C_α`-causal curve**: `Φ_α(γ(0)) ≤ Φ_α(γ(1))`. -/
theorem IsCausalCurve.phiAlpha_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) {γ : ℝ → Mat d}
    (hγ : IsCausalCurve (stableGenCone d α) γ) :
    loewnerLE (phiAlpha d α (γ 0)) (phiAlpha d α (γ 1)) := by
  haveI : NeZero d := ⟨by omega⟩
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  have hherm : ∀ t ∈ Icc (0 : ℝ) 1, (phiAlpha d α (γ t)).IsHermitian := fun t ht =>
    ((hγ.mem_pd t ht).smul (Real.rpow_pos_of_pos (hγ.mem_pd t ht).det_pos s)).isHermitian
  refine loewnerLE_of_ae_deriv (η := fun u => phiAlpha d α (γ u))
    (fun i j => absolutelyContinuous_phi_curve hγ.absolutelyContinuous hγ.mem_pd s i j)
    (hherm 0 ⟨le_rfl, zero_le_one⟩) (hherm 1 ⟨zero_le_one, le_rfl⟩) ?_
  have hdiffs : ∀ᵐ t : ℝ, ∀ p : Fin d × Fin d, t ∈ uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun u => γ u p.1 p.2) t :=
    ae_all_iff.2 fun p => (hγ.absolutelyContinuous p.1 p.2).ae_differentiableAt
  have hcaus : ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 → relStep (γ t) (mderiv γ t) ∈ stableGenCone d α :=
    (ae_restrict_iff' measurableSet_Icc).1 hγ.causal
  filter_upwards [hdiffs, hcaus] with t h1 h2 htI _
  have hpd := hγ.mem_pd t htI
  have hder : ∀ i j, HasDerivAt (fun u => γ u i j) (mderiv γ t i j) t := fun i j =>
    (h1 (i, j) (by rw [uIcc_of_le zero_le_one]; exact htI)).hasDerivAt
  have hm : mderiv (fun u => phiAlpha d α (γ u)) t = (γ t).det ^ s •
      (msqrt (γ t) * (relStep (γ t) (mderiv γ t) +
        (s * (relStep (γ t) (mderiv γ t)).trace) • 1) * msqrt (γ t)) := by
    ext i j
    simp only [mderiv, Matrix.of_apply]
    exact (hasDerivAt_phiAlpha_curve α hpd hder i j).deriv
  rw [hm]
  refine Matrix.PosSemidef.smul ?_ (Real.rpow_pos_of_pos hpd.det_pos s).le
  have hZ := stableGenCone_shift_posSemidef hα (h2 htI)
  have := (posSemidef_relStep_iff hpd (msqrt (γ t) * (relStep (γ t) (mderiv γ t) +
    (s * (relStep (γ t) (mderiv γ t)).trace) • 1) * msqrt (γ t))).1
  rw [relStep_msqrt_mul hpd] at this
  exact this hZ

/-- **The shape is constant along a `C₀`-causal curve**: `Φ₀(γ(0)) = Φ₀(γ(1))`. -/
theorem IsCausalCurve.phiAlpha_zero_eq (hd : 1 ≤ d) {γ : ℝ → Mat d}
    (hγ : IsCausalCurve (stableGenCone d 0) γ) :
    phiAlpha d 0 (γ 0) = phiAlpha d 0 (γ 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  set s := -(1 : ℝ) / ((d : ℝ) + 0)
  refine eq_of_ae_deriv_zero (η := fun u => phiAlpha d 0 (γ u))
    (fun i j => absolutelyContinuous_phi_curve hγ.absolutelyContinuous hγ.mem_pd s i j) ?_
  have hdiffs : ∀ᵐ t : ℝ, ∀ p : Fin d × Fin d, t ∈ uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun u => γ u p.1 p.2) t :=
    ae_all_iff.2 fun p => (hγ.absolutelyContinuous p.1 p.2).ae_differentiableAt
  have hcaus : ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 → relStep (γ t) (mderiv γ t) ∈ stableGenCone d 0 :=
    (ae_restrict_iff' measurableSet_Icc).1 hγ.causal
  filter_upwards [hdiffs, hcaus] with t h1 h2 htI i j
  have hpd := hγ.mem_pd t htI
  have hder : ∀ i j, HasDerivAt (fun u => γ u i j) (mderiv γ t i j) t := fun i j =>
    (h1 (i, j) (by rw [uIcc_of_le zero_le_one]; exact htI)).hasDerivAt
  have h := hasDerivAt_phiAlpha_curve 0 hpd hder i j
  -- `Y = cI`, so `Y + s(tr Y)I = 0`
  have hY := h2 htI
  rw [stableGenCone_zero hd] at hY
  obtain ⟨c, -, hc⟩ := hY
  rw [hc] at h
  have hz : c • (1 : Mat d) + (s * (c • (1 : Mat d)).trace) • (1 : Mat d) = 0 := by
    rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, ← add_smul]
    have : c + s * (c * d) = 0 := by
      simp only [s, add_zero]
      field_simp
      ring
    rw [this, zero_smul]
  rw [hz, Matrix.mul_zero, Matrix.zero_mul, smul_zero] at h
  simpa using h

/-- **A `PSD(d)`-causal curve is Loewner-monotone.** -/
theorem IsCausalCurve.loewnerLE_psd {γ : ℝ → Mat d} (hγ : IsCausalCurve (psdSet d) γ) :
    loewnerLE (γ 0) (γ 1) := by
  refine loewnerLE_of_ae_deriv hγ.absolutelyContinuous
    (hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩).isHermitian (hγ.mem_pd 1 ⟨zero_le_one, le_rfl⟩).isHermitian ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hγ.causal] with t ht htI _
  exact (posSemidef_relStep_iff (hγ.mem_pd t htI) _).1 (ht htI)

/-! ## Clause (1): the three corners -/

/-- `C_α = {X ∈ Sym(d) : (d+α) λ_min(X) ≥ tr X}` for `α > 0`: the condition `X ≥ 0` is implied. -/
theorem stableGenCone_pos_eq (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    stableGenCone d α = {X : Mat d | X.IsSymm ∧ X.trace ≤ ((d : ℝ) + α) * lamMin X} := by
  haveI : NeZero d := ⟨by omega⟩
  ext X
  constructor
  · rintro ⟨hX, h⟩
    exact ⟨isSymm_of_isHermitian hX.isHermitian, h⟩
  · rintro ⟨hXs, h⟩
    have hXh := isHermitian_of_isSymm hXs
    have hsym : symPart X = X := by
      rw [symPart, hXs.eq, ← two_smul ℝ X, smul_smul]; norm_num
    have h1 := trace_ge_card_mul_lamMin X
    rw [hsym] at h1
    have hl : 0 ≤ lamMin X := by nlinarith
    refine ⟨?_, h⟩
    have := (posSemidef_sub_smul_one_iff hXh 0).2 (by rwa [← lamMin_eq_eigUp_zero hXh])
    simpa using this

/-- `tr(log M) = log det M` and `λ_min(log M) = log λ_min(M)` on `PD(d)`. -/
theorem trace_mlog {M : Mat d} (hM : M.PosDef) : (mlog M).trace = Real.log M.det := by
  rw [← sum_eigUp (mlog_isHermitian M)]
  change ∑ i, logSpec M i = _
  rw [logSpec_eq hM, ← Real.log_prod (fun i _ => (eigUp_pos hM i).ne'), prod_eigUp hM.isHermitian]

theorem lamMin_mlog [NeZero d] {M : Mat d} (hM : M.PosDef) :
    lamMin (mlog M) = Real.log (lamMin M) := by
  rw [lamMin_eq_eigUp_zero (mlog_isHermitian M), lamMin_eq_eigUp_zero hM.isHermitian]
  change logSpec M 0 = _
  rw [logSpec_eq hM]

/-- **`M ∈ exp C_α` iff `λ_min(M)^{d+α} ≥ det M`**, for `α > 0`. -/
theorem mem_expSet_stableGenCone_iff (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {M : Mat d}
    (hM : M.PosDef) : M ∈ expSet (stableGenCone d α) ↔ M.det ≤ lamMin M ^ ((d : ℝ) + α) := by
  haveI : NeZero d := ⟨by omega⟩
  have hdα : 0 < (d : ℝ) + α := by positivity
  have hl := lamMin_pos hM
  have hkey : mlog M ∈ stableGenCone d α ↔ M.det ≤ lamMin M ^ ((d : ℝ) + α) := by
    rw [stableGenCone_pos_eq hd hα]
    simp only [Set.mem_setOf_eq, mlog_isSymm M, true_and]
    rw [trace_mlog hM, lamMin_mlog hM, ← Real.log_rpow hl,
      Real.log_le_log_iff hM.det_pos (Real.rpow_pos_of_pos hl _)]
  rw [← hkey]
  constructor
  · rintro ⟨X, hX, rfl⟩
    rwa [mlog_mexp (isHermitian_of_isSymm ((stableGenCone_props hd hα.le).1 hX))]
  · intro h
    exact ⟨mlog M, h, (mexp_mlog hM).symm⟩

/-- **`M ∈ exp PSD(d)` iff `M ≥ I`.** -/
theorem mem_expSet_psdSet_iff {M : Mat d} (hM : M.PosDef) :
    M ∈ expSet (psdSet d) ↔ loewnerLE 1 M := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (mexp_sub_one_posSemidef_iff (isSymm_of_isHermitian hX.isHermitian)).2 hX
  · intro h
    refine ⟨mlog M, (mexp_sub_one_posSemidef_iff (mlog_isSymm M)).1 ?_, (mexp_mlog hM).symm⟩
    rw [mexp_mlog hM]
    exact h

/-- `Σ ≤ Σ'` iff `I ≤ Σ^{-1/2}Σ'Σ^{-1/2}`. -/
theorem loewnerLE_iff_relStep {S S' : Mat d} (hS : S.PosDef) :
    loewnerLE S S' ↔ loewnerLE 1 (relStep S S') := by
  unfold loewnerLE
  rw [← posSemidef_relStep_iff hS, relStep_sub, relStep_self hS]

/-- **`Φ_α(Σ) ≤ Φ_α(Σ')` iff `λ_min(M)^{d+α} ≥ det M`**, `M` the relative step, `α > 0`. -/
theorem phiAlpha_le_iff (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {S S' : Mat d} (hS : S.PosDef)
    (hS' : S'.PosDef) :
    loewnerLE (phiAlpha d α S) (phiAlpha d α S') ↔
      (relStep S S').det ≤ lamMin (relStep S S') ^ ((d : ℝ) + α) := by
  haveI : NeZero d := ⟨by omega⟩
  set M := relStep S S'
  have hM : M.PosDef := (posDef_relStep_iff hS S').2 hS'
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  have hdα : 0 < (d : ℝ) + α := by positivity
  have hDS := hS.det_pos
  have hDM := hM.det_pos
  have hl := lamMin_pos hM
  have hdet : S'.det = S.det * M.det := by
    rw [det_relStep hS, mul_div_cancel₀ _ hDS.ne']
  have hrel : relStep S (phiAlpha d α S' - phiAlpha d α S) =
      S.det ^ s • (M.det ^ s • M - 1) := by
    unfold phiAlpha
    rw [relStep_sub, relStep_smul, relStep_smul, relStep_self hS, hdet,
      Real.mul_rpow hDS.le hDM.le, smul_sub, smul_smul]
  unfold loewnerLE
  rw [← posSemidef_relStep_iff hS, hrel, posSemidef_smul_iff (Real.rpow_pos_of_pos hDS s),
    show M.det ^ s • M - 1 = M.det ^ s • M - (1 : ℝ) • (1 : Mat d) by rw [one_smul],
    posSemidef_sub_smul_one_iff ((hM.smul (Real.rpow_pos_of_pos hDM s)).isHermitian),
    eigUp_smul (Real.rpow_pos_of_pos hDM s).le hM.isHermitian, Pi.smul_apply, smul_eq_mul,
    ← lamMin_eq_eigUp_zero hM.isHermitian]
  -- `1 ≤ D^s L ⟺ D ≤ L^{d+α}` through logarithms
  rw [← Real.log_le_log_iff one_pos (mul_pos (Real.rpow_pos_of_pos hDM s) hl),
    ← Real.log_le_log_iff hDM (Real.rpow_pos_of_pos hl _), Real.log_one,
    Real.log_mul (Real.rpow_pos_of_pos hDM s).ne' hl.ne', Real.log_rpow hDM, Real.log_rpow hl]
  simp only [s]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hdα.le
    field_simp at this ⊢
    linarith
  · intro h
    rw [div_mul_eq_mul_div, neg_mul, one_mul, neg_div, le_neg_add_iff_add_le, add_zero,
      div_le_iff₀ hdα]
    linarith

/-- **`prop:stable-order-generated`(1)**, `α = 0`: `C₀ = {cI : c ≥ 0}`, and `Σ ≼₀ Σ'` if and only if
`Σ' = cΣ` with `c ≥ 1`, the ray order on `PD(d)`; the related pairs are joined by the
`C₀`-causal curve `Σ^{1/2}M^tΣ^{1/2}`, which joins them (its endpoints `Σ`, `Σ'`: blind review
R3-3). -/
theorem stable_order_zero (hd : 1 ≤ d) :
    stableGenCone d 0 = {X : Mat d | ∃ c : ℝ, 0 ≤ c ∧ X = c • 1} ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (causalLE (stableGenCone d 0) S S' ↔ ∃ c : ℝ, 1 ≤ c ∧ S' = c • S) ∧
        (causalLE (stableGenCone d 0) S S' →
          IsCausalCurve (stableGenCone d 0) (stepGeodesic S S') ∧
            stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S') := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hCsym, hO, hC, -, -⟩ := stableGenCone_props hd (le_refl (0 : ℝ))
  have hC0 := stableGenCone_zero hd
  refine ⟨hC0, fun S S' hS hS' => ?_⟩
  have hgeo : (∃ c : ℝ, 1 ≤ c ∧ S' = c • S) →
      IsCausalCurve (stableGenCone d 0) (stepGeodesic S S') ∧
        stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S' := by
    rintro ⟨c, hc, hS'c⟩
    refine stepGeodesic_causal hCsym hO hS hS' ⟨Real.log c • (1 : Mat d), ?_, ?_⟩
    · rw [hC0]; exact ⟨Real.log c, Real.log_nonneg hc, rfl⟩
    · rw [mexp_smul_one, Real.exp_log (by linarith), hS'c, relStep_smul, relStep_self hS]
  have hiff : causalLE (stableGenCone d 0) S S' ↔ ∃ c : ℝ, 1 ≤ c ∧ S' = c • S := by
    constructor
    · rintro ⟨γ, hγ, rfl, rfl⟩
      have hconst := hγ.phiAlpha_zero_eq hd
      have hle := (hγ.mono fun X hX => hX.1).loewnerLE_psd
      set a := (γ 0).det ^ (-(1 : ℝ) / ((d : ℝ) + 0))
      set b := (γ 1).det ^ (-(1 : ℝ) / ((d : ℝ) + 0))
      have ha : 0 < a := Real.rpow_pos_of_pos hS.det_pos _
      have hb : 0 < b := Real.rpow_pos_of_pos hS'.det_pos _
      have hγ1 : γ 1 = (a / b) • γ 0 := by
        have h : a • γ 0 = b • γ 1 := hconst
        calc γ 1 = b⁻¹ • (b • γ 1) := by rw [smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
          _ = b⁻¹ • (a • γ 0) := by rw [h]
          _ = (a / b) • γ 0 := by rw [smul_smul, div_eq_inv_mul]
      refine ⟨a / b, ?_, hγ1⟩
      by_contra hlt
      push Not at hlt
      obtain ⟨v, hv, -⟩ := exists_unit_eigvec_eigUp_zero hS.isHermitian
      have hq := quad_nonneg hle v
      rw [hγ1, quad_sub, quad_smul] at hq
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hv
        exact zero_ne_one hv
      have hpos := quad_pos hS hv0
      nlinarith
    · intro h
      obtain ⟨hc, h0, h1⟩ := hgeo h
      exact ⟨_, hc, h0, h1⟩
  exact ⟨hiff, fun h => hgeo (hiff.1 h)⟩

/-- **`prop:stable-order-generated`(1)**, `0 < α < ∞`: the condition `X ≥ 0` in `C_α` is implied by
the inequality, and `Σ ≼_α Σ'` if and only if `λ_min(M)^{d+α} ≥ det M` (`stableLE`, which for
`0 < α < 2` is the order of `prop:stable-step-cone`(2)); the related pairs are joined by the
`C_α`-causal curve `Σ^{1/2}M^tΣ^{1/2}`, which joins them (its endpoints, blind review R3-3). -/
theorem stable_order_pos (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    stableGenCone d α = {X : Mat d | X.IsSymm ∧ X.trace ≤ ((d : ℝ) + α) * lamMin X} ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (causalLE (stableGenCone d α) S S' ↔ stableLE α S S') ∧
        (causalLE (stableGenCone d α) S S' →
          IsCausalCurve (stableGenCone d α) (stepGeodesic S S') ∧
            stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S') := by
  obtain ⟨hCsym, hO, -, -, -⟩ := stableGenCone_props hd hα.le
  refine ⟨stableGenCone_pos_eq hd hα, fun S S' hS hS' => ?_⟩
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hstep : stableLE α S S' ↔ relStep S S' ∈ expSet (stableGenCone d α) := by
    rw [mem_expSet_stableGenCone_iff hd hα hM]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hS, hS', hM, h⟩⟩
  have hiff : causalLE (stableGenCone d α) S S' ↔ stableLE α S S' := by
    constructor
    · rintro ⟨γ, hγ, rfl, rfl⟩
      exact ⟨hS, hS', hM, (phiAlpha_le_iff hd hα hS hS').1 (hγ.phiAlpha_le hd hα.le)⟩
    · intro h
      obtain ⟨hc, h0, h1⟩ := stepGeodesic_causal hCsym hO hS hS' (hstep.1 h)
      exact ⟨_, hc, h0, h1⟩
  exact ⟨hiff, fun h => stepGeodesic_causal hCsym hO hS hS' (hstep.1 (hiff.1 h))⟩

/-- **`prop:stable-order-generated`(1)**, `α = ∞`: `Σ ≼_∞ Σ'` if and only if `Σ ≤ Σ'`, the Loewner
order; the related pairs are joined by the `PSD(d)`-causal curve `Σ^{1/2}M^tΣ^{1/2}` (its
endpoints, blind review R3-3). -/
theorem stable_order_infty (hd : 1 ≤ d) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef →
      (causalLE (psdSet d) S S' ↔ loewnerLE S S') ∧
      (causalLE (psdSet d) S S' →
        IsCausalCurve (psdSet d) (stepGeodesic S S') ∧
          stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S') := by
  obtain ⟨hCsym, hO, -, -, -⟩ := psdSet_cone_props (d := d) hd
  intro S S' hS hS'
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hstep : loewnerLE S S' ↔ relStep S S' ∈ expSet (psdSet d) := by
    rw [mem_expSet_psdSet_iff hM, loewnerLE_iff_relStep hS]
  have hiff : causalLE (psdSet d) S S' ↔ loewnerLE S S' := by
    constructor
    · rintro ⟨γ, hγ, rfl, rfl⟩
      exact hγ.loewnerLE_psd
    · intro h
      obtain ⟨hc, h0, h1⟩ := stepGeodesic_causal hCsym hO hS hS' (hstep.1 h)
      exact ⟨_, hc, h0, h1⟩
  exact ⟨hiff, fun h => stepGeodesic_causal hCsym hO hS hS' (hstep.1 (hiff.1 h))⟩

/-! ## Clause (3): `Φ_α` and `ψ_α` -/

theorem phiAlpha_one (α : ℝ) : phiAlpha d α (1 : Mat d) = 1 := by
  simp [phiAlpha]

theorem phiAlpha_posDef (α : ℝ) {S : Mat d} (hS : S.PosDef) : (phiAlpha d α S).PosDef :=
  hS.smul (Real.rpow_pos_of_pos hS.det_pos _)

/-- `Φ_α(AΣAᵀ) = ψ_α(A)Φ_α(Σ)ψ_α(A)ᵀ`. -/
theorem phiAlpha_act (α : ℝ) (A : Mat d) {S : Mat d} (hS : S.PosDef) :
    phiAlpha d α (act A S) = act (psiAlpha d α A) (phiAlpha d α S) := by
  have hdet : (act A S).det = (|A.det| * |A.det|) * S.det := by
    rw [act, det_mul, det_mul, det_transpose, abs_mul_abs_self]; ring
  have ha : 0 ≤ |A.det| := abs_nonneg _
  unfold phiAlpha psiAlpha
  rw [hdet, Real.mul_rpow (mul_nonneg ha ha) hS.det_pos.le, Real.mul_rpow ha ha]
  simp only [act, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- `ψ_α(AB) = ψ_α(A)ψ_α(B)`. -/
theorem psiAlpha_mul (α : ℝ) (A B : Mat d) :
    psiAlpha d α (A * B) = psiAlpha d α A * psiAlpha d α B := by
  unfold psiAlpha
  rw [det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

/-- The exponent identity behind both inverses: `(sd + 1)/α + s = 0` for `s = -1/(d+α)`. -/
theorem phi_exponent_identity {α : ℝ} (hα : 0 < α) (d' : ℝ) (hd' : 0 ≤ d') :
    (-(1 : ℝ) / (d' + α) * d' + 1) * (1 / α) + -(1 : ℝ) / (d' + α) = 0 := by
  have h1 : d' + α ≠ 0 := by linarith
  field_simp
  ring

/-- **`Φ_α` and `T ↦ (det T)^{1/α}T` are inverse on `PD(d)`.** -/
theorem phiAlpha_invOn {α : ℝ} (hα : 0 < α) :
    InvOn (fun T : Mat d => (T.det ^ (1 / α)) • T) (phiAlpha d α) (pdSet d) (pdSet d) := by
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hid := phi_exponent_identity hα (d : ℝ) hdn
  constructor
  · intro S hS
    have hS : S.PosDef := hS
    have hD := hS.det_pos
    simp only [phiAlpha]
    rw [det_smul, Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_add_one hD.ne', ← Real.rpow_mul hD.le, smul_smul, ← Real.rpow_add hD, hid,
      Real.rpow_zero, one_smul]
  · intro T hT
    have hT : T.PosDef := hT
    have hD := hT.det_pos
    have hdα : 0 < (d : ℝ) + α := by linarith
    simp only [phiAlpha]
    rw [det_smul, Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_add_one hD.ne', ← Real.rpow_mul hD.le, smul_smul, ← Real.rpow_add hD]
    have : (1 / α * (d : ℝ) + 1) * (-(1 : ℝ) / ((d : ℝ) + α)) + 1 / α = 0 := by
      field_simp
      ring
    rw [this, Real.rpow_zero, one_smul]

/-- **`ψ_α` is a bijection of `GL(d)`**, with inverse `A ↦ |det A|^{1/α}A`. -/
theorem psiAlpha_invOn {α : ℝ} (hα : 0 < α) :
    InvOn (fun A : Mat d => (|A.det| ^ (1 / α)) • A) (psiAlpha d α) (glSet d) (glSet d) := by
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hid := phi_exponent_identity hα (d : ℝ) hdn
  have habs : ∀ {A : Mat d} {c : ℝ}, 0 < c → |(c • A).det| = c ^ (d : ℕ) * |A.det| := by
    intro A c hc
    rw [det_smul, Fintype.card_fin, abs_mul, abs_of_pos (pow_pos hc d)]
  constructor
  · intro A hA
    have hD : 0 < |A.det| := abs_pos.2 ((isUnit_iff_ne_zero).1 hA)
    simp only [psiAlpha]
    rw [habs (Real.rpow_pos_of_pos hD _), ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_add_one hD.ne', ← Real.rpow_mul hD.le, smul_smul, ← Real.rpow_add hD, hid,
      Real.rpow_zero, one_smul]
  · intro A hA
    have hD : 0 < |A.det| := abs_pos.2 ((isUnit_iff_ne_zero).1 hA)
    have hdα : 0 < (d : ℝ) + α := by linarith
    simp only [psiAlpha]
    rw [habs (Real.rpow_pos_of_pos hD _), ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_add_one hD.ne', ← Real.rpow_mul hD.le, smul_smul, ← Real.rpow_add hD]
    have : (1 / α * (d : ℝ) + 1) * (-(1 : ℝ) / ((d : ℝ) + α)) + 1 / α = 0 := by
      field_simp
      ring
    rw [this, Real.rpow_zero, one_smul]

theorem psiAlpha_mem_glSet (α : ℝ) {A : Mat d} (hA : A ∈ glSet d) : psiAlpha d α A ∈ glSet d := by
  have hD : 0 < |A.det| := abs_pos.2 ((isUnit_iff_ne_zero).1 hA)
  change IsUnit (psiAlpha d α A).det
  rw [psiAlpha, det_smul]
  exact (mul_ne_zero (pow_ne_zero _ (Real.rpow_pos_of_pos hD _).ne')
    ((isUnit_iff_ne_zero).1 hA)).isUnit

/-! ## Clause (2): the exponent cone is the tangent wedge -/

theorem lamMin_add_smul_one [NeZero d] {X : Mat d} (hX : X.IsHermitian) (c : ℝ) :
    lamMin (X + c • (1 : Mat d)) = lamMin X + c := by
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hX
  have he : X + c • (1 : Mat d) = udiag V (fun i => eigUp X i + c) := by
    conv_lhs => rw [hXV]
    rw [← udiag_const hV, udiag_add_udiag]
    rfl
  have hXc : (X + c • (1 : Mat d)).IsHermitian := by rw [he]; exact udiag_isHermitian V _
  rw [lamMin_eq_eigUp_zero hXc, lamMin_eq_eigUp_zero hX, he, eigUp_udiag hV,
    sortUp_of_monotone fun i j hij => by
      have := eigUp_monotone hX hij
      linarith]

/-- **The tangent wedge of the Loewner semigroup**: `e^{tB}e^{tB}ᵀ ≥ I` for every `t ≥ 0` if and only
if `λ_min(sym B) ≥ 0`, through `d/dt |e^{tBᵀ}x|² = 2⟨y, Bᵀy⟩`. -/
theorem loewner_tangent_iff [NeZero d] (B : Mat d) :
    (∀ t : ℝ, 0 ≤ t → loewnerLE 1 (mexp (t • B) * (mexp (t • B))ᵀ)) ↔ 0 ≤ lamMin (symPart B) := by
  have hsymT : symPart Bᵀ = symPart B := by
    rw [symPart, symPart, transpose_transpose, add_comm]
  have hq : ∀ (t : ℝ) (x : Rd d), quad (mexp (t • B) * (mexp (t • B))ᵀ) x =
      ‖lin (mexp (t • Bᵀ)) x‖ ^ 2 := by
    intro t x
    have := quad_act (mexp (t • B)) 1 x
    rw [act, Matrix.mul_one, quad_one] at this
    rw [this, mexp_smul_transpose]
  constructor
  · intro h
    refine (le_lamMin_iff (symPart_isHermitian B) 0).2 fun x hx => ?_
    set f : ℝ → ℝ := fun u => ‖lin (mexp (u • Bᵀ)) x‖ ^ 2
    have hf := hasDerivAt_norm_sq_mexp Bᵀ x 0
    rw [zero_smul, mexp_zero, lin_one] at hf
    have hslope := hf.tendsto_slope_zero_right
    have hge : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 ≤ u⁻¹ • (f (0 + u) - f 0) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : (0 : ℝ) < u := hu
      have h1 := quad_nonneg (h u hu.le) x
      rw [quad_sub, hq, quad_one] at h1
      have h0 : f 0 = ‖x‖ ^ 2 := by simp [f, mexp_zero, lin_one]
      simp only [smul_eq_mul, zero_add, h0]
      exact mul_nonneg (inv_nonneg.2 hu.le) h1
    have := ge_of_tendsto hslope hge
    simp only [one_apply_eq_self] at this
    have hqT : quad Bᵀ x = quad (symPart B) x := by
      rw [← quad_symPart, hsymT]
    rw [hqT] at this
    linarith
  · intro h t ht
    refine posSemidef_of_quad_nonneg ?_ fun x => ?_
    · have hs : (mexp (t • B) * (mexp (t • B))ᵀ - 1).IsSymm := by
        rw [Matrix.IsSymm, transpose_sub, transpose_mul, transpose_transpose, transpose_one]
      exact isHermitian_of_isSymm hs
    · rw [quad_sub, hq, quad_one]
      have := exp_mul_le_norm_sq_mexp Bᵀ x ht
      rw [hsymT] at this
      have he : 1 ≤ Real.exp (2 * lamMin (symPart B) * t) :=
        Real.one_le_exp (by positivity)
      nlinarith [sq_nonneg ‖x‖]

/-- `ψ_α(e^{tB}) = e^{t(B + s(tr B)I)}`, `s = -1/(d+α)`. -/
theorem psiAlpha_mexp (α : ℝ) (B : Mat d) (t : ℝ) :
    psiAlpha d α (mexp (t • B)) =
      mexp (t • (B + ((-(1 : ℝ) / ((d : ℝ) + α)) * B.trace) • (1 : Mat d))) := by
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  have hcomm : Commute (t • B) ((t * (s * B.trace)) • (1 : Mat d)) :=
    (Commute.one_right _).smul_right _
  rw [smul_add, smul_smul]
  rw [show mexp (t • B + (t * (s * B.trace)) • (1 : Mat d)) =
      mexp (t • B) * mexp ((t * (s * B.trace)) • (1 : Mat d)) from
    Matrix.exp_add_of_commute _ _ hcomm]
  rw [mexp_smul_one, Matrix.mul_smul, Matrix.mul_one, psiAlpha, det_mexp_smul,
    abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  ring

/-- **Three readings of `I ≼_α AAᵀ`**, for `A ∈ GL(d)` and `α > 0`: `AAᵀ ∈ exp C_α`, and
`ψ_α(A)ψ_α(A)ᵀ ≥ I`. -/
theorem causalLE_one_mul_transpose_iff (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) {A : Mat d}
    (hAgl : A ∈ glSet d) :
    (A * Aᵀ ∈ expSet (stableGenCone d α) ↔ causalLE (stableGenCone d α) 1 (A * Aᵀ)) ∧
      (causalLE (stableGenCone d α) 1 (A * Aᵀ) ↔
        loewnerLE 1 (psiAlpha d α A * (psiAlpha d α A)ᵀ)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hpd : (A * Aᵀ).PosDef := by
    have := (posDef_act_iff hAgl 1).2 Matrix.PosDef.one
    rwa [act, Matrix.mul_one] at this
  have hc := (stable_order_pos hd hα0).2 1 _ Matrix.PosDef.one hpd
  have hrel : relStep 1 (A * Aᵀ) = A * Aᵀ := relStep_one_left _
  have hstab : stableLE α 1 (A * Aᵀ) ↔ (A * Aᵀ).det ≤ lamMin (A * Aᵀ) ^ ((d : ℝ) + α) := by
    unfold stableLE stepLE stableStepSet
    rw [hrel]
    exact ⟨fun h => h.2.2.2, fun h => ⟨Matrix.PosDef.one, hpd, hpd, h⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hc.1, hstab, mem_expSet_stableGenCone_iff hd hα0 hpd]
  · rw [hc.1, hstab]
    have h1 := phiAlpha_le_iff hd hα0 Matrix.PosDef.one hpd
    rw [hrel, phiAlpha_one] at h1
    rw [← h1]
    have := phiAlpha_act α A (Matrix.PosDef.one (n := Fin d))
    rw [act, Matrix.mul_one, phiAlpha_one, act, Matrix.mul_one] at this
    rw [this]

/-- **`prop:stable-order-generated`(2)**, the exponent cone is the tangent cone: for `0 < α < 2`,
`𝔨_α = {B : e^{tB}e^{tBᵀ} ∈ exp C_α for every t ≥ 0}`, which is the tangent set of the semigroup
`{A : I ≼_α AAᵀ}`, and `𝔨_α ∩ Sym(d) = C_α`. -/
theorem stableExpCone_tangent (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) :
    stableExpCone d α =
        {B : Mat d | ∀ t : ℝ, 0 ≤ t → mexp (t • B) * mexp (t • Bᵀ) ∈ expSet (stableGenCone d α)} ∧
      stableExpCone d α =
        {B : Mat d | ∀ t : ℝ, 0 ≤ t →
          causalLE (stableGenCone d α) 1 (mexp (t • B) * (mexp (t • B))ᵀ)} ∧
      stableExpCone d α ∩ symSet d = stableGenCone d α := by
  haveI : NeZero d := ⟨by omega⟩
  have hdα : 0 < (d : ℝ) + α := by positivity
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  have hA := fun (A : Mat d) (hAgl : A ∈ glSet d) => causalLE_one_mul_transpose_iff hd hα0 hAgl
  have hmem : ∀ B : Mat d, B ∈ stableExpCone d α ↔ 0 ≤ lamMin (symPart (B + (s * B.trace) • 1)) := by
    intro B
    rw [symPart_add, symPart_smul, symPart_one,
      lamMin_add_smul_one (symPart_isHermitian B)]
    change B.trace ≤ ((d : ℝ) + α) * lamMin (symPart B) ↔ _
    simp only [s]
    constructor
    · intro h
      have : B.trace / ((d : ℝ) + α) ≤ lamMin (symPart B) := by rw [div_le_iff₀ hdα]; linarith
      have e : -(1 : ℝ) / ((d : ℝ) + α) * B.trace = -(B.trace / ((d : ℝ) + α)) := by ring
      rw [e]; linarith
    · intro h
      have e : -(1 : ℝ) / ((d : ℝ) + α) * B.trace = -(B.trace / ((d : ℝ) + α)) := by ring
      rw [e] at h
      have : B.trace / ((d : ℝ) + α) ≤ lamMin (symPart B) := by linarith
      rw [div_le_iff₀ hdα] at this
      linarith
  have hcausal : ∀ B : Mat d, B ∈ stableExpCone d α ↔ ∀ t : ℝ, 0 ≤ t →
      causalLE (stableGenCone d α) 1 (mexp (t • B) * (mexp (t • B))ᵀ) := by
    intro B
    rw [hmem, ← loewner_tangent_iff]
    refine forall₂_congr fun t _ => ?_
    rw [(hA _ (mexp_mem_glSet _)).2, psiAlpha_mexp]
  refine ⟨?_, ?_, ?_⟩
  · ext B
    rw [Set.mem_setOf_eq, hcausal]
    refine forall₂_congr fun t _ => ?_
    rw [mexp_smul_transpose, (hA _ (mexp_mem_glSet _)).1]
  · ext B
    exact hcausal B
  · rw [stableGenCone_pos_eq hd hα0]
    ext X
    constructor
    · rintro ⟨hX, hXs⟩
      have hXs' : X.IsSymm := hXs
      have hsym : symPart X = X := by
        rw [symPart, hXs'.eq, ← two_smul ℝ X, smul_smul]; norm_num
      refine ⟨hXs', ?_⟩
      have : X.trace ≤ ((d : ℝ) + α) * lamMin (symPart X) := hX
      rwa [hsym] at this
    · rintro ⟨hXs, h⟩
      have hsym : symPart X = X := by
        rw [symPart, hXs.eq, ← two_smul ℝ X, smul_smul]; norm_num
      refine ⟨?_, hXs⟩
      change X.trace ≤ ((d : ℝ) + α) * lamMin (symPart X)
      rwa [hsym]

/-! ## Clause (3): the Loewner order in other coordinates -/

section Smooth

open scoped Matrix.Norms.Elementwise ContDiff

theorem contDiff_det_mat : ContDiff ℝ ∞ (fun S : Mat d => S.det) := by
  have hfun : (fun S : Mat d => S.det) = fun S => ∑ σ : Equiv.Perm (Fin d),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, S (σ i) i := by
    funext S; rw [det_apply']
  rw [hfun]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact contDiff_apply_apply ℝ ℝ (σ i) i

/-- `S ↦ (det S)^p S` is smooth on `PD(d)`. -/
theorem contDiffOn_det_rpow_smul (p : ℝ) :
    ContDiffOn ℝ ∞ (fun S : Mat d => (S.det ^ p) • S) (pdSet d) := by
  intro S hS
  have hS : S.PosDef := hS
  refine ContDiffAt.contDiffWithinAt ?_
  exact ((contDiff_det_mat.contDiffAt).rpow_const_of_ne hS.det_pos.ne').smul contDiffAt_id

end Smooth

/-- The derivative of `Φ_α` at `Σ` in the direction `V`. -/
theorem hasDerivAt_phiAlpha_dir (α : ℝ) {S : Mat d} (hS : S.PosDef) (V : Mat d) (i j : Fin d) :
    HasDerivAt (fun t : ℝ => phiAlpha d α (S + t • V) i j)
      ((S.det ^ (-(1 : ℝ) / ((d : ℝ) + α)) •
        (msqrt S * (relStep S V + ((-(1 : ℝ) / ((d : ℝ) + α)) * (relStep S V).trace) • 1) *
          msqrt S)) i j) 0 := by
  set γ : ℝ → Mat d := fun t => S + t • V
  have hγ0 : γ 0 = S := by simp [γ]
  have hder : ∀ a b, HasDerivAt (fun u => γ u a b) (V a b) 0 := fun a b => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (V a b)).const_add (S a b)
    simpa [γ] using this
  have hm : mderiv γ 0 = V := by
    ext a b
    exact (hder a b).deriv
  have h := hasDerivAt_phiAlpha_curve α (γ := γ) (t := 0) (by rw [hγ0]; exact hS)
    (fun a b => by rw [hm]; exact hder a b) i j
  rw [hm, hγ0] at h
  exact h

/-- The image of `Σ^{1/2}C_αΣ^{1/2}` under the derivative of `Φ_α` at `Σ` is `PSD(d)`. -/
theorem image_deriv_phiAlpha (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {S : Mat d} (hS : S.PosDef) :
    (fun V => mderiv (fun t : ℝ => phiAlpha d α (S + t • V)) 0) ''
        ((fun X => msqrt S * X * msqrt S) '' stableGenCone d α) = psdSet d := by
  haveI : NeZero d := ⟨by omega⟩
  set s := -(1 : ℝ) / ((d : ℝ) + α)
  have hdα : 0 < (d : ℝ) + α := by positivity
  have hDs : 0 < S.det ^ s := Real.rpow_pos_of_pos hS.det_pos s
  have hm : ∀ V : Mat d, mderiv (fun t : ℝ => phiAlpha d α (S + t • V)) 0 =
      S.det ^ s • (msqrt S * (relStep S V + (s * (relStep S V).trace) • 1) * msqrt S) := by
    intro V
    ext i j
    exact (hasDerivAt_phiAlpha_dir α hS V i j).deriv
  have hcong : ∀ Z : Mat d, Z.PosSemidef → (msqrt S * Z * msqrt S).PosSemidef := fun Z hZ => by
    have := (posSemidef_relStep_iff hS (msqrt S * Z * msqrt S)).1
    rw [relStep_msqrt_mul hS] at this
    exact this hZ
  ext P
  constructor
  · rintro ⟨V, ⟨Y, hY, rfl⟩, rfl⟩
    beta_reduce
    rw [hm, relStep_msqrt_mul hS]
    exact (hcong _ (stableGenCone_shift_posSemidef hα.le hY)).smul hDs.le
  · intro hP
    have hP : P.PosSemidef := hP
    set Z := (S.det ^ s)⁻¹ • relStep S P
    have hZ : Z.PosSemidef := ((posSemidef_relStep_iff hS P).2 hP).smul (inv_pos.2 hDs).le
    have h1ds' : 1 + (d : ℝ) * s = α / ((d : ℝ) + α) := by
      simp only [s]
      field_simp
      ring
    have h1ds : 1 + (d : ℝ) * s ≠ 0 := by rw [h1ds']; positivity
    have h1ds2 : 1 + s * (d : ℝ) ≠ 0 := by rw [mul_comm]; exact h1ds
    set Y := Z - ((s / (1 + (d : ℝ) * s)) * Z.trace) • (1 : Mat d)
    have htr : Y.trace = Z.trace / (1 + (d : ℝ) * s) := by
      have : Y.trace = Z.trace - s / (1 + (d : ℝ) * s) * Z.trace * d := by
        simp only [Y, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
      rw [this, eq_div_iff h1ds, sub_mul, show s / (1 + (d : ℝ) * s) * Z.trace * d *
        (1 + (d : ℝ) * s) = s * Z.trace * d by field_simp]
      ring
    have hYZ : Y + (s * Y.trace) • (1 : Mat d) = Z := by
      rw [htr]
      simp only [Y]
      rw [sub_add_eq_add_sub, add_sub_assoc, ← sub_smul]
      rw [show s * (Z.trace / (1 + (d : ℝ) * s)) - s / (1 + (d : ℝ) * s) * Z.trace = 0 by ring,
        zero_smul, add_zero]
    have hYs : Y.IsSymm := by
      have hZs : Z.IsSymm := isSymm_of_isHermitian hZ.isHermitian
      exact hZs.sub (isSymm_one.smul _)
    have hYC : Y ∈ stableGenCone d α := by
      rw [stableGenCone_pos_eq hd hα]
      refine ⟨hYs, ?_⟩
      have hYh := isHermitian_of_isSymm hYs
      have hsh : (Y - (Y.trace / ((d : ℝ) + α)) • (1 : Mat d)).PosSemidef := by
        convert hZ using 1
        rw [← hYZ, sub_eq_add_neg, ← neg_smul]
        congr 2
        simp only [s]
        ring
      have := (posSemidef_sub_smul_one_iff hYh _).1 hsh
      rw [← lamMin_eq_eigUp_zero hYh, div_le_iff₀ hdα] at this
      linarith
    refine ⟨msqrt S * Y * msqrt S, ⟨Y, hYC, rfl⟩, ?_⟩
    simp only
    rw [hm, relStep_msqrt_mul hS, hYZ]
    simp only [Z, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hDs.ne', one_smul,
      msqrt_mul_relStep hS]

open scoped Matrix.Norms.Elementwise ContDiff in
/-- **`prop:stable-order-generated`(3)**, the Loewner order in other coordinates: for
`0 < α < ∞`, `Φ_α(Σ) = (det Σ)^{-1/(d+α)}Σ` is a diffeomorphism of `PD(d)` with inverse
`T ↦ (det T)^{1/α}T`; `Σ ≼_α Σ'` if and only if `Φ_α(Σ) ≤ Φ_α(Σ')`; the derivative of `Φ_α` at `Σ`
maps the cone `Σ^{1/2}C_αΣ^{1/2}` onto `PSD(d)`; `Φ_α(AΣAᵀ) = ψ_α(A)Φ_α(Σ)ψ_α(A)ᵀ` with
`ψ_α(A) = |det A|^{-1/(d+α)}A` an automorphism of `GL(d)`, which maps `{A : I ≼_α AAᵀ}` onto
`{A : AAᵀ ≥ I}`. -/
theorem stable_order_loewner_coords (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    BijOn (phiAlpha d α) (pdSet d) (pdSet d) ∧
      InvOn (fun T : Mat d => (T.det ^ (1 / α)) • T) (phiAlpha d α) (pdSet d) (pdSet d) ∧
      ContDiffOn ℝ ∞ (phiAlpha d α) (pdSet d) ∧
      ContDiffOn ℝ ∞ (fun T : Mat d => (T.det ^ (1 / α)) • T) (pdSet d) ∧
      (∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (causalLE (stableGenCone d α) S S' ↔ loewnerLE (phiAlpha d α S) (phiAlpha d α S'))) ∧
      (∀ S : Mat d, S.PosDef →
        (∀ V : Mat d, ∀ i j, DifferentiableAt ℝ (fun t : ℝ => phiAlpha d α (S + t • V) i j) 0) ∧
        (fun V => mderiv (fun t : ℝ => phiAlpha d α (S + t • V)) 0) ''
            ((fun X => msqrt S * X * msqrt S) '' stableGenCone d α) = psdSet d) ∧
      (∀ A ∈ glSet d, ∀ S : Mat d, S.PosDef →
        phiAlpha d α (act A S) = act (psiAlpha d α A) (phiAlpha d α S)) ∧
      (∀ A ∈ glSet d, ∀ B ∈ glSet d, psiAlpha d α (A * B) = psiAlpha d α A * psiAlpha d α B) ∧
      BijOn (psiAlpha d α) (glSet d) (glSet d) ∧
      psiAlpha d α '' {A | A ∈ glSet d ∧ causalLE (stableGenCone d α) 1 (A * Aᵀ)} =
        {A | A ∈ glSet d ∧ loewnerLE 1 (A * Aᵀ)} := by
  have hinvΦ := phiAlpha_invOn (d := d) hα
  have hinvψ := psiAlpha_invOn (d := d) hα
  have hψinv_gl : ∀ A ∈ glSet d, (|A.det| ^ (1 / α)) • A ∈ glSet d := by
    intro A hA
    have hD : 0 < |A.det| := abs_pos.2 ((isUnit_iff_ne_zero).1 hA)
    change IsUnit ((|A.det| ^ (1 / α)) • A).det
    rw [det_smul]
    exact (mul_ne_zero (pow_ne_zero _ (Real.rpow_pos_of_pos hD _).ne')
      ((isUnit_iff_ne_zero).1 hA)).isUnit
  refine ⟨hinvΦ.bijOn (fun S hS => phiAlpha_posDef α hS)
      (fun T hT => (show T.PosDef from hT).smul (Real.rpow_pos_of_pos hT.det_pos _)),
    hinvΦ, contDiffOn_det_rpow_smul _, contDiffOn_det_rpow_smul _,
    fun S S' hS hS' => ?_, fun S hS => ⟨fun V i j =>
      (hasDerivAt_phiAlpha_dir α hS V i j).differentiableAt, image_deriv_phiAlpha hd hα hS⟩,
    fun A _ S hS => phiAlpha_act α A hS, fun A _ B _ => psiAlpha_mul α A B,
    hinvψ.bijOn (fun A hA => psiAlpha_mem_glSet α hA) hψinv_gl, ?_⟩
  · rw [((stable_order_pos hd hα).2 S S' hS hS').1, phiAlpha_le_iff hd hα hS hS']
    have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
    exact ⟨fun h => h.2.2.2, fun h => ⟨hS, hS', hM, h⟩⟩
  · ext B
    constructor
    · rintro ⟨A, ⟨hA, hcA⟩, rfl⟩
      exact ⟨psiAlpha_mem_glSet α hA, (causalLE_one_mul_transpose_iff hd hα hA).2.1 hcA⟩
    · rintro ⟨hB, hlB⟩
      refine ⟨_, ⟨hψinv_gl B hB, ?_⟩, hinvψ.2 hB⟩
      rw [(causalLE_one_mul_transpose_iff hd hα (hψinv_gl B hB)).2, hinvψ.2 hB]
      exact hlB

end AffineHemigroup
