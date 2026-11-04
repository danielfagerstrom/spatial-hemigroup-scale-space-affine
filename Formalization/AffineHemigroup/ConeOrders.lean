/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SpectralCones
import AffineHemigroup.StableExponentCone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# `thm:cone-orders`: the order of a cone field

Blueprint: `blueprint/src/parts/05-wedges.tex`, `thm:cone-orders`, the cone field and clause (1)
(wave 2, group F, Q-0281). Three parts.

* **The geodesic** `γ(t) = Σ^{1/2}M^tΣ^{1/2}` with `M = e^X`, `X ∈ C`: in an eigenbasis of `X`
  its entries are finite sums of exponentials, so it is smooth, and with
  `A = Σ^{1/2}Ve^{tx/2}` it is `AAᵀ` with derivative `A diag(x) Aᵀ`, so `γ^{-1/2}γ'γ^{-1/2}` is an
  orthogonal conjugate of `diag(x) ∈ C`. Lean core.
* **Causal curves end in the order.** For `w ∈ D^#`, `F_w(Σ, Σ') = ∑ᵢ w↓ᵢ ℓᵢ(Σ^{-1/2}Σ'Σ^{-1/2})`
  is superadditive (`lem:spectral-cones`(2), hence ledger A9), `g(t) = F_w(γ(0), γ(t))` is
  absolutely continuous (dominated by the entries of `γ`: `λ↑` is Lipschitz by
  `lem:spectral-cones`(1) and `log` is Lipschitz above the least eigenvalue on `[0,1]`), and at
  almost every `t` its right slopes are at least `F_w(γ(t), γ(t+h))/h → ∑ᵢ w↓ᵢ λ↑ᵢ(Y) ≥ 0`,
  `Y = γ^{-1/2}γ'γ^{-1/2} ∈ C`, read through `λ↑(I + hY + o(h)) = 1 + hλ↑(Y) + o(h)` and
  `(x-1)/x ≤ log x ≤ x - 1`. So `g(1) = ∫₀¹ g' ≥ 0` (Mathlib's fundamental theorem for absolutely
  continuous functions).
* The order properties, from `prop:invariant-orders` and `lem:spectral-cones`(5).
-/

namespace AffineHemigroup

open Matrix Filter Set MeasureTheory
open scoped Topology

variable {d : ℕ}

/-! ## Absolute continuity by domination -/

/-- **A function dominated by absolutely continuous ones is absolutely continuous**: if
`|f s - f t| ≤ K ∑ⱼ |fⱼ s - fⱼ t|` on `[a, b]` and every `fⱼ` is absolutely continuous there, so
is `f`. -/
theorem AbsolutelyContinuousOnInterval.of_dominated {ι : Type*} [Fintype ι] {f : ℝ → ℝ}
    {fs : ι → ℝ → ℝ} {a b K : ℝ} (hfs : ∀ j, AbsolutelyContinuousOnInterval (fs j) a b)
    (hdom : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, |f s - f t| ≤ K * ∑ j, |fs j s - fs j t|) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hfs ⊢
  have hsum := (tendsto_finsetSum Finset.univ fun j _ => hfs j).const_mul K
  rw [Finset.sum_const_zero, mul_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ hsum
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with E hE
  calc ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, K * ∑ j, |fs j (E.2 i).1 - fs j (E.2 i).2| :=
        Finset.sum_le_sum fun i hi => by
          rw [Real.dist_eq]
          exact hdom _ (hE.1 i hi).1 _ (hE.1 i hi).2
    _ = K * ∑ j, ∑ i ∈ Finset.range E.1, dist (fs j (E.2 i).1) (fs j (E.2 i).2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Real.dist_eq]

/-- `|log x - log y| ≤ |x - y|/m` for `x, y ≥ m > 0`. -/
theorem abs_log_sub_log_le {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ m⁻¹ * |x - y| := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  have key : ∀ {u v : ℝ}, m ≤ u → m ≤ v → v ≤ u → Real.log u - Real.log v ≤ m⁻¹ * (u - v) := by
    intro u v hu hv hvu
    have hv0 : 0 < v := hm.trans_le hv
    have h1 : Real.log u - Real.log v = Real.log (u / v) := by
      rw [Real.log_div (hm.trans_le hu).ne' hv0.ne']
    have h2 : Real.log (u / v) ≤ u / v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hm.trans_le hu) hv0)
    have h3 : u / v - 1 = (u - v) / v := by field_simp
    have h4 : (u - v) / v ≤ (u - v) / m := div_le_div_of_nonneg_left (by linarith) hm hv
    rw [h1]
    calc Real.log (u / v) ≤ (u - v) / m := by linarith
      _ = m⁻¹ * (u - v) := by ring
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (by linarith [Real.log_le_log hy0 h]), abs_of_nonneg (by linarith)]
    exact key hx hy h
  · rw [abs_of_nonpos (by linarith [Real.log_le_log hx0 h]), abs_of_nonpos (by linarith)]
    have := key hy hx h
    linarith

/-- `‖x ↦ Ex‖ ≤ ∑_{a,b} |E_ab|`. -/
theorem norm_lin_le_sum (E : Mat d) : ‖lin E‖ ≤ ∑ a, ∑ b, |E a b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => abs_nonneg _) fun x => ?_
  have hx : ∀ b, |x b| ≤ ‖x‖ := fun b => by
    have := PiLp.norm_apply_le x b
    simpa [Real.norm_eq_abs] using this
  have hy : ∀ y : Rd d, ‖y‖ ≤ ∑ a, |y a| := fun y => by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sqrt_le_left (Finset.sum_nonneg fun a _ => abs_nonneg _)]
    calc ∑ a, ‖y a‖ ^ 2 = ∑ a, |y a| * |y a| := by
          simp [Real.norm_eq_abs, sq]
      _ ≤ ∑ a, |y a| * ∑ b, |y b| := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun b => |y b|)
            (fun b _ => abs_nonneg _) (Finset.mem_univ a)) (abs_nonneg _)
      _ = (∑ a, |y a|) ^ 2 := by rw [← Finset.sum_mul, sq]
  calc ‖lin E x‖ ≤ ∑ a, |(lin E x) a| := hy _
    _ ≤ ∑ a, ∑ b, |E a b| * ‖x‖ := Finset.sum_le_sum fun a _ => by
        have : (lin E x) a = ∑ b, E a b * x b := by
          rw [ofLp_lin]
          rfl
        rw [this]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx b) (abs_nonneg _)
    _ = (∑ a, ∑ b, |E a b|) * ‖x‖ := by rw [Finset.sum_mul]; simp only [Finset.sum_mul]

/-- `λ↑` along a filter on which the matrices are eventually symmetric. -/
theorem tendsto_eigUp' {ι : Type*} {l : Filter ι} {Xs : ι → Mat d} {X : Mat d}
    (hXs : ∀ᶠ n in l, (Xs n).IsSymm) (hX : X.IsSymm) (h : Tendsto Xs l (𝓝 X)) :
    Tendsto (fun n => eigUp (Xs n)) l (𝓝 (eigUp X)) := by
  have hlin : Tendsto (fun n => ‖lin (Xs n - X)‖) l (𝓝 0) := by
    have h1 : Tendsto (fun n => Xs n - X) l (𝓝 0) := by
      simpa using h.sub_const X
    have h2 := (continuous_lin.tendsto (0 : Mat d)).comp h1
    rw [show lin (0 : Mat d) = 0 from map_zero _] at h2
    simpa using h2.norm
  refine tendsto_pi_nhds.2 fun k => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun n => (2 * (k : ℝ) + 1) * ‖lin (Xs n - X)‖) l (𝓝 0) := by
    simpa using hlin.const_mul (2 * (k : ℝ) + 1)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hc
  filter_upwards [hXs] with n hn
  rw [Real.norm_eq_abs]
  exact eigUp_lipschitz hn hX k

/-! ## Superadditivity of `F_w` -/

/-- **`F_w(Σ, Σ') = ∑ᵢ w↓ᵢ ℓᵢ(Σ^{-1/2}Σ'Σ^{-1/2})`**, `ℓ` read increasing. -/
noncomputable def coneFunctional (w : Fin d → ℝ) (S S' : Mat d) : ℝ :=
  ∑ i, sortDown w i * sortUp (logSpec (relStep S S')) i

theorem stepSet_pdSet : IsStepSet (pdSet d) :=
  ⟨subset_refl _, fun M hM Q hQ => by
    have := (posDef_act_iff (orthSet_subset_glSet hQ) M).2 hM
    rwa [act] at this⟩

/-- `ℓ(QᵀNQ) = ℓ(N)` for `Q` orthogonal. -/
theorem logSpec_conj_orth {Q : Mat d} (hQ : Q ∈ orthSet d) {N : Mat d} (hN : N.PosDef) :
    logSpec (Qᵀ * N * Q) = logSpec N := by
  have hQ' : Qᵀ * Qᵀᵀ = 1 := by rw [transpose_transpose]; exact orth_transpose_mul hQ
  have hN' : (Qᵀ * N * Q).PosDef := by
    have := (posDef_act_iff (orthSet_subset_glSet (transpose_mem_orthSet hQ)) N).2 hN
    rwa [act, transpose_transpose] at this
  have he : eigUp (Qᵀ * N * Q) = eigUp N := by
    have := eigUp_conj_orth hQ' N
    rwa [transpose_transpose] at this
  rw [logSpec_eq hN', logSpec_eq hN, he]

/-- **Superadditivity**: `F_w(Σ, Σ'') ≥ F_w(Σ, Σ') + F_w(Σ', Σ'')` for `Σ, Σ', Σ'' ∈ PD(d)`; it
reads `lem:spectral-cones-products`, hence ledger A9. -/
theorem coneFunctional_superadditive (hd : 1 ≤ d) (w : Fin d → ℝ) {S S' S'' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (hS'' : S''.PosDef) :
    coneFunctional w S S' + coneFunctional w S' S'' ≤ coneFunctional w S S'' := by
  have h₁ : stepLE (pdSet d) S S' := ⟨hS, hS', (posDef_relStep_iff hS S').2 hS'⟩
  have h₂ : stepLE (pdSet d) S' S'' := ⟨hS', hS'', (posDef_relStep_iff hS' S'').2 hS''⟩
  obtain ⟨Q, hQ, hrel, -⟩ := stepLE_compose hd stepSet_pdSet hS hS' hS'' h₁ h₂
  set M := relStep S S'
  set N := relStep S' S''
  have hM : M.PosDef := h₁.2.2
  have hN : N.PosDef := h₂.2.2
  have hN' : (Qᵀ * N * Q).PosDef := by
    have := (posDef_act_iff (orthSet_subset_glSet (transpose_mem_orthSet hQ)) N).2 hN
    rwa [act, transpose_transpose] at this
  have hmaj := logSpec_product_majorized hd hM hN'
  rw [logSpec_conj_orth hQ hN] at hmaj
  have hmono := sum_sortDown_mul_sortUp_mono hmaj w
  have hmMN : Monotone (logSpec M + logSpec N) := (logSpec_monotone hM).add (logSpec_monotone hN)
  have hsum : sortUp (logSpec M + logSpec N) = sortUp (logSpec M) + sortUp (logSpec N) := by
    rw [sortUp_of_monotone hmMN,
      sortUp_of_monotone (logSpec_monotone hM), sortUp_of_monotone (logSpec_monotone hN)]
  rw [hsum] at hmono
  unfold coneFunctional
  rw [hrel]
  calc ∑ i, sortDown w i * sortUp (logSpec M) i + ∑ i, sortDown w i * sortUp (logSpec N) i
      = ∑ i, sortDown w i * (sortUp (logSpec M) + sortUp (logSpec N)) i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
    _ ≤ _ := hmono

/-- `F_w(Σ, Σ) = 0`. -/
theorem coneFunctional_self (w : Fin d → ℝ) {S : Mat d} (hS : S.PosDef) :
    coneFunctional w S S = 0 := by
  unfold coneFunctional
  rw [relStep_self hS]
  have h1 : logSpec (1 : Mat d) = 0 := by
    have := logSpec_mexp (d := d) (X := 0) (isHermitian_of_isSymm isSymm_zero)
    rw [mexp_zero, eigUp_zero] at this
    exact this
  rw [h1, sortUp_of_monotone (fun _ _ _ => le_rfl)]
  simp

/-! ## The geodesic `Σ^{1/2}M^tΣ^{1/2}` -/

/-- The entries of `W diag(w) Wᵀ`. -/
theorem udiag_apply (W : Mat d) (w : Fin d → ℝ) (i j : Fin d) :
    udiag W w i j = ∑ k, W i k * w k * W j k := by
  rw [udiag, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem smul_udiag (t : ℝ) (V : Mat d) (x : Fin d → ℝ) : t • udiag V x = udiag V (t • x) := by
  rw [udiag, udiag, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- `Σ^{-1/2}(AYAᵀ)Σ^{-1/2} = QYQᵀ` with `Q = Σ^{-1/2}A`. -/
theorem relStep_factor (S A Y : Mat d) :
    relStep S (A * Y * Aᵀ) = ((msqrt S)⁻¹ * A) * Y * ((msqrt S)⁻¹ * A)ᵀ := by
  rw [relStep, transpose_mul, msqrt_inv_transpose]
  simp only [Matrix.mul_assoc]

/-- **The geodesic in an eigenbasis**: if the relative step is `e^{V diag(x) Vᵀ}`, then
`γ(t) = W diag(e^{tx}) Wᵀ` with `W = Σ^{1/2}V`. -/
theorem stepGeodesic_eq {S S' : Mat d} {V : Mat d} (hV : V * Vᵀ = 1) {x : Fin d → ℝ}
    (hrel : relStep S S' = mexp (udiag V x)) (t : ℝ) :
    stepGeodesic S S' t = udiag (msqrt S * V) (fun k => Real.exp (t * x k)) := by
  have hX : (udiag V x).IsHermitian := udiag_isHermitian V x
  unfold stepGeodesic
  rw [hrel, mrpow_eq_mexp (posDef_mexp (isSymm_of_isHermitian hX)) t, mlog_mexp hX, smul_udiag,
    mexp_udiag hV]
  simp only [udiag, transpose_mul, msqrt_transpose, Matrix.mul_assoc, Pi.smul_apply, smul_eq_mul]

theorem hasDerivAt_udiag_exp (W : Mat d) (x : Fin d → ℝ) (i j : Fin d) (t : ℝ) :
    HasDerivAt (fun s => udiag W (fun k => Real.exp (s * x k)) i j)
      (udiag W (fun k => x k * Real.exp (t * x k)) i j) t := by
  simp only [udiag_apply]
  apply HasDerivAt.fun_sum
  intro k _
  have h1 : HasDerivAt (fun s => Real.exp (s * x k)) (Real.exp (t * x k) * x k) t := by
    simpa using ((hasDerivAt_id t).mul_const (x k)).exp
  exact ((h1.const_mul (W i k)).mul_const (W j k)).congr_deriv (by ring)

theorem contDiff_udiag_exp (W : Mat d) (x : Fin d → ℝ) (i j : Fin d) :
    ContDiff ℝ 1 (fun s => udiag W (fun k => Real.exp (s * x k)) i j) := by
  simp only [udiag_apply]
  fun_prop

/-- `γ(0) = Σ` and `γ(1) = Σ'`. -/
theorem stepGeodesic_ends {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) :
    stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S' := by
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  unfold stepGeodesic
  rw [mrpow_eq_mexp hM, mrpow_eq_mexp hM, zero_smul, mexp_zero, Matrix.mul_one,
    msqrt_mul_self hS.posSemidef, one_smul, mexp_mlog hM, msqrt_mul_relStep hS]
  exact ⟨rfl, rfl⟩

/-- `γ(t) ∈ PD(d)` for every `t`. -/
theorem stepGeodesic_posDef {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (t : ℝ) :
    (stepGeodesic S S' t).PosDef := by
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  unfold stepGeodesic
  rw [mrpow_eq_mexp hM]
  exact posDef_msqrt_conj hS (posDef_mexp ((mlog_isSymm _).smul t))

/-- **`thm:cone-orders`(1), the geodesic**: if the relative step lies in `exp C`, the geodesic
`Σ^{1/2}M^tΣ^{1/2}` is `C`-causal from `Σ` to `Σ'`. Lean core. -/
theorem stepGeodesic_causal {C : Set (Mat d)} (hCsym : C ⊆ symSet d) (hO : IsOrthInvariant C)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hM : relStep S S' ∈ expSet C) :
    IsCausalCurve C (stepGeodesic S S') ∧ stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S' := by
  obtain ⟨X, hXC, hMX⟩ := hM
  have hXs : X.IsSymm := hCsym hXC
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hXs)
  set x := eigUp X
  have hV' : Vᵀ * V = 1 := transpose_mul_self_of_mul_transpose hV
  have hrel : relStep S S' = mexp (udiag V x) := by rw [hMX, ← hXV]
  have hγ := stepGeodesic_eq hV hrel
  set W := msqrt S * V
  have hdiag : diagonal x ∈ C := by
    have h := hO Vᵀ (transpose_mem_orthSet (mem_orthSet_of hV)) X hXC
    rw [transpose_transpose] at h
    convert h using 1
    rw [hXV, udiag]
    simp only [← Matrix.mul_assoc, hV', Matrix.one_mul]
    rw [Matrix.mul_assoc, hV', Matrix.mul_one]
  have hderiv : ∀ t, mderiv (stepGeodesic S S') t =
      udiag W (fun k => x k * Real.exp (t * x k)) := by
    intro t
    ext i j
    simp only [mderiv, Matrix.of_apply, hγ]
    exact (hasDerivAt_udiag_exp W x i j t).deriv
  refine ⟨⟨fun t _ => stepGeodesic_posDef hS hS' t, fun i j => ?_,
    Eventually.of_forall fun t => ?_⟩, stepGeodesic_ends hS hS'⟩
  · simp only [hγ]
    exact (contDiff_udiag_exp W x i j).contDiffOn.absolutelyContinuousOnInterval
  · set A := W * diagonal (fun k => Real.exp (t * x k / 2))
    have hhalf : ∀ k, Real.exp (t * x k / 2) * Real.exp (t * x k / 2) = Real.exp (t * x k) :=
      fun k => by rw [← Real.exp_add, add_halves]
    have hAA : A * Aᵀ = stepGeodesic S S' t := by
      rw [hγ, udiag, transpose_mul, diagonal_transpose]
      simp only [A, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
      simp only [hhalf]
    have hAY : A * diagonal x * Aᵀ = mderiv (stepGeodesic S S') t := by
      rw [hderiv, udiag, transpose_mul, diagonal_transpose]
      simp only [A, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
        ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
      congr 3
      funext k
      rw [mul_comm (Real.exp _) (x k), mul_assoc, hhalf]
    rw [← hAY, relStep_factor]
    have hQ := msqrt_inv_mul_mem_orthSet (stepGeodesic_posDef hS hS' t) hAA
    exact hO _ hQ _ hdiag

/-! ## Causal curves end in the order -/

theorem udiag_add_udiag (V : Mat d) (a b : Fin d → ℝ) :
    udiag V a + udiag V b = udiag V (a + b) := by
  rw [udiag, udiag, udiag, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  rfl

/-- `λ↑(I + hY) = 1 + hλ↑(Y)` for symmetric `Y` and `h ≥ 0`. -/
theorem eigUp_one_add_smul {Y : Mat d} (hY : Y.IsSymm) {h : ℝ} (hh : 0 ≤ h) :
    eigUp (1 + h • Y) = fun i => 1 + h * eigUp Y i := by
  obtain ⟨V, hV, hYV⟩ := exists_udiag_eigUp (isHermitian_of_isSymm hY)
  have he : 1 + h • Y = udiag V (fun i => 1 + h * eigUp Y i) := by
    conv_lhs => rw [hYV, ← udiag_one hV, smul_udiag, udiag_add_udiag]
    rfl
  rw [he, eigUp_udiag hV]
  exact sortUp_of_monotone fun i j hij => by
    have := eigUp_monotone (isHermitian_of_isSymm hY) hij
    nlinarith

theorem continuous_relStep (S : Mat d) : Continuous (relStep S) := by
  unfold relStep
  fun_prop

/-- The relative step `γ(t)^{-1/2}γ(t+h)γ(t)^{-1/2} = I + hY + o(h)` read on `λ↑`: the right
slopes of `λ↑ᵢ` at `h = 0` tend to `λ↑ᵢ(Y)`, `Y = γ(t)^{-1/2}γ'(t)γ(t)^{-1/2}`. -/
theorem tendsto_eigUp_slope {γ : ℝ → Mat d} {t : ℝ} {γ' : Mat d}
    (hder : ∀ a b, HasDerivAt (fun s => γ s a b) (γ' a b) t)
    (hsymm : ∀ᶠ h in 𝓝[>] (0 : ℝ), (γ (t + h)).IsSymm) (ht : (γ t).PosDef)
    (hY : (relStep (γ t) γ').IsSymm) (i : Fin d) :
    Tendsto (fun h => h⁻¹ * (eigUp (relStep (γ t) (γ (t + h))) i - 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (eigUp (relStep (γ t) γ') i)) := by
  set Y := relStep (γ t) γ'
  have hslope : Tendsto (fun h : ℝ => h⁻¹ • (γ (t + h) - γ t)) (𝓝[>] (0 : ℝ)) (𝓝 γ') := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
    have := (hder a b).tendsto_slope_zero_right
    simpa using this
  set E : ℝ → Mat d := fun h => relStep (γ t) (h⁻¹ • (γ (t + h) - γ t) - γ')
  have hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => h⁻¹ • (γ (t + h) - γ t) - γ') (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hslope.sub_const γ'
    have h2 := ((continuous_relStep (γ t)).tendsto 0).comp h1
    rw [show relStep (γ t) 0 = 0 by simp [relStep]] at h2
    exact h2
  have hEn : Tendsto (fun h => (2 * (i : ℝ) + 1) * ‖lin (E h)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 := (continuous_lin.tendsto (0 : Mat d)).comp hE
    rw [show lin (0 : Mat d) = 0 from map_zero _] at h2
    simpa using h2.norm.const_mul (2 * (i : ℝ) + 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun h => norm_nonneg _) ?_ hEn
  filter_upwards [hsymm, self_mem_nhdsWithin] with h hsh hpos
  have hpos : 0 < h := hpos
  have hP : (relStep (γ t) (γ (t + h))).IsSymm := by
    unfold relStep
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, msqrt_inv_transpose, hsh.eq,
      Matrix.mul_assoc]
  have h1Y : (1 + h • Y).IsSymm := isSymm_one.add (hY.smul h)
  have hdiff : relStep (γ t) (γ (t + h)) - (1 + h • Y) = h • E h := by
    simp only [E, relStep_sub, relStep_smul, smul_sub, smul_smul, mul_inv_cancel₀ hpos.ne',
      one_smul, relStep_self ht, Y]
    abel
  have hlip := eigUp_lipschitz hP h1Y i
  rw [hdiff, eigUp_one_add_smul hY hpos.le, show lin (h • E h) = h • lin (E h) from
    lin_smul h (E h), norm_smul, Real.norm_of_nonneg hpos.le] at hlip
  rw [Real.norm_eq_abs]
  have : h⁻¹ * (eigUp (relStep (γ t) (γ (t + h))) i - 1) - eigUp Y i =
      h⁻¹ * (eigUp (relStep (γ t) (γ (t + h))) i - (1 + h * eigUp Y i)) := by
    field_simp
    ring
  rw [this, abs_mul, abs_of_pos (inv_pos.2 hpos)]
  calc h⁻¹ * |eigUp (relStep (γ t) (γ (t + h))) i - (1 + h * eigUp Y i)|
      ≤ h⁻¹ * ((2 * (i : ℝ) + 1) * (h * ‖lin (E h)‖)) :=
        mul_le_mul_of_nonneg_left hlip (inv_nonneg.2 hpos.le)
    _ = (2 * (i : ℝ) + 1) * ‖lin (E h)‖ := by field_simp

/-- From the slopes of `x(h) → 1` to those of `log x(h)`: `(x - 1)/x ≤ log x ≤ x - 1`. -/
theorem tendsto_log_slope {u : ℝ → ℝ} {L : ℝ}
    (hu : Tendsto (fun h => h⁻¹ * (u h - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < u h) :
    Tendsto (fun h => h⁻¹ * Real.log (u h)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hu1 : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have := (h0.mul hu).add_const 1
    rw [zero_mul, zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh : (0 : ℝ) < h := hh
    field_simp
    ring
  have hlow : Tendsto (fun h => h⁻¹ * (u h - 1) * (u h)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have := hu.mul (hu1.inv₀ one_ne_zero)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hu ?_ ?_
  · filter_upwards [hpos, self_mem_nhdsWithin] with h hu0 hh
    have hh : (0 : ℝ) < h := hh
    have := Real.one_sub_inv_le_log_of_pos hu0
    have e : h⁻¹ * (u h - 1) * (u h)⁻¹ = h⁻¹ * (1 - (u h)⁻¹) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hh.le)
  · filter_upwards [hpos, self_mem_nhdsWithin] with h hu0 hh
    have hh : (0 : ℝ) < h := hh
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu0) (inv_nonneg.2 hh.le)

/-- `F_w(Σ, Σ') = ∑ᵢ w↓ᵢ log λ↑ᵢ(Σ^{-1/2}Σ'Σ^{-1/2})`. -/
theorem coneFunctional_eq (w : Fin d → ℝ) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) :
    coneFunctional w S S' = ∑ i, sortDown w i * Real.log (eigUp (relStep S S') i) := by
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  unfold coneFunctional
  rw [sortUp_of_monotone (logSpec_monotone hM), logSpec_eq hM]

/-- **The slope of `F_w` along a curve**: `F_w(γ(t), γ(t+h))/h → ∑ᵢ w↓ᵢ λ↑ᵢ(Y)` as `h ↓ 0`. -/
theorem tendsto_coneFunctional_slope (w : Fin d → ℝ) {γ : ℝ → Mat d} {t : ℝ} {γ' : Mat d}
    (hder : ∀ a b, HasDerivAt (fun s => γ s a b) (γ' a b) t)
    (hpd : ∀ᶠ h in 𝓝[>] (0 : ℝ), (γ (t + h)).PosDef) (ht : (γ t).PosDef)
    (hY : (relStep (γ t) γ').IsSymm) :
    Tendsto (fun h => h⁻¹ * coneFunctional w (γ t) (γ (t + h))) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i, sortDown w i * eigUp (relStep (γ t) γ') i)) := by
  have hsymm : ∀ᶠ h in 𝓝[>] (0 : ℝ), (γ (t + h)).IsSymm :=
    hpd.mono fun h hh => isSymm_of_isHermitian hh.isHermitian
  have hi : ∀ i, Tendsto (fun h => h⁻¹ * Real.log (eigUp (relStep (γ t) (γ (t + h))) i))
      (𝓝[>] (0 : ℝ)) (𝓝 (eigUp (relStep (γ t) γ') i)) := fun i =>
    tendsto_log_slope (tendsto_eigUp_slope hder hsymm ht hY i)
      (hpd.mono fun h hh => eigUp_pos ((posDef_relStep_iff ht _).2 hh) i)
  have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    (hi i).const_mul (sortDown w i)
  refine hsum.congr' ?_
  filter_upwards [hpd] with h hh
  rw [coneFunctional_eq w ht hh, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A causal curve is continuous on `[0,1]`. -/
theorem IsCausalCurve.continuousOn {C : Set (Mat d)} {γ : ℝ → Mat d} (hγ : IsCausalCurve C γ) :
    ContinuousOn γ (Icc 0 1) := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  have := (hγ.absolutelyContinuous a b).continuousOn
  rwa [uIcc_of_le zero_le_one] at this

/-- **A uniform lower bound for the spectrum along a causal curve**: the least eigenvalue of
`γ(0)^{-1/2}γ(s)γ(0)^{-1/2}` is continuous on `[0,1]` and positive, hence bounded below. -/
theorem IsCausalCurve.exists_eigUp_lower [NeZero d] {C : Set (Mat d)} {γ : ℝ → Mat d}
    (hγ : IsCausalCurve C γ) :
    ∃ m > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, m ≤ eigUp (relStep (γ 0) (γ s)) i := by
  have h0 : (γ 0).PosDef := hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩
  have hN : ∀ s ∈ Icc (0 : ℝ) 1, (relStep (γ 0) (γ s)).PosDef := fun s hs =>
    (posDef_relStep_iff h0 _).2 (hγ.mem_pd s hs)
  have hcont : ContinuousOn (fun s => eigUp (relStep (γ 0) (γ s)) 0) (Icc 0 1) := by
    intro s hs
    have hNc : Tendsto (fun u => relStep (γ 0) (γ u)) (𝓝[Icc 0 1] s)
        (𝓝 (relStep (γ 0) (γ s))) :=
      ((continuous_relStep (γ 0)).tendsto _).comp (hγ.continuousOn s hs)
    have hsym : ∀ᶠ u in 𝓝[Icc (0 : ℝ) 1] s, (relStep (γ 0) (γ u)).IsSymm := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact isSymm_of_isHermitian (hN u hu).isHermitian
    have := tendsto_eigUp' hsym (isSymm_of_isHermitian (hN s hs).isHermitian) hNc
    exact ((continuous_apply (0 : Fin d)).tendsto _).comp this
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  refine ⟨eigUp (relStep (γ 0) (γ s₀)) 0, eigUp_pos (hN s₀ hs₀) 0, fun s hs i => ?_⟩
  exact (hmin hs).trans (eigUp_monotone (hN s hs).isHermitian (Fin.zero_le i))

/-- **`g(s) = F_w(γ(0), γ(s))` is absolutely continuous** along a causal curve. -/
theorem IsCausalCurve.absolutelyContinuous_coneFunctional [NeZero d] {C : Set (Mat d)}
    {γ : ℝ → Mat d} (hγ : IsCausalCurve C γ) (w : Fin d → ℝ) :
    AbsolutelyContinuousOnInterval (fun s => coneFunctional w (γ 0) (γ s)) 0 1 := by
  obtain ⟨m, hm, hlow⟩ := hγ.exists_eigUp_lower
  have h0 : (γ 0).PosDef := hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩
  set R := (msqrt (γ 0))⁻¹
  set K := (∑ i : Fin d, |sortDown w i| * (m⁻¹ * (2 * (i : ℝ) + 1))) * (‖lin R‖ * ‖lin R‖)
  refine AbsolutelyContinuousOnInterval.of_dominated (fs := fun p : Fin d × Fin d =>
    fun s => γ s p.1 p.2) (K := K) (fun p => hγ.absolutelyContinuous p.1 p.2) fun s hs s' hs' => ?_
  rw [uIcc_of_le zero_le_one] at hs hs'
  rw [coneFunctional_eq w h0 (hγ.mem_pd s hs), coneFunctional_eq w h0 (hγ.mem_pd s' hs'),
    ← Finset.sum_sub_distrib]
  set E := γ s - γ s'
  have hNs := isSymm_of_isHermitian ((posDef_relStep_iff h0 _).2 (hγ.mem_pd s hs)).isHermitian
  have hNs' := isSymm_of_isHermitian ((posDef_relStep_iff h0 _).2 (hγ.mem_pd s' hs')).isHermitian
  have hlinE : ‖lin (relStep (γ 0) (γ s) - relStep (γ 0) (γ s'))‖ ≤
      ‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2| := by
    rw [← relStep_sub, relStep, lin_mul, lin_mul]
    calc ‖lin R * lin E * lin R‖ ≤ ‖lin R‖ * ‖lin E‖ * ‖lin R‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖lin R‖ * (∑ a, ∑ b, |E a b|) * ‖lin R‖ := by
          gcongr
          exact norm_lin_le_sum E
      _ = _ := by
          rw [Fintype.sum_prod_type]
          simp only [E, Matrix.sub_apply]
          ring
  have hterm : ∀ i : Fin d, |sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s)) i) -
      sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s')) i)| ≤
      |sortDown w i| * (m⁻¹ * (2 * (i : ℝ) + 1)) *
        (‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2|) := by
    intro i
    rw [← mul_sub, abs_mul]
    have h1 := abs_log_sub_log_le hm (hlow s hs i) (hlow s' hs' i)
    have h2 := eigUp_lipschitz hNs hNs' i
    have h3 : |Real.log (eigUp (relStep (γ 0) (γ s)) i) -
        Real.log (eigUp (relStep (γ 0) (γ s')) i)| ≤ m⁻¹ * (2 * (i : ℝ) + 1) *
          (‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2|) := by
      calc _ ≤ m⁻¹ * |eigUp (relStep (γ 0) (γ s)) i - eigUp (relStep (γ 0) (γ s')) i| := h1
        _ ≤ m⁻¹ * ((2 * (i : ℝ) + 1) * ‖lin (relStep (γ 0) (γ s) - relStep (γ 0) (γ s'))‖) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hm.le)
        _ ≤ m⁻¹ * ((2 * (i : ℝ) + 1) *
            (‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2|)) := by
            gcongr
        _ = _ := by ring
    calc |sortDown w i| * |Real.log (eigUp (relStep (γ 0) (γ s)) i) -
          Real.log (eigUp (relStep (γ 0) (γ s')) i)|
        ≤ |sortDown w i| * (m⁻¹ * (2 * (i : ℝ) + 1) *
          (‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2|)) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = _ := by ring
  calc |∑ i, (sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s)) i) -
        sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s')) i))|
      ≤ ∑ i, |sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s)) i) -
        sortDown w i * Real.log (eigUp (relStep (γ 0) (γ s')) i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, |sortDown w i| * (m⁻¹ * (2 * (i : ℝ) + 1)) *
        (‖lin R‖ * ‖lin R‖ * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2|) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = K * ∑ p : Fin d × Fin d, |γ s p.1 p.2 - γ s' p.1 p.2| := by
        rw [← Finset.sum_mul]
        ring

/-- **Causal curves end in the order**: along a `C`-causal curve, `F_w(γ(0), γ(1)) ≥ 0` for every
`w` with `∑ᵢ w↓ᵢ λ↑ᵢ(Y) ≥ 0` on `C`. Through the superadditivity, it spends ledger A9. -/
theorem IsCausalCurve.coneFunctional_nonneg (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    {γ : ℝ → Mat d} (hγ : IsCausalCurve C γ) (w : Fin d → ℝ)
    (hw : ∀ Y ∈ C, 0 ≤ ∑ i, sortDown w i * eigUp Y i) :
    0 ≤ coneFunctional w (γ 0) (γ 1) := by
  haveI : NeZero d := ⟨by omega⟩
  set g : ℝ → ℝ := fun s => coneFunctional w (γ 0) (γ s)
  have h0 : (γ 0).PosDef := hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩
  have hac := hγ.absolutelyContinuous_coneFunctional w
  have hint := hac.integral_deriv_eq_sub
  have hg0 : g 0 = 0 := coneFunctional_self w h0
  have hdiffs : ∀ᵐ s : ℝ, ∀ p : Fin d × Fin d, s ∈ uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun u => γ u p.1 p.2) s :=
    ae_all_iff.2 fun p => (hγ.absolutelyContinuous p.1 p.2).ae_differentiableAt
  have hcaus : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → relStep (γ s) (mderiv γ s) ∈ C :=
    (ae_restrict_iff' measurableSet_Icc).1 hγ.causal
  have hne0 : ∀ᵐ s : ℝ, s ≠ 0 := compl_mem_ae_iff.2 (Real.volume_singleton)
  have hne1 : ∀ᵐ s : ℝ, s ≠ 1 := compl_mem_ae_iff.2 (Real.volume_singleton)
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..1, deriv g s := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hdiffs, hcaus, hne0, hne1] with s hs1 hs2 hs3 hs4 hsI
    simp only [Pi.zero_apply]
    by_cases hgd : DifferentiableAt ℝ g s
    · have hsIoo : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs3),
        lt_of_le_of_ne hsI.2 hs4⟩
      have hs : (γ s).PosDef := hγ.mem_pd s hsI
      have hY := hs2 hsI
      have hder : ∀ a b, HasDerivAt (fun u => γ u a b) (mderiv γ s a b) s := fun a b =>
        (hs1 (a, b) (by rw [uIcc_of_le zero_le_one]; exact hsI)).hasDerivAt
      have hpd : ∀ᶠ h in 𝓝[>] (0 : ℝ), (γ (s + h)).PosDef := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - s by linarith [hsIoo.2])] with h hh
        exact hγ.mem_pd _ ⟨by linarith [hh.1, hsIoo.1], by linarith [hh.2]⟩
      have hq := tendsto_coneFunctional_slope w hder hpd hs (hCsym hY)
      have hslope := hgd.hasDerivAt.tendsto_slope_zero_right
      have hle : ∀ᶠ h in 𝓝[>] (0 : ℝ), h⁻¹ * coneFunctional w (γ s) (γ (s + h)) ≤
          h⁻¹ • (g (s + h) - g s) := by
        filter_upwards [hpd, self_mem_nhdsWithin] with h hh hpos
        have hpos : (0 : ℝ) < h := hpos
        have := coneFunctional_superadditive hd w h0 hs hh
        rw [smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (by simp only [g]; linarith) (inv_nonneg.2 hpos.le)
      exact (hw _ hY).trans (le_of_tendsto_of_tendsto hq hslope hle)
    · rw [deriv_zero_of_not_differentiableAt hgd]
  have : g 1 - g 0 ≥ 0 := by rw [← hint]; exact hnonneg
  simp only [g] at this hg0
  linarith

/-- **`thm:cone-orders`(1), causal curves end in the order**: the relative step of the ends of a
`C`-causal curve lies in `exp C`. Spends ledger A9 through the superadditivity of `F_w`. -/
theorem IsCausalCurve.relStep_mem_expSet (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) {γ : ℝ → Mat d}
    (hγ : IsCausalCurve C γ) : relStep (γ 0) (γ 1) ∈ expSet C := by
  obtain ⟨hDsym, hDc, hCD, -, -⟩ := orthInvariant_cone_eq_specCone hd hCsym hC hO
  have h0 : (γ 0).PosDef := hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩
  have h1 : (γ 1).PosDef := hγ.mem_pd 1 ⟨zero_le_one, le_rfl⟩
  have hD := (orthInvariant_cone_eq_specCone hd hCsym hC hO).2.2.1
  rw [hCD, expSet_specCone_eq]
  refine ⟨(posDef_relStep_iff h0 _).2 h1, (symCone_mem_iff hd hDsym hDc _).2 fun w hw => ?_⟩
  refine hγ.coneFunctional_nonneg hd hCsym w fun Y hY => ?_
  have hYD := hY
  rw [hCD] at hYD
  have := (symCone_mem_iff hd hDsym hDc _).1 hYD.2 w hw
  rwa [sortUp_of_monotone (eigUp_monotone (isHermitian_of_isSymm hYD.1))] at this

/-! ## `thm:cone-orders`: the cone field and clause (1) -/

/-- **`thm:cone-orders`**, the cone field: `Σ^{1/2}CΣ^{1/2}` equals `ACAᵀ` for every `A` with
`AAᵀ = Σ`, so that `B(Σ^{1/2}CΣ^{1/2})Bᵀ` is the cone at `BΣBᵀ` for `B ∈ GL(d)`. -/
theorem coneField_eq (_hd : 1 ≤ d) {C : Set (Mat d)} (_hCsym : C ⊆ symSet d)
    (_hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) {S : Mat d} (hS : S.PosDef) :
    (∀ A : Mat d, A * Aᵀ = S →
        (fun X => msqrt S * X * msqrt S) '' C = (fun X => A * X * Aᵀ) '' C) ∧
      ∀ B ∈ glSet d, (fun Y => B * Y * Bᵀ) '' ((fun X => msqrt S * X * msqrt S) '' C) =
        (fun X => msqrt (act B S) * X * msqrt (act B S)) '' C := by
  have hfield : ∀ {T : Mat d}, T.PosDef → ∀ A : Mat d, A * Aᵀ = T →
      (fun X => msqrt T * X * msqrt T) '' C = (fun X => A * X * Aᵀ) '' C := by
    intro T hT A hAT
    have hQ := msqrt_inv_mul_mem_orthSet hT hAT
    set Q := (msqrt T)⁻¹ * A with hQdef
    have hA : A = msqrt T * Q := by
      rw [hQdef, ← Matrix.mul_assoc, msqrt_mul_inv hT, Matrix.one_mul]
    have hconj : ∀ X, A * X * Aᵀ = msqrt T * (Q * X * Qᵀ) * msqrt T := fun X => by
      rw [hA, transpose_mul, msqrt_transpose]
      simp only [Matrix.mul_assoc]
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨Qᵀ * X * Q, ?_, ?_⟩
      · have := hO Qᵀ (transpose_mem_orthSet hQ) X hX
        rwa [transpose_transpose] at this
      · simp only
        rw [hconj, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, orth_mul_transpose hQ,
          Matrix.one_mul, Matrix.mul_assoc X, orth_mul_transpose hQ, Matrix.mul_one]
    · rintro ⟨X, hX, rfl⟩
      exact ⟨Q * X * Qᵀ, hO Q hQ X hX, (hconj X).symm⟩
  refine ⟨hfield hS, fun B hB => ?_⟩
  have hBS : (act B S).PosDef := (posDef_act_iff hB S).2 hS
  rw [Set.image_image, hfield hBS (B * msqrt S) (mul_msqrt_mul_transpose hS.posSemidef B)]
  congr 1
  funext X
  rw [transpose_mul, msqrt_transpose]
  simp only [Matrix.mul_assoc]

/-- **`thm:cone-orders`(1)**: `Σ ≼_C Σ'` if and only if the relative step lies in `exp C`, and
then `γ(t) = Σ^{1/2}M^tΣ^{1/2}` is `C`-causal. -/
theorem causalLE_iff_expSet (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) {S S' : Mat d} (hS : S.PosDef)
    (hS' : S'.PosDef) :
    (causalLE C S S' ↔ relStep S S' ∈ expSet C) ∧
      (relStep S S' ∈ expSet C → IsCausalCurve C (stepGeodesic S S') ∧
        stepGeodesic S S' 0 = S ∧ stepGeodesic S S' 1 = S') := by
  refine ⟨⟨fun ⟨γ, hγ, h0, h1⟩ => ?_, fun h => ?_⟩, stepGeodesic_causal hCsym hO hS hS'⟩
  · have := hγ.relStep_mem_expSet hd hCsym hC hO
    rwa [h0, h1] at this
  · obtain ⟨hc, h0, h1⟩ := stepGeodesic_causal hCsym hO hS hS' h
    exact ⟨_, hc, h0, h1⟩

/-- `exp C` for an invariant closed convex cone `C ⊆ Sym(d)`: a step set, closed in `PD(d)`, closed
under `M^{1/2}NM^{1/2}`. -/
theorem expSet_props (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) :
    IsStepSet (expSet C) ∧ closure (expSet C) ∩ pdSet d ⊆ expSet C ∧
      ∀ M ∈ expSet C, ∀ N ∈ expSet C, msqrt M * N * msqrt M ∈ expSet C := by
  obtain ⟨hDsym, hDc, hCD, -, -⟩ := orthInvariant_cone_eq_specCone hd hCsym hC hO
  obtain ⟨-, h1, h2, h3⟩ := expSet_specCone hd hDsym hDc
  rw [hCD]
  exact ⟨h1, h2, h3⟩

/-- **`thm:cone-orders`(1)**: `≼_C` is `≤_{exp C}`, a closed `GL(d)`-invariant preorder on `PD(d)`,
a partial order if and only if `C ∩ (-C) = {0}`; and `C(exp C) = C`. -/
theorem causalLE_order (hd : 1 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) :
    (∀ S S' : Mat d, S.PosDef → S'.PosDef → (causalLE C S S' ↔ stepLE (expSet C) S S')) ∧
      closure {p : Mat d × Mat d | stepLE (expSet C) p.1 p.2} ∩ (pdSet d ×ˢ pdSet d) ⊆
        {p : Mat d × Mat d | stepLE (expSet C) p.1 p.2} ∧
      (∀ B ∈ glSet d, ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        (stepLE (expSet C) S S' ↔ stepLE (expSet C) (act B S) (act B S'))) ∧
      (∀ S : Mat d, S.PosDef → stepLE (expSet C) S S) ∧
      (∀ S S' S'' : Mat d, S.PosDef → S'.PosDef → S''.PosDef →
        stepLE (expSet C) S S' → stepLE (expSet C) S' S'' → stepLE (expSet C) S S'') ∧
      ((∀ S S' : Mat d, S.PosDef → S'.PosDef →
          stepLE (expSet C) S S' → stepLE (expSet C) S' S → S = S') ↔
        ∀ X ∈ C, -X ∈ C → X = 0) ∧
      infCone (expSet C) = C := by
  obtain ⟨hK, hKc, hKp⟩ := expSet_props hd hCsym hC hO
  have hprops := stepLE_order_props hd hK
  have h1 : (1 : Mat d) ∈ expSet C := ⟨0, hC.2.2.1, mexp_zero.symm⟩
  refine ⟨fun S S' hS hS' => ?_, hprops.2.2.2 hKc, fun B hB S S' hS hS' =>
    stepLE_invariant hd hK hS hS' B hB, hprops.1.2 h1, ?_, ?_, ?_⟩
  · rw [(causalLE_iff_expSet hd hCsym hC hO hS hS').1]
    exact ⟨fun h => ⟨hS, hS', h⟩, fun h => h.2.2⟩
  · exact ((stepLE_trans_tfae hd hK).out 1 0).1 hKp
  · rw [hprops.2.1]
    constructor
    · intro h X hX hnX
      have hXs : X.IsSymm := hCsym hX
      have hinv : (mexp X)⁻¹ = mexp (-X) := by
        unfold mexp
        rw [Matrix.exp_neg]
      have := h (mexp X) ⟨X, hX, rfl⟩ (by rw [hinv]; exact ⟨-X, hnX, rfl⟩)
      exact eq_zero_of_mexp_eq_one hXs this
    · rintro h M ⟨X, hX, rfl⟩ ⟨Y, hY, hYX⟩
      have hXs : X.IsSymm := hCsym hX
      have hYs : Y.IsSymm := hCsym hY
      have hinv : (mexp X)⁻¹ = mexp (-X) := by
        unfold mexp
        rw [Matrix.exp_neg]
      rw [hinv] at hYX
      have hYX' : Y = -X := (mexp_injOn (isHermitian_of_isSymm hYs)
        (isHermitian_of_isSymm hXs.neg) hYX.symm)
      rw [h X hX (hYX' ▸ hY), mexp_zero]
  · ext X
    constructor
    · rintro ⟨hXs, hX⟩
      obtain ⟨Y, hY, hYX⟩ := hX 1 zero_le_one
      rw [one_smul] at hYX
      rwa [mexp_injOn (isHermitian_of_isSymm hXs) (isHermitian_of_isSymm (hCsym hY)) hYX]
    · intro hX
      exact ⟨hCsym hX, fun t ht => ⟨t • X, hC.2.2.2 t ht X hX, rfl⟩⟩

end AffineHemigroup
