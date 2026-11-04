/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityLine

/-!
# `prop:similarity-degenerate-family`: without a nondegenerate rank-one limit the shape is unbounded

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-degenerate-family`.
Wave 2, group I (Q-0281).

(1) The gauge `h(Σ) = (det Σ)^γ Σ^p`, `p = 1 - dγ`, is continuous on `PSD(d)`, similarity
equivariant and orders the stable densities; `N(0, 2bΣ) * S_α(h(Σ))` has infinitely divisible
increments forming a family with (K1)–(K4), (K3) for similarities (`degenerate_cascade`, A3(iii)).
(2) `ecc(h(Σ)) = ecc(Σ)^p`, the exponent and rotational spreads, the moment bound with `G₀`, `G₁`, and
`L_* = 0` (`degenerate_unbounded`, Lean core). (3) With the isotropic part `S'_β(tr(Σ)I)`, `β < α`:
the cascade, `L'_* = n'_I dx`, nonzero and rotation invariant, `θ_s > 0`, and the two unbounded
functionals (`degenerate_rotation_invariant_limit`, A3(iii)).

## Routes

* **The Loewner–Heinz inequality** (`quad_mrpow_mono`) from the integral representation
  `κ_p⟨x, Σ^p x⟩ = ∫_0^∞ s^{p-1}(|x|² - s⟨x, (Σ+s)⁻¹x⟩) ds` (`ofReal_rpowConst_mul_quad_mrpow`), proved
  in the spectral form, with inversion reversing the order by the variational form of `⟨x, A⁻¹x⟩`
  (`quad_inv_antitone`). Mathlib's `CFC.rpow_le_rpow` is stated for complex C⋆-algebras and does not
  apply to real matrices.
* **The continuity of `Σ ↦ Σ^p` on `PSD(d)`** (`continuousOn_mrpow`) from the same representation by
  dominated convergence, and polarization; Mathlib's `continuousOn_cfc` needs an isometric functional
  calculus that real matrices lack here.
* **The moments of the stable measure** (`ofReal_quad_moment_stable_le`, `_ge`) by `x = H^{1/2}y`
  (`lintegral_stableLevy`), a reflection, the dilation `lintegral_min_dilate`, and the directional
  average `lintegral_radial_mul_inner_sq` (the second moments of `σ̄`, from `SimilarityLine`).
* **`L_* = 0`** by dominated convergence with `n_{h(Σ_ε)} ≤ n_I` and the explicit
  `Σ_ε^p = Σ_{ε^p}`.
* **`θ_s > 0`**: the moment matrices along `Σ_ε` decrease, so their limit exists
  (`tendsto_momentMatrix_of_mono`), and it dominates `𝓜_s(n'_I) = (T_s(n'_I)/d) I`.
* **The cascades** through `simCascade_of_exponent` (from `SimilarityLine`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## Inversion reverses the Loewner order -/

/-- **The variational form of `⟨x, A⁻¹x⟩`**: `2⟨x,y⟩ - ⟨y,Ay⟩ ≤ ⟨x,A⁻¹x⟩`, with equality at
`y = A⁻¹x`. Mathlib types only. -/
theorem quad_inv_variational {A : Mat d} (hA : A.PosDef) (x y : Rd d) :
    2 * ⟪x, y⟫ - quad A y ≤ quad A⁻¹ x ∧ 2 * ⟪x, lin A⁻¹ x⟫ - quad A (lin A⁻¹ x) = quad A⁻¹ x := by
  set z := lin A⁻¹ x with hz
  have hAz : lin A z = x := lin_mul_inv_apply (isUnit_iff_ne_zero.2 hA.det_pos.ne') x
  have hqz : quad A z = quad A⁻¹ x := by
    rw [quad, hAz, quad, ← hz, real_inner_comm]
  refine ⟨?_, ?_⟩
  · have h := quad_nonneg hA.posSemidef (y - z)
    rw [sub_eq_add_neg, quad_add_vec hA.isHermitian, quad_neg_vec, map_neg, inner_neg_right,
      hAz, hqz] at h
    rw [real_inner_comm]
    linarith
  · have hxz : ⟪x, z⟫ = quad A⁻¹ x := rfl
    rw [hqz, hxz]
    ring

/-- **Inversion reverses the Loewner order on `PD(d)`**: `A ≤ B` gives `⟨x,B⁻¹x⟩ ≤ ⟨x,A⁻¹x⟩`. -/
theorem quad_inv_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hle : loewnerLE A B)
    (x : Rd d) : quad B⁻¹ x ≤ quad A⁻¹ x := by
  set y := lin B⁻¹ x
  have h1 := (quad_inv_variational hB x 0).2
  have h2 := (quad_inv_variational hA x y).1
  have h3 : quad A y ≤ quad B y := by
    have := quad_nonneg hle y
    rw [quad_sub] at this
    linarith
  linarith

/-! ## Powers of a positive semidefinite matrix in the spectral form -/

theorem udiag_inv {U : Mat d} (hU : U * Uᵀ = 1) {w : Fin d → ℝ} (hw : ∀ i, w i ≠ 0) :
    (udiag U w)⁻¹ = udiag U (fun i => (w i)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [udiag_mul hU, ← udiag_one hU]
  congr 1
  funext i
  simp [hw i]

theorem udiag_add_smul_one {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (s : ℝ) :
    udiag U w + s • (1 : Mat d) = udiag U (fun i => w i + s) := by
  rw [← udiag_const hU, udiag_add_udiag]
  rfl

/-- The data of the spectral form of `Σ ∈ PSD(d)`: `Σ = U diag(λ) Uᵀ`, `U` orthogonal, `λ ≥ 0`. -/
theorem psd_spectral {S : Mat d} (hS : S.PosSemidef) :
    ∃ U : Mat d, ∃ w : Fin d → ℝ, U * Uᵀ = 1 ∧ (∀ i, 0 ≤ w i) ∧ S = udiag U w :=
  ⟨_, _, (spectral_udiag hS.isHermitian).1, hS.eigenvalues_nonneg,
    (spectral_udiag hS.isHermitian).2⟩

theorem quad_udiag {U : Mat d} (w : Fin d → ℝ) (x : Rd d) :
    quad (udiag U w) x = ∑ i, w i * ((lin Uᵀ x) i) ^ 2 :=
  quad_orth_diag U w x

/-! ## The integral representation of `Σ^p`, `0 < p < 1` -/

/-- `κ_p := ∫_0^∞ u^{p-1}/(1+u) du`. -/
noncomputable def rpowConst (p : ℝ) : ℝ :=
  (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) / (1 + u))).toReal

theorem lintegral_rpowConst_ne_top {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) / (1 + u)) ≠ ⊤ := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext r
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro h; by_cases h1 : r < 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_lt.1 h1)
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit, lintegral_union measurableSet_Ici
    (Set.disjoint_left.2 fun x hx hx' => absurd (show (1 : ℝ) ≤ x from hx') (not_le.2 hx.2))]
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by linarith : -1 < p - 1)).lintegral_lt_top.ne ?_
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun u hu => ?_))
    have hu0 : 0 < u := hu.1
    refine ENNReal.ofReal_le_ofReal (div_le_self (Real.rpow_nonneg hu0.le _) (by linarith))
  · rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
    refine ne_top_of_le_ne_top (integrableOn_Ioi_rpow_of_lt (by linarith : p - 2 < -1)
      zero_lt_one).lintegral_lt_top.ne ?_
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_))
    have hu0 : (0 : ℝ) < u := zero_lt_one.trans hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub_one hu0.ne' (p - 1)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hu0.le _) hu0 (by linarith)

theorem rpowConst_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < rpowConst p := by
  refine ENNReal.toReal_pos ?_ (lintegral_rpowConst_ne_top hp0 hp1)
  refine ne_of_gt (lt_of_lt_of_le ?_ (lintegral_mono_set (show Ioo (1 : ℝ) 2 ⊆ Ioi 0 from
    fun u hu => (show (0 : ℝ) < u by linarith [hu.1]))))
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (2 ^ (p - 1) / 3) * volume (Ioo (1 : ℝ) 2) := by
        rw [Real.volume_Ioo]
        refine ENNReal.mul_pos ?_ (by norm_num)
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
    _ = ∫⁻ _u in Ioo (1 : ℝ) 2, ENNReal.ofReal (2 ^ (p - 1) / 3) := (setLIntegral_const _ _).symm
    _ ≤ _ := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun u hu => ?_))
        have hu0 : (0 : ℝ) < u := by linarith [hu.1]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (2 : ℝ) ^ (p - 1) ≤ u ^ (p - 1) :=
          Real.rpow_le_rpow_of_nonpos hu0 hu.2.le (by linarith)
        exact div_le_div₀ (Real.rpow_nonneg hu0.le _) h1 (by linarith) (by linarith [hu.2])

/-- `∫_0^∞ s^{p-1} λ/(λ+s) ds = κ_p λ^p` for `λ ≥ 0`, by `s = λu`. -/
theorem lintegral_resolvent_scalar {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {l : ℝ} (hl : 0 ≤ l) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * (l / (l + s))) =
      ENNReal.ofReal (rpowConst p * l ^ p) := by
  rcases hl.eq_or_lt with rfl | hl0
  · simp [Real.zero_rpow hp0.ne']
  set K := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) / (1 + u)) with hK
  set H : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (p - 1) * (l / (l + s))) with hHdef
  -- the substitution `s = l r` (the shared library's `setLIntegral_Ioi_comp_mul`)
  have hint := ScaleSpace.setLIntegral_Ioi_comp_mul hl0 H
  have hH : ∀ r ∈ Ioi (0 : ℝ), H (l * r) =
      ENNReal.ofReal (l ^ (p - 1)) * ENNReal.ofReal (r ^ (p - 1) / (1 + r)) := by
    intro r hr
    have hr0 : 0 < r := hr
    simp only [hHdef]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl0.le _), Real.mul_rpow hl0.le hr0.le,
      show l / (l + l * r) = 1 / (1 + r) by field_simp]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioi hH, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← hK] at hint
  have hKfin : K ≠ ⊤ := lintegral_rpowConst_ne_top hp0 hp1
  rw [hint, ← mul_assoc, ← ENNReal.ofReal_mul hl0.le, show rpowConst p = K.toReal from rfl,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKfin, mul_comm K]
  congr 2
  rw [Real.rpow_sub_one hl0.ne', mul_div_cancel₀ _ hl0.ne']

/-- **The integral representation of `Σ^p`**, `0 < p < 1`, `Σ ∈ PSD(d)`:
`κ_p ⟨x, Σ^p x⟩ = ∫_0^∞ s^{p-1}(|x|² - s⟨x,(Σ + s)^{-1}x⟩) ds`. -/
theorem ofReal_rpowConst_mul_quad_mrpow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {S : Mat d}
    (hS : S.PosSemidef) (x : Rd d) :
    ENNReal.ofReal (rpowConst p * quad (mrpow S p) x) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (p - 1) * (‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x)) := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
  set c : Fin d → ℝ := fun i => (lin Uᵀ x) i with hc
  have hsum : ∑ i, c i ^ 2 = ‖x‖ ^ 2 := sum_sq_lin_transpose hU x
  rw [mrpow_udiag hU hw, quad_udiag]
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (p - 1) * (‖x‖ ^ 2 - s * quad (udiag U w + s • (1 : Mat d))⁻¹ x)) =
        ∑ i, ENNReal.ofReal (c i ^ 2) * ENNReal.ofReal (s ^ (p - 1) * (w i / (w i + s))) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hne : ∀ i, w i + s ≠ 0 := fun i => (add_pos_of_nonneg_of_pos (hw i) hs0).ne'
    rw [udiag_add_smul_one hU, udiag_inv hU hne, quad_udiag, ← hsum]
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hs0.le _) (div_nonneg (hw i) (by linarith [hw i]))))]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hne i
    field_simp
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_finsetSum _ (fun i _ => by
    fun_prop)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (rpowConst_pos hp0 hp1).le
    (mul_nonneg (Real.rpow_nonneg (hw i) _) (sq_nonneg _)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_resolvent_scalar hp0 hp1 (hw i), ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  ring

/-- **The Loewner–Heinz inequality**, `0 < p < 1`: `Σ ≤ Σ'` in `PSD(d)` gives `Σ^p ≤ Σ'^p`, in
quadratic forms. -/
theorem quad_mrpow_mono {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {S S' : Mat d} (hS : S.PosSemidef)
    (hle : loewnerLE S S') (x : Rd d) : quad (mrpow S p) x ≤ quad (mrpow S' p) x := by
  have hS' : S'.PosSemidef := by
    have := hS.add hle
    rwa [add_sub_cancel] at this
  have hκ := rpowConst_pos hp0 hp1
  have h := ofReal_rpowConst_mul_quad_mrpow hp0 hp1 hS x
  have h' := ofReal_rpowConst_mul_quad_mrpow hp0 hp1 hS' x
  have hle' : ENNReal.ofReal (rpowConst p * quad (mrpow S p) x) ≤
      ENNReal.ofReal (rpowConst p * quad (mrpow S' p) x) := by
    rw [h, h']
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))
    have hs0 : 0 < s := hs
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le _))
    have hA : (S + s • (1 : Mat d)).PosDef := by
      rw [add_comm]; exact (PosDef.one.smul hs0).add_posSemidef hS
    have hB : (S' + s • (1 : Mat d)).PosDef := by
      rw [add_comm]; exact (PosDef.one.smul hs0).add_posSemidef hS'
    have hAB : loewnerLE (S + s • (1 : Mat d)) (S' + s • (1 : Mat d)) := by
      unfold loewnerLE
      rw [add_sub_add_right_eq_sub]
      exact hle
    have := quad_inv_antitone hA hB hAB x
    nlinarith
  have hpsd : (mrpow S' p).PosSemidef := by
    obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS'
    rw [mrpow_udiag hU hw]
    exact (udiag_posSemidef_iff hU _).2 fun i => Real.rpow_nonneg (hw i) _
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hκ.le (quad_nonneg hpsd x))).1 hle'
  exact le_of_mul_le_mul_left this hκ

/-- The resolvent term in the spectral form: `0 ≤ |x|² - s⟨x,(Σ+s)^{-1}x⟩ ≤ |x|² min(1, tr Σ/s)`. -/
theorem resolvent_term_bounds {S : Mat d} (hS : S.PosSemidef) (x : Rd d) {s : ℝ} (hs : 0 < s) :
    0 ≤ ‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x ∧
      ‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x ≤ ‖x‖ ^ 2 ∧
      ‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x ≤ ‖x‖ ^ 2 * S.trace / s := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
  have hsum : ∑ i, ((lin Uᵀ x) i) ^ 2 = ‖x‖ ^ 2 := sum_sq_lin_transpose hU x
  have hne : ∀ i, w i + s ≠ 0 := fun i => (add_pos_of_nonneg_of_pos (hw i) hs).ne'
  rw [udiag_add_smul_one hU, udiag_inv hU hne, quad_udiag, trace_udiag hU]
  have heq : ‖x‖ ^ 2 - s * ∑ i, (w i + s)⁻¹ * ((lin Uᵀ x) i) ^ 2 =
      ∑ i, w i / (w i + s) * ((lin Uᵀ x) i) ^ 2 := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hne i
    field_simp
    ring
  rw [heq]
  have hw' : ∀ i, w i ≤ ∑ j, w j := fun i =>
    Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ i)
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (hw i) (by linarith [hw i]))
    (sq_nonneg _), ?_, ?_⟩
  · rw [← hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    rw [div_le_one (by linarith [hw i])]
    linarith
  · rw [← hsum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm (w i / (w i + s)), mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc w i / (w i + s) ≤ w i / s := div_le_div_of_nonneg_left (hw i) hs (by linarith [hw i])
      _ ≤ (∑ j, w j) / s := div_le_div_of_nonneg_right (hw' i) hs.le

theorem continuousAt_quad_inv {A₀ : Mat d} (hA : A₀.PosDef) (x : Rd d) :
    ContinuousAt (fun A : Mat d => quad A⁻¹ x) A₀ :=
  (continuous_quad x).continuousAt.comp
    (continuousAt_inv_of_isUnit (isUnit_iff_ne_zero.2 hA.det_pos.ne'))

theorem continuousOn_resolvent_quad {S : Mat d} (hS : S.PosSemidef) (x : Rd d) :
    ContinuousOn (fun s : ℝ => quad (S + s • (1 : Mat d))⁻¹ x) (Ioi 0) := by
  intro s hs
  have hs0 : 0 < s := hs
  have hA : (S + s • (1 : Mat d)).PosDef := by
    rw [add_comm]; exact (PosDef.one.smul hs0).add_posSemidef hS
  exact (ContinuousAt.comp (f := fun t : ℝ => S + t • (1 : Mat d)) (continuousAt_quad_inv hA x)
    (by fun_prop)).continuousWithinAt

/-- **`Σ ↦ ⟨x, Σ^p x⟩` is continuous on `PSD(d)`**, `0 < p < 1`: dominated convergence in the
integral representation. -/
theorem continuousOn_quad_mrpow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : Rd d) :
    ContinuousOn (fun S : Mat d => quad (mrpow S p) x) (psdSet d) := by
  have hκ := rpowConst_pos hp0 hp1
  set F : Mat d → ℝ → ℝ := fun S s =>
    s ^ (p - 1) * (‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x) with hF
  have hFm : ∀ S : Mat d, S.PosSemidef → AEStronglyMeasurable (F S) (volume.restrict (Ioi 0)) := by
    intro S hS
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt hs)).mul
      (continuousOn_const.sub (continuousOn_id.mul (continuousOn_resolvent_quad hS x))))
  have hF0 : ∀ S : Mat d, S.PosSemidef → ∀ s : ℝ, 0 < s → 0 ≤ F S s := fun S hS s hs =>
    mul_nonneg (Real.rpow_nonneg hs.le _) (resolvent_term_bounds hS x hs).1
  have heq : ∀ S : Mat d, S.PosSemidef →
      quad (mrpow S p) x = (rpowConst p)⁻¹ * ∫ s in Ioi (0 : ℝ), F S s := by
    intro S hS
    have h := ofReal_rpowConst_mul_quad_mrpow hp0 hp1 hS x
    have hq : 0 ≤ quad (mrpow S p) x := by
      obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
      rw [mrpow_udiag hU hw, quad_udiag]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (sq_nonneg _)
    have hint : ∫ s in Ioi (0 : ℝ), F S s =
        (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (F S s)).toReal :=
      integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioi).2
        (ae_of_all _ fun s hs => hF0 S hS s hs)) (hFm S hS)
    have h2 : rpowConst p * quad (mrpow S p) x = ∫ s in Ioi (0 : ℝ), F S s := by
      rw [hint]
      exact (ENNReal.toReal_ofReal (mul_nonneg hκ.le hq)).symm.trans (congrArg ENNReal.toReal h)
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
  intro S₀ hS₀
  set T := S₀.trace + 1 with hT
  have hev : ∀ᶠ S in 𝓝[psdSet d] S₀, S.PosSemidef ∧ S.trace < T := by
    refine eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds ?_)
    have htc : Continuous fun S : Mat d => S.trace := continuous_id.matrix_trace
    exact htc.continuousAt.eventually (gt_mem_nhds (by rw [hT]; linarith : S₀.trace < T))
  have hT0 : 0 < T := by rw [hT]; linarith [hS₀.trace_nonneg]
  set bound : ℝ → ℝ := fun s => ‖x‖ ^ 2 * ((Ioc 0 T).indicator (fun s => s ^ (p - 1)) s +
    (Ioi T).indicator (fun s => T * s ^ (p - 2)) s) with hbound
  have hbint : Integrable bound (volume.restrict (Ioi 0)) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioc).restrict
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    · exact (IntegrableOn.integrable_indicator (f := fun s => T * s ^ (p - 2))
        ((integrableOn_Ioi_rpow_of_lt (by linarith : p - 2 < -1) hT0).const_mul T)
        measurableSet_Ioi).restrict
  refine ContinuousWithinAt.congr (f := fun S => (rpowConst p)⁻¹ * ∫ s in Ioi (0 : ℝ), F S s) ?_
    (fun S hS => heq S hS) (heq S₀ hS₀)
  refine continuousWithinAt_const.mul ?_
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbint ?_
  · filter_upwards [hev] with S hS
    exact hFm S hS.1
  · filter_upwards [hev] with S hS
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
    have hs0 : 0 < s := hs
    obtain ⟨h0, h1, h2⟩ := resolvent_term_bounds hS.1 x hs0
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 S hS.1 s hs0), hbound]
    simp only [hF]
    by_cases hsT : s ≤ T
    · rw [indicator_of_mem (show s ∈ Ioc 0 T from ⟨hs0, hsT⟩),
        indicator_of_notMem (show s ∉ Ioi T from not_lt.2 hsT), add_zero, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0.le _)
    · push Not at hsT
      rw [indicator_of_notMem (show s ∉ Ioc 0 T from fun h => not_le.2 hsT h.2),
        indicator_of_mem (show s ∈ Ioi T from hsT), zero_add]
      have htr : S.trace ≤ T := hS.2.le
      calc s ^ (p - 1) * (‖x‖ ^ 2 - s * quad (S + s • (1 : Mat d))⁻¹ x)
          ≤ s ^ (p - 1) * (‖x‖ ^ 2 * T / s) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (Real.rpow_nonneg hs0.le _)
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htr (sq_nonneg _)) hs0.le
        _ = ‖x‖ ^ 2 * (T * s ^ (p - 2)) := by
            rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub_one hs0.ne' (p - 1)]
            field_simp
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hA : (S₀ + s • (1 : Mat d)).PosDef := by
      rw [add_comm]; exact (PosDef.one.smul hs0).add_posSemidef hS₀
    have hc : ContinuousAt (fun S : Mat d => quad (S + s • (1 : Mat d))⁻¹ x) S₀ :=
      ContinuousAt.comp (f := fun S : Mat d => S + s • (1 : Mat d)) (continuousAt_quad_inv hA x)
        (by fun_prop)
    exact ((continuousAt_const.mul (continuousAt_const.sub (continuousAt_const.mul hc))).tendsto
      ).mono_left nhdsWithin_le_nhds

/-- **`Σ ↦ Σ^p` is continuous on `PSD(d)`**, entrywise by polarization. -/
theorem continuousOn_mrpow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (fun S : Mat d => mrpow S p) (psdSet d) := by
  have hent : ∀ S : Mat d, S.PosSemidef → ∀ i j : Fin d, mrpow S p i j =
      (quad (mrpow S p) (ebasis i + ebasis j) - quad (mrpow S p) (ebasis i) -
        quad (mrpow S p) (ebasis j)) / 2 := by
    intro S hS i j
    have hH : (mrpow S p).IsHermitian := by
      obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
      rw [mrpow_udiag hU hw]
      exact udiag_isHermitian U _
    rw [quad_add_vec hH, inner_ebasis_lin]
    ring
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  refine ContinuousOn.congr ?_ fun S hS => hent S hS i j
  exact (((continuousOn_quad_mrpow hp0 hp1 _).sub (continuousOn_quad_mrpow hp0 hp1 _)).sub
    (continuousOn_quad_mrpow hp0 hp1 _)).div_const 2

/-! ## The gauge `h(Σ) = (det Σ)^γ Σ^p` -/

theorem mrpow_posSemidef {S : Mat d} (hS : S.PosSemidef) (p : ℝ) : (mrpow S p).PosSemidef := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
  rw [mrpow_udiag hU hw]
  exact (udiag_posSemidef_iff hU _).2 fun i => Real.rpow_nonneg (hw i) _

theorem mrpow_posDef {S : Mat d} (hS : S.PosDef) (p : ℝ) : (mrpow S p).PosDef := by
  obtain ⟨U, w, hU, hw, hSw⟩ := psd_spectral hS.posSemidef
  have hw' : ∀ i, 0 < w i := (udiag_posDef_iff hU w).1 (hSw ▸ hS)
  rw [hSw, mrpow_udiag hU hw]
  exact (udiag_posDef_iff hU _).2 fun i => Real.rpow_pos_of_pos (hw' i) _

theorem det_mrpow {S : Mat d} (hS : S.PosSemidef) (p : ℝ) : (mrpow S p).det = S.det ^ p := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
  rw [mrpow_udiag hU hw, det_udiag hU, det_udiag hU, Real.finsetProd_rpow _ _ fun i _ => hw i]

theorem mrpow_one_mat (p : ℝ) : mrpow (1 : Mat d) p = 1 := by
  have h1 : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
  have := mrpow_udiag h1 (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) p
  rw [udiag_one h1] at this
  rw [this]
  simp only [Real.one_rpow]
  exact udiag_one h1

/-- `(cQΣQᵀ)^p = c^p Q Σ^p Qᵀ` for `c ≥ 0` and `Q` orthogonal. -/
theorem mrpow_smul_conj {S : Mat d} (hS : S.PosSemidef) {c : ℝ} (hc : 0 ≤ c) {Q : Mat d}
    (hQ : Q ∈ orthSet d) (p : ℝ) :
    mrpow (c • (Q * S * Qᵀ)) p = c ^ p • (Q * mrpow S p * Qᵀ) := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hS
  have hQQ : Q * Qᵀ = 1 := orth_mul_transpose hQ
  have hQU : (Q * U) * (Q * U)ᵀ = 1 := by
    rw [transpose_mul, show Q * U * (Uᵀ * Qᵀ) = Q * (U * Uᵀ) * Qᵀ by simp only [Matrix.mul_assoc],
      hU, Matrix.mul_one, hQQ]
  have heq : c • (Q * udiag U w * Qᵀ) = udiag (Q * U) (fun i => c * w i) := by
    simp only [udiag, transpose_mul, Matrix.mul_assoc]
    rw [show diagonal (fun i => c * w i) = c • diagonal w by
      ext i j; by_cases hij : i = j <;> simp [hij, Matrix.diagonal]]
    simp
  have heq' : Q * udiag U (fun i => w i ^ p) * Qᵀ = udiag (Q * U) (fun i => w i ^ p) := by
    simp only [udiag, transpose_mul, Matrix.mul_assoc]
  rw [heq, mrpow_udiag hQU (fun i => mul_nonneg hc (hw i)), mrpow_udiag hU hw, heq']
  simp_rw [Real.mul_rpow hc (hw _)]
  simp only [udiag]
  rw [show diagonal (fun i => c ^ p * w i ^ p) = c ^ p • diagonal (fun i => w i ^ p) by
    ext i j; by_cases hij : i = j <;> simp [hij, Matrix.diagonal]]
  simp

theorem det_smul_conj {S : Mat d} (c : ℝ) {Q : Mat d} (hQ : Q ∈ orthSet d) :
    (c • (Q * S * Qᵀ)).det = c ^ d * S.det := by
  have hQQ : Q * Qᵀ = 1 := orth_mul_transpose hQ
  have hdQ : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQQ
    rwa [det_mul, det_transpose, det_one] at this
  rw [det_smul, Fintype.card_fin, det_mul, det_mul, det_transpose]
  have : Q.det * S.det * Q.det = S.det := by
    calc Q.det * S.det * Q.det = (Q.det * Q.det) * S.det := by ring
      _ = S.det := by rw [hdQ, one_mul]
  rw [this]

section Gauge

variable {γ p : ℝ}

theorem degGauge_posSemidef {S : Mat d} (hS : S.PosSemidef) :
    (degGauge γ p S).PosSemidef :=
  (mrpow_posSemidef hS p).smul (Real.rpow_nonneg hS.det_nonneg _)

theorem degGauge_posDef {S : Mat d} (hS : S.PosDef) : (degGauge γ p S).PosDef :=
  (mrpow_posDef hS p).smul (Real.rpow_pos_of_pos hS.det_pos _)

theorem degGauge_singular (hγ : 0 < γ) {S : Mat d} (hS : S.det = 0) : degGauge γ p S = 0 := by
  rw [degGauge, hS, Real.zero_rpow hγ.ne', zero_smul]

theorem degGauge_one : degGauge γ p (1 : Mat d) = 1 := by
  rw [degGauge, det_one, Real.one_rpow, one_smul, mrpow_one_mat]

theorem degGauge_zero [NeZero d] (hγ : 0 < γ) : degGauge γ p (0 : Mat d) = 0 :=
  degGauge_singular hγ (Matrix.det_zero ⟨0⟩)

/-- `h(cQΣQᵀ) = c Q h(Σ) Qᵀ` when `dγ + p = 1`. -/
theorem degGauge_smul_conj (hdp : (d : ℝ) * γ + p = 1)
    {S : Mat d} (hS : S.PosSemidef) {c : ℝ} (hc : 0 < c) {Q : Mat d} (hQ : Q ∈ orthSet d) :
    degGauge γ p (c • (Q * S * Qᵀ)) = c • (Q * degGauge γ p S * Qᵀ) := by
  rw [degGauge, degGauge, det_smul_conj c hQ, mrpow_smul_conj hS hc.le hQ p,
    Real.mul_rpow (pow_nonneg hc.le _) hS.det_nonneg, smul_smul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  calc c ^ ((d : ℝ) * γ) * S.det ^ γ * c ^ p = c ^ ((d : ℝ) * γ + p) * S.det ^ γ := by
        rw [Real.rpow_add hc]; ring
    _ = c * S.det ^ γ := by rw [hdp, Real.rpow_one]

/-- `det h(Σ) = det Σ` when `dγ + p = 1`. -/
theorem det_degGauge [NeZero d] (hγ : 0 < γ) (hdp : (d : ℝ) * γ + p = 1) {S : Mat d}
    (hS : S.PosSemidef) : (degGauge γ p S).det = S.det := by
  rcases hS.det_nonneg.eq_or_lt with h0 | hpos
  · rw [degGauge_singular hγ h0.symm, Matrix.det_zero ⟨0⟩, ← h0]
  rw [degGauge, det_smul, Fintype.card_fin, det_mrpow hS, ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos, mul_comm γ, hdp, Real.rpow_one]

/-- **The density of `S_α(h(Σ))`**:
`n_{h(Σ)}(x) = c_{d,α}^{-1} (det Σ)^{((d+α)γ - 1)/2} ⟨x, Σ^{-p}x⟩^{-(d+α)/2}`, written with `(Σ^p)⁻¹`. -/
theorem stableDensity_degGauge [NeZero d] {α : ℝ} (hγ : 0 < γ) (hdp : (d : ℝ) * γ + p = 1)
    {S : Mat d} (hS : S.PosDef) (x : Rd d) (hx : x ≠ 0) :
    stableDensity α (degGauge γ p S) x = (stableConst (d := d) α)⁻¹ *
      S.det ^ ((((d : ℝ) + α) * γ - 1) / 2) * quad (mrpow S p)⁻¹ x ^ (-((d : ℝ) + α) / 2) := by
  have hdet := hS.det_pos
  have hP := mrpow_posDef hS p
  have hq : 0 < quad (mrpow S p)⁻¹ x := quad_pos hP.inv hx
  have hinv : (degGauge γ p S)⁻¹ = (S.det ^ γ)⁻¹ • (mrpow S p)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [degGauge, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hdet γ).ne', one_smul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP.det_pos.ne')]
  rw [stableDensity, det_degGauge hγ hdp hS.posSemidef, hinv, quad_smul,
    Real.mul_rpow (inv_nonneg.2 (Real.rpow_nonneg hdet.le _)) hq.le, Real.inv_rpow
      (Real.rpow_nonneg hdet.le _), ← Real.rpow_mul hdet.le, mul_assoc, mul_assoc]
  congr 1
  rw [← Real.rpow_neg hdet.le, ← mul_assoc, ← Real.rpow_add hdet]
  congr 2
  ring

/-- **The densities are ordered**: `n_{h(Σ)} ≤ n_{h(Σ')}` for `Σ ≤ Σ'` in `PD(d)`, when
`dγ + p = 1`, `(d+α)γ ≥ 1` and `0 < p < 1`. -/
theorem stableDensity_degGauge_mono [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hγ : 0 < γ)
    (hp0 : 0 < p) (hp1 : p < 1) (hdp : (d : ℝ) * γ + p = 1) (hγα : 1 ≤ ((d : ℝ) + α) * γ)
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) (hle : loewnerLE S S') (x : Rd d)
    (hx : x ≠ 0) :
    stableDensity α (degGauge γ p S) x ≤ stableDensity α (degGauge γ p S') x := by
  rw [stableDensity_degGauge hγ hdp hS x hx, stableDensity_degGauge hγ hdp hS' x hx]
  have hc : 0 ≤ (stableConst (d := d) α)⁻¹ :=
    inv_nonneg.2 (stableConst_pos_finite (d := d) hα0 hα2).2.le
  have hdet : S.det ≤ S'.det := det_le_det_of_loewnerLE hS.posSemidef hle
  have hLH : loewnerLE (mrpow S p) (mrpow S' p) := by
    unfold loewnerLE
    refine posSemidef_of_quad_nonneg ((mrpow_posSemidef hS'.posSemidef p).isHermitian.sub
      (mrpow_posSemidef hS.posSemidef p).isHermitian) fun y => ?_
    rw [quad_sub]
    linarith [quad_mrpow_mono hp0 hp1 hS.posSemidef hle y]
  have hq := quad_inv_antitone (mrpow_posDef hS p) (mrpow_posDef hS' p) hLH x
  have hq0 : 0 < quad (mrpow S' p)⁻¹ x := quad_pos (mrpow_posDef hS' p).inv hx
  refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hS.det_pos.le hdet
    (by linarith)) hc) (Real.rpow_le_rpow_of_nonpos hq0 hq (by linarith))
    (Real.rpow_nonneg (hq0.le.trans hq) _) (mul_nonneg hc (Real.rpow_nonneg hS'.det_pos.le _))

end Gauge

theorem continuousOn_degGauge {γ p : ℝ} (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (degGauge γ p : Mat d → Mat d) (psdSet d) := by
  have hdet : Continuous fun S : Mat d => S.det := continuous_id.matrix_det
  exact (hdet.continuousOn.rpow_const fun S _ => Or.inr hγ.le).smul (continuousOn_mrpow hp0 hp1)

theorem continuousOn_stableExp_degGauge {α γ p : ℝ} (hα0 : 0 < α) (hγ : 0 < γ) (hp0 : 0 < p)
    (hp1 : p < 1) (ω : Rd d) :
    ContinuousOn (fun S : Mat d => stableExp α (degGauge γ p S) ω) (psdSet d) := by
  unfold stableExp
  exact (((continuous_quad ω).comp_continuousOn (continuousOn_degGauge hγ hp0 hp1)).rpow_const
    fun S _ => Or.inr (by positivity))

/-- **`prop:similarity-degenerate-family`(1)**, a cascade: for `1/(d+α) ≤ γ < 1/d`,
`p := 1 - dγ ∈ (0, α/(d+α)]`, the gauge `h(Σ) := (det Σ)^γ Σ^p` is continuous on `PSD(d)`,
similarity-equivariant, and orders the densities, `n_{h(Σ)} ≤ n_{h(Σ')}` for `Σ ≤ Σ'` in `PD(d)`;
and `μ_Σ := N(0, 2bΣ) * S_α(h(Σ))` has infinitely divisible increments on every Loewner step in
`PSD(d)` forming a family with (K1), (K2), (K4) and (K3) for every similarity. Spends A3(iii). -/
theorem degenerate_cascade [NeZero d] (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (γ : ℝ)
    (hγ1 : 1 / ((d : ℝ) + α) ≤ γ) (hγ2 : γ < 1 / (d : ℝ)) (b : ℝ) (hb : 0 ≤ b)
    (σ : Mat d → Measure (Rd d))
    (hσ : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable α (degGauge γ (1 - d * γ) S) (σ S)) :
    let p : ℝ := 1 - d * γ
    let μ : Mat d → Measure (Rd d) := fun S => multivariateGaussian 0 ((2 * b) • S) ∗ σ S
    (0 < p ∧ p ≤ α / ((d : ℝ) + α)) ∧ ContinuousOn (degGauge γ p) (psdSet d) ∧
      (∀ S : Mat d, S.PosSemidef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
        degGauge γ p (c • (Q * S * Qᵀ)) = c • (Q * degGauge γ p S * Qᵀ)) ∧
      (∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' → ∀ x : Rd d, x ≠ 0 →
        stableDensity α (degGauge γ p S) x ≤ stableDensity α (degGauge γ p S') x) ∧
      ∃ ρ : Mat d → Mat d → Measure (Rd d),
        (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
          IsProbabilityMeasure (ρ S S') ∧ IsInfinitelyDivisible (ρ S S') ∧ μ S' = μ S ∗ ρ S S') ∧
        IsGWCascadeFamily (simSet d) loewnerLE ρ := by
  intro p μ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdα : (0 : ℝ) < d + α := by linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ1
  have hp0 : 0 < p := by
    have : (d : ℝ) * γ < 1 := by rwa [lt_div_iff₀ hd0, mul_comm] at hγ2
    show 0 < 1 - (d : ℝ) * γ
    linarith
  have hpα : p ≤ α / ((d : ℝ) + α) := by
    show 1 - (d : ℝ) * γ ≤ α / ((d : ℝ) + α)
    have h1 : 1 ≤ ((d : ℝ) + α) * γ := by rwa [div_le_iff₀ hdα, mul_comm] at hγ1
    rw [le_div_iff₀ hdα]
    nlinarith
  have hp1 : p < 1 := by
    have : α / ((d : ℝ) + α) < 1 := by rw [div_lt_one hdα]; linarith
    linarith
  have hdp : (d : ℝ) * γ + p = 1 := by show (d : ℝ) * γ + (1 - (d : ℝ) * γ) = 1; ring
  have hγα : 1 ≤ ((d : ℝ) + α) * γ := by rwa [div_le_iff₀ hdα, mul_comm] at hγ1
  have hσ' : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable α (degGauge γ p S) (σ S) := hσ
  refine ⟨⟨hp0, hpα⟩, continuousOn_degGauge hγ0 hp0 hp1,
    fun S hS c hc Q hQ => degGauge_smul_conj hdp hS hc hQ,
    fun S S' hS hS' hle x hx =>
      stableDensity_degGauge_mono hα0 hα2 hγ0 hp0 hp1 hdp hγα hS hS' hle x hx, ?_⟩
  set Φ : Mat d → Rd d → ℝ := fun S ω => b * quad S ω + stableExp α (degGauge γ p S) ω with hΦ
  refine simCascade_of_exponent Φ (fun ω => ?_) ?_ ?_ ?_ μ fun S hS => ?_
  · exact ((continuous_const.mul (continuous_quad ω)).continuousOn).add
      (continuousOn_stableExp_degGauge hα0 hγ0 hp0 hp1 ω)
  · rintro A ⟨c, hc, Q, hQ, rfl⟩ S hS ω
    simp only [hΦ]
    rw [quad_act, act_smul_left, degGauge_smul_conj hdp hS (pow_pos hc 2) hQ, ← act_smul_left,
      stableExp_act]
  · refine ⟨ebasis 0, ?_⟩
    simp only [hΦ, quad_zero, mul_zero, degGauge_zero hγ0, stableExp_zero_mat hα0, add_zero,
      degGauge_one]
    have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
    rw [stableExp, quad_one, he, one_pow, Real.one_rpow]
    have : 0 ≤ b * 1 := by linarith
    linarith
  · intro S S' hS hS' hle
    have hG : ((2 * b) • (S' - S)).PosSemidef := hle.smul (by positivity)
    obtain ⟨τ, hτ, hτid, hτc⟩ : ∃ τ : Measure (Rd d), IsProbabilityMeasure τ ∧
        IsInfinitelyDivisible τ ∧ ∀ ω : Rd d, charFun τ ω = ((Real.exp (-(stableExp α
          (degGauge γ p S') ω - stableExp α (degGauge γ p S) ω)) : ℝ) : ℂ) := by
      by_cases hSpd : S.PosDef
      · have hS'pd : S'.PosDef := by
          have := hSpd.add_posSemidef hle
          rwa [add_sub_cancel] at this
        obtain ⟨ρ, hρ, hρid, -, hρc⟩ := exists_stable_increment hα0 hα2 (degGauge_posDef hSpd)
          (degGauge_posDef hS'pd) fun x hx =>
            stableDensity_degGauge_mono hα0 hα2 hγ0 hp0 hp1 hdp hγα hSpd hS'pd hle x hx
        exact ⟨ρ, hρ, hρid, hρc⟩
      · have hdet0 : S.det = 0 := by
          by_contra h
          exact hSpd (hS.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det S).2
            (isUnit_iff_ne_zero.2 h)))
        rw [degGauge_singular hγ0 hdet0]
        by_cases hS'pd : S'.PosDef
        · obtain ⟨ρ, hρ, hρid, -⟩ := exists_ellipticalStable hα0 hα2 (degGauge_posDef (γ := γ)
            (p := p) hS'pd)
          refine ⟨ρ, hρ.1, hρid, fun ω => ?_⟩
          rw [hρ.2, stableExp_zero_mat hα0, sub_zero]
        · have hdet0' : S'.det = 0 := by
            by_contra h
            exact hS'pd (hS'.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det S').2
              (isUnit_iff_ne_zero.2 h)))
          refine ⟨multivariateGaussian 0 0, inferInstance,
            isInfinitelyDivisible_gaussian PosSemidef.zero, fun ω => ?_⟩
          rw [degGauge_singular hγ0 hdet0', stableExp_zero_mat hα0,
            charFun_multivariateGaussian_zero PosSemidef.zero, quad_zero]
          simp
    refine ⟨multivariateGaussian 0 ((2 * b) • (S' - S)) ∗ τ, inferInstance,
      (isInfinitelyDivisible_gaussian hG).conv hτid, fun ω => ?_⟩
    rw [charFun_conv, charFun_multivariateGaussian_zero hG, hτc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    simp only [hΦ, quad_smul, quad_sub]
    ring
  · haveI := (hσ' S hS).1
    refine ⟨inferInstance, fun ω => ?_⟩
    show charFun (multivariateGaussian 0 ((2 * b) • S) ∗ σ S) ω = _
    rw [charFun_conv, charFun_multivariateGaussian_zero (hS.smul (by positivity)), (hσ' S hS).2,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    simp only [hΦ, quad_smul]
    ring

/-! ## Clause (2): eigenvalues of `Σ^p`, and the moments of the stable \Levy measure -/

theorem lin_udiag_apply (U : Mat d) (w : Fin d → ℝ) (v : Rd d) :
    lin (udiag U w) v = lin U (lin (diagonal w) (lin Uᵀ v)) := by
  rw [udiag, lin_mul_apply, lin_mul_apply]

/-- **A function of `U diag(w) Uᵀ` on an eigenvector**: if `Σv = ηv`, then `f(Σ)v = f(η)v`. -/
theorem lin_udiag_comp_eigvec {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (f : ℝ → ℝ)
    {v : Rd d} {η : ℝ} (hv : lin (udiag U w) v = η • v) :
    lin (udiag U (fun i => f (w i))) v = f η • v := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  set c := lin Uᵀ v with hc
  have hUc : lin U c = v := by
    rw [hc, ← lin_mul_apply, hU, lin_one]; rfl
  have hUT : ∀ y : Rd d, lin Uᵀ (lin U y) = y := fun y => by
    rw [← lin_mul_apply, hU', lin_one]; rfl
  have hcoord : ∀ i, w i * c i = η * c i := by
    intro i
    have h := congrArg (fun y => lin Uᵀ y) hv
    rw [lin_udiag_apply, hUT, map_smul] at h
    have := congrArg (fun y : Rd d => y i) h
    simpa [lin_diagonal_apply] using this
  rw [lin_udiag_apply, ← hc]
  conv_rhs => rw [← hUc, ← map_smul]
  congr 1
  ext i
  rw [lin_diagonal_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hci : c i = 0
  · rw [hci, mul_zero, mul_zero]
  · have : w i = η := mul_right_cancel₀ hci (hcoord i)
    rw [this]

theorem le_lamMax_udiag [NeZero d] {U : Mat d} (hU : U * Uᵀ = 1) (w : Fin d → ℝ) (i : Fin d) :
    w i ≤ lamMax (udiag U w) := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.1 hU
  set e : Rd d := EuclideanSpace.single i 1
  set x : Rd d := lin U e
  have hx : lin Uᵀ x = e := by
    simp only [x, ← mul_apply_eq_comp, ← lin_mul, hU', lin_one]
    rfl
  have hsq : ∀ j, (e j) ^ 2 = if j = i then 1 else 0 := fun j => by
    simp only [e, PiLp.single_apply]
    split_ifs <;> norm_num
  have hn : ‖x‖ = 1 := by
    have h := sum_sq_lin_transpose hU x
    rw [hx] at h
    simp only [hsq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h0 := norm_nonneg x
    nlinarith
  have h := quad_le_lamMax (udiag_isHermitian U w) hn
  rw [quad_udiag, hx] at h
  simpa [hsq] using h

theorem lamMax_udiag_le [NeZero d] {U : Mat d} (hU : U * Uᵀ = 1) {w : Fin d → ℝ} {c : ℝ}
    (hc : ∀ i, w i ≤ c) : lamMax (udiag U w) ≤ c := by
  refine (lamMax_le_iff (udiag_isHermitian U w) c).2 fun x hx => ?_
  have hn := sum_sq_lin_transpose hU x
  rw [hx, one_pow] at hn
  rw [quad_udiag]
  calc ∑ i, w i * ((lin Uᵀ x) i) ^ 2 ≤ ∑ i, c * ((lin Uᵀ x) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hn, mul_one]

/-- `λ_max(Σ^p) = λ_max(Σ)^p` and `λ_min(Σ^p) = λ_min(Σ)^p` for `Σ ∈ PD(d)`, `p > 0`. -/
theorem lamMax_lamMin_mrpow [NeZero d] {S : Mat d} (hS : S.PosDef) {p : ℝ} (hp : 0 < p) :
    lamMax (mrpow S p) = lamMax S ^ p ∧ lamMin (mrpow S p) = lamMin S ^ p := by
  obtain ⟨U, w, hU, hw, hSw⟩ := psd_spectral hS.posSemidef
  have hrp : mrpow S p = udiag U (fun i => w i ^ p) := by rw [hSw, mrpow_udiag hU hw]
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a ^ p ≤ b ^ p := fun a b ha hab =>
    Real.rpow_le_rpow ha hab hp.le
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · rw [hrp]
    exact lamMax_udiag_le hU fun i => hmono _ _ (hw i) (hSw ▸ le_lamMax_udiag hU w i)
  · obtain ⟨v, hv, hSv⟩ := exists_unit_eigvec_eigUp hS.isHermitian (Fin.rev 0)
    rw [← lamMax_eq_eigUp_last hS.isHermitian, hSw] at hSv
    have h := lin_udiag_comp_eigvec hU w (fun t => t ^ p) hSv
    have hq := quad_le_lamMax (mrpow_posSemidef hS.posSemidef p).isHermitian hv
    rw [hrp, quad, h, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at hq
    rw [hrp, hSw]
    simpa using hq
  · obtain ⟨v, hv, hSv⟩ := exists_unit_eigvec_eigUp hS.isHermitian 0
    rw [← lamMin_eq_eigUp_zero hS.isHermitian, hSw] at hSv
    have h := lin_udiag_comp_eigvec hU w (fun t => t ^ p) hSv
    have hq := lamMin_le_inner (mrpow_posSemidef hS.posSemidef p).isHermitian hv
    rw [hrp, h, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at hq
    rw [hrp, hSw]
    simpa using hq
  · rw [hrp]
    refine le_lamMin_udiag hU fun i => hmono _ _ (lamMin_nonneg hS.posSemidef) ?_
    rw [hSw]
    exact lamMin_udiag_le hU w i

theorem ecc_degGauge [NeZero d] {γ p : ℝ} (hp : 0 < p) {S : Mat d} (hS : S.PosDef) :
    ecc (degGauge γ p S) = ecc S ^ p := by
  obtain ⟨h1, h2⟩ := lamMax_lamMin_mrpow hS hp
  rw [degGauge, ecc_smul (Real.rpow_pos_of_pos hS.det_pos γ), ecc, ecc, h1, h2,
    Real.div_rpow (lamMax_pos hS).le (lamMin_pos hS).le]

/-- `msqrt H v = √η v` on an eigenvector. -/
theorem lin_msqrt_eigvec {H : Mat d} (hH : H.PosSemidef) {v : Rd d} {η : ℝ}
    (hv : lin H v = η • v) : lin (msqrt H) v = Real.sqrt η • v := by
  obtain ⟨U, w, hU, hw, rfl⟩ := psd_spectral hH
  rw [msqrt_udiag hU hw]
  exact lin_udiag_comp_eigvec hU w Real.sqrt hv

/-- **Integrals against `n_H(x) dx`**, `H ∈ PD(d)`, by `x = H^{1/2}y`:
`∫ f n_H = c_{d,α}^{-1} ∫ f(H^{1/2}y) |y|^{-d-α} dy` for `f ≥ 0` with `f(0) = 0`. -/
theorem lintegral_stableLevy [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef)
    {f : Rd d → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0) :
    ∫⁻ x, f x ∂(stableLevy α H) = ENNReal.ofReal (stableConst (d := d) α)⁻¹ *
      ∫⁻ y, f (lin (msqrt H) y) * ENNReal.ofReal (‖y‖ ^ (-(d : ℝ) - α)) := by
  have hn := measurable_stableDensity (d := d) α H
  rw [stableLevy, lintegral_withDensity_eq_lintegral_mul _ hn.ennreal_ofReal hf]
  have h1 : ∫⁻ x in ({0}ᶜ : Set (Rd d)), (fun x => ENNReal.ofReal (stableDensity α H x) * f x) x =
      ∫⁻ x, ENNReal.ofReal (stableDensity α H x) * f x := by
    rw [← lintegral_indicator (measurableSet_singleton _).compl]
    refine lintegral_congr fun x => ?_
    by_cases hx : x = 0
    · subst hx; simp [hf0]
    · rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx)]
  rw [show (∫⁻ a in ({0}ᶜ : Set (Rd d)),
      ((fun x => ENNReal.ofReal (stableDensity α H x)) * f) a) =
    ∫⁻ x, ENNReal.ofReal (stableDensity α H x) * f x from h1]
  set A := msqrt H with hA
  have hdA : A.det ≠ 0 := (msqrt_mem_glSet hH).ne_zero
  have hG : Measurable fun x => ENNReal.ofReal (stableDensity α H x) * f x :=
    hn.ennreal_ofReal.mul hf
  have hcov := lintegral_comp_lin hdA hG
  have hdet := abs_det_msqrt hH
  have hdH := hH.det_pos
  have hmain : ∫⁻ x, ENNReal.ofReal (stableDensity α H x) * f x =
      ENNReal.ofReal |A.det| * ∫⁻ y, ENNReal.ofReal (stableDensity α H (lin A y)) * f (lin A y) := by
    rw [hcov, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
      mul_inv_cancel₀ (abs_pos.2 hdA).ne', ENNReal.ofReal_one, one_mul]
  rw [hmain, hdet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  have hc : 0 ≤ (stableConst (d := d) α)⁻¹ :=
    inv_nonneg.2 (stableConst_pos_finite (d := d) hα0 hα2).2.le
  rw [hA, stableDensity_lin_msqrt hH, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hab : H.det ^ ((1 : ℝ) / 2) * ((stableConst (d := d) α)⁻¹ * H.det ^ (-(1 : ℝ) / 2) *
      ‖y‖ ^ (-(d : ℝ) - α)) = (stableConst (d := d) α)⁻¹ * ‖y‖ ^ (-(d : ℝ) - α) := by
    rw [mul_comm ((stableConst (d := d) α)⁻¹), mul_assoc, ← mul_assoc (H.det ^ ((1 : ℝ) / 2)),
      ← Real.rpow_add hdH]
    norm_num
  rw [hab, ENNReal.ofReal_mul hc]
  ring

/-- `ψ_{L}(ω) = ⟨ω, Hω⟩^{α/2}` for `L = n_H(x) dx`, and `L` is a Lévy measure. -/
theorem stableLevy_props [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) :
    IsLevyMeasure (stableLevy α H) ∧ ∀ ω : Rd d, levyExp (stableLevy α H) ω = stableExp α H ω := by
  obtain ⟨hψ, hfin⟩ := stableExp_eq_lintegral hα0 hα2 hH
  have hn := measurable_stableDensity (d := d) α H
  have hwd : ∀ g : Rd d → ℝ, Measurable g → (∀ x, 0 ≤ g x) →
      ∫⁻ x, ENNReal.ofReal (g x) ∂(stableLevy α H) =
        ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (g x * stableDensity α H x) := by
    intro g hg hg0
    rw [stableLevy, lintegral_withDensity_eq_lintegral_mul _ hn.ennreal_ofReal hg.ennreal_ofReal]
    refine setLIntegral_congr_fun (measurableSet_singleton _).compl fun x _ => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hg0 x), mul_comm]
  refine ⟨⟨?_, ?_⟩, fun ω => ?_⟩
  · rw [stableLevy, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_restrict (measurableSet_singleton 0)]
    simp
  · rw [hwd _ (by fun_prop) fun x => by positivity]
    exact hfin
  · have hpsi : 0 ≤ stableExp α H ω := Real.rpow_nonneg (quad_nonneg hH.posSemidef ω) _
    rw [levyExp, levyExpL, hwd _ (by fun_prop) fun x => by linarith [Real.cos_le_one ⟪ω, x⟫],
      ← hψ ω, ENNReal.toReal_ofReal hpsi]

/-! ## The constants `G₀`, `G₁` -/

theorem g1_le_bound [NeZero d] {α : ℝ} (z : Rd d) :
    min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) ≤ 2 * stableConstBound d α ‖z‖ := by
  unfold stableConstBound
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0, indicator_of_notMem (show (0 : ℝ) ∉ Ioc 0 1 from fun h => lt_irrefl _ h.1),
      indicator_of_notMem (show (0 : ℝ) ∉ Ioi 1 from fun h => by norm_num at h)]
    simp
  by_cases h1 : ‖z‖ ≤ 1
  · rw [indicator_of_mem (show ‖z‖ ∈ Ioc 0 1 from ⟨hpos, h1⟩),
      indicator_of_notMem (show ‖z‖ ∉ Ioi 1 from not_lt.2 h1), add_zero,
      min_eq_left (by nlinarith [norm_nonneg z])]
    rw [show (2 : ℝ) - d - α = 2 + (-(d : ℝ) - α) by ring, Real.rpow_add hpos, Real.rpow_two]
    linarith [le_refl (‖z‖ ^ 2 * ‖z‖ ^ (-(d : ℝ) - α))]
  · push Not at h1
    rw [indicator_of_notMem (show ‖z‖ ∉ Ioc 0 1 from fun h => not_le.2 h1 h.2),
      indicator_of_mem (show ‖z‖ ∈ Ioi 1 from h1), zero_add,
      min_eq_right (by nlinarith)]
    have := Real.rpow_nonneg hpos.le (-(d : ℝ) - α)
    nlinarith

theorem degConst_props [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Integrable (fun z : Rd d =>
        min (z ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)) ∧
      0 < degConstG0 (d := d) α ∧
      Integrable (fun z : Rd d => min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)) ∧ 0 < degConstG1 d α := by
  set l : Fin d := ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩ with hl
  have hm1 : Measurable fun z : Rd d => min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) := by fun_prop
  have hm0 : Measurable fun z : Rd d => min (z l ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) := by fun_prop
  have hi1 : Integrable fun z : Rd d => min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) := by
    refine Integrable.mono' ((integrable_stableConstBound (d := d) hα0 hα2).const_mul 2)
      hm1.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact g1_le_bound z
  have hle : ∀ z : Rd d, min (z l ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) ≤
      min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) := fun z =>
    mul_le_mul_of_nonneg_right (min_le_min (sq_apply_le_norm_sq z l) le_rfl) (by positivity)
  have hi0 : Integrable fun z : Rd d => min (z l ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α) := by
    refine Integrable.mono' hi1 hm0.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle z
  have he : ‖(ebasis l : Rd d)‖ = 1 := by simp [ebasis]
  have hball : ∀ z ∈ Metric.ball (ebasis l : Rd d) (1 / 2), 0 < min (z l ^ 2) 1 *
      ‖z‖ ^ (-(d : ℝ) - α) := by
    intro z hz
    have h1 : |z l - 1| < 1 / 2 := by
      have := PiLp.norm_apply_le (z - ebasis l) l
      rw [Metric.mem_ball, dist_eq_norm] at hz
      simp only [PiLp.sub_apply, Real.norm_eq_abs] at this
      have hel : (ebasis l : Rd d) l = 1 := by simp [ebasis]
      rw [hel] at this
      linarith
    have hzl : 1 / 2 < z l := by linarith [abs_lt.1 h1]
    have hz0 : 0 < ‖z‖ := by
      have := PiLp.norm_apply_le z l
      rw [Real.norm_eq_abs] at this
      linarith [abs_nonneg (z l), le_abs_self (z l)]
    positivity
  have hpos : ∀ g : Rd d → ℝ, Integrable g → (∀ z, 0 ≤ g z) →
      (∀ z ∈ Metric.ball (ebasis l : Rd d) (1 / 2), 0 < g z) → 0 < ∫ z, g z := by
    intro g hg hg0 hgb
    refine (integral_pos_iff_support_of_nonneg hg0 hg).2 ?_
    refine lt_of_lt_of_le (Metric.measure_ball_pos volume (ebasis l) (by norm_num : (0 : ℝ) < 1 / 2))
      (measure_mono fun z hz => ?_)
    exact (hgb z hz).ne'
  refine ⟨hi0, hpos _ hi0 (fun z => by positivity) hball, hi1,
    hpos _ hi1 (fun z => by positivity) fun z hz => lt_of_lt_of_le (hball z hz) (hle z)⟩

/-- **Dilation**: `∫ F = t^d ∫ F(tw) dw` for `t > 0`. -/
theorem lintegral_dilate {t : ℝ} (ht : 0 < t) {F : Rd d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y = ENNReal.ofReal (t ^ d) * ∫⁻ w, F (t • w) := by
  have hdet : (t • (1 : Mat d)).det = t ^ d := by
    rw [det_smul, det_one, mul_one, Fintype.card_fin]
  have h := lintegral_comp_lin (B := t • (1 : Mat d)) (by rw [hdet]; positivity) hF
  have hlin : ∀ w : Rd d, lin (t • (1 : Mat d)) w = t • w := fun w => by
    rw [lin_smul, lin_one]; rfl
  simp_rw [hlin] at h
  rw [h, hdet, abs_of_pos (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- **The directional average**: `∫ F(|y|)⟨v,y⟩²/|y|² dy = (1/d) ∫ F(|y|) dy` for a unit `v`. -/
theorem lintegral_radial_mul_inner_sq (hd : 1 ≤ d) {v : Rd d} (hv : ‖v‖ = 1) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ y, F ‖y‖ * ENNReal.ofReal (⟪v, y⟫ ^ 2 / ‖y‖ ^ 2) =
      ENNReal.ofReal (1 / d) * ∫⁻ y : Rd d, F ‖y‖ := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  set σ := (volume : Measure (Rd d)).toSphere with hσ
  set I : ℝ≥0∞ := ∫⁻ r in Ioi (0 : ℝ), F r * ENNReal.ofReal (r ^ (d - 1)) with hI
  have hA := sphereArea_eq_toSphere hd
  have hsph : ∫⁻ η : Metric.sphere (0 : Rd d) 1, ENNReal.ofReal (⟪v, (η : Rd d)⟫ ^ 2) ∂σ =
      σ univ * ENNReal.ofReal (1 / d) := by
    have h1 : ∫⁻ u, ENNReal.ofReal (⟪v, u⟫ ^ 2) ∂normSphere d = ENNReal.ofReal (1 / d) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_normSphere hd (by fun_prop))
        (ae_of_all _ fun u => sq_nonneg _), integral_inner_sq hd, hv, one_pow]
    rw [normSphere, lintegral_smul_measure, lintegral_map (by fun_prop) measurable_subtype_coe] at h1
    have hne : σ univ ≠ 0 := by rw [← hA.1]; simp [hA.2]
    have hnt : σ univ ≠ ⊤ := by rw [← hA.1]; exact ENNReal.ofReal_ne_top
    rw [← h1, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]
  have hrad : ∫⁻ y : Rd d, F ‖y‖ = σ univ * I := by
    rw [lintegral_polar hd (fun y => F ‖y‖) (hF.comp measurable_norm)]
    rw [show (fun η : Metric.sphere (0 : Rd d) 1 => ∫⁻ r in Ioi (0 : ℝ),
        F ‖r • (η : Rd d)‖ * ENNReal.ofReal (r ^ (d - 1))) = fun _ => I from ?_]
    · rw [lintegral_const, mul_comm]
    · funext η
      refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  rw [lintegral_polar hd (fun y => F ‖y‖ * ENNReal.ofReal (⟪v, y⟫ ^ 2 / ‖y‖ ^ 2))
    ((hF.comp measurable_norm).mul (by fun_prop)), hrad]
  rw [show (fun η : Metric.sphere (0 : Rd d) 1 => ∫⁻ r in Ioi (0 : ℝ),
      F ‖r • (η : Rd d)‖ * ENNReal.ofReal (⟪v, r • (η : Rd d)⟫ ^ 2 / ‖r • (η : Rd d)‖ ^ 2) *
        ENNReal.ofReal (r ^ (d - 1))) =
      fun η : Metric.sphere (0 : Rd d) 1 => ENNReal.ofReal (⟪v, (η : Rd d)⟫ ^ 2) * I from ?_]
  · rw [lintegral_mul_const _ (by fun_prop), hsph]
    ring
  · funext η
    rw [hI, ← lintegral_const_mul _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hn : ‖r • (η : Rd d)‖ = r := by
      rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
    have hq : (r * ⟪v, (η : Rd d)⟫) ^ 2 / r ^ 2 = ⟪v, (η : Rd d)⟫ ^ 2 := by
      field_simp
    rw [hn, real_inner_smul_right, hq]
    ring

/-- **The dilation of the `G`-integrands**: for `φ ≥ 0` homogeneous of degree `2`,
`∫ (ηφ(z) ∧ s²)|z|^{-d-α} dz = s^{2-α}η^{α/2} ∫ (φ(w) ∧ 1)|w|^{-d-α} dw`. -/
theorem lintegral_min_dilate {α η s : ℝ} (hη : 0 < η) (hs : 0 < s) {φ : Rd d → ℝ}
    (hφm : Measurable φ) (_hφ0 : ∀ z, 0 ≤ φ z) (hφ : ∀ (t : ℝ) (w : Rd d), 0 < t → φ (t • w) = t ^ 2 * φ w) :
    ∫⁻ z, ENNReal.ofReal (min (η * φ z) (s ^ 2) * ‖z‖ ^ (-(d : ℝ) - α)) =
      ENNReal.ofReal (s ^ (2 - α) * η ^ (α / 2)) *
        ∫⁻ w, ENNReal.ofReal (min (φ w) 1 * ‖w‖ ^ (-(d : ℝ) - α)) := by
  set t := s / Real.sqrt η with ht
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have ht0 : 0 < t := div_pos hs hsη
  have hηt : η * t ^ 2 = s ^ 2 := by
    rw [ht, div_pow, Real.sq_sqrt hη.le]; field_simp
  rw [lintegral_dilate ht0 (by fun_prop), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hφ t w ht0, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
    Real.mul_rpow ht0.le (norm_nonneg w), ← mul_assoc η, hηt,
    show min (s ^ 2 * φ w) (s ^ 2) = s ^ 2 * min (φ w) 1 by
      rw [mul_min_of_nonneg _ _ (sq_nonneg s), mul_one]]
  have h1 : t ^ d * (s ^ 2 * t ^ (-(d : ℝ) - α)) = s ^ 2 * t ^ (-α) := by
    rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add ht0,
      show (d : ℝ) + (-(d : ℝ) - α) = -α by ring]
  have h2 : t ^ (-α) = s ^ (-α) * η ^ (α / 2) := by
    rw [ht, Real.div_rpow hs.le hsη.le, Real.rpow_neg hsη.le α, div_inv_eq_mul, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hη.le]
    congr 2
    ring
  have h3 : s ^ 2 * s ^ (-α) = s ^ (2 - α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    norm_num
    ring_nf
  have hpow : t ^ d * (s ^ 2 * t ^ (-(d : ℝ) - α)) = s ^ (2 - α) * η ^ (α / 2) := by
    rw [h1, h2, ← mul_assoc, h3]
  rw [← hpow]
  ring

theorem inner_lin_msqrt {H : Mat d} (hH : H.PosSemidef) {v : Rd d} {η : ℝ}
    (hv : lin H v = η • v) (y : Rd d) : ⟪v, lin (msqrt H) y⟫ = Real.sqrt η * ⟪v, y⟫ := by
  rw [real_inner_comm, inner_lin_left, msqrt_transpose, lin_msqrt_eigvec hH hv,
    real_inner_smul_right, real_inner_comm]

theorem norm_lin_msqrt_sq {H : Mat d} (hH : H.PosSemidef) (y : Rd d) :
    ‖lin (msqrt H) y‖ ^ 2 = quad H y := by
  rw [← real_inner_self_eq_norm_sq, inner_lin_left, msqrt_transpose, ← lin_mul_apply,
    msqrt_mul_self hH, quad, real_inner_comm]

/-- **The upper Rayleigh bound**: for a unit eigenvector `v` of `H`, eigenvalue `η`,
`⟨v, 𝓜_s(n_H)v⟩ ≤ c_{d,α}^{-1} η^{α/2} s^{2-α} G₀`. -/
theorem ofReal_quad_moment_stable_le [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) {v : Rd d} (hv : ‖v‖ = 1) {η : ℝ} (hHv : lin H v = η • v) {s : ℝ}
    (hs : 0 < s) :
    ENNReal.ofReal (quad (momentMatrix s (stableLevy α H)) v) ≤
      ENNReal.ofReal (stableConst (d := d) α)⁻¹ *
        (ENNReal.ofReal (s ^ (2 - α) * η ^ (α / 2)) * ENNReal.ofReal (degConstG0 (d := d) α)) := by
  set l : Fin d := ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩ with hl
  have hη : 0 < η := by
    have h := quad_pos hH (show v ≠ 0 by rintro rfl; simp at hv)
    rw [quad, hHv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at h
    simpa using h
  have hL := (stableLevy_props hα0 hα2 hH).1
  rw [quad_momentMatrix hL, ofReal_integral_eq_lintegral_ofReal (integrable_moment_quad hL s v)
    (ae_of_all _ fun x => by positivity)]
  have hpt : ∀ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) (s ^ 2) * ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2) ≤
      ENNReal.ofReal (min (⟪v, x⟫ ^ 2) (s ^ 2)) := by
    intro x
    refine ENNReal.ofReal_le_ofReal ?_
    rcases (norm_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [sq_nonneg]
    have ha : ⟪v, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
      have := abs_real_inner_le_norm v x
      rw [hv, one_mul] at this
      exact sq_le_sq' (by linarith [neg_abs_le ⟪v, x⟫]) (le_trans (le_abs_self _) this)
    have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    refine le_min ?_ ?_
    · rw [mul_div_assoc]
      calc min (‖x‖ ^ 2) (s ^ 2) * (⟪v, x⟫ ^ 2 / ‖x‖ ^ 2) ≤ ‖x‖ ^ 2 * (⟪v, x⟫ ^ 2 / ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = ⟪v, x⟫ ^ 2 := by field_simp
    · rw [mul_div_assoc]
      calc min (‖x‖ ^ 2) (s ^ 2) * (⟪v, x⟫ ^ 2 / ‖x‖ ^ 2) ≤ s ^ 2 * 1 :=
            mul_le_mul (min_le_right _ _) ((div_le_one hx2).2 ha) (by positivity) (sq_nonneg s)
        _ = s ^ 2 := mul_one _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_stableLevy hα0 hα2 hH (by fun_prop) (by simp)]
  refine mul_le_mul_right (le_of_eq ?_) _
  have hel : ‖(ebasis l : Rd d)‖ = 1 := by simp [ebasis]
  set R := (ℝ ∙ (v - ebasis l))ᗮ.reflection with hR
  have hRv : R v = ebasis l := Submodule.reflection_sub (hv.trans hel.symm)
  have hself : ∀ a b : Rd d, ⟪a, R b⟫ = ⟪R a, b⟫ := fun a b => by
    rw [← R.inner_map_map a (R b), hR, Submodule.reflection_reflection]
  set F : Rd d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (min (η * ⟪v, y⟫ ^ 2) (s ^ 2) * ‖y‖ ^ (-(d : ℝ) - α)) with hF
  have h1 : ∀ y : Rd d, ENNReal.ofReal (min (⟪v, lin (msqrt H) y⟫ ^ 2) (s ^ 2)) *
      ENNReal.ofReal (‖y‖ ^ (-(d : ℝ) - α)) = F y := by
    intro y
    rw [hF, inner_lin_msqrt hH.posSemidef hHv, mul_pow, Real.sq_sqrt hη.le,
      ← ENNReal.ofReal_mul (le_min (by positivity) (sq_nonneg s))]
  rw [lintegral_congr h1, ← (R.measurePreserving).lintegral_comp_emb
    R.toHomeomorph.measurableEmbedding F]
  have h2 : ∀ z : Rd d, F (R z) =
      ENNReal.ofReal (min (η * z l ^ 2) (s ^ 2) * ‖z‖ ^ (-(d : ℝ) - α)) := by
    intro z
    rw [hF]
    simp only [LinearIsometryEquiv.norm_map]
    rw [hself, hRv, inner_ebasis_left]
  rw [lintegral_congr h2, lintegral_min_dilate hη hs (φ := fun z : Rd d => z l ^ 2) (by fun_prop)
    (fun z => sq_nonneg _) (fun t w _ => by simp [mul_pow]), degConstG0,
    ofReal_integral_eq_lintegral_ofReal (degConst_props (d := d) hα0 hα2).1
      (ae_of_all _ fun z => by positivity)]

/-- **The lower Rayleigh bound**: for a unit eigenvector `v` of `H` for an eigenvalue `η` with
`⟨y, Hy⟩ ≤ η|y|²`, `⟨v, 𝓜_s(n_H)v⟩ ≥ c_{d,α}^{-1} d^{-1} η^{α/2} s^{2-α} G₁`. -/
theorem ofReal_quad_moment_stable_ge [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) {v : Rd d} (hv : ‖v‖ = 1) {η : ℝ} (hHv : lin H v = η • v)
    (hmax : ∀ y : Rd d, quad H y ≤ η * ‖y‖ ^ 2) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (stableConst (d := d) α)⁻¹ * (ENNReal.ofReal (1 / d) *
        (ENNReal.ofReal (s ^ (2 - α) * η ^ (α / 2)) * ENNReal.ofReal (degConstG1 d α))) ≤
      ENNReal.ofReal (quad (momentMatrix s (stableLevy α H)) v) := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hη : 0 < η := by
    have h := quad_pos hH (show v ≠ 0 by rintro rfl; simp at hv)
    rw [quad, hHv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at h
    simpa using h
  have hL := (stableLevy_props hα0 hα2 hH).1
  rw [quad_momentMatrix hL, ofReal_integral_eq_lintegral_ofReal (integrable_moment_quad hL s v)
    (ae_of_all _ fun x => by positivity), lintegral_stableLevy hα0 hα2 hH (by fun_prop) (by simp)]
  refine mul_le_mul_right ?_ _
  rw [degConstG1, ofReal_integral_eq_lintegral_ofReal (degConst_props (d := d) hα0 hα2).2.2.1
    (ae_of_all _ fun z => by positivity),
    ← lintegral_min_dilate hη hs (φ := fun z : Rd d => ‖z‖ ^ 2) (by fun_prop) (fun z => sq_nonneg _)
      (fun t w ht => by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow])]
  rw [← lintegral_radial_mul_inner_sq hd1 hv (F := fun r => ENNReal.ofReal
    (min (η * r ^ 2) (s ^ 2) * r ^ (-(d : ℝ) - α))) (by fun_prop)]
  refine lintegral_mono fun y => ?_
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · have hy : y = 0 := norm_eq_zero.1 h0.symm
    subst hy
    simp
  have hpw : 0 ≤ ‖y‖ ^ (-(d : ℝ) - α) := Real.rpow_nonneg (norm_nonneg y) _
  rw [← ENNReal.ofReal_mul (mul_nonneg (le_min (by positivity) (sq_nonneg s)) hpw),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show min (η * ‖y‖ ^ 2) (s ^ 2) * ‖y‖ ^ (-(d : ℝ) - α) * (⟪v, y⟫ ^ 2 / ‖y‖ ^ 2) =
    min (η * ‖y‖ ^ 2) (s ^ 2) * (⟪v, y⟫ ^ 2 / ‖y‖ ^ 2) * ‖y‖ ^ (-(d : ℝ) - α) by ring]
  refine mul_le_mul_of_nonneg_right ?_ hpw
  set q := ‖lin (msqrt H) y‖ ^ 2 with hq
  set Q := η * ‖y‖ ^ 2 with hQ
  have hqQ : q ≤ Q := by rw [hq, norm_lin_msqrt_sq hH.posSemidef]; exact hmax y
  have hq0 : 0 < q := by
    rw [hq, norm_lin_msqrt_sq hH.posSemidef]
    exact quad_pos hH (norm_pos_iff.1 hpos)
  have hQ0 : 0 < Q := by positivity
  rw [inner_lin_msqrt hH.posSemidef hHv, mul_pow, Real.sq_sqrt hη.le]
  have hratio : min Q (s ^ 2) / Q ≤ min q (s ^ 2) / q := by
    rw [div_le_div_iff₀ hQ0 hq0]
    rcases le_or_gt Q (s ^ 2) with h | h
    · rw [min_eq_left h, min_eq_left (hqQ.trans h)]
      linarith [mul_comm Q q]
    · rw [min_eq_right h.le]
      rcases le_or_gt q (s ^ 2) with h' | h'
      · rw [min_eq_left h']
        nlinarith
      · rw [min_eq_right h'.le]
        nlinarith [sq_nonneg s]
  calc min (η * ‖y‖ ^ 2) (s ^ 2) * (⟪v, y⟫ ^ 2 / ‖y‖ ^ 2)
      = min Q (s ^ 2) / Q * (η * ⟪v, y⟫ ^ 2) := by
        rw [hQ]; field_simp
    _ ≤ min q (s ^ 2) / q * (η * ⟪v, y⟫ ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = min q (s ^ 2) * (η * ⟪v, y⟫ ^ 2) / q := by ring

/-- **The condition number of the stable moment matrices**:
`cond 𝓜_s(n_H) ≥ (G₁/(dG₀)) ecc(H)^{α/2}`, by the two Rayleigh quotients. -/
theorem condNum_moment_stable_ge [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (degConstG1 d α / (d * degConstG0 (d := d) α) * ecc H ^ (α / 2)) ≤
      condNum (momentMatrix s (stableLevy α H)) := by
  obtain ⟨vp, hvp, hHvp⟩ := exists_unit_eigvec_eigUp hH.isHermitian (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hH.isHermitian] at hHvp
  obtain ⟨vm, hvm, hHvm⟩ := exists_unit_eigvec_eigUp hH.isHermitian 0
  rw [← lamMin_eq_eigUp_zero hH.isHermitian] at hHvm
  set ηp := lamMax H with hηp
  set ηm := lamMin H with hηm
  have hp0 : 0 < ηp := lamMax_pos hH
  have hm0 : 0 < ηm := lamMin_pos hH
  obtain ⟨-, hG0, -, hG1⟩ := degConst_props (d := d) hα0 hα2
  have hc : 0 < (stableConst (d := d) α)⁻¹ := inv_pos.2 (stableConst_pos_finite (d := d) hα0 hα2).2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from Nat.pos_of_ne_zero (NeZero.ne d))
  have hL := (stableLevy_props hα0 hα2 hH).1
  set M := momentMatrix s (stableLevy α H) with hM
  have hMpsd : M.PosSemidef := momentMatrix_posSemidef hL s
  have hup := ofReal_quad_moment_stable_le hα0 hα2 hH hvm hHvm hs
  have hlo := ofReal_quad_moment_stable_ge hα0 hα2 hH hvp hHvp
    (fun y => quad_le_lamMax_mul hH.isHermitian y) hs
  set B := (stableConst (d := d) α)⁻¹ * (s ^ (2 - α) * ηm ^ (α / 2) * degConstG0 (d := d) α)
    with hB
  set A := (stableConst (d := d) α)⁻¹ * (1 / d * (s ^ (2 - α) * ηp ^ (α / 2) * degConstG1 d α))
    with hA
  have hb : quad M vm ≤ B := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc.le] at hup
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have ha : A ≤ quad M vp := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hc.le] at hlo
    exact (ENNReal.ofReal_le_ofReal_iff (quad_nonneg hMpsd _)).1 hlo
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  unfold condNum
  split_ifs with h0
  · exact le_top
  · have hmin : 0 < lamMin M := lt_of_le_of_ne (lamMin_nonneg hMpsd) (Ne.symm h0)
    have hlm : lamMin M ≤ quad M vm := lamMin_le_inner hMpsd.isHermitian hvm
    have hlM : quad M vp ≤ lamMax M := quad_le_lamMax hMpsd.isHermitian hvp
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : degConstG1 d α / (d * degConstG0 (d := d) α) * ecc H ^ (α / 2) = A / B := by
      rw [ecc, ← hηp, ← hηm, Real.div_rpow hp0.le hm0.le, hA, hB]
      have h1 : 0 < ηm ^ (α / 2) := Real.rpow_pos_of_pos hm0 _
      have h2 : 0 < s ^ (2 - α) := Real.rpow_pos_of_pos hs _
      have h3 : stableConst (d := d) α ≠ 0 := (stableConst_pos_finite (d := d) hα0 hα2).2.ne'
      field_simp
    rw [heq]
    exact div_le_div₀ (hA0.le.trans (ha.trans hlM)) (ha.trans hlM) hmin (hlm.trans hb)

/-! ## The rank-one limit of the degenerate family is `0` -/

theorem mrpow_sigmaEps [NeZero d] {ε : ℝ} (hε : 0 ≤ ε) {p : ℝ} (_hp : 0 < p) :
    mrpow (sigmaEps d ε) p = sigmaEps d (ε ^ p) := by
  have h1 : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
  have hw : ∀ i : Fin d, 0 ≤ (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else ε) i := fun i => by
    simp only; split_ifs <;> linarith
  have hS : sigmaEps d ε = udiag 1 (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else ε) := by
    simp [sigmaEps, udiag]
  rw [hS, mrpow_udiag h1 hw]
  simp only [sigmaEps, udiag, Matrix.one_mul, transpose_one, Matrix.mul_one]
  congr 1
  funext i
  split_ifs <;> simp [Real.one_rpow]

theorem sigmaEps_inv [NeZero d] {t : ℝ} (ht : 0 < t) : (sigmaEps d t)⁻¹ = sigmaEps d t⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [sigmaEps, sigmaEps, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs
  · norm_num
  · exact mul_inv_cancel₀ ht.ne'

theorem det_sigmaEps [NeZero d] (ε : ℝ) : (sigmaEps d ε).det = ε ^ (d - 1) := by
  rw [sigmaEps, det_diagonal, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (0 : Fin d))]
  have h0 : (if ((0 : Fin d) : ℕ) = 0 then (1 : ℝ) else ε) = 1 := by simp
  rw [h0, mul_one, Finset.prod_congr rfl (g := fun _ => ε) fun i hi => if_neg (fun h =>
    Finset.ne_of_mem_erase hi (Fin.ext_iff.2 (by simp [h]))), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- **`L_* = 0`** for the degenerate gauge: on every set bounded away from the origin
`n_{h(Σ_ε)} ≤ n_I` and `n_{h(Σ_ε)}(x) ≤ c^{-1}(ε^{-p}(|x|² - x₁²))^{-(d+α)/2} → 0` off the null set
`{x₂ = ⋯ = x_d = 0}`. -/
theorem degenerate_rankOne_zero [NeZero d] (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {γ p : ℝ} (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) (hdp : (d : ℝ) * γ + p = 1)
    (hγα : 1 ≤ ((d : ℝ) + α) * γ) :
    IsRankOneLimit (fun S : Mat d => stableLevy α (degGauge γ p S)) 0 := by
  refine ⟨by simp, fun B hB hBa => ?_⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp [i1] at this
  have hc : 0 ≤ (stableConst (d := d) α)⁻¹ :=
    inv_nonneg.2 (stableConst_pos_finite (d := d) hα0 hα2).2.le
  set E := B ∩ ({0}ᶜ : Set (Rd d)) with hE
  have hEm : MeasurableSet E := hB.inter (measurableSet_singleton _).compl
  have happly : ∀ H : Mat d, stableLevy α H B =
      ∫⁻ x, E.indicator (fun x => ENNReal.ofReal (stableDensity α H x)) x := by
    intro H
    rw [stableLevy, withDensity_apply _ hB, Measure.restrict_restrict hB, lintegral_indicator hEm]
  simp_rw [happly]
  have h0 : (0 : Measure (Rd d)) B = ∫⁻ x, (0 : Rd d → ℝ≥0∞) x := by simp
  rw [h0]
  have hL1 := (stableLevy_props (d := d) hα0 hα2 (H := 1) PosDef.one).1
  obtain ⟨n, hn⟩ := hBa.exists_subset
  have hfin : ∫⁻ x, E.indicator (fun x => ENNReal.ofReal (stableDensity α (1 : Mat d) x)) x ≠ ⊤ := by
    rw [← happly]
    exact ne_top_of_le_ne_top (hL1.awaySet_ne_top n) (measure_mono hn)
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun x => E.indicator (fun x => ENNReal.ofReal (stableDensity α (1 : Mat d) x)) x) ?_ ?_ hfin ?_
  · exact Eventually.of_forall fun ε =>
      ((measurable_stableDensity α _).ennreal_ofReal.indicator hEm)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ae_of_all _ fun x => ?_
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle := stableDensity_degGauge_mono hα0 hα2 hγ hp0 hp1 hdp hγα
        (sigmaEps_posDef hε.1) PosDef.one
        (by rw [← sigmaEps_one]; exact sigmaEps_le hε.2.le) x hx.2
      rwa [degGauge_one] at hle
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · /- the limit, off `{x : x₂ = 0}` -/
    have hnull : volume {x : Rd d | x i1 = 0} = 0 := by
      have he : (ebasis i1 : Rd d) ≠ 0 := by
        intro h; have := congrArg (fun x : Rd d => x i1) h; simp [ebasis] at this
      refine measure_mono_null (fun x (hx : x i1 = 0) => ?_)
        (Measure.addHaar_submodule volume (ℝ ∙ (ebasis i1 : Rd d))ᗮ ?_)
      · rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_ebasis_left]
        exact hx
      · intro htop
        have : (ebasis i1 : Rd d) ∈ (ℝ ∙ (ebasis i1 : Rd d))ᗮ := by rw [htop]; trivial
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at this
        exact he (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
    filter_upwards [compl_mem_ae_iff.2 hnull] with x hx
    have hx1 : x i1 ≠ 0 := hx
    by_cases hxE : x ∈ E
    · simp only [indicator_of_mem hxE, Pi.zero_apply]
      have hx0 : x ≠ 0 := hxE.2
      set r := ‖x‖ ^ 2 - x 0 ^ 2 with hr
      have hr0 : 0 < r := by
        have h := EuclideanSpace.norm_sq_eq x
        simp only [Real.norm_eq_abs, sq_abs] at h
        rw [hr, h, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d)), add_sub_cancel_left]
        exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => x i ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_erase.2 ⟨h10, Finset.mem_univ _⟩))
      have hbound : ∀ ε ∈ Ioo (0 : ℝ) 1, stableDensity α (degGauge γ p (sigmaEps d ε)) x ≤
          (stableConst (d := d) α)⁻¹ * (r ^ (-((d : ℝ) + α) / 2) *
            ε ^ (p * (((d : ℝ) + α) / 2))) := by
        intro ε hε
        have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε.1 p
        rw [stableDensity_degGauge hγ hdp (sigmaEps_posDef hε.1) x hx0, mrpow_sigmaEps hε.1.le hp0,
          sigmaEps_inv hεp, quad_sigmaEps, det_sigmaEps]
        have hdet : (ε ^ (d - 1)) ^ ((((d : ℝ) + α) * γ - 1) / 2) ≤ 1 :=
          Real.rpow_le_one (pow_nonneg hε.1.le _) (pow_le_one₀ hε.1.le hε.2.le) (by linarith)
        have hq : (ε ^ p)⁻¹ * r ≤ (ε ^ p)⁻¹ * ‖x‖ ^ 2 + (1 - (ε ^ p)⁻¹) * x 0 ^ 2 := by
          rw [hr]; nlinarith [sq_nonneg (x 0)]
        have hq0 : 0 < (ε ^ p)⁻¹ * r := by positivity
        have hpow : ((ε ^ p)⁻¹ * r) ^ (-((d : ℝ) + α) / 2) =
            r ^ (-((d : ℝ) + α) / 2) * ε ^ (p * (((d : ℝ) + α) / 2)) := by
          rw [Real.mul_rpow (inv_nonneg.2 hεp.le) hr0.le, Real.inv_rpow hεp.le,
            ← Real.rpow_neg hεp.le, ← Real.rpow_mul hε.1.le]
          rw [mul_comm]
          congr 2
          ring
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc (ε ^ (d - 1)) ^ ((((d : ℝ) + α) * γ - 1) / 2) *
              ((ε ^ p)⁻¹ * ‖x‖ ^ 2 + (1 - (ε ^ p)⁻¹) * x 0 ^ 2) ^ (-((d : ℝ) + α) / 2)
            ≤ 1 * ((ε ^ p)⁻¹ * r) ^ (-((d : ℝ) + α) / 2) := by
              refine mul_le_mul hdet (Real.rpow_le_rpow_of_nonpos hq0 hq (by linarith))
                (Real.rpow_nonneg (hq0.le.trans hq) _) zero_le_one
          _ = r ^ (-((d : ℝ) + α) / 2) * ε ^ (p * (((d : ℝ) + α) / 2)) := by rw [one_mul, hpow]
      have hlim : Tendsto (fun ε : ℝ => (stableConst (d := d) α)⁻¹ * (r ^ (-((d : ℝ) + α) / 2) *
          ε ^ (p * (((d : ℝ) + α) / 2)))) (𝓝[>] 0) (𝓝 0) := by
        have hcont : ContinuousAt (fun ε : ℝ => ε ^ (p * (((d : ℝ) + α) / 2))) 0 :=
          Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
        have hcont' : ContinuousAt (fun ε : ℝ => (stableConst (d := d) α)⁻¹ *
            (r ^ (-((d : ℝ) + α) / 2) * ε ^ (p * (((d : ℝ) + α) / 2)))) 0 :=
          continuousAt_const.mul (continuousAt_const.mul hcont)
        have h := hcont'.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa [Real.zero_rpow (by positivity : p * (((d : ℝ) + α) / 2) ≠ 0)] using h
      have hlim' : Tendsto (fun ε : ℝ => stableDensity α (degGauge γ p (sigmaEps d ε)) x)
          (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
          exact stableDensity_nonneg hα0 hα2 (degGauge_posDef (sigmaEps_posDef hε.1)) x
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
          exact hbound ε hε
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim'
      rw [ENNReal.ofReal_zero] at this
      exact this
    · simp only [indicator_of_notMem hxE, Pi.zero_apply]
      exact tendsto_const_nhds

/-- The parameter range of `prop:similarity-degenerate-family`: for `1/(d+α) ≤ γ < 1/d`,
`p := 1 - dγ ∈ (0, α/(d+α)] ⊂ (0,1)`, `dγ + p = 1`, `(d+α)γ ≥ 1`, `γ > 0`. -/
theorem degenerate_params [NeZero d] {α : ℝ} (hα0 : 0 < α) {γ : ℝ}
    (hγ1 : 1 / ((d : ℝ) + α) ≤ γ) (hγ2 : γ < 1 / (d : ℝ)) :
    0 < γ ∧ 0 < 1 - d * γ ∧ 1 - d * γ ≤ α / ((d : ℝ) + α) ∧ 1 - d * γ < 1 ∧
      (d : ℝ) * γ + (1 - d * γ) = 1 ∧ 1 ≤ ((d : ℝ) + α) * γ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdα : (0 : ℝ) < d + α := by linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ1
  have hγα : 1 ≤ ((d : ℝ) + α) * γ := by rwa [div_le_iff₀ hdα, mul_comm] at hγ1
  have h1 : (d : ℝ) * γ < 1 := by rwa [lt_div_iff₀ hd0, mul_comm] at hγ2
  have hpα : 1 - (d : ℝ) * γ ≤ α / ((d : ℝ) + α) := by
    rw [le_div_iff₀ hdα]
    nlinarith
  refine ⟨hγ0, by linarith, hpα, ?_, by ring, hγα⟩
  have : α / ((d : ℝ) + α) < 1 := by rw [div_lt_one hdα]; linarith
  linarith

/-- **`prop:similarity-degenerate-family`(2)**, unbounded shape: for `Σ ∈ PD(d)`,
`ecc(h(Σ)) = ecc(Σ)^p`, `es(ψ_Σ) = ecc(Σ)^{pα/2}`, `rs(L_Σ) ≥ ecc(Σ)^{pα/2}`, and
`cond 𝓜_s(L_Σ) ≥ (G₁/(dG₀)) ecc(Σ)^{pα/2}` for every `s > 0`, with `G₀`, `G₁` finite and positive;
the rank-one limit is `L_* = 0`. -/
theorem degenerate_unbounded [NeZero d] (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (γ : ℝ)
    (hγ1 : 1 / ((d : ℝ) + α) ≤ γ) (hγ2 : γ < 1 / (d : ℝ)) :
    let p : ℝ := 1 - d * γ
    (∀ S : Mat d, S.PosDef →
      ecc (degGauge γ p S) = ecc S ^ p ∧
      expSpread (stableExp α (degGauge γ p S)) = ENNReal.ofReal (ecc S ^ (p * α / 2)) ∧
      ENNReal.ofReal (ecc S ^ (p * α / 2)) ≤ rotSpread (stableLevy α (degGauge γ p S)) ∧
      ∀ s : ℝ, 0 < s →
        ENNReal.ofReal (degConstG1 d α / (d * degConstG0 (d := d) α) * ecc S ^ (p * α / 2)) ≤
          condNum (momentMatrix s (stableLevy α (degGauge γ p S)))) ∧
    (Integrable (fun z : Rd d =>
        min (z ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)) ∧
      0 < degConstG0 (d := d) α) ∧
    (Integrable (fun z : Rd d => min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)) ∧ 0 < degConstG1 d α) ∧
    IsRankOneLimit (fun S : Mat d => stableLevy α (degGauge γ p S)) 0 := by
  intro p
  obtain ⟨hγ0, hp0, -, hp1, hdp, hγα⟩ := degenerate_params hα0 hγ1 hγ2
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hi0, hG0, hi1, hG1⟩ := degConst_props (d := d) hα0 hα2
  refine ⟨fun S hS => ?_, ⟨hi0, hG0⟩, ⟨hi1, hG1⟩,
    degenerate_rankOne_zero hd hα0 hα2 hγ0 hp0 hp1 hdp hγα⟩
  have hH := degGauge_posDef (γ := γ) (p := p) hS
  have hecc := ecc_degGauge (γ := γ) hp0 hS
  have hecc0 : 0 ≤ ecc S := div_nonneg (lamMax_pos hS).le (lamMin_pos hS).le
  have hpow : ecc (degGauge γ p S) ^ (α / 2) = ecc S ^ (p * α / 2) := by
    rw [hecc, ← Real.rpow_mul hecc0]
    congr 1
    ring
  have hes : expSpread (stableExp α (degGauge γ p S)) = ENNReal.ofReal (ecc S ^ (p * α / 2)) := by
    rw [expSpread_stable hd1 hα0 hH, hpow]
  obtain ⟨hL, hψ⟩ := stableLevy_props hα0 hα2 hH
  refine ⟨hecc, hes, ?_, fun s hs => ?_⟩
  · rw [← hes, show stableExp α (degGauge γ p S) = levyExp (stableLevy α (degGauge γ p S)) from
      funext fun ω => (hψ ω).symm]
    exact expSpread_levyExp_le _
  · have := condNum_moment_stable_ge hα0 hα2 hH hs
    rwa [hpow] at this

/-! ## Clause (3): the isotropic second part `S'_β(tr(Σ) I)` -/

theorem stableDensity_smul_one [NeZero d] {β t : ℝ} (ht : 0 < t) (x : Rd d) :
    stableDensity β (t • (1 : Mat d)) x = t ^ (β / 2) * stableDensity β (1 : Mat d) x := by
  have hinv : (t • (1 : Mat d))⁻¹ = t⁻¹ • (1 : Mat d) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ ht.ne',
      one_smul]
  unfold stableDensity
  rw [hinv, inv_one, quad_smul, quad_one, det_smul, det_one, mul_one, Fintype.card_fin,
    Real.mul_rpow (inv_nonneg.2 ht.le) (sq_nonneg _), Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
    ← Real.rpow_natCast, ← Real.rpow_mul ht.le, Real.one_rpow, mul_one]
  have h : t ^ ((d : ℝ) * (-(1 : ℝ) / 2)) * t ^ (-(-((d : ℝ) + β) / 2)) = t ^ (β / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc (stableConst (d := d) β)⁻¹ * t ^ ((d : ℝ) * (-(1 : ℝ) / 2)) *
        (t ^ (-(-((d : ℝ) + β) / 2)) * (‖x‖ ^ 2) ^ (-((d : ℝ) + β) / 2))
      = (t ^ ((d : ℝ) * (-(1 : ℝ) / 2)) * t ^ (-(-((d : ℝ) + β) / 2))) *
        ((stableConst (d := d) β)⁻¹ * (‖x‖ ^ 2) ^ (-((d : ℝ) + β) / 2)) := by ring
    _ = t ^ (β / 2) * ((stableConst (d := d) β)⁻¹ * (‖x‖ ^ 2) ^ (-((d : ℝ) + β) / 2)) := by rw [h]

theorem stableLevy_smul_one [NeZero d] {β t : ℝ} (ht : 0 < t) :
    stableLevy β (t • (1 : Mat d)) = ENNReal.ofReal (t ^ (β / 2)) • stableLevy β (1 : Mat d) := by
  unfold stableLevy
  rw [← withDensity_smul _ (measurable_stableDensity β 1).ennreal_ofReal]
  congr 1
  funext x
  rw [stableDensity_smul_one ht, Pi.smul_apply, smul_eq_mul,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]

theorem stableLevy_one_rotationInvariant [NeZero d] (β : ℝ) :
    IsRotationInvariant (stableLevy β (1 : Mat d)) := by
  intro Q hQ
  have hrad : ∀ x : Rd d, ENNReal.ofReal (stableDensity β (1 : Mat d) (orthIsometry hQ x)) =
      ENNReal.ofReal (stableDensity β (1 : Mat d) x) := by
    intro x
    unfold stableDensity
    rw [inv_one, quad_one, quad_one, orthIsometry_apply, norm_lin_of_orth hQ]
  unfold stableLevy push
  rw [MeasureTheory.restrict_compl_singleton]
  have h := map_withDensity_isometry (orthIsometry hQ)
    (measurable_stableDensity β (1 : Mat d)).ennreal_ofReal hrad
  exact h

theorem stableLevy_one_ne_zero [NeZero d] {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) :
    stableLevy β (1 : Mat d) ≠ 0 := by
  intro h0
  have h := (stableLevy_props (d := d) hβ0 hβ2 PosDef.one).2 (ebasis 0)
  rw [h0] at h
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  rw [stableExp, quad_one, he, one_pow, Real.one_rpow] at h
  simp [levyExp, levyExpL] at h

theorem stableExp_smul_one {β t : ℝ} (ht : 0 ≤ t) (_hβ : 0 < β) (ω : Rd d) :
    stableExp β (t • (1 : Mat d)) ω = t ^ (β / 2) * ‖ω‖ ^ β := by
  rw [stableExp, quad_smul, quad_one, Real.mul_rpow ht (sq_nonneg _), ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  push_cast
  ring

theorem trace_act_simSet {A : Mat d} (hA : A ∈ simSet d) (S : Mat d) :
    act A (S.trace • (1 : Mat d)) = (act A S).trace • (1 : Mat d) := by
  obtain ⟨c, hc, Q, hQ, rfl⟩ := hA
  have hQQ : Q * Qᵀ = 1 := orth_mul_transpose hQ
  have hQQ' : Qᵀ * Q = 1 := mul_eq_one_comm.1 hQQ
  have htr : (Q * S * Qᵀ).trace = S.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
  rw [act_smul_left, act_smul_left, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQQ,
    trace_smul, htr, smul_eq_mul, smul_smul]

/-- The stable increments along the degenerate gauge, from (1). -/
theorem exists_degGauge_increment [NeZero d] {α γ p : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) (hdp : (d : ℝ) * γ + p = 1)
    (hγα : 1 ≤ ((d : ℝ) + α) * γ) {S S' : Mat d} (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (hle : loewnerLE S S') :
    ∃ τ : Measure (Rd d), IsProbabilityMeasure τ ∧ IsInfinitelyDivisible τ ∧ ∀ ω : Rd d,
      charFun τ ω = ((Real.exp (-(stableExp α (degGauge γ p S') ω -
        stableExp α (degGauge γ p S) ω)) : ℝ) : ℂ) := by
  by_cases hSpd : S.PosDef
  · have hS'pd : S'.PosDef := by
      have := hSpd.add_posSemidef hle
      rwa [add_sub_cancel] at this
    obtain ⟨ρ, hρ, hρid, -, hρc⟩ := exists_stable_increment hα0 hα2 (degGauge_posDef hSpd)
      (degGauge_posDef hS'pd) fun x hx =>
        stableDensity_degGauge_mono hα0 hα2 hγ hp0 hp1 hdp hγα hSpd hS'pd hle x hx
    exact ⟨ρ, hρ, hρid, hρc⟩
  · have hdet0 : S.det = 0 := by
      by_contra h
      exact hSpd (hS.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det S).2
        (isUnit_iff_ne_zero.2 h)))
    rw [degGauge_singular hγ hdet0]
    by_cases hS'pd : S'.PosDef
    · obtain ⟨ρ, hρ, hρid, -⟩ := exists_ellipticalStable hα0 hα2 (degGauge_posDef (γ := γ)
        (p := p) hS'pd)
      refine ⟨ρ, hρ.1, hρid, fun ω => ?_⟩
      rw [hρ.2, stableExp_zero_mat hα0, sub_zero]
    · have hdet0' : S'.det = 0 := by
        by_contra h
        exact hS'pd (hS'.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det S').2
          (isUnit_iff_ne_zero.2 h)))
      refine ⟨multivariateGaussian 0 0, inferInstance,
        isInfinitelyDivisible_gaussian PosSemidef.zero, fun ω => ?_⟩
      rw [degGauge_singular hγ hdet0', stableExp_zero_mat hα0,
        charFun_multivariateGaussian_zero PosSemidef.zero, quad_zero]
      simp

/-- The stable increments along the trace gauge `tr(Σ) I`. -/
theorem exists_trace_increment [NeZero d] {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) {S S' : Mat d}
    (hS : S.PosSemidef) (hle : loewnerLE S S') :
    ∃ τ : Measure (Rd d), IsProbabilityMeasure τ ∧ IsInfinitelyDivisible τ ∧ ∀ ω : Rd d,
      charFun τ ω = ((Real.exp (-(stableExp β (S'.trace • (1 : Mat d)) ω -
        stableExp β (S.trace • (1 : Mat d)) ω)) : ℝ) : ℂ) := by
  have htr : S.trace ≤ S'.trace := trace_le_of_loewnerLE hle
  have ht0 := hS.trace_nonneg
  rcases ht0.eq_or_lt with h0 | hpos
  · have hz : ∀ ω : Rd d, stableExp β (0 : Mat d) ω = 0 := stableExp_zero_mat hβ0
    rw [← h0, zero_smul]
    simp_rw [hz, sub_zero]
    rcases (h0.le.trans htr).eq_or_lt with h0' | hpos'
    · refine ⟨multivariateGaussian 0 0, inferInstance,
        isInfinitelyDivisible_gaussian PosSemidef.zero, fun ω => ?_⟩
      rw [← h0', zero_smul, hz, charFun_multivariateGaussian_zero PosSemidef.zero, quad_zero]
      simp
    · obtain ⟨ρ, hρ, hρid, -⟩ := exists_ellipticalStable hβ0 hβ2
        (PosDef.one.smul hpos' : (S'.trace • (1 : Mat d)).PosDef)
      refine ⟨ρ, hρ.1, hρid, fun ω => ?_⟩
      rw [hρ.2]
  · have hpos' : 0 < S'.trace := hpos.trans_le htr
    obtain ⟨ρ, hρ, hρid, -, hρc⟩ := exists_stable_increment hβ0 hβ2
      (PosDef.one.smul hpos : (S.trace • (1 : Mat d)).PosDef)
      (PosDef.one.smul hpos' : (S'.trace • (1 : Mat d)).PosDef) fun x _ => by
        rw [stableDensity_smul_one hpos, stableDensity_smul_one hpos']
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le htr (by positivity))
          (stableDensity_nonneg hβ0 hβ2 PosDef.one x)
    exact ⟨ρ, hρ, hρid, hρc⟩

theorem continuousOn_stableExp_trace {β : ℝ} (hβ : 0 < β) (ω : Rd d) :
    ContinuousOn (fun S : Mat d => stableExp β (S.trace • (1 : Mat d)) ω) (psdSet d) := by
  have h : ∀ S ∈ psdSet d, stableExp β (S.trace • (1 : Mat d)) ω = S.trace ^ (β / 2) * ‖ω‖ ^ β :=
    fun S hS => stableExp_smul_one (Matrix.PosSemidef.trace_nonneg hS) hβ ω
  refine ContinuousOn.congr ?_ h
  have htc : Continuous fun S : Mat d => S.trace := continuous_id.matrix_trace
  exact (htc.continuousOn.rpow_const fun S _ => Or.inr (by positivity)).mul continuousOn_const

theorem stableLevy_degGauge_mono [NeZero d] {α γ p : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) (hdp : (d : ℝ) * γ + p = 1)
    (hγα : 1 ≤ ((d : ℝ) + α) * γ) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef)
    (hle : loewnerLE S S') : stableLevy α (degGauge γ p S) ≤ stableLevy α (degGauge γ p S') := by
  unfold stableLevy
  refine withDensity_mono ((ae_restrict_iff' (measurableSet_singleton _).compl).2
    (ae_of_all _ fun x hx => ENNReal.ofReal_le_ofReal ?_))
  exact stableDensity_degGauge_mono hα0 hα2 hγ hp0 hp1 hdp hγα hS hS' hle x hx

theorem stableLevy_trace_mono [NeZero d] {β : ℝ} (hβ : 0 < β) {S S' : Mat d} (hS : S.PosDef)
    (hle : loewnerLE S S') :
    stableLevy β (S.trace • (1 : Mat d)) ≤ stableLevy β (S'.trace • (1 : Mat d)) := by
  have hpos : 0 < S.trace := hS.trace_pos
  have htr : S.trace ≤ S'.trace := trace_le_of_loewnerLE hle
  rw [stableLevy_smul_one hpos, stableLevy_smul_one (hpos.trans_le htr)]
  refine Measure.le_iff.2 fun B _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hpos.le htr (by positivity)))
    _

theorem trace_sigmaEps [NeZero d] (ε : ℝ) : (sigmaEps d ε).trace = 1 + ((d : ℝ) - 1) * ε := by
  rw [sigmaEps, trace_diagonal, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d))]
  have h0 : (if ((0 : Fin d) : ℕ) = 0 then (1 : ℝ) else ε) = 1 := by simp
  rw [h0, Finset.sum_congr rfl (g := fun _ => ε) fun i hi => if_neg (fun h =>
    Finset.ne_of_mem_erase hi (Fin.ext_iff.2 (by simp [h]))), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)), Nat.cast_one]

/-- **The exponent spread of `ψ_{h(Σ)} + ψ'_{τI}`** is at least `ecc(h(Σ))^{α/2}` for `β < α`: along
`rv_±` the ratio tends to `(η_+/η_-)^{α/2}` as `r → ∞`. -/
theorem expSpread_stable_add_ge [NeZero d] {α β : ℝ} (_hα0 : 0 < α) (hβ0 : 0 < β) (hβα : β < α)
    {H : Mat d} (hH : H.PosDef) {τ : ℝ} (hτ : 0 ≤ τ) :
    ENNReal.ofReal (ecc H ^ (α / 2)) ≤
      expSpread (fun ω => stableExp α H ω + stableExp β (τ • (1 : Mat d)) ω) := by
  obtain ⟨vp, hvp, hHvp⟩ := exists_unit_eigvec_eigUp hH.isHermitian (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hH.isHermitian] at hHvp
  obtain ⟨vm, hvm, hHvm⟩ := exists_unit_eigvec_eigUp hH.isHermitian 0
  rw [← lamMin_eq_eigUp_zero hH.isHermitian] at hHvm
  set ηp := lamMax H
  set ηm := lamMin H
  have hp0 : 0 < ηp := lamMax_pos hH
  have hm0 : 0 < ηm := lamMin_pos hH
  set R := (ℝ ∙ (vm - vp))ᗮ.reflection with hR
  have hRv : R vm = vp := Submodule.reflection_sub (hvm.trans hvp.symm)
  have hψ : ∀ (v : Rd d) (η : ℝ), ‖v‖ = 1 → lin H v = η • v → 0 ≤ η → ∀ r : ℝ, 0 < r →
      stableExp α H (r • v) + stableExp β (τ • (1 : Mat d)) (r • v) =
        r ^ α * (η ^ (α / 2) + τ ^ (β / 2) * r ^ (β - α)) := by
    intro v η hv hHv hη r hr
    rw [stableExp_smul_one hτ hβ0, stableExp, quad_smul_vec, quad, hHv, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hv, norm_smul, hv, Real.norm_eq_abs, abs_of_pos hr, one_pow,
      mul_one, mul_one, Real.mul_rpow (sq_nonneg r) hη, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      Real.rpow_sub hr]
    have : (((2 : ℕ) : ℝ) * (α / 2)) = α := by push_cast; ring
    rw [this]
    field_simp
  refine le_expSpread fun K hK1 hK => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hKpt : ∀ r : ℝ, 0 < r → ηp ^ (α / 2) + τ ^ (β / 2) * r ^ (β - α) ≤
      K * (ηm ^ (α / 2) + τ ^ (β / 2) * r ^ (β - α)) := by
    intro r hr
    have h := hK (isoMat R) (isoMat_mem_orthSet R) (r • vm)
    rw [lin_isoMat] at h
    change stableExp α H (R (r • vm)) + stableExp β (τ • (1 : Mat d)) (R (r • vm)) ≤
      K * (stableExp α H (r • vm) + stableExp β (τ • (1 : Mat d)) (r • vm)) at h
    rw [map_smul, hRv, hψ vp ηp hvp hHvp hp0.le r hr, hψ vm ηm hvm hHvm hm0.le r hr,
      mul_left_comm] at h
    exact le_of_mul_le_mul_left h (Real.rpow_pos_of_pos hr α)
  have hlim : Tendsto (fun r : ℝ => r ^ (β - α)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (by linarith : 0 < α - β) |>.congr' (by
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [show -(α - β) = β - α by ring])
  have h1 : Tendsto (fun r : ℝ => ηp ^ (α / 2) + τ ^ (β / 2) * r ^ (β - α)) atTop
      (𝓝 (ηp ^ (α / 2))) := by
    simpa using tendsto_const_nhds.add (hlim.const_mul (τ ^ (β / 2)))
  have h2 : Tendsto (fun r : ℝ => K * (ηm ^ (α / 2) + τ ^ (β / 2) * r ^ (β - α))) atTop
      (𝓝 (K * ηm ^ (α / 2))) := by
    simpa using (tendsto_const_nhds.add (hlim.const_mul (τ ^ (β / 2)))).const_mul K
  have hle := le_of_tendsto_of_tendsto h1 h2 ((eventually_gt_atTop 0).mono fun r hr => hKpt r hr)
  rw [ecc, Real.div_rpow hp0.le hm0.le, div_le_iff₀ (Real.rpow_pos_of_pos hm0 _)]
  exact hle

theorem isLevyMeasure_add {L₁ L₂ : Measure (Rd d)} (h₁ : IsLevyMeasure L₁) (h₂ : IsLevyMeasure L₂) :
    IsLevyMeasure (L₁ + L₂) :=
  ⟨by rw [Measure.add_apply, h₁.1, h₂.1, add_zero], by
    rw [lintegral_add_measure]; exact ENNReal.add_ne_top.2 ⟨h₁.2, h₂.2⟩⟩

/-- **The moment matrices along `Σ_ε` converge** when the measures increase with `ε`. -/
theorem tendsto_momentMatrix_of_mono [NeZero d] {L : Mat d → Measure (Rd d)}
    (hLevy : ∀ ε : ℝ, 0 < ε → IsLevyMeasure (L (sigmaEps d ε)))
    (hmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → L (sigmaEps d ε) ≤ L (sigmaEps d ε')) (r : ℝ) :
    ∃ Ms : Mat d, Tendsto (fun ε => momentMatrix r (L (sigmaEps d ε))) (𝓝[>] 0) (𝓝 Ms) ∧
      Ms.IsHermitian ∧ ∀ v : Rd d,
        Tendsto (fun ε => quad (momentMatrix r (L (sigmaEps d ε))) v) (𝓝[>] 0) (𝓝 (quad Ms v)) := by
  set Mε : ℝ → Mat d := fun ε => momentMatrix r (L (sigmaEps d ε)) with hMε
  have hMmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → loewnerLE (Mε ε) (Mε ε') := fun ε ε' hε h =>
    momentMatrix_mono (hLevy ε hε) (hLevy ε' (hε.trans_le h)) (hmono ε ε' hε h) r
  have hq : ∀ v : Rd d, Tendsto (fun ε => quad (Mε ε) v) (𝓝[>] 0)
      (𝓝 (⨅ k : ℕ, quad (Mε (1 / ((k : ℝ) + 1))) v)) := by
    intro v
    refine tendsto_nhdsGT_of_monotone_real' (fun ε hε =>
      quad_nonneg (momentMatrix_posSemidef (hLevy ε hε) r) v) fun ε ε' hε h => ?_
    have := quad_nonneg (hMmono ε ε' hε h) v
    rw [quad_sub] at this
    linarith
  set q : Rd d → ℝ := fun v => ⨅ k : ℕ, quad (Mε (1 / ((k : ℝ) + 1))) v with hqdef
  set Ms : Mat d := Matrix.of fun i j =>
    (q (ebasis i + ebasis j) - q (ebasis i) - q (ebasis j)) / 2 with hMs
  have htend : Tendsto Mε (𝓝[>] 0) (𝓝 Ms) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (((hq (ebasis i + ebasis j)).sub (hq (ebasis i))).sub (hq (ebasis j))).div_const 2
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (entry_eq_polar (momentMatrix_isHermitian r _) i j).symm
  have hMsh : Ms.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hMs, Matrix.transpose_apply, Matrix.of_apply]
    rw [add_comm (ebasis j)]
    ring
  exact ⟨Ms, htend, hMsh, fun v => ((continuous_quad v).tendsto Ms).comp htend⟩

/-- **`θ_s > 0`** for the family with the isotropic part `S'_β(tr(Σ) I)`. -/
theorem degenerate_theta_pos [NeZero d] {α β γ p : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hβ0 : 0 < β)
    (hβ2 : β < 2) (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) (hdp : (d : ℝ) * γ + p = 1)
    (hγα : 1 ≤ ((d : ℝ) + α) * γ) {s : ℝ} (hs : 0 < s) :
    0 < momentTheta (fun S : Mat d =>
      stableLevy α (degGauge γ p S) + stableLevy β (S.trace • (1 : Mat d))) s := by
  set L' : Mat d → Measure (Rd d) := fun S =>
    stableLevy α (degGauge γ p S) + stableLevy β (S.trace • (1 : Mat d)) with hL'
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hLevyPD : ∀ S : Mat d, S.PosDef → IsLevyMeasure (L' S) := fun S hS =>
    isLevyMeasure_add (stableLevy_props hα0 hα2 (degGauge_posDef hS)).1
      (stableLevy_props hβ0 hβ2 (PosDef.one.smul hS.trace_pos)).1
  have hLevy : ∀ ε : ℝ, 0 < ε → IsLevyMeasure (L' (sigmaEps d ε)) := fun ε hε =>
    hLevyPD _ (sigmaEps_posDef hε)
  have hmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → L' (sigmaEps d ε) ≤ L' (sigmaEps d ε') := by
    intro ε ε' hε h
    exact add_le_add (stableLevy_degGauge_mono hα0 hα2 hγ hp0 hp1 hdp hγα (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le h)) (sigmaEps_le h))
      (stableLevy_trace_mono hβ0 (sigmaEps_posDef hε) (sigmaEps_le h))
  obtain ⟨Ms, htend, hMsh, hqM⟩ := tendsto_momentMatrix_of_mono hLevy hmono s
  have hrank : rankOneMoment L' s = Ms := htend.limUnder_eq
  set L₀ := stableLevy β (1 : Mat d) with hL₀
  have hL₀levy := (stableLevy_props (d := d) hβ0 hβ2 PosDef.one).1
  have hL₀ne := stableLevy_one_ne_zero (d := d) hβ0 hβ2
  set T₀ := momentTrace s L₀ with hT₀
  have hT₀pos : 0 < T₀ := momentTrace_pos hL₀levy hL₀ne hs
  have hM₀ : momentMatrix s L₀ = (T₀ / d) • (1 : Mat d) :=
    momentMatrix_rot hL₀levy (stableLevy_one_rotationInvariant β) s
  have hle : ∀ ε : ℝ, 0 < ε → L₀ ≤ L' (sigmaEps d ε) := by
    intro ε hε
    have htr : 1 ≤ (sigmaEps d ε).trace := by
      rw [trace_sigmaEps]
      have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
      nlinarith
    refine le_trans ?_ (Measure.le_add_left le_rfl)
    rw [stableLevy_smul_one (zero_lt_one.trans_le htr), hL₀]
    refine Measure.le_iff.2 fun B _ => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    refine le_mul_of_one_le_left bot_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow htr (by positivity))
  have hlow : ∀ v : Rd d, ‖v‖ = 1 → T₀ / d ≤ quad Ms v := by
    intro v hv
    have h0 : quad (momentMatrix s L₀) v = T₀ / d := by
      rw [hM₀, quad_smul, quad_one, hv, one_pow, mul_one]
    rw [← h0]
    refine ge_of_tendsto (hqM v) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have := quad_nonneg (momentMatrix_mono hL₀levy (hLevy ε hε) (hle ε hε) s) v
    rw [quad_sub] at this
    linarith
  have hlm : T₀ / d ≤ lamMin Ms := (le_lamMin_iff hMsh _).2 hlow
  have hT1 : 0 < momentTrace s (L' 1) := by
    refine momentTrace_pos (hLevyPD 1 PosDef.one) ?_ hs
    intro h0
    have h1 : L₀ ≤ L' 1 := by
      rw [← sigmaEps_one]
      exact hle 1 one_pos
    rw [h0] at h1
    exact hL₀ne (le_antisymm h1 (Measure.zero_le _))
  rw [momentTheta, hrank]
  have : 0 < lamMin Ms := lt_of_lt_of_le (by positivity) hlm
  positivity

theorem momentMatrix_add {L₁ L₂ : Measure (Rd d)} (h₁ : IsLevyMeasure L₁) (h₂ : IsLevyMeasure L₂)
    (r : ℝ) : momentMatrix r (L₁ + L₂) = momentMatrix r L₁ + momentMatrix r L₂ := by
  ext i j
  simp only [momentMatrix, Matrix.of_apply, Matrix.add_apply]
  exact integral_add_measure (integrable_moment_entry h₁ r i j) (integrable_moment_entry h₂ r i j)

/-- `T_s(n'_{τI}) = c_{d,β}^{-1} τ^{β/2} s^{2-β} G₁(β)`. -/
theorem momentTrace_stableLevy_smul_one [NeZero d] {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) {τ : ℝ}
    (hτ : 0 < τ) {s : ℝ} (hs : 0 < s) :
    momentTrace s (stableLevy β (τ • (1 : Mat d))) =
      (stableConst (d := d) β)⁻¹ * (s ^ (2 - β) * τ ^ (β / 2) * degConstG1 d β) := by
  have hH : (τ • (1 : Mat d)).PosDef := PosDef.one.smul hτ
  have hL := (stableLevy_props hβ0 hβ2 hH).1
  have hc : 0 ≤ (stableConst (d := d) β)⁻¹ :=
    inv_nonneg.2 (stableConst_pos_finite (d := d) hβ0 hβ2).2.le
  have hG := (degConst_props (d := d) hβ0 hβ2).2.2
  have hsq : msqrt (τ • (1 : Mat d)) = Real.sqrt τ • (1 : Mat d) := by
    have h1 : (1 : Mat d) * (1 : Mat d)ᵀ = 1 := by simp
    have h := msqrt_udiag h1 (w := fun _ : Fin d => τ) (fun _ => hτ.le)
    rw [udiag_const h1, udiag_const h1] at h
    exact h
  have hof : ENNReal.ofReal (momentTrace s (stableLevy β (τ • (1 : Mat d)))) =
      ENNReal.ofReal ((stableConst (d := d) β)⁻¹ * (s ^ (2 - β) * τ ^ (β / 2) * degConstG1 d β)) := by
    rw [momentTrace, ofReal_integral_eq_lintegral_ofReal (hL.integrable_min_sq s)
      (ae_of_all _ fun x => le_min (sq_nonneg _) (sq_nonneg _)),
      lintegral_stableLevy hβ0 hβ2 hH (by fun_prop) (by simp), hsq]
    have h1 : ∀ y : Rd d, ENNReal.ofReal (min (‖lin (Real.sqrt τ • (1 : Mat d)) y‖ ^ 2) (s ^ 2)) *
        ENNReal.ofReal (‖y‖ ^ (-(d : ℝ) - β)) =
        ENNReal.ofReal (min (τ * ‖y‖ ^ 2) (s ^ 2) * ‖y‖ ^ (-(d : ℝ) - β)) := by
      intro y
      rw [← ENNReal.ofReal_mul (le_min (sq_nonneg _) (sq_nonneg _)), lin_smul, lin_one]
      congr 2
      change min (‖Real.sqrt τ • y‖ ^ 2) (s ^ 2) = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt hτ.le]
    rw [lintegral_congr h1, lintegral_min_dilate hτ hs (φ := fun z : Rd d => ‖z‖ ^ 2)
      (by fun_prop) (fun z => sq_nonneg _)
      (fun t w ht => by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]),
      ← ofReal_integral_eq_lintegral_ofReal hG.1 (ae_of_all _ fun z => by positivity),
      ← degConstG1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
  have hG1 := hG.2
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => le_min (sq_nonneg _)
    (sq_nonneg _)) (mul_nonneg hc (by positivity))).1 hof

/-- **`sup_s cond 𝓜_s(n_H + n'_{τI}) ≥ (G₁/(dG₀)) ecc(H)^{α/2}`** for `β < α`: the ratio of the
Rayleigh quotients tends to `(G₁/(dG₀)) ecc(H)^{α/2}` as `s ↓ 0`. -/
theorem iSup_condNum_stable_add_ge [NeZero d] {α β : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hβ0 : 0 < β) (hβα : β < α) {H : Mat d} (hH : H.PosDef) {τ : ℝ} (hτ : 0 < τ) :
    ENNReal.ofReal (degConstG1 d α / (d * degConstG0 (d := d) α) * ecc H ^ (α / 2)) ≤
      ⨆ s : Ioi (0 : ℝ), condNum (momentMatrix s
        (stableLevy α H + stableLevy β (τ • (1 : Mat d)))) := by
  have hβ2 : β < 2 := hβα.trans hα2
  obtain ⟨vp, hvp, hHvp⟩ := exists_unit_eigvec_eigUp hH.isHermitian (Fin.rev 0)
  rw [← lamMax_eq_eigUp_last hH.isHermitian] at hHvp
  obtain ⟨vm, hvm, hHvm⟩ := exists_unit_eigvec_eigUp hH.isHermitian 0
  rw [← lamMin_eq_eigUp_zero hH.isHermitian] at hHvm
  set ηp := lamMax H with hηp
  set ηm := lamMin H with hηm
  have hp0 : 0 < ηp := lamMax_pos hH
  have hm0 : 0 < ηm := lamMin_pos hH
  obtain ⟨-, hG0, -, hG1⟩ := degConst_props (d := d) hα0 hα2
  have hG1β := (degConst_props (d := d) hβ0 hβ2).2.2.2
  have hca : 0 < (stableConst (d := d) α)⁻¹ := inv_pos.2 (stableConst_pos_finite (d := d) hα0 hα2).2
  have hcb : 0 < (stableConst (d := d) β)⁻¹ := inv_pos.2 (stableConst_pos_finite (d := d) hβ0 hβ2).2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hLa := (stableLevy_props hα0 hα2 hH).1
  have hLb := (stableLevy_props hβ0 hβ2 (PosDef.one.smul hτ : (τ • (1 : Mat d)).PosDef)).1
  set A' := (stableConst (d := d) α)⁻¹ * (1 / d * (ηp ^ (α / 2) * degConstG1 d α)) with hA'
  set B' := (stableConst (d := d) α)⁻¹ * (ηm ^ (α / 2) * degConstG0 (d := d) α) with hB'
  set C' := (stableConst (d := d) β)⁻¹ * (τ ^ (β / 2) * degConstG1 d β) with hC'
  have hA'0 : 0 < A' := by positivity
  have hB'0 : 0 < B' := by positivity
  have hC'0 : 0 < C' := by positivity
  have hratio : ∀ s : ℝ, 0 < s → ENNReal.ofReal (A' / (B' + C' * s ^ (α - β))) ≤
      condNum (momentMatrix s (stableLevy α H + stableLevy β (τ • (1 : Mat d)))) := by
    intro s hs
    set Ma := momentMatrix s (stableLevy α H)
    set Mb := momentMatrix s (stableLevy β (τ • (1 : Mat d)))
    have hM : momentMatrix s (stableLevy α H + stableLevy β (τ • (1 : Mat d))) = Ma + Mb :=
      momentMatrix_add hLa hLb s
    have hMa := momentMatrix_posSemidef hLa s
    have hMb := momentMatrix_posSemidef hLb s
    have hMpsd : (Ma + Mb).PosSemidef := hMa.add hMb
    have hs2 : 0 < s ^ (2 - α) := Real.rpow_pos_of_pos hs _
    have hup := ofReal_quad_moment_stable_le hα0 hα2 hH hvm hHvm hs
    have hlo := ofReal_quad_moment_stable_ge hα0 hα2 hH hvp hHvp
      (fun y => quad_le_lamMax_mul hH.isHermitian y) hs
    have hb : quad Ma vm ≤ B' * s ^ (2 - α) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hca.le] at hup
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
      rw [hB']
      linarith [show (stableConst (d := d) α)⁻¹ * (s ^ (2 - α) * ηm ^ (α / 2) *
        degConstG0 (d := d) α) = (stableConst (d := d) α)⁻¹ * (ηm ^ (α / 2) *
          degConstG0 (d := d) α) * s ^ (2 - α) by ring]
    have ha : A' * s ^ (2 - α) ≤ quad Ma vp := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hca.le] at hlo
      have := (ENNReal.ofReal_le_ofReal_iff (quad_nonneg hMa _)).1 hlo
      rw [hA']
      linarith [show (stableConst (d := d) α)⁻¹ * (1 / d * (s ^ (2 - α) * ηp ^ (α / 2) *
        degConstG1 d α)) = (stableConst (d := d) α)⁻¹ * (1 / d * (ηp ^ (α / 2) *
          degConstG1 d α)) * s ^ (2 - α) by ring]
    have hc : quad Mb vm ≤ C' * s ^ (α - β) * s ^ (2 - α) := by
      have h1 : quad Mb vm ≤ momentTrace s (stableLevy β (τ • (1 : Mat d))) := by
        rw [quad_momentMatrix hLb, momentTrace]
        refine integral_mono (integrable_moment_quad hLb s vm) (hLb.integrable_min_sq s) fun x => ?_
        rcases (norm_nonneg x).eq_or_lt with h0 | hpos
        · rw [← h0]; simp [sq_nonneg]
        have hin : ⟪vm, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
          have := abs_real_inner_le_norm vm x
          rw [hvm, one_mul] at this
          exact sq_le_sq' (by linarith [neg_abs_le ⟪vm, x⟫]) (le_trans (le_abs_self _) this)
        rw [mul_div_assoc]
        exact mul_le_of_le_one_right (le_min (sq_nonneg _) (sq_nonneg _))
          ((div_le_one (by positivity)).2 hin)
      rw [momentTrace_stableLevy_smul_one hβ0 hβ2 hτ hs] at h1
      calc quad Mb vm ≤ _ := h1
        _ = C' * s ^ (α - β) * s ^ (2 - α) := by
            rw [hC', mul_assoc C', ← Real.rpow_add hs, show α - β + (2 - α) = 2 - β by ring]
            ring
    unfold condNum
    rw [hM]
    split_ifs with h0
    · exact le_top
    · have hmin : 0 < lamMin (Ma + Mb) := lt_of_le_of_ne (lamMin_nonneg hMpsd) (Ne.symm h0)
      have hlm : lamMin (Ma + Mb) ≤ quad (Ma + Mb) vm := lamMin_le_inner hMpsd.isHermitian hvm
      have hlM : quad (Ma + Mb) vp ≤ lamMax (Ma + Mb) := quad_le_lamMax hMpsd.isHermitian hvp
      have hqp : A' * s ^ (2 - α) ≤ quad (Ma + Mb) vp := by
        rw [quad_add]; linarith [quad_nonneg hMb vp]
      have hqm : quad (Ma + Mb) vm ≤ (B' + C' * s ^ (α - β)) * s ^ (2 - α) := by
        rw [quad_add]; nlinarith
      refine ENNReal.ofReal_le_ofReal ?_
      have hden : 0 < B' + C' * s ^ (α - β) := by positivity
      calc A' / (B' + C' * s ^ (α - β)) = (A' * s ^ (2 - α)) / ((B' + C' * s ^ (α - β)) *
            s ^ (2 - α)) := by field_simp
        _ ≤ lamMax (Ma + Mb) / lamMin (Ma + Mb) :=
            div_le_div₀ ((by positivity : 0 ≤ A' * s ^ (2 - α)).trans (hqp.trans hlM))
              (hqp.trans hlM) hmin (hlm.trans hqm)
  have hlim : Tendsto (fun s : ℝ => A' / (B' + C' * s ^ (α - β))) (𝓝[>] 0) (𝓝 (A' / B')) := by
    have hcont : ContinuousAt (fun s : ℝ => A' / (B' + C' * s ^ (α - β))) 0 := by
      refine continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul
        (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))))) ?_
      rw [Real.zero_rpow (by linarith), mul_zero, add_zero]
      exact hB'0.ne'
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Real.zero_rpow (by linarith : α - β ≠ 0)] using h
  have heq : degConstG1 d α / (d * degConstG0 (d := d) α) * ecc H ^ (α / 2) = A' / B' := by
    rw [ecc, ← hηp, ← hηm, Real.div_rpow hp0.le hm0.le, hA', hB']
    have h1 : 0 < ηm ^ (α / 2) := Real.rpow_pos_of_pos hm0 _
    have h3 : stableConst (d := d) α ≠ 0 := (stableConst_pos_finite (d := d) hα0 hα2).2.ne'
    field_simp
  rw [heq]
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hratio s hs).trans (le_iSup_of_le (⟨s, hs⟩ : Ioi (0 : ℝ)) le_rfl)

/-- **`prop:similarity-degenerate-family`(3)**, a nonzero rotation-invariant rank-one limit is not
enough: for `0 < β < α`, `μ'_Σ := μ_Σ * S'_β(tr(Σ) I)` with `L'_Σ = (n_{h(Σ)} + n'_{tr(Σ)I}) dx`
has the properties of (1); its rank-one limit is `L'_* = n'_I dx`, nonzero and rotation invariant;
`θ_s > 0` for every `s > 0`; and `es(ψ'_Σ) ≥ ecc(Σ)^{pα/2}`,
`sup_s cond 𝓜_s(L'_Σ) ≥ (G₁/(dG₀)) ecc(Σ)^{pα/2}` for every `Σ ∈ PD(d)`. Spends A3(iii). -/
theorem degenerate_rotation_invariant_limit [NeZero d] (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) (γ : ℝ) (hγ1 : 1 / ((d : ℝ) + α) ≤ γ) (hγ2 : γ < 1 / (d : ℝ)) (b : ℝ)
    (hb : 0 ≤ b) (σ : Mat d → Measure (Rd d))
    (hσ : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable α (degGauge γ (1 - d * γ) S) (σ S))
    {β : ℝ} (hβ0 : 0 < β) (hβα : β < α) (σ' : Mat d → Measure (Rd d))
    (hσ' : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable β (S.trace • (1 : Mat d)) (σ' S)) :
    let p : ℝ := 1 - d * γ
    let μ' : Mat d → Measure (Rd d) := fun S =>
      (multivariateGaussian 0 ((2 * b) • S) ∗ σ S) ∗ σ' S
    let L' : Mat d → Measure (Rd d) := fun S =>
      stableLevy α (degGauge γ p S) + stableLevy β (S.trace • (1 : Mat d))
    (∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' → L' S ≤ L' S') ∧
      (∃ ρ : Mat d → Mat d → Measure (Rd d),
        (∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
          IsProbabilityMeasure (ρ S S') ∧ IsInfinitelyDivisible (ρ S S') ∧
          μ' S' = μ' S ∗ ρ S S') ∧
        IsGWCascadeFamily (simSet d) loewnerLE ρ) ∧
      IsRankOneLimit L' (stableLevy β 1) ∧ stableLevy β (1 : Mat d) ≠ 0 ∧
      IsRotationInvariant (stableLevy β (1 : Mat d)) ∧
      (∀ s : ℝ, 0 < s → 0 < momentTheta L' s) ∧
      ∀ S : Mat d, S.PosDef →
        ENNReal.ofReal (ecc S ^ (p * α / 2)) ≤
          expSpread (fun ω => stableExp α (degGauge γ p S) ω +
            stableExp β (S.trace • (1 : Mat d)) ω) ∧
        ENNReal.ofReal (degConstG1 d α / (d * degConstG0 (d := d) α) * ecc S ^ (p * α / 2)) ≤
          ⨆ s : Ioi (0 : ℝ), condNum (momentMatrix s (L' S)) := by
  intro p μ' L'
  obtain ⟨hγ0, hp0, -, hp1, hdp, hγα⟩ := degenerate_params hα0 hγ1 hγ2
  have hβ2 : β < 2 := hβα.trans hα2
  have hσa : ∀ S : Mat d, S.PosSemidef → IsEllipticalStable α (degGauge γ p S) (σ S) := hσ
  have hpow : ∀ S : Mat d, S.PosDef → ecc (degGauge γ p S) ^ (α / 2) = ecc S ^ (p * α / 2) := by
    intro S hS
    have hecc0 : 0 ≤ ecc S := div_nonneg (lamMax_pos hS).le (lamMin_pos hS).le
    rw [ecc_degGauge hp0 hS, ← Real.rpow_mul hecc0]
    congr 1
    ring
  refine ⟨fun S S' hS hS' hle => add_le_add (stableLevy_degGauge_mono hα0 hα2 hγ0 hp0 hp1 hdp hγα
    hS hS' hle) (stableLevy_trace_mono hβ0 hS hle), ?_, ?_, stableLevy_one_ne_zero hβ0 hβ2,
    stableLevy_one_rotationInvariant β,
    fun s hs => degenerate_theta_pos hα0 hα2 hβ0 hβ2 hγ0 hp0 hp1 hdp hγα hs,
    fun S hS => ⟨?_, ?_⟩⟩
  · /- the cascade -/
    set Φ : Mat d → Rd d → ℝ := fun S ω => b * quad S ω + stableExp α (degGauge γ p S) ω +
      stableExp β (S.trace • (1 : Mat d)) ω with hΦ
    refine simCascade_of_exponent Φ (fun ω => ?_) ?_ ?_ ?_ μ' fun S hS => ?_
    · exact (((continuous_const.mul (continuous_quad ω)).continuousOn).add
        (continuousOn_stableExp_degGauge hα0 hγ0 hp0 hp1 ω)).add
        (continuousOn_stableExp_trace hβ0 ω)
    · rintro A hA S hS ω
      obtain ⟨c, hc, Q, hQ, rfl⟩ := hA
      simp only [hΦ]
      rw [← trace_act_simSet ⟨c, hc, Q, hQ, rfl⟩ S, stableExp_act, quad_act, act_smul_left,
        degGauge_smul_conj hdp hS (pow_pos hc 2) hQ, ← act_smul_left, stableExp_act]
    · refine ⟨ebasis 0, ?_⟩
      have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
      simp only [hΦ, quad_zero, mul_zero, degGauge_zero hγ0, stableExp_zero_mat hα0, add_zero,
        degGauge_one, trace_zero, zero_smul, stableExp_zero_mat hβ0]
      rw [stableExp, quad_one, he, one_pow, Real.one_rpow,
        stableExp_smul_one (PosSemidef.one.trace_nonneg : (0 : ℝ) ≤ (1 : Mat d).trace) hβ0, he,
        Real.one_rpow,
        mul_one]
      have : 0 ≤ b * quad 1 (ebasis (0 : Fin d)) := mul_nonneg hb (quad_nonneg PosSemidef.one _)
      have : 0 ≤ (1 : Mat d).trace ^ (β / 2) :=
        Real.rpow_nonneg (PosSemidef.one.trace_nonneg) _
      linarith
    · intro S S' hS hS' hle
      have hG : ((2 * b) • (S' - S)).PosSemidef := hle.smul (by positivity)
      obtain ⟨τa, hτa, hτaid, hτac⟩ := exists_degGauge_increment hα0 hα2 hγ0 hp0 hp1 hdp hγα
        hS hS' hle
      obtain ⟨τb, hτb, hτbid, hτbc⟩ := exists_trace_increment hβ0 hβ2 hS hle
      refine ⟨(multivariateGaussian 0 ((2 * b) • (S' - S)) ∗ τa) ∗ τb, inferInstance,
        ((isInfinitelyDivisible_gaussian hG).conv hτaid).conv hτbid, fun ω => ?_⟩
      rw [charFun_conv, charFun_conv, charFun_multivariateGaussian_zero hG, hτac, hτbc,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [hΦ, quad_smul, quad_sub]
      ring
    · haveI := (hσa S hS).1
      haveI := (hσ' S hS).1
      refine ⟨inferInstance, fun ω => ?_⟩
      show charFun ((multivariateGaussian 0 ((2 * b) • S) ∗ σ S) ∗ σ' S) ω = _
      rw [charFun_conv, charFun_conv, charFun_multivariateGaussian_zero (hS.smul (by positivity)),
        (hσa S hS).2, (hσ' S hS).2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add,
        ← Real.exp_add]
      congr 2
      simp only [hΦ, quad_smul]
      ring
  · /- the rank-one limit -/
    have hL0 := (stableLevy_props (d := d) hβ0 hβ2 PosDef.one).1
    refine ⟨hL0.1, fun B hB hBa => ?_⟩
    have h1 := (degenerate_rankOne_zero hd hα0 hα2 hγ0 hp0 hp1 hdp hγα).2 B hB hBa
    obtain ⟨n, hn⟩ := hBa.exists_subset
    have hfin : stableLevy β (1 : Mat d) B ≠ ⊤ :=
      ne_top_of_le_ne_top (hL0.awaySet_ne_top n) (measure_mono hn)
    have htr : Tendsto (fun ε => (sigmaEps d ε).trace) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous fun ε : ℝ => (sigmaEps d ε).trace := by
        simp_rw [trace_sigmaEps]
        fun_prop
      have h := hc.tendsto 0
      rw [trace_sigmaEps, mul_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε => stableLevy β ((sigmaEps d ε).trace • (1 : Mat d)) B) (𝓝[>] 0)
        (𝓝 (stableLevy β (1 : Mat d) B)) := by
      have hpow : Tendsto (fun ε => ENNReal.ofReal ((sigmaEps d ε).trace ^ (β / 2))) (𝓝[>] 0)
          (𝓝 1) := by
        have := ENNReal.tendsto_ofReal (((Real.continuousAt_rpow_const 1 (β / 2)
          (Or.inl one_ne_zero)).tendsto).comp htr)
        simpa using this
      have h := ENNReal.Tendsto.mul_const hpow (Or.inr hfin)
      rw [one_mul] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have htrpos : 0 < (sigmaEps d ε).trace := (sigmaEps_posDef hε).trace_pos
      rw [stableLevy_smul_one htrpos, Measure.smul_apply, smul_eq_mul]
    have h := h1.add h2
    simp only [Measure.coe_zero, Pi.zero_apply, zero_add] at h
    simpa only [L', Measure.add_apply] using h
  · /- the exponent spread -/
    rw [← hpow S hS]
    exact expSpread_stable_add_ge hα0 hβ0 hβα (degGauge_posDef hS) hS.posSemidef.trace_nonneg
  · /- the moments -/
    rw [← hpow S hS]
    exact iSup_condNum_stable_add_ge hα0 hα2 hβ0 hβα (degGauge_posDef hS) hS.trace_pos

end AffineHemigroup
