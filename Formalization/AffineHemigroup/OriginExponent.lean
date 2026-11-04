/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Polar
import ScaleSpaceCore.Cin

/-!
# The exponent `F_d` of an isotropic origin datum: its sphere form, radiality and finiteness

Blueprint: `blueprint/src/parts/03-isotropic.tex`, the opening of the proofs of
`lem:isotropic-exponent-log` and `thm:origin-boundedness-d`(1): with `a = 0`,
`F_d(ξ) = |S^{d-1}|⁻¹ ∫_{S^{d-1}} φ(⟨ξ, η⟩) σ_{d-1}(dη)` with
`φ(s) = ∫_0^∞ (1 - cos(rs)) k_d(r) dr/r` (`cosProfileL`), through `lem:polar-decomposition`.
Wave 2, group A (Q-0281).

Here: the sphere form (`OriginDatum.exponentL_eq_sphere`), the radiality of `F_d`
(`OriginDatum.exponentL_eq_of_norm_eq`: Lebesgue measure and the radial density of `ν_d` are
invariant under the reflection taking `ξ` to `ξ'`), the two bounds on `φ` read in the blueprint's
proofs (`k_d ≤ c` on `(0,1]` and `1 - cos ≤ 2` beyond, and `k_d ≥ β` near the origin), the bounds
`log X - 3 ≤ Cin(X)` and `Cin(X) ≤ log X + 13/4` (`eq:cin-log`), and the finiteness of `F_d`
(`OriginDatum.exponentL_ne_top`), which the real-valued exponent `F_d = (F_d)_{ℝ≥0∞}.toReal` reads.
`Cin` is the shared library's `ScaleSpace.cin` ([B, Lem. 3.1]; Lean core).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ScaleSpace
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## `Cin`: the bounds `eq:cin-log` -/

theorem one_le_of_mem_uIcc {X v : ℝ} (hX : 1 ≤ X) (hv : v ∈ uIcc (1 : ℝ) X) : 1 ≤ v := by
  rw [uIcc_of_le hX] at hv; exact hv.1

theorem intervalIntegrable_inv_sq {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun v : ℝ => (v ^ 2)⁻¹) volume 1 X := by
  refine ContinuousOn.intervalIntegrable ((continuous_pow 2).continuousOn.inv₀ fun v hv => ?_)
  have := one_le_of_mem_uIcc hX hv
  positivity

theorem intervalIntegrable_sin_div_sq {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun v : ℝ => Real.sin v / v ^ 2) volume 1 X := by
  refine ContinuousOn.intervalIntegrable
    (Real.continuous_sin.continuousOn.div (continuous_pow 2).continuousOn fun v hv => ?_)
  have := one_le_of_mem_uIcc hX hv
  positivity

theorem integral_inv_sq_eq {X : ℝ} (hX : 1 ≤ X) : (∫ v in (1 : ℝ)..X, (v ^ 2)⁻¹) = 1 - X⁻¹ := by
  have hderiv : ∀ x ∈ uIcc (1 : ℝ) X, HasDerivAt (fun v : ℝ => -v⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have := one_le_of_mem_uIcc hX hx; positivity
    have h := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_inv_sq hX)]
  simp only [inv_one]
  ring

theorem abs_integral_sin_div_sq_le {X : ℝ} (hX : 1 ≤ X) :
    |∫ v in (1 : ℝ)..X, Real.sin v / v ^ 2| ≤ 1 - X⁻¹ := by
  rw [← integral_inv_sq_eq hX]
  refine (intervalIntegral.abs_integral_le_integral_abs hX).trans ?_
  refine intervalIntegral.integral_mono_on hX (intervalIntegrable_sin_div_sq hX).abs
    (intervalIntegrable_inv_sq hX) fun v hv => ?_
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv.1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2), div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one v)

/-- `Cin(X) ≤ log X + 13/4` for `X ≥ 1` (`eq:cin-log`, upper bound). Mathlib types and Paper V's
`cin` only. -/
theorem cin_le_log_add {X : ℝ} (hX : 1 ≤ X) : cin X ≤ Real.log X + 13 / 4 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have h1 : cin 1 ≤ 1 / 4 := by simpa using cin_le_sq (1 : ℝ)
  have hJ := abs_integral_sin_div_sq_le hX
  have hJ' := neg_abs_le (∫ v in (1 : ℝ)..X, Real.sin v / v ^ 2)
  have hsinX : -(Real.sin X / X) ≤ X⁻¹ := by
    rw [← neg_div, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_pos.mpr hX0).le (by linarith [Real.neg_one_le_sin X])
  have hsin1 : Real.sin 1 ≤ 1 := Real.sin_le_one 1
  rw [cin_eq_log_sub hX, integral_cos_div hX]
  linarith

/-- `log X - 3 ≤ Cin(X)` for `X > 0` (`eq:cin-log`, lower bound). Mathlib types and Paper V's
`cin` only. -/
theorem log_sub_le_cin {X : ℝ} (hX : 0 < X) : Real.log X - 3 ≤ cin X := by
  rcases lt_or_ge X 1 with h | h
  · have : Real.log X < 0 := Real.log_neg hX h
    linarith [cin_nonneg hX.le]
  · have h1 : 0 ≤ cin 1 := cin_nonneg zero_le_one
    have hJ := abs_integral_sin_div_sq_le h
    have hJ' := le_abs_self (∫ v in (1 : ℝ)..X, Real.sin v / v ^ 2)
    have hsinX : Real.sin X / X ≤ X⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_pos.mpr hX).le (Real.sin_le_one X)
    have hsin1 : -1 ≤ Real.sin 1 := Real.neg_one_le_sin 1
    rw [cin_eq_log_sub h, integral_cos_div h]
    linarith

/-- `∫_{(0,τ]} (1 - cos(rs)) dr/r = Cin(sτ)` for `τ ≥ 0`, as a lower integral. -/
theorem lintegral_cos_div_eq_cin (s : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ r in Ioc (0 : ℝ) τ, ENNReal.ofReal ((1 - Real.cos (r * s)) / r) = ENNReal.ofReal (cin (s * τ)) := by
  have hint := intervalIntegrable_dilate_cinIntegrand s hτ
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ] at hint
  have hcongr : ∀ r : ℝ, (1 - Real.cos (r * s)) / r = (1 - Real.cos (s * r)) / r := fun r => by
    rw [mul_comm]
  simp_rw [hcongr]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (.of_forall fun r hr => dilate_cinIntegrand_nonneg s hr.1.le)),
    ← intervalIntegral.integral_of_le hτ, intervalIntegral_dilate_cinIntegrand]

/-! ## The cosine profile `φ(s) = ∫_0^∞ (1 - cos(rs)) k(r) dr/r` -/

/-- **The cosine profile** `φ_k(s) = ∫_0^∞ (1 - cos(rs)) k(r) dr/r`, `ℝ≥0∞`-valued. -/
noncomputable def cosProfileL (k : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (1 - Real.cos (r * s)) * ENNReal.ofReal (k r / r)

/-- `φ` is even. -/
theorem cosProfileL_neg (k : ℝ → ℝ) (s : ℝ) : cosProfileL k (-s) = cosProfileL k s := by
  simp [cosProfileL, mul_neg, Real.cos_neg]

/-- **The sphere form of the exponent** (the opening of the proofs of `lem:isotropic-exponent-log`
and `thm:origin-boundedness-d`(1)): `F_d(ξ) = ½a|ξ|² + |S^{d-1}|⁻¹ ∫_{S^{d-1}} φ(⟨ξ,η⟩) dσ`. -/
theorem OriginDatum.exponentL_eq_sphere (hd : 1 ≤ d) (D : OriginDatum d) (ξ : Rd d) :
    D.exponentL ξ = ENNReal.ofReal (D.a * ‖ξ‖ ^ 2 / 2) + (ENNReal.ofReal (sphereArea d))⁻¹ *
      ∫⁻ η : sphere (0 : Rd d) 1, cosProfileL D.k ⟪ξ, (η : Rd d)⟫
        ∂((volume : Measure (Rd d)).toSphere) := by
  rw [OriginDatum.exponentL, D.polar_decomposition hd (fun x => ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫))
    (by fun_prop) (by simp)]
  congr 2
  refine lintegral_congr fun η => ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [inner_smul_right]

/-- The radial density of `ν_d` is invariant under a linear isometry. -/
theorem OriginDatum.levyDensity_isometry (D : OriginDatum d) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (x : Rd d) :
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) (Q x)
    = ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hQx : Q x ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
    rw [indicator_of_mem (show Q x ∈ ({0}ᶜ : Set (Rd d)) from hQx),
      indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx), LinearIsometryEquiv.norm_map]

/-- **`F_d` is invariant under linear isometries**: `F_d(Qξ) = F_d(ξ)`. -/
theorem OriginDatum.exponentL_isometry (D : OriginDatum d) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (ξ : Rd d) :
    D.exponentL (Q ξ) = D.exponentL ξ := by
  rw [OriginDatum.exponentL, OriginDatum.exponentL, LinearIsometryEquiv.norm_map]
  congr 1
  have hinner : ∀ x : Rd d, ⟪Q ξ, x⟫ = ⟪ξ, Q.symm x⟫ := fun x => by
    conv_lhs => rw [← Q.apply_symm_apply x]
    exact Q.inner_map_map ξ (Q.symm x)
  simp_rw [hinner]
  have hf : Measurable fun y : Rd d => ENNReal.ofReal (1 - Real.cos ⟪ξ, y⟫) := by fun_prop
  have hf' : Measurable fun x => ENNReal.ofReal (1 - Real.cos ⟪ξ, Q.symm x⟫) :=
    hf.comp Q.symm.continuous.measurable
  rw [OriginDatum.levyMeasure, lintegral_withDensity_eq_lintegral_mul _ D.measurable_levyDensity hf',
    lintegral_withDensity_eq_lintegral_mul _ D.measurable_levyDensity hf]
  have h := (Q.symm.measurePreserving).lintegral_comp_emb Q.symm.toHomeomorph.measurableEmbedding
    (fun y => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) y *
        ENNReal.ofReal (1 - Real.cos ⟪ξ, y⟫))
  simp only [Pi.mul_apply]
  rw [← h]
  refine lintegral_congr fun x => ?_
  rw [D.levyDensity_isometry Q.symm x]

/-- **`F_d` is radial**: `F_d(ξ) = F_d(ξ')` when `|ξ| = |ξ'|`, through the reflection in
`(ξ - ξ')^⊥`. -/
theorem OriginDatum.exponentL_eq_of_norm_eq (D : OriginDatum d) {ξ ξ' : Rd d} (h : ‖ξ‖ = ‖ξ'‖) :
    D.exponentL ξ = D.exponentL ξ' := by
  have := D.exponentL_isometry (Submodule.reflection (ℝ ∙ (ξ - ξ'))ᗮ) ξ
  rwa [Submodule.reflection_sub h, eq_comm] at this

theorem OriginDatum.exponent_eq_of_norm_eq (D : OriginDatum d) {ξ ξ' : Rd d} (h : ‖ξ‖ = ‖ξ'‖) :
    D.exponent ξ = D.exponent ξ' := by
  rw [OriginDatum.exponent, OriginDatum.exponent, D.exponentL_eq_of_norm_eq h]

/-! ## Bounds on the cosine profile -/

/-- `k_d(r) ≤ c` for `r > 0`, as `ℝ≥0∞`. -/
theorem OriginDatum.ofReal_k_le (D : OriginDatum d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (D.k r) ≤ D.profileAtOrigin :=
  le_iSup (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (D.k r)) ⟨r, hr⟩

/-- Below `c`, near the origin: if `β < c` there is `r_β ∈ (0, 1]` with `k_d ≥ β` on `(0, r_β)`. -/
theorem OriginDatum.exists_le_k (D : OriginDatum d) {β : ℝ}
    (hβ : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ rβ ∈ Ioc (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) rβ, β ≤ D.k r := by
  obtain ⟨⟨r₀, hr₀⟩, hlt⟩ := lt_iSup_iff.mp hβ
  have hβk : β < D.k r₀ := by
    by_contra hcon
    push Not at hcon
    exact absurd hlt (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
  refine ⟨min r₀ 1, ⟨lt_min hr₀ one_pos, min_le_right _ _⟩, fun r hr => ?_⟩
  have hrr₀ : r ≤ r₀ := le_trans hr.2.le (min_le_left _ _)
  exact le_trans hβk.le (D.k_antitone hr.1 hr₀ hrr₀)

/-- **The upper bound** of the proof of `lem:isotropic-exponent-log`(1): split at `r = 1`; on
`(0,1]` use `k_d ≤ c`, beyond it `1 - cos ≤ 2`: `φ(s) ≤ c Cin(s) + 2 C_k`. -/
theorem OriginDatum.cosProfileL_le_cin (D : OriginDatum d) (s : ℝ) :
    cosProfileL D.k s ≤ D.profileAtOrigin * ENNReal.ofReal (cin s) +
      2 * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r) := by
  rw [cosProfileL, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  gcongr
  · calc ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.cos (r * s)) * ENNReal.ofReal (D.k r / r)
        ≤ ∫⁻ r in Ioc (0 : ℝ) 1, D.profileAtOrigin * ENNReal.ofReal ((1 - Real.cos (r * s)) / r) := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          have hk := D.k_nonneg r hr.1
          have h1 : 0 ≤ 1 - Real.cos (r * s) := by linarith [Real.cos_le_one (r * s)]
          rw [← ENNReal.ofReal_mul h1, show (1 - Real.cos (r * s)) * (D.k r / r)
              = D.k r * ((1 - Real.cos (r * s)) / r) by ring, ENNReal.ofReal_mul hk]
          gcongr
          exact D.ofReal_k_le hr.1
      _ = D.profileAtOrigin * ENNReal.ofReal (cin s) := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_cos_div_eq_cin s zero_le_one, mul_one]
  · rw [← lintegral_const_mul' _ _ (by simp)]
    refine setLIntegral_mono' measurableSet_Ioi fun r _ => ?_
    gcongr
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.neg_one_le_cos (r * s)])

/-- **The lower bound** of the proof of `thm:origin-boundedness-d`(1): if `k_d ≥ β` on `(0, r_β)`,
discarding `(r_β, ∞)` leaves `φ(s) ≥ β Cin(s r_β)`. -/
theorem cosProfileL_ge {k : ℝ → ℝ} {β rβ : ℝ} (hrβ : 0 < rβ) (hk : ∀ r ∈ Ioo (0 : ℝ) rβ, β ≤ k r)
    (s : ℝ) : ENNReal.ofReal β * ENNReal.ofReal (cin (s * rβ)) ≤ cosProfileL k s := by
  have hIoo : ∫⁻ r in Ioo (0 : ℝ) rβ, ENNReal.ofReal ((1 - Real.cos (r * s)) / r)
      = ENNReal.ofReal (cin (s * rβ)) := by
    rw [← lintegral_cos_div_eq_cin s hrβ.le]
    exact setLIntegral_congr Ioo_ae_eq_Ioc
  rw [← hIoo, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold cosProfileL
  refine le_trans ?_ (lintegral_mono_set (fun x hx => hx.1 : Ioo (0 : ℝ) rβ ⊆ Ioi 0))
  refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
  have h1 : 0 ≤ 1 - Real.cos (r * s) := by linarith [Real.cos_le_one (r * s)]
  have hβ : ENNReal.ofReal β ≤ ENNReal.ofReal (k r) := ENNReal.ofReal_le_ofReal (hk r hr)
  calc ENNReal.ofReal β * ENNReal.ofReal ((1 - Real.cos (r * s)) / r)
      ≤ ENNReal.ofReal (k r) * ENNReal.ofReal ((1 - Real.cos (r * s)) / r) := by gcongr
    _ = ENNReal.ofReal (1 - Real.cos (r * s)) * ENNReal.ofReal (k r / r) := by
        rcases le_or_gt 0 (k r) with hkr | hkr
        · rw [← ENNReal.ofReal_mul hkr, ← ENNReal.ofReal_mul h1]
          congr 1; ring
        · rw [ENNReal.ofReal_of_nonpos hkr.le, zero_mul,
            ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hkr.le hr.1.le), mul_zero]

/-- **The quadratic bound** behind the finiteness of `F_d`: `1 - cos(rs) ≤ r²s²/2` on `(0,1)`,
`≤ 2` on `[1,∞)`, so `φ(s) ≤ (s²/2) ∫₀¹ k_d(r) r dr + 2 ∫₁^∞ k_d(r) dr/r`. -/
theorem cosProfileL_le_sq (k : ℝ → ℝ) (hk : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r) (s : ℝ) :
    cosProfileL k s ≤ ENNReal.ofReal (s ^ 2 / 2) * (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (k r * r)) +
      2 * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) := by
  rw [cosProfileL, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_lt.mpr hx'))]
  gcongr ?_ + ?_
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
    have hkr := hk r hr.1
    have h1 : 0 ≤ 1 - Real.cos (r * s) := by linarith [Real.cos_le_one (r * s)]
    have h2 : 1 - Real.cos (r * s) ≤ (r * s) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := r * s)]
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr0 : 0 < r := hr.1
    calc (1 - Real.cos (r * s)) * (k r / r) ≤ (r * s) ^ 2 / 2 * (k r / r) := by
          gcongr
      _ = s ^ 2 / 2 * (k r * r) := by field_simp
  · rw [← lintegral_const_mul' _ _ (by simp), Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    refine setLIntegral_mono' measurableSet_Ioi fun r _ => ?_
    gcongr
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.neg_one_le_cos (r * s)])

/-- `|S^{d-1}|⁻¹ σ_{d-1}(S^{d-1}) = 1`: the normalized surface measure has mass `1`. -/
theorem inv_sphereArea_mul_toSphere_univ (hd : 1 ≤ d) :
    (ENNReal.ofReal (sphereArea d))⁻¹ * (volume : Measure (Rd d)).toSphere univ = 1 := by
  rw [← (sphereArea_eq_toSphere hd).1]
  exact ENNReal.inv_mul_cancel (by simp [(sphereArea_eq_toSphere hd).2]) ENNReal.ofReal_ne_top

/-- **`F_d` is finite** at every `ξ`, by `cosProfileL_le_sq`, `|⟨ξ,η⟩| ≤ |ξ|` on the sphere and the
finiteness of `σ_{d-1}`. -/
theorem OriginDatum.exponentL_ne_top (hd : 1 ≤ d) (D : OriginDatum d) (ξ : Rd d) :
    D.exponentL ξ ≠ ⊤ := by
  rw [D.exponentL_eq_sphere hd]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simp [(sphereArea_eq_toSphere hd).2])) ?_
  set B : ℝ≥0∞ := ENNReal.ofReal (‖ξ‖ ^ 2 / 2) * (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (D.k r * r)) +
      2 * ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r) with hB
  have hBfin : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top D.integrable_near_zero,
      ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) D.integrable_at_top⟩
  have hσ : (volume : Measure (Rd d)).toSphere univ ≠ ⊤ := measure_ne_top _ _
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBfin hσ) ?_
  refine (lintegral_mono fun η => ?_).trans (lintegral_const B).le
  refine (cosProfileL_le_sq D.k D.k_nonneg _).trans ?_
  have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
  have hle : ⟪ξ, (η : Rd d)⟫ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    have := abs_real_inner_le_norm ξ (η : Rd d)
    rw [hη, mul_one] at this
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  rw [hB]
  gcongr

/-- `ofReal F_d(ξ) = (F_d)_{ℝ≥0∞}(ξ)`, the exponent being finite. -/
theorem OriginDatum.ofReal_exponent (hd : 1 ≤ d) (D : OriginDatum d) (ξ : Rd d) :
    ENNReal.ofReal (D.exponent ξ) = D.exponentL ξ :=
  ENNReal.ofReal_toReal (D.exponentL_ne_top hd ξ)

theorem OriginDatum.exponent_nonneg (D : OriginDatum d) (ξ : Rd d) : 0 ≤ D.exponent ξ :=
  ENNReal.toReal_nonneg

/-- `|μ̂(ξ)| = e^{-F_d(ξ)}` for a law of the datum. -/
theorem IsLawOf.norm_charFun {D : OriginDatum d} {μ : Measure (Rd d)} (hμ : IsLawOf D μ)
    (ξ : Rd d) : ‖charFun μ ξ‖ = Real.exp (-D.exponent ξ) := by
  rw [hμ.2 ξ, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

end AffineHemigroup
