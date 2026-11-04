/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OriginExponent
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `lem:isotropic-exponent-log`(1) and `lem:origin-decay-exponent`: the exponent grows like `c log|ξ|`

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:isotropic-exponent-log`(1) and
`lem:origin-decay-exponent` (`thm:origin-boundedness-d`(1)). Wave 2, group A (Q-0281).

**Clause (1) of `lem:isotropic-exponent-log`** follows the blueprint: `φ(s) ≤ c Cin(|s|) + 2C_k`
(`OriginDatum.cosProfileL_le_cin`), `Cin` nondecreasing on `[0,∞)`, `|⟨ξ,η⟩| ≤ |ξ|` on the sphere,
the normalized surface measure of mass `1`, and `Cin(ρ) ≤ log ρ + 13/4`.

**`lem:origin-decay-exponent` takes another route than the blueprint's** at one step. The blueprint
bounds `F_d(ξ) ≥ β[log ρ - C]` through the sphere average `J_d` of `log|⟨ξ̂,η⟩|`, whose finiteness
needs the density `(1-u²)^{(d-3)/2}` of the image of `σ_{d-1}` under `η ↦ ⟨ξ̂,η⟩`. Here only the
**caps** `{η : |⟨e,η⟩| ≥ ε}` are read: for a finite `β < c` pick `β < β₁ < c`, then a cap whose
normalized measure `p` has `p β₁ ≥ β` (the caps increase to the complement of the great subsphere
`{⟨e,η⟩ = 0}`, which is `σ_{d-1}`-null because its cone lies in a hyperplane); on the cap
`Cin(r_β ρ|⟨e,η⟩|) ≥ log(ρ ε r_β) - 3`, so `F_d(ρe) ≥ p β₁ (log ρ - L) ≥ β (log ρ - L)` once the
bracket is nonnegative. `F_d` is radial (`OriginDatum.exponentL_eq_of_norm_eq`), so one direction
`e = e₁` serves every `ξ`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric ScaleSpace
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## `lem:isotropic-exponent-log`(1) -/

/-- `Cin(s) ≤ Cin(ρ)` when `|s| ≤ ρ`. -/
theorem cin_le_cin_of_abs_le {s ρ : ℝ} (h : |s| ≤ ρ) : cin s ≤ cin ρ := by
  have hs : cin s = cin |s| := by
    rcases le_or_gt 0 s with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, cin_neg]
  rw [hs]
  exact monotoneOn_cin (abs_nonneg s) (le_trans (abs_nonneg s) h) h

/-- **`lem:isotropic-exponent-log`(1)**: for a datum with Gaussian coefficient `0` and finite
profile at the origin `c`, `F_d(ξ) ≤ c log|ξ| + 13c/4 + 2C_k` and
`e^{-F_d(ξ)} ≥ e^{-13c/4 - 2C_k}|ξ|^{-c}` for `|ξ| ≥ 1`. -/
theorem isotropic_exponent_log_bound (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (hc : D.profileAtOrigin ≠ ⊤) (ξ : Rd d) (hξ : 1 ≤ ‖ξ‖) :
    D.exponent ξ ≤ D.profileAtOrigin.toReal * Real.log ‖ξ‖ + 13 / 4 * D.profileAtOrigin.toReal
        + 2 * D.tailConst ∧
      Real.exp (-(13 / 4 * D.profileAtOrigin.toReal) - 2 * D.tailConst)
          * ‖ξ‖ ^ (-D.profileAtOrigin.toReal) ≤ Real.exp (-D.exponent ξ) := by
  set c := D.profileAtOrigin with hcdef
  set I1 := ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r) with hI1
  have hρ0 : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hξ
  -- the bound in `ℝ≥0∞`
  have hL : D.exponentL ξ ≤ c * ENNReal.ofReal (cin ‖ξ‖) + 2 * I1 := by
    rw [D.exponentL_eq_sphere hd, ha, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
    calc (ENNReal.ofReal (sphereArea d))⁻¹ *
          ∫⁻ η : sphere (0 : Rd d) 1, cosProfileL D.k ⟪ξ, (η : Rd d)⟫
            ∂((volume : Measure (Rd d)).toSphere)
        ≤ (ENNReal.ofReal (sphereArea d))⁻¹ *
          ∫⁻ _η : sphere (0 : Rd d) 1, (c * ENNReal.ofReal (cin ‖ξ‖) + 2 * I1)
            ∂((volume : Measure (Rd d)).toSphere) := by
          gcongr with η
          refine (D.cosProfileL_le_cin _).trans ?_
          gcongr
          have hη : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
          refine cin_le_cin_of_abs_le ?_
          have := abs_real_inner_le_norm ξ (η : Rd d)
          rwa [hη, mul_one] at this
      _ = c * ENNReal.ofReal (cin ‖ξ‖) + 2 * I1 := by
          rw [lintegral_const, mul_comm, mul_assoc, mul_comm _ (ENNReal.ofReal (sphereArea d))⁻¹,
            inv_sphereArea_mul_toSphere_univ hd, mul_one]
  have hI1fin : I1 ≠ ⊤ := D.integrable_at_top
  have hfin : c * ENNReal.ofReal (cin ‖ξ‖) + 2 * I1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by norm_num) hI1fin⟩
  have hR : D.exponent ξ ≤ c.toReal * cin ‖ξ‖ + 2 * D.tailConst := by
    have h := ENNReal.toReal_mono hfin hL
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (by norm_num) hI1fin), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (cin_nonneg hρ0.le)] at h
  have hcin := cin_le_log_add hξ
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hmain : D.exponent ξ ≤ c.toReal * Real.log ‖ξ‖ + 13 / 4 * c.toReal + 2 * D.tailConst := by
    have : c.toReal * cin ‖ξ‖ ≤ c.toReal * (Real.log ‖ξ‖ + 13 / 4) :=
      mul_le_mul_of_nonneg_left hcin hc0
    linarith
  refine ⟨hmain, ?_⟩
  rw [Real.rpow_def_of_pos hρ0, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith

/-! ## The great subsphere is null, and the caps -/

/-- **A great subsphere is `σ_{d-1}`-null**: for `e ≠ 0`, `σ_{d-1}{η : ⟨e,η⟩ = 0} = 0`, its cone
`(0,1)·{η : ⟨e,η⟩ = 0}` lying in the hyperplane `e^⊥`, which is Lebesgue-null. -/
theorem toSphere_inner_eq_zero {e : Rd d} (he : e ≠ 0) :
    (volume : Measure (Rd d)).toSphere {η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0} = 0 := by
  have hmeas : MeasurableSet {η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [Measure.toSphere_apply' _ hmeas]
  refine mul_eq_zero_of_right _ (measure_mono_null ?_
    (Measure.addHaar_submodule volume (ℝ ∙ e)ᗮ ?_))
  · rintro _ ⟨t, -, _, ⟨η, hη, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [mem_setOf_eq] at hη
    simp [inner_smul_right, hη]
  · intro htop
    have : e ∈ (ℝ ∙ e)ᗮ := by rw [htop]; trivial
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at this
    exact he (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

/-- **The caps fill the sphere**: for `e ≠ 0` and any `q < σ_{d-1}(S^{d-1})` there is `ε ∈ (0,1]`
with `σ_{d-1}{η : |⟨e,η⟩| ≥ ε} > q`. -/
theorem exists_cap_gt {e : Rd d} (he : e ≠ 0) {q : ℝ≥0∞}
    (hq : q < (volume : Measure (Rd d)).toSphere univ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      q < (volume : Measure (Rd d)).toSphere {η : sphere (0 : Rd d) 1 | ε ≤ |⟪e, (η : Rd d)⟫|} := by
  set σ := (volume : Measure (Rd d)).toSphere
  let s : ℕ → Set (sphere (0 : Rd d) 1) :=
    fun n => {η | 1 / ((n : ℝ) + 1) ≤ |⟪e, (η : Rd d)⟫|}
  have hmono : Monotone s := by
    intro m n hmn η hη
    simp only [s, mem_setOf_eq] at hη ⊢
    refine le_trans ?_ hη
    gcongr
  have hunion : (⋃ n, s n) = {η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0}ᶜ := by
    ext η
    simp only [s, mem_iUnion, mem_setOf_eq, mem_compl_iff]
    constructor
    · rintro ⟨n, hn⟩ h0
      rw [h0, abs_zero] at hn
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro h0
      have hpos : 0 < |⟪e, (η : Rd d)⟫| := abs_pos.mpr h0
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, hn.le⟩
  have hfull : σ (⋃ n, s n) = σ univ := by
    rw [hunion]
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    calc σ univ ≤ σ ({η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0}ᶜ)
          + σ {η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0} := by
          rw [add_comm]; exact (measure_union_le _ _).trans' (by rw [union_compl_self])
      _ = σ ({η : sphere (0 : Rd d) 1 | ⟪e, (η : Rd d)⟫ = 0}ᶜ) := by
          rw [toSphere_inner_eq_zero he, add_zero]
  have htend := tendsto_measure_iUnion_atTop (μ := σ) hmono
  rw [hfull] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (lt_mem_nhds hq)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, hn⟩
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ## `lem:origin-decay-exponent` -/

namespace OriginDatum

/-- **`lem:origin-decay-exponent`, on the exponent** (Q-0409): for a datum with Gaussian
coefficient `0` and every finite `β < c := k_d(0+)` there is `C_β < ∞` with
`e^{-F_d(ξ)} ≤ C_β(1 + |ξ|)^{-β}`. This is the whole content of `origin_decay_exponent`, whose
proof it was: no law is named, so `cor:origin-profile-exponent` reads the bound without one.
(Declared inside `namespace OriginDatum`, as the node's `\lean` tag is read from the source.) -/
theorem exponent_decay (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) (β : ℝ)
    (hβ : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ C : ℝ, ∀ ξ : Rd d, Real.exp (-D.exponent ξ) ≤ C * (1 + ‖ξ‖) ^ (-β) := by
  rcases le_or_gt β 0 with hβ0 | hβ0
  · -- `β ≤ 0`: `e^{-F_d} ≤ 1 ≤ (1 + |ξ|)^{-β}`
    refine ⟨1, fun ξ => ?_⟩
    rw [one_mul]
    calc Real.exp (-D.exponent ξ) ≤ 1 := Real.exp_le_one_iff.mpr (by
          linarith [D.exponent_nonneg ξ])
      _ ≤ (1 + ‖ξ‖) ^ (-β) := Real.one_le_rpow (by linarith [norm_nonneg ξ]) (by linarith)
  -- `β > 0`: an intermediate `β₁` and the radius `r_β`
  obtain ⟨β₁', -, hββ₁, hβ₁c'⟩ := ENNReal.lt_iff_exists_real_btwn.mp hβ
  have hβ₁ : β < β₁' := by
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hβ0.le).mp hββ₁
    exact this
  set β₁ := β₁' with hβ₁def
  have hβ₁0 : 0 < β₁ := lt_trans hβ0 hβ₁
  obtain ⟨rβ, ⟨hrβ0, hrβ1⟩, hkβ⟩ := D.exists_le_k hβ₁c'
  -- a cap of normalized mass at least `β/β₁`
  haveI : NeZero d := ⟨by omega⟩
  set e : Rd d := ebasis (0 : Fin d) with he
  have he1 : ‖e‖ = 1 := by simp [he, ebasis]
  have he0 : e ≠ 0 := by rw [← norm_ne_zero_iff, he1]; exact one_ne_zero
  set A := sphereArea d with hA
  have hApos : 0 < A := (sphereArea_eq_toSphere hd).2
  have hσ : (volume : Measure (Rd d)).toSphere univ = ENNReal.ofReal A := (sphereArea_eq_toSphere hd).1.symm
  have hq : ENNReal.ofReal (A * (β / β₁)) < (volume : Measure (Rd d)).toSphere univ := by
    rw [hσ, ENNReal.ofReal_lt_ofReal_iff hApos]
    have : β / β₁ < 1 := (div_lt_one hβ₁0).mpr hβ₁
    nlinarith
  obtain ⟨ε, hε0, hε1, hcap⟩ := exists_cap_gt he0 hq
  set cap := {η : sphere (0 : Rd d) 1 | ε ≤ |⟪e, (η : Rd d)⟫|} with hcapdef
  set L := 3 - Real.log (ε * rβ) with hL
  have hL0 : 0 ≤ L := by
    have : Real.log (ε * rβ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by nlinarith)
    linarith
  -- the lower bound on the exponent along `e`
  have hlow : ∀ ρ : ℝ, 0 < ρ → β * (Real.log ρ - L) ≤ D.exponent (ρ • e) := by
    intro ρ hρ
    rcases lt_or_ge (Real.log ρ - L) 0 with hneg | hnn
    · nlinarith [D.exponent_nonneg (ρ • e)]
    set X := β₁ * (Real.log ρ - L) with hX
    have hX0 : 0 ≤ X := mul_nonneg hβ₁0.le hnn
    have hcapmeas : MeasurableSet cap := measurableSet_le measurable_const (by fun_prop)
    have hL1 : (volume : Measure (Rd d)).toSphere cap * ENNReal.ofReal X ≤
        ∫⁻ η : sphere (0 : Rd d) 1, cosProfileL D.k ⟪ρ • e, (η : Rd d)⟫
          ∂((volume : Measure (Rd d)).toSphere) := by
      rw [mul_comm, ← lintegral_indicator_const hcapmeas]
      refine lintegral_mono fun η => ?_
      by_cases hη : η ∈ cap
      · rw [indicator_of_mem hη]
        refine le_trans ?_ (cosProfileL_ge hrβ0 hkβ _)
        rw [← ENNReal.ofReal_mul hβ₁0.le]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hβ₁0.le)
        have hηc : ε ≤ |⟪e, (η : Rd d)⟫| := hη
        set t := ⟪ρ • e, (η : Rd d)⟫ * rβ with ht
        have htabs : ρ * ε * rβ ≤ |t| := by
          rw [ht, inner_smul_left, abs_mul, abs_mul, RCLike.conj_to_real, abs_of_pos hρ,
            abs_of_pos hrβ0]
          gcongr
        have hcin : cin t = cin |t| := by
          rcases le_or_gt 0 t with h0 | h0
          · rw [abs_of_nonneg h0]
          · rw [abs_of_neg h0, cin_neg]
        have htpos : 0 < |t| := lt_of_lt_of_le (by positivity) htabs
        rw [hcin]
        refine le_trans ?_ (log_sub_le_cin htpos)
        have hlog : Real.log (ρ * ε * rβ) ≤ Real.log |t| := Real.log_le_log (by positivity) htabs
        have hsplit : Real.log (ρ * ε * rβ) = Real.log ρ + Real.log (ε * rβ) := by
          rw [mul_assoc, Real.log_mul hρ.ne' (by positivity)]
        rw [hL]
        linarith
      · rw [indicator_of_notMem hη]
        exact zero_le
    have hEL := D.exponentL_eq_sphere hd (ρ • e)
    rw [ha, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add] at hEL
    have hfinL := D.exponentL_ne_top hd (ρ • e)
    have h2 : (ENNReal.ofReal A)⁻¹ * ((volume : Measure (Rd d)).toSphere cap * ENNReal.ofReal X)
        ≤ D.exponentL (ρ • e) := by
      rw [hEL]; gcongr
    have hcapfin : (volume : Measure (Rd d)).toSphere cap ≠ ⊤ := measure_ne_top _ _
    have h3 := ENNReal.toReal_mono hfinL h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hApos.le,
      ENNReal.toReal_ofReal hX0] at h3
    have hcapR : A * (β / β₁) ≤ ((volume : Measure (Rd d)).toSphere cap).toReal := by
      have := (ENNReal.ofReal_le_iff_le_toReal hcapfin).mp hcap.le
      exact this
    have hfinal : β * (Real.log ρ - L) ≤ A⁻¹ * (((volume : Measure (Rd d)).toSphere cap).toReal * X) := by
      have hAinv : 0 < A⁻¹ := inv_pos.mpr hApos
      calc β * (Real.log ρ - L) = A⁻¹ * ((A * (β / β₁)) * X) := by
            rw [hX]; field_simp
        _ ≤ A⁻¹ * (((volume : Measure (Rd d)).toSphere cap).toReal * X) := by
            gcongr
    exact hfinal.trans h3
  -- the constant
  refine ⟨(2 : ℝ) ^ β * (1 + Real.exp (β * L)), fun ξ => ?_⟩
  have h2pos : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos two_pos β
  have hbase : (1 : ℝ) ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  rcases lt_or_ge ‖ξ‖ 1 with hsmall | hlarge
  · -- `|ξ| < 1`: `e^{-F} ≤ 1 ≤ 2^β (1+|ξ|)^{-β}`
    have h1 : Real.exp (-D.exponent ξ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [D.exponent_nonneg ξ])
    have h2 : 1 ≤ (2 : ℝ) ^ β * (1 + ‖ξ‖) ^ (-β) := by
      rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hβ0.le
    calc Real.exp (-D.exponent ξ) ≤ 1 := h1
      _ ≤ (2 : ℝ) ^ β * (1 + ‖ξ‖) ^ (-β) := h2
      _ ≤ (2 : ℝ) ^ β * (1 + Real.exp (β * L)) * (1 + ‖ξ‖) ^ (-β) := by
          have : 0 ≤ (1 + ‖ξ‖) ^ (-β) := Real.rpow_nonneg (by linarith) _
          have : 0 < Real.exp (β * L) := Real.exp_pos _
          nlinarith
  · -- `|ξ| ≥ 1`: `e^{-F} ≤ e^{βL} |ξ|^{-β} ≤ e^{βL} 2^β (1+|ξ|)^{-β}`
    have hρ : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hlarge
    have hrad : D.exponent ξ = D.exponent (‖ξ‖ • e) :=
      D.exponent_eq_of_norm_eq (by rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hρ.le])
    have hF := hlow ‖ξ‖ hρ
    rw [← hrad] at hF
    have h1 : Real.exp (-D.exponent ξ) ≤ Real.exp (β * L) * ‖ξ‖ ^ (-β) := by
      rw [Real.rpow_def_of_pos hρ, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h2 : ‖ξ‖ ^ (-β) ≤ (2 : ℝ) ^ β * (1 + ‖ξ‖) ^ (-β) := by
      have hle : (1 + ‖ξ‖) ^ β ≤ 2 ^ β * ‖ξ‖ ^ β := by
        rw [← Real.mul_rpow two_pos.le hρ.le]
        exact Real.rpow_le_rpow (by linarith) (by linarith) hβ0.le
      have ha : 0 < ‖ξ‖ ^ β := Real.rpow_pos_of_pos hρ β
      have hb : 0 < (1 + ‖ξ‖) ^ β := Real.rpow_pos_of_pos (by linarith) β
      rw [Real.rpow_neg hρ.le, Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hb,
        inv_mul_le_iff₀ ha]
      linarith
    calc Real.exp (-D.exponent ξ) ≤ Real.exp (β * L) * ‖ξ‖ ^ (-β) := h1
      _ ≤ Real.exp (β * L) * ((2 : ℝ) ^ β * (1 + ‖ξ‖) ^ (-β)) := by gcongr
      _ ≤ (2 : ℝ) ^ β * (1 + Real.exp (β * L)) * (1 + ‖ξ‖) ^ (-β) := by
          have : 0 ≤ (1 + ‖ξ‖) ^ (-β) := Real.rpow_nonneg (by linarith) _
          nlinarith

end OriginDatum

/-- **`lem:origin-decay-exponent`** (`thm:origin-boundedness-d`(1)): for a datum with Gaussian
coefficient `0` and `c := k_d(0+) ∈ (0,∞]`, every law `μ` of the datum and every finite `β < c`
there is `C_β < ∞` with `|μ̂(ξ)| ≤ C_β(1 + |ξ|)^{-β}`. It is `OriginDatum.exponent_decay` read
through `|μ̂| = e^{-F_d}`. -/
theorem origin_decay_exponent (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0)
    (_hc : 0 < D.profileAtOrigin) (μ : Measure (Rd d)) (hμ : IsLawOf D μ) (β : ℝ)
    (hβ : ENNReal.ofReal β < D.profileAtOrigin) :
    ∃ C : ℝ, ∀ ξ : Rd d, ‖charFun μ ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-β) := by
  obtain ⟨C, hC⟩ := D.exponent_decay hd ha β hβ
  exact ⟨C, fun ξ => by rw [hμ.norm_charFun]; exact hC ξ⟩

end AffineHemigroup
