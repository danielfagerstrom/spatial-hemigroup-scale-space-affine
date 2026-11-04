/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.FiltrationStrict
import AffineHemigroup.PolarReading
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `lem:shadow-polar-profile`: the polar profile of a shadow

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:shadow-polar-profile` (Q-0425; its Lean
is Q-0429). An isotropic origin datum `(a, k')` in dimension `d + 1` casts a shadow in dimension
`d`: the datum `(a, k̄)` with

  `k̄(r) = C_d ∫_ℝ k'(r√(1+u²)) (1+u²)^{-(d+1)/2} du`,  `C_d = |S^{d-1}|/|S^d|`.

The module proves the lemma on data and measures and cites nothing.

* The splitting `ℝ^{d+1} = ℝ × ℝ^d` (`splitLast`, the last coordinate and `dropLast`) preserves
  Lebesgue measure (`measurePreserving_splitLast`).
* `lintegral_shadow` is `eq:shadow-identity`, for nonnegative measurable `g` on `ℝ^d` and `h` on
  `ℝ`: Tonelli's theorem on `ℝ × ℝ^d` and the substitution `y = |x| u` in the last coordinate.
* Clause (1), `shadow_profile_mean`: the normalisation `C_d ∫ (1+u²)^{-(d+1)/2} du = 1`, from
  polar coordinates in the two dimensions applied to `h = 1_{(1,2)}` and the invariance of
  `dr/r` under dilations; and `0 ≤ k̄ ≤ k'`.
* Clause (2), `shadow_profile_regular`: `k̄` is nonincreasing and continuous on `(0,∞)`
  (dominated convergence; a nonincreasing function has countably many discontinuities, each met
  by at most two `u`), and `k̄(0+) = k'(0+)` in `[0,∞]` (monotone convergence).
* Clause (3): `OriginDatum.shadow`, the datum `(a, k̄)`; `OriginDatum.shadow_levyMeasure`, its
  Lévy measure is the image of `ν'` under `dropLast`, which gives the origin no mass;
  `OriginDatum.shadow_exponent`, its exponent is `ξ ↦ F'((ξ, 0))`, and radial with the same
  function when `F'` is.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The splitting `ℝ^{d+1} = ℝ × ℝ^d` -/

/-- The splitting of `ℝ^{d+1}`: the last coordinate, and the first `d` coordinates. -/
noncomputable def splitLast (d : ℕ) (z : Rd (d + 1)) : ℝ × Rd d := (z (Fin.last d), dropLast d z)

/-- The splitting carries Lebesgue measure on `ℝ^{d+1}` to the product of the Lebesgue measures
of `ℝ` and `ℝ^d`. Mathlib types only. -/
theorem measurePreserving_splitLast (d : ℕ) :
    MeasurePreserving (splitLast d) (volume : Measure (Rd (d + 1)))
      ((volume : Measure ℝ).prod (volume : Measure (Rd d))) := by
  have h1 : MeasurePreserving (WithLp.ofLp : Rd (d + 1) → (Fin (d + 1) → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin (d + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  have h3 : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) :=
    PiLp.volume_preserving_toLp (Fin d)
  have h4 := (MeasurePreserving.id (volume : Measure ℝ)).prod h3
  have h := h4.comp (h2.comp h1)
  have hfun : splitLast d = Prod.map id (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)) ∘
        (WithLp.ofLp : Rd (d + 1) → (Fin (d + 1) → ℝ)) := by
    funext z
    refine Prod.ext rfl ?_
    ext i
    simp [splitLast, dropLast, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.init]
  rw [hfun]
  exact h

/-- `|z|² = |Πz|² + z_{d+1}²`, as a square root. -/
theorem norm_eq_sqrt_split (z : Rd (d + 1)) :
    ‖z‖ = Real.sqrt (‖dropLast d z‖ ^ 2 + z (Fin.last d) ^ 2) := by
  rw [EuclideanSpace.norm_eq z, EuclideanSpace.norm_eq (dropLast d z),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_castSucc]
  simp [dropLast]

/-! ## A dilation of the line -/

/-- `∫ f(y) dy = r ∫ f(ru) du` for `r > 0`, for every nonnegative `f`. Mathlib types only. -/
theorem lintegral_comp_mul_left_pos {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f y = ENNReal.ofReal r * ∫⁻ u, f (r * u) := by
  have h := Real.map_volume_mul_left hr.ne'
  have h2 : ∫⁻ y, f y ∂(Measure.map (r * ·) volume) = ∫⁻ u, f (r * u) :=
    lintegral_map_equiv f (Homeomorph.mulLeft₀ r hr.ne').toMeasurableEquiv
  rw [h, lintegral_smul_measure, abs_of_pos (inv_pos.2 hr), smul_eq_mul] at h2
  rw [← h2, ← mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one,
    one_mul]

/-- The measure `dr/r` on `(0,∞)` is invariant under dilations:
`∫_0^∞ h(rs) dr/r = ∫_0^∞ h(t) dt/t` for `s > 0`. Mathlib types only. -/
theorem lintegral_Ioi_comp_mul_div {s : ℝ} (hs : 0 < s) (h : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), h (r * s) * ENNReal.ofReal (1 / r)
      = ∫⁻ t in Ioi (0 : ℝ), h t * ENNReal.ofReal (1 / t) := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    lintegral_comp_mul_left_pos hs ((Ioi (0 : ℝ)).indicator fun t => h t * ENNReal.ofReal (1 / t)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · have hr0 : 0 < r := hr
    rw [indicator_of_mem hr, indicator_of_mem (show s * r ∈ Ioi (0 : ℝ) from mul_pos hs hr0),
      mul_comm s r, mul_left_comm, ← ENNReal.ofReal_mul hs.le]
    congr 2
    field_simp
  · have hr0 : r ≤ 0 := not_lt.1 hr
    rw [indicator_of_notMem hr, indicator_of_notMem (show s * r ∉ Ioi (0 : ℝ) from
      not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hs.le hr0)), mul_zero]

/-! ## The weight and the profile of the shadow -/

/-- **The weight** `(1 + u²)^{-(d+1)/2}` of `lem:shadow-polar-profile`. -/
noncomputable def shadowWeight (d : ℕ) (u : ℝ) : ℝ := (1 + u ^ 2) ^ (-((d : ℝ) + 1) / 2)

theorem shadowWeight_pos (d : ℕ) (u : ℝ) : 0 < shadowWeight d u :=
  Real.rpow_pos_of_pos (by positivity) _

theorem continuous_shadowWeight (d : ℕ) : Continuous (shadowWeight d) := by
  unfold shadowWeight
  exact (by fun_prop : Continuous fun u : ℝ => 1 + u ^ 2).rpow_const fun u =>
    Or.inl (by positivity)

/-- The weight is integrable on the line, for `d ≥ 1`: it is at most `(1 + u²)^{-1}`. -/
theorem integrable_shadowWeight (hd : 1 ≤ d) : Integrable (shadowWeight d) := by
  refine integrable_inv_one_add_sq.mono' (continuous_shadowWeight d).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.norm_of_nonneg (shadowWeight_pos d u).le, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg u]) (by linarith)

/-- The weight is `(√(1+u²))^{-(d+1)}`. -/
theorem shadowWeight_eq (d : ℕ) (u : ℝ) :
    shadowWeight d u = 1 / Real.sqrt (1 + u ^ 2) ^ (d + 1) := by
  have h0 : (0 : ℝ) ≤ 1 + u ^ 2 := by positivity
  have hpow : Real.sqrt (1 + u ^ 2) ^ (d + 1) = (1 + u ^ 2) ^ (((d : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + u ^ 2) ^ (1 / 2 : ℝ)) (d + 1),
      ← Real.rpow_mul h0]
    congr 1
    push_cast
    ring
  rw [hpow, one_div, ← Real.rpow_neg h0, shadowWeight]
  congr 1
  ring

/-- **The polar profile of the shadow** (`lem:shadow-polar-profile`):
`k̄(r) = C_d ∫_ℝ k(r√(1+u²)) (1+u²)^{-(d+1)/2} du`, `C_d = |S^{d-1}|/|S^d|`, as a Bochner
integral. Read at `r > 0`, for a profile `k` that is nonnegative and nonincreasing on `(0,∞)`
and `d ≥ 1`, where the integrand is integrable. -/
noncomputable def shadowProfile (d : ℕ) (k : ℝ → ℝ) (r : ℝ) : ℝ :=
  sphereArea d / sphereArea (d + 1) * ∫ u : ℝ, k (r * Real.sqrt (1 + u ^ 2)) * shadowWeight d u

/-- The same mean for an `ℝ≥0∞`-valued function, with a lower integral: the function `h̄` of the
proof of `lem:shadow-polar-profile`. -/
noncomputable def shadowL (d : ℕ) (h : ℝ → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (sphereArea d / sphereArea (d + 1)) *
    ∫⁻ u : ℝ, h (r * Real.sqrt (1 + u ^ 2)) * ENNReal.ofReal (shadowWeight d u)

/-! ## The integral over the last coordinate (`eq:shadow-identity`) -/

/-- **`eq:shadow-identity`**: for nonnegative measurable `g` on `ℝ^d` and `h` on `ℝ`,
`∫ g(Πz) h(|z|)/(|S^d||z|^{d+1}) dz = ∫ g(x) h̄(|x|)/(|S^{d-1}||x|^d) dx`, both sides in
`[0,∞]`. The densities are written `1/(|S||x|^n) · h(|x|)`, which vanish at the origin by Lean's
`1/0 = 0`, so `g(0) = 0` is not assumed. -/
theorem lintegral_shadow (hd : 1 ≤ d) (g : Rd d → ℝ≥0∞) (hg : Measurable g) (h : ℝ → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ z : Rd (d + 1), g (dropLast d z) *
        (ENNReal.ofReal (1 / (sphereArea (d + 1) * ‖z‖ ^ (d + 1))) * h ‖z‖)
      = ∫⁻ x : Rd d, g x *
        (ENNReal.ofReal (1 / (sphereArea d * ‖x‖ ^ d)) * shadowL d h ‖x‖) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  set ρ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (1 / (sphereArea (d + 1) * t ^ (d + 1))) * h t
    with hρ
  have hρm : Measurable ρ := by rw [hρ]; fun_prop
  set Φ : ℝ × Rd d → ℝ≥0∞ := fun p => g p.2 * ρ (Real.sqrt (‖p.2‖ ^ 2 + p.1 ^ 2)) with hΦ
  have hΦm : Measurable Φ := by
    rw [hΦ]
    exact (hg.comp measurable_snd).mul (hρm.comp (by fun_prop))
  have h1 : ∫⁻ z : Rd (d + 1), g (dropLast d z) *
      (ENNReal.ofReal (1 / (sphereArea (d + 1) * ‖z‖ ^ (d + 1))) * h ‖z‖)
      = ∫⁻ z : Rd (d + 1), Φ (splitLast d z) := by
    refine lintegral_congr fun z => ?_
    simp only [hΦ, hρ, splitLast, ← norm_eq_sqrt_split]
  rw [h1, (measurePreserving_splitLast d).lintegral_comp hΦm, lintegral_prod_symm' Φ hΦm]
  have hne : ∀ᵐ x : Rd d, x ≠ 0 := by
    have : (volume : Measure (Rd d)) {0} = 0 := measure_singleton 0
    exact compl_mem_ae_iff.2 this
  refine lintegral_congr_ae (hne.mono fun x hx => ?_)
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  simp only [hΦ]
  set r := ‖x‖ with hrdef
  rw [lintegral_const_mul (g x)
    (show Measurable fun y : ℝ => ρ (Real.sqrt (r ^ 2 + y ^ 2)) from hρm.comp (by fun_prop))]
  congr 1
  rw [lintegral_comp_mul_left_pos hr, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, shadowL,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun u => ?_
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (r ^ 2 + (r * u) ^ 2) = r * Real.sqrt (1 + u ^ 2) := by
    rw [show r ^ 2 + (r * u) ^ 2 = r ^ 2 * (1 + u ^ 2) by ring, Real.sqrt_mul (sq_nonneg r),
      Real.sqrt_sq hr.le]
  rw [hsq, hρ]
  simp only
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (by positivity),
    mul_right_comm _ (h _) (ENNReal.ofReal (shadowWeight d u)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [shadowWeight_eq, mul_pow]
  have hrd : r ^ (d + 1) = r * r ^ d := pow_succ' r d
  rw [hrd]
  field_simp

/-! ## Polar coordinates for a radial density, and the normalisation of the weight -/

/-- Polar coordinates for a radial density: `∫ φ(|x|)/(|S^{d-1}||x|^d) dx = ∫_0^∞ φ(r) dr/r`.
It is `lintegral_radial` (`AffineHemigroup.OriginBoundedness`) for the function
`t ↦ φ(t)/(|S^{d-1}| t^d)`. Mathlib types, with the library's `sphereArea`. -/
theorem lintegral_radial_density (hd : 1 ≤ d) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x : Rd d, ENNReal.ofReal (1 / (sphereArea d * ‖x‖ ^ d)) * φ ‖x‖
      = ∫⁻ r in Ioi (0 : ℝ), φ r * ENNReal.ofReal (1 / r) := by
  have hA := (sphereArea_eq_toSphere hd).2
  rw [lintegral_radial hd (fun t => ENNReal.ofReal (1 / (sphereArea d * t ^ d)) * φ t)
    (by fun_prop), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have hrd : r ^ d = r * r ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hrd1 : 0 < r ^ (d - 1) := pow_pos hr _
  rw [mul_right_comm (ENNReal.ofReal (1 / (sphereArea d * r ^ d))),
    ← ENNReal.ofReal_mul (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul hA.le,
    mul_comm (φ r)]
  congr 2
  rw [hrd]
  field_simp

theorem shadowL_measurable (h : ℝ → ℝ≥0∞) (hh : Measurable h) : Measurable (shadowL d h) := by
  have hw : Measurable (shadowWeight d) := (continuous_shadowWeight d).measurable
  have hF : Measurable fun p : ℝ × ℝ =>
      h (p.1 * Real.sqrt (1 + p.2 ^ 2)) * ENNReal.ofReal (shadowWeight d p.2) :=
    (hh.comp (by fun_prop)).mul (hw.comp measurable_snd).ennreal_ofReal
  exact (Measurable.lintegral_prod_right' hF).const_mul _

/-- **`lem:shadow-polar-profile`(1), the normalisation**, with a lower integral:
`C_d ∫ (1+u²)^{-(d+1)/2} du = 1`. `eq:shadow-identity` with `g = 1` and `h = 1_{(1,2)}`: in polar
coordinates of `ℝ^{d+1}` the left side is `I = ∫_1^2 dt/t`, and in polar coordinates of `ℝ^d`,
by Tonelli's theorem and the invariance of `dr/r` under dilations, the right side is
`C_d ∫ (1+u²)^{-(d+1)/2} du · I`; and `0 < I < ∞`. No Beta integral. -/
theorem shadowWeight_lintegral (hd : 1 ≤ d) :
    ENNReal.ofReal (sphereArea d / sphereArea (d + 1)) *
      ∫⁻ u : ℝ, ENNReal.ofReal (shadowWeight d u) = 1 := by
  set h : ℝ → ℝ≥0∞ := (Ioo (1 : ℝ) 2).indicator 1 with hh
  have hhm : Measurable h := measurable_one.indicator measurableSet_Ioo
  set I : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), h t * ENNReal.ofReal (1 / t) with hI
  have hIeq : I = ∫⁻ t in Ioo (1 : ℝ) 2, ENNReal.ofReal (1 / t) := by
    rw [hI, ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Ioo (1 : ℝ) 2
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from lt_trans one_pos ht.1), hh,
        indicator_of_mem ht, indicator_of_mem ht, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem ht]
      by_cases ht0 : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht0, hh, indicator_of_notMem ht, zero_mul]
      · rw [indicator_of_notMem ht0]
  have hItop : I ≠ ⊤ := by
    rw [hIeq]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioo (1 : ℝ) 2, 1) ?_
      (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_)
    · rw [setLIntegral_const, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.one_ne_top ENNReal.ofReal_ne_top
    · rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_one (by linarith [ht.1])]
      exact ht.1.le
  have hIpos : I ≠ 0 := by
    rw [hIeq]
    have hle : ∫⁻ _ in Ioo (1 : ℝ) 2, ENNReal.ofReal (1 / 2)
        ≤ ∫⁻ t in Ioo (1 : ℝ) 2, ENNReal.ofReal (1 / t) :=
      setLIntegral_mono' measurableSet_Ioo fun t ht =>
        ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by linarith [ht.1]) ht.2.le)
    rw [setLIntegral_const, Real.volume_Ioo] at hle
    intro h0
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.ofReal_eq_zero, ENNReal.ofReal_eq_zero] at hle
    rcases hle with h1 | h1 <;> norm_num at h1
  set C : ℝ≥0∞ := ENNReal.ofReal (sphereArea d / sphereArea (d + 1)) with hC
  have hw : Measurable (shadowWeight d) := (continuous_shadowWeight d).measurable
  -- the identity with `g = 1`, read in polar coordinates on both sides
  have key := lintegral_shadow hd (fun _ => 1) measurable_const h hhm
  simp only [one_mul] at key
  rw [lintegral_radial_density (d := d + 1) (by omega) h hhm,
    lintegral_radial_density hd (shadowL d h) (shadowL_measurable h hhm)] at key
  have hFm : Measurable (Function.uncurry fun r u : ℝ =>
      h (r * Real.sqrt (1 + u ^ 2)) * ENNReal.ofReal (shadowWeight d u) *
        ENNReal.ofReal (1 / r)) := by
    change Measurable fun p : ℝ × ℝ =>
      h (p.1 * Real.sqrt (1 + p.2 ^ 2)) * ENNReal.ofReal (shadowWeight d p.2) *
        ENNReal.ofReal (1 / p.1)
    exact ((hhm.comp (by fun_prop)).mul (hw.comp measurable_snd).ennreal_ofReal).mul
      (by fun_prop)
  have hswap : ∫⁻ r in Ioi (0 : ℝ), shadowL d h r * ENNReal.ofReal (1 / r)
      = C * (∫⁻ u : ℝ, ENNReal.ofReal (shadowWeight d u)) * I := by
    calc ∫⁻ r in Ioi (0 : ℝ), shadowL d h r * ENNReal.ofReal (1 / r)
        = ∫⁻ r in Ioi (0 : ℝ), C * ∫⁻ u : ℝ, h (r * Real.sqrt (1 + u ^ 2)) *
            ENNReal.ofReal (shadowWeight d u) * ENNReal.ofReal (1 / r) := by
          refine lintegral_congr fun r => ?_
          rw [shadowL, mul_assoc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ = C * ∫⁻ r in Ioi (0 : ℝ), ∫⁻ u : ℝ, h (r * Real.sqrt (1 + u ^ 2)) *
            ENNReal.ofReal (shadowWeight d u) * ENNReal.ofReal (1 / r) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = C * ∫⁻ u : ℝ, ∫⁻ r in Ioi (0 : ℝ), h (r * Real.sqrt (1 + u ^ 2)) *
            ENNReal.ofReal (shadowWeight d u) * ENNReal.ofReal (1 / r) := by
          rw [lintegral_lintegral_swap hFm.aemeasurable]
      _ = C * ∫⁻ u : ℝ, ENNReal.ofReal (shadowWeight d u) * I := by
          congr 1
          refine lintegral_congr fun u => ?_
          have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
          rw [hI, ← lintegral_Ioi_comp_mul_div hs h,
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun r => ?_
          ring
      _ = C * (∫⁻ u : ℝ, ENNReal.ofReal (shadowWeight d u)) * I := by
          rw [lintegral_mul_const' _ _ hItop, mul_assoc]
  rw [hswap] at key
  have h1 : C * (∫⁻ u : ℝ, ENNReal.ofReal (shadowWeight d u)) * I = 1 * I := by
    rw [one_mul]; exact key.symm
  exact (ENNReal.mul_left_inj hIpos hItop).1 h1

/-- **`lem:shadow-polar-profile`(1), the normalisation**:
`C_d ∫_ℝ (1+u²)^{-(d+1)/2} du = 1`, `C_d = |S^{d-1}|/|S^d|`. -/
theorem shadowWeight_normalisation (hd : 1 ≤ d) :
    sphereArea d / sphereArea (d + 1) * ∫ u : ℝ, shadowWeight d u = 1 := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  have h := shadowWeight_lintegral hd
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_shadowWeight hd)
    (ae_of_all _ fun u => (shadowWeight_pos d u).le),
    ← ENNReal.ofReal_mul (div_nonneg hA.le hA'.le), ENNReal.ofReal_eq_one] at h
  exact h

/-! ## The profile of the shadow: a mean, nonincreasing, continuous -/

section Profile

variable {k : ℝ → ℝ}

theorem le_mul_sqrt_one_add_sq {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    r ≤ r * Real.sqrt (1 + u ^ 2) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + u ^ 2) := by
    rw [Real.le_sqrt' one_pos]; nlinarith [sq_nonneg u]
  nlinarith

theorem mul_sqrt_one_add_sq_pos {r : ℝ} (hr : 0 < r) (u : ℝ) :
    0 < r * Real.sqrt (1 + u ^ 2) := mul_pos hr (Real.sqrt_pos.2 (by positivity))

theorem shadow_integrand_measurable (hk : AntitoneOn k (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    Measurable fun u : ℝ => k (r * Real.sqrt (1 + u ^ 2)) := by
  have hm := measurable_indicator_Ioi_of_antitoneOn hk
  have heq : (fun u : ℝ => k (r * Real.sqrt (1 + u ^ 2)))
      = fun u : ℝ => (Ioi (0 : ℝ)).indicator k (r * Real.sqrt (1 + u ^ 2)) := by
    funext u
    rw [indicator_of_mem (show r * Real.sqrt (1 + u ^ 2) ∈ Ioi (0 : ℝ) from
      mul_sqrt_one_add_sq_pos hr u)]
  rw [heq]
  exact hm.comp (by fun_prop)

/-- The integrand of `k̄(r)` is integrable: it is at most `k(r) (1+u²)^{-(d+1)/2}`. -/
theorem shadow_integrable (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    Integrable fun u : ℝ => k (r * Real.sqrt (1 + u ^ 2)) * shadowWeight d u := by
  refine ((integrable_shadowWeight hd).const_mul (k r)).mono'
    ((shadow_integrand_measurable hk hr).mul
      (continuous_shadowWeight d).measurable).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  have hpos := mul_sqrt_one_add_sq_pos hr u
  rw [Real.norm_of_nonneg (mul_nonneg (hk0 _ hpos) (shadowWeight_pos d u).le)]
  exact mul_le_mul_of_nonneg_right (hk hr hpos (le_mul_sqrt_one_add_sq hr.le u))
    (shadowWeight_pos d u).le

theorem shadowProfile_nonneg (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r) {r : ℝ}
    (hr : 0 < r) : 0 ≤ shadowProfile d k r := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  exact mul_nonneg (div_nonneg hA.le hA'.le) (integral_nonneg fun u =>
    mul_nonneg (hk0 _ (mul_sqrt_one_add_sq_pos hr u)) (shadowWeight_pos d u).le)

/-- **`lem:shadow-polar-profile`(1)**: `k̄(r) ≤ k(r)`, a mean of the values of `k` on
`[r,∞)`. -/
theorem shadowProfile_le (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) {r : ℝ} (hr : 0 < r) : shadowProfile d k r ≤ k r := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  have h1 : ∫ u : ℝ, k (r * Real.sqrt (1 + u ^ 2)) * shadowWeight d u
      ≤ ∫ u : ℝ, k r * shadowWeight d u :=
    integral_mono (shadow_integrable hd hk0 hk hr) ((integrable_shadowWeight hd).const_mul _)
      fun u => mul_le_mul_of_nonneg_right
        (hk hr (mul_sqrt_one_add_sq_pos hr u) (le_mul_sqrt_one_add_sq hr.le u))
        (shadowWeight_pos d u).le
  rw [integral_const_mul] at h1
  calc shadowProfile d k r
      ≤ sphereArea d / sphereArea (d + 1) * (k r * ∫ u : ℝ, shadowWeight d u) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hA.le hA'.le)
    _ = k r := by rw [mul_left_comm, shadowWeight_normalisation hd, mul_one]

/-- **`lem:shadow-polar-profile`(2)**: `k̄` is nonincreasing on `(0,∞)`. -/
theorem shadowProfile_antitoneOn (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) : AntitoneOn (shadowProfile d k) (Ioi 0) := by
  intro r (hr : 0 < r) r' (hr' : 0 < r') hrr'
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  refine mul_le_mul_of_nonneg_left (integral_mono (shadow_integrable hd hk0 hk hr')
    (shadow_integrable hd hk0 hk hr) fun u => ?_) (div_nonneg hA.le hA'.le)
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  exact mul_le_mul_of_nonneg_right (hk (mul_pos hr hs) (mul_pos hr' hs)
    (mul_le_mul_of_nonneg_right hrr' hs.le)) (shadowWeight_pos d u).le

/-- **`lem:shadow-polar-profile`(2)**: `k̄` is continuous on `(0,∞)`, whatever the jumps of `k`.
The nonincreasing `k` has countably many discontinuities, each met by `r₀√(1+u²)` for at most two
`u`; off that countable set the integrand is continuous in `r` at `r₀`, and for `r > r₀/2` it is
dominated by `k(r₀/2)(1+u²)^{-(d+1)/2}`. -/
theorem shadowProfile_continuousOn (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) : ContinuousOn (shadowProfile d k) (Ioi 0) := by
  intro r₀ (hr₀ : 0 < r₀)
  refine ContinuousAt.continuousWithinAt ?_
  change ContinuousAt (fun r => sphereArea d / sphereArea (d + 1) *
    ∫ u : ℝ, k (r * Real.sqrt (1 + u ^ 2)) * shadowWeight d u) r₀
  refine continuousAt_const.mul ?_
  have hT : {t ∈ Ioi (0 : ℝ) | ¬ ContinuousWithinAt k (Ioi 0) t}.Countable :=
    hk.countable_not_continuousWithinAt
  set T := {t ∈ Ioi (0 : ℝ) | ¬ ContinuousWithinAt k (Ioi 0) t} with hTdef
  set N : Set ℝ := {u | r₀ * Real.sqrt (1 + u ^ 2) ∈ T} with hN
  have hNc : N.Countable := by
    refine ((hT.image fun t => Real.sqrt ((t / r₀) ^ 2 - 1)).union
      (hT.image fun t => -Real.sqrt ((t / r₀) ^ 2 - 1))).mono fun u hu => ?_
    have hu' : r₀ * Real.sqrt (1 + u ^ 2) ∈ T := hu
    have hval : Real.sqrt ((r₀ * Real.sqrt (1 + u ^ 2) / r₀) ^ 2 - 1) = |u| := by
      rw [mul_div_cancel_left₀ _ hr₀.ne', Real.sq_sqrt (by positivity), add_sub_cancel_left,
        Real.sqrt_sq_eq_abs]
    rcases le_total 0 u with h0 | h0
    · refine Or.inl ⟨_, hu', ?_⟩
      change Real.sqrt ((r₀ * Real.sqrt (1 + u ^ 2) / r₀) ^ 2 - 1) = u
      rw [hval, abs_of_nonneg h0]
    · refine Or.inr ⟨_, hu', ?_⟩
      change -Real.sqrt ((r₀ * Real.sqrt (1 + u ^ 2) / r₀) ^ 2 - 1) = u
      rw [hval, abs_of_nonpos h0, neg_neg]
  have hNnull : ∀ᵐ u : ℝ, u ∉ N := compl_mem_ae_iff.2 (hNc.measure_zero volume)
  refine continuousAt_of_dominated (bound := fun u => k (r₀ / 2) * shadowWeight d u) ?_ ?_
    ((integrable_shadowWeight hd).const_mul _) ?_
  · filter_upwards [Ioi_mem_nhds hr₀] with r hr
    exact (shadow_integrable hd hk0 hk hr).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show r₀ / 2 < r₀ by linarith)] with r hr
    refine ae_of_all _ fun u => ?_
    have hr2 : r₀ / 2 < r := hr
    have hr0 : 0 < r := lt_trans (by linarith) hr2
    have hpos := mul_sqrt_one_add_sq_pos hr0 u
    rw [Real.norm_of_nonneg (mul_nonneg (hk0 _ hpos) (shadowWeight_pos d u).le)]
    exact mul_le_mul_of_nonneg_right (hk (show (0 : ℝ) < r₀ / 2 by linarith) hpos
      (hr2.le.trans (le_mul_sqrt_one_add_sq hr0.le u))) (shadowWeight_pos d u).le
  · filter_upwards [hNnull] with u hu
    have hpos := mul_sqrt_one_add_sq_pos hr₀ u
    have hc : ContinuousAt k (r₀ * Real.sqrt (1 + u ^ 2)) := by
      by_contra hcon
      exact hu ⟨hpos, fun hw =>
        hcon ((continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hpos)).1 hw)⟩
    exact (ContinuousAt.comp (f := fun r : ℝ => r * Real.sqrt (1 + u ^ 2)) hc
      (by fun_prop)).mul continuousAt_const

/-- The profile of the shadow as a lower integral: `k̄(r) = h̄(r)` for `h = k` cut off to `0` off
`(0,∞)`. -/
theorem ofReal_shadowProfile (hd : 1 ≤ d) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hk : AntitoneOn k (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (shadowProfile d k r)
      = shadowL d (fun t => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator k t)) r := by
  have hA := (sphereArea_eq_toSphere hd).2
  have hA' := (sphereArea_eq_toSphere (d := d + 1) (by omega)).2
  rw [shadowProfile, shadowL, ENNReal.ofReal_mul (div_nonneg hA.le hA'.le),
    ofReal_integral_eq_lintegral_ofReal (shadow_integrable hd hk0 hk hr)
      (ae_of_all _ fun u => mul_nonneg (hk0 _ (mul_sqrt_one_add_sq_pos hr u))
        (shadowWeight_pos d u).le)]
  congr 1
  refine lintegral_congr fun u => ?_
  rw [indicator_of_mem (show r * Real.sqrt (1 + u ^ 2) ∈ Ioi (0 : ℝ) from
    mul_sqrt_one_add_sq_pos hr u), ENNReal.ofReal_mul (hk0 _ (mul_sqrt_one_add_sq_pos hr u))]

end Profile

/-! ## The shadow of a datum -/

namespace OriginDatum

/-- The radial density of `ν_d` as a product, `1/(|S^{d-1}||x|^d) · k_d(|x|)`, with `k_d` cut off
to `0` off `(0,∞)`; at the origin both sides are `0`. -/
theorem levyDensity_eq (hd : 1 ≤ d) (D : OriginDatum d) (x : Rd d) :
    ({0}ᶜ : Set (Rd d)).indicator
        (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x
      = ENNReal.ofReal (1 / (sphereArea d * ‖x‖ ^ d)) *
        ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D.k ‖x‖) := by
  have hA := (sphereArea_eq_toSphere hd).2
  by_cases hx : x = 0
  · subst hx
    simp [show d ≠ 0 by omega]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [indicator_of_mem (show x ∈ ({0}ᶜ : Set (Rd d)) from hx),
      indicator_of_mem (show ‖x‖ ∈ Ioi (0 : ℝ) from hpos), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

/-- **The shadow of a datum** (`lem:shadow-polar-profile`(3)): for an isotropic origin datum
`(a, k')` in dimension `d + 1`, the pair `(a, k̄)` is an isotropic origin datum in dimension `d`.
The two integrability conditions follow from `k̄ ≤ k'`. -/
noncomputable def shadow (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) : OriginDatum d where
  a := D'.a
  k := shadowProfile d D'.k
  a_nonneg := D'.a_nonneg
  k_nonneg := fun _ hr => shadowProfile_nonneg hd D'.k_nonneg hr
  k_antitone := shadowProfile_antitoneOn hd D'.k_nonneg D'.k_antitone
  integrable_near_zero := by
    refine ne_top_of_le_ne_top D'.integrable_near_zero
      (setLIntegral_mono' measurableSet_Ioo fun r hr => ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (shadowProfile_le hd D'.k_nonneg D'.k_antitone hr.1) hr.1.le
  integrable_at_top := by
    refine ne_top_of_le_ne_top D'.integrable_at_top
      (setLIntegral_mono' measurableSet_Ioi fun r hr => ENNReal.ofReal_le_ofReal ?_)
    have hr0 : 0 < r := lt_trans one_pos hr
    exact div_le_div_of_nonneg_right (shadowProfile_le hd D'.k_nonneg D'.k_antitone hr0) hr0.le

@[simp] theorem shadow_a (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) : (D'.shadow hd).a = D'.a := rfl

@[simp] theorem shadow_k (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) :
    (D'.shadow hd).k = shadowProfile d D'.k := rfl

/-- **`lem:shadow-polar-profile`(3), the image**: `∫ g(Πz) ν'(dz) = ∫ g dν̄` for every
nonnegative Borel `g` on `ℝ^d`. This is `eq:shadow-identity` with `h = k'`. -/
theorem lintegral_dropLast_levyMeasure (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) (g : Rd d → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ z, g (dropLast d z) ∂D'.levyMeasure = ∫⁻ x, g x ∂(D'.shadow hd).levyMeasure := by
  set h : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D'.k t) with hh
  have hhm : Measurable h :=
    (measurable_indicator_Ioi_of_antitoneOn D'.k_antitone).ennreal_ofReal
  rw [OriginDatum.levyMeasure, OriginDatum.levyMeasure,
    lintegral_withDensity_eq_lintegral_mul _ D'.measurable_levyDensity
      (show Measurable fun z : Rd (d + 1) => g (dropLast d z) from
        hg.comp continuous_dropLast.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (D'.shadow hd).measurable_levyDensity hg]
  simp only [Pi.mul_apply]
  have hL : ∀ z : Rd (d + 1), ({0}ᶜ : Set (Rd (d + 1))).indicator
      (fun z => ENNReal.ofReal (D'.k ‖z‖ / (sphereArea (d + 1) * ‖z‖ ^ (d + 1)))) z *
        g (dropLast d z)
      = g (dropLast d z) *
        (ENNReal.ofReal (1 / (sphereArea (d + 1) * ‖z‖ ^ (d + 1))) * h ‖z‖) := fun z => by
    rw [D'.levyDensity_eq (by omega), mul_comm]
  have hR : ∀ x : Rd d, ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal ((D'.shadow hd).k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x * g x
      = g x * (ENNReal.ofReal (1 / (sphereArea d * ‖x‖ ^ d)) * shadowL d h ‖x‖) := fun x => by
    rw [(D'.shadow hd).levyDensity_eq hd, mul_comm]
    by_cases hx : x = 0
    · subst hx
      simp [show d ≠ 0 by omega]
    · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      rw [indicator_of_mem (show ‖x‖ ∈ Ioi (0 : ℝ) from hpos), shadow_k,
        ofReal_shadowProfile hd D'.k_nonneg D'.k_antitone hpos]
  rw [lintegral_congr hL, lintegral_congr hR]
  exact lintegral_shadow hd g hg h hhm

/-- **`lem:shadow-polar-profile`(3), the Lévy measure**: `ν̄` is the image of `ν'` under the
projection `Π` on the first `d` coordinates, and the image gives the origin no mass:
`ν'({z : Πz = 0}) = 0`. So the restriction of the image to `ℝ^d ∖ {0}` removes nothing. -/
theorem shadow_levyMeasure (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) :
    D'.levyMeasure.map (dropLast d) = (D'.shadow hd).levyMeasure ∧
      D'.levyMeasure (dropLast d ⁻¹' {0}) = 0 := by
  have hmap : D'.levyMeasure.map (dropLast d) = (D'.shadow hd).levyMeasure := by
    refine Measure.ext fun B hB => ?_
    rw [← lintegral_indicator_one hB, ← lintegral_indicator_one hB,
      lintegral_map (measurable_one.indicator hB) continuous_dropLast.measurable]
    exact D'.lintegral_dropLast_levyMeasure hd _ (measurable_one.indicator hB)
  refine ⟨hmap, ?_⟩
  rw [← Measure.map_apply continuous_dropLast.measurable (measurableSet_singleton 0), hmap]
  exact (D'.shadow hd).levyMeasure_zero

/-- **`lem:shadow-polar-profile`(3), the exponent**: the exponent of `(a, k̄)` is
`ξ ↦ F'((ξ, 0))`. -/
theorem shadow_exponent (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) (ξ : Rd d) :
    (D'.shadow hd).exponent ξ = D'.exponent (padZero d ξ) := by
  rw [OriginDatum.exponent, OriginDatum.exponent, OriginDatum.exponentL, OriginDatum.exponentL,
    norm_padZero, shadow_a,
    ← D'.lintegral_dropLast_levyMeasure hd (fun x => ENNReal.ofReal (1 - Real.cos (inner ℝ ξ x)))
      (by fun_prop)]
  congr 2
  refine lintegral_congr fun z => ?_
  rw [inner_dropLast]

/-- **`lem:shadow-polar-profile`, "in particular"**: if `F'(ζ) = F(|ζ|)`, the shadow has the
exponent `ξ ↦ F(|ξ|)`. -/
theorem shadow_exponent_radial (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) {F : ℝ → ℝ}
    (hF : ∀ ζ : Rd (d + 1), F ‖ζ‖ = D'.exponent ζ) (ξ : Rd d) :
    F ‖ξ‖ = (D'.shadow hd).exponent ξ := by
  rw [D'.shadow_exponent hd, ← hF, norm_padZero]

/-- **`lem:shadow-polar-profile`(2), the limit at the origin**: `k̄(0+) = k'(0+)` in `[0,∞]`. As
`r ↓ 0`, `k'(r√(1+u²))` increases to `k'(0+)` for every `u`; monotone convergence along
`r = 1/(n+1)` and the normalisation give `sup k̄ = k'(0+)`. -/
theorem shadow_profileAtOrigin (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) :
    (D'.shadow hd).profileAtOrigin = D'.profileAtOrigin := by
  refine le_antisymm (iSup_le fun r => ?_) ?_
  · exact (ENNReal.ofReal_le_ofReal (shadowProfile_le hd D'.k_nonneg D'.k_antitone r.2)).trans
      (le_iSup (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (D'.k r)) r)
  set h : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D'.k t) with hh
  have hhm : Measurable h :=
    (measurable_indicator_Ioi_of_antitoneOn D'.k_antitone).ennreal_ofReal
  have hw : Measurable (shadowWeight d) := (continuous_shadowWeight d).measurable
  have hhk : ∀ t : ℝ, 0 < t → h t = ENNReal.ofReal (D'.k t) := fun t ht => by
    rw [hh]; simp only; rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  have hhanti : ∀ s t : ℝ, 0 < s → s ≤ t → h t ≤ h s := fun s t hs hst => by
    rw [hhk s hs, hhk t (hs.trans_le hst)]
    exact ENNReal.ofReal_le_ofReal (D'.k_antitone hs (hs.trans_le hst) hst)
  have hrn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  -- along `r = 1/(n+1)` the values `k'(rs)` increase to `k'(0+)`
  have hsup : ∀ s : ℝ, 0 < s → ⨆ n : ℕ, h (1 / ((n : ℝ) + 1) * s) = D'.profileAtOrigin := by
    intro s hs
    refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun r => ?_)
    · rw [hhk _ (mul_pos (hrn n) hs)]
      exact le_iSup (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (D'.k r))
        ⟨_, mul_pos (hrn n) hs⟩
    · have hr : (0 : ℝ) < r := r.2
      obtain ⟨n, hn⟩ := exists_nat_gt (s / r)
      have hle : 1 / ((n : ℝ) + 1) * s ≤ r := by
        rw [div_lt_iff₀ hr] at hn
        rw [one_div, inv_mul_le_iff₀ (by positivity)]
        nlinarith
      refine le_trans ?_ (le_iSup (fun n : ℕ => h (1 / ((n : ℝ) + 1) * s)) n)
      rw [← hhk _ hr]
      exact hhanti _ _ (mul_pos (hrn n) hs) hle
  have hmono : Monotone fun (n : ℕ) (u : ℝ) =>
      h (1 / ((n : ℝ) + 1) * Real.sqrt (1 + u ^ 2)) * ENNReal.ofReal (shadowWeight d u) := by
    intro n m hnm u
    have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    refine mul_le_mul_left (hhanti _ _ (mul_pos (hrn m) hs)
      (mul_le_mul_of_nonneg_right ?_ hs.le)) _
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmeas : ∀ n : ℕ, Measurable fun u : ℝ =>
      h (1 / ((n : ℝ) + 1) * Real.sqrt (1 + u ^ 2)) * ENNReal.ofReal (shadowWeight d u) :=
    fun n => (hhm.comp (by fun_prop)).mul hw.ennreal_ofReal
  have hcalc : D'.profileAtOrigin = ⨆ n : ℕ, shadowL d h (1 / ((n : ℝ) + 1)) := by
    simp only [shadowL]
    rw [← ENNReal.mul_iSup, ← lintegral_iSup hmeas hmono]
    have hpt : ∀ u : ℝ, ⨆ n : ℕ, h (1 / ((n : ℝ) + 1) * Real.sqrt (1 + u ^ 2)) *
        ENNReal.ofReal (shadowWeight d u)
        = D'.profileAtOrigin * ENNReal.ofReal (shadowWeight d u) := fun u => by
      rw [← ENNReal.iSup_mul, hsup _ (Real.sqrt_pos.2 (by positivity))]
    rw [lintegral_congr hpt, lintegral_const_mul _ hw.ennreal_ofReal, mul_left_comm,
      shadowWeight_lintegral hd, mul_one]
  rw [hcalc]
  refine iSup_le fun n => ?_
  rw [← ofReal_shadowProfile hd D'.k_nonneg D'.k_antitone (hrn n)]
  exact le_iSup (fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((D'.shadow hd).k r)) ⟨_, hrn n⟩

end OriginDatum

/-! ## The clauses of `lem:shadow-polar-profile` -/

/-- **`lem:shadow-polar-profile`(1)**: `C_d ∫_ℝ (1+u²)^{-(d+1)/2} du = 1`, and for every datum
`(a, k')` in dimension `d + 1` and every `r > 0`, `0 ≤ k̄(r) ≤ k'(r)`. -/
theorem shadow_profile_mean (hd : 1 ≤ d) :
    sphereArea d / sphereArea (d + 1) * ∫ u : ℝ, (1 + u ^ 2) ^ (-((d : ℝ) + 1) / 2) = 1 ∧
      ∀ D' : OriginDatum (d + 1), ∀ r : ℝ, 0 < r →
        0 ≤ shadowProfile d D'.k r ∧ shadowProfile d D'.k r ≤ D'.k r :=
  ⟨shadowWeight_normalisation hd, fun D' _ hr =>
    ⟨shadowProfile_nonneg hd D'.k_nonneg hr, shadowProfile_le hd D'.k_nonneg D'.k_antitone hr⟩⟩

/-- **`lem:shadow-polar-profile`(2)**: `k̄` is nonincreasing and continuous on `(0,∞)`, and
`k̄(0+) = k'(0+)` in `[0,∞]`: `k̄(r) → k'(0+)` as `r ↓ 0`, where `k'(0+)` is
`OriginDatum.profileAtOrigin`, the right limit of `k'` at `0`
(`OriginDatum.tendsto_profileAtOrigin`). -/
theorem shadow_profile_regular (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) :
    AntitoneOn (shadowProfile d D'.k) (Ioi 0) ∧ ContinuousOn (shadowProfile d D'.k) (Ioi 0) ∧
      Tendsto (fun r => ENNReal.ofReal (shadowProfile d D'.k r)) (𝓝[>] 0)
        (𝓝 D'.profileAtOrigin) := by
  refine ⟨shadowProfile_antitoneOn hd D'.k_nonneg D'.k_antitone,
    shadowProfile_continuousOn hd D'.k_nonneg D'.k_antitone, ?_⟩
  have h := (D'.shadow hd).tendsto_profileAtOrigin
  rw [D'.shadow_profileAtOrigin hd] at h
  exact h

/-- **`lem:shadow-polar-profile`(3)**: `(a, k̄)` is an isotropic origin datum in dimension `d`
(`OriginDatum.shadow`, with Gaussian coefficient `a` and profile `k̄`); its Lévy measure is the
image of `ν'` under the projection `Π`, as an identity of integrals and of measures, and the
image gives the origin no mass; its exponent is `ξ ↦ F'((ξ,0))`; and if `F'(ζ) = F(|ζ|)`, its
exponent is `ξ ↦ F(|ξ|)`. -/
theorem shadow_datum (hd : 1 ≤ d) (D' : OriginDatum (d + 1)) :
    (D'.shadow hd).a = D'.a ∧ (D'.shadow hd).k = shadowProfile d D'.k ∧
      (∀ g : Rd d → ℝ≥0∞, Measurable g →
        ∫⁻ z, g (dropLast d z) ∂D'.levyMeasure = ∫⁻ x, g x ∂(D'.shadow hd).levyMeasure) ∧
      D'.levyMeasure.map (dropLast d) = (D'.shadow hd).levyMeasure ∧
      D'.levyMeasure (dropLast d ⁻¹' {0}) = 0 ∧
      (∀ ξ : Rd d, (D'.shadow hd).exponent ξ = D'.exponent (padZero d ξ)) ∧
      ∀ F : ℝ → ℝ, (∀ ζ : Rd (d + 1), F ‖ζ‖ = D'.exponent ζ) →
        ∀ ξ : Rd d, F ‖ξ‖ = (D'.shadow hd).exponent ξ :=
  ⟨rfl, rfl, fun g hg => D'.lintegral_dropLast_levyMeasure hd g hg, (D'.shadow_levyMeasure hd).1,
    (D'.shadow_levyMeasure hd).2, fun ξ => D'.shadow_exponent hd ξ,
    fun _ hF ξ => D'.shadow_exponent_radial hd hF ξ⟩

end AffineHemigroup
