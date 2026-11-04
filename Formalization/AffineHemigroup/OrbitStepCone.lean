/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.EllipticalStable
import AffineHemigroup.PathCondition
import AffineHemigroup.Polar
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import AffineHemigroup.RadialProfileDatum

/-!
# `prop:orbit-step-cone`: the ordered-density cone of an affine orbit

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:orbit-step-cone` (wave 2, group C, Q-0281).
The law of a radial profile and its increments exist by ledger A3(iii), through the symmetric
triplet of a density (`AffineHemigroup.EllipticalStable`); the cone is a substitution and the
monotonicity of `m`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## A generic increment of two ordered densities -/

/-- **The increment of two ordered even densities** `n₀ ≤ n₁` (A3(iii)): a law with triplet
`(0, (n₁ - n₀)(x)dx, 0)` and transform `exp(-(I₁ - I₀))`, `I_j = ∫ (1 - cos⟨ω,x⟩) n_j(x) dx`. -/
theorem exists_density_increment [NeZero d] (n₀ n₁ : Rd d → ℝ) (h₀ : Measurable n₀)
    (h₁ : Measurable n₁) (hn₀ : ∀ x, 0 ≤ n₀ x) (hord : ∀ x : Rd d, x ≠ 0 → n₀ x ≤ n₁ x)
    (heven₀ : ∀ x, n₀ (-x) = n₀ x) (heven₁ : ∀ x, n₁ (-x) = n₁ x)
    (hfin₁ : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n₁ x) ≠ ⊤)
    (hI₁ : ∀ ω : Rd d,
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₁ x) ≠ ⊤) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
      (∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity
          (fun x => ENNReal.ofReal (n₁ x - n₀ x)) ∧ T.γ = 0 ∧ HasTriplet ρ T) ∧
      ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-((∫⁻ x in ({0}ᶜ : Set (Rd d)),
        ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₁ x)).toReal -
        (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₀ x)).toReal))
          : ℝ) : ℂ) := by
  set n : Rd d → ℝ := fun x => n₁ x - n₀ x with hn
  have hnm : Measurable n := h₁.sub h₀
  have hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * n x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin₁ (setLIntegral_mono' (measurableSet_singleton 0).compl
      fun x _ => ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (by simp only [hn]; linarith [hn₀ x]) (by positivity)
  have heven : ∀ x, n (-x) = n x := fun x => by simp only [hn, heven₀, heven₁]
  obtain ⟨ρ, hprob, hid, hT, hchar⟩ := exists_law_densTriplet n hnm hfin heven
  refine ⟨ρ, hprob, hid, ⟨_, rfl, rfl, rfl, hT⟩, fun ω => ?_⟩
  rw [hchar ω]
  congr 3
  have hnn : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪ω, x⟫ := fun x => by
    linarith [Real.cos_le_one ⟪ω, x⟫]
  have hadd : (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n x)) +
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₀ x) =
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₁ x) := by
    rw [← lintegral_add_right _ (Measurable.ennreal_ofReal
      ((by fun_prop : Measurable fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).mul h₀))]
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    rw [← ENNReal.ofReal_add (mul_nonneg (hnn x) (by simp only [hn]; linarith [hord x hx]))
      (mul_nonneg (hnn x) (hn₀ x))]
    congr 1
    simp only [hn]
    ring
  have hfin1 : (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n x)) ≠ ⊤ :=
    ne_top_of_le_ne_top (hI₁ ω) (hadd ▸ le_self_add)
  have hfin0 : (∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * n₀ x)) ≠ ⊤ :=
    ne_top_of_le_ne_top (hI₁ ω) (hadd ▸ le_add_self)
  have := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hfin1 hfin0] at this
  linarith

/-! ## The radial profile -/

namespace RadialProfile

theorem m_nonneg (hd : 1 ≤ d) (K : RadialProfile d) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ K.m r := by
  rcases hr.lt_or_eq with hr | rfl
  · exact div_nonneg (K.k_nonneg r hr) (by positivity)
  · simp [m, zero_pow (by omega : d ≠ 0)]

theorem orbitDensity_nonneg (hd : 1 ≤ d) (K : RadialProfile d) {S : Mat d} (hS : S.PosDef)
    (x : Rd d) : 0 ≤ K.orbitDensity S x :=
  mul_nonneg (Real.rpow_nonneg hS.det_pos.le _) (K.m_nonneg hd (norm_nonneg _))

theorem measurable_orbitDensity (hd : 1 ≤ d) (K : RadialProfile d) (S : Mat d) :
    Measurable (K.orbitDensity S) :=
  measurable_const.mul ((K.measurable_m_norm hd).comp (lin (msqrt S)⁻¹).continuous.measurable)

theorem orbitDensity_neg (K : RadialProfile d) (S : Mat d) (x : Rd d) :
    K.orbitDensity S (-x) = K.orbitDensity S x := by
  simp [orbitDensity]

/-- `|Σ^{-1/2}x|² = ⟨x, Σ⁻¹x⟩`. -/
theorem _root_.AffineHemigroup.norm_sq_lin_msqrt_inv {S : Mat d} (hS : S.PosDef) (x : Rd d) :
    ‖lin (msqrt S)⁻¹ x‖ ^ 2 = quad S⁻¹ x := by
  have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  rw [← quad_inv_lin_msqrt hS, lin_mul_inv_apply hU]

/-- **The substitution `x = Σ^{1/2}y`**: `∫ G(x) n_Σ(x) dx = ∫ G(Σ^{1/2}y) m(|y|) dy`. -/
theorem lintegral_orbitDensity (hd : 1 ≤ d) (K : RadialProfile d) {S : Mat d} (hS : S.PosDef)
    (G : Rd d → ℝ) (hG : Measurable G) :
    ∫⁻ x, ENNReal.ofReal (G x * K.orbitDensity S x) =
      ∫⁻ y, ENNReal.ofReal (G (lin (msqrt S) y) * K.m ‖y‖) := by
  set A := msqrt S with hA
  have hdA : A.det ≠ 0 := (msqrt_mem_glSet hS).ne_zero
  have hU : IsUnit A.det := msqrt_mem_glSet hS
  have hdS := hS.det_pos
  have hmeas : Measurable fun x => ENNReal.ofReal (G x * K.orbitDensity S x) :=
    (hG.mul (K.measurable_orbitDensity hd S)).ennreal_ofReal
  have h := lintegral_comp_lin hdA hmeas
  rw [abs_det_msqrt hS] at h
  have hpt : ∀ y : Rd d, ENNReal.ofReal (G (lin A y) * K.orbitDensity S (lin A y)) =
      ENNReal.ofReal (S.det ^ (-(1 : ℝ) / 2)) * ENNReal.ofReal (G (lin A y) * K.m ‖y‖) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), orbitDensity, ← hA, lin_inv_mul_apply hU]
    congr 1
    ring
  simp_rw [hpt] at h
  have hm2 : Measurable fun y : Rd d => ENNReal.ofReal (G (lin A y) * K.m ‖y‖) :=
    ((hG.comp (lin A).continuous.measurable).mul (K.measurable_m_norm hd)).ennreal_ofReal
  rw [lintegral_const_mul _ hm2] at h
  have hK : (S.det ^ ((1 : ℝ) / 2))⁻¹ = S.det ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg hdS.le]; ring_nf
  rw [← hK] at h
  have hne : ENNReal.ofReal (S.det ^ ((1 : ℝ) / 2))⁻¹ ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hnt : ENNReal.ofReal (S.det ^ ((1 : ℝ) / 2))⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  exact ((ENNReal.mul_right_inj hne hnt).1 h).symm

/-- `1 - cos⟨ω,x⟩ ≤ (2 + |ω|²)(|x|² ∧ 1)`. -/
theorem _root_.AffineHemigroup.one_sub_cos_le_min (ω x : Rd d) :
    1 - Real.cos ⟪ω, x⟫ ≤ (2 + ‖ω‖ ^ 2) * min (‖x‖ ^ 2) 1 := by
  have hc1 : 1 - Real.cos ⟪ω, x⟫ ≤ ⟪ω, x⟫ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := ⟪ω, x⟫)]
  have hc2 : 1 - Real.cos ⟪ω, x⟫ ≤ 2 := by linarith [Real.neg_one_le_cos ⟪ω, x⟫]
  have hin : ⟪ω, x⟫ ^ 2 ≤ ‖ω‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact sq_le_sq' (by linarith [neg_abs_le ⟪ω, x⟫, abs_real_inner_le_norm ω x])
      (le_trans (le_abs_self _) (abs_real_inner_le_norm ω x))
  rcases le_or_gt (‖x‖ ^ 2) 1 with h | h
  · rw [min_eq_left h]
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖ω‖]
  · rw [min_eq_right h.le, mul_one]
    nlinarith [sq_nonneg ‖ω‖]

/-- **`ψ_I` is finite** (`prop:orbit-step-cone`(1)). -/
theorem exponentL_ne_top (hd : 1 ≤ d) (K : RadialProfile d) (ω : Rd d) : K.exponentL ω ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 + ‖ω‖ ^ 2))
    K.integrable) (le_trans (lintegral_mono fun x => ?_)
      (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm := K.m_nonneg hd (norm_nonneg x)
  calc (1 - Real.cos ⟪ω, x⟫) * K.m ‖x‖ ≤ ((2 + ‖ω‖ ^ 2) * min (‖x‖ ^ 2) 1) * K.m ‖x‖ :=
        mul_le_mul_of_nonneg_right (one_sub_cos_le_min ω x) hm
    _ = (2 + ‖ω‖ ^ 2) * (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d)) := by rw [m]; ring

/-- `∫ (|x|² ∧ 1) n_Σ(x) dx < ∞` (`prop:orbit-step-cone`(1)). -/
theorem orbitDensity_integrable (hd : 1 ≤ d) (K : RadialProfile d) {S : Mat d} (hS : S.PosDef) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1 * K.orbitDensity S x) ≠ ⊤ := by
  haveI : NeZero d := ⟨by omega⟩
  rw [K.lintegral_orbitDensity hd hS _ (by fun_prop)]
  set L := max (lamMax S) 1 with hLdef
  have hlam : ∀ y : Rd d, quad S y ≤ lamMax S * ‖y‖ ^ 2 := fun y => by
    have h := quad_nonneg ((posSemidef_smul_one_sub_iff hS.isHermitian
      (eigUp S (Fin.rev 0))).2 le_rfl) y
    rw [quad_sub, quad_smul, quad_one] at h
    rw [lamMax_eq_eigUp_last hS.isHermitian]
    linarith
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := L))
    K.integrable) (le_trans (lintegral_mono fun y => ?_)
      (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm := K.m_nonneg hd (norm_nonneg y)
  have h1 : min (‖lin (msqrt S) y‖ ^ 2) 1 ≤ L * min (‖y‖ ^ 2) 1 := by
    rw [norm_sq_lin_msqrt hS.posSemidef]
    rcases le_or_gt (‖y‖ ^ 2) 1 with hy | hy
    · rw [min_eq_left hy]
      calc min (quad S y) 1 ≤ quad S y := min_le_left _ _
        _ ≤ lamMax S * ‖y‖ ^ 2 := hlam y
        _ ≤ L * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · rw [min_eq_right hy.le, mul_one]
      exact (min_le_right _ _).trans (le_max_right _ _)
  calc min (‖lin (msqrt S) y‖ ^ 2) 1 * K.m ‖y‖ ≤ (L * min (‖y‖ ^ 2) 1) * K.m ‖y‖ :=
        mul_le_mul_of_nonneg_right h1 hm
    _ = L * (min (‖y‖ ^ 2) 1 * (K.k ‖y‖ / ‖y‖ ^ d)) := by rw [m]; ring

/-- **The exponent along the orbit**: `ψ_I(Σ^{1/2}ω) = ∫ (1 - cos⟨ω,x⟩) n_Σ(x) dx`. -/
theorem exponentL_lin_msqrt (hd : 1 ≤ d) (K : RadialProfile d) {S : Mat d} (hS : S.PosDef)
    (ω : Rd d) :
    K.exponentL (lin (msqrt S) ω) =
      ∫⁻ x, ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.orbitDensity S x) := by
  rw [K.lintegral_orbitDensity hd hS _ (by fun_prop), exponentL]
  refine lintegral_congr fun y => ?_
  rw [inner_lin_left, msqrt_transpose]

end RadialProfile

/-! ## The dilation ratio and the law (`prop:orbit-step-cone`, (1)) -/

/-- The index set of the dilation ratio is nonempty. -/
theorem RadialProfile.exists_pos (K : RadialProfile d) : ∃ r : ℝ, 0 < r ∧ 0 < K.k r := by
  obtain ⟨r, hr, hk⟩ := K.k_ne_zero
  exact ⟨r, hr, lt_of_le_of_ne (K.k_nonneg r hr) (Ne.symm hk)⟩

/-- **`prop:orbit-step-cone`**, the dilation ratio: for `λ ≥ 1` the quotients `k(r/λ)/k(r)` are
bounded below and `R(λ) ∈ [1,∞)`. -/
theorem dilRatio_mem (_hd : 1 ≤ d) (K : RadialProfile d) (lam : ℝ) (hlam : 1 ≤ lam) :
    BddBelow (range fun r : {r : ℝ // 0 < r ∧ 0 < K.k r} => K.k (r.1 / lam) / K.k r.1) ∧
      1 ≤ dilRatio K.k lam := by
  have hq : ∀ r : {r : ℝ // 0 < r ∧ 0 < K.k r}, 1 ≤ K.k (r.1 / lam) / K.k r.1 := by
    rintro ⟨r, hr, hk⟩
    rw [one_le_div hk]
    exact K.k_antitone (div_pos hr (by linarith)) hr (div_le_self hr.le hlam)
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨r0, hr0, hk0⟩⟩
  exact ⟨⟨1, by rintro _ ⟨r, rfl⟩; exact hq r⟩, le_ciInf hq⟩

/-- The law of `K` as a law of the triplet `(0, m(|x|)dx, 0)`. -/
theorem exists_profileLaw (hd : 1 ≤ d) (K : RadialProfile d) :
    ∃ μ : Measure (Rd d), IsProfileLaw K μ ∧ IsInfinitelyDivisible μ ∧
      ∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = volume.withDensity (fun x => ENNReal.ofReal (K.m ‖x‖)) ∧ T.γ = 0 ∧
        HasTriplet μ T := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  have hfin : ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal (min (‖x‖ ^ 2) 1 * K.m ‖x‖) ≠ ⊤ := by
    rw [restrict_compl_singleton]; exact K.integrable
  obtain ⟨μ, hprob, hid, hT, hchar⟩ := exists_law_densTriplet (fun x => K.m ‖x‖)
    (K.measurable_m_norm hd) hfin (fun x => by simp)
  refine ⟨μ, ⟨hprob, fun ω => ?_⟩, hid, _, rfl, ?_, rfl, hT⟩
  · rw [hchar ω, restrict_compl_singleton]; rfl
  · change (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity _ = _
    rw [restrict_compl_singleton]

/-- **`prop:orbit-step-cone`(1)**, the law: `ψ_I` is finite, and there is a unique probability
measure `μ_I` with `μ̂_I = e^{-ψ_I}`. Spends A3(iii). -/
theorem profileLaw_exists_unique (hd : 1 ≤ d) (K : RadialProfile d) :
    (∀ ω : Rd d, K.exponentL ω ≠ ⊤) ∧ ∃! μ : Measure (Rd d), IsProfileLaw K μ := by
  refine ⟨K.exponentL_ne_top hd, ?_⟩
  obtain ⟨μ, hμ, -⟩ := exists_profileLaw hd K
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  haveI := hμ.1
  haveI := hν.1
  exact eq_of_charFun_eq fun ω => by rw [hμ.2, hν.2]

theorem IsProfileLaw.eq {K : RadialProfile d} {μ ν : Measure (Rd d)} (hμ : IsProfileLaw K μ)
    (hν : IsProfileLaw K ν) : μ = ν := by
  haveI := hμ.1
  haveI := hν.1
  exact eq_of_charFun_eq fun ω => by rw [hμ.2, hν.2]

/-- The transform of the orbit of the law of `K`. -/
theorem charFun_affineOrbit_profile (hd : 1 ≤ d) (K : RadialProfile d) {μI : Measure (Rd d)}
    (hμI : IsProfileLaw K μI) {S : Mat d} (hS : S.PosDef) (ω : Rd d) :
    charFun (affineOrbit μI S) ω = ((Real.exp (-(∫⁻ x,
      ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.orbitDensity S x)).toReal) : ℝ) : ℂ) := by
  haveI := hμI.1
  rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hS), hμI.2, msqrt_transpose,
    RadialProfile.exponent, K.exponentL_lin_msqrt hd hS]

/-- **`prop:orbit-step-cone`(1)**, the orbit: the law `μ_I` of `K` is rotation invariant and
infinitely divisible with generating triplet `(0, m(|x|)dx, 0)`, and its orbit has
`μ̂_Σ(ω) = exp[-∫(1 - cos⟨ω,x⟩) n_Σ(x) dx]`. -/
theorem profileLaw_props (hd : 1 ≤ d) (K : RadialProfile d) (μI : Measure (Rd d))
    (hμI : IsProfileLaw K μI) :
    IsRotationInvariant μI ∧ IsInfinitelyDivisible μI ∧
      (∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = volume.withDensity (fun x => ENNReal.ofReal (K.m ‖x‖)) ∧ T.γ = 0 ∧ HasTriplet μI T) ∧
      ∀ S : Mat d, S.PosDef → ∀ ω : Rd d,
        charFun (affineOrbit μI S) ω = ((Real.exp (-(∫⁻ x,
          ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.orbitDensity S x)).toReal) : ℝ) : ℂ) := by
  obtain ⟨μ, hμ, hid, hT⟩ := exists_profileLaw hd K
  have he := hμI.eq hμ
  refine ⟨fun Q hQ => ?_, he ▸ hid, he ▸ hT, fun S hS ω =>
    charFun_affineOrbit_profile hd K hμI hS ω⟩
  -- rotation invariance: `ψ(Qᵀω) = ψ(ω)`, by the substitution `x = Qy`
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
  have hQgl := orthSet_subset_glSet hQ
  haveI := hμI.1
  refine eq_of_charFun_eq fun ω => ?_
  rw [charFun_push Q hQgl, hμI.2, hμI.2, RadialProfile.exponent, RadialProfile.exponent]
  congr 4
  have hdet : Qᵀ.det ≠ 0 := by rw [det_transpose]; exact hQgl.ne_zero
  have habs : |Qᵀ.det| = 1 := by
    have h1 : Q.det * Q.det = 1 := by
      have := congrArg Matrix.det hQQ
      rwa [det_mul, det_transpose, det_one] at this
    rw [det_transpose]
    rcases mul_self_eq_one_iff.1 h1 with h | h <;> simp [h]
  have hmeas : Measurable fun x : Rd d =>
      ENNReal.ofReal ((1 - Real.cos ⟪lin Qᵀ ω, x⟫) * K.m ‖x‖) :=
    ((by fun_prop : Measurable fun x : Rd d => 1 - Real.cos ⟪lin Qᵀ ω, x⟫).mul
      (K.measurable_m_norm hd)).ennreal_ofReal
  have h := lintegral_comp_lin hdet hmeas
  rw [habs, inv_one, ENNReal.ofReal_one, one_mul] at h
  rw [RadialProfile.exponentL, ← h, RadialProfile.exponentL]
  refine lintegral_congr fun y => ?_
  have hn : ‖lin Qᵀ y‖ = ‖y‖ := by
    have h2 := sum_sq_lin_transpose hQQ y
    have h3 : ‖lin Qᵀ y‖ ^ 2 = ∑ i, ((lin Qᵀ y) i) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), h3, h2]
  have hQQ' : Qᵀᵀ * Qᵀ = 1 := by rw [transpose_transpose]; exact hQQ
  have hy : lin Qᵀᵀ (lin Qᵀ y) = y := by
    rw [show lin Qᵀᵀ (lin Qᵀ y) = lin (Qᵀᵀ * Qᵀ) y by rw [lin_mul]; rfl, hQQ', lin_one]; rfl
  rw [hn, inner_lin_left, hy]

/-! ## The cone (`prop:orbit-step-cone`(2)) -/

/-- **A profile bounded below at infinity is not integrable**: if `k ≥ c > 0` on `[R,∞)`, then
`∫ (|x|² ∧ 1) m(|x|) dx = ∞` (polar coordinates; `∫_R^∞ dr/r = ∞`). -/
theorem RadialProfile.not_ge_at_infinity (hd : 1 ≤ d) (K : RadialProfile d) {R c : ℝ}
    (hR : 1 ≤ R) (hc : 0 < c) (hk : ∀ s : ℝ, R ≤ s → c ≤ K.k s) : False := by
  apply K.integrable
  set f : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (min (‖x‖ ^ 2) 1 * (K.k ‖x‖ / ‖x‖ ^ d))
  have hfm : Measurable f :=
    ((by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).mul
      (K.measurable_m_norm hd)).ennreal_ofReal
  -- `∫_R^∞ c/r dr = ∞`
  have hinv : ∫⁻ r in Ioi R, ENNReal.ofReal (c / r) = ⊤ := by
    by_contra hfin
    apply not_integrableOn_Ioi_inv (a := R)
    refine ⟨(measurable_inv.aestronglyMeasurable), ?_⟩
    rw [HasFiniteIntegral]
    have hle : ∫⁻ r in Ioi R, ‖r⁻¹‖ₑ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ r in Ioi R, ENNReal.ofReal (c / r) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
      have hr0 : 0 < r := lt_of_lt_of_le (by linarith) (le_of_lt hr)
      rw [← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      field_simp
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin))
  have hsph := (sphereArea_eq_toSphere (d := d) hd)
  have htop : ∀ η : Metric.sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
      f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))) = ⊤ := by
    intro η
    have hη : ‖(η : Rd d)‖ = 1 := by simp
    refine eq_top_iff.2 (hinv ▸ ?_)
    calc ∫⁻ r in Ioi R, ENNReal.ofReal (c / r)
        ≤ ∫⁻ r in Ioi R, f (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
          have hr0 : 0 < r := lt_of_lt_of_le (by linarith) (le_of_lt hr)
          have hr1 : 1 ≤ r := hR.trans (le_of_lt hr)
          have hn : ‖r • (η : Rd d)‖ = r := by rw [norm_smul, hη, mul_one, Real.norm_of_nonneg hr0.le]
          show ENNReal.ofReal (c / r) ≤ ENNReal.ofReal (min (‖r • (η : Rd d)‖ ^ 2) 1 *
            (K.k ‖r • (η : Rd d)‖ / ‖r • (η : Rd d)‖ ^ d)) * ENNReal.ofReal (r ^ (d - 1))
          rw [hn]
          rw [← ENNReal.ofReal_mul (by
            have := K.k_nonneg r hr0
            have : 0 ≤ min (r ^ 2) 1 := by positivity
            positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [min_eq_right (by nlinarith), one_mul]
          have hk' := hk r (le_of_lt hr)
          have hpow : r ^ (d - 1) * r = r ^ d := by
            rw [← pow_succ]; congr 1; omega
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
            div_le_iff₀ hr0]
          calc c * r ^ d = c * (r ^ (d - 1) * r) := by rw [hpow]
            _ ≤ K.k r * r ^ (d - 1) * r := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hk' (by positivity)
      _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi (by linarith))
  rw [lintegral_polar hd f hfm]
  simp_rw [htop]
  rw [lintegral_const, ENNReal.top_mul]
  rw [← hsph.1]
  exact (ENNReal.ofReal_pos.2 hsph.2).ne'

/-- **The ordering in the coordinates of `Σ`**: with `x = Σ^{1/2}y` and `M = Σ^{-1/2}Σ'Σ^{-1/2}`,
`n_Σ ≤ n_{Σ'}` off `0` if and only if `m(|y|) ≤ (det M)^{-1/2} m(⟨y, M⁻¹y⟩^{1/2})` for `y ≠ 0`. -/
theorem orbitDensity_le_iff (K : RadialProfile d) {S S' : Mat d} (hS : S.PosDef)
    (hS' : S'.PosDef) :
    (∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔
      ∀ y : Rd d, y ≠ 0 → K.m ‖y‖ ≤
        (relStep S S').det ^ (-(1 : ℝ) / 2) * K.m (Real.sqrt (quad (relStep S S')⁻¹ y)) := by
  have hU : IsUnit (msqrt S).det := msqrt_mem_glSet hS
  have hdS := hS.det_pos
  have hdM : (relStep S S').det = S'.det / S.det := det_relStep hS S'
  rw [forall_ne_zero_lin_iff hU]
  refine forall₂_congr fun y _ => ?_
  have h1 : K.orbitDensity S (lin (msqrt S) y) = S.det ^ (-(1 : ℝ) / 2) * K.m ‖y‖ := by
    rw [RadialProfile.orbitDensity, lin_inv_mul_apply hU]
  have h2 : K.orbitDensity S' (lin (msqrt S) y) =
      S'.det ^ (-(1 : ℝ) / 2) * K.m (Real.sqrt (quad (relStep S S')⁻¹ y)) := by
    rw [RadialProfile.orbitDensity, quad_relStep_inv hS, ← norm_sq_lin_msqrt_inv hS',
      Real.sqrt_sq (norm_nonneg _)]
  have h3 : S'.det ^ (-(1 : ℝ) / 2) =
      S.det ^ (-(1 : ℝ) / 2) * (relStep S S').det ^ (-(1 : ℝ) / 2) := by
    rw [hdM, Real.div_rpow hS'.det_pos.le hdS.le,
      mul_div_cancel₀ _ (Real.rpow_pos_of_pos hdS _).ne']
  rw [h1, h2, h3, mul_assoc]
  exact mul_le_mul_iff_right₀ (by positivity)

/-- `R(1) = 1`. -/
theorem dilRatio_one (K : RadialProfile d) : dilRatio K.k 1 = 1 := by
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨r0, hr0, hk0⟩⟩
  unfold dilRatio
  simp_rw [div_one]
  have : ∀ r : {r : ℝ // 0 < r ∧ 0 < K.k r}, K.k r.1 / K.k r.1 = 1 := fun r =>
    div_self r.2.2.ne'
  simp_rw [this]
  exact ciInf_const

/-- **`prop:orbit-step-cone`(2)**, the cone: `n_Σ ≤ n_{Σ'}` off the origin if and only if
`λ_min(M) ≥ 1` and `det M ≤ λ_min(M)^d R(λ_min(M)^{1/2})²`; and then `Σ ≤ Σ'`. -/
theorem orbit_density_order_iff (hd : 1 ≤ d) (K : RadialProfile d) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) :
    ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔
        1 ≤ lamMin (relStep S S') ∧
          (relStep S S').det ≤
            lamMin (relStep S S') ^ d * dilRatio K.k (Real.sqrt (lamMin (relStep S S'))) ^ 2) ∧
      ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) → loewnerLE S S') := by
  haveI : NeZero d := ⟨by omega⟩
  set M := relStep S S' with hMdef
  have hM : M.PosDef := (posDef_relStep_iff hS S').2 hS'
  set ℓ := lamMin M with hℓ
  have hl : 0 < ℓ := lamMin_pos hM
  set lam := Real.sqrt ℓ with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hl
  have hlam2 : lam ^ 2 = ℓ := Real.sq_sqrt hl.le
  have hdM := hM.det_pos
  set D := M.det ^ ((1 : ℝ) / 2) with hD
  have hD0 : 0 < D := by positivity
  have hDinv : M.det ^ (-(1 : ℝ) / 2) = D⁻¹ := by
    rw [hD, ← Real.rpow_neg hdM.le]; ring_nf
  have hD2 : D ^ 2 = M.det := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hdM.le]; norm_num
  have hDge : lam ^ d ≤ D := by
    have h1 := lamMin_pow_le_det hM
    have h2 : (lam ^ d) ^ 2 ≤ D ^ 2 := by
      rw [hD2, ← pow_mul, mul_comm, pow_mul, hlam2]; exact h1
    exact (pow_le_pow_iff_left₀ (by positivity) hD0.le two_ne_zero).1 h2
  have hord_iff := orbitDensity_le_iff K hS hS'
  rw [← hMdef] at hord_iff
  simp_rw [hDinv] at hord_iff
  -- the forward implication's consequences
  have hfwd : (∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) →
      1 ≤ ℓ ∧ M.det ≤ ℓ ^ d * dilRatio K.k lam ^ 2 := by
    intro h
    have h' := hord_iff.1 h
    obtain ⟨v, hv1, hMv⟩ := exists_unit_eigvec_eigUp_zero hM.isHermitian
    rw [← lamMin_eq_eigUp_zero hM.isHermitian, ← hℓ] at hMv
    have hMinv : lin M⁻¹ v = ℓ⁻¹ • v := by
      have hU : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hM.isUnit
      have h1 := congrArg (lin M⁻¹) hMv
      rw [lin_inv_mul_apply hU, map_smul] at h1
      calc lin M⁻¹ v = ℓ⁻¹ • (ℓ • lin M⁻¹ v) := by
            rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
        _ = ℓ⁻¹ • v := by rw [← h1]
    -- `k(r) ≤ D⁻¹ λ^d k(r/λ)` for `r > 0`
    have hP : ∀ r : ℝ, 0 < r → (D / lam ^ d) * K.k r ≤ K.k (r / lam) := by
      intro r hr
      have hy : r • v ≠ 0 := smul_ne_zero hr.ne' (by intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1)
      have h1 := h' (r • v) hy
      have hn : ‖r • v‖ = r := by rw [norm_smul, hv1, mul_one, Real.norm_of_nonneg hr.le]
      have hq : quad M⁻¹ (r • v) = r ^ 2 / ℓ := by
        rw [quad_smul_vec, quad, hMinv, inner_smul_right, real_inner_self_eq_norm_sq, hv1]; ring
      have hs : Real.sqrt (r ^ 2 / ℓ) = r / lam := by
        rw [Real.sqrt_div' _ hl.le, Real.sqrt_sq hr.le]
      rw [hn, hq, hs, RadialProfile.m, RadialProfile.m, div_pow] at h1
      have hrd : 0 < r ^ d := by positivity
      have hld : 0 < lam ^ d := by positivity
      rw [div_le_iff₀ hrd] at h1
      have : K.k r ≤ D⁻¹ * (K.k (r / lam) * lam ^ d) := by
        calc K.k r ≤ D⁻¹ * (K.k (r / lam) / (r ^ d / lam ^ d)) * r ^ d := h1
          _ = D⁻¹ * (K.k (r / lam) * lam ^ d) := by field_simp
      rw [div_mul_eq_mul_div, div_le_iff₀ hld]
      calc D * K.k r ≤ D * (D⁻¹ * (K.k (r / lam) * lam ^ d)) := mul_le_mul_of_nonneg_left this hD0.le
        _ = K.k (r / lam) * lam ^ d := by field_simp
    -- the least eigenvalue is at least `1`
    have hlam1 : 1 ≤ lam := by
      by_contra hlt
      push Not at hlt
      have hstep : ∀ r : ℝ, 0 < r → K.k (r / lam) = K.k r := by
        intro r hr
        have h1 : K.k r ≤ K.k (r / lam) := by
          have := hP r hr
          have hfac : 1 ≤ D / lam ^ d := by rw [one_le_div (by positivity)]; exact hDge
          nlinarith [K.k_nonneg r hr]
        have h2 : K.k (r / lam) ≤ K.k r :=
          K.k_antitone hr (div_pos hr hlam0) ((le_div_iff₀ hlam0).2 (by nlinarith))
        linarith
      have hiter : ∀ (n : ℕ) (r : ℝ), 0 < r → K.k (r / lam ^ n) = K.k r := by
        intro n
        induction n with
        | zero => intro r _; simp
        | succ n ih =>
          intro r hr
          rw [pow_succ, ← div_div, hstep _ (div_pos hr (by positivity)), ih r hr]
      obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
      refine K.not_ge_at_infinity hd (R := max r0 1) le_sup_right hk0 fun s hs => ?_
      have hs0 : 0 < s := lt_of_lt_of_le hr0 (le_trans le_sup_left hs)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / r0) (one_lt_inv_iff₀.2 ⟨hlam0, hlt⟩)
      have hge : s ≤ r0 / lam ^ n := by
        rw [inv_pow, div_lt_iff₀ hr0] at hn
        rw [le_div_iff₀ (by positivity)]
        have := hn.le
        calc s * lam ^ n = s * lam ^ n * 1 := by ring
          _ ≤ _ := by
            have h1 : (lam ^ n)⁻¹ * r0 * lam ^ n = r0 := by field_simp
            nlinarith [pow_pos hlam0 n]
      rw [← hiter n r0 hr0]
      exact K.k_antitone hs0 (div_pos hr0 (by positivity)) hge
    have hl1 : 1 ≤ ℓ := by rw [← hlam2]; nlinarith
    refine ⟨hl1, ?_⟩
    -- `D/λ^d ≤ R(λ)`
    obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
    haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨r0, hr0, hk0⟩⟩
    have hR : D / lam ^ d ≤ dilRatio K.k lam := by
      refine le_ciInf fun r => ?_
      rw [le_div_iff₀ r.2.2]
      exact hP r.1 r.2.1
    have hR0 : 0 ≤ D / lam ^ d := by positivity
    have h2 : D ≤ lam ^ d * dilRatio K.k lam := by
      rwa [div_le_iff₀' (by positivity)] at hR
    rw [← hD2, ← hlam2, ← pow_mul, mul_comm 2 d, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hD0.le h2 2
  refine ⟨⟨fun h => hfwd h, fun ⟨hl1, hdet⟩ => hord_iff.2 fun y hy => ?_⟩, fun h => ?_⟩
  · -- the converse
    have hlam1 : 1 ≤ lam := Real.one_le_sqrt.2 hl1
    have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hq : 0 < quad M⁻¹ y := quad_pos hM.inv hy
    set s := Real.sqrt (quad M⁻¹ y) with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 hq
    have hslam : s * lam ≤ ‖y‖ := by
      rw [hsdef, hlam, ← Real.sqrt_mul hq.le, mul_comm]
      calc Real.sqrt (ℓ * quad M⁻¹ y) ≤ Real.sqrt (‖y‖ ^ 2) :=
            Real.sqrt_le_sqrt (lamMin_mul_quad_inv_le hM y)
        _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)
    have hsle : s ≤ ‖y‖ / lam := (le_div_iff₀ hlam0).2 hslam
    have hsd' : s ^ d * lam ^ d ≤ ‖y‖ ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hslam d
    have hks0 : 0 ≤ K.k s := K.k_nonneg s hs
    have hyd : 0 < ‖y‖ ^ d := by positivity
    rw [RadialProfile.m, RadialProfile.m]
    rcases (K.k_nonneg ‖y‖ hr).lt_or_eq with hk | hk
    · have hRle : dilRatio K.k lam * K.k ‖y‖ ≤ K.k (‖y‖ / lam) :=
        (le_div_iff₀ hk).1 (ciInf_le (dilRatio_mem hd K lam hlam1).1 ⟨‖y‖, hr, hk⟩)
      have hks : K.k (‖y‖ / lam) ≤ K.k s :=
        K.k_antitone hs (div_pos hr hlam0) hsle
      have hR1 := (dilRatio_mem hd K lam hlam1).2
      have hD : D ≤ lam ^ d * dilRatio K.k lam := by
        have h2 : D ^ 2 ≤ (lam ^ d * dilRatio K.k lam) ^ 2 := by
          rw [hD2, mul_pow, ← pow_mul, mul_comm d 2, pow_mul, hlam2]; exact hdet
        exact (pow_le_pow_iff_left₀ hD0.le (by positivity) two_ne_zero).1 h2
      have hkey : K.k ‖y‖ * D ≤ K.k s * lam ^ d := by
        calc K.k ‖y‖ * D ≤ K.k ‖y‖ * (lam ^ d * dilRatio K.k lam) :=
              mul_le_mul_of_nonneg_left hD hk.le
          _ = lam ^ d * (dilRatio K.k lam * K.k ‖y‖) := by ring
          _ ≤ lam ^ d * K.k (‖y‖ / lam) := mul_le_mul_of_nonneg_left hRle (by positivity)
          _ ≤ lam ^ d * K.k s := mul_le_mul_of_nonneg_left hks (by positivity)
          _ = K.k s * lam ^ d := by ring
      rw [div_le_iff₀ hyd]
      have he : D⁻¹ * (K.k s / s ^ d) * ‖y‖ ^ d = (K.k s * ‖y‖ ^ d) / (D * s ^ d) := by
        field_simp
      rw [he, le_div_iff₀ (by positivity)]
      calc K.k ‖y‖ * (D * s ^ d) = (K.k ‖y‖ * D) * s ^ d := by ring
        _ ≤ (K.k s * lam ^ d) * s ^ d := mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = K.k s * (s ^ d * lam ^ d) := by ring
        _ ≤ K.k s * ‖y‖ ^ d := mul_le_mul_of_nonneg_left hsd' hks0
    · rw [← hk, zero_div]
      exact mul_nonneg (by positivity) (div_nonneg hks0 (by positivity))
  · -- then `Σ ≤ Σ'`
    obtain ⟨hl1, -⟩ := hfwd h
    have hM1 : (M - 1).PosSemidef := by
      have := (posSemidef_sub_smul_one_iff hM.isHermitian 1).2
        (by rw [← lamMin_eq_eigUp_zero hM.isHermitian]; exact hl1)
      rwa [one_smul] at this
    unfold loewnerLE
    rw [← posSemidef_relStep_iff hS, relStep_sub, relStep_self hS]
    exact hM1

/-- **`prop:orbit-step-cone`(2)**, the increment: when the densities are ordered,
`μ_{Σ'} = μ_Σ * ρ` with `ρ` the infinitely divisible probability measure with generating triplet
`(0, (n_{Σ'} - n_Σ)(x)dx, 0)`. Spends A3(iii). -/
theorem orbit_density_order_increment (hd : 1 ≤ d) (K : RadialProfile d) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef)
    (hord : ∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x)
    (μI : Measure (Rd d)) (hμI : IsProfileLaw K μI) :
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
      (∃ T : LevyTriplet d, T.A = 0 ∧
        T.ν = volume.withDensity
          (fun x => ENNReal.ofReal (K.orbitDensity S' x - K.orbitDensity S x)) ∧
        T.γ = 0 ∧ HasTriplet ρ T) ∧
      affineOrbit μI S' = affineOrbit μI S ∗ ρ := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  have hI : ∀ (T : Mat d), T.PosDef → ∀ ω : Rd d,
      ∫⁻ x in ({0}ᶜ : Set (Rd d)), ENNReal.ofReal ((1 - Real.cos ⟪ω, x⟫) * K.orbitDensity T x) =
        K.exponentL (lin (msqrt T) ω) := fun T hT ω => by
    rw [restrict_compl_singleton, K.exponentL_lin_msqrt hd hT]
  obtain ⟨ρ, hprob, hid, ⟨T, hTA, hTν, hTγ, hT⟩, hchar⟩ := exists_density_increment
    (K.orbitDensity S) (K.orbitDensity S') (K.measurable_orbitDensity hd S)
    (K.measurable_orbitDensity hd S') (K.orbitDensity_nonneg hd hS) hord
    (K.orbitDensity_neg S) (K.orbitDensity_neg S')
    (by rw [restrict_compl_singleton]; exact K.orbitDensity_integrable hd hS')
    (fun ω => by rw [hI S' hS' ω]; exact K.exponentL_ne_top hd _)
  refine ⟨ρ, hprob, hid, ⟨T, hTA, by rw [hTν, restrict_compl_singleton], hTγ, hT⟩, ?_⟩
  haveI := hμI.1
  refine eq_of_charFun_eq fun ω => ?_
  rw [charFun_conv, charFun_affineOrbit_profile hd K hμI hS',
    charFun_affineOrbit_profile hd K hμI hS, hchar ω, hI S' hS', hI S hS,
    ← K.exponentL_lin_msqrt hd hS', ← K.exponentL_lin_msqrt hd hS, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  ring

/-- `n_{AΣAᵀ}(x) = |det A|⁻¹ n_Σ(A⁻¹x)`. -/
theorem RadialProfile.orbitDensity_act (K : RadialProfile d) {A : Mat d} (hA : A ∈ glSet d)
    {S : Mat d} (hS : S.PosDef) (x : Rd d) :
    K.orbitDensity (act A S) x = |A.det|⁻¹ * K.orbitDensity S (lin A⁻¹ x) := by
  have hAS : (act A S).PosDef := (posDef_act_iff hA S).2 hS
  have hdet : (act A S).det = A.det ^ 2 * S.det := by
    rw [act, det_mul, det_mul, det_transpose]; ring
  have hinv : (act A S)⁻¹ = act (A⁻¹)ᵀ S⁻¹ := by
    rw [act, Matrix.mul_inv_rev, Matrix.mul_inv_rev, act, transpose_transpose,
      transpose_nonsing_inv, mul_assoc]
  have hquad : quad (act A S)⁻¹ x = quad S⁻¹ (lin A⁻¹ x) := by
    rw [hinv, quad_act, transpose_transpose]
  have hpow : (A.det ^ 2 * S.det) ^ (-(1 : ℝ) / 2) = |A.det|⁻¹ * S.det ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow (sq_nonneg _) hS.det_pos.le, ← sq_abs, ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
    norm_num [Real.rpow_neg_one]
  have hn : ‖lin (msqrt (act A S))⁻¹ x‖ = ‖lin (msqrt S)⁻¹ (lin A⁻¹ x)‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_lin_msqrt_inv hAS,
      norm_sq_lin_msqrt_inv hS, hquad]
  unfold RadialProfile.orbitDensity
  rw [hdet, hpow, hn]
  ring

/-- **`prop:orbit-step-cone`(3)**, which steps: the relation of (2) is a partial order on `PD(d)`,
invariant under `Σ ↦ AΣAᵀ` for `A ∈ GL(d)`; it contains every ray and no step `Σ → Σ + P` with
`0 < rank P < d`. -/
theorem orbit_density_order_props (hd : 1 ≤ d) (K : RadialProfile d) :
    let R : Mat d → Mat d → Prop := fun S S' =>
      S.PosDef ∧ S'.PosDef ∧ ∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x
    IsPartialOrderOn (pdSet d) R ∧ (∀ A ∈ glSet d, ∀ S S' : Mat d, R S S' → R (act A S) (act A S')) ∧
      (∀ S : Mat d, S.PosDef → ∀ lam : ℝ, 1 ≤ lam → R S (lam ^ 2 • S)) ∧
      ∀ S P : Mat d, S.PosDef → P.PosSemidef → 0 < P.rank → P.rank < d → ¬ R S (S + P) := by
  haveI : NeZero d := ⟨by omega⟩
  intro R
  refine ⟨⟨fun S hS => ⟨hS, hS, fun x _ => le_rfl⟩, fun S hS S' hS' h h' => ?_,
    fun S hS S' hS' S'' hS'' h h' => ⟨h.1, h'.2.1, fun x hx => (h.2.2 x hx).trans (h'.2.2 x hx)⟩⟩,
    fun A hA S S' h => ?_, fun S hS lam hlam => ?_, fun S P hS hP hr0 hrd h => ?_⟩
  · exact le_antisymm
      ((orbit_density_order_iff hd K h.1 h.2.1).2 h.2.2)
      ((orbit_density_order_iff hd K h'.1 h'.2.1).2 h'.2.2)
  · have hUA : IsUnit A.det := hA
    have hdA : 0 < |A.det|⁻¹ := inv_pos.2 (abs_pos.2 hUA.ne_zero)
    refine ⟨(posDef_act_iff hA S).2 h.1, (posDef_act_iff hA S').2 h.2.1, ?_⟩
    rw [forall_ne_zero_lin_iff hUA]
    intro y hy
    rw [K.orbitDensity_act hA h.1, K.orbitDensity_act hA h.2.1, lin_inv_mul_apply hUA]
    exact mul_le_mul_of_nonneg_left (h.2.2 y hy) hdA.le
  · have hl2 : 0 < lam ^ 2 := by positivity
    have hS2 : (lam ^ 2 • S).PosDef := hS.smul hl2
    refine ⟨hS, hS2, (orbit_density_order_iff hd K hS hS2).1.2 ?_⟩
    rw [relStep_smul, relStep_self hS, lamMin_smul hl2.le, lamMin_one, mul_one, det_smul_one,
      Real.sqrt_sq (by linarith)]
    refine ⟨by nlinarith, ?_⟩
    have hR1 := (dilRatio_mem hd K lam hlam).2
    have h1 : (1 : ℝ) ≤ dilRatio K.k lam ^ 2 := by nlinarith
    calc (lam ^ 2) ^ d = (lam ^ 2) ^ d * 1 := by ring
      _ ≤ (lam ^ 2) ^ d * dilRatio K.k lam ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  · obtain ⟨hS1, hSP, hord⟩ := h
    obtain ⟨hl1, hdet⟩ := (orbit_density_order_iff hd K hS1 hSP).1.1 hord
    set N := relStep S P with hN
    have hNpsd : N.PosSemidef := (posSemidef_relStep_iff hS P).2 hP
    have hN0 : N ≠ 0 := by
      intro h0
      have : P = 0 := relStep_injective hS (by rw [← hN, h0]; simp [relStep])
      rw [this, rank_zero] at hr0
      exact lt_irrefl 0 hr0
    have hM : relStep S (S + P) = 1 + N := by rw [relStep_add, relStep_self hS]
    have hdet1 := one_lt_det_one_add hNpsd hN0
    have hlam := lamMin_relStep_add_le_one hS hP hrd
    have hl : lamMin (relStep S (S + P)) = 1 := le_antisymm hlam hl1
    rw [hl, Real.sqrt_one, dilRatio_one, one_pow, one_pow, mul_one, hM] at hdet
    linarith

/-- `ℓ^d (√ℓ^α)² = ℓ^{d+α}`. -/
theorem pow_mul_sqrt_rpow_sq {ℓ : ℝ} (hl : 0 < ℓ) (α : ℝ) :
    ℓ ^ d * (Real.sqrt ℓ ^ α) ^ 2 = ℓ ^ ((d : ℝ) + α) := by
  have h1 : (Real.sqrt ℓ ^ α) ^ 2 = ℓ ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _), mul_comm,
      Real.rpow_mul (Real.sqrt_nonneg _), Nat.cast_ofNat, Real.rpow_two, Real.sq_sqrt hl.le]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_add hl]

/-- **`prop:orbit-step-cone`(3)**: if `k(r) = c r^{-α}`, `0 < α < 2`, then `R(λ) = λ^α` and the cone
is that of `prop:stable-step-cone`. -/
theorem orbit_density_order_stable (hd : 1 ≤ d) (K : RadialProfile d) (c α : ℝ) (hα0 : 0 < α)
    (_hα2 : α < 2) (hk : ∀ r : ℝ, 0 < r → K.k r = c * r ^ (-α)) :
    (∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ α) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔ stableLE α S S') := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  haveI : Nonempty {r : ℝ // 0 < r ∧ 0 < K.k r} := ⟨⟨r0, hr0, hk0⟩⟩
  have hR : ∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = lam ^ α := by
    intro lam hlam
    have hl0 : 0 < lam := by linarith
    have hq : ∀ r : {r : ℝ // 0 < r ∧ 0 < K.k r}, K.k (r.1 / lam) / K.k r.1 = lam ^ α := by
      rintro ⟨r, hr, hkr⟩
      have hc : c * r ^ (-α) ≠ 0 := by rw [← hk r hr]; exact hkr.ne'
      have hdiv : (r / lam) ^ (-α) = r ^ (-α) * lam ^ α := by
        rw [Real.div_rpow hr.le hl0.le, Real.rpow_neg hl0.le, div_inv_eq_mul]
      change K.k (r / lam) / K.k r = lam ^ α
      rw [hk _ (div_pos hr hl0), hk r hr, hdiv, div_eq_iff hc]
      ring
    unfold dilRatio
    simp_rw [hq]
    exact ciInf_const
  refine ⟨hR, fun S S' hS hS' => ?_⟩
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hl := lamMin_pos hM
  rw [(orbit_density_order_iff hd K hS hS').1]
  constructor
  · rintro ⟨hl1, hdet⟩
    refine ⟨hS, hS', hM, ?_⟩
    rwa [hR _ (Real.one_le_sqrt.2 hl1), pow_mul_sqrt_rpow_sq hl] at hdet
  · rintro ⟨-, -, -, hdet⟩
    have hl1 := one_le_lamMin_of_stable hα0 hM hdet
    refine ⟨hl1, ?_⟩
    rwa [hR _ (Real.one_le_sqrt.2 hl1), pow_mul_sqrt_rpow_sq hl]

/-- **`prop:orbit-step-cone`(3)**: if `k(0+)` is finite, then `R ≡ 1` and the cone is the rays. -/
theorem orbit_density_order_bounded (hd : 1 ≤ d) (K : RadialProfile d) (L : ℝ)
    (hL : Tendsto K.k (𝓝[>] 0) (𝓝 L)) :
    (∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = 1) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef →
        ((∀ x : Rd d, x ≠ 0 → K.orbitDensity S x ≤ K.orbitDensity S' x) ↔
          ∃ lam : ℝ, 1 ≤ lam ∧ S' = lam ^ 2 • S) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨r0, hr0, hk0⟩ := K.exists_pos
  -- `L ≥ k(r₀) > 0`
  have hLpos : 0 < L := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), K.k r0 ≤ K.k r := by
      filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
      exact K.k_antitone hr.1 hr0 hr.2.le
    exact lt_of_lt_of_le hk0 (ge_of_tendsto hL hev)
  have hR : ∀ lam : ℝ, 1 ≤ lam → dilRatio K.k lam = 1 := by
    intro lam hlam
    have hl0 : 0 < lam := by linarith
    refine le_antisymm ?_ (dilRatio_mem hd K lam hlam).2
    -- the quotients tend to `L/L = 1` at `0+`
    have hdiv : Tendsto (fun r : ℝ => r / lam) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_id.div_const lam).tendsto 0
        simp only [id, zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact div_pos hr hl0
    have hq : Tendsto (fun r => K.k (r / lam) / K.k r) (𝓝[>] 0) (𝓝 (L / L)) :=
      (hL.comp hdiv).div hL hLpos.ne'
    rw [div_self hLpos.ne'] at hq
    have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ 0 < K.k r := by
      filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
      exact ⟨hr.1, lt_of_lt_of_le hk0 (K.k_antitone hr.1 hr0 hr.2.le)⟩
    refine ge_of_tendsto hq ?_
    filter_upwards [hpos] with r hr
    exact ciInf_le (dilRatio_mem hd K lam hlam).1 ⟨r, hr⟩
  refine ⟨hR, fun S S' hS hS' => ?_⟩
  have hM : (relStep S S').PosDef := (posDef_relStep_iff hS S').2 hS'
  have hl := lamMin_pos hM
  rw [(orbit_density_order_iff hd K hS hS').1]
  constructor
  · rintro ⟨hl1, hdet⟩
    rw [hR _ (Real.one_le_sqrt.2 hl1), one_pow, mul_one] at hdet
    -- every eigenvalue of `M` equals `λ_min(M)`
    obtain ⟨U, m, hUU, hMU⟩ := exists_udiag hM.isHermitian
    have hml : ∀ i, lamMin (relStep S S') ≤ m i := fun i => by
      rw [hMU]; exact lamMin_udiag_le hUU m i
    have heq : ∀ i, m i = lamMin (relStep S S') := by
      by_contra hne
      push Not at hne
      obtain ⟨j, hj⟩ := hne
      have hlt : lamMin (relStep S S') < m j := lt_of_le_of_ne (hml j) (Ne.symm hj)
      have : ∏ _i : Fin d, lamMin (relStep S S') < ∏ i, m i :=
        Finset.prod_lt_prod (fun _ _ => hl) (fun i _ => hml i) ⟨j, Finset.mem_univ _, hlt⟩
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← det_udiag hUU, ← hMU] at this
      linarith
    have hMc : relStep S S' = lamMin (relStep S S') • (1 : Mat d) := by
      have hm : m = fun _ => lamMin (relStep S S') := funext heq
      conv_lhs => rw [hMU, hm, udiag_const hUU]
    refine ⟨Real.sqrt (lamMin (relStep S S')), Real.one_le_sqrt.2 hl1, ?_⟩
    rw [Real.sq_sqrt hl.le]
    calc S' = msqrt S * relStep S S' * msqrt S := (msqrt_mul_relStep hS S').symm
      _ = lamMin (relStep S S') • S := by
        conv_lhs => rw [hMc]
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, msqrt_mul_self hS.posSemidef]
  · rintro ⟨lam, hlam, rfl⟩
    have hl2 : 0 < lam ^ 2 := by positivity
    rw [relStep_smul, relStep_self hS, lamMin_smul hl2.le, lamMin_one, mul_one, det_smul_one,
      Real.sqrt_sq (by linarith), hR lam hlam]
    exact ⟨by nlinarith, by simp⟩

end AffineHemigroup
