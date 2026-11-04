/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityCascade
import AffineHemigroup.AnisotropyConverse
import AffineHemigroup.RotationInvariant
import AffineHemigroup.PolarReading
import AffineHemigroup.ParameterSpace
import AffineHemigroup.StableExponent
import AffineHemigroup.ShapeAdapted

/-!
# `prop:anisotropy-budget`(1): the anisotropy budget of a rotation-invariant law

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:anisotropy-budget` (clause (2) is the
split child `prop:anisotropy-budget-converse`, proved in `AffineHemigroup.AnisotropyConverse`).

If `e^{-tB} → 0` and `μ` is a rotation-invariant `B`-self-decomposable law that is not Gaussian,
then `λ := λ_min(sym B) > 0` and `tr B < (d+2)λ`.

## Route

The blueprint's, in three parts.

* **The Lévy measure** (A5, A3(i)–(ii)): `μ` and its residuals are infinitely divisible, the Lévy
  measure `ν` of `μ` is rotation invariant, not `0`, and `(e^{-tB})_*ν ≤ ν` (`anisotropy_levy`).
* **The radial smoothing.** `ν_η := ∫ η(s) (sI)_*ν ds` with a smooth bump `η` about `1`
  (`dilAvg`, a `Measure.bind`) inherits the three properties, and its radial image is
  `K(r) dr` with `K(r) = ∫ η(r/|x|)/|x| ν(dx)`. The measure with the radial density
  `K(|y|)/(|S^{d-1}| |y|^{d-1})` is rotation invariant with the same radial image, so the two are
  equal (`eq_of_rotationInvariant`, which needs no Haar measure on `O(d)`). The blueprint's Haar
  average is not needed.
* **The infinitesimal inequality and the budget.** The linear change of variables turns
  `(e^{-tB})_*ν_η ≤ ν_η` into `e^{t tr B} M(|e^{tB}y|) ≤ M(|y|)` for `M(r) := K(r)/r^{d-1}`, first
  almost everywhere and then everywhere by continuity. At `y = rv`, `v` a unit eigenvector of
  `sym B` for `λ`, the right derivative at `t = 0` gives `tr B·M(r) + λ r M'(r) ≤ 0`, so
  `r^{tr B/λ} M(r)` is monotone, and `∫ (r² ∧ 1) K(r) dr < ∞` excludes `λ ≤ 0` and
  `tr B ≥ (d+2)λ`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Metric Matrix ProbabilityTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The Lévy measure (A5, A3) -/

/-- **The Lévy measure of a rotation-invariant `B`-self-decomposable law** that is not Gaussian,
`e^{-tB} → 0`: null at `0`, with `∫ (|x|² ∧ 1) dν < ∞`, not `0`, invariant under every linear
isometry, and `(e^{-tB})_*ν ≤ ν` for `t > 0`. Spends A5 and A3(i)–(ii). -/
theorem anisotropy_levy (B : Mat d) (hB : IsExpContracting B)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hrot : IsRotationInvariant μ)
    (hsd : IsBSelfDecomposable B μ) (hng : ¬ IsGaussian μ) :
    ∃ ν : Measure (Rd d), ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν) ≠ ⊤ ∧
      ν ≠ 0 ∧ (∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν) ∧
      ∀ t : ℝ, 0 < t → push (mexp (-t • B)) ν ≤ ν := by
  have hsd0 : ∀ t : ℝ, 0 ≤ t → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      μ = push (mexp (-t • B)) μ ∗ ρ := by
    intro t ht
    rcases ht.lt_or_eq with ht | rfl
    · exact (isBSelfDecomposable_iff B μ).1 hsd t ht
    · refine ⟨Measure.dirac 0, inferInstance, ?_⟩
      rw [neg_zero, zero_smul, mexp_zero, push_one, Measure.conv_dirac_zero]
  obtain ⟨hres, hID⟩ := operatorSelfDecomposable_infinitelyDivisible B hB μ hsd0
  obtain ⟨T, hT⟩ := levy_khintchine_exists μ hID
  have hsymμ : push (-1) μ = μ := hrot _ neg_one_mem_orthSet
  obtain ⟨hγ, hsym⟩ := symm_triplet_of_symm hID hsymμ hT
  refine ⟨T.ν, T.ν_zero, T.ν_integrable, ?_, fun Q => levyMeasure_rotationInvariant μ hID T hT
    (fun ξ ξ' h => charFun_eq_of_norm_eq hrot h) Q, fun t ht => ?_⟩
  · intro h0
    apply hng
    have hG : μ = multivariateGaussian 0 T.A := by
      apply eq_of_charFun_eq
      intro z
      rw [hT z, charFun_multivariateGaussian_zero T.A_posSemidef z, LevyTriplet.lkExponent, hγ, h0]
      simp only [integral_zero_measure, inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero,
        Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [hG]
    infer_instance
  · obtain ⟨ρ, hρ, heq⟩ := (isBSelfDecomposable_iff B μ).1 hsd t ht
    haveI := hρ
    have hρid := hres t ht.le ρ hρ heq
    have hgl : mexp (-t • B) ∈ glSet d := mexp_mem_glSet _
    obtain ⟨Tρ, -, -, hν, -⟩ :=
      triplet_increment hρid hID (T.hasTriplet_pushSym hT hγ hsym hgl) heq hT
    have h2 : T.ν = push (mexp (-t • B)) T.ν + Tρ.ν := hν
    calc push (mexp (-t • B)) T.ν ≤ push (mexp (-t • B)) T.ν + Tρ.ν := Measure.le_add_right le_rfl
      _ = T.ν := h2.symm

/-! ## Measures null at the origin and finite off every ball -/

/-- A measure with `∫ (|x|² ∧ 1) dν < ∞` is finite off every ball about the origin. -/
theorem measure_norm_gt_ne_top_of_lintegral {ν : Measure (Rd d)}
    (hint : (∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ν {x | ε < ‖x‖} ≠ ⊤ := by
  have hm : MeasurableSet {x : Rd d | ε < ‖x‖} := measurableSet_lt measurable_const
    continuous_norm.measurable
  have hc : 0 < min (ε ^ 2) 1 := lt_min (by positivity) one_pos
  have hle : ENNReal.ofReal (min (ε ^ 2) 1) * ν {x | ε < ‖x‖}
      ≤ ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono' hm fun x (hx : ε < ‖x‖) => ENNReal.ofReal_le_ofReal ?_).trans
      (setLIntegral_le_lintegral _ _)
    exact min_le_min (pow_le_pow_left₀ hε.le hx.le 2) le_rfl
  intro htop
  rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc)] at hle
  exact hint (top_le_iff.mp hle)

/-- A measure null at the origin and finite off every ball about it is σ-finite. -/
theorem sigmaFinite_of_null_finite {ν : Measure (Rd d)} (h0 : ν {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) : SigmaFinite ν := by
  let S : ℕ → Set (Rd d) := fun n => {0} ∪ {x | 1 / ((n : ℝ) + 1) < ‖x‖}
  refine ⟨⟨{ set := S, set_mem := fun _ => trivial, finite := fun n => ?_, spanning := ?_ }⟩⟩
  · calc ν ({0} ∪ {x | 1 / ((n : ℝ) + 1) < ‖x‖})
        ≤ ν {0} + ν {x | 1 / ((n : ℝ) + 1) < ‖x‖} := measure_union_le _ _
      _ < ⊤ := by rw [h0, zero_add]; exact lt_top_iff_ne_top.2 (hfin _ (by positivity))
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, Or.inl rfl⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx)
      exact ⟨n, Or.inr hn⟩

/-! ## The bump `η` -/

/-- The smooth bump about `1`: `1` on `[3/4, 5/4]`, positive exactly on `(1/2, 3/2)`. -/
noncomputable def bumpη : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- `η`, as a function on `ℝ`. -/
noncomputable def eta (s : ℝ) : ℝ := bumpη s

theorem eta_nonneg (s : ℝ) : 0 ≤ eta s := bumpη.nonneg

theorem eta_le_one (s : ℝ) : eta s ≤ 1 := bumpη.le_one

theorem eta_supp {s : ℝ} (h : eta s ≠ 0) : 1 / 2 < s ∧ s < 3 / 2 := by
  have hs : s ∈ Function.support (bumpη : ℝ → ℝ) := h
  rw [bumpη.support_eq, Metric.mem_ball, Real.dist_eq] at hs
  have hr : bumpη.rOut = 1 / 2 := rfl
  rw [hr] at hs
  obtain ⟨h1, h2⟩ := abs_lt.1 hs
  constructor <;> linarith

theorem eta_eq_one {s : ℝ} (h1 : 3 / 4 ≤ s) (h2 : s ≤ 5 / 4) : eta s = 1 := by
  refine bumpη.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hr : bumpη.rIn = 1 / 4 := rfl
  rw [hr, abs_le]
  constructor <;> linarith

theorem eta_zero : eta 0 = 0 := by
  by_contra h
  have := (eta_supp h).1
  norm_num at this

theorem continuous_eta : Continuous eta := bumpη.continuous

theorem measurable_eta : Measurable eta := continuous_eta.measurable

theorem contDiff_eta : ContDiff ℝ 1 eta := bumpη.contDiff

theorem hasDerivAt_eta (s : ℝ) : HasDerivAt eta (deriv eta s) s :=
  ((contDiff_eta.differentiable (by norm_num)) s).hasDerivAt

theorem continuous_deriv_eta : Continuous (deriv eta) := contDiff_eta.continuous_deriv le_rfl

/-- `η'` is bounded. -/
theorem exists_bound_deriv_eta : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv eta s| ≤ M := by
  have hcs : HasCompactSupport (deriv eta) := (bumpη.hasCompactSupport).deriv
  obtain ⟨C, hC⟩ := continuous_deriv_eta.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩

/-- `η'(s) ≠ 0` only on `[1/2, 3/2]`. -/
theorem deriv_eta_supp {s : ℝ} (h : deriv eta s ≠ 0) : 1 / 2 ≤ s ∧ s ≤ 3 / 2 := by
  have hs : s ∈ tsupport (bumpη : ℝ → ℝ) := support_deriv_subset h
  rw [bumpη.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hs
  have hr : bumpη.rOut = 1 / 2 := rfl
  rw [hr] at hs
  obtain ⟨h1, h2⟩ := abs_le.1 hs
  constructor <;> linarith

/-- `0 < ∫ η < ∞`. -/
theorem lintegral_eta : (∫⁻ s, ENNReal.ofReal (eta s)) ≠ 0 ∧ (∫⁻ s, ENNReal.ofReal (eta s)) ≠ ⊤ := by
  constructor
  · intro h
    have hle : ∫⁻ s in Icc (3 / 4 : ℝ) (5 / 4), (1 : ℝ≥0∞) ≤ ∫⁻ s, ENNReal.ofReal (eta s) := by
      refine (setLIntegral_mono' measurableSet_Icc fun s hs => ?_).trans
        (setLIntegral_le_lintegral _ _)
      rw [eta_eq_one hs.1 hs.2, ENNReal.ofReal_one]
    rw [h, setLIntegral_const, one_mul, Real.volume_Icc] at hle
    norm_num at hle
  · refine ne_top_of_le_ne_top (b := ∫⁻ s in Ioo (1 / 2 : ℝ) (3 / 2), (1 : ℝ≥0∞)) ?_ ?_
    · rw [setLIntegral_const, one_mul, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    · rw [← lintegral_indicator measurableSet_Ioo]
      refine lintegral_mono fun s => ?_
      by_cases hs : eta s = 0
      · rw [hs, ENNReal.ofReal_zero]; exact bot_le
      · rw [indicator_of_mem (show s ∈ Ioo (1 / 2 : ℝ) (3 / 2) from eta_supp hs)]
        exact ENNReal.ofReal_le_one.2 (eta_le_one s)

/-! ## The radial smoothing `ν_η = ∫ η(s) (sI)_*ν ds` -/

/-- The law of `s x` for `s ∼ η(s) ds`. -/
noncomputable def dilKer (x : Rd d) : Measure (Rd d) :=
  ((volume : Measure ℝ).withDensity fun s => ENNReal.ofReal (eta s)).map fun s : ℝ => s • x

theorem dilKer_lintegral (x : Rd d) {f : Rd d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(dilKer x) = ∫⁻ s, ENNReal.ofReal (eta s) * f (s • x) := by
  rw [dilKer, lintegral_map hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ measurable_eta.ennreal_ofReal
      (g := fun s : ℝ => f (s • x)) (hf.comp (measurable_id.smul_const x))]
  rfl

theorem measurable_dilKer_aux {U : Set (Rd d)} (hU : MeasurableSet U) :
    Measurable fun p : Rd d × ℝ => ENNReal.ofReal (eta p.2) * U.indicator 1 (p.2 • p.1) :=
  (measurable_eta.comp measurable_snd).ennreal_ofReal.mul
    ((measurable_one.indicator hU).comp (measurable_snd.smul measurable_fst))

theorem dilKer_apply (x : Rd d) {U : Set (Rd d)} (hU : MeasurableSet U) :
    dilKer x U = ∫⁻ s, ENNReal.ofReal (eta s) * U.indicator 1 (s • x) := by
  rw [← lintegral_indicator_one hU, dilKer_lintegral x (measurable_one.indicator hU)]

theorem measurable_dilKer : Measurable (dilKer (d := d)) := by
  refine Measure.measurable_of_measurable_coe _ fun U hU => ?_
  simp_rw [dilKer_apply _ hU]
  exact (measurable_dilKer_aux hU).lintegral_prod_right'

/-- **The radial smoothing** `ν_η(U) = ∫ η(s) ν(s⁻¹U) ds`. -/
noncomputable def dilAvg (ν : Measure (Rd d)) : Measure (Rd d) := ν.bind dilKer

theorem lintegral_dilAvg (ν : Measure (Rd d)) {f : Rd d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(dilAvg ν) = ∫⁻ x, (∫⁻ s, ENNReal.ofReal (eta s) * f (s • x)) ∂ν := by
  rw [dilAvg, Measure.lintegral_bind measurable_dilKer.aemeasurable hf.aemeasurable]
  simp_rw [dilKer_lintegral _ hf]

theorem dilAvg_apply (ν : Measure (Rd d)) {U : Set (Rd d)} (hU : MeasurableSet U) :
    dilAvg ν U = ∫⁻ x, (∫⁻ s, ENNReal.ofReal (eta s) * U.indicator 1 (s • x)) ∂ν := by
  rw [← lintegral_indicator_one hU, lintegral_dilAvg ν (measurable_one.indicator hU)]

theorem dilAvg_mono {ν ν' : Measure (Rd d)} (h : ν ≤ ν') : dilAvg ν ≤ dilAvg ν' :=
  Measure.le_iff.2 fun U hU => by
    rw [dilAvg_apply ν hU, dilAvg_apply ν' hU]
    exact lintegral_mono' h le_rfl

/-- `L_*ν_η = (L_*ν)_η` for a continuous linear `L`. -/
theorem dilAvg_map (ν : Measure (Rd d)) (L : Rd d →L[ℝ] Rd d) :
    (dilAvg ν).map L = dilAvg (ν.map L) := by
  refine Measure.ext fun U hU => ?_
  have hpre : MeasurableSet (L ⁻¹' U) := L.continuous.measurable hU
  rw [Measure.map_apply L.continuous.measurable hU, dilAvg_apply ν hpre, dilAvg_apply _ hU,
    lintegral_map ((measurable_dilKer_aux hU).lintegral_prod_right') L.continuous.measurable]
  refine lintegral_congr fun x => lintegral_congr fun s => ?_
  congr 1
  by_cases h : s • L x ∈ U
  · have h' : s • x ∈ L ⁻¹' U := by rw [mem_preimage, map_smul]; exact h
    simp [indicator, h, h']
  · have h' : s • x ∉ L ⁻¹' U := by rw [mem_preimage, map_smul]; exact h
    simp [indicator, h, h']

/-- `(sI)` never moves `0` off `0`: `ν_η{0} = 0` when `ν{0} = 0`. -/
theorem dilAvg_zero {ν : Measure (Rd d)} (h0 : ν {0} = 0) : dilAvg ν {0} = 0 := by
  rw [dilAvg_apply ν (measurableSet_singleton 0)]
  have hae : ∀ᵐ x ∂ν, x ≠ 0 := measure_eq_zero_iff_ae_notMem.1 h0
  refine (lintegral_congr_ae (hae.mono fun x hx => ?_)).trans lintegral_zero
  refine (lintegral_congr fun s => ?_).trans lintegral_zero
  by_cases hs : s = 0
  · simp [hs, eta_zero]
  · have : s • x ∉ ({0} : Set (Rd d)) := by
      simp only [mem_singleton_iff, smul_eq_zero, hs, hx, or_self, not_false_eq_true]
    simp [indicator_of_notMem this]

/-- `ν_η` is finite off every ball about the origin when `ν` is. -/
theorem dilAvg_norm_gt_ne_top {ν : Measure (Rd d)}
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    dilAvg ν {x | ε < ‖x‖} ≠ ⊤ := by
  have hm : ∀ a : ℝ, MeasurableSet {x : Rd d | a < ‖x‖} := fun a =>
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [dilAvg_apply ν (hm ε)]
  have hpt : ∀ x : Rd d, ∀ s : ℝ, ENNReal.ofReal (eta s) * {x : Rd d | ε < ‖x‖}.indicator 1 (s • x)
      ≤ ENNReal.ofReal (eta s) * {x : Rd d | 2 * ε / 3 < ‖x‖}.indicator 1 x := by
    intro x s
    by_cases hs : eta s = 0
    · simp [hs]
    obtain ⟨hs1, hs2⟩ := eta_supp hs
    by_cases hx : ε < ‖s • x‖
    · have hx' : 2 * ε / 3 < ‖x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith)] at hx
        nlinarith [norm_nonneg x]
      rw [indicator_of_mem (show s • x ∈ {x : Rd d | ε < ‖x‖} from hx),
        indicator_of_mem (show x ∈ {x : Rd d | 2 * ε / 3 < ‖x‖} from hx')]
      simp
    · rw [indicator_of_notMem (show s • x ∉ {x : Rd d | ε < ‖x‖} from hx), mul_zero]
      exact bot_le
  refine ne_top_of_le_ne_top (b := ∫⁻ x, (∫⁻ s, ENNReal.ofReal (eta s)) *
    {x : Rd d | 2 * ε / 3 < ‖x‖}.indicator 1 x ∂ν) ?_ (lintegral_mono fun x => ?_)
  · rw [lintegral_const_mul _ (measurable_one.indicator (hm _)), lintegral_indicator_one (hm _)]
    exact ENNReal.mul_ne_top lintegral_eta.2 (hfin _ (by positivity))
  · rw [← lintegral_mul_const _ measurable_eta.ennreal_ofReal]
    exact lintegral_mono fun s => hpt x s

/-! ## The radial image of `ν_η`, and its density `K` -/

/-- `∫ φ = a ∫ φ(s a) ds` for `a > 0`. Mathlib types only. -/
theorem lintegral_eq_mul_comp_mul {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ r, φ r = ENNReal.ofReal a * ∫⁻ s, φ (s * a) := by
  have h2 : ∫⁻ s, φ (s * a) = ∫⁻ r, φ r ∂(Measure.map (· * a) volume) :=
    (lintegral_map hφ (measurable_mul_const a)).symm
  rw [h2, Real.map_volume_mul_right ha.ne', lintegral_smul_measure, abs_of_pos (inv_pos.2 ha),
    smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne',
    ENNReal.ofReal_one, one_mul]

/-- **The radial density of `ν_η`**, `K(r) = ∫ η(r/|x|)/|x| ν(dx)`. -/
noncomputable def radK (ν : Measure (Rd d)) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (eta (r / ‖x‖) / ‖x‖) ∂ν

theorem measurable_radK_integrand :
    Measurable fun p : Rd d × ℝ => ENNReal.ofReal (eta (p.2 / ‖p.1‖) / ‖p.1‖) :=
  ((measurable_eta.comp (measurable_snd.div measurable_fst.norm)).div
    measurable_fst.norm).ennreal_ofReal

/-- For `x ≠ 0`, `∫ η(s) 1_E(|sx|) ds = ∫_{E ∩ (0,∞)} η(r/|x|)/|x| dr`. -/
theorem lintegral_eta_norm {x : Rd d} (hx : x ≠ 0) {E : Set ℝ} (hE : MeasurableSet E) :
    ∫⁻ s, ENNReal.ofReal (eta s) * ((fun y : Rd d => ‖y‖) ⁻¹' E).indicator 1 (s • x)
      = ∫⁻ r, (E ∩ Ioi 0).indicator 1 r * ENNReal.ofReal (eta (r / ‖x‖) / ‖x‖) := by
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hφm : Measurable fun r : ℝ =>
      (E ∩ Ioi 0).indicator 1 r * ENNReal.ofReal (eta (r / ‖x‖) / ‖x‖) :=
    (measurable_one.indicator (hE.inter measurableSet_Ioi)).mul
      ((measurable_eta.comp (measurable_id.div_const _)).div_const _).ennreal_ofReal
  refine Eq.trans ?_ (lintegral_eq_mul_comp_mul ha hφm).symm
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun s => ?_
  beta_reduce
  rw [mul_div_cancel_right₀ s ha.ne']
  by_cases hs : eta s = 0
  · simp [hs]
  obtain ⟨hs1, hs2⟩ := eta_supp hs
  have hsp : 0 < s := by linarith
  have hn : ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hsp.le]
  by_cases hE' : s * ‖x‖ ∈ E
  · rw [indicator_of_mem (show s • x ∈ (fun y : Rd d => ‖y‖) ⁻¹' E by
        simp only [mem_preimage, hn]; exact hE'),
      indicator_of_mem (show s * ‖x‖ ∈ E ∩ Ioi 0 from ⟨hE', mem_Ioi.2 (by positivity)⟩)]
    simp only [Pi.one_apply, mul_one, one_mul]
    rw [← ENNReal.ofReal_mul ha.le, mul_div_cancel₀ _ ha.ne']
  · rw [indicator_of_notMem (show s • x ∉ (fun y : Rd d => ‖y‖) ⁻¹' E by
        simp only [mem_preimage, hn]; exact hE'), indicator_of_notMem (fun h => hE' h.1)]
    simp

/-- **The radial image of `ν_η`** is `K(r) dr` on `(0,∞)`. -/
theorem map_norm_dilAvg {ν : Measure (Rd d)} [SFinite ν] (h0 : ν {0} = 0) :
    (dilAvg ν).map (fun x => ‖x‖) = (volume.restrict (Ioi (0 : ℝ))).withDensity (radK ν) := by
  refine Measure.ext fun E hE => ?_
  have hpre : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' E) := continuous_norm.measurable hE
  have hEI : MeasurableSet (E ∩ Ioi (0 : ℝ)) := hE.inter measurableSet_Ioi
  rw [Measure.map_apply continuous_norm.measurable hE, dilAvg_apply ν hpre, withDensity_apply _ hE,
    Measure.restrict_restrict hE, ← lintegral_indicator hEI]
  have hae : ∀ᵐ x ∂ν, x ≠ 0 := measure_eq_zero_iff_ae_notMem.1 h0
  rw [lintegral_congr_ae (hae.mono fun x hx => lintegral_eta_norm hx hE)]
  have hjoint : Measurable (Function.uncurry fun (x : Rd d) (r : ℝ) =>
      (E ∩ Ioi 0).indicator 1 r * ENNReal.ofReal (eta (r / ‖x‖) / ‖x‖)) :=
    ((measurable_one.indicator hEI).comp measurable_snd).mul measurable_radK_integrand
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun r => ?_
  by_cases hr : r ∈ E ∩ Ioi 0
  · simp only [indicator_of_mem hr, Pi.one_apply, one_mul]
    rfl
  · simp only [indicator_of_notMem hr, zero_mul, lintegral_zero]

/-- `K(r) < ∞` for `r > 0`. -/
theorem radK_ne_top {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : radK ν r ≠ ⊤ := by
  have hm : MeasurableSet {x : Rd d | 2 * r / 3 < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  refine ne_top_of_le_ne_top (b := ∫⁻ x, ENNReal.ofReal (3 / (2 * r)) *
    {x : Rd d | 2 * r / 3 < ‖x‖}.indicator 1 x ∂ν) ?_ (lintegral_mono fun x => ?_)
  · rw [lintegral_const_mul _ (measurable_one.indicator hm), lintegral_indicator_one hm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ (by positivity))
  · by_cases h : eta (r / ‖x‖) = 0
    · simp [h]
    obtain ⟨h1, h2⟩ := eta_supp h
    have hx : 0 < ‖x‖ := by
      rcases (norm_nonneg x).lt_or_eq with hx | hx
      · exact hx
      · rw [← hx, div_zero] at h1; norm_num at h1
    have hx1 : 2 * r / 3 < ‖x‖ := by
      rw [div_lt_iff₀ hx] at h2; linarith
    rw [indicator_of_mem (show x ∈ {x : Rd d | 2 * r / 3 < ‖x‖} from hx1), Pi.one_apply, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc eta (r / ‖x‖) / ‖x‖ ≤ 1 / ‖x‖ := div_le_div_of_nonneg_right (eta_le_one _) hx.le
      _ ≤ 3 / (2 * r) := by rw [div_le_div_iff₀ hx (by positivity)]; linarith

/-- `K` as a real function, a Bochner integral. -/
noncomputable def radKr (ν : Measure (Rd d)) (r : ℝ) : ℝ := ∫ x, eta (r / ‖x‖) / ‖x‖ ∂ν

theorem radK_integrand_nonneg (r : ℝ) (x : Rd d) : 0 ≤ eta (r / ‖x‖) / ‖x‖ :=
  div_nonneg (eta_nonneg _) (norm_nonneg _)

theorem measurable_radKr_integrand (r : ℝ) : Measurable fun x : Rd d => eta (r / ‖x‖) / ‖x‖ :=
  (measurable_eta.comp (measurable_const.div measurable_norm)).div measurable_norm

theorem integrable_radK {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x : Rd d => eta (r / ‖x‖) / ‖x‖) ν := by
  refine ⟨(measurable_radKr_integrand r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => radK_integrand_nonneg r x)]
  exact lt_top_iff_ne_top.2 (radK_ne_top hfin hr)

theorem ofReal_radKr {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : ENNReal.ofReal (radKr ν r) = radK ν r :=
  ofReal_integral_eq_lintegral_ofReal (integrable_radK hfin hr)
    (ae_of_all _ fun x => radK_integrand_nonneg r x)

theorem radKr_nonneg (ν : Measure (Rd d)) (r : ℝ) : 0 ≤ radKr ν r :=
  integral_nonneg fun x => radK_integrand_nonneg r x

/-- **`K` is differentiable on `(0,∞)`**, by differentiation under the integral: on
`|r' - r| < r/2` the integrand moves only on `{|x| > r/3}`, of finite `ν`-measure. -/
theorem hasDerivAt_radKr {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radKr ν) (∫ x, deriv eta (r / ‖x‖) / ‖x‖ ^ 2 ∂ν) r := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_eta
  set S : Set (Rd d) := {x | r / 3 < ‖x‖} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hSfin : ν S ≠ ⊤ := hfin _ (by positivity)
  have hball : ball r (r / 2) ∈ 𝓝 r := ball_mem_nhds r (by positivity)
  have hmeasF' : ∀ r' : ℝ, Measurable fun x : Rd d => deriv eta (r' / ‖x‖) / ‖x‖ ^ 2 :=
    fun r' => (continuous_deriv_eta.measurable.comp (measurable_const.div measurable_norm)).div
      (measurable_norm.pow_const 2)
  have hbound_int : Integrable (S.indicator fun _ => 9 * M / r ^ 2) ν :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r' (x : Rd d) => eta (r' / ‖x‖) / ‖x‖)
    (F' := fun r' (x : Rd d) => deriv eta (r' / ‖x‖) / ‖x‖ ^ 2)
    (bound := S.indicator fun _ => 9 * M / r ^ 2) hball (Eventually.of_forall fun r' => (measurable_radKr_integrand r').aestronglyMeasurable)
    (integrable_radK hfin hr) (hmeasF' r).aestronglyMeasurable
    (ae_of_all _ fun x r' hr' => ?_) hbound_int (ae_of_all _ fun x r' _ => ?_)).2
  · -- the bound
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
    by_cases h : deriv eta (r' / ‖x‖) = 0
    · rw [h, abs_zero, zero_div]
      exact indicator_nonneg (fun _ _ => by positivity) _
    obtain ⟨h1, h2⟩ := deriv_eta_supp h
    have hr' : r / 2 < r' := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr'; linarith [hr'.1]
    have hx : 0 < ‖x‖ := by
      rcases (norm_nonneg x).lt_or_eq with hx | hx
      · exact hx
      · rw [← hx, div_zero] at h1; norm_num at h1
    have hx1 : r / 3 < ‖x‖ := by
      rw [div_le_iff₀ hx] at h2; linarith
    rw [indicator_of_mem (show x ∈ S from hx1)]
    calc |deriv eta (r' / ‖x‖)| / ‖x‖ ^ 2 ≤ M / ‖x‖ ^ 2 :=
          div_le_div_of_nonneg_right (hM _) (by positivity)
      _ ≤ M / (r / 3) ^ 2 :=
          div_le_div_of_nonneg_left hM0 (by positivity) (pow_le_pow_left₀ (by positivity) hx1.le 2)
      _ = 9 * M / r ^ 2 := by field_simp; ring
  · -- the derivative
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [norm_zero, div_zero, eta_zero]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, div_zero]
      exact hasDerivAt_const r' (0 : ℝ)
    · have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := (hasDerivAt_id r').div_const ‖x‖
      have h2 := ((hasDerivAt_eta (r' / ‖x‖)).comp r' h1).div_const ‖x‖
      simp only [Function.comp_def, id] at h2
      convert h2 using 1
      all_goals first | ring | rfl

theorem continuousOn_radKr {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) :
    ContinuousOn (radKr ν) (Ioi 0) := fun _ hr =>
  (hasDerivAt_radKr hfin hr).continuousAt.continuousWithinAt

theorem measurable_radKr (ν : Measure (Rd d)) [SFinite ν] : Measurable (radKr ν) := by
  have hj : StronglyMeasurable (Function.uncurry fun (r : ℝ) (x : Rd d) => eta (r / ‖x‖) / ‖x‖) :=
    ((measurable_eta.comp (measurable_fst.div measurable_snd.norm)).div
      measurable_snd.norm).stronglyMeasurable
  exact (hj.integral_prod_right (ν := ν)).measurable

/-! ## `ν_η` has the radial density `K(|y|)/(|S^{d-1}| |y|^{d-1})` -/

/-- The density of `ν_η` with respect to Lebesgue measure. -/
noncomputable def radDens (ν : Measure (Rd d)) (y : Rd d) : ℝ :=
  radKr ν ‖y‖ / (sphereArea d * ‖y‖ ^ (d - 1))

/-- The measure with density `radDens`. -/
noncomputable def densMeas (ν : Measure (Rd d)) : Measure (Rd d) :=
  (volume : Measure (Rd d)).withDensity fun y => ENNReal.ofReal (radDens ν y)

theorem measurable_radDens (ν : Measure (Rd d)) [SFinite ν] : Measurable (radDens ν) :=
  ((measurable_radKr ν).comp measurable_norm).div
    (measurable_const.mul (measurable_norm.pow_const _))

theorem radDens_isometry (ν : Measure (Rd d)) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (y : Rd d) :
    radDens ν (Q y) = radDens ν y := by
  simp only [radDens, LinearIsometryEquiv.norm_map]

/-- **The radial image of the density measure** is `K(r) dr` on `(0,∞)`, by polar coordinates. -/
theorem map_norm_densMeas (hd : 1 ≤ d) {ν : Measure (Rd d)} [SFinite ν]
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) :
    (densMeas ν).map (fun x => ‖x‖) = (volume.restrict (Ioi (0 : ℝ))).withDensity (radK ν) := by
  have hA := (sphereArea_eq_toSphere (d := d) hd).2
  refine Measure.ext fun E hE => ?_
  have hpre : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' E) := continuous_norm.measurable hE
  have hEI : MeasurableSet (E ∩ Ioi (0 : ℝ)) := hE.inter measurableSet_Ioi
  have hf : Measurable fun y : Rd d =>
      ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator (fun y => ENNReal.ofReal (radDens ν y)) y :=
    (measurable_radDens ν).ennreal_ofReal.indicator hpre
  rw [Measure.map_apply continuous_norm.measurable hE, densMeas, withDensity_apply _ hpre,
    ← lintegral_indicator hpre, lintegral_polar hd _ hf, withDensity_apply _ hE,
    Measure.restrict_restrict hE]
  have hinner : ∀ η : sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator (fun y => ENNReal.ofReal (radDens ν y))
        (r • (η : Rd d)) * ENNReal.ofReal (r ^ (d - 1))
      = (ENNReal.ofReal (sphereArea d))⁻¹ * ∫⁻ r in E ∩ Ioi 0, radK ν r := by
    intro η
    rw [← lintegral_indicator hEI, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (by simp [hA]))]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · have hr0 : (0 : ℝ) < r := hr
      have hn : ‖r • (η : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr0.le]
      rw [indicator_of_mem hr]
      by_cases hrE : r ∈ E
      · rw [indicator_of_mem (show r • (η : Rd d) ∈ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE),
          indicator_of_mem (show r ∈ E ∩ Ioi 0 from ⟨hrE, hr⟩), radDens, hn,
          ← ofReal_radKr hfin hr0, ← ENNReal.ofReal_inv_of_pos hA,
          ← ENNReal.ofReal_mul (div_nonneg (radKr_nonneg _ _) (by positivity)),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hA.le)]
        congr 1
        have hrp : 0 < r ^ (d - 1) := pow_pos hr0 _
        field_simp
      · rw [indicator_of_notMem (show r • (η : Rd d) ∉ (fun x : Rd d => ‖x‖) ⁻¹' E by
          simp only [mem_preimage, hn]; exact hrE), indicator_of_notMem (fun h => hrE h.1),
          zero_mul, mul_zero]
    · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr h.2), mul_zero]
  simp_rw [hinner]
  rw [lintegral_const, ← (sphereArea_eq_toSphere hd).1, mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [hA]) ENNReal.ofReal_ne_top, one_mul]

/-- The density measure is invariant under every linear isometry. -/
theorem densMeas_isometry (ν : Measure (Rd d)) [SFinite ν] (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (densMeas ν).map Q = densMeas ν := by
  refine Measure.ext fun U hU => ?_
  have hpre : MeasurableSet (Q ⁻¹' U) := Q.continuous.measurable hU
  rw [Measure.map_apply Q.continuous.measurable hU, densMeas, withDensity_apply _ hpre,
    withDensity_apply _ hU, ← lintegral_indicator hpre, ← lintegral_indicator hU]
  conv_rhs => rw [← (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding]
  refine lintegral_congr fun y => ?_
  by_cases hy : Q y ∈ U
  · rw [indicator_of_mem (show y ∈ Q ⁻¹' U from hy), indicator_of_mem hy, radDens_isometry]
  · rw [indicator_of_notMem (show y ∉ Q ⁻¹' U from hy), indicator_of_notMem hy]

/-- **`ν_η` has the radial density**: it is the density measure, both being rotation invariant
with the same radial image (`eq_of_rotationInvariant`). -/
theorem densMeas_eq_dilAvg (hd : 1 ≤ d) {ν : Measure (Rd d)} (h0 : ν {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν) : densMeas ν = dilAvg ν := by
  haveI := sigmaFinite_of_null_finite h0 hfin
  have hrad : (densMeas ν).map (fun x => ‖x‖) = (dilAvg ν).map (fun x => ‖x‖) := by
    rw [map_norm_densMeas hd hfin, map_norm_dilAvg h0]
  have hpreI : ∀ ε : ℝ, {x : Rd d | ε < ‖x‖} = (fun x : Rd d => ‖x‖) ⁻¹' Ioi ε := fun ε => rfl
  refine eq_of_rotationInvariant hd (densMeas_isometry ν) (fun Q => ?_) ?_ (dilAvg_zero h0)
    (fun ε hε => ?_) (fun ε hε => dilAvg_norm_gt_ne_top hfin hε) hrad
  · have h := dilAvg_map ν (Q : Rd d →L[ℝ] Rd d)
    have hQ : ν.map (Q : Rd d →L[ℝ] Rd d) = ν := hrot Q
    rw [hQ] at h
    exact h
  · haveI : Nontrivial (Rd d) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      infer_instance
    rw [densMeas, withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ (measure_singleton 0)
  · rw [hpreI, ← Measure.map_apply continuous_norm.measurable measurableSet_Ioi, hrad,
      Measure.map_apply continuous_norm.measurable measurableSet_Ioi, ← hpreI]
    exact dilAvg_norm_gt_ne_top hfin hε

/-! ## The contraction, pointwise -/

theorem lin_mexp_neg_smul (B : Mat d) (t : ℝ) (y : Rd d) :
    lin (mexp (t • B)) (lin (mexp (-t • B)) y) = y := by
  rw [show lin (mexp (t • B)) (lin (mexp (-t • B)) y)
      = lin (mexp (t • B) * mexp (-t • B)) y by rw [lin_mul]; rfl,
    ← mexp_add_smul, add_neg_cancel, zero_smul, mexp_zero, lin_one]
  rfl

theorem lin_mexp_smul_neg (B : Mat d) (t : ℝ) (y : Rd d) :
    lin (mexp (-t • B)) (lin (mexp (t • B)) y) = y := by
  rw [show lin (mexp (-t • B)) (lin (mexp (t • B)) y)
      = lin (mexp (-t • B) * mexp (t • B)) y by rw [lin_mul]; rfl,
    ← mexp_add_smul, neg_add_cancel, zero_smul, mexp_zero, lin_one]
  rfl

theorem continuousAt_radDens (hd : 1 ≤ d) {ν : Measure (Rd d)}
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) {y : Rd d} (hy : y ≠ 0) :
    ContinuousAt (radDens ν) y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hA := (sphereArea_eq_toSphere (d := d) hd).2
  have hK : ContinuousAt (radKr ν) ‖y‖ := (hasDerivAt_radKr hfin hn).continuousAt
  have hc1 : ContinuousAt (fun y : Rd d => radKr ν ‖y‖) y := hK.comp continuous_norm.continuousAt
  have hc2 : ContinuousAt (fun y : Rd d => sphereArea d * ‖y‖ ^ (d - 1)) y := by fun_prop
  exact hc1.div hc2 (by positivity)

/-- **The contraction of `ν_η`, pointwise**: `e^{t tr B} n(e^{tB}z) ≤ n(z)` for the density `n` of
`ν_η` and every `z ≠ 0`, when `(e^{-tB})_*ν ≤ ν`: the linear change of variables gives it almost
everywhere, and both sides are continuous off the origin. -/
theorem radDens_contract (hd : 1 ≤ d) {ν : Measure (Rd d)} (h0 : ν {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν)
    {B : Mat d} {t : ℝ} (hcon : push (mexp (-t • B)) ν ≤ ν) {z : Rd d} (hz : z ≠ 0) :
    Real.exp (t * B.trace) * radDens ν (lin (mexp (t • B)) z) ≤ radDens ν z := by
  haveI := sigmaFinite_of_null_finite h0 hfin
  set L := mexp (-t • B) with hL
  set L' := mexp (t • B) with hL'
  have hdetL : L.det = Real.exp (-t * B.trace) := det_mexp_smul B (-t)
  have hdet0 : L.det ≠ 0 := by rw [hdetL]; exact (Real.exp_pos _).ne'
  have hle : push L (densMeas ν) ≤ densMeas ν := by
    rw [densMeas_eq_dilAvg hd h0 hfin hrot, push]
    have h := dilAvg_map ν (lin L)
    rw [h]
    exact dilAvg_mono hcon
  set g : Rd d → ℝ≥0∞ := fun y => ENNReal.ofReal (radDens ν y) with hg
  have hgm : Measurable g := (measurable_radDens ν).ennreal_ofReal
  have hL'm : Measurable fun z : Rd d => lin L' z := (lin L').continuous.measurable
  set c := Real.exp (t * B.trace) with hc
  have hfm : Measurable fun z : Rd d => ENNReal.ofReal c * g (lin L' z) :=
    measurable_const.mul (hgm.comp hL'm)
  have hset : ∀ U : Set (Rd d), MeasurableSet U → volume U < ⊤ →
      ∫⁻ z in U, ENNReal.ofReal c * g (lin L' z) ≤ ∫⁻ z in U, g z := by
    intro U hU _
    have hpre : MeasurableSet (lin L ⁻¹' U) := (lin L).continuous.measurable hU
    have h1 := Measure.le_iff.1 hle U hU
    rw [push, Measure.map_apply (lin L).continuous.measurable hU, densMeas,
      withDensity_apply _ hpre, withDensity_apply _ hU] at h1
    have hG : Measurable (U.indicator fun z => g (lin L' z)) := (hgm.comp hL'm).indicator hU
    have hcv := lintegral_comp_lin hdet0 hG
    have hpt : ∀ y, U.indicator (fun z => g (lin L' z)) (lin L y) = (lin L ⁻¹' U).indicator g y := by
      intro y
      by_cases hy : lin L y ∈ U
      · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ lin L ⁻¹' U from hy), hL',
          lin_mexp_neg_smul]
      · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉ lin L ⁻¹' U from hy)]
    simp_rw [hpt] at hcv
    rw [lintegral_indicator hpre, lintegral_indicator hU, hdetL, abs_of_pos (Real.exp_pos _),
      neg_mul, Real.exp_neg, inv_inv] at hcv
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hcv]
    exact h1
  have hae := ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := (volume : Measure (Rd d))) hfm hset
  -- everywhere off the origin, by continuity
  have hcont1 : ∀ z : Rd d, z ≠ 0 → ContinuousAt (fun z => c * radDens ν (lin L' z)) z := by
    intro z hz
    have hLz : lin L' z ≠ 0 := by
      intro h
      apply hz
      rw [← lin_mexp_smul_neg B t z, ← hL', h, map_zero]
    exact continuousAt_const.mul ((continuousAt_radDens hd hfin hLz).comp
      (lin L').continuous.continuousAt)
  set V : Set (Rd d) := {z | z ≠ 0 ∧ radDens ν z < c * radDens ν (lin L' z)} with hV
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun z hzV => ?_
    have h1 : ∀ᶠ z' in 𝓝 z, z' ≠ 0 := isOpen_ne.mem_nhds hzV.1
    have h2 := (continuousAt_radDens hd hfin hzV.1).eventually_lt (hcont1 z hzV.1) hzV.2
    filter_upwards [h1, h2] with z' h1 h2 using ⟨h1, h2⟩
  have hV0 : volume V = 0 := by
    refine measure_mono_null (fun z hzV => ?_) (ae_iff.1 hae)
    intro hle'
    have hle'' : ENNReal.ofReal (c * radDens ν (lin L' z)) ≤ ENNReal.ofReal (radDens ν z) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact hle'
    have hdn : 0 ≤ radDens ν z := div_nonneg (radKr_nonneg _ _)
      (mul_nonneg (sphereArea_eq_toSphere hd).2.le (by positivity))
    rw [ENNReal.ofReal_le_ofReal_iff hdn] at hle''
    exact absurd hzV.2 (not_lt.2 hle'')
  have hVe : V = ∅ := (hVo.measure_eq_zero_iff volume).1 hV0
  by_contra hcon'
  have hzV : z ∈ V := ⟨hz, not_le.1 hcon'⟩
  rw [hVe] at hzV
  exact hzV

/-! ## The infinitesimal inequality -/

/-- `M(r) := K(r)/r^{d-1}`, so that the density of `ν_η` is `M(|y|)/|S^{d-1}|`. -/
noncomputable def radM (ν : Measure (Rd d)) (r : ℝ) : ℝ := radKr ν r / r ^ (d - 1)

theorem radDens_eq (ν : Measure (Rd d)) (y : Rd d) :
    radDens ν y = radM ν ‖y‖ / sphereArea d := by
  rw [radDens, radM, div_div, mul_comm]

theorem hasDerivAt_radM {ν : Measure (Rd d)} (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : HasDerivAt (radM ν) (deriv (radM ν) r) r := by
  have h := ((hasDerivAt_radKr hfin hr).differentiableAt.div
    (differentiableAt_pow (d - 1)) (pow_ne_zero _ hr.ne'))
  exact h.hasDerivAt

/-- A function largest at `0` on `[0, ∞)` has a nonpositive derivative there. Mathlib types only. -/
theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (h : ∀ t : ℝ, 0 < t → f t ≤ f 0) : f' ≤ 0 := by
  refine le_of_tendsto hf.tendsto_slope_zero_right
    (eventually_nhdsWithin_of_forall fun t (htp : 0 < t) => ?_)
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htp.le) (sub_nonpos.2 (h t htp))

/-- **The infinitesimal inequality** `tr B · M(r) + λ r M'(r) ≤ 0` for `r > 0`, `λ = λ_min(sym B)`:
the right derivative at `t = 0` of `e^{t tr B} M(|e^{tB} r v|)`, `v` a unit eigenvector of `sym B`
for `λ`, which is largest at `t = 0`. -/
theorem radM_ode (hd : 1 ≤ d) {ν : Measure (Rd d)} (h0 : ν {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤) (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν)
    {B : Mat d} (hcon : ∀ t : ℝ, 0 < t → push (mexp (-t • B)) ν ≤ ν) {r : ℝ} (hr : 0 < r) :
    B.trace * radM ν r + lamMin (symPart B) * r * deriv (radM ν) r ≤ 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hA := (sphereArea_eq_toSphere (d := d) hd).2
  obtain ⟨v, hv1, hv⟩ := exists_unit_eigvec_eigUp_zero (symPart_isHermitian B)
  rw [← lamMin_eq_eigUp_zero (symPart_isHermitian B)] at hv
  set l := lamMin (symPart B) with hl
  set c := B.trace with hc
  have hqv : quad B v = l := by
    rw [← quad_symPart, quad, hv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv1]
    ring
  set x : Rd d := r • v with hx
  have hxn : ‖x‖ = r := by rw [hx, norm_smul, hv1, mul_one, Real.norm_of_nonneg hr.le]
  set ρ : ℝ → ℝ := fun u => ‖lin (mexp (u • B)) x‖ with hρ
  have hρ0 : ρ 0 = r := by
    simp only [hρ, zero_smul, mexp_zero, lin_one]
    exact hxn
  -- the derivative of `ρ` at `0`
  have hsq := hasDerivAt_norm_sq_mexp B x 0
  have hsq0 : ‖lin (mexp ((0 : ℝ) • B)) x‖ ^ 2 ≠ 0 := by
    rw [zero_smul, mexp_zero, lin_one]
    change ‖x‖ ^ 2 ≠ 0
    rw [hxn]; positivity
  have hρd : HasDerivAt ρ (r * l) 0 := by
    have h := hsq.sqrt hsq0
    have hfun : (fun u : ℝ => Real.sqrt (‖lin (mexp (u • B)) x‖ ^ 2)) = ρ := by
      funext u; exact Real.sqrt_sq (norm_nonneg _)
    rw [hfun] at h
    convert h using 1
    rw [zero_smul, mexp_zero, lin_one]
    change r * l = 2 * quad B x / (2 * Real.sqrt (‖x‖ ^ 2))
    rw [Real.sqrt_sq (norm_nonneg _), hxn, hx, quad_smul_vec, hqv]
    field_simp
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hxn; exact hr.ne' hxn.symm
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * c)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const c).exp
    simpa using this
  have hMρ := HasDerivAt.comp_of_eq (0 : ℝ) (hasDerivAt_radM hfin hr) hρd hρ0.symm
  have hf := hexp.mul hMρ
  have hle := deriv_nonpos_of_right_max hf (fun t ht => ?_)
  · rw [Function.comp_apply, hρ0, zero_mul, Real.exp_zero, one_mul] at hle
    linarith [show deriv (radM ν) r * (r * l) = l * r * deriv (radM ν) r by ring]
  · show Real.exp (t * c) * radM ν (ρ t) ≤ Real.exp (0 * c) * radM ν (ρ 0)
    rw [hρ0, zero_mul, Real.exp_zero, one_mul]
    have hc' := radDens_contract hd h0 hfin hrot (hcon t ht) hx0
    rw [radDens_eq, radDens_eq, hxn, mul_div_assoc', div_le_div_iff_of_pos_right hA] at hc'
    exact hc'

/-! ## The budget -/

theorem measurable_radK (ν : Measure (Rd d)) [SFinite ν] : Measurable (radK ν) :=
  measurable_radK_integrand.lintegral_prod_left'

/-- `∫_0^∞ K(r) f(r) dr = ∫ f(|y|) ν_η(dy)`. -/
theorem lintegral_radK_mul {ν : Measure (Rd d)} [SFinite ν] (h0 : ν {0} = 0) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r in Ioi (0 : ℝ), radK ν r * f r = ∫⁻ y, f ‖y‖ ∂(dilAvg ν) := by
  have h := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioi (0 : ℝ)))
    (measurable_radK ν) hf
  rw [← map_norm_dilAvg h0, lintegral_map hf continuous_norm.measurable] at h
  exact h.symm

theorem min_sq_mul_le {s a : ℝ} (hs0 : 0 ≤ s) (hs : s < 3 / 2) (ha : 0 ≤ a) :
    min (s ^ 2 * a) 1 ≤ 9 / 4 * min a 1 := by
  have hs2 : s ^ 2 ≤ 9 / 4 := by nlinarith
  rcases le_or_gt a 1 with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right h.le]
    exact (min_le_right _ _).trans (by norm_num)

/-- `∫ (|y|² ∧ 1) ν_η(dy) < ∞`. -/
theorem lintegral_min_dilAvg_ne_top {ν : Measure (Rd d)}
    (hint : (∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν) ≠ ⊤) :
    (∫⁻ y, ENNReal.ofReal (min (‖y‖ ^ 2) 1) ∂(dilAvg ν)) ≠ ⊤ := by
  have hm : Measurable fun y : Rd d => ENNReal.ofReal (min (‖y‖ ^ 2) 1) := by fun_prop
  rw [lintegral_dilAvg ν hm]
  refine ne_top_of_le_ne_top (b := ∫⁻ x, (∫⁻ s, ENNReal.ofReal (eta s)) *
    (ENNReal.ofReal (9 / 4) * ENNReal.ofReal (min (‖x‖ ^ 2) 1)) ∂ν) ?_
    (lintegral_mono fun x => ?_)
  · rw [lintegral_const_mul _ (measurable_const.mul (by fun_prop)),
      lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_ne_top lintegral_eta.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint)
  · rw [← lintegral_mul_const _ measurable_eta.ennreal_ofReal]
    refine lintegral_mono fun s => ?_
    by_cases hs : eta s = 0
    · simp [hs]
    obtain ⟨hs1, hs2⟩ := eta_supp hs
    refine mul_le_mul_right ?_ _
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_smul, Real.norm_of_nonneg (by linarith), mul_pow]
    exact min_sq_mul_le (by linarith) hs2 (by positivity)

/-- `ν_η ≠ 0` when `ν ≠ 0`. -/
theorem dilAvg_univ_ne_zero {ν : Measure (Rd d)} (hne : ν ≠ 0) : dilAvg ν univ ≠ 0 := by
  rw [dilAvg_apply ν MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [lintegral_const]
  exact mul_ne_zero lintegral_eta.1 (fun h => hne (Measure.measure_univ_eq_zero.1 h))

/-- `∫_{Ioo 0 a} r^p dr = ∞` for `p ≤ -1`. Mathlib types only. -/
theorem lintegral_Ioo_rpow_eq_top {a p : ℝ} (ha : 0 < a) (hp : p ≤ -1) :
    ∫⁻ r in Ioo (0 : ℝ) a, ENNReal.ofReal (r ^ p) = ⊤ := by
  by_contra h
  have hint : IntegrableOn (fun r : ℝ => r ^ p) (Ioo 0 a) := by
    refine ⟨(measurable_id.pow_const p).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ fun r hr => Real.rpow_nonneg hr.1.le p))]
    exact lt_top_iff_ne_top.2 h
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ha).1 hint
  linarith

/-- `det e^{-tB} = e^{-t tr B} → 0` forces `tr B > 0`. -/
theorem trace_pos_of_expContracting (hd : 1 ≤ d) {B : Mat d} (hB : IsExpContracting B) :
    0 < B.trace := by
  have hdet : Tendsto (fun t : ℝ => (mexp (-t • B)).det) atTop (𝓝 0) := by
    have h := ((continuous_id.matrix_det).tendsto (0 : Mat d)).comp hB
    rwa [Function.comp_def, id, Matrix.det_zero ⟨⟨0, hd⟩⟩] at h
  by_contra h
  push Not at h
  have hge : ∀ t : ℝ, 0 ≤ t → 1 ≤ (mexp (-t • B)).det := fun t ht => by
    rw [det_mexp_smul]; exact Real.one_le_exp (by nlinarith)
  have := ge_of_tendsto hdet (eventually_atTop.2 ⟨0, hge⟩)
  norm_num at this

/-- **The budget for a contracted Lévy measure**: a rotation-invariant measure `ν ≠ 0` with
`ν{0} = 0`, `∫ (|x|² ∧ 1) dν < ∞` and `(e^{-tB})_*ν ≤ ν` for `t > 0`, `tr B > 0`, has
`tr B < (d+2) λ_min(sym B)`. Lean core. -/
theorem budget_of_contracting (hd : 1 ≤ d) (B : Mat d) (htr : 0 < B.trace)
    {ν : Measure (Rd d)} (h0 : ν {0} = 0)
    (hint : (∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν) ≠ ⊤) (hne : ν ≠ 0)
    (hrot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν)
    (hcon : ∀ t : ℝ, 0 < t → push (mexp (-t • B)) ν ≤ ν) :
    B.trace < ((d : ℝ) + 2) * lamMin (symPart B) := by
  have hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤ := fun ε hε =>
    measure_norm_gt_ne_top_of_lintegral hint hε
  haveI := sigmaFinite_of_null_finite h0 hfin
  set l := lamMin (symPart B) with hl
  set c := B.trace with hc
  have hode : ∀ r : ℝ, 0 < r → c * radM ν r + l * r * deriv (radM ν) r ≤ 0 := fun r hr =>
    radM_ode hd h0 hfin hrot hcon hr
  -- the finite radial integral
  have hI : (∫⁻ r in Ioi (0 : ℝ), radK ν r * ENNReal.ofReal (min (r ^ 2) 1)) ≠ ⊤ := by
    rw [lintegral_radK_mul h0 (by fun_prop)]
    exact lintegral_min_dilAvg_ne_top hint
  -- a radius where `K > 0`
  obtain ⟨r0, hr0, hK0⟩ : ∃ r0 : ℝ, 0 < r0 ∧ 0 < radKr ν r0 := by
    by_contra h
    push Not at h
    apply dilAvg_univ_ne_zero hne
    have h1 := lintegral_radK_mul h0 (f := fun _ => (1 : ℝ≥0∞)) measurable_const
    have hle : ∫⁻ r in Ioi (0 : ℝ), radK ν r * 1 ≤ 0 := by
      calc ∫⁻ r in Ioi (0 : ℝ), radK ν r * 1 ≤ ∫⁻ r in Ioi (0 : ℝ), (0 : ℝ≥0∞) :=
            setLIntegral_mono' measurableSet_Ioi fun r hr => by
              rw [mul_one, ← ofReal_radKr hfin hr, ENNReal.ofReal_eq_zero.2 (h r hr)]
        _ = 0 := lintegral_zero
    rw [h1, lintegral_one] at hle
    exact le_antisymm hle bot_le
  have hM0 : 0 < radM ν r0 := div_pos hK0 (pow_pos hr0 _)
  have hKM : ∀ r : ℝ, 0 < r → radKr ν r = r ^ (d - 1) * radM ν r := fun r hr => by
    rw [radM]; field_simp
  have hpow : ∀ r : ℝ, 0 < r → ∀ κ : ℝ, r ^ (d - 1) * r ^ 2 * r ^ (-κ) = r ^ ((d : ℝ) + 1 - κ) := by
    intro r hr κ
    rw [← pow_add, show d - 1 + 2 = d + 1 by omega, ← Real.rpow_natCast, ← Real.rpow_add hr]
    push_cast
    ring_nf
  by_contra hcon'
  push Not at hcon'
  rcases lt_trichotomy l 0 with hlneg | hl0 | hlpos
  rotate_left
  · have := hode r0 hr0
    rw [hl0, zero_mul, zero_mul, add_zero] at this
    nlinarith [mul_pos htr hM0]
  all_goals
    set κ := c / l with hκ
    set G : ℝ → ℝ := fun r => r ^ κ * radM ν r with hGdef
    have hG : ∀ r : ℝ, 0 < r → HasDerivAt G (κ * r ^ (κ - 1) * radM ν r + r ^ κ * deriv (radM ν) r) r :=
      fun r hr => (Real.hasDerivAt_rpow_const (Or.inl hr.ne')).mul (hasDerivAt_radM hfin hr)
    have hkey : ∀ r : ℝ, 0 < r → κ * r ^ (κ - 1) * radM ν r + r ^ κ * deriv (radM ν) r =
        r ^ (κ - 1) / l * (c * radM ν r + l * r * deriv (radM ν) r) := by
      intro r hr
      have hl' : l ≠ 0 := by first | exact hlneg.ne | exact hlpos.ne'
      rw [Real.rpow_sub_one hr.ne', hκ]
      field_simp
    have hGc : ContinuousOn G (Ioi 0) := fun r hr => (hG r hr).continuousAt.continuousWithinAt
    have hGd : DifferentiableOn ℝ G (interior (Ioi 0)) := by
      rw [interior_Ioi]; exact fun r hr => (hG r hr).differentiableAt.differentiableWithinAt
    have hC0 : 0 < r0 ^ κ * radM ν r0 := mul_pos (Real.rpow_pos_of_pos hr0 _) hM0
    have hlow : ∀ r : ℝ, 0 < r → r0 ^ κ * radM ν r0 ≤ G r →
        r0 ^ κ * radM ν r0 * r ^ (-κ) ≤ radM ν r := by
      intro r hr hle
      have h1 : r ^ (-κ) * r ^ κ = 1 := by
        rw [Real.rpow_neg hr.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hr _).ne']
      calc r0 ^ κ * radM ν r0 * r ^ (-κ) ≤ G r * r ^ (-κ) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hr.le _)
        _ = radM ν r := by
            simp only [hGdef]
            rw [mul_comm (r ^ κ), mul_assoc, mul_comm (r ^ κ), h1, mul_one]
    by_cases hlp : 0 < l
    · have hanti : AntitoneOn G (Ioi 0) := antitoneOn_of_deriv_nonpos (convex_Ioi 0) hGc hGd
        (fun r hr => by
          rw [interior_Ioi] at hr
          rw [(hG r hr).deriv, hkey r hr]
          exact mul_nonpos_of_nonneg_of_nonpos
            (div_nonneg (Real.rpow_nonneg (le_of_lt hr) _) hlp.le) (hode r hr))
      have hκd : (d : ℝ) + 2 ≤ κ := by rw [hκ, le_div_iff₀ hlp]; exact hcon'
      set r1 := min r0 1 with hr1
      have hr1p : 0 < r1 := lt_min hr0 one_pos
      set p := (d : ℝ) + 1 - κ with hp
      have hp1 : p ≤ -1 := by rw [hp]; linarith
      have hpt : ∀ r ∈ Ioo (0 : ℝ) r1, ENNReal.ofReal (r0 ^ κ * radM ν r0 * r ^ p) ≤
          radK ν r * ENNReal.ofReal (min (r ^ 2) 1) := by
        intro r hr
        have hr0' : 0 < r := hr.1
        have hrr0 : r ≤ r0 := hr.2.le.trans (min_le_left _ _)
        have hr1' : r ≤ 1 := hr.2.le.trans (min_le_right _ _)
        have hGr := hanti hr0' hr0 hrr0
        have hM := hlow r hr0' hGr
        rw [← ofReal_radKr hfin hr0', min_eq_left (by nlinarith),
          ← ENNReal.ofReal_mul (radKr_nonneg _ _), hKM r hr0']
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hp, ← hpow r hr0' κ]
        have h2 : 0 ≤ r ^ (d - 1) * r ^ 2 := by positivity
        calc r0 ^ κ * radM ν r0 * (r ^ (d - 1) * r ^ 2 * r ^ (-κ))
            = r ^ (d - 1) * r ^ 2 * (r0 ^ κ * radM ν r0 * r ^ (-κ)) := by ring
          _ ≤ r ^ (d - 1) * r ^ 2 * radM ν r := mul_le_mul_of_nonneg_left hM h2
          _ = r ^ (d - 1) * radM ν r * r ^ 2 := by ring
      apply hI
      refine top_le_iff.1 ?_
      calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (r0 ^ κ * radM ν r0) *
            ∫⁻ r in Ioo (0 : ℝ) r1, ENNReal.ofReal (r ^ p) := by
            rw [lintegral_Ioo_rpow_eq_top hr1p hp1, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC0).ne']
        _ = ∫⁻ r in Ioo (0 : ℝ) r1, ENNReal.ofReal (r0 ^ κ * radM ν r0 * r ^ p) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun r => ?_
            rw [ENNReal.ofReal_mul hC0.le]
        _ ≤ ∫⁻ r in Ioo (0 : ℝ) r1, radK ν r * ENNReal.ofReal (min (r ^ 2) 1) :=
            setLIntegral_mono' measurableSet_Ioo hpt
        _ ≤ ∫⁻ r in Ioi (0 : ℝ), radK ν r * ENNReal.ofReal (min (r ^ 2) 1) :=
            lintegral_mono_set Ioo_subset_Ioi_self
    · have hln : l < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hlp) with h | h
        · exact h
        · exact absurd h (by first | exact hlneg.ne | exact hlpos.ne')
      have hmono : MonotoneOn G (Ioi 0) := monotoneOn_of_deriv_nonneg (convex_Ioi 0) hGc hGd
        (fun r hr => by
          rw [interior_Ioi] at hr
          rw [(hG r hr).deriv, hkey r hr]
          exact mul_nonneg_of_nonpos_of_nonpos
            (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (le_of_lt hr) _) hln.le) (hode r hr))
      have hκn : κ < 0 := by rw [hκ]; exact div_neg_of_pos_of_neg htr hln
      set R := max r0 1 with hR
      have hpt : ∀ r ∈ Ioi R, ENNReal.ofReal (r0 ^ κ * radM ν r0) ≤
          radK ν r * ENNReal.ofReal (min (r ^ 2) 1) := by
        intro r hr
        have hrR : R < r := hr
        have hr1 : 1 ≤ r := (le_max_right _ _).trans hrR.le
        have hr0' : 0 < r := by linarith
        have hrr0 : r0 ≤ r := (le_max_left _ _).trans hrR.le
        have hGr := hmono hr0 hr0' hrr0
        have hM := hlow r hr0' hGr
        rw [← ofReal_radKr hfin hr0', min_eq_right (by nlinarith), ENNReal.ofReal_one, mul_one,
          hKM r hr0']
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 ≤ r ^ (-κ) := Real.one_le_rpow hr1 (by linarith)
        have h2 : 1 ≤ r ^ (d - 1) := one_le_pow₀ hr1
        have hMp : 0 ≤ radM ν r := le_trans (mul_pos hC0 (Real.rpow_pos_of_pos hr0' _)).le hM
        calc r0 ^ κ * radM ν r0 ≤ r0 ^ κ * radM ν r0 * r ^ (-κ) := le_mul_of_one_le_right hC0.le h1
          _ ≤ radM ν r := hM
          _ ≤ r ^ (d - 1) * radM ν r := le_mul_of_one_le_left hMp h2
      apply hI
      refine top_le_iff.1 ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ r in Ioi R, ENNReal.ofReal (r0 ^ κ * radM ν r0) := by
            rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC0).ne']
        _ ≤ ∫⁻ r in Ioi R, radK ν r * ENNReal.ofReal (min (r ^ 2) 1) :=
            setLIntegral_mono' measurableSet_Ioi hpt
        _ ≤ ∫⁻ r in Ioi (0 : ℝ), radK ν r * ENNReal.ofReal (min (r ^ 2) 1) :=
            lintegral_mono_set (Ioi_subset_Ioi (hr0.le.trans (le_max_left _ _)))

/-- **`prop:anisotropy-budget`(1)**: if `e^{-tB} → 0` as `t → ∞` and `μ` is a rotation-invariant
`B`-self-decomposable law on `ℝ^d` that is not Gaussian (a point mass counting as Gaussian), then
`λ := λ_min(sym B) > 0` and `tr B < (d+2)λ`. Spends A5 and A3(i)–(ii). -/
theorem anisotropy_budget (hd : 1 ≤ d) (B : Mat d) (hB : IsExpContracting B)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hrot : IsRotationInvariant μ)
    (hsd : IsBSelfDecomposable B μ) (hng : ¬ IsGaussian μ) :
    0 < lamMin (symPart B) ∧ B.trace < ((d : ℝ) + 2) * lamMin (symPart B) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨ν, h0, hint, hne, hrotν, hcon⟩ := anisotropy_levy B hB μ hrot hsd hng
  have hb := budget_of_contracting hd B (trace_pos_of_expContracting hd hB) h0 hint hne hrotν hcon
  have hge := trace_ge_card_mul_lamMin B
  exact ⟨by nlinarith, hb⟩

end AffineHemigroup
