/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableTail
import AffineHemigroup.Orbits

/-!
# `prop:log-orbit-rays`: an orbit of logarithmic exponent has positive increments on the rays only

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:log-orbit-rays` (wave 2, group C, Q-0281).
Lean core only.

## The route

The blueprint's blow-up, with the limit functional read directly. For a smooth compactly supported
real `φ`, `Λ(φ) := lim_{R↓0} ∫ φ(x/R) ρ(dx)` exists and equals `Re ∫ 𝓕φ(ξ) h(ξ) dξ`, with
`h(ξ) = (⟨ξ,Σξ⟩/⟨ξ,Σ'ξ⟩)^κ` (Fourier inversion and dominated convergence, through
`integral_test_eq_fourier` of `lem:stable-tail`). `Λ` is linear, positive and invariant under
dilations. **The Riesz representation is not used**: the annuli argument is run on `Λ` itself (a
nonnegative test function vanishing near `0` has `N Λ(φ) ≤ M Λ(χ)` for every `N`, by `N` dilates
with disjoint supports), so `Λ` vanishes on the test functions vanishing near `0`, and positivity
then gives `Λ(φ) = c₀ φ(0)`. **Density of `C_c^∞` in the Schwartz space is not used** either: the
test functions `ψ(x/n) cos 2π⟨a,x⟩` have `Λ = c₀`, and their Fourier side tends to `h(a)`.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real Filter Complex
open scoped MatrixOrder RealInnerProductSpace ENNReal Topology FourierTransform

variable {d : ℕ}

/-! ## The increment's transform and its blow-up -/

/-- The transform of a positive increment of the orbit of `μ_I`, `μ̂_I(ω) = e^{-g(|ω|²)}`. -/
theorem charFun_orbit_increment {g : ℝ → ℝ} {μI : Measure (Rd d)} [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) {ρ : Measure (Rd d)} [IsFiniteMeasure ρ]
    (h : affineOrbit μI S' = affineOrbit μI S ∗ ρ) (ω : Rd d) :
    charFun ρ ω = ((Real.exp (-(g (quad S' ω) - g (quad S ω))) : ℝ) : ℂ) := by
  have horb : ∀ T : Mat d, T.PosDef → charFun (affineOrbit μI T) ω =
      ((Real.exp (-g (quad T ω)) : ℝ) : ℂ) := fun T hT => by
    rw [affineOrbit, charFun_push _ (msqrt_mem_glSet hT), msqrt_transpose, hμI,
      norm_sq_lin_msqrt hT.posSemidef]
  have h2 := congrArg (fun m => charFun m ω) h
  haveI : IsProbabilityMeasure (affineOrbit μI S) := by unfold affineOrbit; infer_instance
  simp only [charFun_conv, horb S' hS', horb S hS] at h2
  have hne : ((Real.exp (-g (quad S ω)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  rw [show -(g (quad S' ω) - g (quad S ω)) = -g (quad S' ω) - (-g (quad S ω)) by ring,
    Real.exp_sub, Complex.ofReal_div, h2, mul_div_cancel_left₀ _ hne]

/-- **The blow-up limit** of the increment's transform: `ρ̂(tξ) → h(ξ) = (⟨ξ,Σξ⟩/⟨ξ,Σ'ξ⟩)^κ`
as `t → ∞`, for `ξ ≠ 0`. -/
theorem tendsto_charFun_blowup {g : ℝ → ℝ} {κ : ℝ}
    (hlog : ∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop (𝓝 (κ * Real.log c)))
    {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) {ρ : Measure (Rd d)}
    (hρ : ∀ ω, charFun ρ ω = ((Real.exp (-(g (quad S' ω) - g (quad S ω))) : ℝ) : ℂ))
    {ξ : Rd d} (hξ : ξ ≠ 0) :
    Tendsto (fun R : ℝ => charFun ρ ((2 * π * R⁻¹) • ξ)) (𝓝[>] 0)
      (𝓝 (((quad S ξ / quad S' ξ) ^ κ : ℝ) : ℂ)) := by
  have hq := quad_pos hS hξ
  have hq' := quad_pos hS' hξ
  set c := quad S' ξ / quad S ξ with hc
  have hc0 : 0 < c := div_pos hq' hq
  -- `u(R) = (2π/R)² ⟨ξ,Σξ⟩ → ∞`
  have hu : Tendsto (fun R : ℝ => (2 * π * R⁻¹) ^ 2 * quad S ξ) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun R : ℝ => 2 * π * R⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
    exact (tendsto_pow_atTop two_ne_zero |>.comp h1).atTop_mul_const hq
  have hlim := ((hlog c hc0).comp hu)
  set u : ℝ → ℝ := fun R => (2 * π * R⁻¹) ^ 2 * quad S ξ with hudef
  have hval : ∀ R : ℝ, charFun ρ ((2 * π * R⁻¹) • ξ) =
      ((Real.exp (-(g (c * u R) - g (u R))) : ℝ) : ℂ) := by
    intro R
    rw [hρ, quad_smul_vec, quad_smul_vec]
    congr 4
    simp only [hudef, hc]
    field_simp
  simp_rw [hval]
  have hexp : Real.exp (-(κ * Real.log c)) = (quad S ξ / quad S' ξ) ^ κ := by
    rw [show -(κ * Real.log c) = Real.log c * (-κ) by ring, ← Real.rpow_def_of_pos hc0,
      Real.rpow_neg hc0.le, ← Real.inv_rpow hc0.le, hc, inv_div]
  rw [← hexp]
  exact (Complex.continuous_ofReal.tendsto _).comp
    ((Real.continuous_exp.tendsto _).comp (hlim.neg))

/-- `h(ξ) = (⟨ξ,Σξ⟩/⟨ξ,Σ'ξ⟩)^κ` is bounded. -/
theorem exists_bound_ratio_rpow {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef) {κ : ℝ}
    (hκ : 0 < κ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Rd d, (quad S ξ / quad S' ξ) ^ κ ≤ C := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, zero_le_one, fun ξ => ?_⟩
    have : ξ = 0 := Subsingleton.elim _ _
    subst this
    simp [quad_eq_dotProduct, Real.zero_rpow hκ.ne']
  haveI : NeZero d := ⟨hd.ne'⟩
  -- `⟨ξ,Σξ⟩ ≤ λ_max(Σ)|ξ|²` and `⟨ξ,Σ'ξ⟩ ≥ λ_min(Σ')|ξ|²`
  have hl' := lamMin_pos hS'
  have hup : ∀ ξ : Rd d, quad S ξ ≤ lamMax S * ‖ξ‖ ^ 2 := fun ξ => by
    have h := quad_nonneg ((posSemidef_smul_one_sub_iff hS.isHermitian
      (eigUp S (Fin.rev 0))).2 le_rfl) ξ
    rw [quad_sub, quad_smul, quad_one] at h
    rw [lamMax_eq_eigUp_last hS.isHermitian]
    linarith
  have hlow : ∀ ξ : Rd d, lamMin S' * ‖ξ‖ ^ 2 ≤ quad S' ξ := fun ξ =>
    lamMin_mul_norm_sq_le hS'.isHermitian ξ
  have hLmax : 0 ≤ lamMax S := by
    have := hup (ebasis (0 : Fin d))
    have h1 : ‖ebasis (0 : Fin d)‖ = 1 := by simp [ebasis]
    rw [h1] at this
    have h2 := quad_nonneg hS.posSemidef (ebasis (0 : Fin d))
    nlinarith
  refine ⟨(lamMax S / lamMin S') ^ κ, by positivity, fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [quad_eq_dotProduct, Real.zero_rpow hκ.ne']; positivity
  have hq := quad_pos hS hξ
  have hq' := quad_pos hS' hξ
  have hn : 0 < ‖ξ‖ ^ 2 := by have := norm_pos_iff.2 hξ; positivity
  refine Real.rpow_le_rpow (by positivity) ?_ hκ.le
  rw [div_le_div_iff₀ hq' hl']
  calc quad S ξ * lamMin S' ≤ lamMax S * ‖ξ‖ ^ 2 * lamMin S' :=
        mul_le_mul_of_nonneg_right (hup ξ) hl'.le
    _ = lamMax S * (lamMin S' * ‖ξ‖ ^ 2) := by ring
    _ ≤ lamMax S * quad S' ξ := mul_le_mul_of_nonneg_left (hlow ξ) hLmax

/-! ## Test functions and the limit functional -/

/-- **A test function**: smooth with compact support, real-valued. -/
def IsRealTestFn (φ : Rd d → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

namespace IsRealTestFn

variable {φ ψ : Rd d → ℝ}

theorem continuous (h : IsRealTestFn φ) : Continuous φ := h.1.continuous

theorem add (hφ : IsRealTestFn φ) (hψ : IsRealTestFn ψ) : IsRealTestFn (fun x => φ x + ψ x) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

theorem const_mul (hφ : IsRealTestFn φ) (c : ℝ) : IsRealTestFn (fun x => c * φ x) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.mul_left⟩

theorem sub (hφ : IsRealTestFn φ) (hψ : IsRealTestFn ψ) : IsRealTestFn (fun x => φ x - ψ x) :=
  ⟨hφ.1.sub hψ.1, hφ.2.sub hψ.2⟩

theorem mul_smooth (hφ : IsRealTestFn φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    IsRealTestFn (fun x => φ x * ψ x) :=
  ⟨hφ.1.mul hψ, hφ.2.mul_right⟩

theorem dilate (hφ : IsRealTestFn φ) {c : ℝ} (hc : c ≠ 0) : IsRealTestFn (fun x => φ (c • x)) :=
  ⟨hφ.1.comp (contDiff_const_smul c), hφ.2.comp_smul hc⟩

theorem sum (hφ : IsRealTestFn φ) {c : ℕ → ℝ} (hc : ∀ n, c n ≠ 0) (N : ℕ) :
    IsRealTestFn (fun x => ∑ n ∈ Finset.range N, φ (c n • x)) := by
  induction N with
  | zero => exact ⟨contDiff_const, HasCompactSupport.zero⟩
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact ih.add (hφ.dilate (hc N))

theorem bump (b : ContDiffBump (0 : Rd d)) : IsRealTestFn (b : Rd d → ℝ) :=
  ⟨b.contDiff, b.hasCompactSupport⟩

theorem bounded (hφ : IsRealTestFn φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |φ x| ≤ M := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- A test function vanishing near `0` vanishes on a ball `B(0, r)` and off a ball `B(0, R)`. -/
theorem exists_annulus (hφ : IsRealTestFn φ) (h0 : (0 : Rd d) ∉ tsupport φ) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ R ∧ (∀ x, ‖x‖ < r → φ x = 0) ∧ ∀ x, R < ‖x‖ → φ x = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport φ).isOpen_compl 0 h0
  obtain ⟨R0, hR0⟩ := hφ.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨r, max R0 r, hr, le_max_right _ _, fun x hx => ?_, fun x hx => ?_⟩
  · exact image_eq_zero_of_notMem_tsupport (hball (by simpa using hx))
  · refine image_eq_zero_of_notMem_tsupport fun hx' => ?_
    have := hR0 hx'
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R0 r]

end IsRealTestFn

/-- **The limit functional** `Λ(φ) := lim_{R↓0} ∫ φ(x/R) ρ(dx)`. -/
noncomputable def blowLim (ρ : Measure (Rd d)) (φ : Rd d → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ

section Blow

variable {ρ : Measure (Rd d)} [IsFiniteMeasure ρ]

/-- The hypothesis that every test function has a limit. -/
def HasBlowLim (ρ : Measure (Rd d)) : Prop :=
  ∀ φ : Rd d → ℝ, IsRealTestFn φ → ∃ c : ℝ,
    Tendsto (fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ) (𝓝[>] 0) (𝓝 c)

theorem blowLim_tendsto (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ) :
    Tendsto (fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ) (𝓝[>] 0) (𝓝 (blowLim ρ φ)) :=
  tendsto_nhds_limUnder (hex φ hφ)

theorem integrable_test {φ : Rd d → ℝ} (hφ : IsRealTestFn φ) (R : ℝ) :
    Integrable (fun x => φ (R⁻¹ • x)) ρ := by
  obtain ⟨M, -, hM⟩ := hφ.bounded
  exact Integrable.of_bound ((hφ.continuous.comp (continuous_const_smul _)).aestronglyMeasurable)
    M (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM _)

theorem blowLim_add (hex : HasBlowLim ρ) {φ ψ : Rd d → ℝ} (hφ : IsRealTestFn φ) (hψ : IsRealTestFn ψ) :
    blowLim ρ (fun x => φ x + ψ x) = blowLim ρ φ + blowLim ρ ψ := by
  refine tendsto_nhds_unique (blowLim_tendsto hex (hφ.add hψ)) ?_
  refine ((blowLim_tendsto hex hφ).add (blowLim_tendsto hex hψ)).congr fun R => ?_
  rw [integral_add (integrable_test hφ R) (integrable_test hψ R)]

theorem blowLim_const_mul (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ) (c : ℝ) :
    blowLim ρ (fun x => c * φ x) = c * blowLim ρ φ := by
  refine tendsto_nhds_unique (blowLim_tendsto hex (hφ.const_mul c)) ?_
  refine ((blowLim_tendsto hex hφ).const_mul c).congr fun R => ?_
  rw [integral_const_mul]

theorem blowLim_sub (hex : HasBlowLim ρ) {φ ψ : Rd d → ℝ} (hφ : IsRealTestFn φ) (hψ : IsRealTestFn ψ) :
    blowLim ρ (fun x => φ x - ψ x) = blowLim ρ φ - blowLim ρ ψ := by
  refine tendsto_nhds_unique (blowLim_tendsto hex (hφ.sub hψ)) ?_
  refine ((blowLim_tendsto hex hφ).sub (blowLim_tendsto hex hψ)).congr fun R => ?_
  rw [integral_sub (integrable_test hφ R) (integrable_test hψ R)]

theorem blowLim_nonneg (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ)
    (hnn : ∀ x, 0 ≤ φ x) : 0 ≤ blowLim ρ φ :=
  ge_of_tendsto (blowLim_tendsto hex hφ) (Eventually.of_forall fun R =>
    integral_nonneg fun x => hnn _)

theorem blowLim_mono (hex : HasBlowLim ρ) {φ ψ : Rd d → ℝ} (hφ : IsRealTestFn φ) (hψ : IsRealTestFn ψ)
    (hle : ∀ x, φ x ≤ ψ x) : blowLim ρ φ ≤ blowLim ρ ψ := by
  have := blowLim_nonneg hex (hψ.sub hφ) fun x => sub_nonneg.2 (hle x)
  rw [blowLim_sub hex hψ hφ] at this
  linarith

/-- **`Λ` is invariant under dilations**. -/
theorem blowLim_dilate (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ) {c : ℝ}
    (hc : 0 < c) : blowLim ρ (fun x => φ (c • x)) = blowLim ρ φ := by
  refine tendsto_nhds_unique (blowLim_tendsto hex (hφ.dilate hc.ne')) ?_
  have hmul : Tendsto (fun R : ℝ => c⁻¹ * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun R : ℝ => c⁻¹ * R) (𝓝 0) (𝓝 (c⁻¹ * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with R hR
      exact mul_pos (inv_pos.2 hc) hR
  refine ((blowLim_tendsto hex hφ).comp hmul).congr fun R => ?_
  simp only [Function.comp_apply, smul_smul, mul_inv, inv_inv]

theorem blowLim_sum_dilate (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ) {c : ℕ → ℝ}
    (hc : ∀ n, 0 < c n) (N : ℕ) :
    blowLim ρ (fun x => ∑ n ∈ Finset.range N, φ (c n • x)) = N * blowLim ρ φ := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]
    have := blowLim_const_mul hex hφ 0
    simp only [zero_mul] at this
    exact this
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [blowLim_add hex (hφ.sum (fun n => (hc n).ne') N) (hφ.dilate (hc N).ne'), ih,
      blowLim_dilate hex hφ (hc N)]
    push_cast
    ring

/-- **A nonnegative test function vanishing near `0` has `Λ = 0`**: `N` dilates with disjoint
supports sum to at most `sup φ`, so `N Λ(φ) ≤ (sup φ) Λ(χ)` for every `N`. -/
theorem blowLim_eq_zero_of_nonneg (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ)
    (hnn : ∀ x, 0 ≤ φ x) (h0 : (0 : Rd d) ∉ tsupport φ) : blowLim ρ φ = 0 := by
  obtain ⟨r, R, hr, hrR, hin, hout⟩ := hφ.exists_annulus h0
  obtain ⟨M, hM0, hM⟩ := hφ.bounded
  set lam := R / r + 1 with hlam
  have hlam1 : 1 < lam := by have : 0 < R / r := div_pos (hr.trans_le hrR) hr; linarith
  have hlamr : R < lam * r := by
    rw [hlam, add_mul, div_mul_cancel₀ _ hr.ne']; linarith
  have hpow : ∀ n : ℕ, 0 < lam ^ n := fun n => pow_pos (by linarith) n
  -- a nonzero term pins `‖lam^n x‖` in `[r, R]`
  have hpin : ∀ (n : ℕ) (x : Rd d), φ (lam ^ n • x) ≠ 0 →
      r ≤ lam ^ n * ‖x‖ ∧ lam ^ n * ‖x‖ ≤ R := by
    intro n x hne
    have hn : ‖lam ^ n • x‖ = lam ^ n * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hpow n).le]
    refine ⟨?_, ?_⟩
    · by_contra h; push Not at h; exact hne (hin _ (hn ▸ h))
    · by_contra h; push Not at h; exact hne (hout _ (hn ▸ h))
  -- at most one nonzero term
  have huniq : ∀ (x : Rd d) (n m : ℕ), φ (lam ^ n • x) ≠ 0 → φ (lam ^ m • x) ≠ 0 → n = m := by
    intro x n m hn hm
    by_contra hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · have h1 := (hpin n x hn).1
      have h2 := (hpin m x hm).2
      have : lam ^ m * ‖x‖ ≥ lam * (lam ^ n * ‖x‖) := by
        have hpm : lam ^ m ≥ lam ^ (n + 1) := pow_le_pow_right₀ hlam1.le h
        rw [pow_succ] at hpm
        nlinarith [norm_nonneg x, hpow n]
      nlinarith
    · have h1 := (hpin m x hm).1
      have h2 := (hpin n x hn).2
      have : lam ^ n * ‖x‖ ≥ lam * (lam ^ m * ‖x‖) := by
        have hpm : lam ^ n ≥ lam ^ (m + 1) := pow_le_pow_right₀ hlam1.le h
        rw [pow_succ] at hpm
        nlinarith [norm_nonneg x, hpow m]
      nlinarith
  set ψ : ℕ → Rd d → ℝ := fun N x => ∑ n ∈ Finset.range N, φ (lam ^ n • x) with hψ
  have hψle : ∀ N x, ψ N x ≤ M := by
    intro N x
    by_cases hex' : ∃ n ∈ Finset.range N, φ (lam ^ n • x) ≠ 0
    · obtain ⟨n0, hn0, hne⟩ := hex'
      simp only [hψ]
      rw [Finset.sum_eq_single n0 (fun m _ hm => by
        by_contra h; exact hm (huniq x m n0 h hne)) (fun h => absurd hn0 h)]
      exact (le_abs_self _).trans (hM _)
    · push Not at hex'
      simp only [hψ]
      rw [Finset.sum_eq_zero hex']
      exact hM0
  have hψout : ∀ N x, R < ‖x‖ → ψ N x = 0 := by
    intro N x hx
    refine Finset.sum_eq_zero fun n _ => ?_
    by_contra hne
    have := (hpin n x hne).2
    have h1 : 1 ≤ lam ^ n := one_le_pow₀ hlam1.le
    nlinarith [norm_nonneg x]
  -- the bump `χ = 1` on `B̄(0, R)`
  let χ : ContDiffBump (0 : Rd d) := ⟨R, R + 1, hr.trans_le hrR, by linarith⟩
  have hχ := IsRealTestFn.bump χ
  have hle : ∀ N x, ψ N x ≤ M * χ x := by
    intro N x
    by_cases hx : ‖x‖ ≤ R
    · rw [χ.one_of_mem_closedBall (by simpa using hx), mul_one]; exact hψle N x
    · rw [hψout N x (lt_of_not_ge hx)]; exact mul_nonneg hM0 χ.nonneg
  have hN : ∀ N : ℕ, (N : ℝ) * blowLim ρ φ ≤ M * blowLim ρ χ := by
    intro N
    rw [← blowLim_sum_dilate hex hφ hpow N, ← blowLim_const_mul hex hχ M]
    exact blowLim_mono hex (hφ.sum (fun n => (hpow n).ne') N) (hχ.const_mul M) (hle N)
  have h0le := blowLim_nonneg hex hφ hnn
  by_contra hne
  have hpos : 0 < blowLim ρ φ := lt_of_le_of_ne h0le (Ne.symm hne)
  obtain ⟨N, hNgt⟩ := exists_nat_gt (M * blowLim ρ χ / blowLim ρ φ)
  have := hN N
  rw [div_lt_iff₀ hpos] at hNgt
  linarith

/-- **Every test function vanishing near `0` has `Λ = 0`**: it is a difference of two
nonnegative ones, through an annular bump. -/
theorem blowLim_eq_zero (hex : HasBlowLim ρ) {φ : Rd d → ℝ} (hφ : IsRealTestFn φ)
    (h0 : (0 : Rd d) ∉ tsupport φ) : blowLim ρ φ = 0 := by
  obtain ⟨r, R, hr, hrR, hin, hout⟩ := hφ.exists_annulus h0
  obtain ⟨M, hM0, hM⟩ := hφ.bounded
  let bin : ContDiffBump (0 : Rd d) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let bout : ContDiffBump (0 : Rd d) := ⟨R, R + 1, hr.trans_le hrR, by linarith⟩
  set χ : Rd d → ℝ := fun x => bout x * (1 - bin x) with hχ
  have hχt : IsRealTestFn χ :=
    (IsRealTestFn.bump bout).mul_smooth (contDiff_const.sub bin.contDiff)
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => mul_nonneg bout.nonneg (sub_nonneg.2 bin.le_one)
  have hχ1 : ∀ x, φ x ≠ 0 → χ x = 1 := by
    intro x hx
    have hx1 : r ≤ ‖x‖ := by by_contra h; push Not at h; exact hx (hin x h)
    have hx2 : ‖x‖ ≤ R := by by_contra h; push Not at h; exact hx (hout x h)
    have hb1 : bout x = 1 := bout.one_of_mem_closedBall (by simpa using hx2)
    have hb2 : bin x = 0 := by
      have : x ∉ Function.support bin := by
        rw [bin.support_eq, Metric.mem_ball, dist_zero_right]; exact not_lt.2 (by change r / 2 ≤ ‖x‖; linarith)
      simpa using this
    simp [hχ, hb1, hb2]
  have hnear : ∀ x : Rd d, ‖x‖ < r / 4 → χ x = 0 := by
    intro x hx
    have : bin x = 1 := bin.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; change ‖x‖ ≤ r / 4; linarith)
    simp [hχ, this]
  have hev : ∀ f : Rd d → ℝ, (∀ x : Rd d, ‖x‖ < r / 4 → f x = 0) → (0 : Rd d) ∉ tsupport f := by
    intro f hf
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds (0 : Rd d) (by positivity : (0 : ℝ) < r / 4)] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hf x hx
  have hA : blowLim ρ (fun x => φ x + M * χ x) = 0 := by
    refine blowLim_eq_zero_of_nonneg hex (hφ.add (hχt.const_mul M)) (fun x => ?_) (hev _ fun x hx => ?_)
    · by_cases hx : φ x = 0
      · rw [hx, zero_add]; exact mul_nonneg hM0 (hχ0 x)
      · rw [hχ1 x hx, mul_one]; linarith [neg_abs_le (φ x), hM x]
    · rw [hin x (by linarith), hnear x hx, mul_zero, add_zero]
  have hB : blowLim ρ χ = 0 := blowLim_eq_zero_of_nonneg hex hχt hχ0 (hev _ hnear)
  rw [blowLim_add hex hφ (hχt.const_mul M), blowLim_const_mul hex hχt, hB, mul_zero,
    add_zero] at hA
  exact hA

/-- **`Λ(φ) = c₀ φ(0)`**: the limit functional is a multiple of the point mass at `0`. -/
theorem blowLim_eq_mul_eval_zero (hex : HasBlowLim ρ) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ φ : Rd d → ℝ, IsRealTestFn φ → blowLim ρ φ = c₀ * φ 0 := by
  let χ : ContDiffBump (0 : Rd d) := ⟨1, 2, one_pos, by norm_num⟩
  have hχ := IsRealTestFn.bump χ
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
  refine ⟨blowLim ρ χ, blowLim_nonneg hex hχ fun x => χ.nonneg, fun φ hφ => ?_⟩
  set ψ : Rd d → ℝ := fun x => φ x - φ 0 * χ x with hψ
  have hψt : IsRealTestFn ψ := hφ.sub (hχ.const_mul (φ 0))
  have hψ0 : ψ 0 = 0 := by simp [hψ, hχ0]
  -- `|Λ(ψ)| ≤ η Λ(χ)` for every `η > 0`
  have hsmall : ∀ η : ℝ, 0 < η → |blowLim ρ ψ| ≤ η * blowLim ρ χ := by
    intro η hη
    obtain ⟨δ', hδ', hδ'ψ⟩ := Metric.continuousAt_iff.1 hψt.continuous.continuousAt η hη
    set δ := min (δ' / 2) (1 / 2) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδ1 : 2 * δ ≤ 1 := by have := min_le_right (δ' / 2) (1 / 2); linarith
    have hδ2 : 2 * δ ≤ δ' := by have := min_le_left (δ' / 2) (1 / 2); linarith
    let b : ContDiffBump (0 : Rd d) := ⟨δ, 2 * δ, hδ0, by linarith⟩
    have hbt := IsRealTestFn.bump b
    set ψ1 : Rd d → ℝ := fun x => ψ x * (1 - b x) with hψ1
    set ψ2 : Rd d → ℝ := fun x => ψ x * b x with hψ2
    have hψ1t : IsRealTestFn ψ1 := hψt.mul_smooth (contDiff_const.sub b.contDiff)
    have hψ2t : IsRealTestFn ψ2 := hψt.mul_smooth b.contDiff
    have hsplit : ψ = fun x => ψ1 x + ψ2 x := by
      funext x; simp only [hψ1, hψ2]; ring
    have h1 : blowLim ρ ψ1 = 0 := by
      refine blowLim_eq_zero hex hψ1t ?_
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [Metric.ball_mem_nhds (0 : Rd d) hδ0] with x hx
      have : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
      simp [hψ1, this]
    -- `|ψ₂| ≤ η χ`
    have hbound : ∀ x, |ψ2 x| ≤ η * χ x := by
      intro x
      by_cases hx : ‖x‖ < 2 * δ
      · have hψx : |ψ x| ≤ η := by
          have := hδ'ψ (show dist x 0 < δ' by rw [dist_zero_right]; linarith)
          rw [hψ0, Real.dist_eq, sub_zero] at this
          exact this.le
        rw [χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; linarith),
          mul_one, hψ2, abs_mul, abs_of_nonneg b.nonneg]
        calc |ψ x| * b x ≤ η * 1 := mul_le_mul hψx b.le_one b.nonneg hη.le
          _ = η := mul_one η
      · have : b x = 0 := by
          have hns : x ∉ Function.support b := by
            rw [b.support_eq, Metric.mem_ball, dist_zero_right]; exact hx
          simpa using hns
        rw [hψ2]; simp only [this, mul_zero, abs_zero]
        exact mul_nonneg hη.le χ.nonneg
    have hup : blowLim ρ ψ2 ≤ η * blowLim ρ χ := by
      rw [← blowLim_const_mul hex hχ η]
      exact blowLim_mono hex hψ2t (hχ.const_mul η) fun x => (le_abs_self _).trans (hbound x)
    have hlow : -(η * blowLim ρ χ) ≤ blowLim ρ ψ2 := by
      have := blowLim_mono hex (hχ.const_mul (-η)) hψ2t fun x => by
        have := hbound x
        rw [abs_le] at this
        linarith
      rw [blowLim_const_mul hex hχ] at this
      linarith
    rw [hsplit, blowLim_add hex hψ1t hψ2t, h1, zero_add, abs_le]
    exact ⟨hlow, hup⟩
  have hψ0' : blowLim ρ ψ = 0 := by
    by_contra hne
    have hpos : 0 < |blowLim ρ ψ| := abs_pos.2 hne
    have hc0 : 0 ≤ blowLim ρ χ := blowLim_nonneg hex hχ fun x => χ.nonneg
    rcases hc0.lt_or_eq with hc | hc
    · have := hsmall (|blowLim ρ ψ| / (2 * blowLim ρ χ)) (by positivity)
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hc.ne'] at this
      linarith
    · have := hsmall 1 one_pos
      rw [← hc, mul_zero] at this
      linarith
  have := blowLim_sub hex hφ (hχ.const_mul (φ 0))
  rw [← hψ, hψ0', blowLim_const_mul hex hχ] at this
  linarith

end Blow

/-! ## The limit through the Fourier side -/

theorem testSchwartz_coe (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : (testSchwartz φ hφ hc : Rd d → ℂ) = fun x => (φ x : ℂ) := rfl

/-- **The limit functional on the Fourier side**: for a probability measure `ρ` whose transform
blows up to a bounded `h` off the origin, `∫ φ(x/R) ρ(dx) → Re ∫ 𝓕φ(ξ) h(ξ) dξ` as `R ↓ 0`. -/
theorem tendsto_blow_fourier [NeZero d] {ρ : Measure (Rd d)} [IsProbabilityMeasure ρ]
    {h : Rd d → ℝ} (hblow : ∀ ξ : Rd d, ξ ≠ 0 →
      Tendsto (fun R : ℝ => charFun ρ ((2 * π * R⁻¹) • ξ)) (𝓝[>] 0) (𝓝 (h ξ : ℂ)))
    (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    Tendsto (fun R : ℝ => ∫ x, φ (R⁻¹ • x) ∂ρ) (𝓝[>] 0)
      (𝓝 (∫ ξ, (𝓕 (testSchwartz φ hφ hc)) ξ * (h ξ : ℂ)).re) := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  set Φ : Rd d → ℂ := fun ξ => (𝓕 (testSchwartz φ hφ hc)) ξ with hΦ
  have hΦi : Integrable Φ := (𝓕 (testSchwartz φ hφ hc)).integrable
  have hΦc : Continuous Φ := (𝓕 (testSchwartz φ hφ hc)).continuous
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun (R : ℝ) ξ => Φ ξ * charFun ρ ((2 * π * R⁻¹) • ξ))
    (f := fun ξ => Φ ξ * (h ξ : ℂ)) (fun ξ => ‖Φ ξ‖) ?_ ?_ hΦi.norm ?_
  · have hc' : Tendsto (fun R : ℝ => (((∫ x, φ (R⁻¹ • x) ∂ρ : ℝ)) : ℂ)) (𝓝[>] 0)
        (𝓝 (∫ ξ, Φ ξ * (h ξ : ℂ))) := by
      refine hdom.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with R hR
      exact (integral_test_eq_fourier φ hφ hc ρ hR).symm
    have := (Complex.continuous_re.tendsto _).comp hc'
    exact this.congr fun R => by simp
  · refine Eventually.of_forall fun R => Continuous.aestronglyMeasurable ?_
    exact hΦc.mul (continuous_charFun.comp (continuous_const_smul _))
  · refine Eventually.of_forall fun R => Eventually.of_forall fun ξ => ?_
    rw [norm_mul]
    calc ‖Φ ξ‖ * ‖charFun ρ ((2 * π * R⁻¹) • ξ)‖ ≤ ‖Φ ξ‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_charFun_le_one _) (norm_nonneg _)
      _ = ‖Φ ξ‖ := mul_one _
  · have h0 : ∀ᵐ ξ ∂(volume : Measure (Rd d)), ξ ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, setOf_eq_eq_singleton, measure_singleton]
    filter_upwards [h0] with ξ hξ
    exact (hblow ξ hξ).const_mul (Φ ξ)

/-- `∫ e^{-2πi⟨x,ζ⟩} ψ(x/N) dx = N^d 𝓕ψ(Nζ)`. -/
theorem fourier_dilate (ψ : Rd d → ℝ) {N : ℝ} (hN : 0 < N) (ζ : Rd d) :
    ∫ x, Complex.exp (↑(-2 * π * ⟪x, ζ⟫) * Complex.I) * ((ψ (N⁻¹ • x)) : ℂ) =
      ((N ^ d : ℝ) : ℂ) * ∫ y, Complex.exp (↑(-2 * π * ⟪y, N • ζ⟫) * Complex.I) * ((ψ y) : ℂ) := by
  set f : Rd d → ℂ := fun x => Complex.exp (↑(-2 * π * ⟪x, ζ⟫) * Complex.I) * ((ψ (N⁻¹ • x)) : ℂ)
    with hf
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Rd d))) f N
  rw [finrank_euclideanSpace_fin] at h
  have hpos : (0 : ℝ) < N ^ d := pow_pos hN d
  rw [abs_of_pos (inv_pos.2 hpos)] at h
  have h2 : ∫ x, f x = ((N ^ d : ℝ) : ℂ) * ∫ x, f (N • x) := by
    rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne',
      Complex.ofReal_one, one_mul]
  rw [h2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hf, smul_smul, inv_mul_cancel₀ hN.ne', one_smul, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]

/-- **The Fourier transform of a modulated dilate**: for `φ(x) = ψ(x/N) cos 2π⟨a,x⟩`,
`𝓕φ(ξ) = (N^d/2)(𝓕ψ(N(ξ - a)) + 𝓕ψ(N(ξ + a)))`. -/
theorem fourier_test_cos (ψ : Rd d → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) {N : ℝ} (hN : 0 < N) (a : Rd d)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫))
    (hcφ : HasCompactSupport fun x => ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫)) (ξ : Rd d) :
    (𝓕 (testSchwartz _ hφ hcφ)) ξ = ((N ^ d : ℝ) : ℂ) / 2 *
      ((𝓕 (testSchwartz ψ hψ hc)) (N • (ξ - a)) + (𝓕 (testSchwartz ψ hψ hc)) (N • (ξ + a))) := by
  have hint : ∀ ζ : Rd d, Integrable fun x : Rd d =>
      Complex.exp (↑(-2 * π * ⟪x, ζ⟫) * Complex.I) * ((ψ (N⁻¹ • x)) : ℂ) := by
    intro ζ
    have hψN : Integrable fun x : Rd d => ((ψ (N⁻¹ • x)) : ℂ) :=
      ((Complex.continuous_ofReal.comp (hψ.continuous.comp (continuous_const_smul _))).integrable_of_hasCompactSupport
        ((hc.comp_smul (inv_ne_zero hN.ne')).comp_left Complex.ofReal_zero))
    refine hψN.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [SchwartzMap.fourier_coe, testSchwartz_coe, Real.fourier_eq', SchwartzMap.fourier_coe,
    testSchwartz_coe, Real.fourier_eq', Real.fourier_eq']
  have hpt : ∀ x : Rd d, Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) •
      (((ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫)) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (Complex.exp (↑(-2 * π * ⟪x, ξ - a⟫) * Complex.I) * ((ψ (N⁻¹ • x)) : ℂ)) +
      (1 / 2 : ℂ) * (Complex.exp (↑(-2 * π * ⟪x, ξ + a⟫) * Complex.I) * ((ψ (N⁻¹ • x)) : ℂ)) := by
    intro x
    rw [smul_eq_mul]
    have hcos : ((Real.cos (2 * π * ⟪a, x⟫) : ℝ) : ℂ) = (Complex.exp (↑(2 * π * ⟪x, a⟫) * Complex.I)
        + Complex.exp (-(↑(2 * π * ⟪x, a⟫) * Complex.I))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos, real_inner_comm a x]
      ring_nf
    have e1 : Complex.exp (↑(-2 * π * ⟪x, ξ - a⟫) * Complex.I) =
        Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) * Complex.exp (↑(2 * π * ⟪x, a⟫) * Complex.I) := by
      rw [← Complex.exp_add, inner_sub_right]; congr 1; push_cast; ring
    have e2 : Complex.exp (↑(-2 * π * ⟪x, ξ + a⟫) * Complex.I) =
        Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) *
          Complex.exp (-(↑(2 * π * ⟪x, a⟫) * Complex.I)) := by
      rw [← Complex.exp_add, inner_add_right]; congr 1; push_cast; ring
    rw [show (((ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫)) : ℝ) : ℂ) =
      ((ψ (N⁻¹ • x) : ℝ) : ℂ) * ((Real.cos (2 * π * ⟪a, x⟫) : ℝ) : ℂ) from Complex.ofReal_mul _ _,
      hcos, e1, e2]
    ring
  simp_rw [hpt]
  rw [integral_add ((hint _).const_mul _) ((hint _).const_mul _), integral_const_mul,
    integral_const_mul, fourier_dilate ψ hN, fourier_dilate ψ hN]
  simp only [smul_eq_mul]
  ring

/-- **The modulated dilates detect `h` at `a`**: `Re ∫ 𝓕φ_N(ξ) h(ξ) dξ → h(a)` as `N → ∞`, for
`φ_N(x) = ψ(x/N) cos 2π⟨a,x⟩` with `ψ(0) = 1`, `h` bounded, measurable, even, continuous at `a`. -/
theorem tendsto_fourier_test_cos (ψ : Rd d → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hψ0 : ψ 0 = 1) {h : Rd d → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ ξ, |h ξ| ≤ C) (heven : ∀ ξ, h (-ξ) = h ξ) {a : Rd d}
    (hca : ContinuousAt h a) (hca' : ContinuousAt h (-a))
    (hφ : ∀ N : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x => ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫))
    (hcφ : ∀ N : ℝ, 0 < N → HasCompactSupport fun x => ψ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫)) :
    Tendsto (fun n : ℕ => (∫ ξ, (𝓕 (testSchwartz _ (hφ ((n : ℝ) + 1))
      (hcφ ((n : ℝ) + 1) (by positivity)))) ξ * (h ξ : ℂ)).re) atTop (𝓝 (h a)) := by
  set Ψ : Rd d → ℂ := fun η => (𝓕 (testSchwartz ψ hψ hc)) η with hΨ
  have hΨi : Integrable Ψ := (𝓕 (testSchwartz ψ hψ hc)).integrable
  have hΨc : Continuous Ψ := (𝓕 (testSchwartz ψ hψ hc)).continuous
  have hΨ1 : ∫ η, Ψ η = 1 := by
    rw [hΨ, testSchwartz_integral, hψ0, Complex.ofReal_one]
  have hhb : ∀ ξ, ‖(h ξ : ℂ)‖ ≤ C := fun ξ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC ξ
  -- the substitution `ξ = ±a + η/N`
  have hsub : ∀ (N : ℝ), 0 < N → ∀ b : Rd d,
      ((N ^ d : ℝ) : ℂ) * ∫ ξ, Ψ (N • (ξ - b)) * (h ξ : ℂ) =
        ∫ η, Ψ η * (h (b + N⁻¹ • η) : ℂ) := by
    intro N hN b
    have htr : ∫ ξ, Ψ (N • (ξ - b)) * (h ξ : ℂ) = ∫ ξ, Ψ (N • ξ) * (h (ξ + b) : ℂ) := by
      rw [← integral_add_right_eq_self (fun ξ => Ψ (N • (ξ - b)) * (h ξ : ℂ)) b]
      simp only [add_sub_cancel_right]
    have hsc := Measure.integral_comp_smul (μ := (volume : Measure (Rd d)))
      (fun ξ => Ψ (N • ξ) * (h (ξ + b) : ℂ)) N⁻¹
    rw [finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hN d)] at hsc
    rw [htr]
    simp only [smul_smul, mul_inv_cancel₀ hN.ne', one_smul] at hsc
    have hcomm : ∫ η, Ψ η * (h (b + N⁻¹ • η) : ℂ) = ∫ η, Ψ η * (h (N⁻¹ • η + b) : ℂ) := by
      congr 1; funext η; rw [add_comm]
    rw [hcomm, hsc, Complex.real_smul]
  have hlim : ∀ b : Rd d, ContinuousAt h b →
      Tendsto (fun n : ℕ => ∫ η, Ψ η * (h (b + ((n : ℝ) + 1)⁻¹ • η) : ℂ)) atTop
        (𝓝 (∫ η, Ψ η * (h b : ℂ))) := by
    intro b hcb
    refine tendsto_integral_of_dominated_convergence (fun η => C * ‖Ψ η‖) ?_
      (hΨi.norm.const_mul C) ?_ ?_
    · intro n
      exact (hΨc.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp
        (hm.comp (measurable_const.add (measurable_const_smul _)))).aestronglyMeasurable)
    · intro n
      refine Eventually.of_forall fun η => ?_
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hhb _) (norm_nonneg _)
    · refine Eventually.of_forall fun η => ?_
      have h1 : Tendsto (fun n : ℕ => b + ((n : ℝ) + 1)⁻¹ • η) atTop (𝓝 b) := by
        have : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by simp
        simpa using (tendsto_const_nhds (x := b)).add (this.smul_const η)
      exact ((Complex.continuous_ofReal.tendsto _).comp (hcb.tendsto.comp h1)).const_mul (Ψ η)
  have hval : ∀ n : ℕ, ∫ ξ, (𝓕 (testSchwartz _ (hφ ((n : ℝ) + 1))
      (hcφ ((n : ℝ) + 1) (by positivity)))) ξ * (h ξ : ℂ) =
      (1 / 2 : ℂ) * (∫ η, Ψ η * (h (a + ((n : ℝ) + 1)⁻¹ • η) : ℂ)) +
      (1 / 2 : ℂ) * (∫ η, Ψ η * (h (-a + ((n : ℝ) + 1)⁻¹ • η) : ℂ)) := by
    intro n
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hintS : ∀ b : Rd d, Integrable fun ξ => Ψ (((n : ℝ) + 1) • (ξ - b)) * (h ξ : ℂ) := by
      intro b
      have hcomp : Integrable fun ξ => Ψ (((n : ℝ) + 1) • (ξ - b)) := by
        have h1 := (hΨi.comp_smul (μ := (volume : Measure (Rd d))) hN.ne')
        exact h1.comp_sub_right b
      exact hcomp.mul_bdd (c := C) (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
        (Eventually.of_forall hhb)
    have hpt : ∀ ξ : Rd d, (𝓕 (testSchwartz _ (hφ ((n : ℝ) + 1))
        (hcφ ((n : ℝ) + 1) (by positivity)))) ξ * (h ξ : ℂ) =
        (1 / 2 : ℂ) * (((((n : ℝ) + 1) ^ d : ℝ) : ℂ) * (Ψ (((n : ℝ) + 1) • (ξ - a)) * (h ξ : ℂ))) +
        (1 / 2 : ℂ) * (((((n : ℝ) + 1) ^ d : ℝ) : ℂ) *
          (Ψ (((n : ℝ) + 1) • (ξ - -a)) * (h ξ : ℂ))) := by
      intro ξ
      rw [fourier_test_cos ψ hψ hc hN a (hφ _) (hcφ _ hN), sub_neg_eq_add]
      ring
    simp_rw [hpt]
    rw [integral_add (((hintS a).const_mul _).const_mul _) (((hintS (-a)).const_mul _).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      hsub _ hN a, hsub _ hN (-a)]
  have hconv := ((hlim a hca).const_mul (1 / 2 : ℂ)).add ((hlim (-a) hca').const_mul (1 / 2 : ℂ))
  have htarget : (1 / 2 : ℂ) * (∫ η, Ψ η * (h a : ℂ)) + (1 / 2 : ℂ) * (∫ η, Ψ η * (h (-a) : ℂ)) =
      (h a : ℂ) := by
    rw [integral_mul_const, integral_mul_const, hΨ1, heven]
    ring
  rw [htarget] at hconv
  have := (Complex.continuous_re.tendsto _).comp hconv
  refine (this.congr fun n => ?_)
  simp only [Function.comp_apply, Complex.ofReal_re] at *
  rw [hval n]

/-! ## `prop:log-orbit-rays` -/

/-- A symmetric matrix is determined by its quadratic form. -/
theorem eq_of_quad_eq {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x : Rd d, quad A x = quad B x) : A = B := by
  set N := A - B with hN
  have hNs : Nᵀ = N := by
    have hA' : Aᵀ = A := by
      have := hA; unfold Matrix.IsHermitian at this
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    have hB' : Bᵀ = B := by
      have := hB; unfold Matrix.IsHermitian at this
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    rw [hN, transpose_sub, hA', hB']
  have hq : ∀ x, quad N x = 0 := fun x => by rw [hN, quad_sub, h, sub_self]
  have hsym : ∀ x y : Rd d, ⟪x, lin N y⟫ = ⟪y, lin N x⟫ := fun x y => by
    rw [real_inner_comm, inner_lin_left, hNs]
  have hpol : ∀ x y : Rd d, ⟪x, lin N y⟫ = 0 := by
    intro x y
    have h1 := hq (x + y)
    unfold quad at h1
    rw [map_add, inner_add_left, inner_add_right, inner_add_right] at h1
    have hx := hq x
    have hy := hq y
    unfold quad at hx hy
    rw [hsym y x] at h1
    linarith
  have hzero : lin N = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    have := hpol (lin N y) y
    rw [real_inner_self_eq_norm_sq] at this
    have : ‖lin N y‖ = 0 := by nlinarith [norm_nonneg (lin N y)]
    simpa using this
  have : N = 0 := lin_injective (by rw [hzero]; simp [lin])
  exact sub_eq_zero.1 this

/-- **`prop:log-orbit-rays`**: for `g` with the hypothesis of `prop:affine-orbits` and
`g(cu) - g(u) → κ log c` as `u → ∞`, `κ > 0`, a positive finite increment `μ_{Σ'} = μ_Σ * ρ`
forces `Σ' = cΣ`, `c > 0`. -/
theorem log_orbit_rays (hd : 1 ≤ d) (g : ℝ → ℝ) (_hg_cont : ContinuousOn g (Ici 0))
    (_hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (_hg0 : g 0 = 0) (μI : Measure (Rd d))
    [IsProbabilityMeasure μI] (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    (κ : ℝ) (hκ : 0 < κ)
    (hlog : ∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop (𝓝 (κ * Real.log c))) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
      affineOrbit μI S' = affineOrbit μI S ∗ ρ → ∃ c : ℝ, 0 < c ∧ S' = c • S := by
  intro S S' hS hS' ρ hρfin hconv
  haveI : NeZero d := ⟨by omega⟩
  have hρ := charFun_orbit_increment hμI hS hS' hconv
  -- `ρ` is a probability measure
  haveI hprob : IsProbabilityMeasure ρ := by
    have h0 := hρ 0
    rw [charFun_zero, quad_eq_dotProduct, quad_eq_dotProduct] at h0
    simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, sub_self, neg_zero,
      Real.exp_zero, Complex.ofReal_one] at h0
    have h1 : ρ.real univ = 1 := by exact_mod_cast h0
    rw [Measure.real, ENNReal.toReal_eq_one_iff] at h1
    exact ⟨h1⟩
  -- the blow-up function `h`
  set h : Rd d → ℝ := fun ξ => (quad S ξ / quad S' ξ) ^ κ with hh
  have hqc : ∀ T : Mat d, Continuous fun ξ : Rd d => quad T ξ := fun T => by
    unfold quad; fun_prop
  have hm : Measurable h :=
    (((hqc S).measurable.div (hqc S').measurable).pow_const κ)
  obtain ⟨C, hC0, hCb⟩ := exists_bound_ratio_rpow hS hS' hκ
  have hhb : ∀ ξ, |h ξ| ≤ C := fun ξ => by
    rw [abs_of_nonneg (Real.rpow_nonneg (div_nonneg (quad_nonneg hS.posSemidef ξ)
      (quad_nonneg hS'.posSemidef ξ)) κ)]
    exact hCb ξ
  have heven : ∀ ξ, h (-ξ) = h ξ := fun ξ => by
    simp only [hh, show -ξ = (-1 : ℝ) • ξ by simp, quad_smul_vec]
    norm_num
  have hcont : ∀ a : Rd d, a ≠ 0 → ContinuousAt h a := fun a ha =>
    (((hqc S).continuousAt.div (hqc S').continuousAt (quad_pos hS' ha).ne').rpow_const
      (Or.inl (div_pos (quad_pos hS ha) (quad_pos hS' ha)).ne'))
  have hblow : ∀ ξ : Rd d, ξ ≠ 0 →
      Tendsto (fun R : ℝ => charFun ρ ((2 * π * R⁻¹) • ξ)) (𝓝[>] 0) (𝓝 (h ξ : ℂ)) :=
    fun ξ hξ => tendsto_charFun_blowup hlog hS hS' hρ hξ
  have hex : HasBlowLim ρ := fun φ hφ =>
    ⟨_, tendsto_blow_fourier hblow φ hφ.1 hφ.2⟩
  obtain ⟨c₀, -, hc₀⟩ := blowLim_eq_mul_eval_zero hex
  -- `h(a) = c₀` off the origin
  let χ : ContDiffBump (0 : Rd d) := ⟨1, 2, one_pos, by norm_num⟩
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
  have hconst : ∀ a : Rd d, a ≠ 0 → h a = c₀ := by
    intro a ha
    have hφ : ∀ N : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        fun x => χ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫) := fun N =>
      (χ.contDiff.comp (contDiff_const_smul _)).mul
        (Real.contDiff_cos.comp (contDiff_const.mul ((innerSL ℝ a).contDiff)))
    have hcφ : ∀ N : ℝ, 0 < N →
        HasCompactSupport fun x => χ (N⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫) := fun N hN =>
      (χ.hasCompactSupport.comp_smul (inv_ne_zero hN.ne')).mul_right
    have hlimF := tendsto_fourier_test_cos χ χ.contDiff χ.hasCompactSupport hχ0 hm hhb heven
      (hcont a ha) (hcont (-a) (neg_ne_zero.2 ha)) hφ hcφ
    have hval : ∀ n : ℕ, (∫ ξ, (𝓕 (testSchwartz _ (hφ ((n : ℝ) + 1))
        (hcφ ((n : ℝ) + 1) (by positivity)))) ξ * (h ξ : ℂ)).re = c₀ := by
      intro n
      have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have htest : IsRealTestFn fun x => χ (((n : ℝ) + 1)⁻¹ • x) * Real.cos (2 * π * ⟪a, x⟫) :=
        ⟨hφ _, hcφ _ hN⟩
      have h1 := tendsto_nhds_unique (blowLim_tendsto hex htest)
        (tendsto_blow_fourier hblow _ (hφ _) (hcφ _ hN))
      rw [← h1, hc₀ _ htest]
      simp [hχ0]
    have := tendsto_nhds_unique hlimF (by simp_rw [hval]; exact tendsto_const_nhds)
    exact this
  -- the step is a ray
  have he : ebasis (0 : Fin d) ≠ 0 := by
    intro h0
    have := congrArg (fun y : Rd d => y 0) h0
    simp [ebasis] at this
  have hc0pos : 0 < c₀ := by
    rw [← hconst _ he]
    exact Real.rpow_pos_of_pos (div_pos (quad_pos hS he) (quad_pos hS' he)) κ
  set k := c₀ ^ κ⁻¹ with hk
  have hkpos : 0 < k := Real.rpow_pos_of_pos hc0pos _
  have hratio : ∀ a : Rd d, quad S' a = k⁻¹ * quad S a := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp [quad_eq_dotProduct]
    · have h1 := hconst a ha
      have hpos := div_pos (quad_pos hS ha) (quad_pos hS' ha)
      have h2 : quad S a / quad S' a = k := by
        rw [hk, ← h1]
        simp only [hh]
        rw [← Real.rpow_mul hpos.le, mul_inv_cancel₀ hκ.ne', Real.rpow_one]
      have hq' := quad_pos hS' ha
      field_simp
      rw [div_eq_iff hq'.ne'] at h2
      linarith
  refine ⟨k⁻¹, inv_pos.2 hkpos, eq_of_quad_eq hS'.isHermitian
    (hS.smul (inv_pos.2 hkpos)).isHermitian fun x => ?_⟩
  rw [quad_smul, hratio]

/-- **`prop:log-orbit-rays`**, in particular: for every `γ > 0`, no step of the Matérn orbit of
index `γ` off the rays has a positive increment. -/
theorem matern_log_orbit_rays (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (μI : Measure (Rd d))
    (hμI : IsMaternLaw γ μI) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
      affineOrbit μI S' = affineOrbit μI S ∗ ρ → ∃ c : ℝ, 0 < c ∧ S' = c • S := by
  haveI := hμI.1
  set g : ℝ → ℝ := fun u => γ * Real.log (1 + u) with hg
  refine log_orbit_rays hd g (fun u hu => ?_) (fun u hu => ?_) (by simp [hg]) μI
    (fun ω => ?_) γ hγ (fun c hc => ?_)
  · have h1 : (1 : ℝ) + u ≠ 0 := by have : (0 : ℝ) ≤ u := hu; linarith
    exact (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).log h1)).continuousWithinAt
  · exact mul_nonneg hγ.le (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ u from hu]))
  · rw [hμI.2]
    have hpos : (0 : ℝ) < 1 + ‖ω‖ ^ 2 := by positivity
    congr 1
    rw [Real.rpow_def_of_pos hpos, hg]
    congr 1
    ring
  · -- `γ log((1 + cu)/(1 + u)) → γ log c`
    have hq : Tendsto (fun u : ℝ => (1 + c * u) / (1 + u)) atTop (𝓝 c) := by
      have h1 : Tendsto (fun u : ℝ => (u⁻¹ + c) / (u⁻¹ + 1)) atTop (𝓝 ((0 + c) / (0 + 1))) :=
        ((tendsto_inv_atTop_zero.add tendsto_const_nhds).div
          (tendsto_inv_atTop_zero.add tendsto_const_nhds) (by norm_num))
      rw [zero_add, zero_add, div_one] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with u hu
      field_simp
    have hlogc := ((Real.continuousAt_log hc.ne').tendsto.comp hq).const_mul γ
    refine hlogc.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    simp only [hg, Function.comp_apply]
    rw [Real.log_div (by positivity) (by positivity)]
    ring

end AffineHemigroup
