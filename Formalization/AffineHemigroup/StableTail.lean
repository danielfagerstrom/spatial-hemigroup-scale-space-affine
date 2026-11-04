/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.StableExponent
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# `lem:stable-tail`: the tail of an increment is the difference of the Lévy densities

Blueprint: `blueprint/src/parts/05-orbits.tex`, `lem:stable-tail` (wave 1, group D, Q-0281). For a
positive finite measure `ρ` with `ρ̂(ω) = exp[-⟨ω,Cω⟩ - ψ_{H'}(ω) + ψ_H(ω)]`: `ρ` is a probability
measure, `R^α ∫ φ(x/R) ρ(dx) → ∫ φ (n_{H'} - n_H)` for smooth compactly supported `φ` vanishing near
`0`, and `n_H ≤ n_{H'}` off the origin.

The route is the blueprint's. Mathlib's Fourier transform `𝓕` has the kernel `e^{-2πi⟨x,ξ⟩}`, so
the inversion formula reads `φ(x) = ∫ Φ(ξ) e^{2πi⟨ξ,x⟩} dξ` with `Φ = 𝓕φ`, a Schwartz function
(`HasCompactSupport.toSchwartzMap`), and the transform of `ρ` enters at `2πξ/R`. Lean core only.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Real Filter Complex
open scoped MatrixOrder RealInnerProductSpace ENNReal Topology FourierTransform

variable {d : ℕ}

/-! ### The exponent of `ρ` -/

/-- `ψ_H(cω) = c^α ψ_H(ω)` for `c ≥ 0` and `H ∈ PSD(d)`. -/
theorem stableExp_smul {α : ℝ} {H : Mat d} (hH : H.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (ω : Rd d) : stableExp α H (c • ω) = c ^ α * stableExp α H ω := by
  unfold stableExp
  rw [quad_smul_vec, mul_rpow (sq_nonneg c) (quad_nonneg hH ω), ← rpow_natCast,
    ← rpow_mul hc]
  congr 2
  push_cast
  ring

/-- `ψ_H(0) = 0` for `α > 0`. -/
theorem stableExp_zero {α : ℝ} (hα : 0 < α) (H : Mat d) : stableExp α H 0 = 0 := by
  unfold stableExp
  rw [quad_eq_dotProduct]
  simp [zero_rpow (by positivity : α / 2 ≠ 0)]

/-- `ψ_H(ω) ≤ ‖H‖^{α/2}|ω|^α`, through `⟨ω,Hω⟩ ≤ ‖H‖|ω|²`. -/
theorem stableExp_le {α : ℝ} (hα : 0 < α) {H : Mat d} (hH : H.PosSemidef) (ω : Rd d) :
    stableExp α H ω ≤ ‖lin H‖ ^ (α / 2) * ‖ω‖ ^ α := by
  unfold stableExp
  have hq : quad H ω ≤ ‖lin H‖ * ‖ω‖ ^ 2 := by
    unfold quad
    calc ⟪ω, lin H ω⟫ ≤ ‖ω‖ * ‖lin H ω‖ := real_inner_le_norm _ _
      _ ≤ ‖ω‖ * (‖lin H‖ * ‖ω‖) := mul_le_mul_of_nonneg_left ((lin H).le_opNorm ω) (norm_nonneg _)
      _ = ‖lin H‖ * ‖ω‖ ^ 2 := by ring
  calc quad H ω ^ (α / 2) ≤ (‖lin H‖ * ‖ω‖ ^ 2) ^ (α / 2) :=
        rpow_le_rpow (quad_nonneg hH ω) hq (by positivity)
    _ = ‖lin H‖ ^ (α / 2) * ‖ω‖ ^ α := by
        rw [mul_rpow (norm_nonneg _) (by positivity), ← rpow_natCast, ← rpow_mul (norm_nonneg _)]
        congr 2
        push_cast
        ring

/-- `|⟨ω,Gω⟩| ≤ ‖G‖|ω|²`. -/
theorem abs_quad_le (G : Mat d) (ω : Rd d) : |quad G ω| ≤ ‖lin G‖ * ‖ω‖ ^ 2 := by
  unfold quad
  calc |⟪ω, lin G ω⟫| ≤ ‖ω‖ * ‖lin G ω‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ω‖ * (‖lin G‖ * ‖ω‖) := mul_le_mul_of_nonneg_left ((lin G).le_opNorm ω) (norm_nonneg _)
    _ = ‖lin G‖ * ‖ω‖ ^ 2 := by ring

/-! ### The test function and its Fourier transform -/

/-- A real test function, as a complex Schwartz function. -/
noncomputable def testSchwartz (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : SchwartzMap (Rd d) ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun x => (φ x : ℂ))
    (hc.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp hφ)

/-- **Fourier inversion** for a real test function: `φ(x) = ∫ Φ(ξ) e^{2πi⟨ξ,x⟩} dξ`. -/
theorem testSchwartz_inversion (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (x : Rd d) :
    ∫ ξ, cexp (↑(2 * π * ⟪ξ, x⟫) * I) * (𝓕 (testSchwartz φ hφ hc)) ξ = (φ x : ℂ) := by
  set S := testSchwartz φ hφ hc
  have h := S.continuous.fourierInv_fourier_eq S.integrable (𝓕 S).integrable
  have hx := congrFun h x
  rw [fourierInv_eq'] at hx
  simp only [smul_eq_mul] at hx
  rw [SchwartzMap.fourier_coe]
  exact hx

/-- `∫ Φ = φ(0)`. -/
theorem testSchwartz_integral (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∫ ξ, (𝓕 (testSchwartz φ hφ hc)) ξ = (φ 0 : ℂ) := by
  have := testSchwartz_inversion φ hφ hc 0
  simpa using this

/-- **The Fourier side** (the blueprint's "Fourier side"): for `R > 0` and a finite measure `ρ`,
`∫ φ(x/R) ρ(dx) = ∫ Φ(ξ) ρ̂(2πξ/R) dξ`. -/
theorem integral_test_eq_fourier (φ : Rd d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (ρ : Measure (Rd d)) [IsFiniteMeasure ρ] {R : ℝ} (_hR : 0 < R) :
    ((∫ x, φ (R⁻¹ • x) ∂ρ : ℝ) : ℂ) =
      ∫ ξ, (𝓕 (testSchwartz φ hφ hc)) ξ * charFun ρ ((2 * π * R⁻¹) • ξ) := by
  set Φ : Rd d → ℂ := fun ξ => (𝓕 (testSchwartz φ hφ hc)) ξ with hΦ
  have hΦi : Integrable Φ := (𝓕 (testSchwartz φ hφ hc)).integrable
  have hΦc : Continuous Φ := (𝓕 (testSchwartz φ hφ hc)).continuous
  set F : Rd d → Rd d → ℂ := fun x ξ => cexp (↑(2 * π * ⟪ξ, R⁻¹ • x⟫) * I) * Φ ξ with hF
  have hint : Integrable (Function.uncurry F) (ρ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF, Function.uncurry_def]
      fun_prop
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, one_mul]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [← integral_complex_ofReal]
  have h1 : ∀ x, ((φ (R⁻¹ • x) : ℝ) : ℂ) = ∫ ξ, F x ξ := fun x =>
    (testSchwartz_inversion φ hφ hc (R⁻¹ • x)).symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1
  funext ξ
  simp only [hF]
  rw [integral_mul_const, mul_comm, charFun_apply]
  congr 2
  funext x
  congr 1
  rw [inner_smul_right, inner_smul_right, real_inner_comm]
  push_cast
  ring

/-! ### The limit on the Fourier side -/

/-- `R^α (R⁻¹)² = R^{α-2}` and `R^α (R⁻¹)^α = 1` for `R > 0`. -/
theorem rpow_mul_inv_sq {α R : ℝ} (hR : 0 < R) : R ^ α * R⁻¹ ^ 2 = R ^ (α - 2) := by
  rw [rpow_sub hR, inv_pow, div_eq_mul_inv, rpow_two]

theorem rpow_mul_inv_rpow {α R : ℝ} (hR : 0 < R) : R ^ α * R⁻¹ ^ α = 1 := by
  rw [inv_rpow hR.le, mul_inv_cancel₀ (rpow_pos_of_pos hR α).ne']

/-- **The scalar limit**: with `a_R = R^{-2}A + R^{-α}B ≥ 0`, `R^α(e^{-a_R} - 1) → -B`. -/
theorem tendsto_rpow_mul_exp_sub_one {α A B : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (ha : ∀ R : ℝ, 0 < R → 0 ≤ R⁻¹ ^ 2 * A + R⁻¹ ^ α * B) :
    Tendsto (fun R : ℝ => R ^ α * (Real.exp (-(R⁻¹ ^ 2 * A + R⁻¹ ^ α * B)) - 1)) atTop
      (𝓝 (-B)) := by
  -- `R^α a_R = R^{α-2}A + B → B`
  have hpow : Tendsto (fun R : ℝ => R ^ (α - 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 2 - α) (by linarith)
    simpa only [neg_sub] using this
  have hRa : Tendsto (fun R : ℝ => R ^ α * (R⁻¹ ^ 2 * A + R⁻¹ ^ α * B)) atTop (𝓝 B) := by
    have h : Tendsto (fun R : ℝ => R ^ (α - 2) * A + B) atTop (𝓝 B) := by
      simpa using (hpow.mul_const A).add_const B
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [mul_add, ← mul_assoc, rpow_mul_inv_sq hR, ← mul_assoc, rpow_mul_inv_rpow hR, one_mul]
  -- `a_R → 0`
  have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ha0 : Tendsto (fun R : ℝ => R⁻¹ ^ 2 * A + R⁻¹ ^ α * B) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R⁻¹ ^ 2 * A) atTop (𝓝 0) := by
      simpa using (hinv.pow 2).mul_const A
    have h2 : Tendsto (fun R : ℝ => R⁻¹ ^ α * B) atTop (𝓝 0) := by
      have := ((continuous_id.rpow_const fun _ => Or.inr hα0.le).tendsto 0).comp hinv
      simpa [zero_rpow hα0.ne'] using this.mul_const B
    simpa using h1.add h2
  -- the remainder `R^α(e^{-a} - 1 + a) → 0`
  have hrem : Tendsto (fun R : ℝ => R ^ α * (Real.exp (-(R⁻¹ ^ 2 * A + R⁻¹ ^ α * B)) - 1 +
      (R⁻¹ ^ 2 * A + R⁻¹ ^ α * B))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun R : ℝ => R ^ α * (R⁻¹ ^ 2 * A + R⁻¹ ^ α * B) *
        (R⁻¹ ^ 2 * A + R⁻¹ ^ α * B)) atTop (𝓝 0) := by
      simpa using hRa.mul ha0
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 ha0).2 1 one_pos] with R hR h1
    set a := R⁻¹ ^ 2 * A + R⁻¹ ^ α * B
    have ha' : 0 ≤ a := ha R hR
    have habs : |(-a)| ≤ 1 := by rw [abs_neg, abs_of_nonneg ha']; exact h1.le
    have h := Real.abs_exp_sub_one_sub_id_le habs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hR α)]
    rw [show Real.exp (-a) - 1 + a = Real.exp (-a) - 1 - -a by ring]
    calc R ^ α * |Real.exp (-a) - 1 - -a| ≤ R ^ α * (-a) ^ 2 :=
          mul_le_mul_of_nonneg_left h (rpow_pos_of_pos hR α).le
      _ = R ^ α * a * a := by ring
  have := hrem.sub hRa
  simp only [zero_sub] at this
  refine this.congr' ?_
  filter_upwards with R
  ring

/-- `|ψ_H(ω)| ≤ ‖H‖^{α/2}(1 + |ω|²)` for `α ≤ 2`. -/
theorem stableExp_le_one_add {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {H : Mat d}
    (hH : H.PosSemidef) (ω : Rd d) :
    stableExp α H ω ≤ ‖lin H‖ ^ (α / 2) * (1 + ‖ω‖ ^ 2) := by
  refine (stableExp_le hα0 hH ω).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases le_or_gt ‖ω‖ 1 with h | h
  · have : ‖ω‖ ^ α ≤ 1 := rpow_le_one (norm_nonneg _) h hα0.le
    nlinarith [sq_nonneg ‖ω‖]
  · have : ‖ω‖ ^ α ≤ ‖ω‖ ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le h.le hα2
    rw [rpow_two] at this
    linarith

theorem continuous_stableExp {α : ℝ} (hα0 : 0 < α) (H : Mat d) :
    Continuous (stableExp α H) := by
  unfold stableExp quad
  exact (by fun_prop : Continuous fun ω : Rd d => ⟪ω, lin H ω⟫).rpow_const
    fun _ => Or.inr (by positivity)

/-- **The limit on the Fourier side**: for an integrable `Φ` with `|ξ|²Φ` integrable, and
`a(ω) = ⟨ω,Gω⟩ + ψ_{H'}(ω) - ψ_H(ω) ≥ 0`,
`R^α ∫ Φ(ξ)(e^{-a(2πξ/R)} - 1) dξ → -∫ Φ(ξ)(ψ_{H'} - ψ_H)(2πξ) dξ`. -/
theorem tendsto_fourier_side {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H H' G : Mat d}
    (hH : H.PosSemidef) (hH' : H'.PosSemidef) (Φ : Rd d → ℂ) (hΦc : Continuous Φ)
    (hΦ : Integrable Φ) (hΦ2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖Φ ξ‖)
    (hE : ∀ ω, 0 ≤ quad G ω + (stableExp α H' ω - stableExp α H ω)) :
    Tendsto (fun R : ℝ => ((R ^ α : ℝ) : ℂ) * ∫ ξ, Φ ξ * (((Real.exp (-(quad G ((2 * π * R⁻¹) • ξ) +
        (stableExp α H' ((2 * π * R⁻¹) • ξ) - stableExp α H ((2 * π * R⁻¹) • ξ)))) : ℝ) : ℂ) - 1))
      atTop (𝓝 (∫ ξ, Φ ξ *
        ((-(stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ)) : ℝ) : ℂ))) := by
  set Q : Rd d → ℝ := fun ξ => quad G ((2 * π) • ξ) with hQ
  set D : Rd d → ℝ := fun ξ => stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ) with hD
  -- homogeneity: `a(2πξ/R) = R^{-2}Q(ξ) + R^{-α}D(ξ)`
  have hhom : ∀ R : ℝ, 0 < R → ∀ ξ : Rd d,
      quad G ((2 * π * R⁻¹) • ξ) + (stableExp α H' ((2 * π * R⁻¹) • ξ) -
        stableExp α H ((2 * π * R⁻¹) • ξ)) = R⁻¹ ^ 2 * Q ξ + R⁻¹ ^ α * D ξ := by
    intro R hR ξ
    have e : (2 * π * R⁻¹) • ξ = R⁻¹ • (2 * π) • ξ := by rw [smul_smul]; ring_nf
    rw [e, quad_smul_vec, stableExp_smul hH' (by positivity), stableExp_smul hH (by positivity)]
    simp only [hQ, hD]
    ring
  -- the bound
  set B : Rd d → ℝ := fun ξ => ‖Φ ξ‖ * (|Q ξ| + |D ξ|) with hB
  have hBint : Integrable B := by
    set K : ℝ := ‖lin G‖ * (2 * π) ^ 2 + (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2
    have hdom : ∀ ξ, ‖B ξ‖ ≤ (K + K) * ‖Φ ξ‖ + K * (‖ξ‖ ^ 2 * ‖Φ ξ‖) := by
      intro ξ
      have hQb : |Q ξ| ≤ ‖lin G‖ * (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
        have := abs_quad_le G ((2 * π) • ξ)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)] at this
        simp only [hQ]; nlinarith
      have hDb : |D ξ| ≤
          (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2 * (1 + ‖ξ‖ ^ 2) := by
        have h1 := stableExp_le_one_add hα0 hα2.le hH' ((2 * π) • ξ)
        have h2 := stableExp_le_one_add hα0 hα2.le hH ((2 * π) • ξ)
        have h1' : 0 ≤ stableExp α H' ((2 * π) • ξ) := rpow_nonneg (quad_nonneg hH' _) _
        have h2' : 0 ≤ stableExp α H ((2 * π) • ξ) := rpow_nonneg (quad_nonneg hH _) _
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow] at h1 h2
        have hπ : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.two_le_pi]
        have hn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
        have hA : 0 ≤ ‖lin H'‖ ^ (α / 2) := by positivity
        have hA' : 0 ≤ ‖lin H‖ ^ (α / 2) := by positivity
        simp only [hD]
        rw [abs_le]
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hπ hA,
          mul_le_mul_of_nonneg_left hπ hA',
          mul_nonneg hA hn, mul_nonneg hA' hn]
      have hK0 : 0 ≤ ‖lin G‖ * (2 * π) ^ 2 := by positivity
      have hc2 : 0 ≤ (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2 := by positivity
      rw [Real.norm_of_nonneg (by simp only [hB]; positivity)]
      simp only [hB]
      have hΦn := norm_nonneg (Φ ξ)
      calc ‖Φ ξ‖ * (|Q ξ| + |D ξ|)
          ≤ ‖Φ ξ‖ * (‖lin G‖ * (2 * π) ^ 2 * ‖ξ‖ ^ 2 +
              (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2 * (1 + ‖ξ‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (add_le_add hQb hDb) hΦn
        _ = (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2 * ‖Φ ξ‖ +
              K * (‖ξ‖ ^ 2 * ‖Φ ξ‖) := by ring
        _ ≤ (K + K) * ‖Φ ξ‖ + K * (‖ξ‖ ^ 2 * ‖Φ ξ‖) := by
            gcongr
            linarith
    refine Integrable.mono' ((hΦ.norm.const_mul (K + K)).add (hΦ2.const_mul K)) ?_
      (Filter.Eventually.of_forall hdom)
    refine Continuous.aestronglyMeasurable ?_
    simp only [hB, hQ, hD]
    have := continuous_stableExp hα0 H
    have := continuous_stableExp hα0 H'
    unfold quad
    fun_prop
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (R : ℝ) ξ => ((R ^ α : ℝ) : ℂ) * (Φ ξ * (((Real.exp (-(quad G ((2 * π * R⁻¹) • ξ) +
        (stableExp α H' ((2 * π * R⁻¹) • ξ) - stableExp α H ((2 * π * R⁻¹) • ξ)))) : ℝ) : ℂ) - 1)))
    (f := fun ξ => Φ ξ * ((-(stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ)) : ℝ) : ℂ))
    B ?_ ?_ hBint ?_
  · refine hlim.congr fun R => ?_
    rw [integral_const_mul]
  · -- measurability
    refine Filter.Eventually.of_forall fun R => Continuous.aestronglyMeasurable ?_
    have := continuous_stableExp hα0 H
    have := continuous_stableExp hα0 H'
    unfold quad
    fun_prop
  · -- the bound, for `R ≥ 1`
    filter_upwards [eventually_ge_atTop 1] with R hR1
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hR : 0 < R := by linarith
    have ha := hE ((2 * π * R⁻¹) • ξ)
    rw [hhom R hR ξ] at ha ⊢
    set a := R⁻¹ ^ 2 * Q ξ + R⁻¹ ^ α * D ξ
    have hexp : |Real.exp (-a) - 1| ≤ a := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 ha)])]
      linarith [Real.add_one_le_exp (-a)]
    have hRα : 0 < R ^ α := rpow_pos_of_pos hR α
    have hRa : R ^ α * a ≤ |Q ξ| + |D ξ| := by
      have e : R ^ α * a = R ^ (α - 2) * Q ξ + D ξ := by
        simp only [a]
        rw [mul_add, ← mul_assoc, rpow_mul_inv_sq hR, ← mul_assoc, rpow_mul_inv_rpow hR, one_mul]
      rw [e]
      have hp : R ^ (α - 2) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
      have hp0 : 0 ≤ R ^ (α - 2) := (rpow_pos_of_pos hR _).le
      have h1 : R ^ (α - 2) * Q ξ ≤ |Q ξ| := by
        calc R ^ (α - 2) * Q ξ ≤ R ^ (α - 2) * |Q ξ| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hp0
          _ ≤ 1 * |Q ξ| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
          _ = |Q ξ| := one_mul _
      linarith [le_abs_self (D ξ)]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hRα.le]
    rw [show (((Real.exp (-a)) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    calc R ^ α * (‖Φ ξ‖ * |Real.exp (-a) - 1|) ≤ R ^ α * (‖Φ ξ‖ * a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hRα.le
      _ = ‖Φ ξ‖ * (R ^ α * a) := by ring
      _ ≤ ‖Φ ξ‖ * (|Q ξ| + |D ξ|) := mul_le_mul_of_nonneg_left hRa (norm_nonneg _)
  · -- the pointwise limit
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hscal := tendsto_rpow_mul_exp_sub_one (A := Q ξ) (B := D ξ) hα0 hα2
      (fun R hR => by rw [← hhom R hR ξ]; exact hE _)
    have hc : Tendsto (fun R : ℝ => ((R ^ α * (Real.exp (-(R⁻¹ ^ 2 * Q ξ + R⁻¹ ^ α * D ξ)) - 1) :
        ℝ) : ℂ)) atTop (𝓝 ((-D ξ : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hscal
    have := hc.const_mul (Φ ξ)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [hhom R hR ξ]
    push_cast
    ring

/-! ### The Lévy side -/

theorem stableDensity_nonneg [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) (x : Rd d) : 0 ≤ stableDensity α H x := by
  have hc := (stableConst_pos_finite (d := d) hα0 hα2).2
  unfold stableDensity
  exact mul_nonneg (mul_nonneg (inv_pos.2 hc).le (rpow_nonneg hH.det_pos.le _))
    (rpow_nonneg (quad_nonneg hH.inv.posSemidef x) _)

theorem measurable_stableDensity [NeZero d] (α : ℝ) (H : Mat d) :
    Measurable (stableDensity α H) := by
  have hq : Continuous fun x : Rd d => quad H⁻¹ x := by unfold quad; fun_prop
  unfold stableDensity
  exact measurable_const.mul (hq.measurable.pow_const _)

theorem stableDensity_neg [NeZero d] (α : ℝ) (H : Mat d) (x : Rd d) :
    stableDensity α H (-x) = stableDensity α H x := by
  unfold stableDensity
  rw [show quad H⁻¹ (-x) = quad H⁻¹ x by
    rw [show -x = (-1 : ℝ) • x by simp, quad_smul_vec]; ring]

/-- **Clause (1) of `lem:elliptical-stable-density` as a Bochner integral**: the integrand
`(1 - cos⟨ω,x⟩)n_H(x)` is integrable and integrates to `ψ_H(ω)`. -/
theorem stableExp_eq_integral [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H : Mat d}
    (hH : H.PosDef) (ω : Rd d) :
    Integrable (fun x => (1 - Real.cos ⟪ω, x⟫) * stableDensity α H x) ∧
      ∫ x, (1 - Real.cos ⟪ω, x⟫) * stableDensity α H x = stableExp α H ω := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  have h1 := (stableExp_eq_lintegral hα0 hα2 hH).1 ω
  rw [restrict_compl_singleton] at h1
  have hnn : ∀ x, 0 ≤ (1 - Real.cos ⟪ω, x⟫) * stableDensity α H x := fun x =>
    mul_nonneg (by linarith [Real.cos_le_one ⟪ω, x⟫]) (stableDensity_nonneg hα0 hα2 hH x)
  have hmeas : AEStronglyMeasurable (fun x => (1 - Real.cos ⟪ω, x⟫) * stableDensity α H x)
      volume :=
    ((by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).measurable.mul
      (measurable_stableDensity α H)).aestronglyMeasurable
  have hint : Integrable (fun x => (1 - Real.cos ⟪ω, x⟫) * stableDensity α H x) := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hmeas (Filter.Eventually.of_forall hnn), ← h1]
    exact ENNReal.ofReal_ne_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hmeas, ← h1]
  exact ENNReal.toReal_ofReal
    (by unfold stableExp; exact rpow_nonneg (quad_nonneg hH.posSemidef ω) _)

/-- A continuous function with compact support away from `0`, times `n_H`, is integrable. -/
theorem integrable_mul_stableDensity [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {H : Mat d} (hH : H.PosDef) {g : Rd d → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg0 : (0 : Rd d) ∉ tsupport g) :
    Integrable (fun x => g x * stableDensity α H x) := by
  haveI : Nontrivial (Rd d) := ⟨⟨EuclideanSpace.single 0 1, 0, fun h => by
    have := congrArg (fun y : Rd d => y 0) h
    simp at this⟩⟩
  -- a positive lower bound `δ` of `|x|` on the support
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ x ∈ tsupport g, δ ≤ ‖x‖ := by
    rcases (tsupport g).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hgc.isCompact.exists_isMinOn h continuous_norm.continuousOn
    refine ⟨‖x₀‖, norm_pos_iff.2 fun h0 => hg0 (h0 ▸ hx₀), fun x hx => hmin hx⟩
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  -- the moment `min(|x|², 1) n_H` is integrable
  have hmom := (stableExp_eq_lintegral hα0 hα2 hH).2
  rw [restrict_compl_singleton] at hmom
  have hmeasm : AEStronglyMeasurable (fun x => min (‖x‖ ^ 2) 1 * stableDensity α H x) volume :=
    ((by fun_prop : Continuous fun x : Rd d => min (‖x‖ ^ 2) 1).measurable.mul
      (measurable_stableDensity α H)).aestronglyMeasurable
  have hmint : Integrable (fun x => min (‖x‖ ^ 2) 1 * stableDensity α H x) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeasm (Filter.Eventually.of_forall fun x =>
      mul_nonneg (le_min (sq_nonneg _) zero_le_one) (stableDensity_nonneg hα0 hα2 hH x))).1 hmom
  set m := min (δ ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  refine Integrable.mono' (hmint.const_mul (C / m)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hg.measurable.mul (measurable_stableDensity α H)).aestronglyMeasurable
  · have hn := stableDensity_nonneg hα0 hα2 hH x
    by_cases hx : x ∈ tsupport g
    · have hδx := hδK x hx
      have hmx : m ≤ min (‖x‖ ^ 2) 1 := min_le_min_right _ (pow_le_pow_left₀ hδ.le hδx 2)
      rw [norm_mul, Real.norm_of_nonneg hn]
      have hCx : ‖g x‖ ≤ C := hC x
      have hC0 : 0 ≤ C := (norm_nonneg _).trans hCx
      calc ‖g x‖ * stableDensity α H x ≤ C * stableDensity α H x :=
            mul_le_mul_of_nonneg_right hCx hn
        _ = C / m * (m * stableDensity α H x) := by field_simp
        _ ≤ C / m * (min (‖x‖ ^ 2) 1 * stableDensity α H x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmx hn) (by positivity)
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
      exact mul_nonneg (div_nonneg ((norm_nonneg _).trans (hC x)) hm0.le)
        (mul_nonneg (le_min (sq_nonneg _) zero_le_one) hn)

/-- `|Φ| (ψ_{H'} + ψ_H)(2π·)` is integrable when `Φ` and `|ξ|²Φ` are. -/
theorem integrable_norm_mul_stableExp {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H H' : Mat d}
    (hH : H.PosSemidef) (hH' : H'.PosSemidef) (Φ : Rd d → ℂ) (hΦc : Continuous Φ)
    (hΦ : Integrable Φ) (hΦ2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖Φ ξ‖) :
    Integrable fun ξ => ‖Φ ξ‖ * (stableExp α H' ((2 * π) • ξ) + stableExp α H ((2 * π) • ξ)) := by
  set K : ℝ := (‖lin H'‖ ^ (α / 2) + ‖lin H‖ ^ (α / 2)) * (2 * π) ^ 2
  have hK : 0 ≤ K := by positivity
  refine Integrable.mono' ((hΦ.norm.const_mul K).add (hΦ2.const_mul K)) ?_
    (Filter.Eventually.of_forall fun ξ => ?_)
  · have := continuous_stableExp hα0 H
    have := continuous_stableExp hα0 H'
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h1 := stableExp_le_one_add hα0 hα2.le hH' ((2 * π) • ξ)
    have h2 := stableExp_le_one_add hα0 hα2.le hH ((2 * π) • ξ)
    have h1' : 0 ≤ stableExp α H' ((2 * π) • ξ) := rpow_nonneg (quad_nonneg hH' _) _
    have h2' : 0 ≤ stableExp α H ((2 * π) • ξ) := rpow_nonneg (quad_nonneg hH _) _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow] at h1 h2
    have hπ : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.two_le_pi]
    have hA : 0 ≤ ‖lin H'‖ ^ (α / 2) := by positivity
    have hA' : 0 ≤ ‖lin H‖ ^ (α / 2) := by positivity
    have hsum : stableExp α H' ((2 * π) • ξ) + stableExp α H ((2 * π) • ξ) ≤ K * (1 + ‖ξ‖ ^ 2) := by
      have hn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hπ hA, mul_le_mul_of_nonneg_left hπ hA',
        mul_nonneg hA hn, mul_nonneg hA' hn, mul_nonneg (mul_nonneg hA hn) (sub_nonneg.2 hπ),
        mul_nonneg (mul_nonneg hA' hn) (sub_nonneg.2 hπ)]
    rw [Real.norm_of_nonneg (by positivity)]
    have hΦn := norm_nonneg (Φ ξ)
    calc ‖Φ ξ‖ * (stableExp α H' ((2 * π) • ξ) + stableExp α H ((2 * π) • ξ))
        ≤ ‖Φ ξ‖ * (K * (1 + ‖ξ‖ ^ 2)) := mul_le_mul_of_nonneg_left hsum hΦn
      _ = K * ‖Φ ξ‖ + K * (‖ξ‖ ^ 2 * ‖Φ ξ‖) := by ring

/-- **Back to `x`**: `-∫ Φ(ξ)(ψ_{H'} - ψ_H)(2πξ) dξ = ∫ φ (n_{H'} - n_H)`. -/
theorem fourier_limit_eq [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H H' : Mat d}
    (hH : H.PosDef) (hH' : H'.PosDef) (φ : Rd d → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφ0 : (0 : Rd d) ∉ tsupport φ) :
    ∫ ξ, (𝓕 (testSchwartz φ hφ hc)) ξ *
        ((-(stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ)) : ℝ) : ℂ) =
      ((∫ x, φ x * (stableDensity α H' x - stableDensity α H x) : ℝ) : ℂ) := by
  set S := testSchwartz φ hφ hc
  set Φ : Rd d → ℂ := fun ξ => (𝓕 S) ξ with hΦdef
  have hΦi : Integrable Φ := (𝓕 S).integrable
  have hΦc : Continuous Φ := (𝓕 S).continuous
  have hΦ2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖Φ ξ‖ := (𝓕 S).integrable_pow_mul volume 2
  set f : Rd d → ℝ := fun x => stableDensity α H' x - stableDensity α H x with hf
  set k : Rd d → Rd d → ℝ := fun ξ x => 1 - Real.cos ⟪(2 * π) • ξ, x⟫ with hk
  have hφ0' : φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ0
  have hmeasn := measurable_stableDensity α H
  have hmeasn' := measurable_stableDensity α H'
  -- (a) the exponent as an integral
  have hD : ∀ ξ, stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ) =
      ∫ x, k ξ x * f x := by
    intro ξ
    obtain ⟨i1, e1⟩ := stableExp_eq_integral hα0 hα2 hH' ((2 * π) • ξ)
    obtain ⟨i2, e2⟩ := stableExp_eq_integral hα0 hα2 hH ((2 * π) • ξ)
    rw [← e1, ← e2, ← integral_sub i1 i2]
    congr 1; funext x; simp only [hk, hf]; ring
  -- (b) the double integral, and its integrability
  set F : Rd d → Rd d → ℂ := fun ξ x => Φ ξ * ((k ξ x * f x : ℝ) : ℂ) with hF
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    set Kf : Rd d × Rd d → ℝ := fun p => ‖Φ p.1‖ * (k p.1 p.2 * stableDensity α H' p.2 +
      k p.1 p.2 * stableDensity α H p.2) with hKf
    have hkm : Measurable fun p : Rd d × Rd d => k p.1 p.2 := by
      simp only [hk]; fun_prop
    have hKmeas : AEStronglyMeasurable Kf (volume.prod volume) := by
      refine Measurable.aestronglyMeasurable ?_
      simp only [hKf]
      exact (hΦc.measurable.comp measurable_fst).norm.mul
        ((hkm.mul (hmeasn'.comp measurable_snd)).add
        (hkm.mul (hmeasn.comp measurable_snd)))
    have hKint : Integrable Kf (volume.prod volume) := by
      rw [integrable_prod_iff hKmeas]
      constructor
      · refine Filter.Eventually.of_forall fun ξ => ?_
        exact (((stableExp_eq_integral hα0 hα2 hH' ((2 * π) • ξ)).1.add
          (stableExp_eq_integral hα0 hα2 hH ((2 * π) • ξ)).1).const_mul ‖Φ ξ‖)
      · refine (integrable_norm_mul_stableExp hα0 hα2 hH.posSemidef hH'.posSemidef Φ hΦc hΦi
          hΦ2).congr (Filter.Eventually.of_forall fun ξ => ?_)
        have hnn : ∀ x, 0 ≤ Kf (ξ, x) := fun x => by
          simp only [hKf, hk]
          have := Real.cos_le_one ⟪(2 * π) • ξ, x⟫
          exact mul_nonneg (norm_nonneg _) (add_nonneg
            (mul_nonneg (by linarith) (stableDensity_nonneg hα0 hα2 hH' x))
            (mul_nonneg (by linarith) (stableDensity_nonneg hα0 hα2 hH x)))
        simp only [Real.norm_of_nonneg (hnn _)]
        simp only [hKf]
        rw [integral_const_mul, integral_add (stableExp_eq_integral hα0 hα2 hH' ((2 * π) • ξ)).1
          (stableExp_eq_integral hα0 hα2 hH ((2 * π) • ξ)).1,
          (stableExp_eq_integral hα0 hα2 hH' ((2 * π) • ξ)).2,
          (stableExp_eq_integral hα0 hα2 hH ((2 * π) • ξ)).2]
    refine hKint.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, Function.uncurry_def]
      exact (hΦc.measurable.comp measurable_fst).mul (Complex.measurable_ofReal.comp
        (hkm.mul ((hmeasn'.comp measurable_snd).sub (hmeasn.comp measurable_snd))))
    · simp only [hF, hKf, Function.uncurry_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hk0 : 0 ≤ k p.1 p.2 := by
        simp only [hk]; linarith [Real.cos_le_one ⟪(2 * π) • p.1, p.2⟫]
      have hn := stableDensity_nonneg hα0 hα2 hH p.2
      have hn' := stableDensity_nonneg hα0 hα2 hH' p.2
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [abs_of_nonneg hk0, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hk0
      simp only [hf]
      rw [abs_le]; constructor <;> linarith
  -- (c) the inner integral, through Fourier inversion at `x` and `-x`
  have hinner : ∀ x, ∫ ξ, F ξ x = -((f x * ((φ x + φ (-x)) / 2) : ℝ) : ℂ) := by
    intro x
    have hcos : ∀ ξ, ((Real.cos ⟪(2 * π) • ξ, x⟫ : ℝ) : ℂ) =
        (cexp (↑(2 * π * ⟪ξ, x⟫) * I) + cexp (↑(2 * π * ⟪ξ, -x⟫) * I)) / 2 := by
      intro ξ
      rw [real_inner_smul_left, inner_neg_right, Complex.ofReal_cos, eq_div_iff two_ne_zero,
        mul_comm, Complex.two_cos]
      push_cast
      ring_nf
    have h1 : Integrable fun ξ => Φ ξ * cexp (↑(2 * π * ⟪ξ, x⟫) * I) :=
      hΦi.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun ξ => by
        rw [Complex.norm_exp_ofReal_mul_I])
    have h2 : Integrable fun ξ => Φ ξ * cexp (↑(2 * π * ⟪ξ, -x⟫) * I) :=
      hΦi.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun ξ => by
        rw [Complex.norm_exp_ofReal_mul_I])
    have i1 := testSchwartz_inversion φ hφ hc x
    have i2 := testSchwartz_inversion φ hφ hc (-x)
    have i0 := testSchwartz_integral φ hφ hc
    rw [hφ0'] at i0
    simp only [mul_comm (cexp _)] at i1 i2
    have e : ∀ ξ, F ξ x = ((f x : ℝ) : ℂ) * (Φ ξ - (Φ ξ * cexp (↑(2 * π * ⟪ξ, x⟫) * I) +
        Φ ξ * cexp (↑(2 * π * ⟪ξ, -x⟫) * I)) / 2) := by
      intro ξ
      simp only [hF, hk]
      conv_lhs => rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, hcos ξ]
      ring
    have h12 : Integrable fun ξ => (Φ ξ * cexp (↑(2 * π * ⟪ξ, x⟫) * I) +
        Φ ξ * cexp (↑(2 * π * ⟪ξ, -x⟫) * I)) / 2 := (h1.add h2).div_const 2
    simp_rw [e]
    rw [integral_const_mul, integral_sub hΦi h12, integral_div, integral_add h1 h2]
    change ((f x : ℝ) : ℂ) * ((∫ ξ, (𝓕 S) ξ) - ((∫ ξ, (𝓕 S) ξ * cexp (↑(2 * π * ⟪ξ, x⟫) * I)) +
      ∫ ξ, (𝓕 S) ξ * cexp (↑(2 * π * ⟪ξ, -x⟫) * I)) / 2) = _
    rw [i0, i1, i2]
    push_cast
    ring
  -- (d) assemble
  have hswap := integral_integral_swap hFint
  have hlhs : ∫ ξ, Φ ξ * ((-(stableExp α H' ((2 * π) • ξ) - stableExp α H ((2 * π) • ξ)) : ℝ) :
      ℂ) = -∫ ξ, ∫ x, F ξ x := by
    rw [← integral_neg]
    congr 1; funext ξ
    simp only [hF]
    rw [integral_const_mul, integral_complex_ofReal, ← hD ξ]
    push_cast; ring
  change ∫ ξ, Φ ξ * _ = _
  rw [hlhs, hswap]
  simp_rw [hinner]
  rw [integral_neg, neg_neg, integral_complex_ofReal]
  congr 1
  -- `∫ f (φ + φ∘neg)/2 = ∫ φ f`, `f` being even
  have hφn : Continuous fun x => φ (-x) := hφ.continuous.comp continuous_neg
  have hφnc : HasCompactSupport fun x => φ (-x) := hc.comp_homeomorph (Homeomorph.neg (Rd d))
  have hφn0 : (0 : Rd d) ∉ tsupport fun x => φ (-x) := by
    rw [show (fun x : Rd d => φ (-x)) = φ ∘ (Homeomorph.neg (Rd d)) from rfl,
      tsupport_comp_eq_preimage]
    simpa using hφ0
  have ia : Integrable fun x => φ x * f x := by
    refine ((integrable_mul_stableDensity hα0 hα2 hH' hφ.continuous hc hφ0).sub
      (integrable_mul_stableDensity hα0 hα2 hH hφ.continuous hc hφ0)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hf]; ring
  have ib : Integrable fun x => f x * φ (-x) := by
    refine ((integrable_mul_stableDensity hα0 hα2 hH' hφn hφnc hφn0).sub
      (integrable_mul_stableDensity hα0 hα2 hH hφn hφnc hφn0)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hf]; ring
  have heven : ∫ x, f x * φ (-x) = ∫ x, φ x * f x := by
    have hneg := (LinearIsometryEquiv.neg ℝ (E := Rd d)).measurePreserving.integral_comp
      (LinearIsometryEquiv.neg ℝ (E := Rd d)).toHomeomorph.measurableEmbedding
      (fun x => f x * φ (-x))
    simp only [LinearIsometryEquiv.coe_neg, neg_neg] at hneg
    rw [← hneg]
    congr 1; funext x
    simp only [hf, stableDensity_neg]
    ring
  have e1 : (fun x => f x * ((φ x + φ (-x)) / 2)) =
      fun x => (1 / 2 : ℝ) • (φ x * f x + f x * φ (-x)) := by
    funext x; rw [smul_eq_mul]; ring
  rw [e1, integral_smul, integral_add ia ib, heven, smul_eq_mul]
  have hfx : ∫ x, φ x * f x = ∫ x, φ x * (stableDensity α H' x - stableDensity α H x) := rfl
  rw [hfx]
  ring

/-! ### The node -/

theorem continuousAt_stableDensity [NeZero d] (α : ℝ) {H : Mat d} (hH : H.PosDef) {x : Rd d}
    (hx : x ≠ 0) : ContinuousAt (stableDensity α H) x := by
  have hq : Continuous fun x : Rd d => quad H⁻¹ x := by unfold quad; fun_prop
  have hpos : quad H⁻¹ x ≠ 0 := (quad_pos hH.inv hx).ne'
  unfold stableDensity
  exact continuousAt_const.mul (hq.continuousAt.rpow_const (Or.inl hpos))

/-- **`lem:stable-tail`**: if a positive finite measure `ρ` has
`ρ̂(ω) = exp[-⟨ω,Cω⟩ - ψ_{H'}(ω) + ψ_H(ω)]`, then `ρ` is a probability measure, for every smooth
`φ` with compact support in `ℝ^d ∖ {0}`
`R^α ∫ φ(x/R) ρ(dx) → ∫ φ(x)(n_{H'}(x) - n_H(x)) dx` as `R → ∞`, and `n_H ≤ n_{H'}` off the
origin. -/
theorem stable_tail [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {H H' G : Mat d}
    (hH : H.PosDef) (hH' : H'.PosDef) (ρ : Measure (Rd d)) [IsFiniteMeasure ρ]
    (hρ : ∀ ω : Rd d, charFun ρ ω =
      ((Real.exp (-quad G ω - stableExp α H' ω + stableExp α H ω) : ℝ) : ℂ)) :
    IsProbabilityMeasure ρ ∧
      (∀ φ : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (0 : Rd d) ∉ tsupport φ →
        Tendsto (fun R : ℝ => R ^ α * ∫ x, φ (R⁻¹ • x) ∂ρ) atTop
          (𝓝 (∫ x, φ x * (stableDensity α H' x - stableDensity α H x)))) ∧
      ∀ x : Rd d, x ≠ 0 → stableDensity α H x ≤ stableDensity α H' x := by
  -- `ρ` is a probability measure
  have hprob : IsProbabilityMeasure ρ := by
    have h0 := hρ 0
    rw [charFun_zero, quad_eq_dotProduct, stableExp_zero hα0, stableExp_zero hα0] at h0
    simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, neg_zero, sub_zero,
      add_zero, Real.exp_zero, Complex.ofReal_one] at h0
    have h1 : ρ.real univ = 1 := by exact_mod_cast h0
    rw [Measure.real, ENNReal.toReal_eq_one_iff] at h1
    exact ⟨h1⟩
  -- the exponent `a(ω) = ⟨ω,Gω⟩ + ψ_{H'}(ω) - ψ_H(ω)` is nonnegative
  have hE : ∀ ω, 0 ≤ quad G ω + (stableExp α H' ω - stableExp α H ω) := by
    intro ω
    have h := norm_charFun_le_one (μ := ρ) ω
    rw [hρ, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff] at h
    linarith
  have hlim : ∀ φ : Rd d → ℝ, ∀ hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ,
      ∀ hc : HasCompactSupport φ, (0 : Rd d) ∉ tsupport φ →
      Tendsto (fun R : ℝ => R ^ α * ∫ x, φ (R⁻¹ • x) ∂ρ) atTop
        (𝓝 (∫ x, φ x * (stableDensity α H' x - stableDensity α H x))) := by
    intro φ hφ hc hφ0
    set S := testSchwartz φ hφ hc
    set Φ : Rd d → ℂ := fun ξ => (𝓕 S) ξ with hΦdef
    have hΦi : Integrable Φ := (𝓕 S).integrable
    have hΦc : Continuous Φ := (𝓕 S).continuous
    have hΦ2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖Φ ξ‖ := (𝓕 S).integrable_pow_mul volume 2
    have hΦ0 : ∫ ξ, Φ ξ = 0 := by
      have := testSchwartz_integral φ hφ hc
      rw [image_eq_zero_of_notMem_tsupport hφ0, Complex.ofReal_zero] at this
      exact this
    have hF := tendsto_fourier_side hα0 hα2 hH.posSemidef hH'.posSemidef (G := G) Φ hΦc hΦi hΦ2 hE
    rw [fourier_limit_eq hα0 hα2 hH hH' φ hφ hc hφ0] at hF
    have hC : Tendsto (fun R : ℝ => ((R ^ α * ∫ x, φ (R⁻¹ • x) ∂ρ : ℝ) : ℂ)) atTop
        (𝓝 ((∫ x, φ x * (stableDensity α H' x - stableDensity α H x) : ℝ) : ℂ)) := by
      refine hF.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with R hR
      rw [Complex.ofReal_mul, integral_test_eq_fourier φ hφ hc ρ hR]
      congr 1
      -- `∫ Φ ρ̂ = ∫ Φ (ρ̂ - 1)`, since `∫ Φ = 0`
      have hcf : Integrable fun ξ => Φ ξ * charFun ρ ((2 * π * R⁻¹) • ξ) :=
        hΦi.mul_bdd (c := 1) (by
          have : Continuous fun ξ : Rd d => charFun ρ ((2 * π * R⁻¹) • ξ) :=
            (continuous_charFun (μ := ρ)).comp (continuous_const.smul continuous_id)
          exact this.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun ξ => norm_charFun_le_one _)
      rw [show (fun ξ => Φ ξ * (((Real.exp (-(quad G ((2 * π * R⁻¹) • ξ) +
          (stableExp α H' ((2 * π * R⁻¹) • ξ) - stableExp α H ((2 * π * R⁻¹) • ξ)))) : ℝ) : ℂ) - 1))
          = fun ξ => Φ ξ * charFun ρ ((2 * π * R⁻¹) • ξ) - Φ ξ by
            funext ξ; rw [hρ]; push_cast; ring_nf,
        integral_sub hcf hΦi, hΦ0, sub_zero]
    have := (Complex.continuous_re.tendsto _).comp hC
    rw [Complex.ofReal_re] at this
    exact this.congr fun R => by simp only [Function.comp_apply, Complex.ofReal_re]
  refine ⟨hprob, hlim, fun x0 hx0 => ?_⟩
  -- the sign, by a bump function at a point where `n_{H'} - n_H < 0`
  by_contra hlt
  push Not at hlt
  set f : Rd d → ℝ := fun x => stableDensity α H' x - stableDensity α H x with hf
  have hf0 : f x0 < 0 := by simp only [hf]; linarith
  have hfc : ContinuousAt f x0 :=
    (continuousAt_stableDensity α hH' hx0).sub (continuousAt_stableDensity α hH hx0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hfc.eventually (gt_mem_nhds hf0) : ∀ᶠ x in 𝓝 x0, f x < 0)
  have hn : 0 < ‖x0‖ := norm_pos_iff.2 hx0
  set r' := min r (‖x0‖ / 2) with hr'
  have hr'pos : 0 < r' := lt_min hr (by positivity)
  let b : ContDiffBump x0 := ⟨r' / 2, r', by positivity, by linarith⟩
  have hbφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑b) := b.contDiff
  have hbc : HasCompactSupport (⇑b) := b.hasCompactSupport
  have hb0 : (0 : Rd d) ∉ tsupport (⇑b) := by
    rw [b.tsupport_eq, Metric.mem_closedBall, dist_comm, dist_zero_right]
    have : r' ≤ ‖x0‖ / 2 := min_le_right _ _
    intro h; change ‖x0‖ ≤ r' at h; linarith
  have hL := hlim (⇑b) hbφ hbc hb0
  -- the terms are nonnegative
  have hge : 0 ≤ ∫ x, b x * (stableDensity α H' x - stableDensity α H x) := by
    refine ge_of_tendsto hL ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact mul_nonneg (rpow_pos_of_pos hR α).le (integral_nonneg fun x => b.nonneg)
  -- and the limit is negative
  have hlt' : ∫ x, b x * (stableDensity α H' x - stableDensity α H x) < 0 := by
    have hint : Integrable fun x => b x * f x := by
      refine ((integrable_mul_stableDensity hα0 hα2 hH' b.continuous hbc hb0).sub
        (integrable_mul_stableDensity hα0 hα2 hH b.continuous hbc hb0)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, hf]; ring
    have hnn : ∀ x, 0 ≤ -(b x * f x) := by
      intro x
      by_cases hx : x ∈ Metric.ball x0 r'
      · have := hball x (Metric.ball_subset_ball (min_le_left _ _) hx)
        have := b.nonneg (x := x)
        nlinarith
      · have : b x = 0 := by
          rw [← Function.notMem_support, b.support_eq]; exact hx
        rw [this]; simp
    have hpos : 0 < ∫ x, -(b x * f x) := by
      rw [integral_pos_iff_support_of_nonneg hnn hint.neg]
      refine lt_of_lt_of_le (Metric.measure_ball_pos volume x0 hr'pos) (measure_mono fun x hx => ?_)
      rw [Function.mem_support]
      have h1 := b.pos_of_mem_ball hx
      have h2 := hball x (Metric.ball_subset_ball (min_le_left _ _) hx)
      have : 0 < -(b x * f x) := by nlinarith
      exact this.ne'
    rw [integral_neg] at hpos
    change ∫ x, b x * f x < 0
    linarith
  linarith

end AffineHemigroup
