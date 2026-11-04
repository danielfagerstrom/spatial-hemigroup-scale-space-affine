/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OneParameter
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# `prop:one-parameter-families`(2): the two forms of the contraction hypothesis

`isExpContracting_iff`: every eigenvalue of `B` (as a complex matrix) has positive real part if and
only if `e^{-tB} → 0` as `t → ∞`. Wave 2, group E, Q-0281. Both directions read one lemma,
`e^{A}u = e^{z}u` for an eigenvector `Au = zu` (`exp_mulVec_of_eigenvector`, from the exponential
series). `⇒`: `|e^{-tz}| ≤ ‖e^{-tB}‖`-type bound read on an eigenvector. `⇐`: every eigenvalue of
`E = e^{-B}` is `e^{-z}` for an eigenvalue `z` of `B` (an eigenvector of `B` inside the
`B`-invariant eigenspace of `E`), so the spectral radius of `E` is below `1`, and Gelfand's formula
gives `‖Eⁿ‖ → 0`.
-/

namespace AffineHemigroup

open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

variable {d : ℕ}

/-- **The exponential on an eigenvector**: `e^{A}u = e^{z}u` when `Au = zu`, for complex
matrices. -/
theorem exp_mulVec_of_eigenvector {A : Matrix (Fin d) (Fin d) ℂ} {z : ℂ} {u : Fin d → ℂ}
    (h : A *ᵥ u = z • u) : NormedSpace.exp A *ᵥ u = Complex.exp z • u := by
  have hpow : ∀ n : ℕ, A ^ n *ᵥ u = z ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  let Lin : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun M => M *ᵥ u
      map_add' := fun M N => Matrix.add_mulVec M N u
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap Lin
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL L
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const u
  have heq : (fun n => L ((n.factorial⁻¹ : ℂ) • A ^ n)) =
      fun n => ((n.factorial⁻¹ : ℂ) • z ^ n) • u := by
    funext n
    change ((n.factorial⁻¹ : ℂ) • A ^ n) *ᵥ u = _
    rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]
  rw [heq] at h1
  rw [Complex.exp_eq_exp_ℂ]
  exact h1.unique h2

/-- The complexification `B ↦ B_ℂ` of a real matrix. -/
abbrev cplx (B : Mat d) : Matrix (Fin d) (Fin d) ℂ := B.map ((↑) : ℝ → ℂ)

/-- `e^{B}` commutes with complexification. -/
theorem cplx_mexp (A : Mat d) : cplx (mexp A) = NormedSpace.exp (cplx A) := by
  have hc : Continuous (Complex.ofRealHom.mapMatrix : Mat d →+* Matrix (Fin d) (Fin d) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  exact NormedSpace.map_exp _ hc A

/-- `((-t)B)_ℂ = -(t B_ℂ)`. -/
theorem cplx_neg_smul (t : ℝ) (B : Mat d) : cplx ((-t) • B) = -((t : ℂ) • cplx B) := by
  ext i j
  simp

/-- An eigenvalue of a complex matrix has an eigenvector. -/
theorem exists_eigenvector_of_mem_spectrum {A : Matrix (Fin d) (Fin d) ℂ} {z : ℂ}
    (hz : z ∈ spectrum ℂ A) : ∃ u : Fin d → ℂ, u ≠ 0 ∧ A *ᵥ u = z • u := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hz
  obtain ⟨u, hu, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hz
  refine ⟨u, hu, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at h
  exact h.symm

/-- An eigenvector gives an eigenvalue in the spectrum. -/
theorem mem_spectrum_of_eigenvector {A : Matrix (Fin d) (Fin d) ℂ} {z : ℂ} {u : Fin d → ℂ}
    (hu : u ≠ 0) (h : A *ᵥ u = z • u) : z ∈ spectrum ℂ A := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hu, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h,
    sub_self]

/-- **`prop:one-parameter-families`(2)**, the hypothesis's two forms (blind review R4-2): every
eigenvalue of `B` has positive real part if and only if `e^{tB} → 0` as `t → -∞`
(`IsExpContracting B`). The eigenvalues are the spectrum of `B` as a complex matrix. -/
theorem isExpContracting_iff (B : Mat d) :
    IsExpContracting B ↔
      ∀ z ∈ spectrum ℂ (B.map ((↑) : ℝ → ℂ)), 0 < z.re := by
  have hcplxc : Continuous (cplx : Mat d → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  constructor
  · -- `⇒`: read `e^{-tB}` on a complex eigenvector
    intro hB z hz
    obtain ⟨u, hu, huz⟩ := exists_eigenvector_of_mem_spectrum hz
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    have hev : ∀ t : ℝ, cplx (mexp ((-t) • B)) *ᵥ u = Complex.exp (-((t : ℂ) * z)) • u := by
      intro t
      rw [cplx_mexp, cplx_neg_smul]
      refine exp_mulVec_of_eigenvector ?_
      rw [Matrix.neg_mulVec, Matrix.smul_mulVec, huz, smul_smul, neg_smul]
    -- the left side tends to `0`
    have hc : Continuous fun M : Matrix (Fin d) (Fin d) ℂ => (M *ᵥ u) k :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun t : ℝ => (cplx (mexp ((-t) • B)) *ᵥ u) k) atTop
        (𝓝 (((cplx 0) *ᵥ u) k)) := ((hc.comp hcplxc).tendsto 0).comp hB
    have hz0 : ((cplx (0 : Mat d)) *ᵥ u) k = 0 := by simp
    rw [hz0] at hlim
    simp only [hev, Pi.smul_apply, smul_eq_mul] at hlim
    have hn : Tendsto (fun t : ℝ => ‖Complex.exp (-((t : ℂ) * z))‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => ‖Complex.exp (-((t : ℂ) * z)) * u k‖) atTop (𝓝 ‖(0 : ℂ)‖) :=
        (continuous_norm.tendsto 0).comp hlim
      rw [norm_zero] at h1
      have h2 := h1.div_const ‖u k‖
      rw [zero_div] at h2
      refine h2.congr fun t => ?_
      rw [norm_mul]
      field_simp [norm_ne_zero_iff.2 hk]
    by_contra hre
    push Not at hre
    have hge : ∀ t : ℝ, 0 ≤ t → 1 ≤ ‖Complex.exp (-((t : ℂ) * z))‖ := by
      intro t ht
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact Real.one_le_exp (by nlinarith)
    have := ge_of_tendsto hn (eventually_atTop.2 ⟨0, fun t ht => hge t ht⟩)
    norm_num at this
  · -- `⇐`: the spectral radius of `E = e^{-B_ℂ}` is below `1`
    intro hspec
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · -- `d = 0`: the matrices form a point
      exact tendsto_const_nhds.congr fun t => Subsingleton.elim _ _
    haveI : NeZero d := ⟨hdpos.ne'⟩
    show Tendsto (fun t : ℝ => mexp ((-t) • B)) atTop (𝓝 0)
    set Bc := cplx B with hBc
    set E : Matrix (Fin d) (Fin d) ℂ := NormedSpace.exp (-Bc) with hE
    have hcomm : Commute Bc E := ((Commute.refl Bc).neg_right).exp_right
    -- every eigenvalue of `E` is `e^{-z}` with `z` an eigenvalue of `B`
    have hμ : ∀ μ ∈ spectrum ℂ E, ‖μ‖ < 1 := by
      intro μ hμE
      obtain ⟨w, hw, hEw⟩ := exists_eigenvector_of_mem_spectrum hμE
      set f : Module.End ℂ (Fin d → ℂ) := Matrix.toLin' Bc with hf
      set V := Module.End.eigenspace (Matrix.toLin' E) μ with hV
      have hmemV : ∀ x : Fin d → ℂ, x ∈ V ↔ E *ᵥ x = μ • x := by
        intro x
        rw [hV, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hwV : w ∈ V := (hmemV w).2 hEw
      have hfV : ∀ x ∈ V, f x ∈ V := by
        intro x hx
        rw [hmemV] at hx ⊢
        rw [hf, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hcomm.eq, ← Matrix.mulVec_mulVec, hx,
          Matrix.mulVec_smul]
      haveI : Nontrivial V := ⟨⟨⟨w, hwV⟩, 0, fun h => hw (congrArg Subtype.val h)⟩⟩
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict hfV)
      obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
      have hx0 : (x : Fin d → ℂ) ≠ 0 := fun h => hx.2 (Subtype.ext h)
      have hBx : Bc *ᵥ (x : Fin d → ℂ) = c • (x : Fin d → ℂ) := by
        have h1 := Module.End.mem_eigenspace_iff.1 hx.1
        have h2 := congrArg Subtype.val h1
        simpa [hf, LinearMap.restrict_apply, Matrix.toLin'_apply] using h2
      have hEx : E *ᵥ (x : Fin d → ℂ) = μ • (x : Fin d → ℂ) := (hmemV _).1 x.2
      have hEx' : E *ᵥ (x : Fin d → ℂ) = Complex.exp (-c) • (x : Fin d → ℂ) := by
        rw [hE]
        refine exp_mulVec_of_eigenvector ?_
        rw [Matrix.neg_mulVec, hBx, neg_smul]
      have hμc : μ = Complex.exp (-c) := by
        rw [hEx] at hEx'
        obtain ⟨k, hk⟩ : ∃ k, (x : Fin d → ℂ) k ≠ 0 := by
          by_contra h
          push Not at h
          exact hx0 (funext h)
        have := congrFun hEx' k
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact mul_right_cancel₀ hk this
      have hcre := hspec c (mem_spectrum_of_eigenvector hx0 hBx)
      rw [hμc, Complex.norm_exp, Complex.neg_re, ← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by linarith)
    -- the spectral radius is below `1`
    obtain ⟨μ₀, hμ₀, hr⟩ := spectrum.exists_nnnorm_eq_spectralRadius E
    have hr1 : spectralRadius ℂ E < 1 := by
      rw [← hr]
      have h1 : ‖μ₀‖₊ < 1 := by
        have := hμ μ₀ hμ₀
        exact_mod_cast this
      exact_mod_cast h1
    obtain ⟨q', hrq, hq1⟩ := exists_between hr1
    have hqtop : q' ≠ ⊤ := ne_top_of_lt hq1
    set q := q'.toReal with hq
    have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
    have hq1' : q < 1 := by
      rw [hq, ← ENNReal.toReal_one]
      exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hq1
    -- Gelfand's formula: `‖Eⁿ‖ ≤ qⁿ` eventually
    have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius E
    have hev : ∀ᶠ n : ℕ in atTop, ‖E ^ n‖ ≤ q ^ n := by
      filter_upwards [hG.eventually (gt_mem_nhds hrq), eventually_ge_atTop 1] with n hn hn1
      have h1 : ‖E ^ n‖ ^ (1 / n : ℝ) < q :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hqtop).1 hn
      have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
      calc ‖E ^ n‖ = (‖E ^ n‖ ^ (1 / n : ℝ)) ^ n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div,
              inv_mul_cancel₀ hpos.ne', Real.rpow_one]
        _ ≤ q ^ n := pow_le_pow_left₀ (by positivity) h1.le n
    have hEn : Tendsto (fun n : ℕ => ‖E ^ n‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hev
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1')
    -- the bound on `[0,1]`
    have hcont : Continuous fun s : ℝ => NormedSpace.exp (-((s : ℂ) • Bc)) :=
      NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal.smul continuous_const).neg)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hcont.continuousOn (s := Icc (0 : ℝ) 1))
    -- `e^{-tB_ℂ} = Eⁿ e^{-sB_ℂ}` with `n = ⌊t⌋`, `s = t - n`
    have hsplit : ∀ t : ℝ, NormedSpace.exp (-((t : ℂ) • Bc)) =
        E ^ ⌊t⌋₊ * NormedSpace.exp (-(((t - ⌊t⌋₊ : ℝ) : ℂ) • Bc)) := by
      intro t
      have hcm : Commute (⌊t⌋₊ • -Bc) (-(((t - ⌊t⌋₊ : ℝ) : ℂ) • Bc)) :=
        (((Commute.refl Bc).neg_left.smul_left _).smul_right _).neg_right
      rw [hE, ← Matrix.exp_nsmul, ← Matrix.exp_add_of_commute _ _ hcm]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_neg, ← neg_add, ← add_smul]
      congr 2
      push_cast
      ring
    have hnorm : Tendsto (fun t : ℝ => ‖NormedSpace.exp (-((t : ℂ) • Bc))‖) atTop (𝓝 0) := by
      have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
      have h1 := (hEn.comp hfl).mul_const C
      rw [zero_mul] at h1
      refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ h1
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [hsplit t]
      have hs : t - ⌊t⌋₊ ∈ Icc (0 : ℝ) 1 :=
        ⟨sub_nonneg.2 (Nat.floor_le ht), by linarith [Nat.lt_floor_add_one t]⟩
      calc _ ≤ ‖E ^ ⌊t⌋₊‖ * ‖NormedSpace.exp (-(((t - ⌊t⌋₊ : ℝ) : ℂ) • Bc))‖ := norm_mul_le _ _
        _ ≤ ‖E ^ ⌊t⌋₊‖ * C := mul_le_mul_of_nonneg_left (hC _ hs) (norm_nonneg _)
        _ = _ := rfl
    have hc : Tendsto (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Bc))) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 hnorm
    -- back to the real matrices
    have hre : Continuous fun M : Matrix (Fin d) (Fin d) ℂ => M.map Complex.re :=
      continuous_id.matrix_map Complex.continuous_re
    have h2 : Tendsto (fun t : ℝ => (NormedSpace.exp (-((t : ℂ) • Bc))).map Complex.re) atTop
        (𝓝 ((0 : Matrix (Fin d) (Fin d) ℂ).map Complex.re)) := (hre.tendsto 0).comp hc
    have h0 : (0 : Matrix (Fin d) (Fin d) ℂ).map Complex.re = 0 := by ext; simp
    rw [h0] at h2
    refine h2.congr fun t => ?_
    have hBt : -((t : ℂ) • Bc) = cplx ((-t) • B) := by
      rw [cplx_neg_smul, hBc]
    rw [hBt, ← cplx_mexp]
    ext i j
    simp

end AffineHemigroup
