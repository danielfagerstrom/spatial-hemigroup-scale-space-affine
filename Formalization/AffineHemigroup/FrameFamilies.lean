/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.SmallerGroups
import AffineHemigroup.Orbits
import AffineHemigroup.RayFamilies
import AffineHemigroup.SingleRatio

/-!
# `prop:frame-families`: frame families, and only the Gaussian loses its frame

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:frame-families`. Wave 2, group E,
Q-0281. The product laws `prodLaw` and their transforms (Mathlib's `charFun_pi`), the frame family's
cascade and covariance, the Gaussian frame family, and the Herschel–Maxwell argument of clause (3).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory Complex
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## Product laws -/

/-- A product of probability measures on `ℝ` is a probability measure on `ℝ^d`. -/
theorem isProbabilityMeasure_prodLaw (ν : Fin d → Measure ℝ)
    (h : ∀ i, IsProbabilityMeasure (ν i)) : IsProbabilityMeasure (prodLaw ν) := by
  haveI := h
  unfold prodLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- **The transform of a product law**: `\widehat{ν₁ ⊗ ⋯ ⊗ ν_d}(ω) = ∏ᵢ ν̂ᵢ(ωᵢ)`. -/
theorem charFun_prodLaw (ν : Fin d → Measure ℝ) (h : ∀ i, IsProbabilityMeasure (ν i))
    (ω : Rd d) : charFun (prodLaw ν) ω = ∏ i, charFun (ν i) (ω i) := by
  haveI := h
  exact charFun_pi ω

/-- The coordinates of `A ω` for a diagonal `A`. -/
theorem lin_diagonal_apply (v : Fin d → ℝ) (ω : Rd d) (j : Fin d) :
    lin (diagonal v) ω j = v j * ω j := by
  rw [ofLp_lin, mulVec_diagonal]

/-- The coordinates of `t e_i`. -/
theorem smul_ebasis_apply (t : ℝ) (i j : Fin d) :
    (t • ebasis i) j = if j = i then t else 0 := by
  simp [ebasis]

/-- A product over the coordinates of `t e_i`, with every factor `1` at `0`. -/
theorem prod_smul_ebasis (f : Fin d → ℝ → ℂ) (hf : ∀ j, f j 0 = 1) (t : ℝ) (i : Fin d) :
    ∏ j, f j ((t • ebasis i) j) = f i t := by
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [smul_ebasis_apply, if_neg hj, hf])
    (fun h => absurd (Finset.mem_univ i) h), smul_ebasis_apply, if_pos rfl]

/-! ## Clause (1) -/

/-- **`prop:frame-families`(1)**: for cascades `ν⁽ⁱ⁾` on the line, the frame family has
`μ̂_{A;s,s'}(ω) = ∏ᵢ ν̂⁽ⁱ⁾_{sᵢ,s'ᵢ}((Aᵀω)ᵢ)`, `μ_{A;s,s} = δ₀`,
`μ_{A;s,s''} = μ_{A;s',s''} * μ_{A;s,s'}` for `s ≤ s' ≤ s''`, and `B_*μ_{A;s,s'} = μ_{BA;s,s'}`
for `A, B ∈ GL(d)` and `0 ≤ s ≤ s'` coordinatewise. -/
theorem frame_family_cascade (ν : Fin d → ℝ → ℝ → Measure ℝ) (hν : ∀ i, IsLineCascade (ν i)) :
    (∀ A ∈ glSet d, ∀ s s' : Fin d → ℝ, 0 ≤ s → s ≤ s' → ∀ ω : Rd d,
        charFun (frameFamily ν A s s') ω = ∏ i, charFun (ν i (s i) (s' i)) ((lin Aᵀ ω) i)) ∧
      (∀ A ∈ glSet d, ∀ s : Fin d → ℝ, 0 ≤ s → frameFamily ν A s s = Measure.dirac 0) ∧
      (∀ A ∈ glSet d, ∀ s s' s'' : Fin d → ℝ, 0 ≤ s → s ≤ s' → s' ≤ s'' →
        frameFamily ν A s s'' = frameFamily ν A s' s'' ∗ frameFamily ν A s s') ∧
      ∀ A ∈ glSet d, ∀ B ∈ glSet d, ∀ s s' : Fin d → ℝ, 0 ≤ s → s ≤ s' →
        push B (frameFamily ν A s s') = frameFamily ν (B * A) s s' := by
  have hpr : ∀ s s' : Fin d → ℝ, 0 ≤ s → s ≤ s' → ∀ i,
      IsProbabilityMeasure (ν i (s i) (s' i)) :=
    fun s s' hs hss' i => (hν i).isProbability _ _ (hs i) (hss' i)
  have hF : ∀ A s s', 0 ≤ s → s ≤ s' → IsProbabilityMeasure (frameFamily ν A s s') := by
    intro A s s' hs hss'
    haveI := isProbabilityMeasure_prodLaw _ (hpr s s' hs hss')
    unfold frameFamily
    infer_instance
  have hcf : ∀ A : Mat d, ∀ s s' : Fin d → ℝ, 0 ≤ s → s ≤ s' → ∀ ω : Rd d,
      charFun (frameFamily ν A s s') ω = ∏ i, charFun (ν i (s i) (s' i)) ((lin Aᵀ ω) i) := by
    intro A s s' hs hss' ω
    rw [frameFamily, push, charFun_map_lin, charFun_prodLaw _ (hpr s s' hs hss')]
  refine ⟨fun A _ s s' hs hss' ω => hcf A s s' hs hss' ω, fun A _ s hs => ?_,
    fun A _ s s' s'' hs hss' hs's'' => ?_, fun A _ B _ s s' _ _ => ?_⟩
  · haveI := hF A s s hs le_rfl
    refine eq_of_charFun_eq fun ω => ?_
    rw [hcf A s s hs le_rfl, charFun_dirac]
    simp only [inner_zero_left, ofReal_zero, zero_mul, Complex.exp_zero]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [(hν i).diag _ (hs i), charFun_dirac]
    simp
  · have hs' : 0 ≤ s' := hs.trans hss'
    haveI := hF A s s'' hs (hss'.trans hs's'')
    haveI := hF A s' s'' hs' hs's''
    haveI := hF A s s' hs hss'
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, hcf A s s'' hs (hss'.trans hs's''), hcf A s' s'' hs' hs's'',
      hcf A s s' hs hss', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    haveI := (hν i).isProbability _ _ (hs' i) (hs's'' i)
    haveI := (hν i).isProbability _ _ (hs i) (hss' i)
    rw [(hν i).cascade _ _ _ (hs i) (hss' i) (hs's'' i), charFun_conv]
  · rw [frameFamily, frameFamily, push_push]

/-! ## Clause (2) -/

/-- `⟨ω, A diag(v) Aᵀ ω⟩ = ∑ᵢ vᵢ (Aᵀω)ᵢ²`. -/
theorem quad_act_diagonal (A : Mat d) (v : Fin d → ℝ) (ω : Rd d) :
    quad (A * diagonal v * Aᵀ) ω = ∑ i, v i * (lin Aᵀ ω i) ^ 2 := by
  have h := quad_act A (diagonal v) ω
  rw [act] at h
  rw [h, quad_eq_dotProduct]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (lin Aᵀ ω).ofLp i * (v i * (lin Aᵀ ω).ofLp i) = v i * (lin Aᵀ ω).ofLp i ^ 2
  ring

/-- **`prop:frame-families`(2)**, the Gaussian frame family: if `b ≥ 0` and every `ν⁽ⁱ⁾_{s,s'}`
is the centred Gaussian of variance `2b(s'² - s²)`, then `μ_{A;0,s}` is the centred Gaussian of
covariance `2b A diag(s²) Aᵀ`, and so depends on `(A, s)` only through `A diag(s²) Aᵀ`. -/
theorem frame_family_gaussian (b : ℝ) (hb : 0 ≤ b) (ν : Fin d → ℝ → ℝ → Measure ℝ)
    (hν : ∀ i s s', 0 ≤ s → s ≤ s' →
      ν i s s' = gaussianReal 0 (2 * b * (s' ^ 2 - s ^ 2)).toNNReal) :
    (∀ A ∈ glSet d, ∀ s : Fin d → ℝ, 0 ≤ s →
        frameFamily ν A 0 s =
          multivariateGaussian 0 ((2 * b) • (A * diagonal (fun i => s i ^ 2) * Aᵀ))) ∧
      ∀ A ∈ glSet d, ∀ A' ∈ glSet d, ∀ s s' : Fin d → ℝ, 0 ≤ s → 0 ≤ s' →
        A * diagonal (fun i => s i ^ 2) * Aᵀ = A' * diagonal (fun i => s' i ^ 2) * A'ᵀ →
        frameFamily ν A 0 s = frameFamily ν A' 0 s' := by
  have hpsd : ∀ (A : Mat d) (s : Fin d → ℝ),
      ((2 * b) • (A * diagonal (fun i => s i ^ 2) * Aᵀ)).PosSemidef := by
    intro A s
    refine PosSemidef.smul ?_ (by positivity)
    have := posSemidef_act A (S := diagonal fun i => s i ^ 2)
      (PosSemidef.diagonal fun i => sq_nonneg (s i))
    simpa [act] using this
  have hmain : ∀ A ∈ glSet d, ∀ s : Fin d → ℝ, 0 ≤ s →
      frameFamily ν A 0 s =
        multivariateGaussian 0 ((2 * b) • (A * diagonal (fun i => s i ^ 2) * Aᵀ)) := by
    intro A _ s hs
    have hg : ∀ i, ν i 0 (s i) = gaussianReal 0 (2 * b * (s i ^ 2)).toNNReal := by
      intro i
      rw [hν i 0 (s i) le_rfl (hs i)]
      simp
    have hpr : ∀ i, IsProbabilityMeasure (ν i ((0 : Fin d → ℝ) i) (s i)) := by
      intro i; rw [Pi.zero_apply, hg i]; infer_instance
    haveI := isProbabilityMeasure_prodLaw _ hpr
    haveI : IsProbabilityMeasure (frameFamily ν A 0 s) := by unfold frameFamily; infer_instance
    refine eq_of_charFun_eq fun ω => ?_
    rw [frameFamily, push, charFun_map_lin, charFun_prodLaw _ hpr,
      charFun_multivariateGaussian_zero (hpsd A s), quad_smul, quad_act_diagonal]
    simp only [Pi.zero_apply, hg, charFun_gaussianReal]
    rw [← Complex.exp_sum, Complex.ofReal_exp]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.coe_toNNReal _ (by have := hs i; positivity)]
    push_cast
    ring
  refine ⟨hmain, fun A hA A' hA' s s' hs hs' heq => ?_⟩
  rw [hmain A hA s hs, hmain A' hA' s' hs', heq]

/-! ## Clause (3): only the Gaussian loses its frame -/

/-- **Hamel's equation with a sign**: a function `G ≥ 0` on `[0,∞)`, additive there and
continuous at `0` from the right, is linear: `G(u) = G(1) u`. Through
`lem:single-ratio-cauchy` (whose last paragraph reads only additivity and `G ≥ 0`). -/
theorem additive_nonneg_linear (G : ℝ → ℝ) (hG0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ G u)
    (hGc : ContinuousWithinAt G (Ici 0) 0)
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → G (x + y) = G x + G y) :
    ∀ u : ℝ, 0 ≤ u → G u = G 1 * u := by
  have hz : G 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at this
    linarith
  refine (single_ratio_cauchy G hG0 hGc hz 2 one_lt_two fun u w hu hw => ?_).1
  rw [hadd _ _ (by positivity) hw, hadd _ _ hu.le hw]
  ring

/-- The norm of `a e₀ + b e₁` for distinct basis vectors. -/
theorem norm_smul_ebasis_add_smul_ebasis {i j : Fin d} (hij : i ≠ j) (a b : ℝ) :
    ‖a • ebasis i + b • ebasis j‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  have hi : ‖ebasis i‖ = 1 := by simp [ebasis]
  have hj : ‖ebasis j‖ = 1 := by simp [ebasis]
  have hinner : ⟪ebasis i, ebasis j⟫ = 0 := by
    simp [ebasis, EuclideanSpace.inner_single_left, Ne.symm hij]
  rw [← Real.sqrt_sq (norm_nonneg _), norm_add_sq_real, norm_smul, norm_smul, inner_smul_left,
    inner_smul_right, hinner, hi, hj]
  congr 1
  simp [sq_abs]

/-- **`prop:frame-families`(3)**, only the Gaussian loses its frame: for `d ≥ 2`, if `μ_{A;0,s}`
depends on `(A, s) ∈ GL(d) × (0,∞)^d` only through `A diag(s²) Aᵀ`, there is `b ≥ 0` with
`ν⁽ⁱ⁾_{0,t}` the centred Gaussian of variance `2bt²` for every `i` and `t > 0`. -/
theorem frame_family_only_gaussian (hd : 2 ≤ d) (ν : Fin d → ℝ → ℝ → Measure ℝ)
    (hν : ∀ i, IsLineCascade (ν i))
    (hdep : ∀ A ∈ glSet d, ∀ A' ∈ glSet d, ∀ s s' : Fin d → ℝ, (∀ i, 0 < s i) → (∀ i, 0 < s' i) →
      A * diagonal (fun i => s i ^ 2) * Aᵀ = A' * diagonal (fun i => s' i ^ 2) * A'ᵀ →
      frameFamily ν A 0 s = frameFamily ν A' 0 s') :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ i, ∀ t : ℝ, 0 < t → ν i 0 t = gaussianReal 0 (2 * b * t ^ 2).toNNReal := by
  haveI : NeZero d := ⟨by omega⟩
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have hpr : ∀ i, ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (ν i 0 t) :=
    fun i t ht => (hν i).isProbability 0 t le_rfl ht
  -- the product law at `𝟏` and its transform
  set P : Measure (Rd d) := prodLaw fun i => ν i 0 1 with hP
  have hpr1 : ∀ i, IsProbabilityMeasure (ν i 0 1) := fun i => hpr i 1 zero_le_one
  haveI hPprob : IsProbabilityMeasure P := isProbabilityMeasure_prodLaw _ hpr1
  have hone : ∀ i : Fin d, (0 : ℝ) < (1 : Fin d → ℝ) i := fun i => one_pos
  have hdiag1 : diagonal (fun i => (1 : Fin d → ℝ) i ^ 2) = 1 := by
    simp [diagonal_one]
  have hframe : ∀ (A : Mat d) (s : Fin d → ℝ),
      frameFamily ν A 0 s = push A (prodLaw fun i => ν i 0 (s i)) := fun A s => rfl
  -- `P` is rotation invariant
  have hrot : IsRotationInvariant P := by
    intro Q hQ
    have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hQ
    have h := hdep Q (orthSet_subset_glSet hQ) 1 (by simp [glSet]) 1 1 hone hone
      (by rw [hdiag1]; simp [hQQ])
    rw [hframe, hframe, push_one] at h
    simpa [hP] using h
  set φ : Fin d → ℝ → ℂ := fun i t => charFun (ν i 0 1) t with hφ
  have hφ0 : ∀ i, φ i 0 = 1 := by intro i; simp [hφ, charFun_zero]
  have hψ : ∀ ω : Rd d, charFun P ω = ∏ i, φ i (ω i) := fun ω => charFun_prodLaw _ hpr1 ω
  -- the radial profile `g(r) := ψ(r e₀)`
  set g : ℝ → ℂ := fun r => charFun P (r • ebasis i0) with hg
  have hrad : ∀ ω : Rd d, charFun P ω = g ‖ω‖ := by
    intro ω
    refine charFun_eq_of_norm_eq hrot ?_
    simp [ebasis, norm_smul]
  have hφg : ∀ i t, φ i t = g |t| := by
    intro i t
    rw [← prod_smul_ebasis φ hφ0 t i, ← hψ, hrad]
    simp [ebasis, norm_smul]
  -- `g` is real, by the reflection `-I`
  have hreal : ∀ r : ℝ, (g r).im = 0 := by
    intro r
    have hneg : charFun P (-(r • ebasis i0)) = charFun P (r • ebasis i0) := by
      rw [hrad, hrad, norm_neg]
    rw [charFun_neg] at hneg
    have := congrArg Complex.im hneg
    simp only [Complex.conj_im] at this
    simp only [hg]
    linarith
  -- `F(u) := g(√u)`, real, multiplicative on `[0,∞)`
  set F : ℝ → ℝ := fun u => (g (Real.sqrt u)).re with hF
  have hgF : ∀ u : ℝ, g (Real.sqrt u) = (F u : ℂ) := by
    intro u
    apply Complex.ext <;> simp [hF, hreal]
  have hmul : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → F (x + y) = F x * F y := by
    intro x y hx hy
    have h := hψ (Real.sqrt x • ebasis i0 + Real.sqrt y • ebasis i1)
    rw [hrad, norm_smul_ebasis_add_smul_ebasis h01, Real.sq_sqrt hx, Real.sq_sqrt hy,
      Finset.prod_eq_mul i0 i1 h01] at h
    · have e0 : (Real.sqrt x • ebasis i0 + Real.sqrt y • ebasis i1) i0 = Real.sqrt x := by
        simp [ebasis, h01]
      have e1 : (Real.sqrt x • ebasis i0 + Real.sqrt y • ebasis i1) i1 = Real.sqrt y := by
        simp [ebasis, Ne.symm h01]
      rw [e0, e1, hφg, hφg, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _), hgF, hgF, hgF] at h
      exact_mod_cast h
    · intro c _ hc
      have : (Real.sqrt x • ebasis i0 + Real.sqrt y • ebasis i1) c = 0 := by
        simp [ebasis, hc.1, hc.2]
      rw [this, hφ0]
    · exact fun h => absurd (Finset.mem_univ _) h
    · exact fun h => absurd (Finset.mem_univ _) h
  -- continuity, `F(0) = 1`, `|F| ≤ 1`
  have hFcont : Continuous F := by
    have : Continuous fun u : ℝ => charFun P (Real.sqrt u • ebasis i0) :=
      (continuous_charFun (μ := P)).comp (Real.continuous_sqrt.smul continuous_const)
    exact Complex.continuous_re.comp this
  have hF0 : F 0 = 1 := by
    simp [hF, hg, charFun_zero]
  have hFle : ∀ u, F u ≤ 1 := by
    intro u
    have h1 := norm_charFun_le_one (μ := P) (Real.sqrt u • ebasis i0)
    have h2 := Complex.re_le_norm (charFun P (Real.sqrt u • ebasis i0))
    exact h2.trans h1
  have hFnn : ∀ u, 0 ≤ u → 0 ≤ F u := by
    intro u hu
    have := hmul (u / 2) (u / 2) (by positivity) (by positivity)
    rw [add_halves] at this
    rw [this]
    exact mul_self_nonneg _
  have hFpos : ∀ u, 0 ≤ u → 0 < F u := by
    intro u hu
    refine lt_of_le_of_ne (hFnn u hu) fun h0 => ?_
    have hzero : ∀ n : ℕ, F (u / 2 ^ n) = 0 := by
      intro n
      induction n with
      | zero => simpa using h0.symm
      | succ n ih =>
        have := hmul (u / 2 ^ (n + 1)) (u / 2 ^ (n + 1)) (by positivity) (by positivity)
        have he : u / 2 ^ (n + 1) + u / 2 ^ (n + 1) = u / 2 ^ n := by
          rw [pow_succ]; field_simp; ring
        rw [he, ih] at this
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by rw [sq]; exact this.symm)
    have hlim : Tendsto (fun n : ℕ => F (u / 2 ^ n)) atTop (𝓝 (F 0)) := by
      refine (hFcont.tendsto 0).comp ?_
      have : Tendsto (fun n : ℕ => u * (1 / 2) ^ n) atTop (𝓝 (u * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul u
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow, div_eq_mul_inv]
    simp only [hzero] at hlim
    rw [hF0] at hlim
    exact one_ne_zero (tendsto_nhds_unique hlim tendsto_const_nhds)
  -- `G := -log F` is linear
  set G : ℝ → ℝ := fun u => -Real.log (F u) with hGdef
  have hGlin := additive_nonneg_linear G
    (fun u hu => by
      simp only [hGdef, neg_nonneg]
      exact Real.log_nonpos (hFnn u hu) (hFle u))
    ((Real.continuousAt_log (hFpos 0 le_rfl).ne').comp (hFcont.continuousAt)).neg.continuousWithinAt
    (fun x y hx hy => by
      simp only [hGdef]
      rw [hmul x y hx hy, Real.log_mul (hFpos x hx).ne' (hFpos y hy).ne']
      ring)
  set b := G 1 with hb
  have hb0 : 0 ≤ b := by
    simp only [hb, hGdef, neg_nonneg]
    exact Real.log_nonpos (hFnn 1 zero_le_one) (hFle 1)
  have hFexp : ∀ u, 0 ≤ u → F u = Real.exp (-(b * u)) := by
    intro u hu
    have h := hGlin u hu
    simp only [hGdef] at h
    rw [← h, neg_neg, Real.exp_log (hFpos u hu)]
  have hφexp : ∀ i (τ : ℝ), φ i τ = ((Real.exp (-(b * τ ^ 2)) : ℝ) : ℂ) := by
    intro i τ
    rw [hφg, ← Real.sqrt_sq (abs_nonneg τ), hgF, sq_abs, hFexp _ (sq_nonneg τ)]
  refine ⟨b, hb0, fun i t ht => ?_⟩
  -- the diagonal frame `A = diag(s)⁻¹`, `s = 𝟏 + (t - 1)eᵢ`
  set s : Fin d → ℝ := Function.update 1 i t with hs
  have hspos : ∀ j, 0 < s j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hs, ht]
    · simp [hs, hj]
  set A : Mat d := diagonal fun j => (s j)⁻¹ with hA
  have hAgl : A ∈ glSet d := by
    simp only [glSet, mem_setOf_eq, hA, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (hspos j).ne')
  have hAeq : A * diagonal (fun j => s j ^ 2) * Aᵀ =
      1 * diagonal (fun j => (1 : Fin d → ℝ) j ^ 2) * (1 : Mat d)ᵀ := by
    rw [hdiag1, hA, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      Matrix.one_mul, transpose_one, Matrix.mul_one, ← diagonal_one]
    congr 1
    ext j
    have := (hspos j).ne'
    field_simp
  have h := hdep A hAgl 1 (by simp [glSet]) s 1 hspos hone hAeq
  rw [hframe, hframe, push_one] at h
  have hprs : ∀ j, IsProbabilityMeasure (ν j 0 (s j)) := fun j => hpr j _ (hspos j).le
  haveI := hpr i t ht.le
  -- read the transforms at `ω = τ eᵢ`
  have hcf : ∀ u : ℝ, charFun (ν i 0 t) u = ((Real.exp (-(b * t ^ 2 * u ^ 2)) : ℝ) : ℂ) := by
    intro u
    have h2 := congrArg (fun m => charFun m ((t * u) • ebasis i)) h
    simp only [Pi.one_apply] at h2
    rw [← hP, hψ, prod_smul_ebasis φ hφ0, hφexp, push, charFun_map_lin,
      charFun_prodLaw _ hprs] at h2
    have e : -(b * t ^ 2 * u ^ 2) = -(b * (t * u) ^ 2) := by ring
    rw [e, ← h2, Finset.prod_eq_single i]
    · have hsi : s i = t := by simp [hs]
      rw [hA, diagonal_transpose, lin_diagonal_apply, smul_ebasis_apply, if_pos rfl, hsi]
      congr 1
      field_simp
    · intro j _ hj
      rw [hA, diagonal_transpose, lin_diagonal_apply, smul_ebasis_apply, if_neg hj, mul_zero]
      haveI := hprs j
      simp [charFun_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  refine Measure.ext_of_charFun (funext fun u => ?_)
  rw [hcf, charFun_gaussianReal, Real.coe_toNNReal _ (by positivity)]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end AffineHemigroup
