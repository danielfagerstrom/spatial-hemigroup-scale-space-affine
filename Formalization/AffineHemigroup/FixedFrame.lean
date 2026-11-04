/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.FrameFamilies
import AffineHemigroup.CharFunSubspace

/-!
# `prop:fixed-frame-families`: in a fixed frame the families are products

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:fixed-frame-families`. Wave 2,
group E, Q-0281. A step along axis `i` is a blur along axis `i` (`lem:charfn-one-on-subspace` in its
neighbourhood form, `charFun_one_on_subspace`); the splitting identity
`φ(x eᵢ + η) = φ(x eᵢ) φ(η)` for `η ⊥ eᵢ`; the product by induction over the coordinates; the
factors self-decomposable; the converse.
-/

namespace AffineHemigroup

open ScaleSpace (IsSelfDecomposable isSelfDecomposable_iff_charFun)

open MeasureTheory Set Filter Matrix Complex
open scoped Topology RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## Coordinates -/

/-- The coordinates of `eᵢ`. -/
theorem ebasis_apply (i j : Fin d) : ebasis i j = if j = i then 1 else 0 := by
  simp [ebasis]

/-- The coordinates of a finite sum `∑_{i ∈ T} ωᵢ eᵢ`. -/
theorem sum_smul_ebasis_apply (ω : Rd d) (T : Finset (Fin d)) (j : Fin d) :
    (∑ i ∈ T, ω i • ebasis i) j = if j ∈ T then ω j else 0 := by
  classical
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, ebasis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The `i`-th coordinate of `ℝ^d`. -/
theorem continuous_coord (i : Fin d) : Continuous fun x : Rd d => x i := by fun_prop

/-- **The transform of a coordinate marginal**: `\widehat{(xᵢ)_*μ}(t) = μ̂(t eᵢ)`. -/
theorem charFun_map_coord (μ : Measure (Rd d)) (i : Fin d) (t : ℝ) :
    charFun (μ.map fun x : Rd d => x i) t = charFun μ (t • ebasis i) := by
  rw [charFun_apply, charFun_apply,
    integral_map (continuous_coord i).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  ext x
  congr 3
  rw [inner_smul_right, ebasis, EuclideanSpace.inner_single_right]
  simp

/-- The image of a probability measure on `ℝ` under `x ↦ cx` is a probability measure. -/
theorem isProbabilityMeasure_dilLine (c : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (dilLine c ν) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- `\widehat{(c)_*ν}(t) = ν̂(ct)`. -/
theorem charFun_dilLine (c : ℝ) (ν : Measure ℝ) (t : ℝ) :
    charFun (dilLine c ν) t = charFun ν (c * t) :=
  charFun_map_mul c t

/-- `η ∈ eᵢ^⊥` exactly when `ηᵢ = 0`. -/
theorem mem_orth_ebasis_iff (i : Fin d) (η : Rd d) :
    η ∈ (Submodule.span ℝ {ebasis i})ᗮ ↔ η i = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ebasis,
    EuclideanSpace.inner_single_left]
  simp

/-- The step `D_{𝟏+(λ-1)eᵢ}` moves `x eᵢ + η` to `λx eᵢ + η` when `ηᵢ = 0`. -/
theorem lin_diagonal_update_apply (i : Fin d) (lam x : ℝ) (η : Rd d) (hη : η i = 0) :
    lin (diagonal (Function.update (1 : Fin d → ℝ) i lam)) (x • ebasis i + η) =
      (lam * x) • ebasis i + η := by
  ext j
  rw [lin_diagonal_apply]
  by_cases hj : j = i
  · subst hj
    simp [ebasis_apply, hη]
  · simp [ebasis_apply, hj]

/-! ## A step along an axis is a blur along it -/

/-- **The splitting identity** (`prop:fixed-frame-families`, proof): if `φ` is continuous with
`φ(0) = 1` and, for every `λ > 1`, `φ ∘ D_{𝟏+(λ-1)eᵢ} = φ · ρ̂` for a probability measure `ρ`,
then `φ(x eᵢ + η) = φ(x eᵢ) φ(η)` for every `x` and every `η ⊥ eᵢ`. -/
theorem split_axis (φ : Rd d → ℂ) (hφc : Continuous φ) (hφ0 : φ 0 = 1) (i : Fin d)
    (hstep : ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      ∀ ω, φ (lin (diagonal (Function.update (1 : Fin d → ℝ) i lam)) ω) = φ ω * charFun ρ ω)
    (x : ℝ) (η : Rd d) (hη : η i = 0) :
    φ (x • ebasis i + η) = φ (x • ebasis i) * φ η := by
  set H : Submodule ℝ (Rd d) := (Submodule.span ℝ {ebasis i})ᗮ with hH
  -- `φ` has no zero near the origin
  obtain ⟨r, hr, hnz⟩ : ∃ r > 0, ∀ η' : Rd d, ‖η'‖ < r → φ η' ≠ 0 := by
    have : ∀ᶠ η' in 𝓝 (0 : Rd d), φ η' ≠ 0 :=
      hφc.continuousAt.eventually_ne (by rw [hφ0]; exact one_ne_zero)
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨r, hr, fun η' hη' => h (by simpa using hη')⟩
  -- the two-point identity
  have key : ∀ lam : ℝ, 1 < lam → ∀ x : ℝ,
      φ ((lam * x) • ebasis i + η) * φ (x • ebasis i) =
        φ (x • ebasis i + η) * φ ((lam * x) • ebasis i) := by
    intro lam hlam x
    obtain ⟨ρ, hρ, hfac⟩ := hstep lam hlam
    have h1 : ∀ η' ∈ H, ‖η'‖ < r → charFun ρ η' = 1 := by
      intro η' hη' hr'
      have hη'0 : η' i = 0 := (mem_orth_ebasis_iff i η').1 hη'
      have h := hfac η'
      have he : lin (diagonal (Function.update (1 : Fin d → ℝ) i lam)) η' = η' := by
        have := lin_diagonal_update_apply i lam 0 η' hη'0
        simpa using this
      rw [he] at h
      have hne := hnz η' hr'
      have : φ η' * (charFun ρ η' - 1) = 0 := by rw [mul_sub, ← h]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)
    have hsub := (charFun_one_on_subspace ρ H r hr h1).2
    have hηH : η ∈ H := (mem_orth_ebasis_iff i η).2 hη
    have ha := hfac (x • ebasis i + η)
    rw [lin_diagonal_update_apply i lam x η hη, hsub _ _ hηH] at ha
    have hb := hfac (x • ebasis i)
    have h0 : (0 : Rd d) i = 0 := rfl
    have hb' := lin_diagonal_update_apply i lam x 0 h0
    rw [add_zero, add_zero] at hb'
    rw [hb'] at hb
    rw [ha, hb]
    ring
  -- let `x → 0` along `x₀/(n+2)`
  have hx : Tendsto (fun n : ℕ => x / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using this.inv_tendsto_atTop.const_mul x
  have hlimL : Tendsto (fun n : ℕ => φ (x • ebasis i + η) * φ ((x / ((n : ℝ) + 2)) • ebasis i))
      atTop (𝓝 (φ (x • ebasis i + η) * φ ((0 : ℝ) • ebasis i))) :=
    ((hφc.comp (continuous_id.smul continuous_const)).tendsto 0 |>.comp hx).const_mul _
  have hlimR : Tendsto (fun n : ℕ => φ ((x / ((n : ℝ) + 2)) • ebasis i + η) * φ (x • ebasis i))
      atTop (𝓝 (φ ((0 : ℝ) • ebasis i + η) * φ (x • ebasis i))) :=
    ((hφc.comp ((continuous_id.smul continuous_const).add continuous_const)).tendsto 0
      |>.comp hx).mul_const _
  have heq : ∀ n : ℕ, φ (x • ebasis i + η) * φ ((x / ((n : ℝ) + 2)) • ebasis i) =
      φ ((x / ((n : ℝ) + 2)) • ebasis i + η) * φ (x • ebasis i) := by
    intro n
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    have := key ((n : ℝ) + 2) hn (x / ((n : ℝ) + 2))
    have hc : ((n : ℝ) + 2) * (x / ((n : ℝ) + 2)) = x := by field_simp
    rw [hc] at this
    exact this
  have := tendsto_nhds_unique (hlimL.congr heq) hlimR
  rw [zero_smul, zero_add, hφ0, mul_one] at this
  rw [this, mul_comm]

/-- **The product**: if `φ(x eᵢ + η) = φ(x eᵢ) φ(η)` for every `i`, `x` and `η ⊥ eᵢ`, and
`φ(0) = 1`, then `φ(ω) = ∏ᵢ φ(ωᵢ eᵢ)`. -/
theorem eq_prod_of_split (φ : Rd d → ℂ) (hφ0 : φ 0 = 1)
    (hsplit : ∀ i (x : ℝ) (η : Rd d), η i = 0 → φ (x • ebasis i + η) = φ (x • ebasis i) * φ η)
    (ω : Rd d) : φ ω = ∏ i, φ (ω i • ebasis i) := by
  classical
  have hT : ∀ T : Finset (Fin d),
      φ (∑ i ∈ T, ω i • ebasis i) = ∏ i ∈ T, φ (ω i • ebasis i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [hφ0]
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, hsplit a, ih]
      rw [sum_smul_ebasis_apply, if_neg ha]
  have hω : ω = ∑ i, ω i • ebasis i := by
    ext j
    rw [sum_smul_ebasis_apply, if_pos (Finset.mem_univ j)]
  conv_lhs => rw [hω]
  exact hT Finset.univ

/-! ## The node -/

/-- **`prop:fixed-frame-families`**: probability measures `(μ_s)_{s ∈ (0,∞)^d}` with (D1)
covariance under the positive diagonal group and (D2) a cascade along each axis at `𝟏` are
`μ_s = (s₁)_*ν₁ ⊗ ⋯ ⊗ (s_d)_*ν_d` for self-decomposable laws `ν₁, …, ν_d` on `ℝ`. -/
theorem fixed_frame_families (_hd : 1 ≤ d) (μ : (Fin d → ℝ) → Measure (Rd d))
    (hprob : ∀ s : Fin d → ℝ, (∀ i, 0 < s i) → IsProbabilityMeasure (μ s))
    (hD1 : ∀ δ s : Fin d → ℝ, (∀ i, 0 < δ i) → (∀ i, 0 < s i) →
      push (diagonal δ) (μ s) = μ (δ * s))
    (hD2 : ∀ i : Fin d, ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      μ (Function.update (1 : Fin d → ℝ) i lam) = μ 1 ∗ ρ) :
    ∃ ν : Fin d → Measure ℝ, (∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) ∧
      ∀ s : Fin d → ℝ, (∀ i, 0 < s i) → μ s = prodLaw fun i => dilLine (s i) (ν i) := by
  have hone : ∀ i : Fin d, (0 : ℝ) < (1 : Fin d → ℝ) i := fun _ => one_pos
  haveI hμ1 : IsProbabilityMeasure (μ 1) := hprob 1 hone
  -- the form of the family
  have hform : ∀ s : Fin d → ℝ, (∀ i, 0 < s i) → μ s = push (diagonal s) (μ 1) := by
    intro s hs
    rw [hD1 s 1 hs hone, mul_one]
  set φ : Rd d → ℂ := charFun (μ 1) with hφ
  have hφ0 : φ 0 = 1 := by simp [hφ, charFun_zero]
  have hφc : Continuous φ := continuous_charFun
  have hpos_upd : ∀ i (lam : ℝ), 1 < lam → ∀ j, 0 < Function.update (1 : Fin d → ℝ) i lam j := by
    intro i lam hlam j
    by_cases hj : j = i
    · subst hj; simp; linarith
    · simp [hj]
  -- (D2) on transforms
  have hstep : ∀ i (lam : ℝ), 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
      ∀ ω, φ (lin (diagonal (Function.update (1 : Fin d → ℝ) i lam)) ω) = φ ω * charFun ρ ω := by
    intro i lam hlam
    obtain ⟨ρ, hρ, h⟩ := hD2 i lam hlam
    refine ⟨ρ, hρ, fun ω => ?_⟩
    have h2 := congrArg (fun m => charFun m ω) h
    rw [hform _ (hpos_upd i lam hlam), push, charFun_map_lin, diagonal_transpose,
      charFun_conv] at h2
    exact h2
  have hsplit : ∀ i (x : ℝ) (η : Rd d), η i = 0 → φ (x • ebasis i + η) = φ (x • ebasis i) * φ η :=
    fun i x η hη => split_axis φ hφc hφ0 i (hstep i) x η hη
  -- the factors
  set ν : Fin d → Measure ℝ := fun i => (μ 1).map fun x : Rd d => x i with hν
  have hνprob : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i => Measure.isProbabilityMeasure_map (continuous_coord i).aemeasurable
  have hνcf : ∀ i t, charFun (ν i) t = φ (t • ebasis i) := fun i t => charFun_map_coord _ i t
  refine ⟨ν, fun i => ⟨hνprob i, ?_⟩, fun s hs => ?_⟩
  · -- each factor is self-decomposable
    haveI := hνprob i
    rw [isSelfDecomposable_iff_charFun]
    intro c hc0 hc1
    have hlam : 1 < c⁻¹ := one_lt_inv₀ hc0 |>.2 hc1
    obtain ⟨ρ, hρ, hfac⟩ := hstep i c⁻¹ hlam
    haveI := hρ
    haveI : IsProbabilityMeasure (ρ.map fun x : Rd d => x i) :=
      Measure.isProbabilityMeasure_map (continuous_coord i).aemeasurable
    refine ⟨((ρ.map fun x : Rd d => x i)).map (c * ·),
      Measure.isProbabilityMeasure_map (by fun_prop), fun ξ => ?_⟩
    rw [hνcf, hνcf, charFun_map_mul, charFun_map_coord]
    have h := hfac ((c * ξ) • ebasis i)
    have h0 : (0 : Rd d) i = 0 := rfl
    have he := lin_diagonal_update_apply i c⁻¹ (c * ξ) 0 h0
    rw [add_zero, add_zero] at he
    rw [he, inv_mul_cancel_left₀ hc0.ne'] at h
    rw [h, smul_eq_mul]
  · -- the product form
    haveI := isProbabilityMeasure_prodLaw _ fun i => isProbabilityMeasure_dilLine (s i) (ν i)
    haveI : IsProbabilityMeasure (μ s) := hprob s hs
    refine eq_of_charFun_eq fun ω => ?_
    rw [hform s hs, push, charFun_map_lin, diagonal_transpose,
      charFun_prodLaw _ fun i => isProbabilityMeasure_dilLine (s i) (ν i), ← hφ,
      eq_prod_of_split φ hφ0 hsplit]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [charFun_dilLine, hνcf, lin_diagonal_apply]

/-- **`prop:fixed-frame-families`**, the converse: for self-decomposable laws `ν₁, …, ν_d` on `ℝ`
the family `μ_s := (s₁)_*ν₁ ⊗ ⋯ ⊗ (s_d)_*ν_d` satisfies (D1) and (D2), and cascades along the
coordinatewise order: `μ_{s'} = μ_s * (ρ⁽¹⁾_{s₁,s'₁} ⊗ ⋯ ⊗ ρ⁽ᵈ⁾_{s_d,s'_d})` for `s ≤ s'`. -/
theorem fixed_frame_families_converse (_hd : 1 ≤ d) (ν : Fin d → Measure ℝ)
    (hν : ∀ i, IsProbabilityMeasure (ν i) ∧ IsSelfDecomposable (ν i)) :
    let μ : (Fin d → ℝ) → Measure (Rd d) := fun s => prodLaw fun i => dilLine (s i) (ν i)
    (∀ δ s : Fin d → ℝ, (∀ i, 0 < δ i) → (∀ i, 0 < s i) → push (diagonal δ) (μ s) = μ (δ * s)) ∧
      (∀ i : Fin d, ∀ lam : ℝ, 1 < lam → ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
        μ (Function.update (1 : Fin d → ℝ) i lam) = μ 1 ∗ ρ) ∧
      ∃ ρ : Fin d → ℝ → ℝ → Measure ℝ,
        (∀ i, ∀ a a' : ℝ, 0 < a → a ≤ a' → IsProbabilityMeasure (ρ i a a')) ∧
        ∀ s s' : Fin d → ℝ, (∀ i, 0 < s i) → s ≤ s' →
          μ s' = μ s ∗ prodLaw fun i => ρ i (s i) (s' i) := by
  intro μ
  haveI : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).1
  have hμprob : ∀ s, IsProbabilityMeasure (μ s) := fun s =>
    isProbabilityMeasure_prodLaw _ fun i => isProbabilityMeasure_dilLine (s i) (ν i)
  have hμcf : ∀ s ω, charFun (μ s) ω = ∏ i, charFun (ν i) (s i * ω i) := by
    intro s ω
    simp only [μ]
    rw [charFun_prodLaw _ fun i => isProbabilityMeasure_dilLine (s i) (ν i)]
    simp only [charFun_dilLine]
  -- the residuals
  have hres : ∀ i (a a' : ℝ), 0 < a → a < a' → ∃ r : Measure ℝ, IsProbabilityMeasure r ∧
      ∀ t, charFun (ν i) (a' * t) = charFun (ν i) (a * t) * charFun r t := by
    intro i a a' ha haa'
    have ha' : 0 < a' := ha.trans haa'
    haveI := (hν i).1
    obtain ⟨r, hr, hfac⟩ := (isSelfDecomposable_iff_charFun (ν i)).1 (hν i).2 (a / a')
      (div_pos ha ha') ((div_lt_one ha').2 haa')
    refine ⟨dilLine a' r, isProbabilityMeasure_dilLine a' r, fun t => ?_⟩
    rw [hfac (a' * t), charFun_dilLine, smul_eq_mul]
    congr 2
    field_simp
  classical
  set ρ : Fin d → ℝ → ℝ → Measure ℝ := fun i a a' =>
    if h : 0 < a ∧ a < a' then Classical.choose (hres i a a' h.1 h.2) else Measure.dirac 0
    with hρdef
  have hρprob : ∀ i, ∀ a a' : ℝ, IsProbabilityMeasure (ρ i a a') := by
    intro i a a'
    simp only [hρdef]
    split_ifs with h
    · exact (Classical.choose_spec (hres i a a' h.1 h.2)).1
    · infer_instance
  have hρcf : ∀ i (a a' : ℝ), 0 < a → a ≤ a' → ∀ t,
      charFun (ν i) (a' * t) = charFun (ν i) (a * t) * charFun (ρ i a a') t := by
    intro i a a' ha haa' t
    simp only [hρdef]
    split_ifs with h
    · exact (Classical.choose_spec (hres i a a' h.1 h.2)).2 t
    · have : a = a' := le_antisymm haa' (not_lt.1 fun hlt => h ⟨ha, hlt⟩)
      rw [charFun_dirac, this]
      simp
  have hcasc : ∀ s s' : Fin d → ℝ, (∀ i, 0 < s i) → s ≤ s' →
      μ s' = μ s ∗ prodLaw fun i => ρ i (s i) (s' i) := by
    intro s s' hs hss'
    haveI := isProbabilityMeasure_prodLaw _ fun i => hρprob i (s i) (s' i)
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_conv, hμcf, hμcf, charFun_prodLaw _ fun i => hρprob i (s i) (s' i),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact hρcf i (s i) (s' i) (hs i) (hss' i) (ω i)
  refine ⟨fun δ s _ _ => ?_, fun i lam hlam => ⟨prodLaw fun j =>
    ρ j ((1 : Fin d → ℝ) j) (Function.update (1 : Fin d → ℝ) i lam j),
    isProbabilityMeasure_prodLaw _ fun j => hρprob j _ _, ?_⟩,
    ⟨ρ, fun i a a' _ _ => hρprob i a a', hcasc⟩⟩
  · refine eq_of_charFun_eq fun ω => ?_
    rw [push, charFun_map_lin, diagonal_transpose, hμcf, hμcf]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [lin_diagonal_apply, Pi.mul_apply]
    ring_nf
  · refine hcasc 1 _ (fun _ => one_pos) fun j => ?_
    by_cases hj : j = i
    · subst hj; simp; linarith
    · simp [hj]

end AffineHemigroup
