/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Scheme
import AffineHemigroup.CharFunSubspace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `lem:affine-reduction` — reduction to one function

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:affine-reduction`. Lean core only.

## The route

The blueprint's, step for step. Two choices of the Lean proof:

* **Radial.** The blueprint uses (K3) with `Q ∈ O(d)`. The proof here uses it with the matrix of
  the reflection in `(ω - ω')^⊥`, which maps `ω` to `ω'` when `|ω| = |ω'|`: the matrix of a linear
  isometry `e` has `A Aᵀ = I` and `lin Aᵀ = e` (`charFun_isometry_invariant`). Reality of `μ̂_I`
  is then radial symmetry at `-ω`, so `Q = -I` is not needed separately.
* **No zeros.** The "first zero" argument is a lemma of its own about a function on the triangle
  `0 ≤ s ≤ t` (`ne_zero_of_cascade`), applied to `f(s,t) = μ̂_{sI,tI}(e₁)`; that `φ` has no zero on
  `[0,∞)` is its value at `t = u`, since `⟨e₁, uI e₁⟩ = u`.
-/

namespace AffineHemigroup

open MeasureTheory Matrix ProbabilityTheory Set Filter
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-- **The first-zero argument** (`lem:affine-reduction`, "No zeros"): a function `f` on the
triangle `0 ≤ s ≤ t`, continuous there, with `f(t,t) = 1` and `f(0,t) = f(s,t) f(0,s)`, has no
zero on `{0} × [0,∞)`. A second-demand candidate: its statement mentions Mathlib types only. -/
theorem ne_zero_of_cascade (f : ℝ → ℝ → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2})
    (hdiag : ∀ t : ℝ, 0 ≤ t → f t t = 1)
    (hcasc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → f 0 t = f s t * f 0 s) :
    ∀ t : ℝ, 0 ≤ t → f 0 t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set T : Set ℝ := {t : ℝ | 0 ≤ t ∧ f 0 t = 0} with hT
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, h⟩ := hcon
    exact ⟨t, ht, h⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1⟩
  have hc0 : ContinuousOn (fun t => f 0 t) (Ici 0) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨le_rfl, ht⟩)
  have hTclosed : IsClosed T := by
    have := hc0.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_singleton (x := (0 : ℂ)))
    convert this using 1
    ext t
    simp [hT]
  set t₀ := sInf T with ht₀def
  have ht₀ : t₀ ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · exfalso
      have h2 := ht₀.2
      rw [← h, hdiag 0 le_rfl] at h2
      exact one_ne_zero h2
    · exact h
  have hbelow : ∀ s : ℝ, 0 ≤ s → s < t₀ → f 0 s ≠ 0 := fun s hs hst h0 =>
    (not_lt.2 (csInf_le hTbdd ⟨hs, h0⟩)) hst
  have hc1 : ContinuousWithinAt (fun s => f s t₀) (Icc 0 t₀) t₀ :=
    (hcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs.1, hs.2⟩)) t₀ ⟨ht₀.1, le_rfl⟩
  have hev : ∀ᶠ s in 𝓝[Ico 0 t₀] t₀, f s t₀ ≠ 0 := by
    have h := (hc1.mono Ico_subset_Icc_self).tendsto
    rw [hdiag t₀ ht₀.1] at h
    exact h.eventually_ne one_ne_zero
  haveI : (𝓝[Ico 0 t₀] t₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico ht₀pos.ne]
    exact ⟨ht₀.1, le_rfl⟩
  obtain ⟨s, hfs, hs⟩ := (hev.and self_mem_nhdsWithin).exists
  have h := hcasc s t₀ hs.1 hs.2.le
  rw [ht₀.2] at h
  exact (mul_ne_zero hfs (hbelow s hs.1 hs.2)) h.symm

/-- **The transform of `μ_I` is invariant under every linear isometry**, by (K3) at the matrix of
the isometry. -/
theorem charFun_isometry_invariant {μ : Mat d → Mat d → Measure (Rd d)}
    (hμ : IsAffineCascadeFamily μ) (e : Rd d ≃ₗᵢ[ℝ] Rd d) (ω : Rd d) :
    charFun (μ 0 1) (e ω) = charFun (μ 0 1) ω := by
  set A : Mat d :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (e.symm : Rd d →L[ℝ] Rd d) with hAdef
  have hlinA : lin A = (e.symm : Rd d →L[ℝ] Rd d) := by
    simp only [lin, hAdef, StarAlgEquiv.apply_symm_apply]
  have hlinAT : lin Aᵀ = (e : Rd d →L[ℝ] Rd d) := by
    rw [lin_transpose, hlinA, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  have hAAT : A * Aᵀ = 1 := by
    apply lin_injective
    rw [lin_mul, hlinA, hlinAT, lin_one]
    ext x
    simp
  have hA : A ∈ glSet d := by
    change IsUnit A.det
    have : A.det * Aᵀ.det = 1 := by rw [← det_mul, hAAT, det_one]
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hp : ((0 : Mat d), (1 : Mat d)) ∈ wedgePairs loewnerLE :=
    ⟨PosSemidef.zero, PosSemidef.one, by simp [loewnerLE, PosSemidef.one]⟩
  have h := hμ.covariant A hA _ hp
  have h0 : act A (0 : Mat d) = 0 := by simp [act]
  have h1 : act A (1 : Mat d) = 1 := by rw [act, mul_one, hAAT]
  simp only [h0, h1] at h
  have h2 := charFun_map_lin A (μ 0 1) ω
  rw [hlinAT] at h2
  change charFun (push A (μ 0 1)) ω = _ at h2
  rw [h] at h2
  exact h2.symm

/-- **`lem:affine-reduction`**: an affine cascade family has `μ̂_Σ(ω) = e^{-g(⟨ω,Σω⟩)}` and
`μ̂_{Σ,Σ'}(ω) = exp[-g(⟨ω,Σ'ω⟩) + g(⟨ω,Σω⟩)]` for a continuous `g : [0,∞) → [0,∞)` with
`g(0) = 0` and `g ≢ 0`. -/
theorem affine_reduction (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsAffineCascadeFamily μ) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∃ u : ℝ, 0 ≤ u ∧ g u ≠ 0) ∧
      (∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
        charFun (μ 0 S) ω = ((Real.exp (-g (quad S ω)) : ℝ) : ℂ)) ∧
      ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' → ∀ ω : Rd d,
        charFun (μ S S') ω = ((Real.exp (-g (quad S' ω) + g (quad S ω)) : ℝ) : ℂ) := by
  have hprob : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → loewnerLE S S' →
      IsProbabilityMeasure (μ S S') := fun S S' hS hS' h => hμ.isProbability (S, S') ⟨hS, hS', h⟩
  have hle0 : ∀ S : Mat d, S.PosSemidef → loewnerLE 0 S := fun S hS => by
    rw [loewnerLE, sub_zero]
    exact hS
  haveI hν : IsProbabilityMeasure (μ 0 1) := hprob 0 1 PosSemidef.zero PosSemidef.one
    (hle0 1 PosSemidef.one)
  /- In dimension `0` there is no such family: every probability law there is `δ₀`. -/
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    apply hμ.nondegenerate
    apply eq_dirac_of_charFun_one_near_zero _ 1 one_pos
    intro η _
    have : η = 0 := by
      ext i
      exact i.elim0
    rw [this, charFun_zero]
    simp
  /- (K3) at the kernels from the origin. -/
  have hcov : ∀ A ∈ glSet d, ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      charFun (μ 0 (act A S)) ω = charFun (μ 0 S) (lin Aᵀ ω) := by
    intro A hA S hS ω
    have h := hμ.covariant A hA (0, S) ⟨PosSemidef.zero, hS, hle0 S hS⟩
    have h0 : act A (0 : Mat d) = 0 := by simp [act]
    simp only [h0] at h
    rw [← h]
    exact charFun_map_lin A (μ 0 S) ω
  /- `μ̂_I` is radial and real. -/
  have hrad : ∀ ω ω' : Rd d, ‖ω‖ = ‖ω'‖ → charFun (μ 0 1) ω = charFun (μ 0 1) ω' := by
    intro ω ω' h
    have := charFun_isometry_invariant hμ (Submodule.reflection (ℝ ∙ (ω - ω'))ᗮ) ω
    rw [Submodule.reflection_sub h] at this
    exact this.symm
  set e₀ : Rd d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he₀def
  have he₀ : ‖e₀‖ = 1 := by simp [he₀def]
  set φ : ℝ → ℂ := fun u => charFun (μ 0 1) (Real.sqrt u • e₀) with hφdef
  have hφ : ∀ ω : Rd d, charFun (μ 0 1) ω = φ (‖ω‖ ^ 2) := by
    intro ω
    apply hrad
    simp only [norm_smul, he₀, mul_one, Real.norm_eq_abs, Real.sqrt_sq (norm_nonneg ω),
      abs_norm]
  have hφcont : Continuous φ :=
    continuous_charFun.comp (Real.continuous_sqrt.smul continuous_const)
  have hreal : ∀ ω : Rd d, (charFun (μ 0 1) ω).im = 0 := by
    intro ω
    have h1 : charFun (μ 0 1) (-ω) = charFun (μ 0 1) ω := hrad _ _ (norm_neg ω)
    rw [charFun_neg] at h1
    exact Complex.conj_eq_iff_im.1 h1
  /- The kernels from the origin, at `Σ ∈ PD(d)`. -/
  have hPD : ∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    set R : Mat d := CFC.sqrt S with hRdef
    have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S (nonneg_of_posSemidef hS.posSemidef)
    have hRT : Rᵀ = R := by
      have h := (CFC.sqrt_nonneg S).isSelfAdjoint
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact h
    have hR : R ∈ glSet d := by
      change IsUnit R.det
      have h1 : R.det * R.det = S.det := by rw [← det_mul, hRR]
      have h2 : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit
      rw [← h1] at h2
      exact isUnit_of_mul_isUnit_left h2
    have hact : act R 1 = S := by rw [act, mul_one, hRT, hRR]
    have h := hcov R hR 1 PosSemidef.one ω
    rw [hact] at h
    rw [h, hφ, hRT]
    congr 1
    rw [← real_inner_self_eq_norm_sq, inner_lin_left, hRT, ← hRR, quad, lin_mul]
    rfl
  /- At every `Σ ∈ PSD(d)`, by (K2) along `(0, Σ + εI) → (0, Σ)`. -/
  have hPSD : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d, charFun (μ 0 S) ω = φ (quad S ω) := by
    intro S hS ω
    have hmem : ∀ ε : ℝ, 0 ≤ ε →
        ((0 : Mat d), S + ε • (1 : Mat d)) ∈ wedgePairs loewnerLE := fun ε hε =>
      ⟨PosSemidef.zero, hS.add (PosSemidef.one.smul hε),
        hle0 _ (hS.add (PosSemidef.one.smul hε))⟩
    have hcurve : Continuous fun ε : ℝ => ((0 : Mat d), S + ε • (1 : Mat d)) := by fun_prop
    have hc : ContinuousOn (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (Ici 0) :=
      (hμ.continuous ω).comp hcurve.continuousOn (fun ε hε => hmem ε hε)
    have h1 : Tendsto (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) (𝓝[>] 0)
        (𝓝 (charFun (μ 0 S) ω)) := by
      have := (hc 0 self_mem_Ici).tendsto
      simp only [zero_smul, add_zero] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 : Tendsto (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) (𝓝[>] 0)
        (𝓝 (φ (quad S ω))) := by
      have hc2 : Continuous fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω) :=
        hφcont.comp ((continuous_quad ω).comp (by fun_prop))
      have := hc2.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have heq : (fun ε : ℝ => charFun (μ 0 (S + ε • (1 : Mat d))) ω) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => φ (quad (S + ε • (1 : Mat d)) ω)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hPD _ (PosDef.posSemidef_add hS (PosDef.one.smul hε)) ω
    exact tendsto_nhds_unique (h1.congr' heq) h2
  /- No zeros. -/
  have hφne : ∀ u : ℝ, 0 ≤ u → φ u ≠ 0 := by
    have hmemT : ∀ p : ℝ × ℝ, 0 ≤ p.1 ∧ p.1 ≤ p.2 →
        (p.1 • (1 : Mat d), p.2 • (1 : Mat d)) ∈ wedgePairs loewnerLE := by
      intro p hp
      refine ⟨PosSemidef.one.smul hp.1, PosSemidef.one.smul (hp.1.trans hp.2), ?_⟩
      rw [loewnerLE, ← sub_smul]
      exact PosSemidef.one.smul (sub_nonneg.2 hp.2)
    have hcontT : ContinuousOn (fun p : ℝ × ℝ => charFun (μ (p.1 • 1) (p.2 • 1)) e₀)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      (hμ.continuous e₀).comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 • (1 : Mat d), p.2 • (1 : Mat d))).continuousOn hmemT
    have hdiagT : ∀ t : ℝ, 0 ≤ t → charFun (μ (t • 1) (t • 1)) e₀ = 1 := by
      intro t ht
      rw [hμ.diag _ (PosSemidef.one.smul ht), charFun_dirac]
      simp
    have hcascT : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        charFun (μ ((0 : ℝ) • 1) (t • 1)) e₀ =
          charFun (μ (s • 1) (t • 1)) e₀ * charFun (μ ((0 : ℝ) • 1) (s • 1)) e₀ := by
      intro s t hs hst
      have m1 := hmemT (0, s) ⟨le_rfl, hs⟩
      have m2 := hmemT (s, t) ⟨hs, hst⟩
      haveI := hμ.isProbability _ m1
      haveI := hμ.isProbability _ m2
      rw [hμ.cascade _ _ _ m1.1 m1.2.1 m2.2.1 m1.2.2 m2.2.2, charFun_conv]
    have key := ne_zero_of_cascade (fun s t => charFun (μ (s • 1) (t • 1)) e₀) hcontT hdiagT
      hcascT
    intro u hu
    have := key u hu
    rwa [zero_smul, hPSD _ (PosSemidef.one.smul hu), quad_smul, quad_one, he₀, one_pow,
      mul_one] at this
  /- `φ` is real, positive and at most `1`; `g := -log φ`. -/
  set φr : ℝ → ℝ := fun u => (φ u).re with hφrdef
  have hφr : ∀ u : ℝ, φ u = (φr u : ℂ) := by
    intro u
    apply Complex.ext
    · simp [hφrdef]
    · simp only [Complex.ofReal_im]
      exact hreal _
  have hφr0 : φr 0 = 1 := by
    simp [hφrdef, hφdef, charFun_zero]
  have hφrcont : Continuous φr := Complex.continuous_re.comp hφcont
  have hφrle : ∀ u : ℝ, φr u ≤ 1 := fun u =>
    (Complex.re_le_norm _).trans (norm_charFun_le_one _)
  have hφrpos : ∀ u : ℝ, 0 ≤ u → 0 < φr u := by
    intro u hu
    by_contra hneg
    push Not at hneg
    obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hu hφrcont.continuousOn
      ⟨hneg, by rw [hφr0]; norm_num⟩
    apply hφne v hv.1
    rw [hφr, hv0, Complex.ofReal_zero]
  set g : ℝ → ℝ := fun u => -Real.log (φr u) with hgdef
  have hexp : ∀ u : ℝ, 0 ≤ u → φ u = ((Real.exp (-g u) : ℝ) : ℂ) := by
    intro u hu
    rw [hφr, hgdef, neg_neg, Real.exp_log (hφrpos u hu)]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hφrcont.continuousOn.log fun u hu => (hφrpos u hu).ne').neg
  · intro u hu
    simp only [hgdef, neg_nonneg]
    exact Real.log_nonpos (hφrpos u hu).le (hφrle u)
  · simp [hgdef, hφr0]
  · by_contra hcon
    push Not at hcon
    apply hμ.nondegenerate
    apply eq_dirac_of_charFun_one_near_zero _ 1 one_pos
    intro η _
    rw [hφ, hexp _ (sq_nonneg _), hcon _ (sq_nonneg _)]
    simp
  · intro S hS ω
    rw [hPSD S hS ω, hexp _ (quad_nonneg hS ω)]
  · intro S S' hS hS' hle ω
    have hc := hμ.cascade 0 S S' PosSemidef.zero hS hS' (hle0 S hS) hle
    haveI := hprob S S' hS hS' hle
    haveI := hprob 0 S PosSemidef.zero hS (hle0 S hS)
    have h1 := congrArg (fun m => charFun m ω) hc
    rw [charFun_conv, hPSD S' hS', hPSD S hS, hexp _ (quad_nonneg hS' ω),
      hexp _ (quad_nonneg hS ω)] at h1
    rw [Real.exp_add, Complex.ofReal_mul, h1, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, Complex.ofReal_one, mul_one]

end AffineHemigroup
