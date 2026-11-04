/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Orbits
import Mathlib.Analysis.InnerProductSpace.Spectrum
import AffineHemigroup.RadialTransform

/-!
# `prop:shape-adapted-apertures` — the apertures of shape-adapted smoothing are rank-deficient steps

Blueprint: `blueprint/src/parts/05-shape-adapted.tex`, `prop:shape-adapted-apertures`. Lean core
only.

## The route

The blueprint's, with two choices of the Lean proof.

* **Clause (1) without an eigenbasis of `M`.** `λ_min(M) = λ↑₁(M)` is attained at a unit
  eigenvector (`lamMin_eq_eigUp_zero`), so `M - I ≥ 0` and `M - I` has a kernel. The range of `P`
  is the span of the eigenspaces of `M` above `1` by three facts: each such eigenspace lies in the
  range (`x = P((w(c-1))⁻¹x)`), the range is orthogonal to the kernel (`P` is symmetric), and the
  eigenspaces span `ℝ^d` (Mathlib's spectral theorem for a symmetric operator), those below `1`
  being `0` as `M - I ≥ 0`. The rank is read through rank–nullity.
* **Clause (3) builds `g` from the kernels.** As in `lem:affine-reduction`: `F(u) := μ̂_I(√u e₁)`
  is real (the transform is radial, so `μ̂_I(-ω) = μ̂_I(ω)`), has no zero
  (`prop:gw-ray-families`(1)), and `F(0) = 1`, so `F > 0` on `[0,∞)` by the intermediate value theorem and `g := -log F`.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix ProbabilityTheory Module
open scoped MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## The least eigenvalue -/

/-- A unit eigenvector for the least entry `λ↑₁` of the ordered spectrum. -/
theorem exists_unit_eigvec_eigUp_zero [NeZero d] {X : Mat d} (hX : X.IsHermitian) :
    ∃ v : Rd d, ‖v‖ = 1 ∧ lin X v = eigUp X 0 • v := by
  obtain ⟨i, hi⟩ := eigUp_mem_eigenvalues hX 0
  have hn : ‖(hX.eigenvectorBasis i : Rd d)‖ = 1 := hX.eigenvectorBasis.orthonormal.norm_eq_one i
  have h : lin X (hX.eigenvectorBasis i) = hX.eigenvalues i • (hX.eigenvectorBasis i : Rd d) := by
    apply WithLp.ofLp_injective 2
    have h := hX.mulVec_eigenvectorBasis i
    rw [ofLp_lin, WithLp.ofLp_smul]
    exact h
  exact ⟨_, hn, by rw [h, hi]⟩

/-- **`λ_min(X) = λ↑₁(X)`** for symmetric `X` (`d ≥ 1`): the Rayleigh form of the least
eigenvalue is the least entry of the ordered spectrum. -/
theorem lamMin_eq_eigUp_zero [NeZero d] {X : Mat d} (hX : X.IsHermitian) :
    lamMin X = eigUp X 0 := by
  have hlow : ∀ x : Rd d, eigUp X 0 * ‖x‖ ^ 2 ≤ ⟪x, lin X x⟫ := by
    intro x
    have h := quad_nonneg ((posSemidef_sub_smul_one_iff hX (eigUp X 0)).2 le_rfl) x
    rw [quad_sub, quad_smul, quad_one] at h
    unfold quad at h
    linarith
  obtain ⟨v, hvn, hXv⟩ := exists_unit_eigvec_eigUp_zero hX
  have hval : ⟪v, lin X v⟫ = eigUp X 0 := by
    rw [hXv, inner_smul_right, real_inner_self_eq_norm_sq, hvn, one_pow, mul_one]
  have hlow' : ∀ x : {x : Rd d // ‖x‖ = 1}, eigUp X 0 ≤ ⟪(x : Rd d), lin X x⟫ := by
    intro x
    have h := hlow x
    rwa [x.2, one_pow, mul_one] at h
  haveI : Nonempty {x : Rd d // ‖x‖ = 1} := ⟨⟨v, hvn⟩⟩
  unfold lamMin
  apply le_antisymm
  · have hb : BddBelow (Set.range fun x : {x : Rd d // ‖x‖ = 1} => ⟪(x : Rd d), lin X x⟫) :=
      ⟨eigUp X 0, by rintro _ ⟨x, rfl⟩; exact hlow' x⟩
    exact (ciInf_le hb ⟨v, hvn⟩).trans_eq hval
  · exact le_ciInf hlow'

/-- `λ_min(tM) = t λ_min(M)` for `t ≥ 0`. -/
theorem lamMin_smul {t : ℝ} (ht : 0 ≤ t) (M : Mat d) : lamMin (t • M) = t * lamMin M := by
  unfold lamMin
  rw [Real.mul_iInf_of_nonneg ht]
  congr 1
  ext x
  rw [lin_smul, _root_.smul_apply, inner_smul_right]

/-! ## Clause (1), the step -/

/-- **`prop:shape-adapted-apertures`(1)**, the step: for `M ∈ PD(d)` with least eigenvalue `1`,
`w > 0`, `Σ_w := wM` has least eigenvalue `w`, and `P := Σ_w - wI = w(M - I)` is positive
semidefinite, with kernel the eigenspace of `M` for `1` and range spanned by the eigenvectors of `M`
with eigenvalues above `1`; so `rank P ≤ d - 1`, `rank P = 0` exactly when `M = I`, and for `d = 2`
and `M ≠ I`, `rank P = 1`. -/
theorem shape_adapted_step (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) {M : Mat d} (hM : M.PosDef)
    (hM1 : lamMin M = 1) :
    lamMin (t • M) = t ∧ t • M - t • (1 : Mat d) = t • (M - 1) ∧
      (t • M - t • (1 : Mat d)).PosSemidef ∧
      LinearMap.ker (lin (t • M - t • (1 : Mat d))).toLinearMap =
        Module.End.eigenspace (lin M).toLinearMap 1 ∧
      LinearMap.range (lin (t • M - t • (1 : Mat d))).toLinearMap =
        ⨆ (c : ℝ) (_ : 1 < c), Module.End.eigenspace (lin M).toLinearMap c ∧
      (t • M - t • (1 : Mat d)).rank ≤ d - 1 ∧
      ((t • M - t • (1 : Mat d)).rank = 0 ↔ M = 1) ∧
      (d = 2 → M ≠ 1 → (t • M - t • (1 : Mat d)).rank = 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hX := hM.isHermitian
  have hMT : Mᵀ = M := by
    have := hX.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h0 : eigUp M 0 = 1 := by rw [← lamMin_eq_eigUp_zero hX, hM1]
  have hM1psd : (M - 1).PosSemidef := by
    have := (posSemidef_sub_smul_one_iff hX 1).2 h0.ge
    rwa [one_smul] at this
  set P : Mat d := t • M - t • (1 : Mat d) with hPdef
  have hP : P = t • (M - 1) := (smul_sub t M 1).symm
  have hPpsd : P.PosSemidef := by rw [hP]; exact hM1psd.smul ht.le
  have hPT : Pᵀ = P := by
    rw [hP, transpose_smul, transpose_sub, transpose_one, hMT]
  have hlinP : ∀ x : Rd d, lin P x = t • (lin M x - x) := by
    intro x
    rw [hP, lin_smul, lin_sub, lin_one]
    rfl
  obtain ⟨v, hvn, hMv⟩ := exists_unit_eigvec_eigUp_zero hX
  rw [h0, one_smul] at hMv
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvn
    exact zero_ne_one hvn
  /- The kernel. -/
  have hker : LinearMap.ker (lin P).toLinearMap = Module.End.eigenspace (lin M).toLinearMap 1 := by
    ext x
    rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, one_smul, ContinuousLinearMap.coe_coe,
      hlinP, smul_eq_zero, sub_eq_zero]
    exact ⟨fun h => h.resolve_left ht.ne', fun h => Or.inr h⟩
  /- The range. -/
  set E : ℝ → Submodule ℝ (Rd d) := fun c => Module.End.eigenspace (lin M).toLinearMap c with hE
  have hmemE : ∀ c x, x ∈ E c ↔ lin M x = c • x := fun c x => Module.End.mem_eigenspace_iff
  set K : Submodule ℝ (Rd d) := ⨆ (c : ℝ) (_ : 1 < c), E c with hK
  have hEle : ∀ c : ℝ, 1 < c → E c ≤ LinearMap.range (lin P).toLinearMap := by
    intro c hc x hx
    rw [hmemE] at hx
    refine ⟨(t * (c - 1))⁻¹ • x, ?_⟩
    have hne : t * (c - 1) ≠ 0 := mul_ne_zero ht.ne' (by linarith)
    rw [ContinuousLinearMap.coe_coe, hlinP, map_smul, hx, smul_smul, ← sub_smul, smul_smul]
    have hc1 : c - 1 ≠ 0 := (sub_pos.2 hc).ne'
    have : t * ((t * (c - 1))⁻¹ * c - (t * (c - 1))⁻¹) = 1 := by
      field_simp
    rw [this, one_smul]
  have hKle : K ≤ LinearMap.range (lin P).toLinearMap := iSup₂_le hEle
  have hperp : ∀ y ∈ LinearMap.range (lin P).toLinearMap, ∀ z ∈ E 1, ⟪z, y⟫ = 0 := by
    rintro y ⟨x, rfl⟩ z hz
    rw [hmemE, one_smul] at hz
    rw [ContinuousLinearMap.coe_coe, real_inner_comm, inner_lin_left, hPT, hlinP z, hz, sub_self,
      smul_zero, inner_zero_right]
  have hsymm : ((lin M).toLinearMap).IsSymmetric := by
    intro x y
    change ⟪lin M x, y⟫ = ⟪x, lin M y⟫
    rw [inner_lin_left, hMT]
  have htop : (⨆ μ : ℝ, E μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hsymm.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hbelow : ∀ c : ℝ, c < 1 → E c = ⊥ := by
    intro c hc
    rw [eq_bot_iff]
    intro x hx
    rw [hmemE] at hx
    have hq := quad_nonneg hM1psd x
    have hcx : c • x - x = (c - 1) • x := by rw [sub_smul, one_smul]
    rw [quad, lin_sub, lin_one, _root_.sub_apply, hx, one_apply_eq_self, hcx, inner_smul_right,
      real_inner_self_eq_norm_sq] at hq
    have hx0 : ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x‖]
    rw [Submodule.mem_bot, ← norm_eq_zero]
    nlinarith [norm_nonneg x]
  have hsup : (⊤ : Submodule ℝ (Rd d)) ≤ E 1 ⊔ K := by
    rw [← htop]
    refine iSup_le fun c => ?_
    rcases lt_trichotomy c 1 with h | h | h
    · rw [hbelow c h]
      exact bot_le
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le c h le_rfl)
  have hrange : LinearMap.range (lin P).toLinearMap = K := by
    refine le_antisymm (fun y hy => ?_) hKle
    obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.1 (hsup (Submodule.mem_top (x := y)))
    have hkr := hKle hk
    have haa : ⟪a, a⟫ = 0 := by
      have h1 := hperp y hy a ha
      have h2 := hperp k hkr a ha
      rw [← hak, inner_add_right, h2, add_zero] at h1
      exact h1
    rw [inner_self_eq_zero] at haa
    rw [← hak, haa, zero_add]
    exact hk
  /- The rank, through rank–nullity for `P *ᵥ`. -/
  have hnull := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [Module.finrank_fin_fun] at hnull
  have hkerpos : 0 < finrank ℝ (LinearMap.ker P.mulVecLin) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v.ofLp, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← ofLp_lin, hlinP, hMv, sub_self, smul_zero,
        WithLp.ofLp_zero]
    · intro h
      apply hv0
      have := congrArg Subtype.val h
      exact (WithLp.ofLp_eq_zero 2).1 this
  have hrank_le : P.rank ≤ d - 1 := by
    change finrank ℝ (LinearMap.range P.mulVecLin) ≤ d - 1
    omega
  have hrank0 : P.rank = 0 ↔ M = 1 := by
    constructor
    · intro h
      change finrank ℝ (LinearMap.range P.mulVecLin) = 0 at h
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
      have hP0 : P = 0 := by
        ext i j
        have := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this
      rw [hP, smul_eq_zero, sub_eq_zero] at hP0
      exact hP0.resolve_left ht.ne'
    · intro h
      rw [hP, h, sub_self, smul_zero, rank_zero]
  refine ⟨?_, hP, hPpsd, hker, hrange, hrank_le, hrank0, fun h2 hMI => ?_⟩
  · rw [lamMin_smul ht.le, hM1, mul_one]
  · have := hrank0.not.2 hMI
    omega


/-! ## Clause (2), only the Gaussian follows the apertures -/

/-- The centred Gaussian law with covariance `2bP`, `b ≥ 0`, is carried by the range of `P`
(`δ₀` when `b = 0`). -/
theorem gaussian_carried_by_range {P : Mat d} (hP : P.PosSemidef) {b : ℝ} (hb : 0 ≤ b) :
    multivariateGaussian 0 ((2 * b) • P)
      ((LinearMap.range (lin P).toLinearMap : Set (Rd d))ᶜ) = 0 := by
  rcases hb.lt_or_eq with hb | hb
  · have h := (affineGaussian_carried_by_range hb PosSemidef.zero hP
      (by rw [loewnerLE, sub_zero]; exact hP)).1
    rwa [affineGaussian, sub_zero] at h
  · rw [← hb, mul_zero, zero_smul]
    have h0 : multivariateGaussian (0 : Rd d) (0 : Mat d) = Measure.dirac 0 := by
      apply eq_of_charFun_eq
      intro ω
      rw [charFun_multivariateGaussian_zero PosSemidef.zero, quad_zero, charFun_dirac]
      simp
    have hV : IsClosed ((LinearMap.range (lin P).toLinearMap : Set (Rd d))) :=
      Submodule.closed_of_finiteDimensional _
    rw [h0, Measure.dirac_apply' _ hV.measurableSet.compl]
    simp

/-- **`prop:shape-adapted-apertures`(2)**, only the Gaussian follows the apertures: for `g`, `μ_I`
and the affine orbit `μ_Σ = (Σ^{1/2})_*μ_I` as in `prop:affine-orbits`, and `M ≠ I` as in (1),
there is a probability measure `ρ` with `μ_{Σ_w} = μ_{wI} * ρ` if and only if `g(u) = bu` for some
`b ≥ 0`, that is, `μ_I` is the centred Gaussian law with covariance `2bI`; then `ρ` is the centred
Gaussian law with covariance `2bP`, carried by the range of `P`. -/
theorem shape_adapted_gaussian (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) {M : Mat d} (hM : M.PosDef)
    (hM1 : lamMin M = 1) (hMI : M ≠ 1) (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Ici 0))
    (hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (hg0 : g 0 = 0) (μI : Measure (Rd d))
    [IsProbabilityMeasure μI]
    (hμI : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) :
    ((∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧
        affineOrbit μI (t • M) = affineOrbit μI (t • (1 : Mat d)) ∗ ρ) ↔
        ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, 0 ≤ u → g u = b * u) ∧
      (∀ b : ℝ, 0 ≤ b →
        ((∀ u : ℝ, 0 ≤ u → g u = b * u) ↔ μI = multivariateGaussian 0 ((2 * b) • (1 : Mat d)))) ∧
      ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
        affineOrbit μI (t • M) = affineOrbit μI (t • (1 : Mat d)) ∗ ρ →
        ∃ b : ℝ, 0 ≤ b ∧ (∀ u : ℝ, 0 ≤ u → g u = b * u) ∧
          ρ = multivariateGaussian 0 ((2 * b) • (t • M - t • (1 : Mat d))) ∧
          ρ ((LinearMap.range (lin (t • M - t • (1 : Mat d))).toLinearMap : Set (Rd d))ᶜ) = 0 := by
  obtain ⟨-, -, hPpsd, -, -, hle, h0, -⟩ := shape_adapted_step hd ht hM hM1
  set P : Mat d := t • M - t • (1 : Mat d) with hPdef
  have hrpos : 0 < P.rank := Nat.pos_of_ne_zero fun h => hMI (h0.1 h)
  have hrlt : P.rank < d := by omega
  have hS : (t • (1 : Mat d)).PosDef := PosDef.one.smul ht
  have hTM : t • M = t • (1 : Mat d) + P := by rw [hPdef]; abel
  have hTMpsd : (t • M).PosSemidef := hM.posSemidef.smul ht.le
  /- A convolution identity along the step is the one-step identity of the transforms. -/
  have hstep_of : ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
      affineOrbit μI (t • M) = affineOrbit μI (t • (1 : Mat d)) ∗ ρ → ∀ ω : Rd d,
        ((Real.exp (-g (quad (t • (1 : Mat d) + P) ω)) : ℝ) : ℂ) =
          ((Real.exp (-g (quad (t • (1 : Mat d)) ω)) : ℝ) : ℂ) * charFun ρ ω := by
    intro ρ hρ heq ω
    have h := congrArg (fun m => charFun m ω) heq
    rw [charFun_conv, charFun_affineOrbit_exp hμI hTMpsd,
      charFun_affineOrbit_exp hμI hS.posSemidef, hTM] at h
    exact h
  have hB : ∀ b : ℝ, 0 ≤ b →
      ((∀ u : ℝ, 0 ≤ u → g u = b * u) ↔ μI = multivariateGaussian 0 ((2 * b) • (1 : Mat d))) := by
    intro b hb
    constructor
    · intro hg
      apply eq_of_charFun_eq
      intro ω
      rw [hμI, hg _ (sq_nonneg _), charFun_gaussian_smul_one hb]
    · intro h
      exact eq_mul_of_exp_eq (by omega : 1 ≤ d) fun ω => by
        rw [← hμI, h, charFun_gaussian_smul_one hb]
  have hC : ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
      affineOrbit μI (t • M) = affineOrbit μI (t • (1 : Mat d)) ∗ ρ →
      ∃ b : ℝ, 0 ≤ b ∧ (∀ u : ℝ, 0 ≤ u → g u = b * u) ∧
        ρ = multivariateGaussian 0 ((2 * b) • P) ∧
        ρ ((LinearMap.range (lin P).toLinearMap : Set (Rd d))ᶜ) = 0 := by
    intro ρ hρ heq
    haveI := hρ
    obtain ⟨hg, hg1, hρg⟩ := rank_deficient_step hd g hg_nonneg (hg_cont 0 self_mem_Ici) hg0 _ P
      hS hPpsd hrpos hrlt ρ (hstep_of ρ hρ heq)
    refine ⟨g 1, hg1, hg, hρg, ?_⟩
    rw [hρg]
    exact gaussian_carried_by_range hPpsd hg1
  refine ⟨⟨fun ⟨ρ, hρ, heq⟩ => ?_, fun ⟨b, hb, hg⟩ => ?_⟩, hB, hC⟩
  · obtain ⟨b, hb, hg, -⟩ := hC ρ hρ heq
    exact ⟨b, hb, hg⟩
  · refine ⟨multivariateGaussian 0 ((2 * b) • P), inferInstance, ?_⟩
    apply eq_of_charFun_eq
    intro ω
    rw [charFun_conv, charFun_affineOrbit_exp hμI hTMpsd, charFun_affineOrbit_exp hμI hS.posSemidef,
      hTM]
    exact rank_deficient_step_converse hd g b hb hg _ P hS.posSemidef hPpsd ω

/-! ## Clause (3), in the scheme -/

/-- **`prop:shape-adapted-apertures`(3)**, in the scheme: if `(GL(d), W)` is a wedge datum with
`wI ≤_W wM` for some `w > 0` and some `M ∈ PD(d)` with least eigenvalue `1`, `M ≠ I`, then every
`(GL(d), W)`-cascade family of kernels has a `b > 0` with `μ̂_{Σ,Σ'}(ω) = e^{-b⟨ω,(Σ'-Σ)ω⟩}` for
every pair `Σ ≤_W Σ'`. -/
theorem shape_adapted_scheme (hd : 2 ≤ d) {W : Mat d → Mat d → Prop}
    (hW : IsWedgeDatum (glSet d) W) {t : ℝ} (ht : 0 < t) {M : Mat d} (hM : M.PosDef)
    (hM1 : lamMin M = 1) (hMI : M ≠ 1) (hstep : W (t • (1 : Mat d)) (t • M))
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily (glSet d) W μ) :
    ∃ b : ℝ, 0 < b ∧ ∀ p ∈ wedgePairs W, ∀ ω : Rd d,
      charFun (μ p.1 p.2) ω = ((Real.exp (-(b * quad (p.2 - p.1) ω)) : ℝ) : ℂ) := by
  haveI : NeZero d := ⟨by omega⟩
  /- The restriction to the rays. -/
  have hWray : IsWedgeDatum (glSet d) rayLE :=
    isWedgeDatum_ray glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2
  have hsub : ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → rayLE S S' → W S S' := by
    rintro S S' hS hS' (rfl | ⟨c, hc, rfl⟩)
    · have h := hW.rays S' hS' 0 1 le_rfl zero_le_one
      rwa [zero_smul, one_smul] at h
    · have h := hW.rays S hS 1 c zero_le_one hc
      rwa [one_smul] at h
  have hray := gw_family_restrict hWray hW subset_rfl hsub μ hμ
  obtain ⟨horbit, hrot, hsd, hne, -⟩ := gw_ray_families_gl μ hray
  have hk := gw_kernels_from_origin hW μ hμ
  haveI hI : IsProbabilityMeasure (μ 0 1) := hk.1.isProbability 1 PosSemidef.one
  /- The exponent `g`. -/
  obtain ⟨g, hgc, hgnn, hg0, hg⟩ :=
    exists_exp_of_rotationInvariant (μ 0 1) hrot (selfDecomposable_charFun_ne_zero _ hsd).1
  /- The step `tI ≤_W tM` and clause (2). -/
  have hS : (t • (1 : Mat d)).PosSemidef := PosSemidef.one.smul ht.le
  have hTM : (t • M).PosSemidef := hM.posSemidef.smul ht.le
  obtain ⟨hρ, hcasc⟩ := hk.2 _ _ hS hTM hstep
  rw [horbit _ hS, horbit _ hTM] at hcasc
  obtain ⟨b, hb, hgb⟩ :=
    (shape_adapted_gaussian hd ht hM hM1 hMI g hgc hgnn hg0 (μ 0 1) hg).1.1 ⟨_, hρ, hcasc⟩
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      apply eq_of_charFun_eq
      intro ω
      rw [hg, hgb _ (sq_nonneg _), ← h, charFun_dirac]
      simp
  /- Every pair. -/
  have hform : ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d,
      charFun (μ 0 S) ω = ((Real.exp (-(b * quad S ω)) : ℝ) : ℂ) := by
    intro S hS ω
    rw [horbit S hS, charFun_affineOrbit_exp hg hS, hgb _ (quad_nonneg hS ω)]
  refine ⟨b, hbpos, fun p hp ω => ?_⟩
  obtain ⟨hp1, hp2, hp12⟩ := hp
  obtain ⟨hρ', hc'⟩ := hk.2 _ _ hp1 hp2 hp12
  haveI := hρ'
  haveI := hk.1.isProbability p.1 hp1
  have h := congrArg (fun m => charFun m ω) hc'
  rw [charFun_conv, hform _ hp2, hform _ hp1] at h
  have hne' : ((Real.exp (-(b * quad p.1 ω)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  apply mul_left_cancel₀ hne'
  rw [← h, ← Complex.ofReal_mul, ← Real.exp_add, quad_sub]
  congr 2
  ring

end AffineHemigroup
