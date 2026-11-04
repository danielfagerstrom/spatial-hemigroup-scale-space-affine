/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.IsotropicLibrary
import AffineHemigroup.MaternEndpointProfile
import AffineHemigroup.RadialProfileDatum
import AffineHemigroup.MaternLaw
import ScaleSpaceCore.CausalData

/-!
# Witnesses: the headline theorems' hypotheses are jointly satisfiable

The fidelity review's P1 (article-kit `fidelity-review` skill, § 3.2; `blueprint/REVIEW-fidelity.md`,
section "Witnesses"). Each theorem below instantiates **all** the hypotheses of one of the
isotropic paper's headline theorems (chapter 3) at once, at a concrete model, so that no
headline theorem is true only because nothing satisfies its hypotheses (failure mode F1). They
are named theorems, not `example`s, so that `CIAxiomGuard.lean` can print their axioms; nothing
in the library of the isotropic paper imports this file.

Where the model lives in Lean core the witness certifies the hypothesis class nonempty
independently of the trust boundary. Two models do most of the work, and both are Lean core:

* **the heat family** `μ_{s,t} = N(0, (t² - s²)I)`, the bridge family of `prop:isotropic-bridge`
  at the delay datum `F_I(σ) = σ` (drift `1`, no profile) whose causal kernels are the point
  masses `δ_{y-x}`; it is an isotropic cascade family in every dimension `d ≥ 1`;
* **the Matérn law** `(1 + |ξ|²)^{-γ}` (`prop:affine-orbits`(4)), which is the law of the isotropic
  origin datum `(0, |S^{d-1}| k₀)` of `prop:tempered-step-cone`(4), with profile at the origin
  `c = 2γ`: so it puts the hypotheses of `thm:origin-boundedness-d` in every regime (`γ > d/2`
  above the threshold, `γ ≤ d/2` at and below it), and those of `prop:origin-lower-bound-d`.

The file imports the library of the isotropic paper (`AffineHemigroup.IsotropicLibrary`) and the
three files that hold the Matérn law, its radial profile and the origin datum of a radial
profile. The witnesses of the theorems of chapters 4 and 5 stood here until Q-0452; they are in
`AffineHemigroup.WitnessesAffine`, which imports this file.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-! ## The heat family -/

/-- **The heat delay datum** `F_I(σ) = σ`: drift `1`, no profile. -/
noncomputable def heatCausal : ScaleSpace.CausalAdmissible where
  b₀ := 1
  k := fun _ => 0
  b₀_nonneg := zero_le_one
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  k_zero := rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

theorem heatCausal_exponent {σ : ℝ} (hσ : 0 ≤ σ) : heatCausal.exponent σ = σ := by
  simp [ScaleSpace.CausalAdmissible.exponent, ScaleSpace.CausalAdmissible.exponentL, heatCausal,
    ENNReal.toReal_ofReal hσ]

/-- The causal kernels of the heat delay datum: the point masses `δ_{y-x}`. -/
noncomputable def heatKernelsI : ℝ → ℝ → Measure ℝ := fun x y => Measure.dirac (y - x)

theorem heat_isCausalKernels : IsCausalKernels heatCausal heatKernelsI where
  isProbability := fun _ _ _ _ => by unfold heatKernelsI; infer_instance
  support := fun x y _ hxy => by
    unfold heatKernelsI
    rw [Measure.dirac_apply' _ measurableSet_Iio, indicator_of_notMem]
    simpa using hxy
  laplace := fun x y hx hxy σ hσ => by
    unfold heatKernelsI
    rw [integral_dirac, heatCausal_exponent (mul_nonneg (hx.trans hxy) hσ),
      heatCausal_exponent (mul_nonneg hx hσ)]
    congr 1
    ring

theorem heatCausal_ne_zero : ∃ σ : ℝ, 0 ≤ σ ∧ heatCausal.exponent σ ≠ 0 :=
  ⟨1, zero_le_one, by rw [heatCausal_exponent zero_le_one]; norm_num⟩

/-- **The heat family** `μ_{s,t} := ∫ g^{(d)}_u δ_{t²-s²}(du)`. -/
noncomputable def heatFamily (d : ℕ) : ℝ → ℝ → Measure (Rd d) := bridgeFamily d heatKernelsI

/-- **The heat exponent** `F(r) = F_I(r²/2)`. -/
noncomputable def heatF : ℝ → ℝ := fun r => heatCausal.exponent (r ^ 2 / 2)

theorem isGauge_id : IsGauge id :=
  ⟨rfl, strictMonoOn_id, fun y hy => ⟨y, hy, rfl⟩⟩

/-- **Witness, `thm:isotropic-classification`** (and `def:isotropic-kernel-family`): the heat
family satisfies every hypothesis of the theorem, both sides of its equivalence hold at it, with
the gauge `id` and the exponent `heatF`, and `heatF ∈ 𝒜_d` is not identically `0`. Lean core. -/
theorem witness_isotropic_classification (hd : 1 ≤ d) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (heatFamily d s t)) ∧
      IsIsotropicCascadeFamily (heatFamily d) (fun lam t => lam * t) ∧
      IsGauge id ∧ classA d heatF ∧ (∃ r : ℝ, 0 ≤ r ∧ heatF r ≠ 0) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
        ((Real.exp (-(heatF (id t * ‖ξ‖) - heatF (id s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨hfam, hchar, hA⟩ := isotropic_bridge_family hd heatCausal heatCausal_ne_zero
    heatKernelsI heat_isCausalKernels
  refine ⟨hfam.isProbability, hfam, isGauge_id, hA d hd, ⟨1, zero_le_one, ?_⟩, ?_⟩
  · simp only [heatF]
    rw [heatCausal_exponent (by norm_num)]
    norm_num
  · intro s t hs hst ξ
    simpa [heatF, heatFamily, mul_pow] using hchar s t hs hst ξ

/-- **Witness, `thm:isotropic-classification`, the uniqueness clause**: its hypotheses hold jointly
at the heat family with a second pair `(χ', F') = (2·, F(·/2))` that is *not* the first one, so the
clause's conclusion `χ' = cχ` is exercised at `c = 2 ≠ 1`. Lean core. -/
theorem witness_isotropic_classification_unique (hd : 1 ≤ d) :
    IsGauge (fun t : ℝ => 2 * t) ∧ (fun r : ℝ => heatF (r / 2)) 0 = 0 ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
        ((Real.exp (-((fun r => heatF (r / 2)) ((fun t => 2 * t) t * ‖ξ‖) -
          (fun r => heatF (r / 2)) ((fun t => 2 * t) s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  refine ⟨⟨by norm_num, fun a _ b _ hab => by linarith, fun y hy => ⟨y / 2, ?_, by ring⟩⟩,
    ?_, fun s t hs hst ξ => ?_⟩
  · have : (0 : ℝ) ≤ y := hy
    show (0 : ℝ) ≤ y / 2
    positivity
  · simp [heatF, heatCausal_exponent le_rfl]
  · rw [hrep s t hs hst ξ]
    simp only [id]
    congr 4 <;> ring_nf

/-- **Witness, `cor:isotropic-classification-operators`** (and `def:isotropic-operator-family`):
there are operators on `L¹(ℝ^d)` that are convolution by the heat family on `{0 ≤ s ≤ t}`; they
form an isotropic cascade measurement family, so both sides of the corollary's equivalence hold at
them, with the gauge `id` and the exponent `heatF ∈ 𝒜_d`, not identically `0`; and the second pair
`(χ', F') = (2·, F(·/2))` of `witness_isotropic_classification_unique` meets the hypotheses of the
uniqueness clause with the same measures, so that clause is exercised at `c = 2 ≠ 1`. Lean core. -/
theorem witness_isotropic_classification_operators (hd : 1 ≤ d) :
    ∃ Φ : ℝ → ℝ → (L1 d →L[ℝ] L1 d),
      IsIsotropicOperatorFamily Φ (fun lam t => lam * t) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∃ _ : IsProbabilityMeasure (heatFamily d s t),
        Φ s t = ScaleSpace.mconvL1E (heatFamily d s t)) ∧
      IsGauge id ∧ classA d heatF ∧ (∃ r : ℝ, 0 ≤ r ∧ heatF r ≠ 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
        ((Real.exp (-(heatF (id t * ‖ξ‖) - heatF (id s * ‖ξ‖))) : ℝ) : ℂ)) ∧
      IsGauge (fun t : ℝ => 2 * t) ∧ (fun r : ℝ => heatF (r / 2)) 0 = 0 ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (heatFamily d s t) ξ =
        ((Real.exp (-((fun r => heatF (r / 2)) ((fun t => 2 * t) t * ‖ξ‖) -
          (fun r => heatF (r / 2)) ((fun t => 2 * t) s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨hprob, hfam, hχ, hF, hne, hrep⟩ := witness_isotropic_classification (d := d) hd
  obtain ⟨hχ', hF', hrep'⟩ := witness_isotropic_classification_unique (d := d) hd
  obtain ⟨Φ, hΦ⟩ := exists_operators_of_kernels (heatFamily d) hprob
  exact ⟨Φ, (kernels_to_operators_isotropic hd _ _ hfam Φ hΦ).1, hΦ, hχ, hF, hne, hrep, hχ', hF',
    hrep'⟩

/-! ## The Matérn origin datum -/

/-- `|S^{d-1}| F₀(0) = 2`: the profile at the origin of the Matérn datum is `2γ`. -/
theorem sphereArea_mul_subProfile_zero (hd : 1 ≤ d) : sphereArea d * subProfile d 0 0 = 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hG : Real.Gamma ((d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h4 : (4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf; exact Real.rpow_zero _
  have hπ : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]; ring_nf; exact Real.rpow_zero _
  rw [subProfile_zero hd le_rfl, zero_add, sphereArea, Real.mul_rpow (by norm_num) Real.pi_pos.le]
  calc 2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) *
        ((4 : ℝ) ^ (-(d : ℝ) / 2) * Real.pi ^ (-(d : ℝ) / 2) *
          ((4 : ℝ) ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)))
      = 2 * (Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-(d : ℝ) / 2)) *
          ((4 : ℝ) ^ (-(d : ℝ) / 2) * 4 ^ ((d : ℝ) / 2)) *
          (Real.Gamma ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) := by ring
    _ = 2 := by rw [hπ, h4, div_self hG]; ring

/-- The exponent of the Matérn endpoint profile of `prop:tempered-step-cone`(4):
`ψ_I(ω) = γ log(1 + |ω|²)`. -/
theorem maternEndpoint_exponent (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (ω : Rd d) :
    (maternEndpointProfile hd γ hγ).exponent ω = γ * Real.log (1 + ‖ω‖ ^ 2) := by
  have hK2 : ∀ r : ℝ, 0 < r → (maternEndpointProfile hd γ hγ).k r =
      r ^ (-(2 * (0 : ℝ))) * (γ * subProfile d 0 r) := fun r _ => by
    simp [maternEndpointProfile]
  have hu : 0 ≤ ‖ω‖ ^ 2 := sq_nonneg _
  have hlog : 0 ≤ Real.log (1 + ‖ω‖ ^ 2) := Real.log_nonneg (by linarith)
  rw [RadialProfile.exponent, exponentL_of_subProfile hd _ le_rfl hγ.le hK2 ω,
    lintegral_frullani_subordinator hu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ.le,
    ENNReal.toReal_ofReal hlog]

/-- **The Matérn origin datum** `(0, |S^{d-1}| k₀)` in dimension `d`, `k₀` the profile of
`prop:tempered-step-cone`(4); its law is the Matérn law of index `γ`. -/
noncomputable def maternOriginDatum (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) : OriginDatum d :=
  (maternEndpointProfile hd γ hγ).toOriginDatum hd

theorem maternOriginDatum_a (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) : (maternOriginDatum hd γ hγ).a = 0 := rfl

theorem maternOriginDatum_profileAtOrigin (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (maternOriginDatum hd γ hγ).profileAtOrigin = ENNReal.ofReal (2 * γ) := by
  have hL : Tendsto (maternEndpointProfile hd γ hγ).k (𝓝[>] 0) (𝓝 (γ * subProfile d 0 0)) :=
    ((continuous_const.mul (continuous_subProfile hd le_rfl (d := d))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [maternOriginDatum, RadialProfile.toOriginDatum_profileAtOrigin hd _ hL]
  congr 1
  calc sphereArea d * (γ * subProfile d 0 0) = γ * (sphereArea d * subProfile d 0 0) := by ring
    _ = 2 * γ := by rw [sphereArea_mul_subProfile_zero hd]; ring

/-- The exponent of the Matérn origin datum: `F_d(ξ) = γ log(1 + |ξ|²)`, in every dimension. -/
theorem maternOriginDatum_exponent (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (ξ : Rd d) :
    (maternOriginDatum hd γ hγ).exponent ξ = γ * Real.log (1 + ‖ξ‖ ^ 2) := by
  rw [maternOriginDatum, RadialProfile.toOriginDatum_exponent, maternEndpoint_exponent hd hγ]

theorem maternOriginDatum_isLawOf (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) := by
  obtain ⟨hprob, hchar⟩ := gammaGaussLaw_transform (d := d) γ hγ
  refine ⟨hprob, fun ξ => ?_⟩
  rw [hchar ξ, maternOriginDatum, RadialProfile.toOriginDatum_exponent, maternEndpoint_exponent hd hγ,
    exp_neg_mul_log_one_add (sq_nonneg _)]

theorem maternOriginDatum_k_not_ae_zero (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), (maternOriginDatum hd γ hγ).k r = 0 := by
  intro h
  set K := maternEndpointProfile (d := d) hd γ hγ
  obtain ⟨r₀, hr₀, hk₀⟩ := K.k_ne_zero
  have hr₀' : (0 : ℝ) < r₀ := hr₀
  have hA := (sphereArea_eq_toSphere hd).2
  have hpos : ∀ r ∈ Ioc (0 : ℝ) r₀, (maternOriginDatum hd γ hγ).k r ≠ 0 := by
    intro r hr
    have h1 : K.k r₀ ≤ K.k r := K.k_antitone hr.1 hr₀ hr.2
    have h2 : 0 < K.k r₀ := lt_of_le_of_ne (K.k_nonneg r₀ hr₀) (Ne.symm hk₀)
    show sphereArea d * K.k r ≠ 0
    exact (mul_pos hA (h2.trans_le h1)).ne'
  have h' : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) r₀)), (maternOriginDatum hd γ hγ).k r = 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self h
  have h'' := (ae_restrict_iff' measurableSet_Ioc).1 h'
  have hzero : volume (Ioc (0 : ℝ) r₀) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h''] with r hr hmem
    exact hpos r hmem (hr hmem)
  rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_eq_zero] at hzero
  linarith

/-- **Witness, `thm:origin-boundedness-d`** (clauses (1), (2), (4) and (5); clause (3), the
subordinated slice with its delay law, is `witness_origin_subordinated`),
`lem:origin-decay-exponent` and, at `d ≥ 2`, `prop:origin-lower-bound-d`: the Matérn datum has
Gaussian coefficient `0`, profile at the origin `c = 2γ ∈ (0,∞)` and a law, and it lies above the
threshold exactly when `γ > d/2`; so each regime of the theorem is inhabited. Lean core. -/
theorem witness_origin_boundedness (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (maternOriginDatum hd γ hγ).a = 0 ∧ 0 < (maternOriginDatum hd γ hγ).profileAtOrigin ∧
      (maternOriginDatum hd γ hγ).profileAtOrigin ≠ ⊤ ∧
      IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) ∧
      ((d : ℝ≥0∞) < (maternOriginDatum hd γ hγ).profileAtOrigin ↔ (d : ℝ) < 2 * γ) := by
  refine ⟨rfl, ?_, ?_, maternOriginDatum_isLawOf hd hγ, ?_⟩
  · rw [maternOriginDatum_profileAtOrigin]; exact ENNReal.ofReal_pos.2 (by linarith)
  · rw [maternOriginDatum_profileAtOrigin]; exact ENNReal.ofReal_ne_top
  · rw [maternOriginDatum_profileAtOrigin, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)]

/-- **Witness, `prop:isotropic-radial-monotone`**: clause (1) at the heat family, clause (2) at the
Matérn datum, whose polar profile is not almost everywhere `0`. Lean core. -/
theorem witness_radial_monotone (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    IsIsotropicCascadeFamily (heatFamily d) (fun lam t => lam * t) ∧
      (0 < (maternOriginDatum hd γ hγ).a ∨
        ¬ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), (maternOriginDatum hd γ hγ).k r = 0) ∧
      IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) :=
  ⟨(witness_isotropic_classification hd).2.1, Or.inr (maternOriginDatum_k_not_ae_zero hd hγ),
    maternOriginDatum_isLawOf hd hγ⟩

/-! ## An upper bound at the centre (`prop:origin-upper-bound-d`, Q-0415) -/

/-- **Witness, `prop:origin-upper-bound-d`**: the hypotheses hold jointly at the Matérn datum of
index `γ` with `0 < 2γ ≤ d`, in every dimension `d ≥ 1`: Gaussian coefficient `0`, profile at the
origin `c = 2γ` with `0 < c ≤ d`, and a law, the Matérn law. Both regimes are inhabited, `c < d`
and `c = d`, and for `d ≥ 2` the hypotheses of clause (3) are these. Lean core. -/
theorem witness_origin_upper_bound (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ ≤ d) :
    (maternOriginDatum hd γ hγ).a = 0 ∧ 0 < (maternOriginDatum hd γ hγ).profileAtOrigin ∧
      (maternOriginDatum hd γ hγ).profileAtOrigin ≤ d ∧
      IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) := by
  obtain ⟨ha, hc, -, hlaw, -⟩ := witness_origin_boundedness hd hγ
  refine ⟨ha, hc, ?_, hlaw⟩
  rw [maternOriginDatum_profileAtOrigin, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hγd

/-! ## The rate at the centre (`prop:origin-rate-d`, Q-0416) -/

/-- **Witness, `prop:origin-rate-d`(1)**: the hypotheses hold jointly at the Matérn datum of index
`γ` with `0 < 2γ < d`, in every dimension `d ≥ 1`: Gaussian coefficient `0`, profile at the origin
`c = 2γ` with `0 < c < d`, a law, the Matérn law, and a unit vector. Lean core. -/
theorem witness_origin_rate (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ < d) :
    (maternOriginDatum hd γ hγ).a = 0 ∧ 0 < (maternOriginDatum hd γ hγ).profileAtOrigin ∧
      (maternOriginDatum hd γ hγ).profileAtOrigin < d ∧
      IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) ∧ ∃ e : Rd d, ‖e‖ = 1 := by
  obtain ⟨ha, hc, -, hlaw, -⟩ := witness_origin_boundedness hd hγ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨ha, hc, ?_, hlaw, ?_⟩
  · rw [maternOriginDatum_profileAtOrigin, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff hd0).mpr hγd
  · haveI : NeZero d := ⟨by omega⟩
    exact ⟨ebasis (0 : Fin d), by simp [ebasis]⟩

/-- **Witness, `prop:origin-rate-d`(2)**: the hypotheses hold jointly at the Matérn datum of index
`γ = d/2`, in every dimension `d ≥ 1`: Gaussian coefficient `0`, profile at the origin `c = d`, and
a law. Lean core. -/
theorem witness_origin_rate_critical (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : 2 * γ = d) :
    (maternOriginDatum hd γ hγ).a = 0 ∧ (maternOriginDatum hd γ hγ).profileAtOrigin = d ∧
      IsLawOf (maternOriginDatum hd γ hγ) (gammaGaussLaw d γ) := by
  obtain ⟨ha, -, -, hlaw, -⟩ := witness_origin_boundedness hd hγ
  refine ⟨ha, ?_, hlaw⟩
  rw [maternOriginDatum_profileAtOrigin, hγd, ENNReal.ofReal_natCast]

/-! ## The dimension filtration -/

/-- **Witness, `thm:filtration-strict`(1)**: every interval `(w_{d+1}, w_d]` is nonempty; and
`lem:filtration-top`'s two classes share a member, the heat exponent, so `𝒜_∞ = 𝒮` is not an
identity between empty sets. Lean core. -/
theorem witness_filtration (n : ℕ) (hn : 1 ≤ n) :
    (∃ w : ℝ, threshold ((n : ℝ) + 1) < w ∧ w ≤ threshold n) ∧ classS heatF ∧ classAInf heatF := by
  refine ⟨?_, ⟨heatCausal, fun r _ => rfl⟩, ?_⟩
  · obtain ⟨w, hw⟩ := (threshold_strictAnti.2.2 n hn)
    exact ⟨w, hw.1, hw.2⟩
  · exact (isotropic_bridge_family (d := 1) le_rfl heatCausal heatCausal_ne_zero heatKernelsI
      heat_isCausalKernels).2.2

/-! ## One exponent in two dimensions (`cor:origin-profile-exponent`, Q-0409) -/

/-- The exponent `F^{(w)}` of the witness family is the exponent of an isotropic origin datum in
dimension `d` with Gaussian coefficient `0`, for `0 < w ≤ w_d`: the datum whose polar profile is
`k^{(w)}_d` (`lem:delay-polar-profile`, last sentence). It is the datum inside `witness_classA`,
which exports the membership only. Lean core. -/
theorem witnessF_originDatum (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) (hwd : w ≤ threshold d) :
    ∃ O : OriginDatum d, O.a = 0 ∧ ∀ ξ : Rd d, witnessF w ‖ξ‖ = O.exponent ξ := by
  obtain ⟨D, hD0, hDk, hDexp⟩ := witness_isDelayDatum hw
  have hanti : AntitoneOn (polarProfileOf D.k d) (Ioi 0) := by
    have h := (witness_antitone_iff d hd hw).2 hwd
    intro r hr s hs hrs
    rw [polarProfileOf_congr hDk hr, polarProfileOf_congr hDk hs]
    exact h hr hs hrs
  obtain ⟨O, hOa, -, hO⟩ := delay_polar_profile_datum hd D hanti
  refine ⟨O, hOa.trans hD0, fun ξ => ?_⟩
  rw [OriginDatum.exponent, hO ξ, ← DelayDatum.exponent, hDexp]
  rfl

/-- **Witness, `cor:origin-profile-exponent`**(3): one exponent with a datum in two dimensions.
For a `w ∈ (w_3, w_2]` the exponent `F^{(w)}` of the witness family is the exponent of an isotropic
origin datum on the line and of one in the plane, both with Gaussian coefficient `0`, so the
clause's hypotheses hold jointly at `d = 1`, `d' = 2`, at an exponent that is **not subordinated**
(`witnessF_not_classS`, which is where `w > w_3` is used). Lean core. The Matérn data
`maternOriginDatum` give a second instance, subordinated, in every pair of dimensions
(`maternOriginDatum_exponent`; `probe_origin_profile_dimension_free`). -/
theorem witness_origin_profile_exponent :
    ∃ (w : ℝ) (O₁ : OriginDatum 1) (O₂ : OriginDatum 2), 0 < w ∧ threshold ((3 : ℕ) : ℝ) < w ∧
      O₁.a = 0 ∧ O₂.a = 0 ∧ (∀ ξ : Rd 1, witnessF w ‖ξ‖ = O₁.exponent ξ) ∧
      ∀ ξ : Rd 2, witnessF w ‖ξ‖ = O₂.exponent ξ := by
  obtain ⟨w, hw3, hw2⟩ := threshold_strictAnti.2.2 2 (by norm_num)
  have h3 : threshold ((3 : ℕ) : ℝ) < w := by
    have h23 : ((2 : ℕ) : ℝ) + 1 = ((3 : ℕ) : ℝ) := by norm_num
    rwa [h23] at hw3
  have hw : 0 < w := lt_trans (threshold_strictAnti.2.1 3 (by norm_num)) h3
  have h21 : threshold ((2 : ℕ) : ℝ) < threshold ((1 : ℕ) : ℝ) :=
    threshold_strictAnti.1 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by norm_num)) (by norm_num)
  obtain ⟨O₁, hO₁a, hO₁⟩ := witnessF_originDatum (d := 1) le_rfl hw (hw2.trans h21.le)
  obtain ⟨O₂, hO₂a, hO₂⟩ := witnessF_originDatum (d := 2) (by norm_num) hw hw2
  exact ⟨w, O₁, O₂, hw, h3, hO₁a, hO₂a, hO₁, hO₂⟩

/-- The exponent of `witness_origin_profile_exponent` is not subordinated: for `w > w_3`,
`F^{(w)} ∉ 𝒮`, because `𝒮 ⊆ 𝒜_∞ ⊆ 𝒜_3` and `F^{(w)} ∉ 𝒜_3`. Not Lean core: it spends A2, A3 and
A4, as the exclusion `witness_not_classA` and the inclusion `classAInf_of_classS` do. -/
theorem witnessF_not_classS {w : ℝ} (hw : 0 < w) (h3 : threshold ((3 : ℕ) : ℝ) < w) :
    ¬ classS (witnessF w) := fun hS =>
  witness_not_classA (n := 3) (by norm_num) hw h3 (classAInf_of_classS _ hS 3 (by norm_num))

/-- **Witness, `thm:no-cin-ray-in-the-plane`**: the excluded function is an admissible exponent
on the line, so `F ∉ 𝒜_d` is not a consequence of inadmissibility. Lean core. -/
theorem witness_no_cin_ray : ∃ P : ScaleSpace.SDProfile, P.a = 0 ∧
    ∀ ω : ℝ, P.exponent ω = 1 * ScaleSpace.cin (1 * |ω|) := by
  obtain ⟨P, hPa, -, hP⟩ := cin_ray_scaled (one_pos : (0 : ℝ) < 1) (one_pos : (0 : ℝ) < 1)
  exact ⟨P, hPa, hP⟩

/-! ## The fresh-agent passes' coverage (Q-0376)

Three gaps the adversarial passes named (`blueprint/REVIEW-fidelity.md`, section "The fresh-agent
passes"): the subordinated slice of `thm:origin-boundedness-d`(3) with its delay law, case (2)(a)
of `thm:wedge-axis` (a cone not inside `PSD(d)`; its witness is in
`AffineHemigroup.WitnessesAffine`), and the line half of
`thm:no-cin-ray-in-the-plane` (the `Cin` ray *is* in `𝒜_1`). -/

/-! ### The subordinated slice: the Gamma delay law -/

/-- The causal Gamma datum `(0, γe^{-u})` has exponent `F_I(σ) = γ log(1 + σ)` (Frullani). -/
theorem gammaCausal_exponent {γ : ℝ} (hγ : 0 < γ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).exponent σ = γ * Real.log (1 + σ) := by
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * s))) *
      (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).k s / s) =
      ENNReal.ofReal γ * (ENNReal.ofReal (s ^ (-1 - (0 : ℝ)) * Real.exp (-s)) *
        ENNReal.ofReal (1 - Real.exp (-(s * σ)))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [ScaleSpace.CausalAdmissible.gammaCausalDatum_k hγ.le hs0,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ s ^ (-1 - (0 : ℝ)) * Real.exp (-s) by positivity),
      ← ENNReal.ofReal_mul hγ.le]
    congr 1
    rw [sub_zero, Real.rpow_neg_one, mul_comm s σ]
    field_simp
  rw [ScaleSpace.CausalAdmissible.exponent, ScaleSpace.CausalAdmissible.exponentL,
    ScaleSpace.CausalAdmissible.gammaCausalDatum_b₀, zero_mul, ENNReal.ofReal_zero, zero_add,
    setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_frullani_subordinator hσ, ← ENNReal.ofReal_mul hγ.le,
    ENNReal.toReal_ofReal (mul_nonneg hγ.le (Real.log_nonneg (by linarith)))]

/-- The Gamma law of shape `γ` and scale `1` is the delay law of the causal Gamma datum: its
Laplace transform is `(1 + σ)^{-γ} = e^{-F_I(σ)}`. -/
theorem gammaMeasure_laplace {γ : ℝ} (hγ : 0 < γ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ u, Real.exp (-(σ * u)) ∂(ProbabilityTheory.gammaMeasure γ 1) =
      Real.exp (-(ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).exponent σ) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_gammaMeasure hγ one_pos
  rw [gammaCausal_exponent hγ hσ, exp_neg_mul_log_one_add hσ,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le) (by fun_prop),
    lintegral_exp_gammaMeasure hγ hσ, ENNReal.toReal_ofReal (by positivity)]

theorem gammaMeasure_Iio {γ : ℝ} : ProbabilityTheory.gammaMeasure γ 1 (Iio 0) = 0 :=
  ScaleSpace.gammaMeasure_Iio_zero γ 1

/-- **The subordinated Gamma datum** in dimension `d`: the isotropic origin datum `(0, k_d)` whose
profile is the polar profile `eq:polar-profile-d` of the causal Gamma datum `(0, γe^{-u})`
(`lem:delay-polar-profile`, `polarProfileOf_antitone`). Its law is the law of `√V Z`, `V` Gamma of
shape `γ` and scale `1`, with transform `(1 + |ξ|²/2)^{-γ}`, a Matérn law. -/
noncomputable def gammaSubDatum (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) : OriginDatum d where
  a := 0
  k := polarProfileOf (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).k d
  a_nonneg := le_rfl
  k_nonneg := fun _ hr => polarProfileOf_nonneg (d := d)
    (causalDelayDatum (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le)) hr
  k_antitone := polarProfileOf_antitone hd _
  integrable_near_zero := (delay_polar_profile hd
    (causalDelayDatum (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le))).2.2.1
  integrable_at_top := (delay_polar_profile hd
    (causalDelayDatum (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le))).2.2.2.1

theorem gammaSubDatum_exponent (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (ξ : Rd d) :
    (gammaSubDatum hd γ hγ).exponent ξ =
      (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).exponent (‖ξ‖ ^ 2 / 2) := by
  rw [OriginDatum.exponent, OriginDatum.exponentL_eq_delay hd _
    (causalDelayDatum (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le)) rfl
    (fun _ _ => rfl) ξ,
    causalDelayDatum_exponentL]
  rfl

theorem gammaSubDatum_profileAtOrigin_pos (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    0 < (gammaSubDatum hd γ hγ).profileAtOrigin := by
  set FI := ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le
  have hint := (delay_polar_profile (d := d) hd (causalDelayDatum FI)).1 1 (mem_Ioi.2 one_pos)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < polarProfileOf FI.k d 1 := by
    refine mul_pos (div_pos two_pos (Real.Gamma_pos_of_pos (by positivity))) ?_
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hint).2 ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v (hv : 0 < v) => ?_)
      have := FI.k_nonneg (1 ^ 2 / (2 * v)) (show (0 : ℝ) < 1 ^ 2 / (2 * v) by positivity)
      change 0 ≤ v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * FI.k (1 ^ 2 / (2 * v))
      positivity
    · have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun v : ℝ => v ^ ((d : ℝ) / 2 - 1) *
          Real.exp (-v) * (causalDelayDatum FI).k (1 ^ 2 / (2 * v))) ∩ Ioi 0 := by
        intro v hv
        have hv0 : (0 : ℝ) < v := hv
        refine ⟨?_, hv⟩
        change v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * FI.k (1 ^ 2 / (2 * v)) ≠ 0
        rw [ScaleSpace.CausalAdmissible.gammaCausalDatum_k hγ.le (by positivity)]
        positivity
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [Real.volume_Ioi]
      exact ENNReal.zero_lt_top
  have hle : ENNReal.ofReal ((gammaSubDatum hd γ hγ).k 1) ≤
      (gammaSubDatum hd γ hγ).profileAtOrigin :=
    le_iSup (fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((gammaSubDatum hd γ hγ).k r))
      ⟨1, mem_Ioi.2 one_pos⟩
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) hle

/-- `k_I(0+) = γ` for the causal Gamma datum. -/
theorem gammaCausal_iSup {γ : ℝ} (hγ : 0 < γ) :
    ⨆ u : Ioi (0 : ℝ), ENNReal.ofReal ((ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).k u) =
      ENNReal.ofReal γ := by
  refine le_antisymm (iSup_le fun u => ENNReal.ofReal_le_ofReal ?_) ?_
  · rw [ScaleSpace.CausalAdmissible.gammaCausalDatum_k hγ.le u.2]
    have hu : (0 : ℝ) < u := u.2
    exact mul_le_of_le_one_right hγ.le (Real.exp_le_one_iff.2 (by linarith))
  · have hlim : Tendsto (fun u : ℝ => ENNReal.ofReal (γ * Real.exp (-u))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal γ)) := by
      have h : Tendsto (fun u : ℝ => γ * Real.exp (-u)) (𝓝[>] 0) (𝓝 (γ * Real.exp (-0))) :=
        ((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).tendsto
          (0 : ℝ)).mono_left nhdsWithin_le_nhds
      rw [neg_zero, Real.exp_zero, mul_one] at h
      exact ENNReal.tendsto_ofReal h
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← ScaleSpace.CausalAdmissible.gammaCausalDatum_k hγ.le hu]
    exact le_iSup (fun u : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).k u)) ⟨u, hu⟩

/-- **Witness, `thm:origin-boundedness-d`(3)** (`prop:origin-boundedness-subordinated`): every
hypothesis of the clause's four declarations holds at once at the subordinated Gamma datum — a
datum `(0, k_d)` with `c > 0` and a law, subordinated to the causally admissible `F_I(σ) =
γ log(1+σ)` with drift `0`, and a delay law `ρ` (Gamma, shape `γ`, scale `1`) on `[0,∞)` whose
Laplace transform is `e^{-F_I}`; the clause's first conclusion gives `c = 2γ`, so `γ > d/2` puts it
above the threshold and `γ ≤ d/2` at or below it. Lean core. -/
theorem witness_origin_subordinated (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (gammaSubDatum hd γ hγ).a = 0 ∧ 0 < (gammaSubDatum hd γ hγ).profileAtOrigin ∧
      IsLawOf (gammaSubDatum hd γ hγ) ((ProbabilityTheory.gammaMeasure γ 1).bind (gaussVar d)) ∧
      (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).b₀ = 0 ∧
      (∀ r ∈ Ioi (0 : ℝ), (gammaSubDatum hd γ hγ).k r =
        polarProfileOf (ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).k d r) ∧
      IsProbabilityMeasure (ProbabilityTheory.gammaMeasure γ 1) ∧
      ProbabilityTheory.gammaMeasure γ 1 (Iio 0) = 0 ∧
      (∀ σ : ℝ, 0 ≤ σ → ∫ u, Real.exp (-(σ * u)) ∂(ProbabilityTheory.gammaMeasure γ 1) =
        Real.exp (-(ScaleSpace.CausalAdmissible.gammaCausalDatum γ hγ.le).exponent σ)) ∧
      (gammaSubDatum hd γ hγ).profileAtOrigin = ENNReal.ofReal (2 * γ) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_gammaMeasure hγ one_pos
  have hc := gammaSubDatum_profileAtOrigin_pos hd hγ
  refine ⟨rfl, hc, ⟨isProbabilityMeasure_bind_gaussVar _, fun ξ => ?_⟩, rfl, fun _ _ => rfl,
    inferInstance, gammaMeasure_Iio, fun σ hσ => gammaMeasure_laplace hγ hσ, ?_⟩
  · rw [charFun_bind_gaussVar _ gammaMeasure_Iio, gammaSubDatum_exponent,
      ← gammaMeasure_laplace hγ (show (0 : ℝ) ≤ ‖ξ‖ ^ 2 / 2 by positivity)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    change Real.exp _ = Real.exp _
    congr 1
    ring
  · rw [subordinated_profileAtOrigin hd _ rfl hc _ rfl (fun _ _ => rfl), gammaCausal_iSup hγ,
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

/-! ### `thm:no-cin-ray-in-the-plane`: the line half -/

/-- **The `Cin` ray is in `𝒜_1`** (`thm:no-cin-ray-in-the-plane`, the remark that `d ≥ 2` is
essential; [B, Prop. 4.9(1)]): on the line, `ω ↦ b Cin(τ|ω|)` is the exponent of the
self-decomposable law of the datum `(0, b 1_{(0,τ)})`. So the theorem's exclusion is a fact about
the plane, not an unconditional one; the adversarial goal `cin_ray_not_in_A1` is its negation.
Spends A2, A3(i)–(iii) and A4 through `prop:isotropic-polar-classification`, as membership in a
class does. -/
theorem cin_ray_mem_classA_one {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    classA 1 (fun ω => b * ScaleSpace.cin (τ * |ω|)) := by
  obtain ⟨P, -, -, hP⟩ := cin_ray_scaled hτ hb
  refine (classA_iff_originDatum le_rfl _ fun r _ => ?_).2 ⟨cinDatum hτ hb, fun ξ => ?_⟩
  · rw [← hP r]; exact ENNReal.toReal_nonneg
  · rw [cinDatum_exponent, abs_of_nonneg (norm_nonneg ξ)]

/-! ## The limit of the critical values (`lem:threshold-asymptotic`, Q-0427) -/

/-- **Witness, `lem:threshold-asymptotic`(2)**: the hypotheses of the upper bound, `d ≥ 1` and
`ε_d < 1`, hold jointly at `d = 3`, the first integer dimension at which they do
(`ε_1 = 1.166`, `ε_2 = 1.058`, `ε_3 = 0.961`). So the upper bound is not vacuous at an integer
dimension. The other clauses have no hypothesis beyond `d ≥ 1`. Lean core. -/
theorem witness_threshold_asymptotic : (1 : ℝ) ≤ 3 ∧ thresholdEps 3 < 1 := by
  refine ⟨by norm_num, ?_⟩
  have h := Real.log_two_gt_d9
  norm_num at h
  have : Real.exp (1 / 4 + 3 * (1 / 4 - Real.log 2 / 2)) < Real.exp 0 :=
    Real.exp_lt_exp.2 (by linarith)
  rw [thresholdEps_eq_exp]
  exact this.trans_eq Real.exp_zero

/-! ## The exponent and the rate through the polar profile (Q-0427) -/

/-- **The step datum on the line**, `(0, 1_{(0,1)})`: profile at the origin `c = 1`, the profile
equal to `c` on `(0,1)` and `0` beyond. Its factor is `K ≡ 1` on `(0,1]`, `C_k = 0`, and its
exponent is `Cin(|ω|)` (`cinDatum_exponent`). -/
noncomputable def stepDatum : OriginDatum 1 := cinDatum one_pos one_pos

theorem stepDatum_k (r : ℝ) : stepDatum.k r = (Ioo (0 : ℝ) 1).indicator 1 r := by
  simp [stepDatum, cinDatum, ScaleSpace.cinProfile]

theorem stepDatum_profileAtOrigin : stepDatum.profileAtOrigin = 1 := by
  refine le_antisymm (iSup_le fun r => ?_) ?_
  · rw [stepDatum_k]
    refine ENNReal.ofReal_le_one.2 ?_
    by_cases h : (r : ℝ) ∈ Ioo (0 : ℝ) 1
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  · have h := stepDatum.ofReal_k_le (r := 1 / 2) (by norm_num)
    rw [stepDatum_k, indicator_of_mem (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1)] at h
    simpa using h

theorem stepDatum_toReal : stepDatum.profileAtOrigin.toReal = 1 := by
  rw [stepDatum_profileAtOrigin]; simp

/-- `(c - k(u))/u = 0` on `(0,1)` for the step datum. -/
theorem stepDatum_slowIntegrand {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (stepDatum.profileAtOrigin.toReal - stepDatum.k u) / u = 0 := by
  rw [stepDatum_toReal, stepDatum_k, indicator_of_mem hu]; simp

theorem stepDatum_slowFactor {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : stepDatum.slowFactor x = 1 := by
  have h0 : ∫ u in x..1, (stepDatum.profileAtOrigin.toReal - stepDatum.k u) / u = 0 := by
    rw [intervalIntegral.integral_of_le hx.2, integral_Ioc_eq_integral_Ioo]
    refine (setIntegral_congr_fun measurableSet_Ioo fun u hu =>
      stepDatum_slowIntegrand ⟨lt_trans hx.1 hu.1, hu.2⟩).trans ?_
    simp
  rw [OriginDatum.slowFactor, h0, Real.exp_zero]

theorem stepDatum_integrable : IntegrableOn
    (fun u => (stepDatum.profileAtOrigin.toReal - stepDatum.k u) / u) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact integrableOn_zero.congr_fun (fun u hu => (stepDatum_slowIntegrand hu).symm)
    measurableSet_Ioo

theorem stepDatum_tailConst : stepDatum.tailConst = 0 := by
  have h : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (stepDatum.k r / r) = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)
      fun r (hr : 1 < r) => ?_).trans lintegral_zero
    rw [stepDatum_k, indicator_of_notMem (fun h => absurd h.2 (not_lt.2 hr.le))]
    simp
  rw [OriginDatum.tailConst, h, ENNReal.toReal_zero]

theorem stepDatum_exponent {e : Rd 1} (he : ‖e‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    stepDatum.exponent (ρ • e) = ScaleSpace.cin ρ := by
  rw [stepDatum, cinDatum_exponent, one_mul, one_mul, norm_smul, he, mul_one,
    Real.norm_of_nonneg hρ]

/-- **Witness, `prop:isotropic-exponent-profile`**: its hypotheses hold jointly at the step datum
on the line: Gaussian coefficient `0`, a finite positive profile at the origin (`c = 1`), and a
unit vector; and the hypothesis of the convergent case holds there, with `K ≡ 1` on `(0,1]`.
Lean core. -/
theorem witness_exponent_profile :
    stepDatum.a = 0 ∧ stepDatum.profileAtOrigin ≠ ⊤ ∧ 0 < stepDatum.profileAtOrigin ∧
      (∀ x ∈ Ioc (0 : ℝ) 1, stepDatum.slowFactor x = 1) ∧
      IntegrableOn (fun u => (stepDatum.profileAtOrigin.toReal - stepDatum.k u) / u) (Ioc 0 1) ∧
      ∃ e : Rd 1, ‖e‖ = 1 := by
  refine ⟨rfl, ?_, ?_, fun x hx => stepDatum_slowFactor hx, stepDatum_integrable,
    ebasis (0 : Fin 1), by simp [ebasis]⟩
  · rw [stepDatum_profileAtOrigin]; exact ENNReal.one_ne_top
  · rw [stepDatum_profileAtOrigin]; exact one_pos

/-- **Witness, `prop:isotropic-exponent-profile`, every dimension**: its hypotheses hold jointly
at the Matérn datum of index `γ > 0` in every dimension `d ≥ 1` (`c = 2γ`, with no relation to
`d`), with a unit vector. The hypotheses of `prop:origin-rate-profile-d` are those of
`prop:origin-rate-d`, witnessed by `witness_origin_rate` and `witness_origin_rate_critical`.
Lean core. -/
theorem witness_exponent_profile_matern (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    (maternOriginDatum hd γ hγ).a = 0 ∧ (maternOriginDatum hd γ hγ).profileAtOrigin ≠ ⊤ ∧
      0 < (maternOriginDatum hd γ hγ).profileAtOrigin ∧ ∃ e : Rd d, ‖e‖ = 1 := by
  obtain ⟨ha, hc, hctop, -, -⟩ := witness_origin_boundedness hd hγ
  haveI : NeZero d := ⟨by omega⟩
  exact ⟨ha, hctop, hc, ebasis (0 : Fin d), by simp [ebasis]⟩

/-! ## The separating family, the shadow and the profile one dimension down (Q-0429) -/

/-- **Witness, `thm:separating-family-critical-values`(4)**: the hypotheses of the window, an
integer `d ≥ 1` and `w_{d+1} < w ≤ w_d`, hold jointly at `w = w_d`, for every `d ≥ 1`; those of
"exactly one interval", `0 < w ≤ w_1`, hold at `w = w_1`; and those of the case above, `w > w_1`,
at `w = w_1 + 1`. Clause (1) has no hypothesis beyond `D ≥ 1` and `w > 0`. Lean core. -/
theorem witness_separating_family (hd : 1 ≤ d) :
    (threshold ((d + 1 : ℕ) : ℝ) < threshold d ∧ threshold (d : ℝ) ≤ threshold d) ∧
      ((0 : ℝ) < threshold ((1 : ℕ) : ℝ) ∧ threshold ((1 : ℕ) : ℝ) ≤ threshold ((1 : ℕ) : ℝ)) ∧
      threshold ((1 : ℕ) : ℝ) < threshold ((1 : ℕ) : ℝ) + 1 :=
  ⟨⟨criticalValues_strictAnti.1 (mem_Ici.2 hd) (mem_Ici.2 (by omega)) (Nat.lt_succ_self d),
    le_rfl⟩, ⟨criticalValues_strictAnti.2 1 le_rfl, le_rfl⟩, lt_add_one _⟩

/-- The profile at the origin of the step datum `(0, b 1_{(0,τ)})` is `b`. -/
theorem stepOriginDatum_profileAtOrigin (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (stepOriginDatum d hτ hb).profileAtOrigin = ENNReal.ofReal b := by
  refine le_antisymm (iSup_le fun r => ENNReal.ofReal_le_ofReal ?_) ?_
  · rw [stepOriginDatum_k]
    by_cases h : (r : ℝ) ∈ Ioo (0 : ℝ) τ
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]; exact hb.le
  · have h := (stepOriginDatum d hτ hb).ofReal_k_le (r := τ / 2) (by positivity)
    rwa [stepOriginDatum_k, indicator_of_mem (show τ / 2 ∈ Ioo (0 : ℝ) τ from
      ⟨by positivity, by linarith⟩)] at h

/-- **Witness, `lem:shadow-polar-profile` and `prop:profile-one-dimension-down`(1)**: the
hypotheses hold jointly at a datum that is not trivial. For every `d` the step datum
`(0, b 1_{(0,τ)})` is an isotropic origin datum in dimension `d + 1`, with profile at the origin
`b > 0`, and its exponent is `ζ ↦ F(|ζ|)` for a function `F`. So the lemma's hypothesis (a datum
in dimension `d + 1`) and the first clause's (such a datum with a radial exponent `F(|·|)`) are
satisfied, and the shadow in question is not the zero datum. Lean core. -/
theorem witness_shadow_datum (d : ℕ) {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    ∃ (F : ℝ → ℝ) (D' : OriginDatum (d + 1)), (∀ ζ : Rd (d + 1), F ‖ζ‖ = D'.exponent ζ) ∧
      D'.profileAtOrigin = ENNReal.ofReal b ∧ 0 < D'.profileAtOrigin := by
  obtain ⟨G, hG⟩ := exists_radial_exponent (d := d + 1) (by omega) (stepOriginDatum (d + 1) hτ hb)
  refine ⟨G, stepOriginDatum (d + 1) hτ hb, hG, stepOriginDatum_profileAtOrigin _ hτ hb, ?_⟩
  rw [stepOriginDatum_profileAtOrigin]
  exact ENNReal.ofReal_pos.2 hb

/-- **Witness, `prop:profile-one-dimension-down`(1), the last sentence, at the `Cin` ray**: its
hypotheses hold jointly at the step datum on the line. The exponent of `(0, b 1_{(0,τ)})` in
dimension `1` is the radial function `b Cin(τ|·|)`, and its profile is not continuous on
`(0,∞)`: it falls from `b` to `0` at `τ`. Lean core. -/
theorem witness_profile_discontinuous {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    (∀ ξ : Rd 1, (fun ω : ℝ => b * ScaleSpace.cin (τ * |ω|)) ‖ξ‖ = (cinDatum hτ hb).exponent ξ) ∧
      ¬ ContinuousOn (cinDatum hτ hb).k (Ioi 0) :=
  ⟨fun ξ => by simp only [abs_norm]; rw [cinDatum_exponent],
    stepOriginDatum_not_continuousOn 1 hτ hb⟩

/-! ## `cor:isotropic-scale-zero-kernels` (Q-0434) -/

/-- **Witness, `cor:isotropic-scale-zero-kernels`**: the condition (S) is satisfiable. In every
dimension `d ≥ 1` the kernel from scale zero to scale `1` of the heat family, the standard
Gaussian law, is a probability measure that is rotation invariant, self-decomposable and not
`δ₀`: the hypotheses of clause (3). The residual at `c` is the stage `μ_{c,1}`, read off the
transforms; the corollary is not used. Lean core. -/
theorem witness_scale_zero_kernels (hd : 1 ≤ d) :
    ∃ _ : IsProbabilityMeasure (heatFamily d 0 1),
      IsRotationInvariant (heatFamily d 0 1) ∧
        ScaleSpace.IsSelfDecomposable (heatFamily d 0 1) ∧
        heatFamily d 0 1 ≠ Measure.dirac 0 := by
  obtain ⟨hprob, hfam, -, hF, -, hrep⟩ := witness_isotropic_classification (d := d) hd
  haveI := hprob 0 1 le_rfl zero_le_one
  refine ⟨inferInstance, fun Q hQ => hfam.rotation Q hQ 0 1 le_rfl zero_le_one, ?_,
    hfam.nondegenerate 0 1 le_rfl one_pos⟩
  rw [ScaleSpace.isSelfDecomposable_iff_charFun]
  intro c hc0 hc1
  haveI := hprob c 1 hc0.le hc1.le
  refine ⟨heatFamily d c 1, inferInstance, fun ξ => ?_⟩
  rw [hrep 0 1 le_rfl zero_le_one, hrep 0 1 le_rfl zero_le_one, hrep c 1 hc0.le hc1.le,
    ← Complex.ofReal_mul, ← Real.exp_add]
  simp only [id, zero_mul, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, classA_zero hF,
    sub_zero]
  congr 2
  ring

/-! ## The stages of a cascade: `lem:isotropic-stage-levy-measure`, `prop:isotropic-stage-atom`,
`prop:isotropic-stage-density` (Q-0447) -/

/-- **Witness, `lem:isotropic-stage-levy-measure` (last sentence), `prop:isotropic-stage-atom` and
`prop:isotropic-stage-density`(1)**: the hypotheses are satisfiable. For every index `γ > 0` the
Matérn origin datum, with the gauge `id` and `F(r) = γ log(1 + r²)`, has `a = 0`, a finite profile
at the origin and `F ≢ 0`, and there is a family of probability measures with the display. The
family is that of `lem:isotropic-realisation`, which asks `F ∈ 𝒜_d`; the witness prints A2, A3
and A4 for that, and the nodes it is a witness of do not. -/
theorem witness_isotropic_stage_atom (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (D : OriginDatum d) (F χ : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d)),
      D.a = 0 ∧ D.profileAtOrigin ≠ ⊤ ∧ IsGauge χ ∧ (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) ∧
      (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  have hD : ∀ ξ : Rd d, (fun r : ℝ => γ * Real.log (1 + r ^ 2)) ‖ξ‖
      = (maternOriginDatum hd γ hγ).exponent ξ := fun ξ =>
    (maternOriginDatum_exponent hd hγ ξ).symm
  have hFnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ (fun r : ℝ => γ * Real.log (1 + r ^ 2)) r := fun r _ =>
    mul_nonneg hγ.le (Real.log_nonneg (by nlinarith [sq_nonneg r]))
  have hFne : ∃ r : ℝ, 0 ≤ r ∧ (fun r : ℝ => γ * Real.log (1 + r ^ 2)) r ≠ 0 := by
    have h2 : (1 : ℝ) < 1 + 1 ^ 2 := by norm_num
    exact ⟨1, zero_le_one, (mul_pos hγ (Real.log_pos h2)).ne'⟩
  have hA : classA d (fun r : ℝ => γ * Real.log (1 + r ^ 2)) :=
    (classA_iff_originDatum hd _ hFnn).mpr ⟨_, hD⟩
  obtain ⟨μ, hprob, -, hrep⟩ := isotropic_realisation hd id _ isGauge_id hA hFne
  refine ⟨maternOriginDatum hd γ hγ, _, id, μ, rfl, ?_, isGauge_id, hD, hFne, hprob, hrep⟩
  rw [maternOriginDatum_profileAtOrigin]
  exact ENNReal.ofReal_ne_top

/-- **The heat datum** `(1, 0)`: a Gaussian part and no jumps. -/
noncomputable def heatDatum (d : ℕ) : OriginDatum d where
  a := 1
  k := fun _ => 0
  a_nonneg := zero_le_one
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

theorem heatDatum_exponent (ξ : Rd d) : (heatDatum d).exponent ξ = ‖ξ‖ ^ 2 / 2 := by
  have h : 0 ≤ ‖ξ‖ ^ 2 / 2 := by positivity
  simp [OriginDatum.exponent, OriginDatum.exponentL, OriginDatum.levyMeasure, heatDatum, h]

/-- **Witness, `prop:isotropic-stage-density`(3)**: the hypotheses are satisfiable, at the heat
family with the gauge `id`, whose datum `(1, 0)` has a Gaussian part. Lean core. -/
theorem witness_isotropic_stage_smooth (hd : 1 ≤ d) :
    ∃ (D : OriginDatum d) (F χ : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d)),
      0 < D.a ∧ IsGauge χ ∧ (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) ∧
      (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  obtain ⟨hprob, -, hχ, -, hFne, hrep⟩ := witness_isotropic_classification (d := d) hd
  refine ⟨heatDatum d, heatF, id, heatFamily d, zero_lt_one, hχ, fun ξ => ?_, hFne, hprob, hrep⟩
  rw [heatDatum_exponent, heatF, heatCausal_exponent (by positivity)]

/-- **A datum with no Gaussian part and an infinite profile at the origin**: `k(r) = 1/r` on
`(0,1)` and `0` beyond. -/
noncomputable def steepDatum (d : ℕ) : OriginDatum d where
  a := 0
  k := fun r => if r < 1 then r⁻¹ else 0
  a_nonneg := le_rfl
  k_nonneg := fun r hr => by
    by_cases h : r < 1
    · simp only [h, if_true]; exact (inv_pos.mpr hr).le
    · simp only [h, if_false, le_refl]
  k_antitone := fun r hr s hs hrs => by
    by_cases h : s < 1
    · have hr1 : r < 1 := lt_of_le_of_lt hrs h
      simp only [h, hr1, if_true]
      exact inv_anti₀ hr hrs
    · simp only [h, if_false]
      by_cases hr1 : r < 1
      · simp only [hr1, if_true]; exact (inv_pos.mpr hr).le
      · simp only [hr1, if_false, le_refl]
  integrable_near_zero := by
    have h : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal ((if r < 1 then r⁻¹ else 0) * r) = 1 :=
      fun r hr => by simp [hr.2, inv_mul_cancel₀ hr.1.ne']
    rw [setLIntegral_congr_fun measurableSet_Ioo h]
    simp
  integrable_at_top := by
    have h : ∀ r ∈ Ioi (1 : ℝ), ENNReal.ofReal ((if r < 1 then r⁻¹ else 0) / r) = 0 :=
      fun r (hr : 1 < r) => by simp [not_lt.mpr hr.le]
    rw [setLIntegral_congr_fun measurableSet_Ioi h]
    simp

theorem steepDatum_profileAtOrigin : (steepDatum d).profileAtOrigin = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun q => ?_
  have hq : (0 : ℝ) < (q : ℝ) + 2 := by positivity
  have hr : (0 : ℝ) < ((q : ℝ) + 2)⁻¹ := inv_pos.mpr hq
  have hr1 : ((q : ℝ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [NNReal.coe_nonneg q])
  refine le_trans ?_ ((steepDatum d).ofReal_k_le hr)
  have hk : (steepDatum d).k ((q : ℝ) + 2)⁻¹ = (q : ℝ) + 2 := by
    simp [steepDatum, hr1]
  rw [hk, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Witness, `prop:isotropic-stage-density`(2)**: the hypotheses are satisfiable. The datum
`steepDatum` has `a = 0` and `c = ∞`; its exponent is not identically `0`
(`OriginDatum.exponent_ge_log`); and there is a family of probability measures with its display at
the gauge `id`, that of `lem:isotropic-realisation`, for which the witness prints A2, A3, A4. -/
theorem witness_isotropic_stage_absolutelyContinuous (hd : 1 ≤ d) :
    ∃ (D : OriginDatum d) (F χ : ℝ → ℝ) (μ : ℝ → ℝ → Measure (Rd d)),
      D.a = 0 ∧ D.profileAtOrigin = ⊤ ∧ IsGauge χ ∧ (∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ) ∧
      (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) := by
  haveI : NeZero d := ⟨by omega⟩
  have he : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hD : ∀ ξ : Rd d, (fun r : ℝ => (steepDatum d).exponent (r • ebasis (0 : Fin d))) ‖ξ‖
      = (steepDatum d).exponent ξ := fun ξ =>
    (steepDatum d).exponent_eq_of_norm_eq (by rw [norm_smul, he, mul_one, norm_norm])
  have hFnn : ∀ r : ℝ, 0 ≤ r →
      0 ≤ (fun r : ℝ => (steepDatum d).exponent (r • ebasis (0 : Fin d))) r :=
    fun r _ => (steepDatum d).exponent_nonneg _
  have hFne : ∃ r : ℝ, 0 ≤ r ∧
      (fun r : ℝ => (steepDatum d).exponent (r • ebasis (0 : Fin d))) r ≠ 0 := by
    obtain ⟨K, hK⟩ := (steepDatum d).exponent_ge_log hd rfl (β := 1) zero_le_one
      (by rw [steepDatum_profileAtOrigin]; exact ENNReal.ofReal_lt_top)
    have hr : 1 ≤ Real.exp (|K| + 1) := Real.one_le_exp (by positivity)
    have hn : ‖Real.exp (|K| + 1) • (ebasis (0 : Fin d) : Rd d)‖ = Real.exp (|K| + 1) := by
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h := hK (Real.exp (|K| + 1) • ebasis (0 : Fin d)) (by rw [hn]; exact hr)
    rw [hn, Real.log_exp] at h
    refine ⟨Real.exp (|K| + 1), (Real.exp_pos _).le, ?_⟩
    have : (0 : ℝ) < (steepDatum d).exponent (Real.exp (|K| + 1) • ebasis (0 : Fin d)) := by
      linarith [le_abs_self K]
    exact this.ne'
  have hA : classA d (fun r : ℝ => (steepDatum d).exponent (r • ebasis (0 : Fin d))) :=
    (classA_iff_originDatum hd _ hFnn).mpr ⟨_, hD⟩
  obtain ⟨μ, hprob, -, hrep⟩ := isotropic_realisation hd id _ isGauge_id hA hFne
  exact ⟨steepDatum d, _, id, μ, rfl, steepDatum_profileAtOrigin, isGauge_id, hD, hFne, hprob,
    hrep⟩

end AffineHemigroup
