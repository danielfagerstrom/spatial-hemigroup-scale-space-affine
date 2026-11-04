/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.WitnessesAffine
import AffineHemigroup.Probes
import AffineHemigroup.WedgeAxisCell

/-!
# Positive probes of the affine paper: a should-hold consequence of each headline declaration

The boundary harness's second check (article-kit `docs/LINKAGE.md` rule 5, `linkage boundary`;
`linkage.toml` `[boundary]`) for the headline declarations of chapters 4 and 5. Each probe
**uses** one headline declaration and keeps one clause of it, read at a model of
`WitnessesAffine.lean` where that makes it concrete. A headline statement weakened into something
that still type-checks stops one of these from building. The file is part of the library (CI
builds it, the `sorry` guard covers it) and nothing imports it.

The declarations stood in `AffineHemigroup.Probes` until Q-0452, which left there the probes of
the isotropic paper (chapter 3); they are here unchanged.
-/

namespace AffineHemigroup

/-! ## The headline theorems of chapters 4 and 5 -/

section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- `thm:affine-rigidity`: the kernel `μ_I` of every affine cascade family in dimension `d ≥ 2` is
an affine Gaussian kernel. A rigidity weakened to "some family is Gaussian" stops this. -/
theorem probe_affine_rigidity (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsAffineCascadeFamily μ) : ∃ b : ℝ, 0 < b ∧ μ 0 1 = affineGaussian b 0 1 := by
  obtain ⟨b, hb, heq⟩ := (affine_rigidity hd μ).1 hμ
  exact ⟨b, hb, heq _ (wedge_zero_one_mem
    (isWedgeDatum_loewner glSet_isClosedSubgroupGL.1 glSet_isClosedSubgroupGL.2))⟩

/-- `thm:affine-rigidity-operators`, the uniqueness of `b`: the convolution families of two affine
Gaussian scale spaces with different constants are different operator families. -/
theorem probe_affine_rigidity_operators (hd : 2 ≤ d) {b b' : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hne : b ≠ b') :
    ¬ ∀ p ∈ wedgePairs (loewnerLE (d := d)),
      ScaleSpace.mconvL1E (affineGaussian b p.1 p.2) =
        ScaleSpace.mconvL1E (affineGaussian b' p.1 p.2) := by
  intro h
  exact hne ((affine_rigidity_operators hd
    (fun S S' => ScaleSpace.mconvL1E (affineGaussian b S S'))).2 b b' hb hb'
    (fun _ _ => rfl) h)

/-- `thm:rank-deficient-step`: at `g = id`, `Σ = I`, `P = e₁e₁ᵀ`, the increment is forced to be the
centred Gaussian of covariance `2P`. -/
theorem probe_rank_deficient_step (hd : 2 ≤ d) (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (h : ∀ ω : Rd d, ((Real.exp (-id (quad (1 + stepE1 (d := d) (by omega)) ω)) : ℝ) : ℂ) =
      ((Real.exp (-id (quad 1 ω)) : ℝ) : ℂ) * charFun ρ ω) :
    ρ = ProbabilityTheory.multivariateGaussian 0 ((2 * id (1 : ℝ)) • stepE1 (d := d) (by omega)) :=
  (rank_deficient_step hd id (fun u hu => hu) continuousWithinAt_id rfl 1 _ PosDef.one
    (stepE1_posSemidef _) (by rw [stepE1_rank]; exact one_pos)
    (by rw [stepE1_rank]; omega) ρ h).2.2

/-- `thm:cascade-infinitely-divisible`(2): the kernel from the origin at `I` of the affine Gaussian
family is infinitely divisible. -/
theorem probe_cascade_infinitely_divisible (hd : 2 ≤ d) :
    IsInfinitelyDivisible (affineGaussian (d := d) 1 0 1) := by
  obtain ⟨hfam, -, hW, hP, -, -⟩ := witness_affine_rigidity (d := d) hd
  exact (gw_family_infinitelyDivisible (by omega) hW hP _ hfam).2 1 PosSemidef.one

/-- `thm:wedge-axis`(2)(c): a non-Gaussian `(GL(d), ≼⁺_C)`-cascade family forces `β(C) < 2`. -/
theorem probe_wedge_axis_non_gaussian (hd : 2 ≤ d) {C : Set (Mat d)} (hCsym : C ⊆ symSet d)
    (hC : IsClosedConvexCone C) (hO : IsOrthInvariant C) (hI : (1 : Mat d) ∈ C)
    (hpt : ∀ X ∈ C, -X ∈ C → X = 0) (hpsd : C ⊆ psdSet d)
    (hdef : ∀ X ∈ C, X ≠ 0 → X.det ≠ 0) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (glSet d) (causalPlusLE C) μ)
    (hng : ¬ ProbabilityTheory.IsGaussian (μ 0 1)) : coneIndex C < 2 :=
  (wedge_axis_non_gaussian hd hCsym hC hO hI hpt hpsd hdef).1.1 ⟨μ, hμ, hng⟩

/-- `thm:wedge-axis`(3): the row shrinks along the chain, `𝔉_∞ ⊆ 𝔉_0`. -/
theorem probe_wedge_axis_row (hd : 2 ≤ d) : rowLaws d ⊤ ⊆ rowLaws d 0 :=
  (wedge_axis_row hd).2.1 0 ⊤ le_rfl le_top

/-- `thm:cone-orders`(1), at `C = PSD(d)`: the causal order is the step order of `exp C`. -/
theorem probe_cone_orders (hd : 1 ≤ d) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef →
      (causalLE (psdSet d) S S' ↔ stepLE (expSet (psdSet d)) S S') := by
  obtain ⟨⟨h1, h2, h3, -, -⟩, -⟩ := witness_cone_orders (d := d) hd
  exact (causalLE_order hd h1 h2 h3).1

/-- `prop:shape-adapted-apertures`(3), at the Loewner order and the affine Gaussian family: the
family's increments are Gaussian with a positive constant. -/
theorem probe_shape_adapted (hd : 2 ≤ d) :
    ∃ b : ℝ, 0 < b ∧ ∀ p ∈ wedgePairs (loewnerLE (d := d)), ∀ ω : Rd d,
      charFun (affineGaussian (d := d) 1 p.1 p.2) ω =
        ((Real.exp (-(b * quad (p.2 - p.1) ω)) : ℝ) : ℂ) := by
  obtain ⟨hM, hM1, hMI, -, hW, hstep, hfam⟩ := witness_shape_adapted (d := d) hd
  exact shape_adapted_scheme hd hW one_pos hM hM1 hMI (by simpa using hstep) _ hfam

end

/-! ## The fresh-agent passes' coverage (Q-0376) -/

section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- `thm:wedge-axis`(2)(a), at the cone `{λ_min(X) + tr X ≥ 0}` (`witness_wedge_axis_nonpsd`): no
`(GL(d), ≼⁺_C)`-cascade family exists. -/
theorem probe_wedge_axis_nonpsd (hd : 2 ≤ d) :
    ¬ ∃ μ : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (glSet d) (causalPlusLE (nonpsdCone d)) μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := witness_wedge_axis_nonpsd (d := d) hd
  exact wedge_axis_not_psd hd h1 h2 h3 h4 h5 h6

/-- `thm:cascade-infinitely-divisible`(2), at a **non-Gaussian** family: along `≼⁺_{C_α}`,
`0 ≤ α < 2`, there is a `(GL(d), ≼⁺_{C_α})`-cascade family whose kernel `μ_I` is not Gaussian
(`thm:wedge-axis`(2)(c), A3 and A5), and every increment of it on every pair, and every kernel from
the origin, is infinitely divisible (A6; the wedge datum and its path condition are
`causalPlus_wedge`, A9). A theorem true only of the Gaussian, or weakened to the kernels from the
origin, stops this. -/
theorem probe_cascade_infinitely_divisible_non_gaussian (hd : 2 ≤ d) {α : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α < 2) :
    ∃ μ : Mat d → Mat d → Measure (Rd d),
      IsGWCascadeFamily (glSet d) (causalPlusLE (stableGenCone d α)) μ ∧
        ¬ ProbabilityTheory.IsGaussian (μ 0 1) ∧
        (∀ p ∈ wedgePairs (causalPlusLE (stableGenCone d α)), IsInfinitelyDivisible (μ p.1 p.2)) ∧
        ∀ S : Mat d, S.PosSemidef → IsInfinitelyDivisible (μ 0 S) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, hpsd, hdef⟩, -⟩ := witness_wedge_axis (d := d) hd hα0
  obtain ⟨μ, hμ, hng⟩ := (wedge_axis_non_gaussian hd h1 h2 h3 h4 h5 hpsd hdef).1.2
    (by rw [coneIndex_stableGenCone hd hα0]; exact hα2)
  obtain ⟨hW, hP, -⟩ := causalPlus_wedge (by omega) h1 h2 h3 h4 h5
  exact ⟨μ, hμ, hng, gw_family_infinitelyDivisible (by omega) hW hP μ hμ⟩

/-- `thm:cascade-infinitely-divisible`(2), the increments: every increment of the affine Gaussian
family on a Loewner pair is infinitely divisible (the all-pairs clause, which
`probe_cascade_infinitely_divisible` does not read). -/
theorem probe_cascade_infinitely_divisible_pairs (hd : 2 ≤ d) :
    ∀ p ∈ wedgePairs (loewnerLE (d := d)),
      IsInfinitelyDivisible (affineGaussian (d := d) 1 p.1 p.2) := by
  obtain ⟨hfam, -, hW, hP, -, -⟩ := witness_affine_rigidity (d := d) hd
  exact (gw_family_infinitelyDivisible (by omega) hW hP _ hfam).1

/-- `thm:cone-orders`(1), closedness, at `C = PSD(d)`: a limit in `PD(d)` of pairs in the order is
in the order. -/
theorem probe_cone_orders_closed (hd : 1 ≤ d) {S S' : Mat d} (hS : S.PosDef) (hS' : S'.PosDef)
    {Sn : ℕ → Mat d} (hlim : Tendsto Sn atTop (𝓝 S'))
    (hle : ∀ n, stepLE (expSet (psdSet d)) S (Sn n)) : stepLE (expSet (psdSet d)) S S' := by
  obtain ⟨⟨h1, h2, h3, -, -⟩, -⟩ := witness_cone_orders (d := d) hd
  have hmem : (S, S') ∈ closure {p : Mat d × Mat d | stepLE (expSet (psdSet d)) p.1 p.2} :=
    mem_closure_of_tendsto (tendsto_const_nhds.prodMk_nhds hlim) (Eventually.of_forall hle)
  exact (causalLE_order hd h1 h2 h3).2.1 ⟨hmem, hS, hS'⟩

/-- `thm:cone-orders`(1), `GL(d)`-invariance, at `C = PSD(d)`. -/
theorem probe_cone_orders_invariant (hd : 1 ≤ d) {B : Mat d} (hB : B ∈ glSet d) {S S' : Mat d}
    (hS : S.PosDef) (hS' : S'.PosDef) (h : stepLE (expSet (psdSet d)) S S') :
    stepLE (expSet (psdSet d)) (act B S) (act B S') := by
  obtain ⟨⟨h1, h2, h3, -, -⟩, -⟩ := witness_cone_orders (d := d) hd
  exact ((causalLE_order hd h1 h2 h3).2.2.1 B hB S S' hS hS').1 h

/-- `thm:cone-orders`(1), the partial order, at the pointed cone `C = PSD(d)`: the order is
antisymmetric. -/
theorem probe_cone_orders_antisymm (hd : 1 ≤ d) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → stepLE (expSet (psdSet d)) S S' →
      stepLE (expSet (psdSet d)) S' S → S = S' := by
  obtain ⟨⟨h1, h2, h3, -, h5⟩, -⟩ := witness_cone_orders (d := d) hd
  exact (causalLE_order hd h1 h2 h3).2.2.2.2.2.1.2 h5

/-- `thm:cone-orders`(1), `C(exp C) = C`, at `C = PSD(d)`. -/
theorem probe_cone_orders_infCone (hd : 1 ≤ d) : infCone (expSet (psdSet d)) = psdSet d := by
  obtain ⟨⟨h1, h2, h3, -, -⟩, -⟩ := witness_cone_orders (d := d) hd
  exact (causalLE_order hd h1 h2 h3).2.2.2.2.2.2

end

/-! ## Siblings: the other conjuncts the first probes did not read -/

section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology MatrixOrder

variable {d : ℕ}

/-- `thm:wedge-axis`(3), the first and last sentences: `𝔉_0` consists of self-decomposable laws
other than `δ₀`, and `𝔉_2 ⊊ 𝔉_0`. -/
theorem probe_wedge_axis_row_strict (hd : 2 ≤ d) :
    (∀ m ∈ rowLaws d 0, ScaleSpace.IsSelfDecomposable m ∧ m ≠ Measure.dirac 0) ∧
      rowLaws d ((2 : ℝ) : WithTop ℝ) ⊂ rowLaws d 0 := by
  refine ⟨fun m hm => ?_, (wedge_axis_row hd).2.2 0 ((2 : ℝ) : WithTop ℝ) le_rfl
    (by exact_mod_cast (two_pos : (0 : ℝ) < 2)) le_rfl⟩
  rw [(wedge_axis_row hd).1] at hm
  exact ⟨hm.2.2.1, hm.2.2.2⟩

/-- `thm:wedge-axis`(2)(c), its last sentence, at `C_2`: every `(GL(d), ≼⁺_{C_2})`-cascade family
is an affine Gaussian scale space. -/
theorem probe_wedge_axis_gaussian (hd : 2 ≤ d) (μ : Mat d → Mat d → Measure (Rd d))
    (hμ : IsGWCascadeFamily (glSet d) (causalPlusLE (stableGenCone d 2)) μ) :
    ∃ b : ℝ, 0 < b ∧ EqOnPairs (causalPlusLE (stableGenCone d 2)) μ (affineGaussian b) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, hpsd, hdef⟩, -⟩ := witness_wedge_axis (d := d) hd zero_le_two
  exact ((wedge_axis_non_gaussian hd h1 h2 h3 h4 h5 hpsd hdef).2
    (coneIndex_stableGenCone hd zero_le_two).symm.le μ).1 hμ

/-- `prop:wedge-axis-profiles`(1) at `C_1`, for every profile, right-continuous or not: a Gaussian
part changes nothing, and the law is in `𝔉(C_1)` exactly when `β₋(k) ≥ 1`. A statement weakened to
one direction, or back to right-continuous profiles, stops this. -/
theorem probe_wedge_axis_profiles (hd : 2 ≤ d) (K : RadialProfile d) (ν : Measure (Rd d))
    (hν : IsProfileLaw K ν) {a : ℝ} (ha : 0 ≤ a) :
    ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈ coneLaws (stableGenCone d 1) ↔
      1 ≤ lowerExp K.k := by
  obtain ⟨⟨h1, h2, h3, h4, h5, hpsd, hdef⟩, -⟩ := witness_wedge_axis (d := d) hd zero_le_one
  have hidx := coneIndex_stableGenCone (d := d) hd zero_le_one
  rw [wedge_axis_profiles hd h1 h2 h3 h4 h5 hpsd hdef (by rw [hidx]; exact one_pos) K ν hν ha, hidx]

/-- `prop:wedge-axis-profiles`(2) at `α = 1`: `N(0, I)` lies in `𝔉_1`, and every member is a
Gaussian or is a Gaussian convolved with the law of a profile with `β₋(k) ≥ 1`. A cell that lost a
side of its description stops this. -/
theorem probe_wedge_axis_cell (hd : 2 ≤ d) :
    ProbabilityTheory.multivariateGaussian 0 ((1 : ℝ) • (1 : Mat d)) ∈
        rowLaws d ((1 : ℝ) : WithTop ℝ) ∧
      ∀ m ∈ rowLaws d ((1 : ℝ) : WithTop ℝ),
        (∃ a : ℝ, 0 < a ∧ m = ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d))) ∨
          ∃ a : ℝ, 0 ≤ a ∧ ∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
            1 ≤ lowerExp K.k ∧
              m = ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν := by
  rw [wedge_axis_cell hd one_pos]
  refine ⟨Or.inl ⟨1, one_pos, rfl⟩, fun m hm => ?_⟩
  rcases hm with h | ⟨a, ha, K, ν, hν, -, hle, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, K, ν, hν, hle, hm⟩

/-- `prop:wedge-axis-profiles`(2) past the stable orders: `𝔉_3` has `N(0, I)`, and at `α = 2` itself
no law of a profile, with any Gaussian part, is a member, read from clause (1) at `C_2`. A cell
whose Gaussian end was empty or still held a profile stops this. -/
theorem probe_wedge_axis_cell_gaussian (hd : 2 ≤ d) :
    ProbabilityTheory.multivariateGaussian 0 ((1 : ℝ) • (1 : Mat d)) ∈
        rowLaws d ((3 : ℝ) : WithTop ℝ) ∧
      ∀ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν → ∀ {a : ℝ}, 0 ≤ a →
        ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∉
          rowLaws d ((2 : ℝ) : WithTop ℝ) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨?_, fun K ν hν a ha hm => ?_⟩
  · rw [wedge_axis_cell_gaussian hd (by norm_num : (2 : ℝ) ≤ 3)]
    exact ⟨1, one_pos, rfl⟩
  · obtain ⟨⟨h1, h2, h3, h4, h5, hpsd, hdef⟩, -⟩ := witness_wedge_axis (d := d) hd zero_le_two
    have hidx := coneIndex_stableGenCone (d := d) hd zero_le_two
    rw [rowLaws_coe_eq_coneLaws,
      wedge_axis_profiles hd h1 h2 h3 h4 h5 hpsd hdef (by rw [hidx]; exact two_pos) K ν hν ha,
      hidx] at hm
    exact absurd hm (not_le.2 (dilRatio_exponents hd1 K).2.2.2.2.2.1)

/-- `prop:wedge-axis-profiles`(1) discriminates: at `α = 1`, with any Gaussian part, the law of
`k(r) = r^(-3/2)` is in `𝔉_1` and that of `k(r) = r^(-1/2)` is not. A description true of every law,
or of no law, stops this. (The blind referee's example, 2026-11-04.) -/
theorem probe_wedge_axis_profiles_discriminate (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    (∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
      ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∈
        rowLaws d ((1 : ℝ) : WithTop ℝ)) ∧
    (∃ (K : RadialProfile d) (ν : Measure (Rd d)), IsProfileLaw K ν ∧
      ProbabilityTheory.multivariateGaussian 0 (a • (1 : Mat d)) ∗ ν ∉
        rowLaws d ((1 : ℝ) : WithTop ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hprofile : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ K : RadialProfile d, lowerExp K.k = γ := by
    intro γ h0 h2
    have hj : IsTemperingProfile (fun _ : ℝ => (1 : ℝ)) :=
      ⟨fun _ _ => zero_le_one, fun _ _ _ _ _ => le_rfl, 1, one_pos, tendsto_const_nhds⟩
    obtain ⟨K, hK⟩ := tempered_profile_exists (d := d) hd1 h0 h2 _ hj
    refine ⟨K, (dilRatio_exponents_stable hd1 K 1 γ one_pos h0 h2 fun r hr => ?_).1⟩
    rw [hK r hr, mul_one, one_mul]
  have key := fun (K : RadialProfile d) (ν : Measure (Rd d)) (hν : IsProfileLaw K ν) =>
    (wedge_axis_profiles_stable hd one_pos one_lt_two K ν hν ha).1
  constructor
  · obtain ⟨K, hK⟩ := hprofile (3 / 2) (by norm_num) (by norm_num)
    obtain ⟨ν, hν, -⟩ := exists_profileLaw hd1 K
    refine ⟨K, ν, hν, (key K ν hν).2 ?_⟩
    exact ((dilRatio_exponents hd1 K).2.2.2.2.2.2.2 1 zero_le_one).2 (by rw [hK]; norm_num)
  · obtain ⟨K, hK⟩ := hprofile (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨ν, hν, -⟩ := exists_profileLaw hd1 K
    refine ⟨K, ν, hν, fun hm => ?_⟩
    have h := ((dilRatio_exponents hd1 K).2.2.2.2.2.2.2 1 zero_le_one).1 ((key K ν hν).1 hm)
    rw [hK] at h
    norm_num at h

/-- `thm:rank-deficient-step`, the linearity: a step along `P = e₁e₁ᵀ` forces `g(u) = g(1)u`. -/
theorem probe_rank_deficient_step_linear (hd : 2 ≤ d) (g : ℝ → ℝ)
    (hg0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (hgc : ContinuousWithinAt g (Ici 0) 0) (hgz : g 0 = 0)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (h : ∀ ω : Rd d, ((Real.exp (-g (quad (1 + stepE1 (d := d) (by omega)) ω)) : ℝ) : ℂ) =
      ((Real.exp (-g (quad 1 ω)) : ℝ) : ℂ) * charFun ρ ω) :
    ∀ u : ℝ, 0 ≤ u → g u = g 1 * u :=
  (rank_deficient_step hd g hg0 hgc hgz 1 _ PosDef.one (stepE1_posSemidef _)
    (by rw [stepE1_rank]; exact one_pos) (by rw [stepE1_rank]; omega) ρ h).1

end

end AffineHemigroup
