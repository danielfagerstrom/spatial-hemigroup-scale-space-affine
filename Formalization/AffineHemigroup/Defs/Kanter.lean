/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# The vocabulary of ledger A8: Kanter's uniform laws

Blueprint: `prop:isotropic-radial-monotone` (`blueprint/src/parts/03-isotropic.tex`); ledger entry
A8, `blueprint/AXIOMS.md`, transcribed in `blueprint/AXIOMS-verbatim.md` § A8 (Kanter,
Definitions 1.1, 1.2 and 3.1, pp. 66 and 70). Admitted by the author on 2026-10-05, after the
librarian's independent audit of the transcription.

**Kanter's `λ_K`** (Definition 1.2): for a compact convex `K ⊆ ℝ^N`,
`λ_K(A) = Vol_L(A ∩ K)/Vol_L(K)`, `L` the affine span of `K` and `Vol_L` the Lebesgue measure of
its dimension (Definition 1.1). The ledger writes `u_K`. Here `K` is symmetric and nonempty, so
`0 = ½x + ½(-x) ∈ K` for any `x ∈ K`, and the affine span is the linear span
`V = Submodule.span ℝ K`. `Vol_V` is the `volume` of the inner product space `V`, the Lebesgue
measure normalised by its orthonormal bases, which gives the unit ball the volume
`π^{k/2}/Γ(1 + k/2)` that Definition 1.1 asks for (the normalisation cancels in the quotient in any
case). The quotient is Mathlib's conditional measure `Vol_V[|K]`, pushed into `ℝ^d` by the
inclusion `V → ℝ^d`.

**Kanter presupposes `K` nonempty** (the audit, (a)): for `K = ∅` the quotient is `0/0`. So
`IsKanterUniform` asks for `K.Nonempty`. At dimension `0`, `K = {0}` and `V = {0}`, whose volume
is the unit mass, so `kanterUniform {0} = δ₀` (`kanterUniform_zero`), as Definition 1.1 read at
`k = 0` gives.
-/

namespace AffineHemigroup

open MeasureTheory Set ProbabilityTheory

variable {d : ℕ}

/-- **Kanter's uniform law `λ_K`** (ledger A8's `u_K`; Kanter Def. 1.2, p. 66): the volume of the
linear span `V` of `K`, conditioned on `K`, pushed into `ℝ^d`. Read for a nonempty compact convex
symmetric `K`, whose affine span is `V`. -/
noncomputable def kanterUniform (K : Set (Rd d)) : Measure (Rd d) :=
  ((volume : Measure (Submodule.span ℝ K))[|Subtype.val ⁻¹' K]).map Subtype.val

/-- **`ν ∈ W_d`** (ledger A8; Kanter Def. 3.1, p. 70, with Wolfe's p. 144): `ν` is the uniform law
`λ_K` of a nonempty compact convex symmetric `K ⊆ ℝ^d`. -/
def IsKanterUniform (ν : Measure (Rd d)) : Prop :=
  ∃ K : Set (Rd d), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧
    ν = kanterUniform K

/-- **At dimension `0`, `λ_{{0}} = δ₀`** (Kanter Def. 1.1 read at `k = 0`; the audit's reading
step): the span of `{0}` is the zero space, whose volume is the unit mass. Not a clause of a node:
it checks that the definition is not junk at dimension `0`. -/
theorem kanterUniform_zero : kanterUniform ({0} : Set (Rd d)) = Measure.dirac 0 := by
  unfold kanterUniform
  set V := Submodule.span ℝ ({0} : Set (Rd d)) with hV
  have hV0 : V = ⊥ := by rw [hV, Submodule.span_singleton_eq_bot.mpr rfl]
  haveI : Subsingleton V := by
    rw [hV0]; infer_instance
  have hpre : (Subtype.val ⁻¹' ({0} : Set (Rd d)) : Set V) = univ := by
    ext y; simp [Subsingleton.elim y 0]
  have huniv : (volume : Measure V) univ = 1 := by
    have h := (stdOrthonormalBasis ℝ V).volume_parallelepiped
    have : parallelepiped (stdOrthonormalBasis ℝ V) = univ := by
      apply eq_univ_of_forall
      intro y
      rw [mem_parallelepiped_iff]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩
    rwa [this] at h
  have hvol : (volume : Measure V) = Measure.dirac 0 := by
    ext s hs
    by_cases h0 : (0 : V) ∈ s
    · have : s = univ := eq_univ_of_forall fun y => by rwa [Subsingleton.elim y 0]
      simp [this, huniv]
    · have : s = ∅ := eq_empty_of_forall_notMem fun y hy =>
        h0 (by rwa [Subsingleton.elim y 0] at hy)
      simp [this]
  rw [hpre, hvol, ProbabilityTheory.cond_univ]
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs,
    Measure.dirac_apply' _ (measurable_subtype_coe hs), Measure.dirac_apply' _ hs]
  rfl

/-- **`u_K` is a probability measure** (Kanter Def. 1.2: the quotient by `Vol_V(K) ∈ (0,∞)`) for
every nonempty compact convex symmetric `K`. The preimage `K'` of `K` in its span `V` spans `V`;
being convex and containing `0`, its affine span is `V`, so it has nonempty interior in `V` and
positive volume. It is compact, `V` being closed, so its volume is finite. Not a clause of a node
(blind review W2B-4): it checks that the normalisation of `kanterUniform` is never degenerate on
the sets ledger A8 quantifies over, so that no junk value of the conditional measure widens the
axiom. -/
theorem isProbabilityMeasure_kanterUniform {K : Set (Rd d)} (hKne : K.Nonempty)
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K) :
    IsProbabilityMeasure (kanterUniform K) := by
  set V := Submodule.span ℝ K with hV
  set K' : Set V := Subtype.val ⁻¹' K with hK'
  obtain ⟨x₀, hx₀⟩ := hKne
  have h0K : (0 : Rd d) ∈ K := by
    have := hKcv hx₀ (hKs x₀ hx₀) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa using this
  have h0K' : (0 : V) ∈ K' := by simpa [hK'] using h0K
  have hK'cv : Convex ℝ K' := hKcv.linear_preimage V.subtype
  -- finite: `K'` is compact in `V`
  have hK'c : IsCompact K' :=
    (Submodule.closed_of_finiteDimensional V).isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hfin : (volume : Measure V) K' ≠ ⊤ := hK'c.measure_lt_top.ne
  -- positive: `K'` spans `V`, so its affine span is `V` and its interior is nonempty
  have hspan : Submodule.span ℝ K' = ⊤ := Submodule.span_span_coe_preimage
  have haff : affineSpan ℝ K' = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ V V ⟨0, h0K'⟩,
      vectorSpan_eq_span_vsub_set_right ℝ h0K']
    simpa using hspan
  have hint : (interior K').Nonempty := hK'cv.interior_nonempty_iff_affineSpan_eq_top.mpr haff
  have hpos : (volume : Measure V) K' ≠ 0 :=
    ((isOpen_interior.measure_pos volume hint).trans_le (measure_mono interior_subset)).ne'
  haveI : IsProbabilityMeasure ((volume : Measure V)[|K']) :=
    cond_isProbabilityMeasure_of_finite hpos hfin
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

end AffineHemigroup
