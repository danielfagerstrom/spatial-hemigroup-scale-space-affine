/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.RadialMarginal
import ScaleSpaceCore.Construction

/-!
# `lem:isotropic-marginal-family` — the marginals of an isotropic family form a family on the line

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:isotropic-marginal-family`. Lean core
only: the marginals are assembled into the shared library's `ScaleSpace.CascadeData` (Paper V's
structure, in `ScaleSpaceCore` at `v0.3.0`; read from there since Q-0365), whose `cascadeCore` and
`isScaleCovariant` are Lean core and give
(A1)–(A8) and (ND) of [V, Def. 3.1]; this file checks the data's hypotheses and nothing else.

## The route

The kernels are **totalised**: `marginalKernel μ e s t` is `π_*μ_{s,t}` on the pairs
`0 ≤ s ≤ t` and `δ₀` off them, which is what lets `CascadeData` register a probability instance
for every pair. Its hypotheses are read off `lem:radial-marginal`: symmetry and the probability
property from (1), the diagonal and the cascade law from (3) and (I1) (the convolution order of
`CascadeData.conv` is `κ_{r,s} ∗ κ_{s,t}`, the commuted form of (I1)'s), the continuity of the
cosine transform from (I2) at `ξ = ωe` through `charFun_marginal`, nondegeneracy from (2) and
(ND), and the dilation identity from (3) and (I4).

The blueprint's proof writes out (A1)–(A8) and (ND) for the operators, (A7) by the argument of
[V, Thm. 7.3]'s sufficiency proof; in the Lean those are Paper V's `CascadeData` lemmas, which make
the same argument once for every family of kernels (`CascadeData.continuousOn_mconvL1`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ}

/-- A unit vector exists only in dimension `d ≥ 1`. -/
theorem one_le_of_norm_eq_one {e : Rd d} (he : ‖e‖ = 1) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exfalso
    have h0 : e = 0 := Subsingleton.elim _ _
    simp [h0] at he
  · exact h

open Classical in
/-- **The totalised marginal kernels**: `π_*μ_{s,t}` on the pairs `0 ≤ s ≤ t`, `δ₀` off them. -/
noncomputable def marginalKernel (μ : ℝ → ℝ → Measure (Rd d)) (e : Rd d) (s t : ℝ) : Measure ℝ :=
  if 0 ≤ s ∧ s ≤ t then marginal e (μ s t) else Measure.dirac 0

theorem marginalKernel_of_le (μ : ℝ → ℝ → Measure (Rd d)) (e : Rd d) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : marginalKernel μ e s t = marginal e (μ s t) := by
  rw [marginalKernel, if_pos ⟨hs, hst⟩]

/-- **The marginal data**: the totalised marginals of an isotropic cascade family, with the
hypotheses of Paper V's `CascadeData`. -/
noncomputable def marginalData {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) : ScaleSpace.CascadeData where
  κ := marginalKernel μ e
  prob s t := by
    by_cases h : 0 ≤ s ∧ s ≤ t
    · rw [marginalKernel_of_le μ e h.1 h.2]
      haveI := hμ.isProbability s t h.1 h.2
      infer_instance
    · rw [marginalKernel, if_neg h]
      infer_instance
  sym s t := by
    by_cases h : 0 ≤ s ∧ s ≤ t
    · rw [marginalKernel_of_le μ e h.1 h.2]
      haveI := hμ.isProbability s t h.1 h.2
      exact (radial_marginal (one_le_of_norm_eq_one he) e he (μ s t)
        (fun Q hQ => hμ.rotation Q hQ s t h.1 h.2)).2.1
    · rw [marginalKernel, if_neg h]
      exact ScaleSpace.isSymmetric_dirac_zero
  self t ht := by
    rw [marginalKernel_of_le μ e ht le_rfl, hμ.diag t ht, marginal,
      Measure.map_dirac' (continuous_inner_left e).measurable]
    simp
  conv r s t hr hrs hst := by
    haveI := hμ.isProbability r s hr hrs
    haveI := hμ.isProbability s t (hr.trans hrs) hst
    rw [marginalKernel_of_le μ e hr hrs, marginalKernel_of_le μ e (hr.trans hrs) hst,
      marginalKernel_of_le μ e hr (hrs.trans hst), hμ.cascade r s t hr hrs hst,
      (radial_marginal_ops (one_le_of_norm_eq_one he) e he (μ s t) (μ r s) 1 one_pos).1,
      Measure.conv_comm]
  cos_continuousOn ω := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => (charFun (μ p.1 p.2) (ω • e)).re)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      Complex.continuous_re.comp_continuousOn (hμ.continuous (ω • e))
    refine hc.congr fun p hp => ?_
    have hs : 0 ≤ p.1 := hp.1
    have hst : p.1 ≤ p.2 := hp.2
    haveI := hμ.isProbability p.1 p.2 hs hst
    have hsym := (radial_marginal (one_le_of_norm_eq_one he) e he (μ p.1 p.2)
      (fun Q hQ => hμ.rotation Q hQ p.1 p.2 hs hst)).2.1
    simp only
    rw [marginalKernel_of_le μ e hs hst, ← charFun_marginal,
      ScaleSpace.charFun_eq_fourierCos_of_symmetric hsym, Complex.ofReal_re]

@[simp] theorem marginalData_κ {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    (marginalData hμ e he).κ = marginalKernel μ e := rfl

/-- (ND) for the marginal data, from (ND) of the family and `lem:radial-marginal`(2). -/
theorem marginalData_nondegenerate {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    ∀ s t : ℝ, 0 ≤ s → s < t → (marginalData hμ e he).κ s t ≠ Measure.dirac 0 := by
  intro s t hs hst h
  haveI := hμ.isProbability s t hs hst.le
  rw [marginalData_κ, marginalKernel_of_le μ e hs hst.le,
    radial_marginal_eq_dirac (one_le_of_norm_eq_one he) e he (μ s t)
      (fun Q hQ => hμ.rotation Q hQ s t hs hst.le)] at h
  exact hμ.nondegenerate s t hs hst h

/-- The dilation identity for the marginal data, from (I4) and `lem:radial-marginal`(3). -/
theorem marginalData_dilation {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ((marginalData hμ e he).κ s t).map (fun x => lam * x)
        = (marginalData hμ e he).κ (S lam s) (S lam t) := by
  intro lam hlam s t hs hst
  have hb := hμ.scale_bij lam hlam
  have hSs : 0 ≤ S lam s := hb.mapsTo hs
  have hSst : S lam s ≤ S lam t := hb.strictMonoOn.monotoneOn hs (hs.trans hst) hst
  haveI := hμ.isProbability s t hs hst
  rw [marginalData_κ, marginalKernel_of_le μ e hs hst, marginalKernel_of_le μ e hSs hSst,
    ← (radial_marginal_ops (one_le_of_norm_eq_one he) e he (μ s t) (μ s t) lam hlam).2.1,
    hμ.scale lam hlam s t hs hst]

/-- **`lem:isotropic-marginal-family`, the route**: the marginals `κ_{s,t} := π_*μ_{s,t}` of an
isotropic cascade family are, on the pairs `0 ≤ s ≤ t`, the kernels of a `ScaleSpace.CascadeData`
(symmetric probability kernels with the cascade law `κ_{r,s} ∗ κ_{s,t} = κ_{r,t}` and continuous
cosine transforms), nondegenerate, and with `(λ·)_*κ_{s,t} = κ_{S_λ s, S_λ t}`: Paper V's hypotheses
for (A1)–(A8) and (ND). -/
theorem isotropic_marginal_cascadeData {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    ∃ D : ScaleSpace.CascadeData,
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → D.κ s t = marginal e (μ s t)) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → D.κ s t ≠ Measure.dirac 0) ∧
      ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (D.κ s t).map (fun x => lam * x) = D.κ (S lam s) (S lam t) :=
  ⟨marginalData hμ e he, fun _ _ hs hst => marginalKernel_of_le μ e hs hst,
    marginalData_nondegenerate hμ e he, marginalData_dilation hμ e he⟩

/-- **The marginal family**: Paper V's `CascadeFamily` built on the marginal data, with the
family's own dilation action. -/
noncomputable def marginalFamily {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) : ScaleSpace.CascadeFamily where
  toCascadeCore := (marginalData hμ e he).cascadeCore (marginalData_nondegenerate hμ e he)
  S := S
  covariant := (marginalData hμ e he).isScaleCovariant S
    (fun lam hlam => (hμ.scale_bij lam hlam).mapsTo)
    (fun lam hlam => (hμ.scale_bij lam hlam).strictMonoOn)
    (fun lam hlam => (hμ.scale_bij lam hlam).surjOn)
    (marginalData_dilation hμ e he)

/-- The marginal family is represented by the marginals. -/
theorem marginalFamily_isKernelFamily {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    ScaleSpace.IsKernelFamily (marginalFamily hμ e he).Φ (fun s t => marginal e (μ s t)) where
  isProbability s t hs hst := by
    haveI := hμ.isProbability s t hs hst
    infer_instance
  conv s t hs hst f := by
    have h := (marginalData hμ e he).isKernelFamily.conv s t hs hst f
    rw [marginalData_κ, marginalKernel_of_le μ e hs hst] at h
    exact h

/-- **`lem:isotropic-marginal-family`**: `μ̂_{s,t}(ξ) = κ̂_{s,t}(|ξ|)`, each `κ_{s,t}` is a
symmetric probability measure, and `Φ_{s,t} f := κ_{s,t} ∗ f` is a symmetric cascade measurement
family in the sense of [V, Def. 3.1] — Paper V's `CascadeFamily`, (A1)–(A7), (A4), (ND) and (A8) —
with the same `(S_λ)`. -/
theorem isotropic_marginal_family {μ : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hμ : IsIsotropicCascadeFamily μ S) (e : Rd d) (he : ‖e‖ = 1) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = charFun (marginal e (μ s t)) ‖ξ‖) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (marginal e (μ s t)) ∧
        ScaleSpace.IsSymmetric (marginal e (μ s t))) ∧
      ∃ Fam : ScaleSpace.CascadeFamily, Fam.S = S ∧
        ScaleSpace.IsKernelFamily Fam.Φ (fun s t => marginal e (μ s t)) := by
  have hd := one_le_of_norm_eq_one he
  refine ⟨fun s t hs hst ξ => ?_, fun s t hs hst => ?_,
    ⟨marginalFamily hμ e he, rfl, marginalFamily_isKernelFamily hμ e he⟩⟩
  · haveI := hμ.isProbability s t hs hst
    exact (radial_marginal hd e he (μ s t) (fun Q hQ => hμ.rotation Q hQ s t hs hst)).2.2.1 ξ
  · haveI := hμ.isProbability s t hs hst
    obtain ⟨h1, h2, -⟩ := radial_marginal hd e he (μ s t) (fun Q hQ => hμ.rotation Q hQ s t hs hst)
    exact ⟨h1, h2⟩

end AffineHemigroup
