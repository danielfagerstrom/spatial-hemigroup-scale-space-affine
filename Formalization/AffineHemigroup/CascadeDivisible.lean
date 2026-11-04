/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PathCondition
import AffineHemigroup.Interfaces
import AffineHemigroup.Defs.IsotropicFamily
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# `thm:cascade-infinitely-divisible`: a continuous cascade has infinitely divisible increments

Blueprint: `blueprint/src/parts/04-classical.tex`, `thm:cascade-infinitely-divisible` (wave 2,
group C, Q-0281). Clause (1) spends ledger A6 (`khintchine_null_array`) once; (2) and (4) are
reductions to (1); clause (3) is `lem:path-condition-orders` (`AffineHemigroup.PathCondition`).

## The route

The array is the blueprint's: `μ_{n,k} := μ_{t_{n,k}, t_{n,k+1}}`, `t_{n,k} = s + k(t-s)/(n+1)`,
whose row convolutions are all `μ_{s,t}` by the cascade identity, with `b_n = 0`. **The rows are
infinitesimal** by a uniform statement (`cascade_small_increment`): for `ε, η > 0` there is
`δ > 0` with `μ_{a,b}{|x| > ε} < η` whenever `0 ≤ a ≤ b ≤ 1` and `b - a < δ`. It is proved by
contradiction on a sequence of pairs, through Mathlib's Lévy continuity theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`, a theorem of Mathlib, no interface) and the
portmanteau inequality for the closed set `{|x| ≥ ε}`: along the sequence the transforms tend to
`1`, by the uniform continuity of `(a, b) ↦ μ̂_{a,b}(ω)` on the compact triangle. The blueprint's
one-dimensional truncation inequality is not written out.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology ENNReal

variable {d : ℕ}

/-- The triangle `{0 ≤ a ≤ b ≤ 1}` is compact. -/
theorem isCompact_triangle : IsCompact {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter (isClosed_le continuous_snd continuous_const))
  · rintro ⟨a, b⟩ ⟨h0, hab, h1⟩
    exact ⟨⟨h0, hab.trans h1⟩, ⟨h0.trans hab, h1⟩⟩

/-- **The small increments**: under the hypotheses of `thm:cascade-infinitely-divisible`(1),
for `ε > 0` and `η > 0` there is `δ > 0` with `μ_{a,b}{|x| > ε} < η` whenever
`0 ≤ a ≤ b ≤ 1` and `b - a < δ`. -/
theorem cascade_small_increment (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → IsProbabilityMeasure (μ s t))
    (hdiag : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → μ s s = Measure.dirac 0)
    (hcont : ∀ ω : Rd d, ContinuousOn (fun p : ℝ × ℝ => charFun (μ p.1 p.2) ω)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1})
    {ε : ℝ} (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ →
      μ a b {x | ε < ‖x‖} < η := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ p : ℝ × ℝ, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧
      p.2 - p.1 < 1 / ((n : ℝ) + 1) ∧ η ≤ μ p.1 p.2 {x | ε < ‖x‖} := by
    intro n
    obtain ⟨a, b, ha, hab, hb, hlt, hge⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(a, b), ha, hab, hb, hlt, hge⟩
  choose p hp0 hp1 hp2 hplt hpge using hseq
  set T := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}
  have hpT : ∀ n, p n ∈ T := fun n => ⟨hp0 n, hp1 n, hp2 n⟩
  have hdT : ∀ n, ((p n).1, (p n).1) ∈ T := fun n => ⟨hp0 n, le_rfl, (hp1 n).trans (hp2 n)⟩
  -- the transforms tend to `1`
  have hgap : Tendsto (fun n => (p n).2 - (p n).1) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by linarith [hp1 n]) (fun n => (hplt n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hchar : ∀ ω : Rd d, Tendsto (fun n => charFun (μ (p n).1 (p n).2) ω) atTop (𝓝 1) := by
    intro ω
    have huc := isCompact_triangle.uniformContinuousOn_of_continuous (hcont ω)
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.tendsto_atTop]
    intro η' hη'
    obtain ⟨δ, hδ, hδu⟩ := huc η' hη'
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hgap) δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 : charFun (μ (p n).1 (p n).1) ω = 1 := by
      rw [hdiag _ (hp0 n) ((hp1 n).trans (hp2 n)), charFun_dirac]; simp
    have hd : dist (p n) ((p n).1, (p n).1) < δ := by
      have := hN n hn
      rw [Real.dist_eq, sub_zero] at this
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [max_lt_iff]
      exact ⟨hδ, this⟩
    have := hδu (p n) (hpT n) _ (hdT n) hd
    rw [← h1]
    exact this
  -- Lévy's continuity theorem: the increments tend to `δ₀`
  haveI : ∀ n, IsProbabilityMeasure (μ (p n).1 (p n).2) := fun n =>
    hprob _ _ (hp0 n) (hp1 n) (hp2 n)
  let P : ℕ → ProbabilityMeasure (Rd d) := fun n => ⟨μ (p n).1 (p n).2, inferInstance⟩
  let P₀ : ProbabilityMeasure (Rd d) := ⟨Measure.dirac 0, inferInstance⟩
  have hlim : Tendsto P atTop (𝓝 P₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ω => ?_
    have h1 : charFun (P₀ : Measure (Rd d)) ω = 1 := by
      change charFun (Measure.dirac 0) ω = 1
      rw [charFun_dirac]; simp
    rw [h1]
    exact hchar ω
  -- the portmanteau inequality on `{|x| ≥ ε}`
  have hF : IsClosed {x : Rd d | ε ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  have h0 : (P₀ : Measure (Rd d)) {x : Rd d | ε ≤ ‖x‖} = 0 := by
    change Measure.dirac (0 : Rd d) {x : Rd d | ε ≤ ‖x‖} = 0
    rw [Measure.dirac_apply' _ hF.measurableSet]
    simp [not_le.2 hε]
  rw [h0] at hls
  have hev : ∀ᶠ n in atTop, (P n : Measure (Rd d)) {x : Rd d | ε ≤ ‖x‖} < η :=
    eventually_lt_of_limsup_lt (hls.trans_lt hη)
  obtain ⟨n, hn⟩ := hev.exists
  have hsub : (P n : Measure (Rd d)) {x : Rd d | ε < ‖x‖} ≤
      (P n : Measure (Rd d)) {x : Rd d | ε ≤ ‖x‖} :=
    measure_mono fun x (hx : ε < ‖x‖) => (le_of_lt hx : ε ≤ ‖x‖)
  exact absurd (hsub.trans_lt hn) (not_lt.2 (hpge n))

/-- **The row convolutions**: along a partition `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N` of a subinterval of
`[0,1]`, the convolution of the increments is the increment over the whole interval. -/
theorem convList_cascade (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → IsProbabilityMeasure (μ s t))
    (hdiag : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → μ s s = Measure.dirac 0)
    (hcasc : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → t ≤ 1 → μ r t = μ s t ∗ μ r s) :
    ∀ (N : ℕ) (τ : ℕ → ℝ), 0 ≤ τ 0 → (∀ k, k < N → τ k ≤ τ (k + 1)) → τ N ≤ 1 →
      convList (List.ofFn fun k : Fin N => μ (τ k) (τ (k + 1))) = μ (τ 0) (τ N) := by
  intro N
  induction N with
  | zero =>
    intro τ h0 _ h1
    simp only [List.ofFn_zero, convList]
    exact (hdiag _ h0 h1).symm
  | succ N ih =>
    intro τ h0 hmono h1
    have hmono' : Monotone fun k : Fin (N + 2) => τ k := by
      refine Fin.monotone_iff_le_succ.2 fun i => ?_
      simpa using hmono i i.2
    have hle : ∀ k : ℕ, k ≤ N + 1 → τ 0 ≤ τ k ∧ τ k ≤ τ (N + 1) := fun k hk => by
      have h := @hmono' ⟨0, by omega⟩ ⟨k, by omega⟩ (by simp)
      have h' := @hmono' ⟨k, by omega⟩ ⟨N + 1, by omega⟩ (by simp; omega)
      exact ⟨h, h'⟩
    rw [List.ofFn_succ, convList]
    have hrest := ih (fun k => τ (k + 1)) ((h0.trans (hle 1 (by omega)).1))
      (fun k hk => hmono (k + 1) (by omega)) h1
    simp only [Fin.val_succ, Fin.val_zero, zero_add] at hrest ⊢
    rw [show (fun i : Fin N => μ (τ (↑i + 1)) (τ (↑i + 1 + 1))) =
      fun k : Fin N => μ (τ (↑k + 1)) (τ (↑k + 1 + 1)) from rfl, hrest]
    haveI := hprob (τ 0) (τ 1) h0 (hmono 0 (by omega)) ((hle 1 (by omega)).2.trans h1)
    haveI := hprob (τ 1) (τ (N + 1)) (h0.trans (hle 1 (by omega)).1) (hle 1 (by omega)).2 h1
    rw [Measure.conv_comm, ← hcasc _ _ _ h0 (hmono 0 (by omega)) (hle 1 (by omega)).2 h1]

/-- **`thm:cascade-infinitely-divisible`(1)**: a cascade `(μ_{s,t})_{0 ≤ s ≤ t ≤ 1}` of
probability measures on `ℝ^d` with continuous transforms has infinitely divisible increments.
Spends ledger A6. -/
theorem cascade_interval_infinitelyDivisible (_hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → IsProbabilityMeasure (μ s t))
    (hdiag : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → μ s s = Measure.dirac 0)
    (hcasc : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → t ≤ 1 → μ r t = μ s t ∗ μ r s)
    (hcont : ∀ ω : Rd d, ContinuousOn (fun p : ℝ × ℝ => charFun (μ p.1 p.2) ω)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → IsInfinitelyDivisible (μ s t) := by
  intro s t hs hst ht
  -- the partition points `t_{n,k} = s + k(t - s)/(n+1)`
  set τ : ℕ → ℕ → ℝ := fun n k => s + k * ((t - s) / ((n : ℝ) + 1)) with hτ
  have hh : ∀ n : ℕ, 0 ≤ (t - s) / ((n : ℝ) + 1) := fun n =>
    div_nonneg (by linarith) (by positivity)
  have hτ0 : ∀ n, τ n 0 = s := fun n => by simp [hτ]
  have hτN : ∀ n, τ n (n + 1) = t := fun n => by
    simp only [hτ]; push_cast; field_simp; ring
  have hτmono : ∀ n k, τ n k ≤ τ n (k + 1) := fun n k => by
    simp only [hτ]; push_cast; nlinarith [hh n]
  have hτle : ∀ n k, k ≤ n + 1 → s ≤ τ n k ∧ τ n k ≤ t := fun n k hk => by
    refine ⟨by simp only [hτ]; nlinarith [hh n, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)], ?_⟩
    rw [← hτN n]
    simp only [hτ]
    have : (k : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hk
    nlinarith [hh n]
  -- the array
  set r : ℕ → ℕ := fun n => n + 1
  set ν : (n : ℕ) → Fin (r n) → Measure (Rd d) := fun n k => μ (τ n k) (τ n (k + 1))
  have hνprob : ∀ n k, IsProbabilityMeasure (ν n k) := fun n k => by
    have hk : (k : ℕ) < n + 1 := k.2
    exact hprob _ _ (hs.trans (hτle n k (by omega)).1) (hτmono n k)
      ((hτle n (k + 1) (by omega)).2.trans ht)
  haveI : IsProbabilityMeasure (μ s t) := hprob s t hs hst ht
  -- the rows convolve to `μ_{s,t}`
  have hrow : ∀ n, convList (List.ofFn (ν n)) = μ s t := by
    intro n
    have h := convList_cascade μ hprob hdiag hcasc (n + 1) (τ n)
      (by rw [hτ0]; exact hs) (fun k _ => hτmono n k) (by rw [hτN]; exact ht)
    rw [hτ0, hτN] at h
    exact h
  -- the rows are infinitesimal
  have hnull : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ⨆ k, ν n k {x | ε < ‖x‖}) atTop (𝓝 0) := by
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨δ, hδ, hsmall⟩ := cascade_small_increment μ hprob hdiag hcont hε hη
    have hev : ∀ᶠ n : ℕ in atTop, (t - s) / ((n : ℝ) + 1) < δ := by
      have h := (tendsto_const_nhds (x := t - s)).div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      exact h.eventually (gt_mem_nhds hδ)
    filter_upwards [hev] with n hn
    refine iSup_le fun k => ?_
    have hk : (k : ℕ) < n + 1 := k.2
    refine (hsmall _ _ (hs.trans (hτle n k (by omega)).1)
      (hτmono n k) ((hτle n (k + 1) (by omega)).2.trans ht) ?_).le
    simp only [hτ]; push_cast; nlinarith
  -- Khintchine's theorem (ledger A6), with `b_n = 0`
  refine khintchine_null_array r (fun n => Nat.succ_pos n) ν hνprob hnull (fun _ => 0) (μ s t)
    fun f => ?_
  simp only [neg_zero, Measure.conv_dirac_zero, hrow]
  exact tendsto_const_nhds

/-- **`thm:cascade-infinitely-divisible`(2)**: for a partial order `≤_W` on `𝒫 ⊆ PSD(d)` and
probability measures satisfying (K1) and (K2) on its pairs, the increment of a pair joined by a
`W`-chain is infinitely divisible. -/
theorem chain_infinitelyDivisible (hd : 1 ≤ d) (P : Set (Mat d)) (_hP : P ⊆ psdSet d)
    (le : Mat d → Mat d → Prop) (_hle : IsPartialOrderOn P le)
    (μ : Mat d → Mat d → Measure (Rd d))
    (hprob : ∀ S ∈ P, ∀ S' ∈ P, le S S' → IsProbabilityMeasure (μ S S'))
    (hdiag : ∀ S ∈ P, μ S S = Measure.dirac 0)
    (hcasc : ∀ S ∈ P, ∀ S' ∈ P, ∀ S'' ∈ P, le S S' → le S' S'' → μ S S'' = μ S' S'' ∗ μ S S')
    (hcont : ∀ ω : Rd d, ContinuousOn (fun p : Mat d × Mat d => charFun (μ p.1 p.2) ω)
      {p : Mat d × Mat d | p.1 ∈ P ∧ p.2 ∈ P ∧ le p.1 p.2})
    (S S' : Mat d) (γ : ℝ → Mat d) (hγ : IsWChain P le γ S S') :
    IsInfinitelyDivisible (μ S S') := by
  have hI : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u ∈ Icc (0 : ℝ) 1 := fun u h0 h1 => ⟨h0, h1⟩
  have h := cascade_interval_infinitelyDivisible hd (fun u v => μ (γ u) (γ v))
    (fun u v hu huv hv => hprob _ (hγ.mem u (hI u hu (huv.trans hv))) _
      (hγ.mem v (hI v (hu.trans huv) hv)) (hγ.mono u (hI u hu (huv.trans hv)) v
        (hI v (hu.trans huv) hv) huv))
    (fun u hu hu1 => hdiag _ (hγ.mem u (hI u hu hu1)))
    (fun u v w hu huv hvw hw => by
      have hu' := hI u hu (huv.trans (hvw.trans hw))
      have hv' := hI v (hu.trans huv) (hvw.trans hw)
      have hw' := hI w (hu.trans (huv.trans hvw)) hw
      exact hcasc _ (hγ.mem u hu') _ (hγ.mem v hv') _ (hγ.mem w hw') (hγ.mono u hu' v hv' huv)
        (hγ.mono v hv' w hw' hvw))
    (fun ω => by
      have hmaps : MapsTo (fun p : ℝ × ℝ => (γ p.1, γ p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}
          {p : Mat d × Mat d | p.1 ∈ P ∧ p.2 ∈ P ∧ le p.1 p.2} := by
        rintro ⟨u, v⟩ ⟨hu, huv, hv⟩
        exact ⟨hγ.mem u (hI u hu (huv.trans hv)), hγ.mem v (hI v (hu.trans huv) hv),
          hγ.mono u (hI u hu (huv.trans hv)) v (hI v (hu.trans huv) hv) huv⟩
      have hγc : ContinuousOn (fun p : ℝ × ℝ => (γ p.1, γ p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
        refine ContinuousOn.prodMk ?_ ?_
        · exact hγ.continuousOn.comp continuousOn_fst fun p hp =>
            hI p.1 hp.1 (hp.2.1.trans hp.2.2)
        · exact hγ.continuousOn.comp continuousOn_snd fun p hp =>
            hI p.2 (hp.1.trans hp.2.1) hp.2.2
      exact (hcont ω).comp hγc hmaps)
    0 1 le_rfl zero_le_one le_rfl
  simpa [hγ.start, hγ.finish] using h

/-- **`thm:cascade-infinitely-divisible`(2)**, in particular: for a wedge datum with the path
condition (P), every increment of a `(G, W)`-cascade family of kernels, and every kernel from the
origin, is infinitely divisible. -/
theorem gw_family_infinitelyDivisible (hd : 1 ≤ d) {G : Set (Mat d)}
    {le : Mat d → Mat d → Prop} (hW : IsWedgeDatum G le) (hP : HasPathCondition le)
    (μ : Mat d → Mat d → Measure (Rd d)) (hμ : IsGWCascadeFamily G le μ) :
    (∀ p ∈ wedgePairs le, IsInfinitelyDivisible (μ p.1 p.2)) ∧
      ∀ S : Mat d, S.PosSemidef → IsInfinitelyDivisible (μ 0 S) := by
  have hpo : IsPartialOrderOn (psdSet d) le :=
    ⟨fun S hS => hW.refl S hS, fun S hS S' hS' h h' => hW.antisymm S S' hS hS' h h',
      fun S hS S' hS' S'' hS'' h h' => hW.trans S S' S'' hS hS' hS'' h h'⟩
  have hpair : ∀ p ∈ wedgePairs le, IsInfinitelyDivisible (μ p.1 p.2) := by
    rintro ⟨S, S'⟩ ⟨hS, hS', h⟩
    obtain ⟨γ, hγ⟩ := hP S S' hS hS' h
    exact chain_infinitelyDivisible hd (psdSet d) subset_rfl le hpo μ
      (fun S hS S' hS' h => hμ.isProbability (S, S') ⟨hS, hS', h⟩)
      (fun S hS => hμ.diag S hS)
      (fun S hS S' hS' S'' hS'' h h' => hμ.cascade S S' S'' hS hS' hS'' h h')
      (fun ω => hμ.continuous ω) S S' γ hγ
  exact ⟨hpair, fun S hS => hpair (0, S) ⟨PosSemidef.zero, hS, wedge_zero_le hW hS⟩⟩

/-- **`thm:cascade-infinitely-divisible`(4)**: every `μ_{s,t}` of an isotropic cascade family in
dimension `d` is infinitely divisible. -/
theorem isotropic_family_infinitelyDivisible (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (S : ℝ → ℝ → ℝ) (hμ : IsIsotropicCascadeFamily μ S) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsInfinitelyDivisible (μ s t) := by
  intro s t hs hst
  set L : ℝ → ℝ := fun u => s + u * (t - s) with hL
  have hL0 : ∀ u, 0 ≤ u → 0 ≤ L u := fun u hu => by
    simp only [hL]; nlinarith
  have hLmono : ∀ u v, u ≤ v → L u ≤ L v := fun u v huv => by
    simp only [hL]; nlinarith
  have h := cascade_interval_infinitelyDivisible hd (fun u v => μ (L u) (L v))
    (fun u v hu huv _ => hμ.isProbability _ _ (hL0 u hu) (hLmono u v huv))
    (fun u hu _ => hμ.diag _ (hL0 u hu))
    (fun u v w hu huv hvw _ => hμ.cascade _ _ _ (hL0 u hu) (hLmono u v huv) (hLmono v w hvw))
    (fun ω => by
      have hc : ContinuousOn (fun p : ℝ × ℝ => (L p.1, L p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
        (Continuous.continuousOn (by fun_prop))
      exact (hμ.continuous ω).comp hc fun p hp => ⟨hL0 _ hp.1, hLmono _ _ hp.2.1⟩)
    0 1 le_rfl zero_le_one le_rfl
  have h0 : L 0 = s := by simp [hL]
  have h1 : L 1 = t := by simp [hL]
  simpa [h0, h1] using h

end AffineHemigroup
