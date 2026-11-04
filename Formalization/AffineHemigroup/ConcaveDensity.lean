/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A measure on `(0,∞)` with a concave distribution function has a nonincreasing density

Blueprint: `prop:isotropic-radial-monotone`, the paragraph *the density*
(`blueprint/src/parts/03-isotropic.tex`). Wave 2, group B (Q-0281). Mathlib types only.

**Statement** (`exists_antitone_density_of_concave`). A finite measure `m` on `ℝ` with
`m((-∞,0]) = 0` whose distribution function `G(v) = m((0,v])` is concave on `[0,∞)` is
`D · Lebesgue` on `(0,∞)` for a **nonincreasing** `D ≥ 0`. `D` is the right derivative of `G`;
Mathlib supplies its existence and monotonicity for a convex function
(`ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`, `ConvexOn.monotoneOn_rightDeriv`, applied
to `-G`), the continuity of a concave function on an open interval, and the fundamental theorem of
calculus with a right derivative (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`). The
two measures then agree on every `(a,b]` with `0 < a`, by continuity from below on `(0,b]`, and so
everywhere (`Measure.ext_of_Ioc'`).

**Concavity with values in `[0,∞]`** (`ConcaveENN`). The distribution functions of the node are
mixtures, `G(v) = ∫ G_K(v) Λ(dK)`, of functions that are concave only almost surely and whose
measurability in `K` is not available; so concavity is carried in `ℝ≥0∞`, where the integral of a
pointwise inequality needs no measurability (`le_lintegral_add`, `lintegral_mono_ae`).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **Concavity on `[0,∞)` for an `ℝ≥0∞`-valued function**: `a f(x) + b f(y) ≤ f(ax + by)` for
`x, y ≥ 0`, `a, b ≥ 0`, `a + b = 1`. Mathlib types only. -/
def ConcaveENN (f : ℝ → ℝ≥0∞) : Prop :=
  ∀ ⦃x y a b : ℝ⦄, 0 ≤ x → 0 ≤ y → 0 ≤ a → 0 ≤ b → a + b = 1 →
    ENNReal.ofReal a * f x + ENNReal.ofReal b * f y ≤ f (a * x + b * y)

/-- A nonnegative real function concave on `[0,∞)` is `ConcaveENN` through `ofReal`. -/
theorem concaveENN_ofReal {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g)
    (hg0 : ∀ v, 0 ≤ v → 0 ≤ g v) : ConcaveENN fun v => ENNReal.ofReal (g v) := by
  intro x y a b hx hy ha hb hab
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha (hg0 x hx)) (mul_nonneg hb (hg0 y hy))]
  have h := hg.2 (mem_Ici.mpr hx) (mem_Ici.mpr hy) ha hb hab
  simp only [smul_eq_mul] at h
  exact ENNReal.ofReal_le_ofReal h

/-- A constant multiple of a `ConcaveENN` function is `ConcaveENN`, the constant `∞` included. -/
theorem ConcaveENN.const_mul {f : ℝ → ℝ≥0∞} (hf : ConcaveENN f) (c : ℝ≥0∞) :
    ConcaveENN fun v => c * f v := by
  intro x y a b hx hy ha hb hab
  rw [mul_left_comm, mul_left_comm (ENNReal.ofReal b), ← mul_add]
  exact mul_le_mul' le_rfl (hf hx hy ha hb hab)

/-- **A mixture of almost surely `ConcaveENN` functions is `ConcaveENN`**, with no measurability in
the mixing variable. -/
theorem ConcaveENN.lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ → ℝ≥0∞} (hF : ∀ᵐ θ ∂μ, ConcaveENN (F θ)) :
    ConcaveENN fun v => ∫⁻ θ, F θ v ∂μ := by
  intro x y a b hx hy ha hb hab
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (le_lintegral_add _ _) (lintegral_mono_ae ?_)
  filter_upwards [hF] with θ hθ
  exact hθ hx hy ha hb hab

/-- A finite `ConcaveENN` function is concave on `[0,∞)` after `toReal`. -/
theorem ConcaveENN.concaveOn_toReal {f : ℝ → ℝ≥0∞} (hf : ConcaveENN f) (hfin : ∀ v, f v ≠ ⊤) :
    ConcaveOn ℝ (Ici 0) fun v => (f v).toReal := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h := hf (mem_Ici.mp hx) (mem_Ici.mp hy) ha hb hab
  have hl : (ENNReal.ofReal a * f x + ENNReal.ofReal b * f y).toReal
      = a * (f x).toReal + b * (f y).toReal := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin x))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin y)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  rw [← hl]
  exact ENNReal.toReal_mono (hfin _) h

/-- On a measure null on `(-∞,0]`, an interval `(a,b]` has the measure of `(max a 0, b]`. -/
theorem measure_Ioc_eq_max {m : Measure ℝ} (h0 : m (Iic 0) = 0) (a b : ℝ) :
    m (Ioc a b) = m (Ioc (max a 0) b) := by
  refine le_antisymm ?_ (measure_mono fun x hx => ⟨lt_of_le_of_lt (le_max_left a 0) hx.1, hx.2⟩)
  calc m (Ioc a b) ≤ m (Iic 0 ∪ Ioc (max a 0) b) := measure_mono fun x hx => by
        by_cases hx0 : x ≤ 0
        · exact Or.inl hx0
        · exact Or.inr ⟨max_lt hx.1 (lt_of_not_ge hx0), hx.2⟩
    _ ≤ m (Iic 0) + m (Ioc (max a 0) b) := measure_union_le _ _
    _ = m (Ioc (max a 0) b) := by rw [h0, zero_add]

/-- **A finite measure on `(0,∞)` with a concave distribution function has a nonincreasing
density**: if `m((-∞,0]) = 0` and `v ↦ m((0,v])` is concave on `[0,∞)`, then
`m = D · Lebesgue|_{(0,∞)}` for some `D ≥ 0` nonincreasing on `(0,∞)` (the right derivative of the
distribution function). Mathlib types only. -/
theorem exists_antitone_density_of_concave (m : Measure ℝ) [IsFiniteMeasure m]
    (h0 : m (Iic 0) = 0) (hconc : ConcaveOn ℝ (Ici 0) fun v => (m (Ioc 0 v)).toReal) :
    ∃ D : ℝ → ℝ, (∀ v, 0 < v → 0 ≤ D v) ∧ AntitoneOn D (Ioi 0) ∧
      m = (volume.restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal (D v) := by
  set G : ℝ → ℝ := fun v => (m (Ioc 0 v)).toReal with hG
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  have hconv : ConvexOn ℝ (Ici 0) fun v => -G v := hconc.neg
  set D : ℝ → ℝ := fun v => -derivWithin (fun w => -G w) (Ioi v) v with hD
  have hderiv : ∀ x, 0 < x → HasDerivWithinAt G (D x) (Ioi x) x := by
    intro x hx
    have h := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior (by rw [hint]; exact hx)
    have h2 : HasDerivWithinAt (fun v => - -G v) (D x) (Ioi x) x := h.neg
    simpa only [neg_neg] using h2
  have hmono : Monotone G := fun v w hvw =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioc_subset_Ioc_right hvw))
  have hDnn : ∀ v, 0 < v → 0 ≤ D v := by
    intro v hv
    have h := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv v hv))
    rw [sdiff_singleton_eq_self (fun h => lt_irrefl v (mem_Ioi.mp h))] at h
    refine ge_of_tendsto h (eventually_nhdsWithin_of_forall fun w (hw : v < w) => ?_)
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono hw.le)) (sub_nonneg.mpr hw.le)
  have hDanti : AntitoneOn D (Ioi 0) := by
    intro x hx y hy hxy
    have h := hconv.monotoneOn_rightDeriv (by rw [hint]; exact hx) (by rw [hint]; exact hy) hxy
    simp only [hD]
    linarith
  refine ⟨D, hDnn, hDanti, ?_⟩
  set ν := (volume.restrict (Ioi (0 : ℝ))).withDensity fun v => ENNReal.ofReal (D v) with hν
  have hνIoc : ∀ a b : ℝ, ν (Ioc a b) = ∫⁻ x in Ioc a b ∩ Ioi 0, ENNReal.ofReal (D x) := by
    intro a b
    rw [hν, withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hν0 : ν (Iic 0) = 0 := by
    rw [hν, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
  -- the two measures agree on `(a,b]` for `0 < a ≤ b`
  have hpos : ∀ a b : ℝ, 0 < a → a ≤ b → m (Ioc a b) = ν (Ioc a b) := by
    intro a b ha hab
    have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
    have hcont : ContinuousOn G (Icc a b) :=
      (hconc.continuousOn_interior.mono (by rw [hint]; exact hsub))
    have hii : IntervalIntegrable D volume a b := by
      refine (hDanti.mono ?_).intervalIntegrable
      rw [uIcc_of_le hab]; exact hsub
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
      (fun x hx => hderiv x (lt_trans ha hx.1)) hii
    have hion : IntegrableOn D (Ioc a b) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hii
    have hsplit : m (Ioc 0 b) = m (Ioc 0 a) + m (Ioc a b) := by
      rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
        Ioc_union_Ioc_eq_Ioc ha.le hab]
    have hGdiff : G b - G a = (m (Ioc a b)).toReal := by
      simp only [hG]
      rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    have hinter : Ioc a b ∩ Ioi 0 = Ioc a b :=
      inter_eq_left.mpr fun x hx => lt_trans ha hx.1
    rw [hνIoc, hinter, ← ofReal_integral_eq_lintegral_ofReal hion
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ fun x hx => hDnn x (lt_trans ha hx.1))),
      ← intervalIntegral.integral_of_le hab, hftc, hGdiff,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- and on `(0,b]`, by continuity from below
  have hzero : ∀ b : ℝ, m (Ioc 0 b) = ν (Ioc 0 b) := by
    intro b
    rcases le_or_gt b 0 with hb | hb
    · rw [Ioc_eq_empty (not_lt.mpr hb), measure_empty, measure_empty]
    set S : ℕ → Set ℝ := fun n => Ioc (b / ((n : ℝ) + 1)) b with hS
    have hSmono : Monotone S := by
      intro p q hpq x hx
      refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
      have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      have : ((p : ℝ) + 1) ≤ (q : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hpq 1
      exact div_le_div_of_nonneg_left hb.le hp this
    have hU : (⋃ n, S n) = Ioc 0 b := by
      ext x
      simp only [mem_iUnion, hS, mem_Ioc]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨lt_of_le_of_lt (by positivity) h1, h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_gt (b / x)
        refine ⟨n, ?_, h2⟩
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ h1] at hn
        linarith
    rw [← hU, hSmono.measure_iUnion, hSmono.measure_iUnion]
    refine iSup_congr fun n => hpos _ _ (by positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine Measure.ext_of_Ioc' m ν (fun a b _ => measure_ne_top _ _) fun a b hab => ?_
  rw [measure_Ioc_eq_max h0, measure_Ioc_eq_max hν0]
  rcases le_or_gt b (max a 0) with hb | hb
  · rw [Ioc_eq_empty (not_lt.mpr hb), measure_empty, measure_empty]
  rcases eq_or_lt_of_le (le_max_right a 0) with h | h
  · rw [← h]; exact hzero b
  · exact hpos _ _ h hb.le

end AffineHemigroup
