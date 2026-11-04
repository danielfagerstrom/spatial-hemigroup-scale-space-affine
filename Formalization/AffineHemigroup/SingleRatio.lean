/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# `lem:single-ratio-cauchy` — one ratio forces linearity

Blueprint: `blueprint/src/parts/04-classical.tex`, `lem:single-ratio-cauchy`. Real analysis on
`ℝ`; Lean core only. The statement mentions only Mathlib types (a second-demand candidate).

## The route

The blueprint's, with one simplification in the third step: instead of telescoping over the
dyadic points, put `h(δ) := g(δ) - K(δ)`; then `h(2ε) = h(ε)`, so `h(δ) = h(δ/2ⁿ)
= g(δ/2ⁿ) - K(δ)/2ⁿ → 0` by continuity at `0`. The last step squeezes `n g(x)` between
`⌊nx⌋ g(1)` and `(⌊nx⌋ + 1) g(1)`, which is the monotone squeeze of the blueprint with the
rationals `⌊nx⌋/n`.
-/

namespace AffineHemigroup

open Set Filter Topology

/-- **`lem:single-ratio-cauchy`**: `g ≥ 0` on `[0,∞)`, continuous at `0`, `g(0) = 0`, and one
`a > 1` with `g(au + w) - g(u + w) = g(au) - g(u)` for `u > 0`, `w ≥ 0`, give `g(u) = bu` with
`b = g(1) ≥ 0`. -/
theorem single_ratio_cauchy (g : ℝ → ℝ) (hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u)
    (hg_cont : ContinuousWithinAt g (Ici 0) 0) (hg_zero : g 0 = 0) (a : ℝ) (ha : 1 < a)
    (hratio : ∀ u w : ℝ, 0 < u → 0 ≤ w → g (a * u + w) - g (u + w) = g (a * u) - g u) :
    (∀ u : ℝ, 0 ≤ u → g u = g 1 * u) ∧ 0 ≤ g 1 := by
  have ha1 : 0 < a - 1 := by linarith
  -- the increment `κ(δ)` at the base point `u_δ = δ/(a-1)`
  set κ : ℝ → ℝ := fun δ => g (δ / (a - 1) + δ) - g (δ / (a - 1)) with hκ
  /- A constant difference on a half-line. -/
  have step1 : ∀ δ : ℝ, 0 < δ → ∀ x : ℝ, δ / (a - 1) ≤ x → g (x + δ) - g x = κ δ := by
    intro δ hδ x hx
    have hu : 0 < δ / (a - 1) := div_pos hδ ha1
    have hau : a * (δ / (a - 1)) = δ / (a - 1) + δ := by
      field_simp
      ring
    have h := hratio (δ / (a - 1)) (x - δ / (a - 1)) hu (by linarith)
    rw [hau] at h
    have e1 : δ / (a - 1) + δ + (x - δ / (a - 1)) = x + δ := by ring
    have e2 : δ / (a - 1) + (x - δ / (a - 1)) = x := by ring
    rw [e1, e2] at h
    exact h
  /- Telescoping over `n` equal steps. -/
  have tele : ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 ≤ y → (δ / n) / (a - 1) ≤ y →
      g (y + δ) - g y = n * κ (δ / n) := by
    intro δ hδ n hn y hy hyb
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hδn : 0 < δ / n := div_pos hδ hn'
    have hsum := Finset.sum_range_sub (fun i : ℕ => g (y + i * (δ / n))) n
    have hterm : ∀ i ∈ Finset.range n,
        g (y + ((i + 1 : ℕ) : ℝ) * (δ / n)) - g (y + (i : ℝ) * (δ / n)) = κ (δ / n) := by
      intro i _
      have hx : (δ / n) / (a - 1) ≤ y + (i : ℝ) * (δ / n) := by
        have : 0 ≤ (i : ℝ) * (δ / n) := mul_nonneg (Nat.cast_nonneg i) hδn.le
        linarith
      have h := step1 (δ / n) hδn (y + (i : ℝ) * (δ / n)) hx
      have e : y + ((i + 1 : ℕ) : ℝ) * (δ / n) = y + (i : ℝ) * (δ / n) + δ / n := by
        push_cast
        ring
      rw [e]
      exact h
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have e1 : y + (n : ℝ) * (δ / n) = y + δ := by
      field_simp
    have e2 : y + ((0 : ℕ) : ℝ) * (δ / n) = y := by simp
    rw [e1, e2] at hsum
    exact hsum.symm
  /- The difference `g(y + δ) - g(y)` does not depend on `y > 0`. -/
  have step2 : ∀ δ : ℝ, 0 < δ → ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      g (y₁ + δ) - g y₁ = g (y₂ + δ) - g y₂ := by
    intro δ hδ y₁ y₂ h₁ h₂
    set y := min y₁ y₂ with hy
    have hy0 : 0 < y := lt_min h₁ h₂
    obtain ⟨n, hn⟩ := exists_nat_gt (δ / ((a - 1) * y))
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    have hnpos : 0 < n := Nat.cast_pos.1 hn0
    have hb : (δ / n) / (a - 1) ≤ y := by
      rw [div_div, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith
    rw [tele δ hδ n hnpos y₁ h₁.le (hb.trans (min_le_left _ _)),
      tele δ hδ n hnpos y₂ h₂.le (hb.trans (min_le_right _ _))]
  set K : ℝ → ℝ := fun δ => g (1 + δ) - g 1 with hK
  have hKy : ∀ δ : ℝ, 0 < δ → ∀ y : ℝ, 0 < y → g (y + δ) - g y = K δ := by
    intro δ hδ y hy
    exact step2 δ hδ y 1 hy one_pos
  have hK2 : ∀ ε : ℝ, 0 < ε → K (2 * ε) = 2 * K ε := by
    intro ε hε
    have h1 := hKy ε hε (1 + ε) (by linarith)
    have h2 := hKy ε hε 1 one_pos
    simp only [hK] at h1 h2 ⊢
    have e : 1 + 2 * ε = 1 + ε + ε := by ring
    rw [e]
    linarith
  /- Additivity, from continuity at `0` alone. -/
  have hadd : ∀ δ : ℝ, 0 < δ → g δ = K δ := by
    intro δ hδ
    set h : ℝ → ℝ := fun x => g x - K x with hh
    have hhalf : ∀ ε : ℝ, 0 < ε → h (2 * ε) = h ε := by
      intro ε hε
      have h1 := hKy ε hε ε hε
      have e : ε + ε = 2 * ε := by ring
      rw [e] at h1
      simp only [hh]
      rw [hK2 ε hε]
      linarith
    have hpow : ∀ n : ℕ, h δ = h (δ / 2 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih]
        have hpos : 0 < δ / 2 ^ (n + 1) := by positivity
        have e : δ / 2 ^ n = 2 * (δ / 2 ^ (n + 1)) := by
          rw [pow_succ]
          field_simp
        rw [e, hhalf _ hpos]
    have hKpow : ∀ n : ℕ, K δ = 2 ^ n * K (δ / 2 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih]
        have hpos : 0 < δ / 2 ^ (n + 1) := by positivity
        have e : δ / 2 ^ n = 2 * (δ / 2 ^ (n + 1)) := by
          rw [pow_succ]
          field_simp
        rw [e, hK2 _ hpos, pow_succ]
        ring
    -- `h (δ / 2ⁿ) = g (δ / 2ⁿ) - K δ / 2ⁿ → 0`
    have hseq : ∀ n : ℕ, h δ = g (δ * (1 / 2) ^ n) - K δ * (1 / 2) ^ n := by
      intro n
      have e : δ * (1 / 2 : ℝ) ^ n = δ / 2 ^ n := by
        rw [one_div_pow, mul_one_div]
      rw [e, hpow n]
      simp only [hh]
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      rw [hKpow n, one_div_pow]
      field_simp
    have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hargs : Tendsto (fun n : ℕ => δ * (1 / 2 : ℝ) ^ n) atTop (𝓝[Ici 0] 0) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa using hgeo.const_mul δ
      · exact mem_Ici.2 (by positivity)
    have hlim : Tendsto (fun n : ℕ => g (δ * (1 / 2) ^ n) - K δ * (1 / 2) ^ n) atTop
        (𝓝 (0 - K δ * 0)) := by
      have hg := hg_cont.tendsto.comp hargs
      rw [hg_zero] at hg
      exact hg.sub (hgeo.const_mul (K δ))
    simp only [mul_zero, sub_zero] at hlim
    have hconst : Tendsto (fun n : ℕ => g (δ * (1 / 2) ^ n) - K δ * (1 / 2) ^ n) atTop
        (𝓝 (h δ)) := by
      have : (fun n : ℕ => g (δ * (1 / 2) ^ n) - K δ * (1 / 2) ^ n) = fun _ => h δ := by
        funext n
        exact (hseq n).symm
      rw [this]
      exact tendsto_const_nhds
    have h0 : h δ = 0 := tendsto_nhds_unique hconst hlim
    simp only [hh] at h0
    linarith
  have hadd' : ∀ y δ : ℝ, 0 < y → 0 < δ → g (y + δ) = g y + g δ := by
    intro y δ hy hδ
    have := hKy δ hδ y hy
    rw [hadd δ hδ]
    linarith
  /- Cauchy's equation, by a monotone squeeze. -/
  have hmono : ∀ x x' : ℝ, 0 ≤ x → x ≤ x' → g x ≤ g x' := by
    intro x x' hx hxx'
    rcases eq_or_lt_of_le hx with rfl | hx0
    · rw [hg_zero]
      exact hg_nonneg x' (le_trans hx hxx')
    rcases eq_or_lt_of_le hxx' with rfl | hlt
    · exact le_rfl
    · have e : x' = x + (x' - x) := by ring
      rw [e, hadd' x (x' - x) hx0 (by linarith)]
      linarith [hg_nonneg (x' - x) (by linarith)]
  have hnat : ∀ n : ℕ, g n = n * g 1 := by
    intro n
    induction n with
    | zero => simp [hg_zero]
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · push_cast
        rw [hadd' (n : ℝ) 1 (Nat.cast_pos.2 hn) one_pos, ih]
        ring
  have hmul : ∀ x : ℝ, 0 < x → ∀ n : ℕ, g (n * x) = n * g x := by
    intro x hx n
    induction n with
    | zero => simp [hg_zero]
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · push_cast
        have e : ((n : ℝ) + 1) * x = n * x + x := by ring
        rw [e, hadd' (n * x) x (mul_pos (Nat.cast_pos.2 hn) hx) hx, ih]
        ring
  have hg1 : 0 ≤ g 1 := hg_nonneg 1 zero_le_one
  have hpos : ∀ x : ℝ, 0 < x → g x = g 1 * x := by
    intro x hx
    have hbound : ∀ n : ℕ, 0 < n → (n : ℝ) * |g x - x * g 1| ≤ g 1 := by
      intro n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      have hnx : 0 ≤ (n : ℝ) * x := by positivity
      set m := ⌊(n : ℝ) * x⌋₊ with hm
      have hm1 : (m : ℝ) ≤ n * x := Nat.floor_le hnx
      have hm2 : (n : ℝ) * x < m + 1 := Nat.lt_floor_add_one _
      have hlo : (m : ℝ) * g 1 ≤ n * g x := by
        rw [← hnat m, ← hmul x hx n]
        exact hmono _ _ (Nat.cast_nonneg m) hm1
      have hhi : (n : ℝ) * g x ≤ (m + 1) * g 1 := by
        have : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [← this, ← hnat (m + 1), ← hmul x hx n]
        exact hmono _ _ hnx (by rw [this]; exact hm2.le)
      have hlo' : (m : ℝ) * g 1 ≤ n * x * g 1 := mul_le_mul_of_nonneg_right hm1 hg1
      have hhi' : (n : ℝ) * x * g 1 ≤ (m + 1) * g 1 := mul_le_mul_of_nonneg_right hm2.le hg1
      rw [← abs_of_pos hn', ← abs_mul, abs_le]
      constructor <;> nlinarith
    by_contra hne
    have he : 0 < |g x - x * g 1| := abs_pos.2 (sub_ne_zero.2 (by
      intro h
      apply hne
      rw [h]
      ring))
    obtain ⟨n, hn⟩ := exists_nat_gt (g 1 / |g x - x * g 1|)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hg1 he.le) hn
    have := hbound n (Nat.cast_pos.1 hn0)
    rw [div_lt_iff₀ he] at hn
    linarith
  refine ⟨fun u hu => ?_, hg1⟩
  rcases eq_or_lt_of_le hu with rfl | hu0
  · simp [hg_zero]
  · exact hpos u hu0

end AffineHemigroup
