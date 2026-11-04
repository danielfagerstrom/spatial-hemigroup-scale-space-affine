/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.FiltrationStrict
import AffineHemigroup.ThresholdLimit
import AffineHemigroup.ThresholdAsymptotic

/-!
# `thm:separating-family-critical-values`: the separating family and its critical values

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `thm:separating-family-critical-values`
(Q-0429). One theorem for the family `F^{(w)}`, `w > 0`, of `def:filtration-thresholds`
(`witnessF w`) and its critical values `w_1, w_2, …` (`threshold n` at the integers `n ≥ 1`;
`threshold` is the function of a real parameter of `lem:threshold-monotone`).

The module is an assembly: every clause is a statement of the library read at the integers.

* Clause (1), `witness_classA_iff`: `F^{(w)} ∈ 𝒜_D ↔ w ≤ w_D`, the two steps of
  `thm:filtration-strict`(1) (`witness_classA`, `witness_not_classA`), each of which reads one
  inequality. Spends A2, A3, A4.
* Clause (2), `criticalValues_strictAnti`: `threshold_strictAnti`. Lean core.
* Clause (3), `criticalValues_tendsto`: `threshold_asymptotic` along the reals, composed with the
  cast `ℕ → ℝ`. Lean core.
* Clause (4): the window `witness_classA_iff_le`, the case above `w_1`
  `witness_not_classA_of_gt`, the one interval `criticalValues_existsUnique_window` (Lean core,
  from `threshold_limit`: the least `n ≥ 1` with `w_n < w` exists), and the strict inclusion
  `separating_family_strict` (the nesting is `filtration_strict`).
* The bundle `separating_family_critical_values` states the four clauses as one proposition.

The next critical value after `w_d` is written `threshold ((d + 1 : ℕ) : ℝ)`, the function at the
integer `d + 1`; `filtration_witness` writes the same number `threshold ((d : ℝ) + 1)`.
-/

namespace AffineHemigroup

open Set Filter
open scoped Topology

/-- **`thm:separating-family-critical-values`(1), membership**: for an integer `D ≥ 1` and
`w > 0`, `F^{(w)} ∈ 𝒜_D` if and only if `w ≤ w_D`. -/
theorem witness_classA_iff {D : ℕ} (hD : 1 ≤ D) {w : ℝ} (hw : 0 < w) :
    classA D (witnessF w) ↔ w ≤ threshold D :=
  ⟨fun h => not_lt.1 fun hlt => witness_not_classA hD hw hlt h, witness_classA hD hw⟩

/-- **`thm:separating-family-critical-values`(2)**: `w_1 > w_2 > w_3 > ⋯ > 0`, the critical
values at the integers decrease strictly and are positive. -/
theorem criticalValues_strictAnti :
    StrictAntiOn (fun n : ℕ => threshold n) (Ici 1) ∧ ∀ n : ℕ, 1 ≤ n → 0 < threshold n :=
  ⟨threshold_strictAnti.1, threshold_strictAnti.2.1⟩

/-- **`thm:separating-family-critical-values`(3)**: `√D · w_D → √π` as `D → ∞` along the
integers. -/
theorem criticalValues_tendsto :
    Tendsto (fun D : ℕ => Real.sqrt D * threshold D) atTop (𝓝 (Real.sqrt Real.pi)) :=
  threshold_asymptotic.2.comp tendsto_natCast_atTop_atTop

/-- The critical values at two integers `1 ≤ i ≤ j`: `w_j ≤ w_i`. -/
theorem threshold_natCast_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    threshold (j : ℝ) ≤ threshold (i : ℝ) :=
  threshold_strictAnti.1.antitoneOn (mem_Ici.2 hi) (mem_Ici.2 (hi.trans hij)) hij

/-- **`thm:separating-family-critical-values`(4), the window**: for an integer `d ≥ 1` and
`w ∈ (w_{d+1}, w_d]`, `F^{(w)} ∈ 𝒜_D` for `D = 1, …, d` and for no `D > d`: for every integer
`D ≥ 1`, `F^{(w)} ∈ 𝒜_D` if and only if `D ≤ d`. -/
theorem witness_classA_iff_le {d : ℕ} (hd : 1 ≤ d) {w : ℝ}
    (hw1 : threshold ((d + 1 : ℕ) : ℝ) < w) (hw2 : w ≤ threshold d) {D : ℕ} (hD : 1 ≤ D) :
    classA D (witnessF w) ↔ D ≤ d := by
  have hw : 0 < w := (threshold_strictAnti.2.1 (d + 1) (by omega)).trans hw1
  rw [witness_classA_iff hD hw]
  constructor
  · intro h
    by_contra hcon
    have h1 : threshold (D : ℝ) ≤ threshold ((d + 1 : ℕ) : ℝ) :=
      threshold_natCast_le (by omega) (by omega)
    linarith
  · intro h
    exact hw2.trans (threshold_natCast_le hD h)

/-- **`thm:separating-family-critical-values`(4), above the first critical value**: for
`w > w_1`, `F^{(w)}` belongs to no `𝒜_D`, `D ≥ 1`. -/
theorem witness_not_classA_of_gt {w : ℝ} (hw1 : threshold ((1 : ℕ) : ℝ) < w) {D : ℕ}
    (hD : 1 ≤ D) : ¬ classA D (witnessF w) := by
  have hw : 0 < w := (threshold_strictAnti.2.1 1 le_rfl).trans hw1
  rw [witness_classA_iff hD hw, not_le]
  exact (threshold_natCast_le le_rfl hD).trans_lt hw1

/-- **`thm:separating-family-critical-values`(4), exactly one interval**: every
`w ∈ (0, w_1]` lies in exactly one of the intervals `(w_{d+1}, w_d]`, `d ≥ 1`. The integer is
the largest `d` with `w ≤ w_d`, which exists because `w_d → 0` (`lem:threshold-limit`). -/
theorem criticalValues_existsUnique_window {w : ℝ} (hw : 0 < w)
    (hw1 : w ≤ threshold ((1 : ℕ) : ℝ)) :
    ∃! d : ℕ, 1 ≤ d ∧ threshold ((d + 1 : ℕ) : ℝ) < w ∧ w ≤ threshold d := by
  classical
  -- some critical value is below `w`
  have hex : ∃ n : ℕ, 1 ≤ n ∧ threshold (n : ℝ) < w := by
    obtain ⟨D, hD⟩ := threshold_limit.2.2.2.2.2.2 w hw
    obtain ⟨n, hn⟩ := exists_nat_ge D
    exact ⟨n + 1, by omega, hD _ (hn.trans (by push_cast; linarith))⟩
  -- the least such index
  set N := Nat.find hex with hN
  obtain ⟨hN1, hNw⟩ := Nat.find_spec hex
  have hN2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h | h
    · have h1 : N = 1 := by omega
      rw [← hN, h1] at hNw
      exact absurd hNw (not_lt.2 hw1)
    · exact h
  have hmin : w ≤ threshold ((N - 1 : ℕ) : ℝ) := by
    by_contra hcon
    exact Nat.find_min hex (show N - 1 < N by omega) ⟨by omega, not_le.1 hcon⟩
  refine ⟨N - 1, ⟨by omega, ?_, hmin⟩, ?_⟩
  · rw [show N - 1 + 1 = N by omega]; exact hNw
  · rintro d' ⟨hd'1, hd'2, hd'3⟩
    -- two windows that both hold `w` have the same index
    rcases lt_trichotomy d' (N - 1) with hlt | heq | hgt
    · have h1 : threshold ((N - 1 : ℕ) : ℝ) ≤ threshold ((d' + 1 : ℕ) : ℝ) :=
        threshold_natCast_le (by omega) (by omega)
      linarith
    · exact heq
    · have h1 : threshold (d' : ℝ) ≤ threshold (N : ℝ) := threshold_natCast_le hN1 (by omega)
      linarith

/-- **`thm:separating-family-critical-values`(4), every step is separated by the family**: for
an integer `d ≥ 1` the interval `(w_{d+1}, w_d]` is nonempty, `𝒜_d ∖ 𝒜_{d+1}` contains a member
of the family, and `𝒜_{d+1} ⊊ 𝒜_d`. -/
theorem separating_family_strict {d : ℕ} (hd : 1 ≤ d) :
    (Ioc (threshold ((d + 1 : ℕ) : ℝ)) (threshold d)).Nonempty ∧
      (∃ w : ℝ, 0 < w ∧ classA d (witnessF w) ∧ ¬ classA (d + 1) (witnessF w)) ∧
      {F : ℝ → ℝ | classA (d + 1) F} ⊂ {F | classA d F} := by
  have hlt : threshold ((d + 1 : ℕ) : ℝ) < threshold d :=
    threshold_strictAnti.1 (mem_Ici.2 hd) (mem_Ici.2 (by omega)) (Nat.lt_succ_self d)
  have hpos : 0 < threshold ((d + 1 : ℕ) : ℝ) := threshold_strictAnti.2.1 (d + 1) (by omega)
  refine ⟨⟨threshold d, hlt, le_rfl⟩, ⟨threshold d, hpos.trans hlt, ?_, ?_⟩,
    filtration_strict.1 d hd⟩
  · exact (witness_classA_iff_le hd hlt le_rfl hd).2 le_rfl
  · rw [witness_classA_iff_le hd hlt le_rfl (show 1 ≤ d + 1 by omega)]
    omega

/-- **`thm:separating-family-critical-values`**, the four clauses as one statement. (1) For
every integer `D ≥ 1` and every `w > 0`, `F^{(w)} ∈ 𝒜_D ↔ w ≤ w_D`. (2) The critical values at
the integers decrease strictly and are positive. (3) `√D · w_D → √π` along the integers. (4) For
`w ∈ (w_{d+1}, w_d]`, `F^{(w)} ∈ 𝒜_D ↔ D ≤ d` for every integer `D ≥ 1`; for `w > w_1`,
`F^{(w)}` is in no `𝒜_D`; every `w ∈ (0, w_1]` is in exactly one interval; every interval is
nonempty, `𝒜_d ∖ 𝒜_{d+1}` contains a member of the family, and `𝒜_{d+1} ⊊ 𝒜_d`. -/
theorem separating_family_critical_values :
    (∀ D : ℕ, 1 ≤ D → ∀ w : ℝ, 0 < w → (classA D (witnessF w) ↔ w ≤ threshold D)) ∧
      (StrictAntiOn (fun n : ℕ => threshold n) (Ici 1) ∧ ∀ n : ℕ, 1 ≤ n → 0 < threshold n) ∧
      Tendsto (fun D : ℕ => Real.sqrt D * threshold D) atTop (𝓝 (Real.sqrt Real.pi)) ∧
      (∀ d : ℕ, 1 ≤ d → ∀ w : ℝ, threshold ((d + 1 : ℕ) : ℝ) < w → w ≤ threshold d →
        ∀ D : ℕ, 1 ≤ D → (classA D (witnessF w) ↔ D ≤ d)) ∧
      (∀ w : ℝ, threshold ((1 : ℕ) : ℝ) < w → ∀ D : ℕ, 1 ≤ D → ¬ classA D (witnessF w)) ∧
      (∀ w : ℝ, 0 < w → w ≤ threshold ((1 : ℕ) : ℝ) →
        ∃! d : ℕ, 1 ≤ d ∧ threshold ((d + 1 : ℕ) : ℝ) < w ∧ w ≤ threshold d) ∧
      ∀ d : ℕ, 1 ≤ d → (Ioc (threshold ((d + 1 : ℕ) : ℝ)) (threshold d)).Nonempty ∧
        (∃ w : ℝ, 0 < w ∧ classA d (witnessF w) ∧ ¬ classA (d + 1) (witnessF w)) ∧
        {F : ℝ → ℝ | classA (d + 1) F} ⊂ {F | classA d F} :=
  ⟨fun _ hD _ hw => witness_classA_iff hD hw, criticalValues_strictAnti, criticalValues_tendsto,
    fun _ hd _ hw1 hw2 _ hD => witness_classA_iff_le hd hw1 hw2 hD,
    fun _ hw1 _ hD => witness_not_classA_of_gt hw1 hD,
    fun _ hw hw1 => criticalValues_existsUnique_window hw hw1,
    fun _ hd => separating_family_strict hd⟩

end AffineHemigroup
