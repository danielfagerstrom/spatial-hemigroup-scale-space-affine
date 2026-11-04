/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Origin
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# `lem:threshold-monotone`: the thresholds `w_d` are strictly decreasing

Blueprint: `blueprint/src/parts/03-isotropic.tex`, `lem:threshold-monotone` (wave 1, group D,
Q-0281). The one-variable analysis of `h_d(z) = z^m (e^{-z} - 2^{-d/2} e^{-z/2})`, `m = (d+1)/2`,
for a real parameter `d ≥ 1`:

* `thresholdSup_spec`: `M_d = sup_{z>0} h_d(z)` is finite, positive and attained in `(0, d log 2)`;
* `threshold_pos`: `w_d = Γ(m)/(2M_d) > 0`;
* `thresholdSup_succ`: `M_{d+1} > √m M_d` (the first-order condition at a maximizer of `h_d`, tested
  in dimension `d + 1`) and `w_{d+1} < w_d` (with `Γ(m + 1/2) ≤ √m Γ(m)`, the log-convexity of `Γ`,
  Mathlib's `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`);
* `threshold_strictAnti`: `w_1 > w_2 > ⋯ > 0`.

Lean core only: no ledger entry is read. The closed form of the witness profiles and the criterion
(`lem:threshold-criterion`) are `AffineHemigroup.ThresholdCriterion`.
-/

namespace AffineHemigroup

open Set Real Filter
open scoped Topology

/-! ### The bracket `e^{-z} - 2^{-d/2} e^{-z/2}` and its sign -/

/-- `2^{-d/2} = e^{-(d/2) log 2}`. -/
theorem two_rpow_neg_half_eq (d : ℝ) : (2 : ℝ) ^ (-d / 2) = exp (-(d * log 2) / 2) := by
  rw [rpow_def_of_pos two_pos]; ring_nf

/-- The bracket of `h_d` factors as `e^{-z/2}(e^{-z/2} - 2^{-d/2})`. -/
theorem threshold_bracket_eq (d z : ℝ) :
    exp (-z) - (2 : ℝ) ^ (-d / 2) * exp (-z / 2) =
      exp (-z / 2) * (exp (-z / 2) - (2 : ℝ) ^ (-d / 2)) := by
  have : exp (-z) = exp (-z / 2) * exp (-z / 2) := by rw [← exp_add]; ring_nf
  rw [this]; ring

/-- The bracket is positive below `d log 2`. -/
theorem threshold_bracket_pos {d z : ℝ} (hz : z < d * log 2) :
    0 < exp (-z) - (2 : ℝ) ^ (-d / 2) * exp (-z / 2) := by
  rw [threshold_bracket_eq, two_rpow_neg_half_eq]
  refine mul_pos (exp_pos _) (sub_pos.2 (exp_lt_exp.2 ?_))
  linarith

/-- The bracket is nonpositive from `d log 2` on. -/
theorem threshold_bracket_nonpos {d z : ℝ} (hz : d * log 2 ≤ z) :
    exp (-z) - (2 : ℝ) ^ (-d / 2) * exp (-z / 2) ≤ 0 := by
  rw [threshold_bracket_eq, two_rpow_neg_half_eq]
  refine mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.2 (exp_le_exp.2 ?_))
  linarith

/-- The bracket is at most `e^{-z}`, hence at most `1` for `z ≥ 0`. -/
theorem threshold_bracket_le_one (d : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    exp (-z) - (2 : ℝ) ^ (-d / 2) * exp (-z / 2) ≤ 1 := by
  have h1 : 0 < (2 : ℝ) ^ (-d / 2) * exp (-z / 2) := mul_pos (by positivity) (exp_pos _)
  have h2 : exp (-z) ≤ 1 := exp_le_one_iff.2 (by linarith)
  linarith

/-- `h_d` is continuous for `d ≥ -1`, the exponent `m = (d+1)/2` being nonnegative. -/
theorem continuous_thresholdFun {d : ℝ} (hd : -1 ≤ d) : Continuous (thresholdFun d) := by
  unfold thresholdFun
  exact (continuous_rpow_const (by linarith)).mul
    ((continuous_exp.comp continuous_neg).sub
      (continuous_const.mul (continuous_exp.comp (continuous_neg.div_const _))))

/-- `h_d(z) ≤ z^m` for `z ≥ 0`. -/
theorem thresholdFun_le_rpow (d : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    thresholdFun d z ≤ z ^ ((d + 1) / 2) := by
  unfold thresholdFun
  have := threshold_bracket_le_one d hz
  have h0 : 0 ≤ z ^ ((d + 1) / 2) := rpow_nonneg hz _
  nlinarith

/-- `h_d(z) > 0` on `(0, d log 2)`. -/
theorem thresholdFun_pos {d z : ℝ} (hz : 0 < z) (hz' : z < d * log 2) : 0 < thresholdFun d z :=
  mul_pos (rpow_pos_of_pos hz _) (threshold_bracket_pos hz')

/-- `h_d(z) ≤ 0` on `[d log 2, ∞)`. -/
theorem thresholdFun_nonpos {d z : ℝ} (hz : d * log 2 ≤ z) (hz0 : 0 ≤ z) :
    thresholdFun d z ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (rpow_nonneg hz0 _) (threshold_bracket_nonpos hz)

/-! ### Attainment of the supremum -/

/-- **A maximizer of `h_d` on `(0, ∞)`**, in `(0, d log 2)`, where `h_d` is positive. -/
theorem exists_thresholdFun_max {d : ℝ} (hd : 1 ≤ d) :
    ∃ z ∈ Ioo 0 (d * log 2), 0 < thresholdFun d z ∧
      ∀ y, 0 < y → thresholdFun d y ≤ thresholdFun d z := by
  have hL : 0 < d * log 2 := mul_pos (by linarith) (log_pos one_lt_two)
  set m := (d + 1) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set z0 := d * log 2 / 2 with hz0
  have hz0pos : 0 < z0 := by positivity
  have hz0lt : z0 < d * log 2 := by linarith
  have h0 : 0 < thresholdFun d z0 := thresholdFun_pos hz0pos hz0lt
  set ε := min z0 (thresholdFun d z0 ^ (1 / m)) with hε
  have hεpos : 0 < ε := lt_min hz0pos (rpow_pos_of_pos h0 _)
  have hεle : ε ≤ z0 := min_le_left _ _
  -- below `ε`, `h_d ≤ z^m ≤ ε^m ≤ h_d(z0)`
  have hsmall : ∀ y, 0 < y → y ≤ ε → thresholdFun d y ≤ thresholdFun d z0 := by
    intro y hy hyε
    calc thresholdFun d y ≤ y ^ m := thresholdFun_le_rpow d hy.le
      _ ≤ (thresholdFun d z0 ^ (1 / m)) ^ m :=
          rpow_le_rpow hy.le (hyε.trans (min_le_right _ _)) hm0.le
      _ = thresholdFun d z0 := by
          rw [← rpow_mul h0.le, one_div_mul_cancel hm0.ne', rpow_one]
  have hcont := continuous_thresholdFun (d := d) (by linarith)
  obtain ⟨z, hzK, hzmax⟩ := (isCompact_Icc (a := ε) (b := d * log 2)).exists_isMaxOn
    (nonempty_Icc.2 (hεle.trans hz0lt.le)) hcont.continuousOn
  have hz0K : z0 ∈ Icc ε (d * log 2) := ⟨hεle, hz0lt.le⟩
  have hge : thresholdFun d z0 ≤ thresholdFun d z := hzmax hz0K
  have hzpos : 0 < z := hεpos.trans_le hzK.1
  have hzlt : z < d * log 2 := by
    rcases hzK.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have := thresholdFun_nonpos (d := d) h.ge hzpos.le
      linarith
  refine ⟨z, ⟨hzpos, hzlt⟩, h0.trans_le hge, fun y hy => ?_⟩
  rcases le_or_gt y ε with hyε | hyε
  · exact (hsmall y hy hyε).trans hge
  rcases le_or_gt y (d * log 2) with hyL | hyL
  · exact hzmax ⟨hyε.le, hyL⟩
  · exact (thresholdFun_nonpos hyL.le hy.le).trans (h0.trans_le hge).le

/-- At a maximizer `z` of `h_d` on `(0, ∞)`, `M_d = h_d(z)`. -/
theorem thresholdSup_eq_of_max {d z : ℝ} (hz : 0 < z)
    (hmax : ∀ y, 0 < y → thresholdFun d y ≤ thresholdFun d z) :
    thresholdSup d = thresholdFun d z := by
  unfold thresholdSup
  refine le_antisymm (ciSup_le fun y => hmax y y.2) ?_
  exact le_ciSup (f := fun y : Ioi (0 : ℝ) => thresholdFun d y) ⟨thresholdFun d z,
    by rintro _ ⟨y, rfl⟩; exact hmax y y.2⟩ ⟨z, hz⟩

/-- **`lem:threshold-monotone`**, the supremum: for a real `d ≥ 1`, `M_d = sup_{z>0} h_d(z)` is
finite and positive and is attained at a point of `(0, d log 2)`. -/
theorem thresholdSup_spec (d : ℝ) (hd : 1 ≤ d) :
    BddAbove (range fun z : Ioi (0 : ℝ) => thresholdFun d z) ∧ 0 < thresholdSup d ∧
      ∃ z ∈ Ioo 0 (d * Real.log 2), thresholdFun d z = thresholdSup d := by
  obtain ⟨z, hz, hpos, hmax⟩ := exists_thresholdFun_max hd
  have heq := thresholdSup_eq_of_max hz.1 hmax
  refine ⟨⟨thresholdFun d z, by rintro _ ⟨y, rfl⟩; exact hmax y y.2⟩, heq ▸ hpos, z, hz, heq.symm⟩

/-- `h_d(z) ≤ M_d` for `z > 0` and `d ≥ 1`. -/
theorem thresholdFun_le_thresholdSup {d : ℝ} (hd : 1 ≤ d) {z : ℝ} (hz : 0 < z) :
    thresholdFun d z ≤ thresholdSup d :=
  le_ciSup (f := fun y : Ioi (0 : ℝ) => thresholdFun d y) (thresholdSup_spec d hd).1 ⟨z, hz⟩

/-- **`lem:threshold-monotone`**, consequently: `w_d = Γ(m)/(2M_d)` is a positive number. -/
theorem threshold_pos (d : ℝ) (hd : 1 ≤ d) : 0 < threshold d :=
  div_pos (Gamma_pos_of_pos (by linarith)) (mul_pos two_pos (thresholdSup_spec d hd).2.1)

/-! ### The first-order condition, and the next dimension -/

/-- The derivative of `h_d` at `z > 0`:
`h_d'(z) = m z^{m-1}(e^{-z} - λ e^{-z/2}) + z^m(-e^{-z} + (λ/2) e^{-z/2})`, `λ = 2^{-d/2}`. -/
theorem hasDerivAt_thresholdFun (d : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (thresholdFun d)
      ((d + 1) / 2 * z ^ ((d + 1) / 2 - 1) * (exp (-z) - (2 : ℝ) ^ (-d / 2) * exp (-z / 2)) +
        z ^ ((d + 1) / 2) * (-exp (-z) + (2 : ℝ) ^ (-d / 2) / 2 * exp (-z / 2))) z := by
  have h1 := hasDerivAt_rpow_const (x := z) (p := (d + 1) / 2) (Or.inl hz.ne')
  have h2 : HasDerivAt (fun z => exp (-z)) (-exp (-z)) z := by
    simpa using (hasDerivAt_neg z).exp
  have h3 : HasDerivAt (fun z => exp (-z / 2)) (exp (-z / 2) * (-1 / 2)) z := by
    have := ((hasDerivAt_neg z).div_const 2).exp
    simpa [neg_div] using this
  have h4 := h2.fun_sub (h3.const_mul ((2 : ℝ) ^ (-d / 2)))
  have := h1.fun_mul h4
  exact this.congr_deriv (by ring)

/-- **The step `M_{d+1} > √m M_d`** (`lem:threshold-monotone`, the first-order condition and the
next dimension): at a maximizer `z*` of `h_d`, `q := 2^{-d/2} e^{z*/2} ∈ (0,1)`,
`m(1-q) = z*(1 - q/2)`, and `h_{d+1}(z*) = √(z*)(1 - q/√2) z*^m e^{-z*} > √m M_d`. -/
theorem thresholdSup_succ_gt (d : ℝ) (hd : 1 ≤ d) :
    Real.sqrt ((d + 1) / 2) * thresholdSup d < thresholdSup (d + 1) := by
  obtain ⟨z, hz, hpos, hmax⟩ := exists_thresholdFun_max hd
  have hM := thresholdSup_eq_of_max hz.1 hmax
  set m := (d + 1) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hz0 := hz.1
  -- the first-order condition
  have hloc : IsLocalMax (thresholdFun d) z :=
    Filter.eventually_of_mem (Ioi_mem_nhds hz0) fun y hy => hmax y hy
  have hderiv := hloc.hasDerivAt_eq_zero (hasDerivAt_thresholdFun d hz0)
  set lam := (2 : ℝ) ^ (-d / 2) with hlam
  set F := exp (-z / 2) with hF
  have hFpos : 0 < F := exp_pos _
  have hE : exp (-z) = F * F := by rw [hF, ← exp_add]; ring_nf
  set q := lam / F with hq
  have hlamF : lam = q * F := by rw [hq]; field_simp
  have hlampos : 0 < lam := by positivity
  have hqpos : 0 < q := div_pos hlampos hFpos
  have hbr : 0 < exp (-z) - lam * exp (-z / 2) := threshold_bracket_pos hz.2
  have hq1 : q < 1 := by
    rw [hE, hlamF] at hbr
    nlinarith [mul_pos hFpos hFpos]
  set P := z ^ (m - 1) with hP
  have hPpos : 0 < P := rpow_pos_of_pos hz0 _
  have hzm : z ^ m = z * P := by
    rw [hP, ← rpow_one_add' hz0.le (by ring_nf; exact hm0.ne')]
    ring_nf
  -- `m (1 - q) = z (1 - q/2)`
  have hfoc : m * (1 - q) = z * (1 - q / 2) := by
    rw [hE, hlamF, hzm] at hderiv
    have hPF : 0 < P * (F * F) := by positivity
    have : P * (F * F) * (m * (1 - q) - z * (1 - q / 2)) = 0 := by
      rw [← hderiv]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hPF.ne'
    · linarith
  -- `M_d = z^m F² (1 - q)`
  have hMd : thresholdSup d = z ^ m * (F * F) * (1 - q) := by
    rw [hM]; unfold thresholdFun
    rw [← hm, ← hlam, hE, ← hF, hlamF]; ring
  -- `h_{d+1}(z) = √z z^m F² (1 - q/√2)`
  set s := Real.sqrt 2 with hs
  have hs0 : 0 < s := by positivity
  have hss : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs32 : s < 3 / 2 := by nlinarith
  have hs1 : 1 < s := by nlinarith
  have hnext : thresholdFun (d + 1) z = Real.sqrt z * (z ^ m * (F * F) * (1 - q / s)) := by
    unfold thresholdFun
    have e1 : z ^ ((d + 1 + 1) / 2) = z ^ m * Real.sqrt z := by
      rw [Real.sqrt_eq_rpow, ← rpow_add hz0, hm]; ring_nf
    have e2 : (2 : ℝ) ^ (-(d + 1) / 2) = lam / s := by
      rw [hlam, hs, Real.sqrt_eq_rpow, eq_div_iff (by positivity), ← rpow_add two_pos]
      ring_nf
    rw [e1, e2, hE, ← hF, hlamF]
    field_simp
  have hMnext : thresholdFun (d + 1) z ≤ thresholdSup (d + 1) :=
    thresholdFun_le_thresholdSup (by linarith) hz0
  refine lt_of_lt_of_le ?_ hMnext
  rw [hnext, hMd]
  -- `√m (1 - q) < √z (1 - q/√2)`, by squaring
  have hA : 0 < z ^ m * (F * F) := by positivity
  have hkey : Real.sqrt m * (1 - q) < Real.sqrt z * (1 - q / s) := by
    have hqs : 0 < 1 - q / s := by
      rw [sub_pos, div_lt_one hs0]; linarith
    have hrhs : 0 ≤ Real.sqrt z * (1 - q / s) := by positivity
    refine lt_of_pow_lt_pow_left₀ 2 hrhs ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le, Real.sq_sqrt hz0.le]
    have h1 : (1 - q / s) ^ 2 = 1 - q * s + q ^ 2 / 2 := by
      have hinv : q / s = q * (s / 2) := by
        field_simp; linarith [hss]
      have e : (1 - q * (s / 2)) ^ 2 = 1 - q * s + q ^ 2 * (s * s) / 4 := by ring
      rw [hinv, e, hss]; ring
    rw [h1]
    have : m * (1 - q) ^ 2 = z * (1 - q / 2) * (1 - q) := by rw [← hfoc]; ring
    rw [this]
    have hpos := mul_pos (mul_pos hz0 hqpos) (sub_pos.2 hs32)
    linarith [hpos]
  calc Real.sqrt m * (z ^ m * (F * F) * (1 - q))
      = (Real.sqrt m * (1 - q)) * (z ^ m * (F * F)) := by ring
    _ < (Real.sqrt z * (1 - q / s)) * (z ^ m * (F * F)) := mul_lt_mul_of_pos_right hkey hA
    _ = Real.sqrt z * (z ^ m * (F * F) * (1 - q / s)) := by ring

/-- `Γ(m + 1/2) ≤ √m Γ(m)` for `m > 0`: the log-convexity of `Γ` at `m` and `m + 1`
(Mathlib's `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`) and `Γ(m+1) = mΓ(m)`. -/
theorem Gamma_add_half_le {m : ℝ} (hm : 0 < m) :
    Gamma (m + 1 / 2) ≤ Real.sqrt m * Gamma m := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hm (by linarith : 0 < m + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG := Gamma_pos_of_pos hm
  rw [Gamma_add_one hm.ne', mul_rpow hm.le hG.le, ← mul_assoc, mul_comm (Gamma m ^ _),
    mul_assoc, ← rpow_add hG] at h
  convert h using 2
  · ring
  · rw [Real.sqrt_eq_rpow]
  · norm_num

/-- **`lem:threshold-monotone`**, the step: `M_{d+1} > √m M_d` and `w_{d+1} < w_d`, `m = (d+1)/2`,
for every real `d ≥ 1`. -/
theorem thresholdSup_succ (d : ℝ) (hd : 1 ≤ d) :
    Real.sqrt ((d + 1) / 2) * thresholdSup d < thresholdSup (d + 1) ∧
      threshold (d + 1) < threshold d := by
  have hstep := thresholdSup_succ_gt d hd
  refine ⟨hstep, ?_⟩
  set m := (d + 1) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hMd := (thresholdSup_spec d hd).2.1
  have hMd' := (thresholdSup_spec (d + 1) (by linarith)).2.1
  have hG := Gamma_pos_of_pos hm0
  have hGam := Gamma_add_half_le hm0
  unfold threshold
  have e : (d + 1 + 1) / 2 = m + 1 / 2 := by rw [hm]; ring
  rw [e, ← hm, div_lt_div_iff₀ (by positivity) (by positivity)]
  calc Gamma (m + 1 / 2) * (2 * thresholdSup d)
      ≤ Real.sqrt m * Gamma m * (2 * thresholdSup d) :=
        mul_le_mul_of_nonneg_right hGam (by positivity)
    _ = Gamma m * 2 * (Real.sqrt m * thresholdSup d) := by ring
    _ < Gamma m * 2 * thresholdSup (d + 1) := mul_lt_mul_of_pos_left hstep (by positivity)
    _ = Gamma m * (2 * thresholdSup (d + 1)) := by ring

/-- **`lem:threshold-monotone`**, in particular: `w_1 > w_2 > ⋯ > 0`, and `(w_{d+1}, w_d]` is a
nonempty interval for every integer `d ≥ 1`. -/
theorem threshold_strictAnti :
    StrictAntiOn (fun n : ℕ => threshold n) (Ici 1) ∧ (∀ n : ℕ, 1 ≤ n → 0 < threshold n) ∧
      ∀ n : ℕ, 1 ≤ n → (Ioc (threshold ((n : ℝ) + 1)) (threshold n)).Nonempty := by
  have hstep : ∀ n : ℕ, 1 ≤ n → threshold ((n + 1 : ℕ) : ℝ) < threshold n := by
    intro n hn
    have := (thresholdSup_succ (n : ℝ) (by exact_mod_cast hn)).2
    simpa using this
  refine ⟨?_, fun n hn => threshold_pos n (by exact_mod_cast hn), fun n hn => ?_⟩
  · intro i hi j hj hij
    clear hj
    simp only
    induction j, hij using Nat.le_induction with
    | base => exact hstep i hi
    | succ k hk ih => exact (hstep k (le_trans hi (by omega))).trans ih
  · exact ⟨threshold n, by simpa using hstep n hn, le_rfl⟩

end AffineHemigroup
