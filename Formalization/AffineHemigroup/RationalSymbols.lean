/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.OrbitRays
import Mathlib.Analysis.Polynomial.Basic

/-!
# `prop:rational-symbols`: rational symbols cascade along rays only

Blueprint: `blueprint/src/parts/05-orbits.tex`, `prop:rational-symbols`. Wave 2, group C, Q-0281.
Lean core.

## The route

The blueprint's. `P/Q` keeps one sign on `[0,∞)` (intermediate values for `PQ`); `g ≥ 0` because a
characteristic function has modulus at most `1`; the asymptotics `g(cu) - g(u) → (p - q) log c` are
Mathlib's limit of a quotient of two polynomials of one degree, applied to `P(c·)/P` and `Q(c·)/Q`;
`prop:log-orbit-rays` and the sign of a ray step (`one_le_of_ray_increment`) give `Σ' = cΣ`,
`c ≥ 1`. The examples are built from the Matérn laws `gammaGaussLaw` of `prop:affine-orbits`(4):
scaled copies of the index-`1` law, convolved (products) or mixed (mixtures).
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix Polynomial
open scoped Topology MatrixOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## The main statement -/

/-- A real polynomial without zeros on `[0,∞)` keeps the sign of `P(0)` there, so `P(0)P(u) > 0`. -/
theorem eval_mul_eval_zero_pos {P : Polynomial ℝ} (hP : ∀ u : ℝ, 0 ≤ u → P.eval u ≠ 0) {u : ℝ}
    (hu : 0 ≤ u) : 0 < P.eval 0 * P.eval u := by
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn (fun x => P.eval 0 * P.eval x) (Icc 0 u) :=
    (continuous_const.mul P.continuous).continuousOn
  have h0 : 0 < P.eval 0 * P.eval 0 := mul_self_pos.2 (hP 0 le_rfl)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hu hcont ⟨hneg, h0.le⟩
  exact hP c hc.1 ((mul_eq_zero.1 hc0).resolve_left (hP 0 le_rfl))

/-- For a rational symbol pair, `P(u)/Q(u) > 0` on `[0,∞)`. -/
theorem IsRationalSymbolPair.div_pos {P Q : Polynomial ℝ} (hPQ : IsRationalSymbolPair P Q)
    {u : ℝ} (hu : 0 ≤ u) : 0 < P.eval u / Q.eval u := by
  obtain ⟨-, h0, hP, hQ⟩ := hPQ
  have h1 := eval_mul_eval_zero_pos hP hu
  have h2 := eval_mul_eval_zero_pos hQ hu
  rw [h0] at h1
  have h3 : 0 < (Q.eval 0 * P.eval u) * (Q.eval 0 * Q.eval u) := mul_pos h1 h2
  have h4 : 0 < P.eval u * Q.eval u := by
    have : (Q.eval 0 * P.eval u) * (Q.eval 0 * Q.eval u) =
        (Q.eval 0) ^ 2 * (P.eval u * Q.eval u) := by ring
    rw [this] at h3
    exact pos_of_mul_pos_right h3 (sq_nonneg _)
  rcases lt_or_gt_of_ne (hQ u hu) with hq | hq
  · exact div_pos_of_neg_of_neg (by nlinarith) hq
  · exact _root_.div_pos (by nlinarith) hq

/-- `P(cu)/P(u) → c^{deg P}` as `u → ∞`, for `P ≠ 0` and `c > 0`. -/
theorem tendsto_eval_mul_div_eval {P : Polynomial ℝ} (hP : P ≠ 0) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u => P.eval (c * u) / P.eval u) atTop (𝓝 (c ^ P.natDegree)) := by
  set P' := P.comp (C c * X) with hP'
  have hq : (C c * X : Polynomial ℝ).natDegree = 1 := natDegree_C_mul_X c hc.ne'
  have hlcP' : P'.leadingCoeff = P.leadingCoeff * c ^ P.natDegree := by
    rw [hP', leadingCoeff_comp (by rw [hq]; exact one_ne_zero), leadingCoeff_C_mul_X]
  have hP'ne : P' ≠ 0 := by
    intro h0
    have := congrArg leadingCoeff h0
    rw [hlcP', leadingCoeff_zero] at this
    exact mul_ne_zero (leadingCoeff_ne_zero.2 hP) (pow_ne_zero _ hc.ne') this
  have hdeg : P'.degree = P.degree := by
    rw [degree_eq_natDegree hP'ne, degree_eq_natDegree hP, hP', natDegree_comp, hq, mul_one]
  have h := div_tendsto_atTop_leadingCoeff_div_of_degree_eq (P := P') (Q := P) hdeg
  have hlc : P'.leadingCoeff / P.leadingCoeff = c ^ P.natDegree := by
    rw [hlcP', mul_comm, mul_div_assoc, div_self (leadingCoeff_ne_zero.2 hP), mul_one]
  rw [hlc] at h
  refine h.congr fun u => ?_
  simp [hP', eval_comp]

/-- **`prop:rational-symbols`**: for real polynomials with `deg P > deg Q`, `P(0) = Q(0)`, neither
vanishing on `[0,∞)`, and a probability measure with `μ̂_I(ω) = Q(|ω|²)/P(|ω|²)`: the orbit has
`μ̂_Σ(ω) = Q(⟨ω,Σω⟩)/P(⟨ω,Σω⟩)`; `g(u) = log(P(u)/Q(u))` satisfies the hypotheses of
`prop:affine-orbits` and of `prop:log-orbit-rays` with `κ = deg P - deg Q`; and a positive finite
increment `μ_{Σ'} = μ_Σ * ρ` forces `Σ' = cΣ` with `c ≥ 1`. -/
theorem rational_symbols (hd : 1 ≤ d) (P Q : Polynomial ℝ) (hPQ : IsRationalSymbolPair P Q)
    (μI : Measure (Rd d)) (hμI : IsSymbolLaw P Q μI) :
    let g : ℝ → ℝ := fun u => Real.log (P.eval u / Q.eval u)
    (∀ S : Mat d, S.PosDef → ∀ ω : Rd d, charFun (affineOrbit μI S) ω =
        ((Q.eval (quad S ω) / P.eval (quad S ω) : ℝ) : ℂ)) ∧
      ContinuousOn g (Ici 0) ∧ (∀ u : ℝ, 0 ≤ u → 0 ≤ g u) ∧ g 0 = 0 ∧
      (∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      (∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop
        (𝓝 (((P.natDegree - Q.natDegree : ℕ) : ℝ) * Real.log c))) ∧
      ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsFiniteMeasure ρ →
        affineOrbit μI S' = affineOrbit μI S ∗ ρ → ∃ c : ℝ, 1 ≤ c ∧ S' = c • S := by
  intro g
  obtain ⟨hprob, hchar⟩ := hμI
  obtain ⟨hdeg, h0, hP, hQ⟩ := hPQ
  have hPQ : IsRationalSymbolPair P Q := ⟨hdeg, h0, hP, hQ⟩
  have hPne : P ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hQne : Q ≠ 0 := by
    rintro rfl
    exact hQ 0 le_rfl (by simp)
  -- the symbol as `e^{-g}`
  have hexp : ∀ u : ℝ, 0 ≤ u → Real.exp (-g u) = Q.eval u / P.eval u := fun u hu => by
    simp only [g]
    rw [Real.exp_neg, Real.exp_log (hPQ.div_pos hu), inv_div]
  have hcharg : ∀ ω : Rd d, charFun μI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ) := fun ω => by
    rw [hchar, hexp _ (sq_nonneg _)]
  have hg0 : g 0 = 0 := by
    simp only [g]
    rw [h0, div_self (hQ 0 le_rfl), Real.log_one]
  have hgnn : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u := by
    intro u hu
    obtain ⟨ω, hω⟩ := exists_norm_sq_eq hd hu
    have h1 := norm_charFun_le_one (μ := μI) ω
    rw [hcharg, hω, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have := Real.exp_le_one_iff.1 h1
    linarith
  have hgc : ContinuousOn g (Ici 0) := by
    refine ContinuousOn.log (P.continuous.continuousOn.div Q.continuous.continuousOn
      fun u hu => hQ u hu) fun u hu => (hPQ.div_pos hu).ne'
  -- the asymptotics
  have hlog : ∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop
      (𝓝 (((P.natDegree - Q.natDegree : ℕ) : ℝ) * Real.log c)) := by
    intro c hc
    have hA := (Real.continuousAt_log (pow_pos hc P.natDegree).ne').tendsto.comp
      (tendsto_eval_mul_div_eval hPne hc)
    have hB := (Real.continuousAt_log (pow_pos hc Q.natDegree).ne').tendsto.comp
      (tendsto_eval_mul_div_eval hQne hc)
    have hlim := hA.sub hB
    rw [Real.log_pow, Real.log_pow, ← sub_mul, ← Nat.cast_sub hdeg.le] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    have hcu : 0 ≤ c * u := mul_nonneg hc.le hu
    simp only [Function.comp, g]
    rw [Real.log_div (hP _ hcu) (hQ _ hcu), Real.log_div (hP _ hu) (hQ _ hu),
      Real.log_div (hP _ hcu) (hP _ hu), Real.log_div (hQ _ hcu) (hQ _ hu)]
    ring
  have hκ : (0 : ℝ) < ((P.natDegree - Q.natDegree : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hdeg
  refine ⟨fun S hS ω => ?_, hgc, hgnn, hg0, hcharg, hlog, fun S S' hS hS' ρ hρ hconv => ?_⟩
  · rw [charFun_affineOrbit_lin, hchar, norm_sq_lin_msqrt hS.posSemidef]
  · obtain ⟨c, hc, rfl⟩ := log_orbit_rays hd g hgc hgnn hg0 μI hcharg _ hκ hlog S S' hS hS' ρ hρ
      hconv
    exact ⟨c, one_le_of_ray_increment hcharg hκ hc (hlog c hc) hd hS hconv, rfl⟩

/-! ## The examples -/

/-- The Matérn law of index `γ > 0` has the transform `(1 + |ω|²)^{-γ}`
(`prop:affine-orbits`(4)). -/
theorem charFun_gammaGaussLaw (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (ω : Rd d) :
    charFun (gammaGaussLaw d γ) ω = (((1 + ‖ω‖ ^ 2) ^ (-γ) : ℝ) : ℂ) :=
  (matern_orbit hd γ hγ).2.1 ω

theorem isProbabilityMeasure_gammaGaussLaw (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    IsProbabilityMeasure (gammaGaussLaw d γ) :=
  (matern_orbit hd γ hγ).1

/-- The index-`1` Matérn law scaled by `√a`: its transform is `(1 + a|ω|²)⁻¹`. -/
theorem charFun_scaled_matern (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (ω : Rd d) :
    charFun (push (Real.sqrt a • (1 : Mat d)) (gammaGaussLaw d 1)) ω =
      (((1 + a * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [charFun_push_smul_one, charFun_gammaGaussLaw hd one_pos, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha, Real.rpow_neg_one]

/-- The convolution of a list of probability measures is a probability measure, and its transform is
the product of the transforms. -/
theorem convList_charFun (l : List (Measure (Rd d))) (h : ∀ μ ∈ l, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (convList l) ∧
      ∀ ω : Rd d, charFun (convList l) ω = (l.map fun μ => charFun μ ω).prod := by
  induction l with
  | nil =>
    refine ⟨by rw [convList]; infer_instance, fun ω => ?_⟩
    rw [convList, charFun_dirac]
    simp
  | cons μ l ih =>
    obtain ⟨hl, hlc⟩ := ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    haveI := hl
    haveI := h μ List.mem_cons_self
    refine ⟨by rw [convList]; infer_instance, fun ω => ?_⟩
    rw [convList, List.map_cons, List.prod_cons, charFun_conv, hlc]

/-- The transform of a finite mixture of probability measures. -/
theorem charFun_mixture {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (μ : Fin n → Measure (Rd d))
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (ω : Rd d) :
    charFun (∑ i, ENNReal.ofReal (w i) • μ i) ω = ∑ i, (w i : ℂ) * charFun (μ i) ω := by
  rw [charFun_apply, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hw i), charFun_apply, Complex.real_smul]
  · intro i _
    haveI := hμ i
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]

theorem natDegree_one_add_C_mul_X {a : ℝ} (ha : a ≠ 0) :
    (1 + Polynomial.C a * Polynomial.X).natDegree = 1 := by
  rw [add_comm, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X a ha]
  simp

theorem leadingCoeff_one_add_C_mul_X {a : ℝ} (ha : a ≠ 0) :
    (1 + Polynomial.C a * Polynomial.X).leadingCoeff = a := by
  rw [leadingCoeff_add_of_degree_lt, leadingCoeff_C_mul_X]
  rw [degree_C_mul_X ha]
  simp

theorem eval_one_add_C_mul_X (a u : ℝ) :
    (1 + Polynomial.C a * Polynomial.X).eval u = 1 + a * u := by simp

/-- **`prop:rational-symbols`**, the examples: the hypotheses hold, with a law of the given symbol,
for the Matérn orbits of integer index `γ ≥ 1` (`Q = 1`, `P = (1+u)^γ`, `κ = γ`), for the products
`∏_{i≤n}(1 + aᵢu)⁻¹` (`κ = n`), and for the mixtures `∑_{i≤n} wᵢ(1 + aᵢu)⁻¹` with `wᵢ ≥ 0`,
`∑ wᵢ = 1` (`κ = 1`), `n ≥ 1`, `aᵢ > 0`. -/
theorem rational_symbols_examples (hd : 1 ≤ d) :
    (∀ γ : ℕ, 1 ≤ γ →
      IsRationalSymbolPair ((1 + Polynomial.X) ^ γ) 1 ∧
        ((1 + Polynomial.X : Polynomial ℝ) ^ γ).natDegree - (1 : Polynomial ℝ).natDegree = γ ∧
        ∃ μI : Measure (Rd d), IsSymbolLaw ((1 + Polynomial.X) ^ γ) 1 μI) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 < a i) →
        IsRationalSymbolPair (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)) 1 ∧
          (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)).natDegree -
            (1 : Polynomial ℝ).natDegree = n ∧
          ∃ μI : Measure (Rd d), IsSymbolLaw (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)) 1 μI) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ a w : Fin n → ℝ, (∀ i, 0 < a i) → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        let P : Polynomial ℝ := ∏ i, (1 + Polynomial.C (a i) * Polynomial.X)
        let Q : Polynomial ℝ := ∑ i, Polynomial.C (w i) *
          ∏ k ∈ Finset.univ.erase i, (1 + Polynomial.C (a k) * Polynomial.X)
        IsRationalSymbolPair P Q ∧ P.natDegree - Q.natDegree = 1 ∧
          ∃ μI : Measure (Rd d), IsSymbolLaw P Q μI := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := isProbabilityMeasure_gammaGaussLaw hd (one_pos : (0 : ℝ) < 1)
  have hlin : ∀ {a : ℝ}, 0 < a → (1 + Polynomial.C a * Polynomial.X) ≠ 0 := fun ha h => by
    have := natDegree_one_add_C_mul_X ha.ne'
    rw [h, natDegree_zero] at this
    exact zero_ne_one this
  -- the product polynomial
  have hprodP : ∀ {n : ℕ} (a : Fin n → ℝ), (∀ i, 0 < a i) → ∀ s : Finset (Fin n),
      (∏ i ∈ s, (1 + Polynomial.C (a i) * Polynomial.X)).natDegree = s.card ∧
      (∏ i ∈ s, (1 + Polynomial.C (a i) * Polynomial.X)).leadingCoeff = ∏ i ∈ s, a i ∧
      ∀ u : ℝ, 0 ≤ u → (∏ i ∈ s, (1 + Polynomial.C (a i) * Polynomial.X)).eval u =
        ∏ i ∈ s, (1 + a i * u) := by
    intro n a ha s
    refine ⟨?_, ?_, fun u _ => ?_⟩
    · rw [natDegree_prod _ _ fun i _ => hlin (ha i)]
      simp [natDegree_one_add_C_mul_X (ha _).ne']
    · rw [leadingCoeff_prod]
      exact Finset.prod_congr rfl fun i _ => leadingCoeff_one_add_C_mul_X (ha i).ne'
    · rw [eval_prod]
      exact Finset.prod_congr rfl fun i _ => eval_one_add_C_mul_X _ _
  refine ⟨fun γ hγ => ?_, fun n hn a ha => ?_, fun n hn a w ha hw hsum => ?_⟩
  · -- the Matérn of integer index
    have hdeg : ((1 + Polynomial.X : Polynomial ℝ) ^ γ).natDegree = γ := by
      rw [natDegree_pow, add_comm, ← C_1, natDegree_X_add_C, mul_one]
    refine ⟨⟨by rw [hdeg, natDegree_one]; omega, by simp, fun u hu => ?_, fun u _ => by simp⟩,
      by rw [hdeg, natDegree_one, Nat.sub_zero], gammaGaussLaw d γ, ?_⟩
    · rw [eval_pow, eval_add, eval_one, eval_X]
      exact pow_ne_zero _ (by linarith)
    · refine ⟨isProbabilityMeasure_gammaGaussLaw hd (by exact_mod_cast hγ), fun ω => ?_⟩
      rw [charFun_gammaGaussLaw hd (by exact_mod_cast hγ), eval_one, eval_pow, eval_add, eval_one,
        eval_X, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
  · -- the products
    obtain ⟨hdeg, -, heval⟩ := hprodP a ha Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hdeg
    have hpos : ∀ u : ℝ, 0 ≤ u → 0 < ∏ i, (1 + a i * u) := fun u hu =>
      Finset.prod_pos fun i _ => by have := mul_nonneg (ha i).le hu; linarith
    refine ⟨⟨by rw [hdeg, natDegree_one]; omega, ?_, fun u hu => ?_, fun u _ => by simp⟩,
      by rw [hdeg, natDegree_one, Nat.sub_zero], ?_⟩
    · rw [heval 0 le_rfl]
      simp
    · rw [heval u hu]
      exact (hpos u hu).ne'
    · set l := (List.finRange n).map fun i => push (Real.sqrt (a i) • (1 : Mat d)) (gammaGaussLaw d 1)
        with hl
      obtain ⟨hprob, hchar⟩ := convList_charFun l fun μ hμ => by
        rw [hl, List.mem_map] at hμ
        obtain ⟨i, -, rfl⟩ := hμ
        infer_instance
      refine ⟨convList l, hprob, fun ω => ?_⟩
      rw [hchar, hl, List.map_map, eval_one, heval _ (sq_nonneg _)]
      have h1 : ((List.finRange n).map ((fun μ => charFun μ ω) ∘
          fun i => push (Real.sqrt (a i) • (1 : Mat d)) (gammaGaussLaw d 1))).prod =
          ∏ i, charFun (push (Real.sqrt (a i) • (1 : Mat d)) (gammaGaussLaw d 1)) ω := by
        rw [Fin.prod_univ_def]
        rfl
      rw [h1]
      simp only [charFun_scaled_matern hd (ha _).le]
      push_cast
      rw [one_div, Finset.prod_inv_distrib]
  · -- the mixtures
    intro P Q
    obtain ⟨hdegP, -, hevalP⟩ := hprodP a ha Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hdegP
    have hpos1 : ∀ i : Fin n, ∀ u : ℝ, 0 ≤ u → 0 < 1 + a i * u := fun i u hu => by
      have := mul_nonneg (ha i).le hu; linarith
    have hPu : ∀ u : ℝ, 0 ≤ u → P.eval u = ∏ i, (1 + a i * u) := hevalP
    have hPpos : ∀ u : ℝ, 0 ≤ u → 0 < P.eval u := fun u hu => by
      rw [hPu u hu]; exact Finset.prod_pos fun i _ => hpos1 i u hu
    have hQu : ∀ u : ℝ, 0 ≤ u →
        Q.eval u = ∑ i, w i * ∏ k ∈ Finset.univ.erase i, (1 + a k * u) := fun u hu => by
      simp only [Q, eval_finsetSum, eval_mul, eval_C]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hprodP a ha _).2.2 u hu]
    -- `Q/P = ∑ wᵢ (1 + aᵢu)⁻¹`
    have hQP : ∀ u : ℝ, 0 ≤ u → Q.eval u / P.eval u = ∑ i, w i * (1 + a i * u)⁻¹ := by
      intro u hu
      rw [hQu u hu, hPu u hu, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_prod_erase Finset.univ (fun k => 1 + a k * u) (Finset.mem_univ i),
        mul_div_assoc]
      congr 1
      have hne : ∏ k ∈ Finset.univ.erase i, (1 + a k * u) ≠ 0 :=
        (Finset.prod_pos fun k _ => hpos1 k u hu).ne'
      rw [mul_comm, ← div_div, div_self hne, one_div]
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    have hQpos : ∀ u : ℝ, 0 ≤ u → 0 < Q.eval u := fun u hu => by
      rw [hQu u hu]
      refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i)
        (Finset.prod_pos fun k _ => hpos1 k u hu).le) ⟨i₀, Finset.mem_univ _, ?_⟩
      exact mul_pos hi₀ (Finset.prod_pos fun k _ => hpos1 k u hu)
    -- `deg Q = n - 1`
    have hcard : ∀ i : Fin n, (Finset.univ.erase i).card = n - 1 := fun i => by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hdegQ : Q.natDegree = n - 1 := by
      refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
      · refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [(hprodP a ha _).1, hcard]
      · simp only [Q, finsetSum_coeff, coeff_C_mul]
        have hc : ∀ i : Fin n, (∏ k ∈ Finset.univ.erase i,
            (1 + Polynomial.C (a k) * Polynomial.X)).coeff (n - 1) =
            ∏ k ∈ Finset.univ.erase i, a k := fun i => by
          rw [← hcard i, ← (hprodP a ha _).1, coeff_natDegree, (hprodP a ha _).2.1]
        simp only [hc]
        refine (Finset.sum_pos' (fun i _ => mul_nonneg (hw i)
          (Finset.prod_pos fun k _ => ha k).le) ⟨i₀, Finset.mem_univ _, ?_⟩).ne'
        exact mul_pos hi₀ (Finset.prod_pos fun k _ => ha k)
    refine ⟨⟨by rw [hdegQ, hdegP]; omega, ?_, fun u hu => (hPpos u hu).ne',
      fun u hu => (hQpos u hu).ne'⟩, by rw [hdegQ, hdegP]; omega, ?_⟩
    · rw [hPu 0 le_rfl, hQu 0 le_rfl]
      simp [hsum]
    · set μ : Fin n → Measure (Rd d) :=
        fun i => push (Real.sqrt (a i) • (1 : Mat d)) (gammaGaussLaw d 1) with hμ
      have hμP : ∀ i, IsProbabilityMeasure (μ i) := fun i => by rw [hμ]; infer_instance
      refine ⟨∑ i, ENNReal.ofReal (w i) • μ i, ⟨?_⟩, fun ω => ?_⟩
      · rw [Measure.coe_finsetSum, Finset.sum_apply]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw i, hsum, ENNReal.ofReal_one]
      · rw [charFun_mixture w hw μ hμP, hQP _ (sq_nonneg _)]
        simp only [hμ, charFun_scaled_matern hd (ha _).le]
        push_cast
        rfl

end AffineHemigroup
