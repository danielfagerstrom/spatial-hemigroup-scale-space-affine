/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityGeneral
import AffineHemigroup.OrbitRays

/-!
# `prop:similarity-general-bounded-shape`: bounded shape under a comparable rank-one limit

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-general-bounded-shape`.

(1) The anisotropy functionals — the rotational spread `rs`, the exponent spread `es`, the moment
matrices `𝓜_s` — and their behaviour under similarities, on sums, on the orbit of a profile
(`es ≤ 4 ecc`) and on the stable orbit (`es = ecc^{α/2}`); (2)–(3) the Lévy and exponent levels of
the sandwich give `rs`, `es ≤ 1/θ` under `L_* ≥ θL_I`, `ψ_* ≥ θψ_I`; (4) the moment matrices at each
scale, `cond 𝓜_s(L_Σ) ≤ 1/θ_{s/√t}`.

## Routes

The blueprint's. The orbit's bound `es ≤ 4 ecc` is read on the exponent `F` of the origin datum
`(0, |S^{d-1}|k)` of the profile (`RadialProfile.toOriginDatum`): `F` is radial, nondecreasing along
rays (`φ(bs) = ∫ (1 - cos(us)) k(u/b) du/u`, `k` nonincreasing) and `F(2ξ) ≤ 4F(ξ)`
(`1 - cos 2τ ≤ 4(1 - cos τ)`); so `|ξ'| ≤ √c|ξ|` gives `F(ξ') ≤ 4cF(ξ)`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The exponent of a radial profile along rays -/

/-- `1 - cos 2τ ≤ 4(1 - cos τ)`. -/
theorem one_sub_cos_two_mul_le (τ : ℝ) : 1 - Real.cos (2 * τ) ≤ 4 * (1 - Real.cos τ) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.cos_le_one τ, Real.neg_one_le_cos τ]

/-- `F(ξ) ≤ F(bξ)` for `b ≥ 1`, for an origin datum without a Gaussian part. -/
theorem OriginDatum.exponentL_le_smul (hd : 1 ≤ d) (D : OriginDatum d) (ha : D.a = 0) {b : ℝ}
    (hb : 1 ≤ b) (ξ : Rd d) : D.exponentL ξ ≤ D.exponentL (b • ξ) := by
  have hb0 : 0 < b := by linarith
  rw [D.exponentL_eq_sphere hd, D.exponentL_eq_sphere hd, ha]
  simp only [zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  refine mul_le_mul_right (lintegral_mono fun η => ?_) _
  rw [real_inner_smul_left, D.cosProfileL_dilate hb0]
  refine setLIntegral_mono' measurableSet_Ioi fun u (hu : 0 < u) => ?_
  refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  exact div_le_div_of_nonneg_right (D.k_antitone (div_pos hu hb0) hu (div_le_self hu.le hb)) hu.le

/-- `F(2ξ) ≤ 4F(ξ)`. -/
theorem OriginDatum.exponentL_two_smul_le (D : OriginDatum d) (ξ : Rd d) :
    D.exponentL ((2 : ℝ) • ξ) ≤ 4 * D.exponentL ξ := by
  unfold OriginDatum.exponentL
  rw [mul_add]
  refine add_le_add (le_of_eq ?_) ?_
  · rw [norm_smul, Real.norm_two, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  · rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun x => ?_
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [real_inner_smul_left]
    exact one_sub_cos_two_mul_le _

/-- **The exponent of a profile, compared on two vectors**: for `c ≥ 1` and `|ξ'| ≤ √c |ξ|`,
`ψ(ξ') ≤ 4c ψ(ξ)`. -/
theorem RadialProfile.exponent_le_four_mul (hd : 1 ≤ d) (K : RadialProfile d) {c : ℝ}
    (hc : 1 ≤ c) {ξ ξ' : Rd d} (h : ‖ξ'‖ ≤ Real.sqrt c * ‖ξ‖) :
    K.exponent ξ' ≤ 4 * c * K.exponent ξ := by
  set D := K.toOriginDatum hd with hD
  have ha : D.a = 0 := rfl
  have hF : ∀ η, K.exponent η = D.exponent η := fun η => (K.toOriginDatum_exponent hd η).symm
  have hfin : ∀ η, D.exponentL η ≠ ⊤ := fun η => D.exponentL_ne_top hd η
  have hmono : ∀ η {b : ℝ}, 1 ≤ b → D.exponent η ≤ D.exponent (b • η) := fun η b hb =>
    ENNReal.toReal_mono (hfin _) (D.exponentL_le_smul hd ha hb η)
  have hdouble : ∀ η, D.exponent ((2 : ℝ) • η) ≤ 4 * D.exponent η := fun η => by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hfin η))
      (D.exponentL_two_smul_le η)
    rwa [ENNReal.toReal_mul, show (4 : ℝ≥0∞).toReal = 4 by simp] at this
  have hpow : ∀ n : ℕ, ∀ η, D.exponent ((2 : ℝ) ^ n • η) ≤ 4 ^ n * D.exponent η := by
    intro n
    induction n with
    | zero => intro η; simp
    | succ n ih =>
      intro η
      rw [pow_succ, mul_smul]
      calc D.exponent ((2 : ℝ) ^ n • (2 : ℝ) • η) ≤ 4 ^ n * D.exponent ((2 : ℝ) • η) := ih _
        _ ≤ 4 ^ n * (4 * D.exponent η) :=
            mul_le_mul_of_nonneg_left (hdouble η) (by positivity)
        _ = 4 ^ (n + 1) * D.exponent η := by ring
  rw [hF, hF]
  have hsc : 1 ≤ Real.sqrt c := Real.one_le_sqrt.2 hc
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hsc (by norm_num : (1 : ℝ) < 2)
  have h0 : 0 ≤ D.exponent ξ := D.exponent_nonneg ξ
  -- `F(ξ') ≤ F(2^{n+1} ξ)`
  have hstep : D.exponent ξ' ≤ D.exponent ((2 : ℝ) ^ (n + 1) • ξ) := by
    rcases eq_or_ne ξ' 0 with h0' | h0'
    · rw [h0']
      have : D.exponent 0 = 0 := by
        unfold OriginDatum.exponent OriginDatum.exponentL
        simp
      rw [this]
      exact D.exponent_nonneg _
    · set b := (2 : ℝ) ^ (n + 1) * ‖ξ‖ / ‖ξ'‖ with hb
      have hξ' : 0 < ‖ξ'‖ := norm_pos_iff.2 h0'
      have hb1 : 1 ≤ b := by
        rw [hb, le_div_iff₀ hξ', one_mul]
        calc ‖ξ'‖ ≤ Real.sqrt c * ‖ξ‖ := h
          _ ≤ 2 ^ (n + 1) * ‖ξ‖ := mul_le_mul_of_nonneg_right hn2.le (norm_nonneg _)
      refine (hmono ξ' hb1).trans (le_of_eq (D.exponent_eq_of_norm_eq ?_))
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity), hb, div_mul_cancel₀ _ hξ'.ne']
  calc D.exponent ξ' ≤ D.exponent ((2 : ℝ) ^ (n + 1) • ξ) := hstep
    _ ≤ 4 ^ (n + 1) * D.exponent ξ := hpow _ ξ
    _ ≤ 4 * c * D.exponent ξ := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h5 : ((2 : ℝ) ^ n) ^ 2 ≤ c := by
          calc ((2 : ℝ) ^ n) ^ 2 ≤ Real.sqrt c ^ 2 := pow_le_pow_left₀ (by positivity) hn1 2
            _ = c := Real.sq_sqrt (by linarith)
        rw [pow_succ, h4]
        nlinarith

/-! ## The two spreads -/

theorem rotSpread_le {L : Measure (Rd d)} {K : ℝ≥0∞} (h1 : 1 ≤ K)
    (h : ∀ R ∈ orthSet d, push R L ≤ K • L) : rotSpread L ≤ K :=
  iInf_le_of_le ⟨K, h1, h⟩ le_rfl

theorem le_rotSpread {L : Measure (Rd d)} {a : ℝ≥0∞}
    (h : ∀ K : ℝ≥0∞, 1 ≤ K → (∀ R ∈ orthSet d, push R L ≤ K • L) → a ≤ K) : a ≤ rotSpread L :=
  le_iInf fun K => h K.1 K.2.1 K.2.2

theorem expSpread_le {ψ : Rd d → ℝ} {K : ℝ} (h1 : 1 ≤ K)
    (h : ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) ≤ K * ψ ω) : expSpread ψ ≤ ENNReal.ofReal K :=
  iInf_le_of_le ⟨K, h1, h⟩ le_rfl

theorem le_expSpread {ψ : Rd d → ℝ} {a : ℝ≥0∞}
    (h : ∀ K : ℝ, 1 ≤ K → (∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) ≤ K * ψ ω) →
      a ≤ ENNReal.ofReal K) : a ≤ expSpread ψ :=
  le_iInf fun K => h K.1 K.2.1 K.2.2

theorem one_le_rotSpread (L : Measure (Rd d)) : 1 ≤ rotSpread L :=
  le_rotSpread fun _ hK _ => hK

theorem one_le_expSpread (ψ : Rd d → ℝ) : 1 ≤ expSpread ψ :=
  le_expSpread fun _ hK _ => by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK

theorem push_mono (A : Mat d) {μ ν : Measure (Rd d)} (h : μ ≤ ν) : push A μ ≤ push A ν :=
  Measure.map_mono h (lin A).continuous.measurable

theorem push_smul_measure (A : Mat d) (c : ℝ≥0∞) (μ : Measure (Rd d)) :
    push A (c • μ) = c • push A μ := Measure.map_smul c μ _

/-- `(cR)(RᵀR'R) = R'(cR)` for `R ∈ O(d)`. -/
theorem smul_orth_conj {c : ℝ} {R : Mat d} (hR : R ∈ orthSet d) (R' : Mat d) :
    (c • R) * (Rᵀ * R' * R) = R' * (c • R) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    orth_mul_transpose hR, Matrix.one_mul]

theorem conj_mem_orthSet {R R' : Mat d} (hR : R ∈ orthSet d) (hR' : R' ∈ orthSet d) :
    Rᵀ * R' * R ∈ orthSet d :=
  (Matrix.orthogonalGroup (Fin d) ℝ).mul_mem ((Matrix.orthogonalGroup (Fin d) ℝ).mul_mem
    (transpose_mem_orthSet hR) hR') hR

/-- **`rs((cQ)_*L) = rs(L)`**. -/
theorem rotSpread_push {c : ℝ} (hc : 0 < c) {R : Mat d} (hR : R ∈ orthSet d)
    (L : Measure (Rd d)) : rotSpread (push (c • R) L) = rotSpread L := by
  have hinv : (c⁻¹ • Rᵀ) * (c • R) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul,
      orth_transpose_mul hR]
  have hiff : ∀ K : ℝ≥0∞, (∀ R' ∈ orthSet d, push R' (push (c • R) L) ≤ K • push (c • R) L) ↔
      ∀ R' ∈ orthSet d, push R' L ≤ K • L := by
    intro K
    constructor
    · intro h R' hR'
      have h1 := h _ (conj_mem_orthSet (transpose_mem_orthSet hR) hR')
      have hm : Rᵀᵀ * R' * Rᵀ * (c • R) = (c • R) * R' := by
        rw [transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc (R * R'),
          orth_transpose_mul hR, Matrix.mul_one]
      rw [push_push, hm, ← push_push, ← push_smul_measure] at h1
      have h2 := push_mono (c⁻¹ • Rᵀ) h1
      rwa [push_push (c⁻¹ • Rᵀ) (c • R) (push R' L), push_push (c⁻¹ • Rᵀ) (c • R) (K • L), hinv,
        push_one, push_one] at h2
    · intro h R' hR'
      rw [push_push, ← smul_orth_conj hR, ← push_push, ← push_smul_measure]
      exact push_mono _ (h _ (conj_mem_orthSet hR hR'))
  exact le_antisymm (le_rotSpread fun K hK h => rotSpread_le hK ((hiff K).2 h))
    (le_rotSpread fun K hK h => rotSpread_le hK ((hiff K).1 h))

theorem lin_mul_apply (X Y : Mat d) (ω : Rd d) : lin (X * Y) ω = lin X (lin Y ω) := by
  rw [lin_mul]; rfl

/-- **`es(ψ(cQ·)) = es(ψ)`**. -/
theorem expSpread_comp {c : ℝ} (hc : 0 < c) {R : Mat d} (hR : R ∈ orthSet d) (ψ : Rd d → ℝ) :
    expSpread (fun ω => ψ (lin (c • R) ω)) = expSpread ψ := by
  have hAB : (c • R) * (c⁻¹ • Rᵀ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
      orth_mul_transpose hR]
  have hiff : ∀ K : ℝ, (∀ R' ∈ orthSet d, ∀ ω : Rd d,
      ψ (lin (c • R) (lin R' ω)) ≤ K * ψ (lin (c • R) ω)) ↔
      ∀ R' ∈ orthSet d, ∀ ω : Rd d, ψ (lin R' ω) ≤ K * ψ ω := by
    intro K
    constructor
    · intro h R' hR' ω
      have h1 := h _ (conj_mem_orthSet hR hR') (lin (c⁻¹ • Rᵀ) ω)
      rw [← lin_mul_apply, ← lin_mul_apply, smul_orth_conj hR, Matrix.mul_assoc, hAB,
        Matrix.mul_one, ← lin_mul_apply, hAB, lin_one] at h1
      exact h1
    · intro h R' hR' ω
      have h1 := h _ (conj_mem_orthSet (transpose_mem_orthSet hR) hR') (lin (c • R) ω)
      rw [← lin_mul_apply] at h1
      have hm : Rᵀᵀ * R' * Rᵀ * (c • R) = (c • R) * R' := by
        rw [transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc (R * R'),
          orth_transpose_mul hR, Matrix.mul_one]
      rwa [hm, lin_mul_apply] at h1
  exact le_antisymm (le_expSpread fun K hK h => expSpread_le hK ((hiff K).2 h))
    (le_expSpread fun K hK h => expSpread_le hK ((hiff K).1 h))

/-- **`rs(L) = 1` exactly when `L` is rotation invariant.** -/
theorem rotSpread_eq_one_iff (L : Measure (Rd d)) : rotSpread L = 1 ↔ IsRotationInvariant L := by
  constructor
  · intro h1 R hR
    have hle : ∀ R ∈ orthSet d, push R L ≤ L := by
      intro R hR
      refine Measure.le_iff'.2 fun B => ?_
      have hKB : ∀ K : ℝ≥0∞, 1 ≤ K → (∀ R ∈ orthSet d, push R L ≤ K • L) →
          push R L B ≤ K * L B := fun K _ hK => by
        have := Measure.le_iff'.1 (hK R hR) B
        rwa [Measure.smul_apply, smul_eq_mul] at this
      have hne : ∃ K : ℝ≥0∞, 1 ≤ K ∧ ∀ R ∈ orthSet d, push R L ≤ K • L := by
        by_contra hcon
        push Not at hcon
        have : rotSpread L = ⊤ := by
          unfold rotSpread
          haveI : IsEmpty {K : ℝ≥0∞ // 1 ≤ K ∧ ∀ R ∈ orthSet d, push R L ≤ K • L} :=
            ⟨fun K => by obtain ⟨R', hR', h'⟩ := hcon K.1 K.2.1; exact h' (K.2.2 R' hR')⟩
          exact iInf_of_empty _
        rw [this] at h1
        exact ENNReal.top_ne_one h1
      obtain ⟨K0, hK01, hK0⟩ := hne
      rcases eq_or_ne (L B) ⊤ with htop | htop
      · rw [htop]; exact le_top
      rcases eq_or_ne (L B) 0 with h0 | h0
      · have := hKB K0 hK01 hK0
        rw [h0, mul_zero] at this
        rw [h0]; exact this
      have hdiv : push R L B / L B ≤ rotSpread L :=
        le_rotSpread fun K hK1 hK => ENNReal.div_le_of_le_mul (hKB K hK1 hK)
      rw [h1, ENNReal.div_le_iff h0 htop, one_mul] at hdiv
      exact hdiv
    refine le_antisymm (hle R hR) ?_
    have h2 := push_mono R (hle Rᵀ (transpose_mem_orthSet hR))
    rwa [push_push, orth_mul_transpose hR, push_one] at h2
  · intro h
    exact le_antisymm (rotSpread_le le_rfl fun R hR => by rw [h R hR, one_smul])
      (one_le_rotSpread L)

/-- **`es(ψ) = 1` exactly when `ψ` is rotation invariant**, for `ψ ≥ 0`. -/
theorem expSpread_eq_one_iff {ψ : Rd d → ℝ} (hψ : ∀ ω, 0 ≤ ψ ω) :
    expSpread ψ = 1 ↔ ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) = ψ ω := by
  constructor
  · intro h1
    have hle : ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) ≤ ψ ω := by
      intro R hR ω
      have hne : ∃ K : ℝ, 1 ≤ K ∧ ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) ≤ K * ψ ω := by
        by_contra hcon
        push Not at hcon
        have : expSpread ψ = ⊤ := by
          unfold expSpread
          haveI : IsEmpty {K : ℝ // 1 ≤ K ∧ ∀ R ∈ orthSet d, ∀ ω : Rd d,
              ψ (lin R ω) ≤ K * ψ ω} :=
            ⟨fun K => by
              obtain ⟨R', hR', ω', h'⟩ := hcon K.1 K.2.1
              exact absurd (K.2.2 R' hR' ω') (not_le.2 h')⟩
          exact iInf_of_empty _
        rw [this] at h1
        exact ENNReal.top_ne_one h1
      obtain ⟨K0, hK01, hK0⟩ := hne
      rcases (hψ ω).lt_or_eq with hpos | h0
      · by_contra hcon
        push Not at hcon
        have hq : 1 < ψ (lin R ω) / ψ ω := by rw [one_lt_div hpos]; exact hcon
        have : ENNReal.ofReal (ψ (lin R ω) / ψ ω) ≤ expSpread ψ := le_expSpread fun K _ hK =>
          ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpos).2 (hK R hR ω))
        rw [h1, ENNReal.ofReal_le_one] at this
        linarith
      · have := hK0 R hR ω
        rw [← h0, mul_zero] at this
        rw [← h0]; exact this
    intro R hR ω
    refine le_antisymm (hle R hR ω) ?_
    have := hle Rᵀ (transpose_mem_orthSet hR) (lin R ω)
    rwa [← lin_mul_apply, orth_transpose_mul hR, lin_one] at this
  · intro h
    refine le_antisymm (le_trans (expSpread_le le_rfl fun R hR ω => by rw [h R hR, one_mul])
      (by simp)) (one_le_expSpread ψ)

/-- `ψ_{A_*L}` in `ℝ≥0∞`. -/
theorem levyExpL_push (A : Mat d) (L : Measure (Rd d)) (z : Rd d) :
    levyExpL (push A L) z = levyExpL L (lin Aᵀ z) := by
  unfold levyExpL push
  rw [lintegral_map (by fun_prop) (lin A).continuous.measurable]
  refine lintegral_congr fun x => ?_
  rw [real_inner_comm, inner_lin_left, real_inner_comm]

theorem levyExpL_mono_measure {L L' : Measure (Rd d)} (h : L ≤ L') (z : Rd d) :
    levyExpL L z ≤ levyExpL L' z := lintegral_mono' h le_rfl

theorem levyExpL_smul_measure (c : ℝ≥0∞) (L : Measure (Rd d)) (z : Rd d) :
    levyExpL (c • L) z = c * levyExpL L z := by
  unfold levyExpL; rw [lintegral_smul_measure, smul_eq_mul]

/-- **`es(ψ_L) ≤ rs(L)`**. -/
theorem expSpread_levyExp_le (L : Measure (Rd d)) : expSpread (levyExp L) ≤ rotSpread L := by
  refine le_rotSpread fun K hK1 hK => ?_
  rcases eq_or_ne K ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hK' : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal htop
  rw [← hK']
  refine expSpread_le (by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono htop hK1)
    fun R hR ω => ?_
  have hRt := transpose_mem_orthSet hR
  -- `ψ_L(Rω) = ψ_{Rᵀ_*L}(ω) ≤ K ψ_L(ω)` and `ψ_L(ω) ≤ K ψ_L(Rω)`
  have h1 : levyExpL L (lin R ω) ≤ K * levyExpL L ω := by
    have := levyExpL_mono_measure (hK Rᵀ hRt) ω
    rwa [levyExpL_push, transpose_transpose, levyExpL_smul_measure] at this
  have h2 : levyExpL L ω ≤ K * levyExpL L (lin R ω) := by
    have := levyExpL_mono_measure (push_mono Rᵀ (hK R hR)) ω
    rw [push_push, orth_transpose_mul hR, push_one, push_smul_measure, levyExpL_smul_measure,
      levyExpL_push, transpose_transpose] at this
    exact this
  unfold levyExp
  rcases eq_or_ne (levyExpL L ω) ⊤ with hω | hω
  · have : levyExpL L (lin R ω) = ⊤ := by
      by_contra hne
      rw [hω] at h2
      exact (ENNReal.mul_ne_top htop hne) (top_le_iff.1 h2)
    rw [this, hω]; simp
  · rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top htop hω) h1

/-- **The exponent spread of a sum** is at most the largest of the terms'. -/
theorem expSpread_sum_le {n : ℕ} (hn : 0 < n) (ψ : Fin n → Rd d → ℝ) (hψ : ∀ j ω, 0 ≤ ψ j ω) :
    expSpread (fun ω => ∑ j, ψ j ω) ≤ ⨆ j, expSpread (ψ j) := by
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have hlt : ∀ j, expSpread (ψ j) < t := fun j =>
    lt_of_le_of_lt (le_iSup (fun j => expSpread (ψ j)) j) ht
  have hex : ∀ j, ∃ K : ℝ, 1 ≤ K ∧ (∀ R ∈ orthSet d, ∀ ω : Rd d, ψ j (lin R ω) ≤ K * ψ j ω) ∧
      ENNReal.ofReal K < t := by
    intro j
    obtain ⟨K, hK⟩ := iInf_lt_iff.1 (hlt j)
    exact ⟨K.1, K.2.1, K.2.2, hK⟩
  choose K hK1 hKad hKt using hex
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Km := Finset.univ.sup' Finset.univ_nonempty K with hKm
  have hKmj : ∀ j, K j ≤ Km := fun j => Finset.le_sup' K (Finset.mem_univ j)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty K
  refine le_trans (expSpread_le ((hK1 j0).trans (hKmj j0)) fun R hR ω => ?_) (by
    rw [hKm, hj0]; exact (hKt j0).le)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => (hKad j R hR ω).trans
    (mul_le_mul_of_nonneg_right (hKmj j) (hψ j ω))

/-- **The orbit of a profile**: `es(ψ_{ν_H}) ≤ 4 ecc(H)`. -/
theorem expSpread_orbit_le (hd : 1 ≤ d) (K : RadialProfile d) {H : Mat d} (hH : H.PosDef) :
    expSpread (fun ω => K.exponent (lin (msqrt H) ω)) ≤ ENNReal.ofReal (4 * ecc H) := by
  haveI : NeZero d := ⟨by omega⟩
  have hl := lamMin_pos hH
  have hm := lamMax_pos hH
  have hecc : 1 ≤ ecc H := by
    unfold ecc; rw [le_div_iff₀ hl, one_mul]; exact lamMin_le_lamMax hH.isHermitian
  refine expSpread_le (by linarith) fun R hR ω => ?_
  have hq : ∀ x, ‖lin (msqrt H) x‖ ^ 2 = quad H x := fun x => norm_sq_lin_msqrt hH.posSemidef x
  have hle : ‖lin (msqrt H) (lin R ω)‖ ≤ Real.sqrt (ecc H) * ‖lin (msqrt H) ω‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (lin (msqrt H) (lin R ω))), ← Real.sqrt_sq (norm_nonneg
      (lin (msqrt H) ω)), ← Real.sqrt_mul (by linarith)]
    refine Real.sqrt_le_sqrt ?_
    rw [hq, hq]
    have h1 := quad_le_lamMax_mul hH.isHermitian (lin R ω)
    have h2 := lamMin_mul_norm_sq_le hH.isHermitian ω
    rw [norm_lin_of_orth hR] at h1
    have h3 : lamMax H = ecc H * lamMin H := by unfold ecc; field_simp
    rw [h3] at h1
    have : ecc H * (lamMin H * ‖ω‖ ^ 2) ≤ ecc H * quad H ω :=
      mul_le_mul_of_nonneg_left (by unfold quad; exact h2) (by linarith)
    nlinarith
  exact K.exponent_le_four_mul hd hecc hle

/-- **The stable orbit**: `es(ψ_{S_α(H)}) = ecc(H)^{α/2}`. -/
theorem expSpread_stable (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) {H : Mat d} (hH : H.PosDef) :
    expSpread (stableExp α H) = ENNReal.ofReal (ecc H ^ (α / 2)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hl := lamMin_pos hH
  have hm := lamMax_pos hH
  have hecc : 1 ≤ ecc H := by
    unfold ecc; rw [le_div_iff₀ hl, one_mul]; exact lamMin_le_lamMax hH.isHermitian
  have hα2 : 0 < α / 2 := by positivity
  refine le_antisymm (expSpread_le (Real.one_le_rpow hecc hα2.le) fun R hR ω => ?_)
    (le_expSpread fun K hK1 hK => ?_)
  · unfold stableExp
    rw [← Real.mul_rpow (by linarith) (quad_nonneg hH.posSemidef ω)]
    refine Real.rpow_le_rpow (quad_nonneg hH.posSemidef _) ?_ hα2.le
    have h1 := quad_le_lamMax_mul hH.isHermitian (lin R ω)
    have h2 := lamMin_mul_norm_sq_le hH.isHermitian ω
    rw [norm_lin_of_orth hR] at h1
    have h3 : lamMax H = ecc H * lamMin H := by unfold ecc; field_simp
    rw [h3] at h1
    have : ecc H * (lamMin H * ‖ω‖ ^ 2) ≤ ecc H * quad H ω :=
      mul_le_mul_of_nonneg_left (by unfold quad; exact h2) (by linarith)
    nlinarith
  · -- the unit eigenvectors for `λ_min` and `λ_max`
    obtain ⟨u, hu1, hHu⟩ := exists_unit_eigvec_eigUp_zero hH.isHermitian
    rw [← lamMin_eq_eigUp_zero hH.isHermitian] at hHu
    obtain ⟨v, hv1, hHv⟩ := exists_unit_eigvec_eigUp hH.isHermitian (Fin.rev 0)
    rw [← lamMax_eq_eigUp_last hH.isHermitian] at hHv
    set Rf : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (u - v))ᗮ with hRf
    have hRu : Rf u = v := Submodule.reflection_sub (hu1.trans hv1.symm)
    have h := hK _ (isoMat_mem_orthSet Rf) u
    rw [lin_isoMat] at h
    change stableExp α H (Rf u) ≤ K * stableExp α H u at h
    rw [hRu] at h
    have hqu : quad H u = lamMin H := by
      rw [quad, hHu, inner_smul_right, real_inner_self_eq_norm_sq, hu1]; ring
    have hqv : quad H v = lamMax H := by
      rw [quad, hHv, inner_smul_right, real_inner_self_eq_norm_sq, hv1]; ring
    unfold stableExp at h
    rw [hqu, hqv] at h
    have hlp : 0 < lamMin H ^ (α / 2) := Real.rpow_pos_of_pos hl _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ecc, Real.div_rpow hm.le hl.le, div_le_iff₀ hlp]
    exact h

/-! ## The moment matrices -/

theorem IsLevyMeasure.integrable_min {L : Measure (Rd d)} (hL : IsLevyMeasure L) :
    Integrable (fun x : Rd d => min (‖x‖ ^ 2) 1) L := by
  refine ⟨(by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (lt_top_iff_ne_top.mpr hL.2)
  rw [Real.enorm_eq_ofReal (by positivity)]

theorem abs_mul_apply_le (x : Rd d) (k l : Fin d) : |x k * x l| ≤ ‖x‖ ^ 2 := by
  rw [abs_mul, sq]
  exact mul_le_mul (by simpa using PiLp.norm_apply_le x k) (by simpa using PiLp.norm_apply_le x l)
    (abs_nonneg _) (norm_nonneg _)

/-- `|min(|x|², r²) x_k x_l / |x|²| ≤ min(|x|², r²)`. -/
theorem abs_moment_entry_le (r : ℝ) (x : Rd d) (k l : Fin d) :
    |min (‖x‖ ^ 2) (r ^ 2) * (x k * x l) / ‖x‖ ^ 2| ≤ min (‖x‖ ^ 2) (r ^ 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      abs_zero]
    exact le_min le_rfl (sq_nonneg r)
  have hx' : 0 < ‖x‖ ^ 2 := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _)),
    abs_of_pos hx', div_le_iff₀ hx']
  exact mul_le_mul_of_nonneg_left (abs_mul_apply_le x k l) (le_min (sq_nonneg _) (sq_nonneg _))

theorem min_sq_le_max_mul (a r : ℝ) (ha : 0 ≤ a) :
    min a (r ^ 2) ≤ max 1 (r ^ 2) * min a 1 := by
  rcases le_or_gt a 1 with h | h
  · rw [min_eq_left h]
    calc min a (r ^ 2) ≤ a := min_le_left _ _
      _ ≤ max 1 (r ^ 2) * a := le_mul_of_one_le_left ha (le_max_left _ _)
  · rw [min_eq_right h.le, mul_one]
    exact (min_le_right _ _).trans (le_max_right _ _)

theorem measurable_moment_entry (r : ℝ) (k l : Fin d) :
    Measurable (fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2) * (x k * x l) / ‖x‖ ^ 2) :=
  Measurable.div (by fun_prop) (by fun_prop)

theorem integrable_moment_entry {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ)
    (k l : Fin d) :
    Integrable (fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2) * (x k * x l) / ‖x‖ ^ 2) L := by
  refine Integrable.mono' (hL.integrable_min.const_mul (max 1 (r ^ 2)))
    (measurable_moment_entry r k l).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_moment_entry_le r x k l).trans (min_sq_le_max_mul _ r (sq_nonneg _))

theorem lin_apply_coord (A : Mat d) (y : Rd d) (i : Fin d) :
    (lin A y) i = ∑ k, A i k * y k := by
  rw [ofLp_lin]
  rfl

/-- A product over the coordinates of `a eᵢ + b eⱼ`, `i ≠ j`, with every factor `1` at `0`. -/
theorem prod_two_ebasis (f : Fin d → ℝ → ℂ) (hf : ∀ j, f j 0 = 1) {i j : Fin d} (hij : i ≠ j)
    (a b : ℝ) : ∏ k, f k ((a • ebasis i + b • ebasis j) k) = f i a * f j b := by
  have hcoord : ∀ k, (a • ebasis i + b • ebasis j) k =
      (if k = i then a else 0) + (if k = j then b else 0) := fun k => by
    simp [ebasis]
  rw [Finset.prod_eq_mul i j hij (fun k _ hk => by rw [hcoord, if_neg hk.1, if_neg hk.2,
    add_zero, hf]) (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h),
    hcoord, hcoord, if_pos rfl, if_neg hij, if_neg hij.symm, if_pos rfl, add_zero, zero_add]

/-- **`𝓜_s((cR)_*L) = c²R𝓜_{s/c}(L)Rᵀ`** for a Lévy measure `L`. -/
theorem momentMatrix_push {L : Measure (Rd d)} (hL : IsLevyMeasure L) {s c : ℝ} (hc : 0 < c)
    {R : Mat d} (hR : R ∈ orthSet d) :
    momentMatrix s (push (c • R) L) = c ^ 2 • (R * momentMatrix (s / c) L * Rᵀ) := by
  ext i j
  have hpt : ∀ y : Rd d, min (‖lin (c • R) y‖ ^ 2) (s ^ 2) *
      ((lin (c • R) y) i * (lin (c • R) y) j) / ‖lin (c • R) y‖ ^ 2 =
      c ^ 2 * ∑ k, ∑ l, R i k * (R j l *
        (min (‖y‖ ^ 2) ((s / c) ^ 2) * (y k * y l) / ‖y‖ ^ 2)) := by
    intro y
    have hn : ‖lin (c • R) y‖ = c * ‖y‖ := by
      rw [lin_smul, _root_.smul_apply, norm_smul, Real.norm_of_nonneg hc.le,
        norm_lin_of_orth hR]
    have hcoord : ∀ i, (lin (c • R) y) i = c * ∑ k, R i k * y k := fun i => by
      rw [lin_smul, _root_.smul_apply, PiLp.smul_apply, lin_apply_coord, smul_eq_mul]
    rw [hn, hcoord, hcoord]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hmin : min ((c * ‖y‖) ^ 2) (s ^ 2) = c ^ 2 * min (‖y‖ ^ 2) ((s / c) ^ 2) := by
      rw [mul_comm (c ^ 2), min_mul_of_nonneg _ _ (sq_nonneg c)]
      congr 1
      · ring
      · field_simp
    rw [hmin]
    set m := min (‖y‖ ^ 2) ((s / c) ^ 2) with hm
    have h1 : c ^ 2 * m * ((c * ∑ k, R i k * y k) * (c * ∑ k, R j k * y k)) / (c * ‖y‖) ^ 2 =
        c ^ 2 * (m * ((∑ k, R i k * y k) * (∑ k, R j k * y k)) / ‖y‖ ^ 2) := by
      field_simp
    rw [h1]
    congr 1
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [momentMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  rw [push, integral_map (lin _).continuous.aemeasurable
    (measurable_moment_entry s i j).aestronglyMeasurable]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  have hint : ∀ k l, Integrable (fun y : Rd d => R i k * (R j l *
      (min (‖y‖ ^ 2) ((s / c) ^ 2) * (y k * y l) / ‖y‖ ^ 2))) L := fun k l =>
    ((integrable_moment_entry hL (s / c) k l).const_mul _).const_mul _
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, integral_const_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **`prop:similarity-general-bounded-shape`(1)**, the functionals: for a measure `L` on
`ℝ^d ∖ {0}`, `c > 0` and `Q ∈ O(d)` (bound as `R` below), `rs((cQ)_*L) = rs(L)`,
`es(ψ(cQ·)) = es(ψ)` for `ψ ≥ 0`, and
`𝓜_s((cQ)_*L) = c²Q𝓜_{s/c}(L)Qᵀ` (read for a Lévy measure, where the entries are finite; the
entrywise Bochner integral is junk where they are not); `rs(L) = 1` exactly when `L` is rotation
invariant, `es(ψ) = 1` exactly when `ψ` is; `es(ψ_L) ≤ rs(L)`; the exponent spread of a
(nonempty, finite) sum is at most the largest exponent spread of its terms; on the orbit of a
profile `es(ψ_{ν_H}) ≤ 4 ecc(H)`, and on the stable orbit `es(ψ_{S_α(H)}) = ecc(H)^{α/2}`. -/
theorem anisotropy_functionals (hd : 1 ≤ d) :
    (∀ L : Measure (Rd d), L {0} = 0 → ∀ c : ℝ, 0 < c → ∀ R ∈ orthSet d,
      rotSpread (push (c • R) L) = rotSpread L) ∧
    (∀ ψ : Rd d → ℝ, (∀ ω, 0 ≤ ψ ω) → ∀ c : ℝ, 0 < c → ∀ R ∈ orthSet d,
      expSpread (fun ω => ψ (lin (c • R) ω)) = expSpread ψ) ∧
    (∀ L : Measure (Rd d), IsLevyMeasure L → ∀ s : ℝ, 0 < s → ∀ c : ℝ, 0 < c → ∀ R ∈ orthSet d,
      momentMatrix s (push (c • R) L) = c ^ 2 • (R * momentMatrix (s / c) L * Rᵀ)) ∧
    (∀ L : Measure (Rd d), L {0} = 0 → (rotSpread L = 1 ↔ IsRotationInvariant L)) ∧
    (∀ ψ : Rd d → ℝ, (∀ ω, 0 ≤ ψ ω) →
      (expSpread ψ = 1 ↔ ∀ R ∈ orthSet d, ∀ ω : Rd d, ψ (lin R ω) = ψ ω)) ∧
    (∀ L : Measure (Rd d), L {0} = 0 → expSpread (levyExp L) ≤ rotSpread L) ∧
    (∀ n : ℕ, 0 < n → ∀ ψ : Fin n → Rd d → ℝ, (∀ j ω, 0 ≤ ψ j ω) →
      expSpread (fun ω => ∑ j, ψ j ω) ≤ ⨆ j, expSpread (ψ j)) ∧
    (∀ K : RadialProfile d, ∀ H : Mat d, H.PosDef →
      expSpread (fun ω => K.exponent (lin (msqrt H) ω)) ≤ ENNReal.ofReal (4 * ecc H)) ∧
    ∀ α : ℝ, 0 < α → α < 2 → ∀ H : Mat d, H.PosDef →
      expSpread (stableExp α H) = ENNReal.ofReal (ecc H ^ (α / 2)) :=
  ⟨fun L _ _ hc _ hR => rotSpread_push hc hR L, fun ψ _ _ hc _ hR => expSpread_comp hc hR ψ,
    fun _ hL _ _ _ hc _ hR => momentMatrix_push hL hc hR, fun L _ => rotSpread_eq_one_iff L,
    fun _ hψ => expSpread_eq_one_iff hψ, fun L _ => expSpread_levyExp_le L,
    fun _ hn ψ hψ => expSpread_sum_le hn ψ hψ, fun K _ hH => expSpread_orbit_le hd K hH,
    fun _ hα0 _ _ hH => expSpread_stable hd hα0 hH⟩

/-! ## The scaling of the general family -/

/-- `L_{tΣ} = (√t I)_*L_Σ`, `ψ_{tΣ}(ω) = ψ_Σ(√t ω)`, and `L_{tI}`, `ψ_{tI}` are rotation
invariant. -/
theorem sim_general_scale (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L) {S : Mat d} (hS : S.PosDef)
    {t : ℝ} (ht : 0 < t) :
    L (t • S) = push (Real.sqrt t • (1 : Mat d)) (L S) ∧
      ∀ ω : Rd d, levyExp (L (t • S)) ω = levyExp (L S) (Real.sqrt t • ω) := by
  have h1o : (1 : Mat d) ∈ orthSet d := (Matrix.orthogonalGroup (Fin d) ℝ).one_mem
  have h := (sim_general_covariance hd μ C L hfam).1 S hS t ht 1 h1o
  simp only [Matrix.one_mul, Matrix.mul_one, transpose_one, lin_one] at h
  exact ⟨h.2.1, fun ω => h.2.2 ω⟩

theorem sim_general_rot_smul_one (hd : 2 ≤ d) {μ : Mat d → Measure (Rd d)} {C : Mat d → Mat d}
    {L : Mat d → Measure (Rd d)} (hfam : IsSimGeneralFamily μ C L) {t : ℝ} (ht : 0 < t)
    {R : Mat d} (hR : R ∈ orthSet d) :
    push R (L (t • (1 : Mat d))) = L (t • (1 : Mat d)) ∧
      ∀ ω : Rd d, levyExp (L (t • (1 : Mat d))) (lin R ω) = levyExp (L (t • (1 : Mat d))) ω := by
  have hc := (sim_general_covariance hd μ C L hfam).1 1 PosDef.one t ht R hR
  have hs := sim_general_scale hd hfam PosDef.one ht
  rw [Matrix.mul_one, orth_mul_transpose hR] at hc
  refine ⟨?_, fun ω => ?_⟩
  · rw [hs.1, push_push, Matrix.mul_smul, Matrix.mul_one, ← hc.2.1, hs.1]
  · rw [hc.2.2, hs.2, ← lin_mul_apply, orth_transpose_mul hR, lin_one]
    rfl

/-! ## Clauses (2)–(3) -/

/-- `L ≤ θ⁻¹ L'` from `θL ≤ L'`. -/
theorem le_inv_smul_of_smul_le {θ : ℝ} (hθ : 0 < θ) {M M' : Measure (Rd d)}
    (h : ENNReal.ofReal θ • M ≤ M') : M ≤ ENNReal.ofReal θ⁻¹ • M' := by
  refine Measure.le_iff'.2 fun B => ?_
  have h1 := Measure.le_iff'.1 h B
  rw [Measure.smul_apply, smul_eq_mul] at h1
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_inv_of_pos hθ]
  have hne : ENNReal.ofReal θ ≠ 0 := by simp [hθ]
  calc M B = (ENNReal.ofReal θ)⁻¹ * (ENNReal.ofReal θ * M B) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal θ)⁻¹ * M' B := mul_le_mul_right h1 _

/-- **`prop:similarity-general-bounded-shape`(2)**, Lévy level: under infinitely divisible Loewner
increments and `L_* ≥ θL_I`, `θ ∈ (0,1]`, every `Σ ∈ PD(d)` has, with `t := λ_max(Σ)`,
`θL_{tI} ≤ L_Σ ≤ L_{tI}`, `rs(L_Σ) ≤ 1/θ` and `es(ψ_Σ) ≤ 1/θ`. -/
theorem sim_bounded_shape_levy (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hID : HasIDLoewnerIncrements μ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcomp : ∃ Lstar : Measure (Rd d), IsRankOneLimit L Lstar ∧ ENNReal.ofReal θ • L 1 ≤ Lstar) :
    ∀ S : Mat d, S.PosDef →
      ENNReal.ofReal θ • L (lamMax S • (1 : Mat d)) ≤ L S ∧ L S ≤ L (lamMax S • (1 : Mat d)) ∧
      rotSpread (L S) ≤ ENNReal.ofReal θ⁻¹ ∧ expSpread (levyExp (L S)) ≤ ENNReal.ofReal θ⁻¹ := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨Lstar, hLs, hθL⟩ := hcomp
  intro S hS
  set t := lamMax S with htdef
  have ht : 0 < t := lamMax_pos hS
  set S₁ := t⁻¹ • S with hS₁
  have hS1 : S₁.PosDef := hS.smul (inv_pos.2 ht)
  have hS1max : lamMax S₁ = 1 := by rw [hS₁, lamMax_smul (inv_pos.2 ht).le, inv_mul_cancel₀ ht.ne']
  have hSeq : t • S₁ = S := by rw [hS₁, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hscale := (sim_general_scale hd hfam hS1 ht).1
  rw [hSeq] at hscale
  have hscaleI := (sim_general_scale hd hfam PosDef.one ht).1
  obtain ⟨Q, hQ, hQv⟩ := exists_orth_top_eigvec hS1.isHermitian
  rw [hS1max, one_smul] at hQv
  have hsand := ((sim_general_sandwich hd μ C L hfam S₁ hS1 hS1max Q hQ
    (by rw [fin_zero_eq (by omega)]; exact hQv)).1 hID).1 Lstar hLs
  have hrot := (sim_general_covariance hd μ C L hfam).2.1
  have h3 : ENNReal.ofReal θ • L 1 ≤ L S₁ := by
    calc ENNReal.ofReal θ • L 1 = push Q (ENNReal.ofReal θ • L 1) := by
          rw [push_smul_measure, hrot Q hQ]
      _ ≤ push Q Lstar := push_mono Q hθL
      _ ≤ L S₁ := hsand.1
  have hlow : ENNReal.ofReal θ • L (t • (1 : Mat d)) ≤ L S := by
    rw [hscale, hscaleI, ← push_smul_measure]; exact push_mono _ h3
  have hup : L S ≤ L (t • (1 : Mat d)) := by
    rw [hscale, hscaleI]; exact push_mono _ hsand.2
  have hθinv : (1 : ℝ≥0∞) ≤ ENNReal.ofReal θ⁻¹ := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_inv_iff₀.2 ⟨hθ0, hθ1⟩)
  have hrs : rotSpread (L S) ≤ ENNReal.ofReal θ⁻¹ := by
    refine rotSpread_le hθinv fun R hR => ?_
    calc push R (L S) ≤ push R (L (t • (1 : Mat d))) := push_mono R hup
      _ = L (t • (1 : Mat d)) := (sim_general_rot_smul_one hd hfam ht hR).1
      _ ≤ ENNReal.ofReal θ⁻¹ • L S := le_inv_smul_of_smul_le hθ0 hlow
  exact ⟨hlow, hup, hrs, (expSpread_levyExp_le (L S)).trans hrs⟩

/-- **`prop:similarity-general-bounded-shape`(3)**, exponent level: under infinitely divisible
Loewner increments, or `C ≡ 0` and positive finite ones, and `ψ_* ≥ θψ_I`, `θ ∈ (0,1]`, every
`Σ ∈ PD(d)` has `θψ_{tI} ≤ ψ_Σ ≤ ψ_{tI}` and `es(ψ_Σ) ≤ 1/θ`, `t := λ_max(Σ)`. -/
theorem sim_bounded_shape_exp (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hinc : HasIDLoewnerIncrements μ ∨
      ((∀ S : Mat d, S.PosDef → C S = 0) ∧ HasFiniteLoewnerIncrements μ))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcomp : ∃ ψstar : Rd d → ℝ, IsRankOneExpLimit L ψstar ∧
      ∀ ω : Rd d, θ * levyExp (L 1) ω ≤ ψstar ω) :
    ∀ S : Mat d, S.PosDef →
      (∀ ω : Rd d, θ * levyExp (L (lamMax S • (1 : Mat d))) ω ≤ levyExp (L S) ω ∧
        levyExp (L S) ω ≤ levyExp (L (lamMax S • (1 : Mat d))) ω) ∧
      expSpread (levyExp (L S)) ≤ ENNReal.ofReal θ⁻¹ := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨ψstar, hψs, hθψ⟩ := hcomp
  intro S hS
  set t := lamMax S with htdef
  have ht : 0 < t := lamMax_pos hS
  set S₁ := t⁻¹ • S with hS₁
  have hS1 : S₁.PosDef := hS.smul (inv_pos.2 ht)
  have hS1max : lamMax S₁ = 1 := by rw [hS₁, lamMax_smul (inv_pos.2 ht).le, inv_mul_cancel₀ ht.ne']
  have hSeq : t • S₁ = S := by rw [hS₁, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hscale := (sim_general_scale hd hfam hS1 ht).2
  rw [hSeq] at hscale
  have hscaleI := (sim_general_scale hd hfam PosDef.one ht).2
  obtain ⟨Q, hQ, hQv⟩ := exists_orth_top_eigvec hS1.isHermitian
  rw [hS1max, one_smul] at hQv
  have hsand := sim_general_sandwich hd μ C L hfam S₁ hS1 hS1max Q hQ
    (by rw [fin_zero_eq (by omega)]; exact hQv)
  have hexp : ∀ ω : Rd d, ψstar (lin Qᵀ ω) ≤ levyExp (L S₁) ω ∧
      levyExp (L S₁) ω ≤ levyExp (L 1) ω := by
    rcases hinc with hID | ⟨hC, hfin⟩
    · exact (hsand.1 hID).2 ψstar hψs
    · exact hsand.2 hC hfin ψstar hψs
  have hrot := (sim_general_covariance hd μ C L hfam).2.2
  have hbounds : ∀ ω : Rd d, θ * levyExp (L (t • (1 : Mat d))) ω ≤ levyExp (L S) ω ∧
      levyExp (L S) ω ≤ levyExp (L (t • (1 : Mat d))) ω := by
    intro ω
    rw [hscale, hscaleI]
    obtain ⟨h1, h2⟩ := hexp (Real.sqrt t • ω)
    refine ⟨?_, h2⟩
    calc θ * levyExp (L 1) (Real.sqrt t • ω) = θ * levyExp (L 1) (lin Qᵀ (Real.sqrt t • ω)) := by
          rw [hrot Qᵀ (transpose_mem_orthSet hQ)]
      _ ≤ ψstar (lin Qᵀ (Real.sqrt t • ω)) := hθψ _
      _ ≤ _ := h1
  refine ⟨hbounds, expSpread_le (one_le_inv_iff₀.2 ⟨hθ0, hθ1⟩) fun R hR ω => ?_⟩
  calc levyExp (L S) (lin R ω) ≤ levyExp (L (t • (1 : Mat d))) (lin R ω) := (hbounds _).2
    _ = levyExp (L (t • (1 : Mat d))) ω := (sim_general_rot_smul_one hd hfam ht hR).2 ω
    _ ≤ θ⁻¹ * levyExp (L S) ω := by
        rw [le_inv_mul_iff₀ hθ0]; exact (hbounds ω).1

/-! ## Clause (4): the moment matrices -/

theorem inner_eq_sum (v x : Rd d) : ⟪v, x⟫ = ∑ i, v i * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

theorem momentMatrix_transpose (r : ℝ) (L : Measure (Rd d)) :
    (momentMatrix r L)ᵀ = momentMatrix r L := by
  ext i j
  simp only [momentMatrix, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  funext x
  ring

theorem momentMatrix_isHermitian (r : ℝ) (L : Measure (Rd d)) :
    (momentMatrix r L).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, momentMatrix_transpose]

theorem integrable_moment_quad {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ) (v : Rd d) :
    Integrable (fun x : Rd d => min (‖x‖ ^ 2) (r ^ 2) * ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2) L := by
  refine Integrable.mono' ((hL.integrable_min.const_mul (max 1 (r ^ 2))).const_mul (‖v‖ ^ 2))
    (Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      abs_zero]
    positivity
  have hx' : 0 < ‖x‖ ^ 2 := by positivity
  have hmin : 0 ≤ min (‖x‖ ^ 2) (r ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hx']
  have hi : ⟪v, x⟫ ^ 2 ≤ ‖v‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact sq_le_sq' (by linarith [neg_abs_le ⟪v, x⟫, abs_real_inner_le_norm v x])
      (le_trans (le_abs_self _) (abs_real_inner_le_norm v x))
  calc min (‖x‖ ^ 2) (r ^ 2) * ⟪v, x⟫ ^ 2 ≤ min (‖x‖ ^ 2) (r ^ 2) * (‖v‖ ^ 2 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hi hmin
    _ ≤ (max 1 (r ^ 2) * min (‖x‖ ^ 2) 1) * (‖v‖ ^ 2 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (min_sq_le_max_mul _ r (sq_nonneg _)) (by positivity)
    _ = ‖v‖ ^ 2 * (max 1 (r ^ 2) * min (‖x‖ ^ 2) 1) * ‖x‖ ^ 2 := by ring

/-- `⟨v, 𝓜_r(L)v⟩ = ∫ (|x|² ∧ r²) ⟨v,x⟩²/|x|² L(dx)`. -/
theorem quad_momentMatrix {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ) (v : Rd d) :
    quad (momentMatrix r L) v = ∫ x, min (‖x‖ ^ 2) (r ^ 2) * ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2 ∂L := by
  rw [quad_eq_sum]
  simp only [momentMatrix, Matrix.of_apply]
  have hint : ∀ a b, Integrable (fun x : Rd d =>
      (v a * v b) * (min (‖x‖ ^ 2) (r ^ 2) * (x a * x b) / ‖x‖ ^ 2)) L := fun a b =>
    (integrable_moment_entry hL r a b).const_mul _
  have hpt : ∀ x : Rd d, min (‖x‖ ^ 2) (r ^ 2) * ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2 =
      ∑ a, ∑ b, (v a * v b) * (min (‖x‖ ^ 2) (r ^ 2) * (x a * x b) / ‖x‖ ^ 2) := by
    intro x
    rw [inner_eq_sum, sq (∑ i, v i * x i), Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

theorem momentMatrix_posSemidef {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ) :
    (momentMatrix r L).PosSemidef :=
  posSemidef_of_quad_nonneg (momentMatrix_isHermitian r L) fun v => by
    rw [quad_momentMatrix hL]
    exact integral_nonneg fun x => by positivity

/-- **`𝓜_r` is monotone** along the order of measures. -/
theorem momentMatrix_mono {L L' : Measure (Rd d)} (hL : IsLevyMeasure L) (hL' : IsLevyMeasure L')
    (hle : L ≤ L') (r : ℝ) : loewnerLE (momentMatrix r L) (momentMatrix r L') := by
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg ((momentMatrix_isHermitian r L').sub
    (momentMatrix_isHermitian r L)) fun v => ?_
  rw [quad_sub, quad_momentMatrix hL, quad_momentMatrix hL', sub_nonneg]
  exact integral_mono_measure hle (ae_of_all _ fun x => by positivity)
    (integrable_moment_quad hL' r v)

theorem trace_momentMatrix {L : Measure (Rd d)} (hL : IsLevyMeasure L) (r : ℝ) :
    (momentMatrix r L).trace = momentTrace r L := by
  simp only [Matrix.trace, Matrix.diag, momentMatrix, Matrix.of_apply, momentTrace]
  rw [← integral_finsetSum _ fun a _ => integrable_moment_entry hL r a a]
  congr 1
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using sq_nonneg r
  have hx' : ‖x‖ ^ 2 ≠ 0 := by positivity
  rw [← Finset.sum_div, ← Finset.mul_sum,
    show ∑ i, x i * x i = ‖x‖ ^ 2 by rw [EuclideanSpace.real_norm_sq_eq]; simp [sq]]
  field_simp

/-- **The moment matrix of a rotation-invariant Lévy measure** is `(T_r(L)/d) I`. -/
theorem momentMatrix_rot [NeZero d] {L : Measure (Rd d)} (hL : IsLevyMeasure L)
    (hrot : IsRotationInvariant L) (r : ℝ) :
    momentMatrix r L = (momentTrace r L / d) • (1 : Mat d) := by
  have hinv : ∀ Q ∈ orthSet d, act Q (momentMatrix r L) = momentMatrix r L := by
    intro Q hQ
    have h := momentMatrix_push hL one_pos hQ (s := r)
    rw [one_smul, hrot Q hQ, one_pow, one_smul, div_one] at h
    exact h.symm
  have hM := eq_smul_one_of_orth_invariant hinv
  have htr := trace_momentMatrix hL r
  rw [hM, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at htr
  rw [hM]
  congr 1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [← htr]
  field_simp

/-- The sign change `diag(1, …, -1, …, 1)`, `-1` at `j`. -/
def signFlipMat (j : Fin d) : Mat d := diagonal fun k => if k = j then -1 else 1

theorem signFlipMat_mem (j : Fin d) : signFlipMat j ∈ orthSet d := by
  change signFlipMat j ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff, signFlipMat, diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  ext k
  split_ifs <;> norm_num

theorem lin_signFlipMat_ebasis [NeZero d] (j : Fin d) :
    lin (signFlipMat j) (ebasis 0) = ebasis 0 ∨ lin (signFlipMat j) (ebasis 0) = -ebasis 0 := by
  by_cases hj : j = 0
  · right
    ext k
    rw [signFlipMat, lin_diagonal_apply]
    by_cases hk : k = 0 <;> simp [ebasis, hk, hj]
  · left
    ext k
    rw [signFlipMat, lin_diagonal_apply]
    by_cases hk : k = 0
    · subst hk; simp [ebasis, Ne.symm hj]
    · simp [ebasis, hk]

theorem permMat_mem (σ : Equiv.Perm (Fin d)) : σ.permMatrix ℝ ∈ orthSet d := by
  change σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff, transpose_permMatrix, ← permMatrix_mul, inv_mul_cancel,
    permMatrix_one]

theorem lin_permMat_ebasis [NeZero d] (σ : Equiv.Perm (Fin d)) (hσ : σ 0 = 0) :
    lin (σ.permMatrix ℝ) (ebasis 0) = ebasis 0 := by
  have hσ' : ∀ i, σ i = 0 ↔ i = 0 := fun i => by
    constructor
    · intro h; exact σ.injective (h.trans hσ.symm)
    · rintro rfl; exact hσ
  ext i
  rw [ofLp_lin]
  simp only [Matrix.mulVec, dotProduct, ebasis]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ']

/-- **A matrix fixed by the orthogonal `R` with `Re₁ = ±e₁` is `diag(a, b, …, b)`.** -/
theorem eq_diag_of_fix_e1 (hd : 2 ≤ d) [NeZero d] {M : Mat d}
    (h : ∀ R ∈ orthSet d, (lin R (ebasis 0) = ebasis 0 ∨ lin R (ebasis 0) = -ebasis 0) →
      act R M = M) :
    M = diagonal fun i : Fin d => if (i : ℕ) = 0 then M 0 0 else M ⟨1, by omega⟩ ⟨1, by omega⟩ := by
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hoff : ∀ j k : Fin d, j ≠ k → M j k = 0 := by
    intro j k hjk
    have h1 := congrFun (congrFun (h _ (signFlipMat_mem j) (lin_signFlipMat_ebasis j)) j) k
    simp only [act, signFlipMat, diagonal_transpose, diagonal_mul, mul_diagonal,
      if_neg (Ne.symm hjk), if_true, mul_one, neg_mul, one_mul] at h1
    linarith
  have hdiag : ∀ k : Fin d, (k : ℕ) ≠ 0 → M k k = M i1 i1 := by
    intro k hk
    by_cases hk1 : k = i1
    · rw [hk1]
    have h01 : (0 : Fin d) ≠ i1 := by
      intro h0; have := congrArg Fin.val h0; simp [hi1] at this
    have h0k : (0 : Fin d) ≠ k := by
      intro h0; apply hk; rw [← h0]; simp
    have hfix : (Equiv.swap i1 k) 0 = 0 := Equiv.swap_apply_of_ne_of_ne h01 h0k
    have h1 := congrFun (congrFun (h _ (permMat_mem (Equiv.swap i1 k))
      (Or.inl (lin_permMat_ebasis _ hfix))) i1) i1
    simp only [act, transpose_permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, id, Equiv.Perm.inv_def, Equiv.symm_symm,
      Equiv.swap_apply_left] at h1
    exact h1
  ext i j
  rw [diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi]
      have : i = 0 := Fin.ext hi
      rw [this]
    · rw [if_neg hi]; exact hdiag i hi
  · rw [if_neg hij]; exact hoff i j hij

/-- A monotone family on `(0,∞)`, nonnegative there, tends to its infimum along `1/(k+1)`. -/
theorem tendsto_nhdsGT_of_monotone_real' {f : ℝ → ℝ} (h0 : ∀ ε, 0 < ε → 0 ≤ f ε)
    (hmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → f ε ≤ f ε') :
    Tendsto f (𝓝[>] 0) (𝓝 (⨅ k : ℕ, f (1 / ((k : ℝ) + 1)))) := by
  have hbdd : BddBelow (range fun k : ℕ => f (1 / ((k : ℝ) + 1))) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact h0 _ (by positivity)⟩
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε'
    exact lt_of_lt_of_le hb ((ciInf_le hbdd k).trans (hmono _ _ (by positivity) hk.le))
  · obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (hmono _ _ hε.1 hε.2.le) hk

/-- Polarization for a symmetric matrix: `M_{ij} = ½(q(eᵢ + eⱼ) - q(eᵢ) - q(eⱼ))`. -/
theorem entry_eq_polar {M : Mat d} (hM : M.IsHermitian) (i j : Fin d) :
    M i j = (quad M (ebasis i + ebasis j) - quad M (ebasis i) - quad M (ebasis j)) / 2 := by
  rw [quad_add_vec hM]
  have : ⟪(ebasis i : Rd d), lin M (ebasis j)⟫ = M i j := by
    have h1 : ⟪(ebasis i : Rd d), lin M (ebasis j)⟫ = (lin M (ebasis j)) i := by
      simp [ebasis, EuclideanSpace.inner_single_left]
    rw [h1, lin_apply_coord]
    simp [ebasis]
  rw [this]
  ring

theorem lamMin_mono [NeZero d] {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : loewnerLE A B) : lamMin A ≤ lamMin B :=
  (le_lamMin_iff hB _).2 fun x hx => by
    have := quad_nonneg h x
    rw [quad_sub] at this
    exact (lamMin_le_inner hA hx).trans (by unfold quad at *; linarith)

theorem lamMax_mono [NeZero d] {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : loewnerLE A B) : lamMax A ≤ lamMax B :=
  (lamMax_le_iff hA _).2 fun x hx => by
    have := quad_nonneg h x
    rw [quad_sub] at this
    exact (show quad A x ≤ quad B x by linarith).trans (quad_le_lamMax hB hx)

theorem condNum_smul {t : ℝ} (ht : 0 < t) (M : Mat d) : condNum (t • M) = condNum M := by
  unfold condNum
  rw [lamMin_smul ht.le, lamMax_smul ht.le, mul_div_mul_left _ _ ht.ne']
  simp [ht.ne']

/-- **`prop:similarity-general-bounded-shape`(4)**, moments scale by scale: under infinitely
divisible Loewner increments and `L_I ≠ 0`, `𝓜*_r = lim_{ε↓0} 𝓜_r(L_{Σ_ε})` exists and is
`diag(a_r, b_r, …, b_r)`, `θ_r ∈ [0,1]`, and `cond 𝓜_s(L_Σ) ≤ 1/θ_{s/√t}`, `t := λ_max(Σ)`, so
`cond 𝓜_s(L_Σ) ≤ 1/inf_{r>0} θ_r`, for every `Σ ∈ PD(d)` and `s > 0`. -/
theorem sim_bounded_shape_moments (hd : 2 ≤ d) (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) (hfam : IsSimGeneralFamily μ C L)
    (hID : HasIDLoewnerIncrements μ) (_hL1 : L 1 ≠ 0) :
    (∀ r : ℝ, 0 < r →
      Tendsto (fun ε => momentMatrix r (L (sigmaEps d ε))) (𝓝[>] 0) (𝓝 (rankOneMoment L r)) ∧
      ∃ a b : ℝ, rankOneMoment L r = diagonal fun i : Fin d => if (i : ℕ) = 0 then a else b) ∧
    (∀ r : ℝ, 0 < r → momentTheta L r ∈ Icc (0 : ℝ) 1) ∧
    ∀ S : Mat d, S.PosDef → ∀ s : ℝ, 0 < s →
      condNum (momentMatrix s (L S)) ≤
          (ENNReal.ofReal (momentTheta L (s / Real.sqrt (lamMax S))))⁻¹ ∧
        condNum (momentMatrix s (L S)) ≤
          (ENNReal.ofReal (⨅ r : Ioi (0 : ℝ), momentTheta L r))⁻¹ := by
  haveI : NeZero d := ⟨by omega⟩
  have hLevy : ∀ S : Mat d, S.PosDef → IsLevyMeasure (L S) := fun S hS => hfam.isLevy hS
  have hmonoL : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → L (sigmaEps d ε) ≤ L (sigmaEps d ε') := by
    intro ε ε' hε hεε'
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ _ (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) (sigmaEps_le hεε')
    exact (sim_general_id_increment hd μ C L hfam _ _ (sigmaEps_posDef hε)
      (sigmaEps_posDef (hε.trans_le hεε')) ρ hρ hρid heq).2.1
  have hfixL : ∀ R ∈ orthSet d, (lin R (ebasis 0) = ebasis 0 ∨ lin R (ebasis 0) = -ebasis 0) →
      ∀ ε : ℝ, 0 < ε → push R (L (sigmaEps d ε)) = L (sigmaEps d ε) := by
    intro R hR hRe ε hε
    have h := (sim_general_conj hd hfam (sigmaEps_posDef hε) hR).1
    rw [act_sigmaEps_of_fix hR hRe] at h
    exact h.symm
  have hL1rot := (sim_general_covariance hd μ C L hfam).2.1
  have hMI : ∀ r : ℝ, momentMatrix r (L 1) = (momentTrace r (L 1) / d) • (1 : Mat d) :=
    fun r => momentMatrix_rot (hLevy 1 PosDef.one) hL1rot r
  -- the limit at each scale
  have key : ∀ r : ℝ, 0 < r → ∃ Ms : Mat d,
      Tendsto (fun ε => momentMatrix r (L (sigmaEps d ε))) (𝓝[>] 0) (𝓝 Ms) ∧
      Ms.IsHermitian ∧ Ms.PosSemidef ∧
      (∀ ε : ℝ, 0 < ε → loewnerLE Ms (momentMatrix r (L (sigmaEps d ε)))) ∧
      ∀ R ∈ orthSet d, (lin R (ebasis 0) = ebasis 0 ∨ lin R (ebasis 0) = -ebasis 0) →
        act R Ms = Ms := by
    intro r hr
    set Mε : ℝ → Mat d := fun ε => momentMatrix r (L (sigmaEps d ε)) with hMε
    have hMmono : ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' → loewnerLE (Mε ε) (Mε ε') := fun ε ε' hε h =>
      momentMatrix_mono (hLevy _ (sigmaEps_posDef hε)) (hLevy _ (sigmaEps_posDef (hε.trans_le h)))
        (hmonoL ε ε' hε h) r
    have hq : ∀ v : Rd d, Tendsto (fun ε => quad (Mε ε) v) (𝓝[>] 0)
        (𝓝 (⨅ k : ℕ, quad (Mε (1 / ((k : ℝ) + 1))) v)) := by
      intro v
      refine tendsto_nhdsGT_of_monotone_real' (fun ε hε =>
        quad_nonneg (momentMatrix_posSemidef (hLevy _ (sigmaEps_posDef hε)) r) v)
        fun ε ε' hε h => ?_
      have := quad_nonneg (hMmono ε ε' hε h) v
      rw [quad_sub] at this
      linarith
    set q : Rd d → ℝ := fun v => ⨅ k : ℕ, quad (Mε (1 / ((k : ℝ) + 1))) v with hqdef
    set Ms : Mat d := Matrix.of fun i j =>
      (q (ebasis i + ebasis j) - q (ebasis i) - q (ebasis j)) / 2 with hMs
    have htend : Tendsto Mε (𝓝[>] 0) (𝓝 Ms) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have h := (((hq (ebasis i + ebasis j)).sub (hq (ebasis i))).sub (hq (ebasis j))).div_const 2
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (entry_eq_polar (momentMatrix_isHermitian r _) i j).symm
    have hqM : ∀ v, Tendsto (fun ε => quad (Mε ε) v) (𝓝[>] 0) (𝓝 (quad Ms v)) := fun v =>
      ((continuous_quad v).tendsto Ms).comp htend
    have hMsh : Ms.IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp only [hMs, Matrix.transpose_apply, Matrix.of_apply]
      rw [add_comm (ebasis j)]
      ring
    have hle : ∀ ε : ℝ, 0 < ε → loewnerLE Ms (Mε ε) := by
      intro ε hε
      unfold loewnerLE
      refine posSemidef_of_quad_nonneg ((momentMatrix_isHermitian r _).sub hMsh) fun v => ?_
      rw [quad_sub, sub_nonneg]
      refine le_of_tendsto (hqM v) ?_
      filter_upwards [Ioo_mem_nhdsGT hε] with ε' hε'
      have := quad_nonneg (hMmono ε' ε hε'.1 hε'.2.le) v
      rw [quad_sub] at this
      linarith
    have hpsd : Ms.PosSemidef := posSemidef_of_quad_nonneg hMsh fun v =>
      ge_of_tendsto (hqM v) (by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact quad_nonneg (momentMatrix_posSemidef (hLevy _ (sigmaEps_posDef hε)) r) v)
    refine ⟨Ms, htend, hMsh, hpsd, hle, fun R hR hRe => ?_⟩
    have hcont : Continuous fun M : Mat d => act R M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h1 : Tendsto (fun ε => act R (Mε ε)) (𝓝[>] 0) (𝓝 (act R Ms)) :=
      (hcont.tendsto Ms).comp htend
    have h2 : Tendsto (fun ε => act R (Mε ε)) (𝓝[>] 0) (𝓝 Ms) := by
      refine htend.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h := momentMatrix_push (hLevy _ (sigmaEps_posDef hε)) one_pos hR (s := r)
      rw [one_smul, hfixL R hR hRe ε hε, one_pow, one_smul, div_one] at h
      exact h
    exact tendsto_nhds_unique h1 h2
  choose! Mstar hMtend hMh hMpsd hMle hMfix using key
  have hrank : ∀ r : ℝ, 0 < r → rankOneMoment L r = Mstar r := fun r hr =>
    (hMtend r hr).limUnder_eq
  have hθ : ∀ r : ℝ, 0 < r → momentTheta L r = (d : ℝ) * lamMin (Mstar r) / momentTrace r (L 1) :=
    fun r hr => by rw [momentTheta, hrank r hr]
  have hT0 : ∀ r : ℝ, 0 ≤ momentTrace r (L 1) := fun r =>
    integral_nonneg fun x => le_min (sq_nonneg _) (sq_nonneg _)
  have hθmem : ∀ r : ℝ, 0 < r → momentTheta L r ∈ Icc (0 : ℝ) 1 := by
    intro r hr
    rw [hθ r hr]
    have hl0 := lamMin_nonneg (hMpsd r hr)
    refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg d) hl0) (hT0 r), ?_⟩
    rcases (hT0 r).lt_or_eq with hT | hT
    · rw [div_le_one hT]
      have h1 := hMle r hr 1 one_pos
      rw [sigmaEps_one, hMI r] at h1
      have h2 := lamMin_mono (hMh r hr) ((isHermitian_one.smul (IsSelfAdjoint.all _))) h1
      rw [lamMin_smul (div_nonneg (hT0 r) (Nat.cast_nonneg d)), lamMin_one, mul_one] at h2
      have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
      rw [le_div_iff₀ hd0] at h2
      linarith
    · rw [← hT, div_zero]; exact zero_le_one
  refine ⟨fun r hr => ⟨(hrank r hr).symm ▸ hMtend r hr, Mstar r 0 0,
    Mstar r ⟨1, by omega⟩ ⟨1, by omega⟩, by
      rw [hrank r hr]; exact eq_diag_of_fix_e1 hd (hMfix r hr)⟩, hθmem, fun S hS s hs => ?_⟩
  -- reduce to `λ_max(Σ) = 1`
  set t := lamMax S with htdef
  have ht : 0 < t := lamMax_pos hS
  set S₁ := t⁻¹ • S with hS₁
  have hS1 : S₁.PosDef := hS.smul (inv_pos.2 ht)
  have hS1max : lamMax S₁ = 1 := by rw [hS₁, lamMax_smul (inv_pos.2 ht).le, inv_mul_cancel₀ ht.ne']
  have hSeq : t • S₁ = S := by rw [hS₁, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hscale := (sim_general_scale hd hfam hS1 ht).1
  rw [hSeq] at hscale
  set r := s / Real.sqrt t with hr
  have hr0 : 0 < r := div_pos hs (Real.sqrt_pos.2 ht)
  have hMS : momentMatrix s (L S) = t • momentMatrix r (L S₁) := by
    have h := momentMatrix_push (hLevy _ hS1) (Real.sqrt_pos.2 ht)
      ((Matrix.orthogonalGroup (Fin d) ℝ).one_mem) (s := s)
    rw [Matrix.one_mul, transpose_one, Matrix.mul_one, Real.sq_sqrt ht.le] at h
    rw [hscale, h]
  rw [hMS, condNum_smul ht]
  -- the two bounds at `λ_max(Σ₁) = 1`
  have hS1h := hS1.isHermitian
  obtain ⟨Q, hQ, hQv⟩ := exists_orth_top_eigvec hS1h
  rw [hS1max, one_smul] at hQv
  have hl1 := lamMin_pos hS1
  set ε₀ := min (lamMin S₁) 1 / 2 with hε₀def
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; exact half_pos (lt_min hl1 one_pos)
  have hε₀l : ε₀ ≤ lamMin S₁ := by
    rw [hε₀def]; linarith [min_le_left (lamMin S₁) 1, lt_min hl1 one_pos]
  have hε₀1 : ε₀ ≤ 1 := by
    rw [hε₀def]; linarith [min_le_right (lamMin S₁) 1, lt_min hl1 one_pos]
  have hpd : (act Q (sigmaEps d ε₀)).PosDef :=
    (posDef_act_iff (orthSet_subset_glSet hQ) _).2 (sigmaEps_posDef hε₀)
  have hstep := sigmaEps_conj_le hS1h hQ hQv hε₀ hε₀l hε₀1
  obtain ⟨ρ, hρ, hρid, heq⟩ := hID _ _ hpd hS1 hstep
  have hLle := (sim_general_id_increment hd μ C L hfam _ _ hpd hS1 ρ hρ hρid heq).2.1
  rw [(sim_general_conj hd hfam (sigmaEps_posDef hε₀) hQ).1] at hLle
  have hMQ : act Q (momentMatrix r (L (sigmaEps d ε₀))) =
      momentMatrix r (push Q (L (sigmaEps d ε₀))) := by
    have h := momentMatrix_push (hLevy _ (sigmaEps_posDef hε₀)) one_pos hQ (s := r)
    rw [one_smul, one_pow, one_smul, div_one] at h
    exact h.symm
  have hlow : loewnerLE (act Q (Mstar r)) (momentMatrix r (L S₁)) := by
    refine loewnerLE_trans' (loewnerLE_act Q (hMle r hr0 ε₀ hε₀)) ?_
    rw [hMQ]
    have hpushLevy : IsLevyMeasure (push Q (L (sigmaEps d ε₀))) := by
      rw [← (sim_general_conj hd hfam (sigmaEps_posDef hε₀) hQ).1]; exact hLevy _ hpd
    exact momentMatrix_mono hpushLevy (hLevy _ hS1) hLle r
  have hMQh : (act Q (Mstar r)).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, act, transpose_mul, transpose_mul,
      transpose_transpose, (show (Mstar r)ᵀ = Mstar r from by
        have := (hMh r hr0).eq; rwa [conjTranspose_eq_transpose_of_trivial] at this),
      Matrix.mul_assoc]
  have hMSh := momentMatrix_isHermitian r (L S₁)
  have hlmin : lamMin (Mstar r) ≤ lamMin (momentMatrix r (L S₁)) := by
    have := lamMin_mono hMQh hMSh hlow
    rwa [act, lamMin_conj_orth hQ (hMh r hr0)] at this
  have hup : loewnerLE (momentMatrix r (L S₁)) ((momentTrace r (L 1) / d) • (1 : Mat d)) := by
    rw [← hMI r]
    obtain ⟨ρ', hρ', hρid', heq'⟩ := hID _ _ hS1 PosDef.one
      (loewnerLE_one_of_lamMax hS1h hS1max)
    exact momentMatrix_mono (hLevy _ hS1) (hLevy 1 PosDef.one)
      (sim_general_id_increment hd μ C L hfam _ _ hS1 PosDef.one ρ' hρ' hρid' heq').2.1 r
  have he0 : ‖(ebasis (0 : Fin d) : Rd d)‖ = 1 := by simp [ebasis]
  have hlm1 : lamMax (1 : Mat d) = 1 := by
    refine le_antisymm ((lamMax_le_iff isHermitian_one 1).2 fun x hx => by
      rw [quad_one, hx, one_pow]) ?_
    have := quad_le_lamMax isHermitian_one he0
    rwa [quad_one, he0, one_pow] at this
  have hlmax : lamMax (momentMatrix r (L S₁)) ≤ momentTrace r (L 1) / d := by
    have := lamMax_mono hMSh (isHermitian_one.smul (IsSelfAdjoint.all _)) hup
    rwa [lamMax_smul (div_nonneg (hT0 r) (Nat.cast_nonneg d)), hlm1, mul_one] at this
  have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hfirst : condNum (momentMatrix r (L S₁)) ≤ (ENNReal.ofReal (momentTheta L r))⁻¹ := by
    rw [hθ r hr0]
    rcases (lamMin_nonneg (hMpsd r hr0)).lt_or_eq with hpos | h0
    · set m := lamMin (Mstar r) with hm
      have hlM : 0 < lamMin (momentMatrix r (L S₁)) := lt_of_lt_of_le hpos hlmin
      have hT : 0 < momentTrace r (L 1) / d :=
        lt_of_lt_of_le hlM ((lamMin_le_lamMax hMSh).trans hlmax)
      have hT' : 0 < momentTrace r (L 1) := by
        have := mul_pos hT hd0; rwa [div_mul_cancel₀ _ hd0.ne'] at this
      rw [condNum, if_neg hlM.ne', ← ENNReal.ofReal_inv_of_pos (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc lamMax (momentMatrix r (L S₁)) / lamMin (momentMatrix r (L S₁))
          ≤ (momentTrace r (L 1) / d) / m :=
            div_le_div₀ hT.le hlmax hpos hlmin
        _ = ((d : ℝ) * m / momentTrace r (L 1))⁻¹ := by field_simp
    · rw [← h0, mul_zero, zero_div, ENNReal.ofReal_zero, ENNReal.inv_zero]
      exact le_top
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hinf : (⨅ r' : Ioi (0 : ℝ), momentTheta L r') ≤ momentTheta L r := by
    have hbdd : BddBelow (range fun r' : Ioi (0 : ℝ) => momentTheta L r') :=
      ⟨0, by rintro _ ⟨r', rfl⟩; exact (hθmem r'.1 r'.2).1⟩
    exact ciInf_le hbdd ⟨r, hr0⟩
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal hinf)

end AffineHemigroup
