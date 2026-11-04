/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SpectralCalculus

/-!
# Ky Fan's minimum principle (`lem:spectral-cones`(1))

Blueprint: `blueprint/src/parts/05-wedges.tex`, `lem:spectral-cones`(1) (wave 2, group F, Q-0281):
`s_k(λ↑(X)) = min{tr(UᵀXU) : UᵀU = I}`, its consequences, the Lipschitz bound
`|s_k(λ↑(X)) - s_k(λ↑(Y))| ≤ k‖X - Y‖` and `λ↑(X + Y) ≺ λ↑(X) + λ↑(Y)`, and the continuity of
`λ↑` on `Sym(d)` that the later clauses read. Proved in-house, as the blueprint writes it: in an
eigenbasis `tr(UᵀXU) = ∑ⱼ λⱼpⱼ` with weights `0 ≤ pⱼ ≤ 1` summing to `k` (`pⱼ` is a diagonal entry
of the projection `WWᵀ`, `W = VᵀU`), and such a weighted sum is at least the sum of the `k` smallest
`λⱼ`. Lean core only.
-/

namespace AffineHemigroup

open Matrix Filter
open scoped Topology RealInnerProductSpace

variable {d : ℕ}

/-! ## The weighted-sum inequality -/

/-- The number of indices of `Fin d` below `k ≤ d` is `k`. -/
theorem card_filter_lt {k : ℕ} (hkd : k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val < k)).card = k := by
  have h := Fin.card_filter_val_lt (n := d) (m := k)
  rw [h]
  omega

/-- **Weights between `0` and `1` summing to `k`** put at least the `k` smallest values:
for `λ` increasing, `∑_{j<k} λⱼ ≤ ∑ⱼ λⱼ pⱼ`. -/
theorem sum_filter_le_weighted {l p : Fin d → ℝ} (hl : Monotone l) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (hsum : ∑ j, p j = k) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), l j ≤ ∑ j, l j * p j := by
  set c := l ⟨k - 1, by omega⟩
  set q : Fin d → ℝ := fun j => if j.val < k then 1 else 0 with hq
  have hqsum : ∑ j, q j = k := by
    rw [hq, ← Finset.sum_filter, Finset.sum_const, card_filter_lt hkd, nsmul_eq_mul, mul_one]
  have hlhs : ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), l j = ∑ j, l j * q j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hq]
    split_ifs <;> simp
  have hterm : ∀ j, 0 ≤ (l j - c) * (p j - q j) := by
    intro j
    by_cases hj : j.val < k
    · have h1 : l j ≤ c := hl (Fin.le_def.2 (by simp; omega))
      have h2 : p j - q j ≤ 0 := by simp only [hq, if_pos hj]; linarith [hp1 j]
      nlinarith
    · have h1 : c ≤ l j := hl (Fin.le_def.2 (by simp; omega))
      have h2 : 0 ≤ p j - q j := by simp only [hq, if_neg hj]; linarith [hp0 j]
      nlinarith
  have hid : ∑ j, l j * p j - ∑ j, l j * q j =
      ∑ j, (l j - c) * (p j - q j) + c * (∑ j, p j - ∑ j, q j) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, hqsum, sub_self, mul_zero, add_zero] at hid
  rw [hlhs]
  linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hterm j]

/-! ## The trace of `UᵀXU` in an eigenbasis -/

/-- `tr(Uᵀ (V diag(l) Vᵀ) U) = ∑ⱼ lⱼ ∑_b (VᵀU)ⱼ_b²`. -/
theorem trace_udiag_compress {k : ℕ} (V : Mat d) (l : Fin d → ℝ) (U : Matrix (Fin d) (Fin k) ℝ) :
    (Uᵀ * udiag V l * U).trace = ∑ j, l j * ∑ b, ((Vᵀ * U) j b) ^ 2 := by
  have h : Uᵀ * udiag V l * U = (Vᵀ * U)ᵀ * diagonal l * (Vᵀ * U) := by
    simp only [udiag, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hb : ∀ b, ((Vᵀ * U)ᵀ * diagonal l * (Vᵀ * U)) b b =
      ∑ j, (Vᵀ * U) j b * l j * (Vᵀ * U) j b := by
    intro b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [h, Matrix.trace]
  simp only [Matrix.diag, hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The weights**: for `V` orthogonal and `UᵀU = I`, the numbers `pⱼ = ∑_b (VᵀU)ⱼ_b²` lie in
`[0, 1]` and sum to `k`. -/
theorem weights_props {k : ℕ} {V : Mat d} (hV : V * Vᵀ = 1) {U : Matrix (Fin d) (Fin k) ℝ}
    (hU : Uᵀ * U = 1) :
    (∀ j, 0 ≤ ∑ b, ((Vᵀ * U) j b) ^ 2) ∧ (∀ j, ∑ b, ((Vᵀ * U) j b) ^ 2 ≤ 1) ∧
      ∑ j, ∑ b, ((Vᵀ * U) j b) ^ 2 = k := by
  set W := Vᵀ * U with hW
  have hWW : Wᵀ * W = 1 := by
    rw [hW, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV,
      Matrix.one_mul, hU]
  -- `P = WWᵀ` is idempotent and symmetric
  have hP2 : (W * Wᵀ) * (W * Wᵀ) = W * Wᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hWW, Matrix.one_mul]
  have hPjj : ∀ j, (W * Wᵀ) j j = ∑ b, (W j b) ^ 2 := fun j => by
    simp [Matrix.mul_apply, sq]
  refine ⟨fun j => Finset.sum_nonneg fun b _ => sq_nonneg _, fun j => ?_, ?_⟩
  · have h1 : (W * Wᵀ) j j = ∑ m, ((W * Wᵀ) j m) ^ 2 := by
      conv_lhs => rw [← hP2]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hsym : (W * Wᵀ) m j = (W * Wᵀ) j m := by
        simp [Matrix.mul_apply, mul_comm]
      rw [hsym, sq]
    have h2 : ((W * Wᵀ) j j) ^ 2 ≤ (W * Wᵀ) j j := by
      have h3 := Finset.single_le_sum (f := fun m => ((W * Wᵀ) j m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
      rw [← h1] at h3
      exact h3
    have h0 : 0 ≤ (W * Wᵀ) j j := by rw [hPjj]; exact Finset.sum_nonneg fun b _ => sq_nonneg _
    rw [← hPjj]
    nlinarith
  · rw [Finset.sum_comm]
    have hb : ∀ b, ∑ j, (W j b) ^ 2 = 1 := fun b => by
      have := congrFun (congrFun hWW b) b
      simpa [Matrix.mul_apply, sq] using this
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## Ky Fan's minimum principle -/

/-- The first `k` columns of `V`, as a `d × k` matrix. -/
def firstCols {k : ℕ} (hkd : k ≤ d) (V : Mat d) : Matrix (Fin d) (Fin k) ℝ :=
  Matrix.of fun a b => V a (Fin.castLE hkd b)

theorem firstCols_orth {k : ℕ} (hkd : k ≤ d) {V : Mat d} (hV : V * Vᵀ = 1) :
    (firstCols hkd V)ᵀ * firstCols hkd V = 1 := by
  have hV' : Vᵀ * V = 1 := transpose_mul_self_of_mul_transpose hV
  ext b c
  have h := congrFun (congrFun hV' (Fin.castLE hkd b)) (Fin.castLE hkd c)
  simp only [firstCols, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] at h ⊢
  rw [h, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.castLE_inj]

theorem transpose_mul_firstCols {k : ℕ} (hkd : k ≤ d) {V : Mat d} (hV : V * Vᵀ = 1)
    (j : Fin d) (b : Fin k) :
    (Vᵀ * firstCols hkd V) j b = if j = Fin.castLE hkd b then 1 else 0 := by
  have hV' : Vᵀ * V = 1 := transpose_mul_self_of_mul_transpose hV
  have h := congrFun (congrFun hV' j) (Fin.castLE hkd b)
  simp only [firstCols, Matrix.mul_apply, Matrix.of_apply] at h ⊢
  rw [h, Matrix.one_apply]

/-- **`lem:spectral-cones`(1)**, sums: `s_k(λ↑(X)) = min{tr(UᵀXU) : U ∈ ℝ^{d×k}, UᵀU = I}`. -/
theorem partialSum_eigUp_isLeast (_hd : 1 ≤ d) {X : Mat d} (hX : X.IsSymm) (k : ℕ) (hk : 1 ≤ k)
    (hkd : k ≤ d) :
    IsLeast {s : ℝ | ∃ U : Matrix (Fin d) (Fin k) ℝ, Uᵀ * U = 1 ∧ s = (Uᵀ * X * U).trace}
      (partialSumUp k (eigUp X)) := by
  have hXh : X.IsHermitian := isHermitian_of_isSymm hX
  obtain ⟨V, hV, hXV⟩ := exists_udiag_eigUp hXh
  have hmono := eigUp_monotone hXh
  rw [partialSumUp_of_monotone hmono]
  refine ⟨⟨firstCols hkd V, firstCols_orth hkd hV, ?_⟩, ?_⟩
  · rw [hXV, trace_udiag_compress, ← hXV]
    simp only [transpose_mul_firstCols hkd hV]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < k
    · have : ∑ b : Fin k, ((if j = Fin.castLE hkd b then (1 : ℝ) else 0)) ^ 2 = 1 := by
        rw [Finset.sum_eq_single ⟨j.val, hj⟩]
        · simp
        · intro b _ hb
          have : j ≠ Fin.castLE hkd b := by
            intro h; apply hb; ext; simp [h]
          simp [this]
        · simp
      rw [if_pos hj, this, mul_one]
    · have : ∑ b : Fin k, ((if j = Fin.castLE hkd b then (1 : ℝ) else 0)) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        have : j ≠ Fin.castLE hkd b := by
          intro h; apply hj; rw [h]; simp
        simp [this]
      rw [if_neg hj, this, mul_zero]
  · rintro s ⟨U, hU, rfl⟩
    obtain ⟨h0, h1, hsum⟩ := weights_props hV hU
    rw [hXV, trace_udiag_compress, ← hXV]
    exact sum_filter_le_weighted hmono h0 h1 hk hkd hsum

/-- `s_k(λ↑(X)) ≤ tr(UᵀXU)` whenever `UᵀU = I`. -/
theorem partialSum_eigUp_le {X : Mat d} (hX : X.IsSymm) {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    {U : Matrix (Fin d) (Fin k) ℝ} (hU : Uᵀ * U = 1) :
    partialSumUp k (eigUp X) ≤ (Uᵀ * X * U).trace :=
  (partialSum_eigUp_isLeast (by omega) hX k hk hkd).2 ⟨U, hU, rfl⟩

/-- The minimum is attained. -/
theorem exists_partialSum_eigUp_eq {X : Mat d} (hX : X.IsSymm) {k : ℕ} (hk : 1 ≤ k)
    (hkd : k ≤ d) :
    ∃ U : Matrix (Fin d) (Fin k) ℝ, Uᵀ * U = 1 ∧ partialSumUp k (eigUp X) = (Uᵀ * X * U).trace :=
  (partialSum_eigUp_isLeast (by omega) hX k hk hkd).1

/-! ## Consequences -/

/-- `tr(UᵀEU) ≤ k‖E‖` for `UᵀU = I`: each diagonal entry is a Rayleigh quotient at a unit column. -/
theorem trace_compress_le {k : ℕ} {U : Matrix (Fin d) (Fin k) ℝ} (hU : Uᵀ * U = 1) (E : Mat d) :
    (Uᵀ * E * U).trace ≤ k * ‖lin E‖ := by
  have hcol : ∀ b : Fin k, (Uᵀ * E * U) b b = quad E (WithLp.toLp 2 fun a => U a b) := by
    intro b
    rw [quad_eq_dotProduct]
    simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have hnorm : ∀ b : Fin k, ‖(WithLp.toLp 2 fun a => U a b : Rd d)‖ = 1 := by
    intro b
    have h1 := quad_one (WithLp.toLp 2 fun a => U a b : Rd d)
    rw [quad_eq_dotProduct] at h1
    have h2 := congrFun (congrFun hU b) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h2
    have h3 : (WithLp.toLp 2 fun a => U a b : Rd d).ofLp ⬝ᵥ (1 : Mat d) *ᵥ
        (WithLp.toLp 2 fun a => U a b : Rd d).ofLp = 1 := by
      simp [dotProduct, h2]
    rw [h3] at h1
    have h4 := norm_nonneg (WithLp.toLp 2 fun a => U a b : Rd d)
    nlinarith
  have hb : ∀ b : Fin k, quad E (WithLp.toLp 2 fun a => U a b) ≤ ‖lin E‖ := by
    intro b
    set u : Rd d := WithLp.toLp 2 fun a => U a b
    calc quad E u = ⟪u, lin E u⟫ := rfl
      _ ≤ ‖u‖ * ‖lin E u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖lin E‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left ((lin E).le_opNorm u) (norm_nonneg _)
      _ = ‖lin E‖ := by rw [hnorm b]; ring
  rw [Matrix.trace]
  simp only [Matrix.diag, hcol]
  calc ∑ b : Fin k, quad E (WithLp.toLp 2 fun a => U a b) ≤ ∑ _b : Fin k, ‖lin E‖ :=
        Finset.sum_le_sum fun b _ => hb b
    _ = k * ‖lin E‖ := by simp

/-- **`lem:spectral-cones`(1)**, consequently: `|s_k(λ↑(X)) - s_k(λ↑(Y))| ≤ k‖X - Y‖`, `‖·‖` the
operator norm. -/
theorem partialSum_eigUp_lipschitz (_hd : 1 ≤ d) {X Y : Mat d} (hX : X.IsSymm) (hY : Y.IsSymm)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    |partialSumUp k (eigUp X) - partialSumUp k (eigUp Y)| ≤ k * ‖lin (X - Y)‖ := by
  have hone : ∀ {A B : Mat d}, A.IsSymm → B.IsSymm →
      partialSumUp k (eigUp A) - partialSumUp k (eigUp B) ≤ k * ‖lin (A - B)‖ := by
    intro A B hA hB
    obtain ⟨U, hU, hBU⟩ := exists_partialSum_eigUp_eq hB hk hkd
    have h1 := partialSum_eigUp_le hA hk hkd hU
    have h2 := trace_compress_le hU (A - B)
    have h3 : (Uᵀ * (A - B) * U).trace = (Uᵀ * A * U).trace - (Uᵀ * B * U).trace := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    linarith
  rw [abs_le]
  refine ⟨?_, hone hX hY⟩
  have h := hone hY hX
  have hn : ‖lin (Y - X)‖ = ‖lin (X - Y)‖ := by
    rw [← neg_sub, show lin (-(X - Y)) = -lin (X - Y) from map_neg _ _, norm_neg]
  rw [hn] at h
  linarith

/-- **`lem:spectral-cones`(1)**, consequently: `λ↑(X + Y) ≺ λ↑(X) + λ↑(Y)`. -/
theorem eigUp_add_majorized (_hd : 1 ≤ d) {X Y : Mat d} (hX : X.IsSymm) (hY : Y.IsSymm) :
    IsMajorized (eigUp (X + Y)) (eigUp X + eigUp Y) := by
  have hXh := isHermitian_of_isSymm hX
  have hYh := isHermitian_of_isSymm hY
  have hXY : (X + Y).IsSymm := hX.add hY
  have hmono : Monotone (eigUp X + eigUp Y) := (eigUp_monotone hXh).add (eigUp_monotone hYh)
  refine ⟨fun k hk hkd => ?_, ?_⟩
  · obtain ⟨U, hU, hXYU⟩ := exists_partialSum_eigUp_eq hXY hk hkd.le
    have h1 := partialSum_eigUp_le hX hk hkd.le hU
    have h2 := partialSum_eigUp_le hY hk hkd.le hU
    have h3 : (Uᵀ * (X + Y) * U).trace = (Uᵀ * X * U).trace + (Uᵀ * Y * U).trace := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    have h4 : partialSumUp k (eigUp X + eigUp Y) =
        partialSumUp k (eigUp X) + partialSumUp k (eigUp Y) := by
      rw [partialSumUp_of_monotone hmono, partialSumUp_of_monotone (eigUp_monotone hXh),
        partialSumUp_of_monotone (eigUp_monotone hYh), ← Finset.sum_add_distrib]
      rfl
    linarith
  · rw [partialSumUp_card, partialSumUp_card, sum_eigUp (isHermitian_of_isSymm hXY)]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_eigUp hXh, sum_eigUp hYh,
      Matrix.trace_add]

/-! ## The continuity of `λ↑` on `Sym(d)` -/

/-- **Weyl's bound, crudely**: `|λ↑ₖ(X) - λ↑ₖ(Y)| ≤ (2k+1)‖X - Y‖`, from `λ↑ₖ = s_{k+1} - s_k`. -/
theorem eigUp_lipschitz {X Y : Mat d} (hX : X.IsSymm) (hY : Y.IsSymm) (k : Fin d) :
    |eigUp X k - eigUp Y k| ≤ (2 * (k : ℝ) + 1) * ‖lin (X - Y)‖ := by
  have hd : 1 ≤ d := by have := k.2; omega
  have hs : ∀ {A : Mat d}, A.IsSymm →
      eigUp A k = partialSumUp (k + 1) (eigUp A) - partialSumUp k (eigUp A) := by
    intro A hA
    have hm := eigUp_monotone (isHermitian_of_isSymm hA)
    rw [partialSumUp_of_monotone hm, partialSumUp_of_monotone hm]
    have hsplit : Finset.univ.filter (fun i : Fin d => i.val < (k : ℕ) + 1) =
        insert k (Finset.univ.filter (fun i : Fin d => i.val < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    ring
  have hlip : ∀ m : ℕ, m ≤ d → |partialSumUp m (eigUp X) - partialSumUp m (eigUp Y)| ≤
      m * ‖lin (X - Y)‖ := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simp [partialSumUp]
    · exact partialSum_eigUp_lipschitz hd hX hY m hpos hm
  rw [hs hX, hs hY]
  have h1 := hlip (k + 1) (by omega)
  have h2 := hlip k (by omega)
  have hn := norm_nonneg (lin (X - Y))
  push_cast at h1
  calc |partialSumUp (↑k + 1) (eigUp X) - partialSumUp (↑k) (eigUp X) -
        (partialSumUp (↑k + 1) (eigUp Y) - partialSumUp (↑k) (eigUp Y))|
      = |(partialSumUp (↑k + 1) (eigUp X) - partialSumUp (↑k + 1) (eigUp Y)) -
          (partialSumUp (↑k) (eigUp X) - partialSumUp (↑k) (eigUp Y))| := by ring_nf
    _ ≤ |partialSumUp (↑k + 1) (eigUp X) - partialSumUp (↑k + 1) (eigUp Y)| +
          |partialSumUp (↑k) (eigUp X) - partialSumUp (↑k) (eigUp Y)| := abs_sub _ _
    _ ≤ ((k : ℝ) + 1) * ‖lin (X - Y)‖ + (k : ℝ) * ‖lin (X - Y)‖ := add_le_add h1 h2
    _ = (2 * (k : ℝ) + 1) * ‖lin (X - Y)‖ := by ring

/-- `X ↦ lin X` is continuous. -/
theorem continuous_lin : Continuous (lin : Mat d → Rd d →L[ℝ] Rd d) := by
  let f : Mat d →ₗ[ℝ] (Rd d →L[ℝ] Rd d) :=
    { toFun := lin, map_add' := lin_add, map_smul' := fun c A => lin_smul c A }
  exact f.continuous_of_finiteDimensional

/-- **`λ↑` is continuous along symmetric matrices**: if `Xₙ → X` with every `Xₙ` symmetric and `X`
symmetric, then `λ↑(Xₙ) → λ↑(X)`. -/
theorem tendsto_eigUp {ι : Type*} {l : Filter ι} {Xs : ι → Mat d} {X : Mat d}
    (hXs : ∀ n, (Xs n).IsSymm) (hX : X.IsSymm) (h : Tendsto Xs l (𝓝 X)) :
    Tendsto (fun n => eigUp (Xs n)) l (𝓝 (eigUp X)) := by
  have hlin : Tendsto (fun n => ‖lin (Xs n - X)‖) l (𝓝 0) := by
    have h1 : Tendsto (fun n => Xs n - X) l (𝓝 0) := by
      simpa using h.sub_const X
    have h2 := (continuous_lin.tendsto (0 : Mat d)).comp h1
    rw [show lin (0 : Mat d) = 0 from map_zero _] at h2
    simpa using h2.norm
  refine tendsto_pi_nhds.2 fun k => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun n => (2 * (k : ℝ) + 1) * ‖lin (Xs n - X)‖) l (𝓝 0) := by
    simpa using hlin.const_mul (2 * (k : ℝ) + 1)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc
  rw [Real.norm_eq_abs]
  exact eigUp_lipschitz (hXs n) hX k

end AffineHemigroup
