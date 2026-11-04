/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.ConeOrders
import AffineHemigroup.LieProduct
import AffineHemigroup.OneParameter

/-!
# `lem:cone-orders-closed`: closed invariant orders and their tangent wedges

Blueprint: `blueprint/src/parts/05-wedges.tex`, `lem:cone-orders-closed` (`thm:cone-orders`(2);
wave 2, group F, Q-0281). For a closed step set `𝒦` whose `≤_𝒦` is a partial order, the semigroup
`𝒮_𝒦` is closed in `GL(d)`, contains `O(d)` and is closed under products
(`prop:invariant-orders`(3)); its tangent set `𝓛 = {B : e^{tB} ∈ 𝒮_𝒦, t ≥ 0}` is closed under
positive multiples, limits and, by the Lie product formula (`AffineHemigroup.LieProduct`), sums; the
symmetric `X` in it are `C(𝒦)` (`e^{tX}e^{tX} = e^{2tX}`), the skew `K` all lie in it (`e^{tK}` is
orthogonal), and so `𝓛 = {B : sym B ∈ C(𝒦)}`. The equivalence (a)–(c) is the blueprint's: (c) ⇒ (b)
by `M^{j+τ} = M^{1/2}M^{j-1+τ}M^{1/2}`, (b) ⇒ (a) and (a) ⇒ (c) through `thm:cone-orders`(1), which
spends ledger A9; so does the inclusion `≼_{C(𝒦)} ⊆ ≤_𝒦`.
-/

namespace AffineHemigroup

open Matrix Filter Set
open scoped Topology

variable {d : ℕ}

/-! ## The semigroup `𝒮_𝒦` -/

/-- `e^X ∈ GL(d)`. -/
theorem mexp_mem_glSet (X : Mat d) : mexp X ∈ glSet d := by
  have h := det_mexp_smul X 1
  rw [one_smul, one_mul] at h
  change IsUnit (mexp X).det
  rw [h]
  exact (Real.exp_pos _).ne'.isUnit

/-- `𝒮_𝒦` is closed in `GL(d)` when `𝒦` is closed in `PD(d)`. -/
theorem stepSemigroup_closed {K : Set (Mat d)} (hKc : closure K ∩ pdSet d ⊆ K) {A : Mat d}
    {As : ℕ → Mat d} (hAs : ∀ n, As n ∈ stepSemigroup K) (hlim : Tendsto As atTop (𝓝 A))
    (hA : A ∈ glSet d) : A ∈ stepSemigroup K := by
  refine ⟨hA, hKc ⟨?_, ?_⟩⟩
  · have hT : Tendsto (fun n => As n * (As n)ᵀ) atTop (𝓝 (A * Aᵀ)) :=
      hlim.mul ((Continuous.matrix_transpose continuous_id).tendsto A |>.comp hlim)
    exact mem_closure_of_tendsto hT (Eventually.of_forall fun n => (hAs n).2)
  · have := (posDef_act_iff hA 1).2 Matrix.PosDef.one
    rwa [act, Matrix.mul_one] at this

/-- The facts about `𝒮_𝒦` that a closed partial order gives. -/
theorem stepSemigroup_props (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    (1 : Mat d) ∈ K ∧ (∀ M ∈ K, ∀ N ∈ K, msqrt M * N * msqrt M ∈ K) ∧
      (∀ A ∈ stepSemigroup K, ∀ B ∈ stepSemigroup K, A * B ∈ stepSemigroup K) ∧
      (∀ Q ∈ orthSet d, Q ∈ stepSemigroup K) ∧
      (∀ A ∈ stepSemigroup K, ∀ n : ℕ, A ^ n ∈ stepSemigroup K) := by
  have h1 : (1 : Mat d) ∈ K := by
    have := (hpo.refl 1 Matrix.PosDef.one).2.2
    rwa [relStep_one_left] at this
  have htrans : ∀ S S' S'' : Mat d, S.PosDef → S'.PosDef → S''.PosDef →
      stepLE K S S' → stepLE K S' S'' → stepLE K S S'' :=
    fun S S' S'' hS hS' hS'' h h' => hpo.trans S hS S' hS' S'' hS'' h h'
  have hprod := ((stepLE_trans_tfae hd hK).out 0 2).1 htrans
  have hone : (1 : Mat d) ∈ stepSemigroup K :=
    ⟨by simp [glSet], by rw [transpose_one, Matrix.mul_one]; exact h1⟩
  refine ⟨h1, ((stepLE_trans_tfae hd hK).out 0 1).1 htrans, hprod, fun Q hQ =>
    ⟨orthSet_subset_glSet hQ, by rw [orth_mul_transpose hQ]; exact h1⟩, fun A hA n => ?_⟩
  induction n with
  | zero => simpa using hone
  | succ n ih => rw [pow_succ]; exact hprod _ ih _ hA

/-! ## The tangent wedge -/

/-- **The tangent set** `𝓛 = {B : e^{tB} ∈ 𝒮_𝒦 for every t ≥ 0}`. -/
def tangentWedge (K : Set (Mat d)) : Set (Mat d) :=
  {B | ∀ t : ℝ, 0 ≤ t → mexp (t • B) ∈ stepSemigroup K}

/-- **`𝓛` is closed under sums**, by the Lie product formula. -/
theorem tangentWedge_add (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) {B B' : Mat d}
    (hB : B ∈ tangentWedge K) (hB' : B' ∈ tangentWedge K) : B + B' ∈ tangentWedge K := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, hprod, -, hpow⟩ := stepSemigroup_props hd hK hpo
  intro t ht
  have hlie := tendsto_lie_product (t • B) (t • B')
  rw [← smul_add] at hlie
  refine stepSemigroup_closed hKc (fun n => hpow _ (hprod _ ?_ _ ?_) n) hlie (mexp_mem_glSet _)
  · rw [smul_smul]; exact hB _ (mul_nonneg (by positivity) ht)
  · rw [smul_smul]; exact hB' _ (mul_nonneg (by positivity) ht)

/-- `𝓛` is a closed convex cone. -/
theorem tangentWedge_isClosedConvexCone (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    IsClosedConvexCone (tangentWedge K) := by
  obtain ⟨h1, -, -, -, -⟩ := stepSemigroup_props hd hK hpo
  have hsmul : ∀ c : ℝ, 0 ≤ c → ∀ B ∈ tangentWedge K, c • B ∈ tangentWedge K :=
    fun c hc B hB t ht => by rw [smul_smul]; exact hB _ (mul_nonneg ht hc)
  refine ⟨?_, fun B hB B' hB' a b ha hb _ =>
    tangentWedge_add hd hK hKc hpo (hsmul a ha B hB) (hsmul b hb B' hB'),
    fun t _ => ⟨by rw [smul_zero, mexp_zero]; simp [glSet], by
      rw [smul_zero, mexp_zero, transpose_one, Matrix.mul_one]; exact h1⟩, hsmul⟩
  refine isClosed_of_closure_subset fun B hB t ht => ?_
  obtain ⟨Bs, hBs, hlim⟩ := mem_closure_iff_seq_limit.1 hB
  have hT : Tendsto (fun n => mexp (t • Bs n)) atTop (𝓝 (mexp (t • B))) :=
    (continuous_mexp.tendsto _).comp (hlim.const_smul t)
  exact stepSemigroup_closed hKc (fun n => hBs n t ht) hT (mexp_mem_glSet _)

/-- For symmetric `X`: `X ∈ 𝓛` if and only if `X ∈ C(𝒦)`. -/
theorem mem_tangentWedge_iff_infCone {K : Set (Mat d)} {X : Mat d} (hX : X.IsSymm) :
    X ∈ tangentWedge K ↔ X ∈ infCone K := by
  have hsq : ∀ t : ℝ, mexp (t • X) * (mexp (t • X))ᵀ = mexp ((2 * t) • X) := fun t => by
    rw [← mexp_smul_transpose, hX.eq, ← mexp_add_smul, two_mul]
  constructor
  · intro h
    refine ⟨hX, fun s hs => ?_⟩
    have := (h (s / 2) (by positivity)).2
    rwa [hsq, show 2 * (s / 2) = s by ring] at this
  · rintro ⟨-, h⟩ t ht
    exact ⟨mexp_mem_glSet _, by rw [hsq]; exact h _ (by positivity)⟩

/-- Every skew-symmetric matrix lies in `𝓛`. -/
theorem skew_mem_tangentWedge (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) {B : Mat d} (hB : Bᵀ = -B) :
    B ∈ tangentWedge K := by
  obtain ⟨h1, -, -, -, -⟩ := stepSemigroup_props hd hK hpo
  intro t _
  refine ⟨mexp_mem_glSet _, ?_⟩
  rw [← mexp_smul_transpose, hB, smul_neg, ← neg_smul]
  have := mexp_neg_mul_mexp B (-t)
  rw [neg_neg] at this
  rw [show mexp (t • B) * mexp ((-t) • B) = 1 by
    rw [← mexp_add_smul, add_neg_cancel, zero_smul, mexp_zero]]
  exact h1

/-- `B = sym B + skew B`. -/
theorem symPart_add_skew (B : Mat d) : B = symPart B + (1 / 2 : ℝ) • (B - Bᵀ) := by
  rw [symPart, ← smul_add]
  rw [show B + Bᵀ + (B - Bᵀ) = (2 : ℝ) • B by rw [two_smul]; abel, smul_smul]
  norm_num

theorem symPart_isSymm (B : Mat d) : (symPart B).IsSymm := by
  rw [symPart, Matrix.IsSymm, transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- **`𝓛 = {B : sym B ∈ C(𝒦)}`.** -/
theorem tangentWedge_eq (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    tangentWedge K = {B | symPart B ∈ infCone K} := by
  have hskew : ∀ B : Mat d, ((1 / 2 : ℝ) • (B - Bᵀ))ᵀ = -((1 / 2 : ℝ) • (B - Bᵀ)) := fun B => by
    rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
  ext B
  constructor
  · intro hB
    have hn : -((1 / 2 : ℝ) • (B - Bᵀ)) ∈ tangentWedge K :=
      skew_mem_tangentWedge hd hK hpo (by rw [transpose_neg, hskew, neg_neg])
    have := tangentWedge_add hd hK hKc hpo hB hn
    rw [show B + -((1 / 2 : ℝ) • (B - Bᵀ)) = symPart B by
      ext i j
      simp only [symPart, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.transpose_apply, smul_eq_mul]
      ring] at this
    exact (mem_tangentWedge_iff_infCone (symPart_isSymm B)).1 this
  · intro hB
    rw [symPart_add_skew B]
    exact tangentWedge_add hd hK hKc hpo ((mem_tangentWedge_iff_infCone (symPart_isSymm B)).2 hB)
      (skew_mem_tangentWedge hd hK hpo (hskew B))

/-- `C(𝒦)` is a closed convex cone. -/
theorem infCone_isClosedConvexCone (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    IsClosedConvexCone (infCone K) := by
  obtain ⟨-, hsmul, hclosed, -⟩ := infCone_props hd hK
  obtain ⟨h1, -, -, -, -⟩ := stepSemigroup_props hd hK hpo
  have hL := tangentWedge_isClosedConvexCone hd hK hKc hpo
  refine ⟨hclosed hKc, fun X hX Y hY a b ha hb hab => ?_,
    ⟨isSymm_zero, fun t _ => by rw [smul_zero, mexp_zero]; exact h1⟩, hsmul⟩
  have hXL := (mem_tangentWedge_iff_infCone hX.1).2 hX
  have hYL := (mem_tangentWedge_iff_infCone hY.1).2 hY
  have hs : (a • X + b • Y).IsSymm := (hX.1.smul a).add (hY.1.smul b)
  exact (mem_tangentWedge_iff_infCone hs).1 (hL.2.1 hXL hYL ha hb hab)

/-- **`lem:cone-orders-closed`** (`thm:cone-orders`(2)): for a closed step set `𝒦` whose `≤_𝒦` is a
partial order, `{B : e^{tB} ∈ 𝒮_𝒦 for every t ≥ 0} = {B : ½(B + Bᵀ) ∈ C(𝒦)}`, a closed convex cone
containing every skew-symmetric matrix; `C(𝒦)` is an `O(d)`-invariant closed convex cone with
`C(𝒦) ∩ (-C(𝒦)) = {0}`; and `≼_{C(𝒦)}` is contained in `≤_𝒦`. -/
theorem closed_order_tangent_wedge (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    let L : Set (Mat d) := {B | ∀ t : ℝ, 0 ≤ t → mexp (t • B) ∈ stepSemigroup K}
    L = {B | symPart B ∈ infCone K} ∧ IsClosedConvexCone L ∧ (∀ B : Mat d, Bᵀ = -B → B ∈ L) ∧
      infCone K ⊆ symSet d ∧ IsOrthInvariant (infCone K) ∧ IsClosedConvexCone (infCone K) ∧
      (∀ X ∈ infCone K, -X ∈ infCone K → X = 0) ∧
      ∀ S S' : Mat d, causalLE (infCone K) S S' → stepLE K S S' := by
  intro L
  obtain ⟨hO, -, -, hpt⟩ := infCone_props hd hK
  have hCc := infCone_isClosedConvexCone hd hK hKc hpo
  have hCsym : infCone K ⊆ symSet d := fun X hX => hX.1
  refine ⟨tangentWedge_eq hd hK hKc hpo, tangentWedge_isClosedConvexCone hd hK hKc hpo,
    fun B hB => skew_mem_tangentWedge hd hK hpo hB, hCsym, hO, hCc,
    hpt fun S S' hS hS' h h' => hpo.antisymm S hS S' hS' h h', ?_⟩
  rintro S S' ⟨γ, hγ, rfl, rfl⟩
  have h0 : (γ 0).PosDef := hγ.mem_pd 0 ⟨le_rfl, zero_le_one⟩
  have h1 : (γ 1).PosDef := hγ.mem_pd 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨X, hX, hMX⟩ := hγ.relStep_mem_expSet hd hCsym hCc hO
  refine ⟨h0, h1, ?_⟩
  rw [hMX]
  have := hX.2 1 zero_le_one
  rwa [one_smul] at this

/-- `M^{1/2}M^sM^{1/2} = M^{s+1}` for `M ∈ PD(d)`. -/
theorem msqrt_mul_mrpow_mul_msqrt {M : Mat d} (hM : M.PosDef) (s : ℝ) :
    msqrt M * mrpow M s * msqrt M = mrpow M (s + 1) := by
  rw [msqrt_eq_mexp hM, mrpow_eq_mexp hM, mrpow_eq_mexp hM, ← mexp_add_smul, ← mexp_add_smul]
  congr 2
  ring

/-- If `≤_𝒦` is `≼_{C'}` on `PD(d)`, then `𝒦 = exp C'` (read at `Σ = I`, through
`thm:cone-orders`(1)). -/
theorem stepSet_eq_expSet_of_iff (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    {C' : Set (Mat d)} (hC'sym : C' ⊆ symSet d) (hC' : IsClosedConvexCone C')
    (hO' : IsOrthInvariant C')
    (hiff : ∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ causalLE C' S S')) :
    K = expSet C' := by
  have hrel : ∀ M : Mat d, M.PosDef → (M ∈ K ↔ M ∈ expSet C') := by
    intro M hM
    have h := hiff 1 M Matrix.PosDef.one hM
    rw [(causalLE_iff_expSet hd hC'sym hC' hO' Matrix.PosDef.one hM).1, relStep_one_left] at h
    rw [← h]
    exact ⟨fun h' => ⟨Matrix.PosDef.one, hM, by rwa [relStep_one_left]⟩, fun h' => by
      have := h'.2.2; rwa [relStep_one_left] at this⟩
  ext M
  constructor
  · intro hM
    exact (hrel M (hK.1 hM)).1 hM
  · rintro ⟨X, hX, rfl⟩
    exact (hrel _ (posDef_mexp (hC'sym hX))).2 ⟨X, hX, rfl⟩

/-- **`lem:cone-orders-closed`** (`thm:cone-orders`(2)), the equivalence: (a) `≤_𝒦` is `≼_{C'}` for
some `O(d)`-invariant closed convex cone `C' ⊆ Sym(d)`; (b) `𝒦 = exp C(𝒦)`; (c) `M^τ ∈ 𝒦` whenever
`M ∈ 𝒦` and `0 ≤ τ ≤ 1`. When they hold, `C' = C(𝒦)`. -/
theorem closed_order_cone_tfae (hd : 1 ≤ d) {K : Set (Mat d)} (hK : IsStepSet K)
    (hKc : closure K ∩ pdSet d ⊆ K) (hpo : IsPartialOrderOn (pdSet d) (stepLE K)) :
    List.TFAE
        [∃ C' : Set (Mat d), C' ⊆ symSet d ∧ IsClosedConvexCone C' ∧ IsOrthInvariant C' ∧
            ∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ causalLE C' S S'),
          K = expSet (infCone K),
          ∀ M ∈ K, ∀ τ ∈ Icc (0 : ℝ) 1, mrpow M τ ∈ K] ∧
      ∀ C' : Set (Mat d), C' ⊆ symSet d → IsClosedConvexCone C' → IsOrthInvariant C' →
        (∀ S S' : Mat d, S.PosDef → S'.PosDef → (stepLE K S S' ↔ causalLE C' S S')) →
        C' = infCone K := by
  obtain ⟨-, -, -, hCsym, hO, hCc, -, -⟩ := closed_order_tangent_wedge hd hK hKc hpo
  obtain ⟨-, hprodK, -, -, -⟩ := stepSemigroup_props hd hK hpo
  refine ⟨?_, fun C' hC'sym hC' hO' hiff => ?_⟩
  · tfae_have 1 → 3 := by
      rintro ⟨C', hC'sym, hC', hO', hiff⟩ M hM τ hτ
      rw [stepSet_eq_expSet_of_iff hd hK hC'sym hC' hO' hiff] at hM ⊢
      obtain ⟨X, hX, rfl⟩ := hM
      have hXh := isHermitian_of_isSymm (hC'sym hX)
      refine ⟨τ • X, hC'.2.2.2 τ hτ.1 X hX, ?_⟩
      rw [mrpow_eq_mexp (posDef_mexp (hC'sym hX)), mlog_mexp hXh]
    tfae_have 3 → 2 := by
      intro hc
      ext M
      constructor
      · intro hM
        have hMpd : M.PosDef := hK.1 hM
        have hall : ∀ n : ℕ, ∀ τ ∈ Icc (0 : ℝ) 1, mrpow M (n + τ) ∈ K := by
          intro n
          induction n with
          | zero => intro τ hτ; simpa using hc M hM τ hτ
          | succ n ih =>
            intro τ hτ
            have := hprodK M hM _ (ih τ hτ)
            rw [msqrt_mul_mrpow_mul_msqrt hMpd] at this
            convert this using 2
            push_cast
            ring
        refine ⟨mlog M, ⟨mlog_isSymm M, fun t ht => ?_⟩, (mexp_mlog hMpd).symm⟩
        rw [← mrpow_eq_mexp hMpd]
        have h := hall ⌊t⌋₊ (t - ⌊t⌋₊)
          ⟨by linarith [Nat.floor_le ht], by linarith [Nat.lt_floor_add_one t]⟩
        simpa using h
      · rintro ⟨X, hX, rfl⟩
        have := hX.2 1 zero_le_one
        rwa [one_smul] at this
    tfae_have 2 → 1 := by
      intro hb
      refine ⟨infCone K, hCsym, hCc, hO, fun S S' hS hS' => ?_⟩
      rw [(causalLE_iff_expSet hd hCsym hCc hO hS hS').1, ← hb]
      exact ⟨fun h => h.2.2, fun h => ⟨hS, hS', h⟩⟩
    tfae_finish
  · have hKe := stepSet_eq_expSet_of_iff hd hK hC'sym hC' hO' hiff
    rw [hKe]
    exact ((causalLE_order hd hC'sym hC' hO').2.2.2.2.2.2).symm

end AffineHemigroup
