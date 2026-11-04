/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.SimilarityStable
import AffineHemigroup.TripletSum
import AffineHemigroup.DilationRatio
import AffineHemigroup.LogOrbitRays

/-!
# `prop:similarity-orbit-family`: similarity-covariant families with an elliptical part

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`, `prop:similarity-orbit-family`.

For a right-continuous profile `k`, the orbit `ν_H = (H^{1/2})_*ν_I` of its law, and
`μ_Σ := N(0, C(Σ)) * ν_{h(Σ)}`: (1) an infinitely divisible increment orders the Gaussian parts in
the Loewner order and the Lévy densities everywhere, so the step `h(Σ) → h(Σ')` is in the cone of
`prop:orbit-step-cone`(2); (2) under similarity equivariance and the extension of `h` to
`PSD(d) ∖ {0}`, `ecc(h(Σ)) ≤ R((h₀/c₁)^{1/2})²`; (3) at index `0` the part is shape-blind; (4) so
is it for a logarithmic exponent without a Gaussian part, under positive increments.

## Routes

* **(1)**: the triplets of a convolution add (`AffineHemigroup.TripletSum`), A3(i) gives `ρ` a
  triplet and A3(ii) makes the Lévy measures add, so `n_{h(Σ)} ≤ n_{h(Σ')}` almost everywhere. To
  make it everywhere the blueprint's open set is used in the coordinates `x = h(Σ)^{1/2}y`, and it
  gives `D m(r) ≤ m(r/λ)` for every `r > 0` (`m` right-continuous); **then the ordering holds
  at every `y ≠ 0` directly**, because `⟨y, M⁻¹y⟩^{1/2} ≤ |y|/λ` and `m` is nonincreasing, so the
  cone is read from `prop:orbit-step-cone`(2) as stated, not re-derived.
* **(2)** is `prop:similarity-stable-family`(2)'s sandwich (`gauge_sandwich`) with the cone in place
  of `≼_α`; **(3)** reads `prop:orbit-step-cone`(3), **(4)** `prop:log-orbit-rays`, on the step
  `Σ ≤ λ_max(Σ) I`.
-/

namespace AffineHemigroup

open MeasureTheory Set Filter Matrix ProbabilityTheory
open scoped Topology MatrixOrder RealInnerProductSpace ENNReal

variable {d : ℕ}

/-! ## The radial density -/

/-- `m(r) = k(r) r^{-d}` is nonincreasing on `(0,∞)`. -/
theorem RadialProfile.m_antitone (K : RadialProfile d) : AntitoneOn K.m (Ioi 0) := by
  intro r hr s hs hrs
  have hr' : (0 : ℝ) < r := hr
  have hs' : (0 : ℝ) < s := hs
  unfold RadialProfile.m
  calc K.k s / s ^ d ≤ K.k r / s ^ d :=
        div_le_div_of_nonneg_right (K.k_antitone hr hs hrs) (by positivity)
    _ ≤ K.k r / r ^ d :=
        div_le_div_of_nonneg_left (K.k_nonneg r hr) (by positivity) (pow_le_pow_left₀ hr'.le hrs d)

/-- `m` is right-continuous where `k` is. -/
theorem RadialProfile.m_rightCont (K : RadialProfile d) {r : ℝ} (hr : 0 < r)
    (hk : ContinuousWithinAt K.k (Ici r) r) : ContinuousWithinAt K.m (Ici r) r := by
  unfold RadialProfile.m
  exact hk.div (continuousWithinAt_id.pow d) (pow_ne_zero _ hr.ne')

/-! ## From almost everywhere to everywhere -/

/-- **The ordering of two orbit densities, almost everywhere to everywhere** (the proof of
`prop:similarity-orbit-family`(1)): for a right-continuous profile, `n_H ≤ n_{H'}` almost
everywhere implies `n_H ≤ n_{H'}` off the origin. -/
theorem orbit_order_of_ae (hd : 1 ≤ d) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) {H H' : Mat d} (hH : H.PosDef)
    (hH' : H'.PosDef)
    (hae : ∀ᵐ x ∂(volume : Measure (Rd d)), K.orbitDensity H x ≤ K.orbitDensity H' x) :
    ∀ x : Rd d, x ≠ 0 → K.orbitDensity H x ≤ K.orbitDensity H' x := by
  haveI : NeZero d := ⟨by omega⟩
  set M := relStep H H' with hMdef
  have hM : M.PosDef := (posDef_relStep_iff hH H').2 hH'
  set ℓ := lamMin M with hℓ
  have hl : 0 < ℓ := lamMin_pos hM
  set lam := Real.sqrt ℓ with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hl
  set c := M.det ^ (-(1 : ℝ) / 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hM.det_pos _
  have hU : IsUnit (msqrt H).det := msqrt_mem_glSet hH
  have hdH := hH.det_pos
  -- the ordering in the coordinates `x = H^{1/2}y`
  have hcoord : ∀ y : Rd d, K.orbitDensity H (lin (msqrt H) y) ≤
      K.orbitDensity H' (lin (msqrt H) y) ↔ K.m ‖y‖ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) := by
    intro y
    have h1 : K.orbitDensity H (lin (msqrt H) y) = H.det ^ (-(1 : ℝ) / 2) * K.m ‖y‖ := by
      rw [RadialProfile.orbitDensity, lin_inv_mul_apply hU]
    have h2 : K.orbitDensity H' (lin (msqrt H) y) =
        H'.det ^ (-(1 : ℝ) / 2) * K.m (Real.sqrt (quad M⁻¹ y)) := by
      rw [RadialProfile.orbitDensity, hMdef, quad_relStep_inv hH, ← norm_sq_lin_msqrt_inv hH',
        Real.sqrt_sq (norm_nonneg _)]
    have h3 : H'.det ^ (-(1 : ℝ) / 2) = H.det ^ (-(1 : ℝ) / 2) * c := by
      rw [hc, hMdef, det_relStep hH, Real.div_rpow hH'.det_pos.le hdH.le,
        mul_div_cancel₀ _ (Real.rpow_pos_of_pos hdH _).ne']
    rw [h1, h2, h3, mul_assoc]
    exact mul_le_mul_iff_right₀ (by positivity)
  -- transport of the almost-everywhere statement
  have hdet : (lin (msqrt H)).det ≠ 0 := by
    change LinearMap.det ((lin (msqrt H) : Rd d →L[ℝ] Rd d) : Rd d →ₗ[ℝ] Rd d) ≠ 0
    rw [det_lin]; exact hU.ne_zero
  have hqmp := Measure.ContinuousLinearMap.quasiMeasurePreserving (volume : Measure (Rd d))
    (lin (msqrt H)) hdet
  have hae' : ∀ᵐ y ∂(volume : Measure (Rd d)), K.m ‖y‖ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) := by
    filter_upwards [hqmp.ae hae] with y hy
    exact (hcoord y).1 hy
  -- a unit eigenvector of `M` for `ℓ`, and `M⁻¹ v = ℓ⁻¹ v`
  obtain ⟨v, hv1, hMv⟩ := exists_unit_eigvec_eigUp_zero hM.isHermitian
  rw [← lamMin_eq_eigUp_zero hM.isHermitian, ← hℓ] at hMv
  have hMinv : lin M⁻¹ v = ℓ⁻¹ • v := by
    have hUM : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hM.isUnit
    have h1 := congrArg (lin M⁻¹) hMv
    rw [lin_inv_mul_apply hUM, map_smul] at h1
    calc lin M⁻¹ v = ℓ⁻¹ • (ℓ • lin M⁻¹ v) := by
          rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
      _ = ℓ⁻¹ • v := by rw [← h1]
  have hqv : ∀ s : ℝ, 0 < s → Real.sqrt (quad M⁻¹ (s • v)) = s / lam := by
    intro s hs
    rw [quad_smul_vec, quad, hMinv, inner_smul_right, real_inner_self_eq_norm_sq, hv1, one_pow,
      mul_one, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, Real.sqrt_inv, ← hlam,
      div_eq_mul_inv]
  have hcont_q : Continuous fun y : Rd d => Real.sqrt (quad M⁻¹ y) := by
    unfold quad; fun_prop
  -- `D m(r) ≤ m(r/λ)` along every radius, by the open set of the blueprint
  have hray : ∀ r : ℝ, 0 < r → K.m r ≤ c * K.m (r / lam) := by
    intro r hr
    have hδb : ∀ δ : ℝ, 0 < δ → K.m (r + δ) ≤ c * K.m (r / lam) := by
      intro δ hδ
      set U : Set (Rd d) := {y | r < ‖y‖ ∧ ‖y‖ < r + δ ∧ r / lam < Real.sqrt (quad M⁻¹ y)}
        with hUdef
      have hUo : IsOpen U :=
        (isOpen_lt continuous_const continuous_norm).inter ((isOpen_lt continuous_norm
          continuous_const).inter (isOpen_lt continuous_const hcont_q))
      have hUne : U.Nonempty := by
        refine ⟨(r + δ / 2) • v, ?_, ?_, ?_⟩
        · rw [norm_smul, hv1, mul_one, Real.norm_of_nonneg (by positivity)]; linarith
        · rw [norm_smul, hv1, mul_one, Real.norm_of_nonneg (by positivity)]; linarith
        · rw [hqv _ (by positivity)]
          exact div_lt_div_of_pos_right (by linarith) hlam0
      have hpos : 0 < (volume : Measure (Rd d)) U := hUo.measure_pos volume hUne
      obtain ⟨y, hyU, hy⟩ : ∃ y ∈ U, K.m ‖y‖ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) := by
        by_contra hcon
        push Not at hcon
        have h0 : (volume : Measure (Rd d)) U = 0 :=
          measure_mono_null (fun y hyU => not_le.2 (hcon y hyU)) (ae_iff.1 hae')
        exact hpos.ne' h0
      obtain ⟨hy1, hy2, hy3⟩ := hyU
      have hr0 : 0 < r / lam := div_pos hr hlam0
      calc K.m (r + δ) ≤ K.m ‖y‖ :=
            K.m_antitone (lt_trans hr hy1) (by show (0 : ℝ) < r + δ; linarith) hy2.le
        _ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) := hy
        _ ≤ c * K.m (r / lam) :=
            mul_le_mul_of_nonneg_left (K.m_antitone hr0 (lt_trans hr0 hy3) hy3.le) hc0.le
    have htend : Tendsto (fun δ : ℝ => K.m (r + δ)) (𝓝[>] 0) (𝓝 (K.m r)) := by
      have h1 := (K.m_rightCont hr (hrc r hr)).tendsto
      have h2 : Tendsto (fun δ : ℝ => r + δ) (𝓝[>] 0) (𝓝[Ici r] r) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := (continuous_const_add r).tendsto 0
          simp only [add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with δ hδ
          exact show r ≤ r + δ by linarith [show (0 : ℝ) < δ from hδ]
      exact h1.comp h2
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδb δ hδ
  -- the ordering at every point
  have hall : ∀ y : Rd d, y ≠ 0 → K.m ‖y‖ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) := by
    intro y hy
    have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hq : 0 < quad M⁻¹ y := quad_pos hM.inv hy
    have hu0 : 0 < Real.sqrt (quad M⁻¹ y) := Real.sqrt_pos.2 hq
    have hule : Real.sqrt (quad M⁻¹ y) ≤ ‖y‖ / lam := by
      rw [le_div_iff₀ hlam0, hlam, ← Real.sqrt_mul hq.le, mul_comm]
      calc Real.sqrt (ℓ * quad M⁻¹ y) ≤ Real.sqrt (‖y‖ ^ 2) :=
            Real.sqrt_le_sqrt (lamMin_mul_quad_inv_le hM y)
        _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)
    calc K.m ‖y‖ ≤ c * K.m (‖y‖ / lam) := hray _ hr
      _ ≤ c * K.m (Real.sqrt (quad M⁻¹ y)) :=
          mul_le_mul_of_nonneg_left (K.m_antitone hu0 (div_pos hr hlam0) hule) hc0.le
  intro x hx
  have hy : lin (msqrt H)⁻¹ x ≠ 0 := by
    intro h0
    apply hx
    rw [← lin_mul_inv_apply hU x, h0, map_zero]
  have := (hcoord _).2 (hall _ hy)
  rwa [lin_mul_inv_apply hU] at this

/-! ## Clause (1) -/

/-- **`prop:similarity-orbit-family`(1)**: for the orbit `ν_H = (H^{1/2})_*ν_I` of a
right-continuous profile `k` and `μ_Σ := N(0, C(Σ)) * ν_{h(Σ)}`, an infinitely divisible increment
`μ_{Σ'} = μ_Σ * ρ` gives `C(Σ) ≤ C(Σ')` and `n_{h(Σ)} ≤ n_{h(Σ')}` everywhere: the step
`h(Σ) → h(Σ')` is in the cone of `prop:orbit-step-cone`(2). Spends A3(i)–(ii). -/
theorem sim_orbit_id_increment (hd : 2 ≤ d) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) (νI : Measure (Rd d))
    (hνI : IsProfileLaw K νI) (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef) :
    ∀ S S' : Mat d, S.PosDef → S'.PosDef → ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
      IsInfinitelyDivisible ρ →
      multivariateGaussian 0 (C S') ∗ affineOrbit νI (h S') =
        (multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S)) ∗ ρ →
      loewnerLE (C S) (C S') ∧
        (∀ x : Rd d, x ≠ 0 → K.orbitDensity (h S) x ≤ K.orbitDensity (h S') x) ∧
        1 ≤ lamMin (relStep (h S) (h S')) ∧
        (relStep (h S) (h S')).det ≤ lamMin (relStep (h S) (h S')) ^ d *
          dilRatio K.k (Real.sqrt (lamMin (relStep (h S) (h S')))) ^ 2 := by
  intro S S' hS hS' ρ hρ hρid heq
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  haveI := hνI.1
  have hH := hh S hS
  have hH' := hh S' hS'
  haveI hpS : IsProbabilityMeasure (affineOrbit νI (h S)) := by
    unfold affineOrbit; infer_instance
  haveI hpS' : IsProbabilityMeasure (affineOrbit νI (h S')) := by
    unfold affineOrbit; infer_instance
  have hT := (hasTriplet_gaussian (hC S hS)).conv (hasTriplet_affineOrbit_profile hd1 K hνI hH)
  have hT' := (hasTriplet_gaussian (hC S' hS')).conv
    (hasTriplet_affineOrbit_profile hd1 K hνI hH')
  have hid' : IsInfinitelyDivisible (multivariateGaussian 0 (C S') ∗ affineOrbit νI (h S')) :=
    (isInfinitelyDivisible_gaussian (hC S' hS')).conv
      ((profileLaw_props hd1 K νI hνI).2.1.push _)
  obtain ⟨Tρ, -, hA, hν, -⟩ := triplet_increment hρid hid' hT heq hT'
  -- the Gaussian parts
  have hA' : C S' = C S + Tρ.A := by
    have := hA
    simp only [LevyTriplet.add, gaussTriplet, densTriplet, add_zero] at this
    exact this
  -- the Lévy densities, almost everywhere
  have hν' : (volume : Measure (Rd d)).withDensity
      (fun x => ENNReal.ofReal (K.orbitDensity (h S') x)) =
      (volume : Measure (Rd d)).withDensity (fun x => ENNReal.ofReal (K.orbitDensity (h S) x)) +
        Tρ.ν := by
    have := hν
    simp only [LevyTriplet.add, gaussTriplet, densTriplet, zero_add] at this
    convert this using 3 <;> exact (restrict_compl_singleton _).symm
  have hae : ∀ᵐ x ∂(volume : Measure (Rd d)), K.orbitDensity (h S) x ≤ K.orbitDensity (h S') x := by
    have hle : ∀ s : Set (Rd d), MeasurableSet s → volume s < ∞ →
        ∫⁻ x in s, ENNReal.ofReal (K.orbitDensity (h S) x) ≤
          ∫⁻ x in s, ENNReal.ofReal (K.orbitDensity (h S') x) := by
      intro s hs _
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, hν', Measure.add_apply]
      exact le_self_add
    have := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (K.measurable_orbitDensity hd1 (h S)).ennreal_ofReal hle
    filter_upwards [this] with x hx
    exact (ENNReal.ofReal_le_ofReal_iff (K.orbitDensity_nonneg hd1 hH' x)).1 hx
  have hord := orbit_order_of_ae hd1 K hrc hH hH' hae
  have hcone := (orbit_density_order_iff hd1 K hH hH').1.1 hord
  refine ⟨?_, hord, hcone⟩
  unfold loewnerLE
  rw [hA', add_sub_cancel_left]
  exact Tρ.A_posSemidef

/-! ## Clauses (2)–(4) -/

/-- **`prop:similarity-orbit-family`(2)**, bounded shape: if `h` is similarity-equivariant, extends
continuously to `PSD(d) ∖ {0}` with values in `PD(d)` (the extension `hbar`), and every Loewner
step in `PD(d)` has an infinitely divisible increment, then `h(I) = h₀I` with `h₀ > 0` and
`ecc(h(Σ)) ≤ R((h₀/c₁)^{1/2})²`, `c₁ := λ_max(h(e₁e₁ᵀ))`. -/
theorem sim_orbit_bounded_shape (hd : 2 ≤ d) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) (νI : Measure (Rd d))
    (hνI : IsProfileLaw K νI) (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ))
    (hbar : Mat d → Mat d) (hbar_eq : ∀ S : Mat d, S.PosDef → hbar S = h S)
    (hbar_cont : ContinuousOn hbar {S | S.PosSemidef ∧ S ≠ 0})
    (hbar_pd : ∀ S : Mat d, S.PosSemidef → S ≠ 0 → (hbar S).PosDef)
    (hID : HasIDLoewnerIncrements fun S => multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S)) :
    ∃ h0 : ℝ, 0 < h0 ∧ h 1 = h0 • (1 : Mat d) ∧ ∀ S : Mat d, S.PosDef →
      ecc (h S) ≤ dilRatio K.k (Real.sqrt (h0 / lamMax (hbar (sigmaEps d 0)))) ^ 2 := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hstep : ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
      ∀ x : Rd d, x ≠ 0 → K.orbitDensity (h S) x ≤ K.orbitDensity (h S') x := by
    intro S S' hS hS' hle
    obtain ⟨ρ, hρ, hρid, heq⟩ := hID S S' hS hS' hle
    exact (sim_orbit_id_increment hd K hrc νI hνI h C hh hC S S' hS hS' ρ hρ hρid heq).2.1
  have hmono : ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
      loewnerLE (h S) (h S') := fun S S' hS hS' hle =>
    (orbit_density_order_iff hd1 K (hh S hS) (hh S' hS')).2 (hstep S S' hS hS' hle)
  obtain ⟨hh0, hH1⟩ := gauge_one h hh hequiv
  set h0 := h 1 0 0 with hh0def
  have hsig0 := sigmaEps_props (d := d) le_rfl
  set c1 := lamMax (hbar (sigmaEps d 0)) with hc1def
  have hc1 : 0 < c1 := lamMax_pos (hbar_pd _ hsig0.1 hsig0.2)
  refine ⟨h0, hh0, hH1, fun S hS => ?_⟩
  have hmain : ∀ S : Mat d, S.PosDef → lamMax S = 1 →
      ecc (h S) ≤ dilRatio K.k (Real.sqrt (h0 / c1)) ^ 2 := by
    intro S hS hSmax
    have hHpd := hh S hS
    have hc1le : c1 ≤ lamMax (h S) :=
      gauge_sandwich h hh hequiv hbar hbar_eq hbar_cont hbar_pd hmono hS hSmax
    have hord := hstep S 1 hS PosDef.one (loewnerLE_one_of_lamMax hS.isHermitian hSmax)
    rw [hH1] at hord
    obtain ⟨hl1, hdetM⟩ := (orbit_density_order_iff hd1 K hHpd (PosDef.one.smul hh0)).1.1 hord
    -- `M = h₀ h(Σ)⁻¹`
    have hη : 0 < lamMax (h S) := lamMax_pos hHpd
    have hη1 : 0 < lamMin (h S) := lamMin_pos hHpd
    have hD := hHpd.det_pos
    have hM : relStep (h S) (h0 • (1 : Mat d)) = h0 • (h S)⁻¹ := by
      rw [relStep_smul, relStep_one_right hHpd]
    have hℓ : lamMin (relStep (h S) (h0 • (1 : Mat d))) = h0 / lamMax (h S) := by
      rw [hM, lamMin_smul hh0.le, lamMin_inv_eq hHpd, div_eq_mul_inv]
    have hdM : (relStep (h S) (h0 • (1 : Mat d))).det = h0 ^ d / (h S).det := by
      rw [hM, det_smul, Fintype.card_fin, det_inv_of_posDef hHpd, div_eq_mul_inv]
    rw [hℓ, hdM] at hdetM
    rw [hℓ] at hl1
    set R := dilRatio K.k (Real.sqrt (h0 / lamMax (h S))) with hRdef
    -- `η^d ≤ R² det h(Σ)`, then `η/η₁ ≤ R²`
    have h1 : lamMax (h S) ^ d ≤ R ^ 2 * (h S).det := by
      rw [div_pow, div_le_iff₀ hD] at hdetM
      have hpos : 0 < h0 ^ d / lamMax (h S) ^ d := by positivity
      have : h0 ^ d * lamMax (h S) ^ d ≤ h0 ^ d * (R ^ 2 * (h S).det) := by
        have := mul_le_mul_of_nonneg_left hdetM (pow_pos hη d).le
        calc h0 ^ d * lamMax (h S) ^ d = lamMax (h S) ^ d * h0 ^ d := by ring
          _ ≤ lamMax (h S) ^ d * (h0 ^ d / lamMax (h S) ^ d * R ^ 2 * (h S).det) := this
          _ = h0 ^ d * (R ^ 2 * (h S).det) := by field_simp
      exact le_of_mul_le_mul_left this (pow_pos hh0 d)
    have hdet := det_le_lamMin_mul_lamMax_pow hHpd
    have hd' : lamMax (h S) ^ d = lamMax (h S) ^ (d - 1) * lamMax (h S) := by
      rw [← pow_succ, Nat.sub_add_cancel hd1]
    have h2 : lamMax (h S) ≤ R ^ 2 * lamMin (h S) := by
      have h3 : lamMax (h S) ^ (d - 1) * lamMax (h S) ≤
          lamMax (h S) ^ (d - 1) * (R ^ 2 * lamMin (h S)) := by
        calc _ = lamMax (h S) ^ d := hd'.symm
          _ ≤ R ^ 2 * (h S).det := h1
          _ ≤ R ^ 2 * (lamMin (h S) * lamMax (h S) ^ (d - 1)) :=
              mul_le_mul_of_nonneg_left hdet (sq_nonneg _)
          _ = _ := by ring
      exact le_of_mul_le_mul_left h3 (pow_pos hη _)
    -- `R` is nondecreasing on `[1,∞)`
    have hmonoR := (dilRatio_monotone hd1 K).2.1
    have hs1 : 1 ≤ Real.sqrt (h0 / lamMax (h S)) := Real.one_le_sqrt.2 hl1
    have hs2 : Real.sqrt (h0 / lamMax (h S)) ≤ Real.sqrt (h0 / c1) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hh0.le hc1 hc1le)
    have hR1 : 1 ≤ R := (dilRatio_mem hd1 K _ hs1).2
    have hRle : R ≤ dilRatio K.k (Real.sqrt (h0 / c1)) :=
      hmonoR hs1 (le_trans hs1 hs2) hs2
    unfold ecc
    rw [div_le_iff₀ hη1]
    calc lamMax (h S) ≤ R ^ 2 * lamMin (h S) := h2
      _ ≤ dilRatio K.k (Real.sqrt (h0 / c1)) ^ 2 * lamMin (h S) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hRle 2) hη1.le
  obtain ⟨ht, hS1, hS1max, hhS⟩ := gauge_rescale h hequiv hS
  rw [hhS, ecc_smul ht]
  exact hmain _ hS1 hS1max

/-- `Σ ≤ λ_max(Σ) I` for symmetric `Σ`. -/
theorem loewnerLE_lamMax_smul_one [NeZero d] {S : Mat d} (hSh : S.IsHermitian) :
    loewnerLE S (lamMax S • (1 : Mat d)) := by
  unfold loewnerLE
  refine posSemidef_of_quad_nonneg ((isHermitian_one.smul (IsSelfAdjoint.all _)).sub hSh)
    fun x => ?_
  rw [quad_sub, quad_smul, quad_one]
  linarith [quad_le_lamMax_mul hSh x]

/-- `h(tI) = t h(I)` for a similarity-equivariant `h`. -/
theorem gauge_smul_one (h : Mat d → Mat d)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ)) {t : ℝ} (ht : 0 < t) :
    h (t • (1 : Mat d)) = t • h 1 := by
  have h1o : (1 : Mat d) ∈ orthSet d := (Matrix.orthogonalGroup (Fin d) ℝ).one_mem
  have := hequiv 1 PosDef.one t ht 1 h1o
  simpa only [transpose_one, Matrix.mul_one, Matrix.one_mul] using this

/-- **`prop:similarity-orbit-family`(3)**, index `0`: if `k(0+)` is finite, `h` is equivariant and
every Loewner step has an infinitely divisible increment, then every `h(Σ)` is a multiple of `I`. -/
theorem sim_orbit_index_zero (hd : 2 ≤ d) (K : RadialProfile d)
    (hrc : ∀ r : ℝ, 0 < r → ContinuousWithinAt K.k (Ici r) r) (νI : Measure (Rd d))
    (hνI : IsProfileLaw K νI) (h C : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hC : ∀ S : Mat d, S.PosDef → (C S).PosSemidef) (L0 : ℝ) (hk0 : Tendsto K.k (𝓝[>] 0) (𝓝 L0))
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ))
    (hID : HasIDLoewnerIncrements fun S => multivariateGaussian 0 (C S) ∗ affineOrbit νI (h S)) :
    ∀ S : Mat d, S.PosDef → ∃ c : ℝ, h S = c • (1 : Mat d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, hrays⟩ := orbit_density_order_bounded hd1 K L0 hk0
  obtain ⟨hh0, hH1⟩ := gauge_one h hh hequiv
  intro S hS
  have ht := lamMax_pos hS
  have htI : (lamMax S • (1 : Mat d)).PosDef := PosDef.one.smul ht
  obtain ⟨ρ, hρ, hρid, heq⟩ := hID S _ hS htI (loewnerLE_lamMax_smul_one hS.isHermitian)
  have hord := (sim_orbit_id_increment hd K hrc νI hνI h C hh hC S _ hS htI ρ hρ hρid heq).2.1
  obtain ⟨lam, hlam, hEq⟩ := (hrays _ _ (hh S hS) (hh _ htI)).1 hord
  have hlam0 : lam ^ 2 ≠ 0 := pow_ne_zero _ (by linarith)
  refine ⟨(lam ^ 2)⁻¹ * (lamMax S * h 1 0 0), ?_⟩
  rw [gauge_smul_one h hequiv ht, hH1, smul_smul] at hEq
  rw [mul_smul, hEq, smul_smul, inv_mul_cancel₀ hlam0, one_smul]

/-- **`prop:similarity-orbit-family`(4)**, logarithmic exponent, no Gaussian part: for the orbit of
a law satisfying the hypothesis of `prop:log-orbit-rays`, `C ≡ 0`, `h` equivariant and positive
finite Loewner increments, every `h(Σ)` is a multiple of `I`. -/
theorem sim_orbit_log (hd : 2 ≤ d) (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Ici 0))
    (hg_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ g u) (hg0 : g 0 = 0) (νI : Measure (Rd d))
    [IsProbabilityMeasure νI] (hνI : ∀ ω : Rd d, charFun νI ω = ((Real.exp (-g (‖ω‖ ^ 2)) : ℝ) : ℂ))
    (κ : ℝ) (hκ : 0 < κ)
    (hlog : ∀ c : ℝ, 0 < c → Tendsto (fun u => g (c * u) - g u) atTop (𝓝 (κ * Real.log c)))
    (h : Mat d → Mat d) (hh : ∀ S : Mat d, S.PosDef → (h S).PosDef)
    (hequiv : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
      h (c • (Q * S * Qᵀ)) = c • (Q * h S * Qᵀ))
    (hfin : HasFiniteLoewnerIncrements fun S => affineOrbit νI (h S)) :
    ∀ S : Mat d, S.PosDef → ∃ c : ℝ, h S = c • (1 : Mat d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hh0, hH1⟩ := gauge_one h hh hequiv
  intro S hS
  have ht := lamMax_pos hS
  have htI : (lamMax S • (1 : Mat d)).PosDef := PosDef.one.smul ht
  obtain ⟨ρ, hρ, heq⟩ := hfin S _ hS htI (loewnerLE_lamMax_smul_one hS.isHermitian)
  obtain ⟨c, hc, hEq⟩ := log_orbit_rays hd1 g hg_cont hg_nonneg hg0 νI hνI κ hκ hlog
    (h S) (h _) (hh S hS) (hh _ htI) ρ hρ heq
  refine ⟨c⁻¹ * (lamMax S * h 1 0 0), ?_⟩
  rw [gauge_smul_one h hequiv ht, hH1, smul_smul] at hEq
  rw [mul_smul, hEq, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

end AffineHemigroup
