/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.IsotropicFamily

/-!
# `def:isotropic-origin-datum` and `def:filtration-thresholds`: origin data, delay data, the
witness family and its thresholds

Blueprint: `blueprint/src/parts/03-isotropic.tex`; PRICING.md items D15–D17; SECOND-DEMAND.md § 4.

## Laws by specification (PRICING finding 1)

The law of an origin datum exists by ledger A3(iii). It is **not** defined here: `IsLawOf D μ` says
that `μ` is a probability measure with `μ̂ = e^{-F_d}`, and a node that only claims properties of
the law quantifies over every such `μ` (the transform determines the law, so nothing is lost).
A3 is spent only where a node concludes that such a `μ` exists.

## The delay datum is this module's, mirroring Paper V's cone stub

`DelayDatum` has the fields of Paper V's `Skeleton.DelayDatum` at `cone-v0.1` (the trunk's
`ScaleSpace.CausalAdmissible` with `k_antitone` replaced by measurability), so that the two types
can be merged when a second module proves something about them (SECOND-DEMAND.md, SSL-7). The
witness profile `u^{-1/2} + w 1_{[1,2]}(u)` is not nonincreasing, which is why the trunk's type
does not serve. The polar profile `eq:polar-profile-d` and the delay exponent (`delayExponentL`) are
defined on a profile **function**, so that the witness's polar profile and exponent need no proof
obligations; that the witness is a delay datum, its closed form `eq:witness-polar` and the criterion
`eq:threshold-criterion` are skeleton statements (`AffineSkeleton.Ch03Isotropic`). Since Q-0286 the
blueprint writes the witness parameter `w` and the thresholds `w_d` (the `c` of [B]); the Lean names
`witnessProfile`, `threshold` are unchanged.
-/

namespace AffineHemigroup

open MeasureTheory Set Real
open scoped ENNReal

variable {d : ℕ}

/-- **`|S^{d-1}|`**, the surface measure of the unit sphere in `ℝ^d`, `2π^{d/2}/Γ(d/2)`. -/
noncomputable def sphereArea (d : ℕ) : ℝ := 2 * π ^ ((d : ℝ) / 2) / Gamma ((d : ℝ) / 2)

/-- **An isotropic origin datum in dimension `d`** (D15; `def:isotropic-origin-datum`): `a ≥ 0`
and a nonincreasing `k_d : (0,∞) → [0,∞)` with `∫₀¹ k_d(r) r dr < ∞` and
`∫₁^∞ k_d(r) dr/r < ∞`. The profile is a function on `ℝ` read on `(0,∞)` (Paper V's
`SDProfile` pattern, without the normalisation `k 0 = 0`, which no node reads). -/
structure OriginDatum (d : ℕ) where
  /-- The Gaussian coefficient `a`. -/
  a : ℝ
  /-- The polar profile `k_d`. -/
  k : ℝ → ℝ
  a_nonneg : 0 ≤ a
  k_nonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  /-- `∫₀¹ k_d(r) r dr < ∞`. -/
  integrable_near_zero : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (k r * r) ≠ ⊤
  /-- `∫₁^∞ k_d(r) dr/r < ∞`. -/
  integrable_at_top : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (k r / r) ≠ ⊤

namespace OriginDatum

/-- **The Lévy measure `ν_d`** (`def:isotropic-origin-datum`): the rotation-invariant measure on
`ℝ^d ∖ {0}` with radial density `f_d(r) = k_d(r) (|S^{d-1}| r^d)⁻¹`. -/
noncomputable def levyMeasure (D : OriginDatum d) : Measure (Rd d) :=
  volume.withDensity fun x =>
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (D.k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x

/-- **The exponent `F_d`** (`eq:isotropic-exponent`):
`F_d(ξ) = ½ a|ξ|² + ∫ (1 - cos⟨ξ, x⟩) ν_d(dx)`, `ℝ≥0∞`-valued as Paper V's `exponentL` is. -/
noncomputable def exponentL (D : OriginDatum d) (ξ : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (D.a * ‖ξ‖ ^ 2 / 2)
    + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (inner ℝ ξ x)) ∂D.levyMeasure

/-- The real-valued exponent `F_d`. -/
noncomputable def exponent (D : OriginDatum d) (ξ : Rd d) : ℝ := (D.exponentL ξ).toReal

/-- **The profile at the origin**, `c := k_d(0+) ∈ [0,∞]`: for a nonincreasing profile the right
limit at `0` is the supremum over `r > 0`. -/
noncomputable def profileAtOrigin (D : OriginDatum d) : ℝ≥0∞ :=
  ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (D.k r)

/-- **`C_k := ∫₁^∞ k_d(r) dr/r`** (`lem:isotropic-exponent-log`), finite by the datum's second
integrability condition. -/
noncomputable def tailConst (D : OriginDatum d) : ℝ :=
  (∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (D.k r / r)).toReal

end OriginDatum

/-- **`μ` is the law of the datum `D`** (PRICING finding 1): a probability measure with
`μ̂ = e^{-F_d}`. -/
def IsLawOf (D : OriginDatum d) (μ : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-D.exponent ξ) : ℝ) : ℂ)

/-- **A delay datum** (D16; `[B, Def. 4.11]`): Paper V's cone stub `Skeleton.DelayDatum`, field
for field — the trunk's `CausalAdmissible` with the monotonicity of the profile dropped and the
measurability it supplied assumed instead. -/
structure DelayDatum where
  /-- The drift coefficient. -/
  b₀ : ℝ
  /-- The delay profile, a density against `du/u` on `(0,∞)`; not assumed nonincreasing. -/
  k : ℝ → ℝ
  b₀_nonneg : 0 ≤ b₀
  k_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u
  k_aemeasurable : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))
  /-- A normalisation, not a constraint, as in `CausalAdmissible`; not in [B, Def. 4.11], and not
  read by any statement (every integral over the profile is over `(0,∞)`; blind review N3-3). -/
  k_zero : k 0 = 0
  /-- `∫₀¹ k(u) du < ∞`. -/
  integrable_near_zero : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u) ≠ ⊤
  /-- `∫₁^∞ k(u) u⁻¹ du < ∞`. -/
  integrable_at_top : ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u) ≠ ⊤

namespace DelayDatum

/-- **The delay exponent** `F_I(σ) = b₀σ + ∫₀^∞ (1 - e^{-σu}) k(u) du/u`, `ℝ≥0∞`-valued. -/
noncomputable def exponentL (D : DelayDatum) (σ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (D.b₀ * σ)
    + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * D.k u / u)

/-- The real-valued delay exponent. -/
noncomputable def exponent (D : DelayDatum) (σ : ℝ) : ℝ := (D.exponentL σ).toReal

end DelayDatum

/-- **The delay exponent of a drift and a profile function**,
`b₀σ + ∫₀^∞ (1 - e^{-σu}) k(u) du/u`, `ℝ≥0∞`-valued, with no conditions on `k` (dispatch 3): the
form in which the witness family's exponent `F^{(w)}_I` is written without first building its
delay datum. `DelayDatum.exponentL` is this at the datum's fields (`DelayDatum.exponentL_eq`). -/
noncomputable def delayExponentL (b₀ : ℝ) (k : ℝ → ℝ) (σ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (b₀ * σ)
    + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u)

theorem DelayDatum.exponentL_eq (D : DelayDatum) (σ : ℝ) :
    D.exponentL σ = delayExponentL D.b₀ D.k σ := rfl

/-- **The polar profile in dimension `d` of a delay profile** (D16; `eq:polar-profile-d`,
`[B, (4.6)]`): `k_d(r) = (2/Γ(d/2)) ∫₀^∞ v^{d/2-1} e^{-v} k_I(r²/(2v)) dv`. -/
noncomputable def polarProfileOf (kI : ℝ → ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  2 / Gamma ((d : ℝ) / 2) *
    ∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * kI (r ^ 2 / (2 * v))

namespace OriginDatum

/-- **The origin datum is subordinated** (`def:isotropic-origin-datum`): it comes from a delay
datum `(a, k_I)` with `k_I` nonincreasing — a causally admissible datum (`[B, Def. 4.1]`) with
drift `a` — and `k_d` is that datum's polar profile on `(0,∞)`. -/
def IsSubordinated (D : OriginDatum d) : Prop :=
  ∃ FI : ScaleSpace.CausalAdmissible, FI.b₀ = D.a ∧
    ∀ r ∈ Ioi (0 : ℝ), D.k r = polarProfileOf FI.k d r

end OriginDatum

/-- **The witness profile** `k^{(w)}_I(u) = u^{-1/2} + w 1_{[1,2]}(u)` (D17;
`def:filtration-thresholds`, `[B, Lem. 4.12]`, where the parameter is written `c`), guarded at the
origin as the trunk's profiles are; it is Paper V's cone stub `Skeleton.filtrationProfile`. -/
noncomputable def witnessProfile (w : ℝ) : ℝ → ℝ := fun u =>
  if 0 < u then u ^ (-(1 : ℝ) / 2) + (if u ∈ Icc (1 : ℝ) 2 then w else 0) else 0

/-- **The witness's delay exponent** `F^{(w)}_I(σ)` (`def:filtration-thresholds`): drift `0`,
profile `witnessProfile w`; real-valued. -/
noncomputable def witnessExponent (w σ : ℝ) : ℝ := (delayExponentL 0 (witnessProfile w) σ).toReal

/-- **The witness exponent on the line** `F^{(w)}(ω) := F^{(w)}_I(ω²/2)`
(`def:filtration-thresholds`). -/
noncomputable def witnessF (w ω : ℝ) : ℝ := witnessExponent w (ω ^ 2 / 2)

/-! ## The heat kernel, the Gaussian of variance `u`, and the mixture density (dispatch 3) -/

/-- **The heat kernel** `g_t(x) = (2πt)^{-d/2} e^{-|x|²/2t}` on `ℝ^d`
(`lem:positive-transform-origin`; also the integrand `(2πu)^{-d/2} e^{-|x|²/2u}` of
`eq:mixture-density`). Read at `t > 0` only. -/
noncomputable def heatKernel (d : ℕ) (t : ℝ) (x : Rd d) : ℝ :=
  (2 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * t))

/-- **`g^{(d)}_u`, the centred Gaussian law on `ℝ^d` with covariance `uI`**
(`prop:isotropic-bridge`; the law of `√u Z` in `thm:origin-boundedness-d`(3)). Mathlib's
`multivariateGaussian`, which at `u = 0` (and, as junk, at `u < 0`, where `uI` is not positive
semidefinite) is `δ₀`: the blueprint's `g^{(d)}_0 := δ₀`. -/
noncomputable def gaussVar (d : ℕ) (u : ℝ) : Measure (Rd d) :=
  ProbabilityTheory.multivariateGaussian 0 (u • (1 : Mat d))

/-- **The mixture density** `p(x) = ∫_{(0,∞)} (2πu)^{-d/2} e^{-|x|²/2u} ρ(du)`
(`eq:mixture-density`), `ℝ≥0∞`-valued (it may be `∞` at the origin). -/
noncomputable def mixtureDensity (d : ℕ) (ρ : Measure ℝ) (x : Rd d) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (heatKernel d u x) ∂ρ

/-- **The regularized lower incomplete gamma function** `P(s, x) = Γ(s)⁻¹ ∫₀^x v^{s-1} e^{-v} dv`
(`eq:witness-polar`), defined by its integral (Mathlib has none). -/
noncomputable def regIncGamma (s x : ℝ) : ℝ :=
  (Gamma s)⁻¹ * ∫ v in Ioc (0 : ℝ) x, v ^ (s - 1) * Real.exp (-v)

/-- **`h_d(z) = z^m (e^{-z} - 2^{-d/2} e^{-z/2})`**, `m = (d+1)/2` (`eq:threshold-constant`,
`lem:threshold-monotone`), for a real parameter `d`. -/
noncomputable def thresholdFun (d z : ℝ) : ℝ :=
  z ^ ((d + 1) / 2) * (Real.exp (-z) - (2 : ℝ) ^ (-d / 2) * Real.exp (-z / 2))

/-- **`M_d := sup_{z>0} h_d(z)`** (`eq:threshold-constant`). That the supremum is finite and
positive is `lem:threshold-monotone`, not assumed. -/
noncomputable def thresholdSup (d : ℝ) : ℝ := ⨆ z : Ioi (0 : ℝ), thresholdFun d z

/-- **`w_d := Γ(m)/(2 M_d)`**, `m = (d+1)/2` (`eq:threshold-constant`; [B, Rem. 4.10] writes
`c_d`). -/
noncomputable def threshold (d : ℝ) : ℝ := Gamma ((d + 1) / 2) / (2 * thresholdSup d)

/-- **`ε_d := 2^{-d/2} e^{m/2}`**, `m = (d+1)/2` (`lem:threshold-limit`). -/
noncomputable def thresholdEps (d : ℝ) : ℝ := (2 : ℝ) ^ (-d / 2) * Real.exp ((d + 1) / 2 / 2)

/-- **`K := √(π/2) + √π + 4`** (`lem:threshold-limit`'s Stirling constant). -/
noncomputable def stirlingK : ℝ := Real.sqrt (π / 2) + Real.sqrt π + 4

/-! ## The constants of `prop:origin-lower-bound-d` (wave 2, group A) -/

/-- **`τ := min{1/2, (3/(4d²c))^{1/2}}`** (`prop:origin-lower-bound-d`), the ratio below which the
small jumps are split off. -/
noncomputable def lowerBoundTau (d : ℕ) (c : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt (3 / (4 * (d : ℝ) ^ 2 * c)))

/-- **`κ₀ := (c/(2|S^{d-1}|))² V_d / 8^d`** (`prop:origin-lower-bound-d`), `V_d` the volume of the
unit ball. -/
noncomputable def lowerBoundKappa (d : ℕ) (c : ℝ) : ℝ :=
  (c / (2 * sphereArea d)) ^ 2 * (volume (Metric.ball (0 : Rd d) 1)).toReal / 8 ^ d

/-- **`c₁ := (κ₀/4) τ^c e^{-C_k} min{2^{c-d}, 4^{c-d}}`** (`prop:origin-lower-bound-d`), for the
profile at the origin `c` and the tail constant `C_k`. -/
noncomputable def lowerBoundConst (d : ℕ) (c Ck : ℝ) : ℝ :=
  lowerBoundKappa d c / 4 * lowerBoundTau d c ^ c * Real.exp (-Ck) *
    min ((2 : ℝ) ^ (c - d)) ((4 : ℝ) ^ (c - d))

/-! ## The causal kernels and the bridge family (dispatch 3; `prop:isotropic-bridge`) -/

/-- **The kernels of a time-causal family in its canonical gauge** (`prop:isotropic-bridge`, as
[B, Prop. 4.5] takes them): probability measures `μ^I_{x,y}`, `0 ≤ x ≤ y`, on `[0,∞)` with Laplace
transform `exp[-(F_I(yσ) - F_I(xσ))]`, `σ ≥ 0`. A hypothesis of the node, not a construction: their
existence is [B, Rem. 4.3], which no node of this module reads. -/
structure IsCausalKernels (FI : ScaleSpace.CausalAdmissible) (μI : ℝ → ℝ → Measure ℝ) : Prop where
  isProbability : ∀ x y : ℝ, 0 ≤ x → x ≤ y → IsProbabilityMeasure (μI x y)
  /-- Carried by `[0,∞)`. -/
  support : ∀ x y : ℝ, 0 ≤ x → x ≤ y → μI x y (Iio 0) = 0
  laplace : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ∀ σ : ℝ, 0 ≤ σ →
    ∫ u, Real.exp (-(σ * u)) ∂(μI x y) = Real.exp (-(FI.exponent (y * σ) - FI.exponent (x * σ)))

/-- **The bridge family** `μ_{s,t} := ∫ g^{(d)}_u μ^I_{s²,t²}(du)` (`eq:isotropic-bridge`), a
`Measure.bind`. -/
noncomputable def bridgeFamily (d : ℕ) (μI : ℝ → ℝ → Measure ℝ) (s t : ℝ) : Measure (Rd d) :=
  (μI (s ^ 2) (t ^ 2)).bind (gaussVar d)

end AffineHemigroup
