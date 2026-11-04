/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Orbits
import AffineHemigroup.Defs.Spectral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The node-local notation of § 5.6, smaller groups

Blueprint: `blueprint/src/parts/05-smaller-groups.tex`. These objects are introduced inside the
statements of § 5.6's nodes (Q-0281, dispatch 4); they are named here so that the nodes that read
them share one type. Every definition is vocabulary: nothing in this file claims anything, and every
claim a node displays beside a definition (that a set *is* a simplex, that `L_Σ` *is* a Lévy
measure, that a limit *exists*) is a skeleton statement of that node.

## Readings fixed here

* **The kernels from the origin** (`lem:gw-kernels-from-origin`(2)): properties (a)–(c) are the
  structure `IsOriginKernels`, with "a map from `PSD(d)` into the probability measures" its first
  field; (d) is `HasIncrements`; "is the family of kernels from the origin of a `(G, W)`-cascade
  family" is `IsKernelsFromOrigin`, an existential over the totalised family (dispatch 1's
  reading: a family is read on `P_W`).
* **Products on `ℝ^d`** (`prop:frame-families`, `prop:fixed-frame-families`): `ν₁ ⊗ ⋯ ⊗ ν_d` is
  `prodLaw ν`, Mathlib's `Measure.pi` carried to `EuclideanSpace` by `WithLp.toLp`, the form in
  which Mathlib's `charFun_pi` is stated; `(s)_*ν` on `ℝ` is `dilLine s ν`.
* **The general similarity setting** (`prop:similarity-general-sandwich`, standing hypotheses):
  the structure `IsSimGeneralFamily μ C L`, the kernel `μ_Σ`, its Gaussian covariance `C(Σ)` and its
  Lévy measure `L_Σ` given as functions on matrices and read on `PD(d)`; "a symmetric infinitely
  divisible probability measure with generating triplet `(C(Σ), L_Σ, 0)`" is: a probability
  measure, `(-I)_*μ_Σ = μ_Σ`, infinitely divisible, and some `LevyTriplet` with those three
  entries is its triplet. The exponent `ψ_Σ` is `levyExp (L Σ)`, real-valued (it is finite for a
  Lévy measure).
* **The rank-one limits** (`prop:similarity-general-sandwich`(4)): `L_*` is any measure with
  `L_*{0} = 0` that is the limit of `L_{Σ_ε}(B)` on every Borel `B` bounded away from the origin
  (`IsRankOneLimit`; such a measure is unique, so nothing is chosen), and `ψ_*` any pointwise limit
  of `ψ_{Σ_ε}` (`IsRankOneExpLimit`). The moment limit `𝓜*_s` is `rankOneMoment` (a `limUnder`,
  read only where the node proves the limit exists), and `θ_s := d min(a_s, b_s)/T_s(L_I)` is
  `momentTheta`, written with `λ_min(𝓜*_s)`, which is `min(a_s, b_s)` for the matrix
  `diag(a_s, b_s, …, b_s)` that the node proves the limit to be.
* **`Σ_ε := diag(1, ε, …, ε)`** is `sigmaEps d ε`; `e₁e₁ᵀ` is `sigmaEps d 0`.
* **The normalised surface measure `σ̄`** on `S^{d-1}` is `normSphere d`, Mathlib's
  `volume.toSphere` carried to `ℝ^d` and divided by its mass; sets of directions are subsets of
  `ℝ^d` contained in the unit sphere.
-/

namespace AffineHemigroup

open MeasureTheory Set Matrix Filter
open scoped ENNReal Topology RealInnerProductSpace

variable {d : ℕ}

/-! ## The kernels from the origin (`lem:gw-kernels-from-origin`) -/

/-- **Properties (a)–(c) of the kernels from the origin** (`lem:gw-kernels-from-origin`(2)) of a
map `Σ ↦ μ_Σ` from `PSD(d)` into the probability measures on `ℝ^d`: (a) `μ_0 = δ₀` and
`μ_I ≠ δ₀`; (b) `A_*μ_Σ = μ_{A·Σ}` for `A ∈ G`; (c) `Σ ↦ μ̂_Σ(ω)` is continuous on `PSD(d)`. -/
structure IsOriginKernels (G : Set (Mat d)) (m : Mat d → Measure (Rd d)) : Prop where
  /-- Each `μ_Σ`, `Σ ∈ PSD(d)`, is a probability measure. -/
  isProbability : ∀ S : Mat d, S.PosSemidef → IsProbabilityMeasure (m S)
  /-- (a) `μ_0 = δ₀`. -/
  zero : m 0 = Measure.dirac 0
  /-- (a) `μ_I ≠ δ₀`. -/
  one_ne : m 1 ≠ Measure.dirac 0
  /-- (b) `A_*μ_Σ = μ_{A·Σ}` for every `A ∈ G` and `Σ ∈ PSD(d)`. -/
  covariant : ∀ A ∈ G, ∀ S : Mat d, S.PosSemidef → push A (m S) = m (act A S)
  /-- (c) for every `ω`, `Σ ↦ μ̂_Σ(ω)` is continuous on `PSD(d)`. -/
  continuous : ∀ ω : Rd d, ContinuousOn (fun S => charFun (m S) ω) (psdSet d)

/-- **Property (d)** (`lem:gw-kernels-from-origin`(2)): every pair `Σ ≤_W Σ'` has a probability
measure `ρ` with `μ_{Σ'} = μ_Σ * ρ`. -/
def HasIncrements (le : Mat d → Mat d → Prop) (m : Mat d → Measure (Rd d)) : Prop :=
  ∀ S S' : Mat d, S.PosSemidef → S'.PosSemidef → le S S' →
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ m S' = m S ∗ ρ

/-- **No transform has a zero** (`lem:gw-kernels-from-origin`(2)–(3)): `μ̂_Σ(ω) ≠ 0` for every
`Σ ∈ PSD(d)` and `ω`. -/
def HasNoZeros (m : Mat d → Measure (Rd d)) : Prop :=
  ∀ S : Mat d, S.PosSemidef → ∀ ω : Rd d, charFun (m S) ω ≠ 0

/-- **`m` is the family of kernels from the origin of a `(G, W)`-cascade family of kernels**:
there is such a family `μ` with `μ_{0,Σ} = m_Σ` for every `Σ ∈ PSD(d)`. -/
def IsKernelsFromOrigin (G : Set (Mat d)) (le : Mat d → Mat d → Prop)
    (m : Mat d → Measure (Rd d)) : Prop :=
  ∃ μ : Mat d → Mat d → Measure (Rd d), IsGWCascadeFamily G le μ ∧
    ∀ S : Mat d, S.PosSemidef → μ 0 S = m S

/-! ## Products and frames (`prop:frame-families`, `prop:fixed-frame-families`) -/

/-- **The product law** `ν₁ ⊗ ⋯ ⊗ ν_d` on `ℝ^d` of laws on `ℝ`: `Measure.pi` on `Fin d → ℝ`,
carried to `EuclideanSpace ℝ (Fin d)` (the form of Mathlib's `charFun_pi`). -/
noncomputable def prodLaw (ν : Fin d → Measure ℝ) : Measure (Rd d) :=
  (Measure.pi ν).map (WithLp.toLp 2)

/-- **`(c)_*ν`**, the image of a law on `ℝ` under `x ↦ c x`. -/
noncomputable def dilLine (c : ℝ) (ν : Measure ℝ) : Measure ℝ := ν.map fun x => c * x

/-- **A cascade on the line** (`prop:frame-families`): probability measures
`(ν_{s,s'})_{0 ≤ s ≤ s'}` on `ℝ` with `ν_{s,s} = δ₀` and `ν_{s,s''} = ν_{s',s''} * ν_{s,s'}` for
`s ≤ s' ≤ s''`. -/
structure IsLineCascade (ν : ℝ → ℝ → Measure ℝ) : Prop where
  isProbability : ∀ s s' : ℝ, 0 ≤ s → s ≤ s' → IsProbabilityMeasure (ν s s')
  diag : ∀ s : ℝ, 0 ≤ s → ν s s = Measure.dirac 0
  cascade : ∀ s s' s'' : ℝ, 0 ≤ s → s ≤ s' → s' ≤ s'' → ν s s'' = ν s' s'' ∗ ν s s'

/-- **The frame family** (`prop:frame-families`): `μ_{A;s,s'} := A_*(ν⁽¹⁾_{s₁,s'₁} ⊗ ⋯ ⊗
ν⁽ᵈ⁾_{s_d,s'_d})`. -/
noncomputable def frameFamily (ν : Fin d → ℝ → ℝ → Measure ℝ) (A : Mat d) (s s' : Fin d → ℝ) :
    Measure (Rd d) :=
  push A (prodLaw fun i => ν i (s i) (s' i))

/-! ## The diagonal group (`prop:diagonal-ray-families`) -/

/-- **`Δ(Σ) := diag(Σ₁₁, …, Σ_dd)`** (`prop:diagonal-ray-families`). -/
def diagPart (S : Mat d) : Mat d := diagonal fun i => S i i

/-- **The symmetric matrices with unit diagonal**, the affine space in which `Corr(d)` is open
(`prop:diagonal-ray-families`(1)). -/
def unitDiagSym (d : ℕ) : Set (Mat d) := {R | R.IsSymm ∧ ∀ i, R i i = 1}

/-- **`Corr(d) := {R ∈ PD(d) : R₁₁ = ⋯ = R_dd = 1}`**, the correlation matrices
(`prop:diagonal-ray-families`). -/
def corrSet (d : ℕ) : Set (Mat d) := {R | R.PosDef ∧ ∀ i, R i i = 1}

/-! ## The similarities (`prop:similarity-ray-families`) -/

/-- **`σ(Σ)`**, the eigenvalues of `Σ` in nonincreasing order divided by `tr Σ`
(`prop:similarity-ray-families`); read on `PSD(d) ∖ {0}`. -/
noncomputable def normSpec (S : Mat d) : Fin d → ℝ := (S.trace)⁻¹ • (eigUp S ∘ Fin.rev)

/-- **`Δ_d := {σ : σ₁ ≥ ⋯ ≥ σ_d ≥ 0, σ₁ + ⋯ + σ_d = 1}`** (`prop:similarity-ray-families`). -/
def simplexDesc (d : ℕ) : Set (Fin d → ℝ) :=
  {σ | Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧ ∑ i, σ i = 1}

/-- **The shape-blind family** `ν_Σ := ((det Σ)^{1/(2d)} I)_*μ_I`
(`prop:similarity-ray-families`(3)(ii)); `(det Σ)^{1/(2d)}` is the volume scale `volScale`. -/
noncomputable def shapeBlind (μI : Measure (Rd d)) (S : Mat d) : Measure (Rd d) :=
  push (volScale S • (1 : Mat d)) μI

/-! ## The general similarity-covariant part (`prop:similarity-general-sandwich`) -/

/-- **The standing hypotheses of `prop:similarity-general-sandwich`**: for each `Σ ∈ PD(d)`,
`μ_Σ` is a symmetric infinitely divisible probability measure with generating triplet
`(C(Σ), L_Σ, 0)`, and `(√c Q)_*μ_Σ = μ_{cQΣQᵀ}` for `c > 0`, `Q ∈ O(d)`. -/
structure IsSimGeneralFamily (μ : Mat d → Measure (Rd d)) (C : Mat d → Mat d)
    (L : Mat d → Measure (Rd d)) : Prop where
  isProbability : ∀ S : Mat d, S.PosDef → IsProbabilityMeasure (μ S)
  /-- `μ_Σ` is symmetric, `(-I)_*μ_Σ = μ_Σ`. -/
  symmetric : ∀ S : Mat d, S.PosDef → push (-1) (μ S) = μ S
  infinitelyDivisible : ∀ S : Mat d, S.PosDef → IsInfinitelyDivisible (μ S)
  /-- `μ_Σ` has generating triplet `(C(Σ), L_Σ, 0)`. -/
  triplet : ∀ S : Mat d, S.PosDef →
    ∃ T : LevyTriplet d, T.A = C S ∧ T.ν = L S ∧ T.γ = 0 ∧ HasTriplet (μ S) T
  /-- Similarity covariance, (K3) for `A = √c Q`. -/
  covariant : ∀ S : Mat d, S.PosDef → ∀ c : ℝ, 0 < c → ∀ Q ∈ orthSet d,
    push (Real.sqrt c • Q) (μ S) = μ (c • (Q * S * Qᵀ))

/-- **The exponent** `ψ_L(ω) := ∫ (1 - cos⟨ω, x⟩) L(dx)`, real-valued (`levyExpL`'s value, finite
for a Lévy measure). -/
noncomputable def levyExp (L : Measure (Rd d)) (ω : Rd d) : ℝ := (levyExpL L ω).toReal

/-- **A Lévy measure on `ℝ^d`** (Sato (8.2)): `L{0} = 0` and `∫ (|x|² ∧ 1) L(dx) < ∞`. -/
def IsLevyMeasure (L : Measure (Rd d)) : Prop :=
  L {0} = 0 ∧ ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂L ≠ ⊤

/-- **"Every Loewner step `Σ ≤ Σ'` in `PD(d)` has an infinitely divisible increment"**
(`prop:similarity-general-sandwich`(4), the first hypothesis). -/
def HasIDLoewnerIncrements (μ : Mat d → Measure (Rd d)) : Prop :=
  ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
    ∃ ρ : Measure (Rd d), IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧ μ S' = μ S ∗ ρ

/-- **"Every Loewner step in `PD(d)` has a positive finite increment"**
(`prop:similarity-general-sandwich`(4), the second hypothesis, with `C ≡ 0`). -/
def HasFiniteLoewnerIncrements (μ : Mat d → Measure (Rd d)) : Prop :=
  ∀ S S' : Mat d, S.PosDef → S'.PosDef → loewnerLE S S' →
    ∃ ρ : Measure (Rd d), IsFiniteMeasure ρ ∧ μ S' = μ S ∗ ρ

/-- **`Σ_ε := diag(1, ε, …, ε)`** (`prop:similarity-general-sandwich`); `Σ₀ = e₁e₁ᵀ`. -/
def sigmaEps (d : ℕ) (ε : ℝ) : Mat d := diagonal fun i => if (i : ℕ) = 0 then 1 else ε

/-- **A set bounded away from the origin**: `|x| ≥ δ` on it for some `δ > 0`. -/
def IsBoundedAway (B : Set (Rd d)) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ B, δ ≤ ‖x‖

/-- **`L_*` is the rank-one limit of `L`** (`prop:similarity-general-sandwich`(4)):
`L_*{0} = 0` and `L_*(B) = lim_{ε↓0} L_{Σ_ε}(B)` for every Borel `B` bounded away from the
origin. -/
def IsRankOneLimit (L : Mat d → Measure (Rd d)) (Lstar : Measure (Rd d)) : Prop :=
  Lstar {0} = 0 ∧ ∀ B : Set (Rd d), MeasurableSet B → IsBoundedAway B →
    Tendsto (fun ε => L (sigmaEps d ε) B) (𝓝[>] 0) (𝓝 (Lstar B))

/-- **`ψ_*` is the rank-one limit of the exponents** (`prop:similarity-general-sandwich`(4)):
`ψ_*(ω) = lim_{ε↓0} ψ_{Σ_ε}(ω)` for every `ω`. -/
def IsRankOneExpLimit (L : Mat d → Measure (Rd d)) (ψstar : Rd d → ℝ) : Prop :=
  ∀ ω : Rd d, Tendsto (fun ε => levyExp (L (sigmaEps d ε)) ω) (𝓝[>] 0) (𝓝 (ψstar ω))

/-- **`𝓜*_r := lim_{ε↓0} 𝓜_r(L_{Σ_ε})`** (`prop:similarity-general-bounded-shape`(4)), read where
the node proves the limit exists. -/
noncomputable def rankOneMoment (L : Mat d → Measure (Rd d)) (r : ℝ) : Mat d :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => momentMatrix r (L (sigmaEps d ε))

/-- **`θ_r := d min(a_r, b_r)/T_r(L_I)`** (`prop:similarity-general-bounded-shape`(4)), with
`min(a_r, b_r) = λ_min(𝓜*_r)` for `𝓜*_r = diag(a_r, b_r, …, b_r)`. -/
noncomputable def momentTheta (L : Mat d → Measure (Rd d)) (r : ℝ) : ℝ :=
  (d : ℝ) * lamMin (rankOneMoment L r) / momentTrace r (L 1)

/-! ## Directions (`prop:similarity-general-index-zero`, `prop:similarity-line-family`) -/

/-- **`σ̄`, the normalised surface measure on `S^{d-1}`**, as a measure on `ℝ^d` carried by the
unit sphere: Mathlib's `volume.toSphere`, pushed forward by the inclusion and divided by its
mass. -/
noncomputable def normSphere (d : ℕ) : Measure (Rd d) :=
  (((volume : Measure (Rd d)).toSphere) univ)⁻¹ •
    ((volume : Measure (Rd d)).toSphere).map Subtype.val

/-- **`K_A(ε) := {x : ε < |x| ≤ 1, x/|x| ∈ A}`** (`prop:similarity-general-index-zero`). -/
def polarSector (A : Set (Rd d)) (ε : ℝ) : Set (Rd d) :=
  {x | ε < ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖x‖⁻¹ • x ∈ A}

/-! ## The part laid along lines (`prop:similarity-line-family`) -/

/-- **`ℓ(dr) := k(|r|) dr/|r|`** on `ℝ ∖ {0}` (`prop:similarity-line-family`). -/
noncomputable def lineProfileMeasure (k : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict ({0}ᶜ : Set ℝ)).withDensity fun r => ENNReal.ofReal (k |r| / |r|)

/-- **`L_Σ`** (`prop:similarity-line-family`): the measure on `ℝ^d ∖ {0}` with
`∫ f dL_Σ = ∫ σ̄(du) ∫ f(r q_Σ(u)^{1/2} u) ℓ(dr)` for Borel `f ≥ 0` with `f(0) = 0`, `q_Σ(u) =
⟨u, Σu⟩`: the mixture over directions of the images of `ℓ`, restricted to `ℝ^d ∖ {0}`. That it is
that measure is clause (1) of the node. -/
noncomputable def lineLevy (k : ℝ → ℝ) (S : Mat d) : Measure (Rd d) :=
  ((normSphere d).bind fun u =>
      (lineProfileMeasure k).map fun r => (r * Real.sqrt (quad S u)) • u).restrict {0}ᶜ

/-! ## The degenerate family (`prop:similarity-degenerate-family`) -/

/-- **The gauge `h(Σ) := (det Σ)^γ Σ^p`** (`prop:similarity-degenerate-family`), `0` when `Σ`
is singular (for `γ > 0`). -/
noncomputable def degGauge (γ p : ℝ) (S : Mat d) : Mat d := (S.det ^ γ) • mrpow S p

/-- **The Lévy measure `n_H(x) dx`** of `S_α(H)` (`lem:elliptical-stable`), on `ℝ^d ∖ {0}`. -/
noncomputable def stableLevy [NeZero d] (α : ℝ) (H : Mat d) : Measure (Rd d) :=
  (volume.restrict ({0}ᶜ : Set (Rd d))).withDensity fun x => ENNReal.ofReal (stableDensity α H x)

/-- **`G₀ := ∫ (z_d² ∧ 1) |z|^{-d-α} dz`** (`prop:similarity-degenerate-family`(2)), `z_d` the last
coordinate. -/
noncomputable def degConstG0 [NeZero d] (α : ℝ) : ℝ :=
  ∫ z : Rd d, min (z ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)

/-- **`G₁ := ∫ (|z|² ∧ 1) |z|^{-d-α} dz`** (`prop:similarity-degenerate-family`(2)). -/
noncomputable def degConstG1 (d : ℕ) (α : ℝ) : ℝ :=
  ∫ z : Rd d, min (‖z‖ ^ 2) 1 * ‖z‖ ^ (-(d : ℝ) - α)

/-! ## The stable order on `PSD(d)` (`prop:similarity-stable-order-families`) -/

/-- **`ε_α(Σ) := (λ₁^{d+α}/det Σ)^{1/α}`** (`prop:similarity-stable-order-families`(1)), `λ₁` the
least eigenvalue. -/
noncomputable def epsAlpha (α : ℝ) (S : Mat d) : ℝ :=
  (lamMin S ^ ((d : ℝ) + α) / S.det) ^ (1 / α)

/-- **`t_α(Σ) := (λ_d^{d+α}/det Σ)^{1/α}`** (`prop:similarity-stable-order-families`(1)), `λ_d` the
largest eigenvalue. -/
noncomputable def tAlpha (α : ℝ) (S : Mat d) : ℝ :=
  (lamMax S ^ ((d : ℝ) + α) / S.det) ^ (1 / α)

/-- **`𝒟_α`**, the diagonal matrices `diag(b)` with `(d+α) min_i b_i ≥ b₁ + ⋯ + b_d`
(`prop:diagonal-stable-order-families`): the diagonal matrices of the cone `𝔨_α`. -/
def diagStableSet (d : ℕ) (α : ℝ) : Set (Mat d) :=
  {B | ∃ b : Fin d → ℝ, B = diagonal b ∧ ∑ i, b i ≤ ((d : ℝ) + α) * ⨅ i, b i}

end AffineHemigroup
