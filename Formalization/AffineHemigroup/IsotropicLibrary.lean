/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Basic
import AffineHemigroup.Defs.IsotropicFamily
import AffineHemigroup.Defs.Operators
import AffineHemigroup.Defs.Origin
import AffineHemigroup.Interfaces
import AffineHemigroup.MatrixCalculus
import AffineHemigroup.Thresholds
import AffineHemigroup.ThresholdCriterion
import AffineHemigroup.ThresholdLimit
import AffineHemigroup.ThresholdAsymptotic
import AffineHemigroup.RadialMarginal
import AffineHemigroup.MarginalFamily
import AffineHemigroup.IsotropicClassification
import AffineHemigroup.Polar
import AffineHemigroup.WitnessDatum
import AffineHemigroup.GaussVar
import AffineHemigroup.OriginDecay
import AffineHemigroup.OriginProfile
import AffineHemigroup.PositiveTransform
import AffineHemigroup.OriginBoundedness
import AffineHemigroup.DelayPolar
import AffineHemigroup.Subordinated
import AffineHemigroup.ExponentLog
import AffineHemigroup.PolarReading
import AffineHemigroup.LineLevyUnique
import AffineHemigroup.PolarClassification
import AffineHemigroup.FiltrationStrict
import AffineHemigroup.LevyKhintchineNegDef
import AffineHemigroup.BernsteinUnique
import AffineHemigroup.FiltrationTop
import AffineHemigroup.NoCinRay
import AffineHemigroup.SeparatingFamily
import AffineHemigroup.ShadowProfile
import AffineHemigroup.ProfileOneDimensionDown
import AffineHemigroup.ScaleZeroKernels
import AffineHemigroup.StageLevyMeasure
import AffineHemigroup.StageAtom
import AffineHemigroup.StageDensity
import AffineHemigroup.IsotropicBridge
import AffineHemigroup.RadialMonotone
import AffineHemigroup.OriginLowerBound
import AffineHemigroup.OriginUpperBound
import AffineHemigroup.OriginRate
import AffineHemigroup.SlowFactor
import AffineHemigroup.SphereLogMean
import AffineHemigroup.ExponentProfile
import AffineHemigroup.OriginRateProfile
import AffineHemigroup.OperatorsKernels
import AffineHemigroup.OperatorFamilies
import AffineHemigroup.KernelsContinuity
import AffineHemigroup.KernelsOperators
import AffineHemigroup.IsotropicOperators

/-!
# The library of the isotropic paper

Imports and no declaration. The files imported are those that hold a declaration which a
statement of the isotropic paper is tagged with in the blueprint: the statements of chapter 3,
the cited facts and `prop:line-levy-unique` of chapter 2, and the two statements of chapter 4
that the paper's lemma on operators and kernels renders (`lem:operators-to-kernels`,
`lem:kernels-to-operators`). Their import closure is the Lean of the isotropic paper.

The formal examples (`AffineHemigroup.Witnesses`), the probes (`AffineHemigroup.Probes`) and the
paper's axiom guard (`AffineHemigroup.IsoAxiomGuard`) import this file where they imported the
whole library `AffineHemigroup` (Q-0452), so that none of the three reaches a file of the affine
paper. A file that comes to hold a tagged declaration of the isotropic paper is added here; the
guard, which names every such declaration, does not build without it.
-/
