/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import ScaleSpaceCore.MainAnalysis
import ScaleSpaceCore.GaugeLevy

/-!
# What the development takes from upstream

The imports the library starts from, and nothing else: no declaration is made here.

* Mathlib: Euclidean space, the Fourier transform, and the Loewner order on matrices (an instance
  scoped to `MatrixOrder`).
* The shared library `ScaleSpaceCore`, required at `v0.3.0`: the modules of
  `ScaleSpace.main_analysis` ([V, Thm 7.3], necessity; `ScaleSpaceCore.MainAnalysis`) and of
  `ScaleSpace.canonical_gauge` ([V, Prop. 6.6], `ScaleSpaceCore.GaugeLevy`), to which the isotropic
  chapter's reductions go. They were Paper V's (`SpatialLine.*`) until Q-0365 switched this
  development to the trunk's copies; the trunk's `main_analysis` takes Paper V's cited clause as a
  hypothesis, which `AffineHemigroup.line_levy_unique` discharges from ledger A3.

The shared library declares no axiom. Paper V's package `SpatialHemigroup` is not required
(`lakefile.toml`, Q-0460); a module that needs it requires it again, and a declaration that *uses*
one of V's theorems would then inherit the interfaces that theorem spends
(`blueprint/trust-boundary.txt`). Later modules import what they use directly and this file's
list shrinks or goes when they do.
-/
