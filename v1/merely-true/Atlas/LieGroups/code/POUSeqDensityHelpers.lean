/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.PartitionOfUnity

set_option linter.unusedSectionVars false

open TopologicalSpace Metric Set Filter Topology

noncomputable section

section MetrizableLCSC

variable (X : Type*) [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X]

instance metrizable_of_lcsc : MetrizableSpace X := inferInstance

end MetrizableLCSC

section FiniteEpsNet

variable {X : Type*} [MetricSpace X]

end FiniteEpsNet

section POUAndDirac

variable {X : Type*} [MetricSpace X] [CompactSpace X]

def ContinuousMap.liftReal (f : C(X, ℝ)) : C(X, ℂ) :=
  (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f

def diracCLM (x : X) : WeakDual ℂ C(X, ℂ) :=
  (ContinuousMap.evalCLM ℂ x : C(X, ℂ) →L[ℂ] ℂ)

def diracPOUApprox
    (μ : WeakDual ℂ C(X, ℂ))
    (S : Finset X)
    (φ : S → C(X, ℝ))
    : WeakDual ℂ C(X, ℂ) :=
  ∑ s : S, (μ (ContinuousMap.liftReal (φ s))) • diracCLM (s : X)

end POUAndDirac

section ErrorBound

variable {X : Type*} [MetricSpace X] [CompactSpace X]


end ErrorBound

end
