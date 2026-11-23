/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.MarkovChain
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]

section LiftKernel

/-- Lift the Markov kernel `κ : S → S` to a kernel on tuples `(x_0, …, x_n)` by reading off the
last coordinate `x_n` and applying `κ`. This is the form required by the Ionescu–Tulcea trajectory
construction. -/
noncomputable def markovLiftKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → S) S :=
  κ.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

/-- The lifted kernel `markovLiftKernel κ n` is again a Markov kernel whenever `κ` is. -/
instance markovLiftKernel.instIsMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovLiftKernel κ n) := by
  unfold markovLiftKernel; infer_instance

end LiftKernel

section CanonicalMeasure

variable (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsProbabilityMeasure μ]

/-- The canonical measure `P_μ` on path space `ℕ → S` of the Markov chain with initial
distribution `μ` and transition kernel `κ`, built via the Ionescu–Tulcea trajectory measure. -/
noncomputable def markovChainMeasure : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ : ℕ => S) μ (markovLiftKernel κ)

/-- `markovChainMeasure κ μ` is a probability measure on path space. -/
instance markovChainMeasure.isProbabilityMeasure :
    IsProbabilityMeasure (markovChainMeasure κ μ) := by
  unfold markovChainMeasure; infer_instance

omit [IsProbabilityMeasure μ] in
/-- Under the canonical Markov-chain measure, the law of the initial state `ω 0` is the initial
distribution `μ`. -/
theorem markovChainMeasure_initial_distribution :
    Measure.map (fun (ω : ℕ → S) => ω 0) (markovChainMeasure κ μ) = μ := by
  unfold markovChainMeasure trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have h_decomp : (fun (f : ℕ → S) => f 0) =
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)) ∘
    (Preorder.frestrictLe 0) := by ext ω; rfl
  rw [h_decomp, Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0)
    (MeasurableEquiv.piUnique _).measurable]
  rw [traj_map_frestrictLe, partialTraj_self]
  rw [← Measure.map_comp _ _ (MeasurableEquiv.piUnique _).measurable]
  rw [Measure.id_comp]
  rw [Measure.map_map (MeasurableEquiv.piUnique _).measurable
    (MeasurableEquiv.piUnique _).symm.measurable]
  have h_id : ⇑(MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)) ∘
    ⇑(MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)).symm = id := by
    ext x; simp [MeasurableEquiv.piUnique]
  rw [h_id, Measure.map_id]

/-- Under the canonical Markov-chain measure, the regular conditional distribution of the next
state `X_{n+1}` given the history `(X_0, …, X_n)` agrees almost everywhere with the lifted
transition kernel `markovLiftKernel κ n`. This is the defining Markov property. -/
theorem markovChainMeasure_condDistrib (n : ℕ)
    [StandardBorelSpace S] [Nonempty S] :
    condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n)
      (markovChainMeasure κ μ)
      =ᵐ[Measure.map (Preorder.frestrictLe n) (markovChainMeasure κ μ)]
        markovLiftKernel κ n := by
  exact Kernel.condDistrib_trajMeasure

end CanonicalMeasure

section ExistenceTheorem

/-- **Markov chain construction theorem.**

Given a Markov transition kernel `κ : S → S` and an initial distribution `μ` on a standard Borel
space `S`, there exists a probability measure `P` on path space `ℕ → S` such that
* the law of `ω 0` under `P` is `μ`, and
* for every `n`, the conditional law of `ω (n+1)` given the past `(ω 0, …, ω n)` is the
  transition kernel `κ` applied to the current state.

That is, the sequence `(X_0, X_1, …)` sampled from `P` is a Markov chain with initial distribution
`μ` and transitions `κ`. -/
theorem markov_chain_construction
    (κ : Kernel S S) [IsMarkovKernel κ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    [StandardBorelSpace S] [Nonempty S] :
    ∃ (P : Measure (ℕ → S)) (_ : IsProbabilityMeasure P),
      P.map (fun (ω : ℕ → S) => ω 0) = μ ∧
      ∀ n : ℕ,
        condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n) P
          =ᵐ[Measure.map (Preorder.frestrictLe n) P] markovLiftKernel κ n :=
  ⟨markovChainMeasure κ μ, markovChainMeasure.isProbabilityMeasure κ μ,
    markovChainMeasure_initial_distribution κ μ,
    fun n => markovChainMeasure_condDistrib κ μ n⟩

end ExistenceTheorem
