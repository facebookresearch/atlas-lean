/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-- Combinatorial data abstracting a reductive group `G` acting on a
representation `V`, together with a unipotent subgroup `U`, an indexing `I` of
irreducible subrepresentations `W i`, and bookkeeping axioms: faithfulness of `U`,
irreducibility of each `W i`, complete reducibility of `V`, the existence of
unipotent fixed points in any nonzero subrepresentation, and the existence of the
fixed-point subspace under `U` of any subrepresentation. -/
structure ReductiveGroupData where
  G : Type
  U : Type
  V : Type
  g_one : G
  u_incl : U → G
  u_one : U
  u_incl_one : u_incl u_one = g_one
  act : G → V → V
  v_zero : V
  act_zero : ∀ g : G, act g v_zero = v_zero
  act_id : ∀ v : V, act g_one v = v
  u_faithful : ∀ u : U, (∀ v : V, act (u_incl u) v = v) → u = u_one
  Sub : Type
  mem_sub : Sub → V → Prop
  I : Type
  W : I → Sub
  W_nonempty : ∀ i : I, ∃ w : V, mem_sub (W i) w ∧ w ≠ v_zero
  irred : ∀ i : I, ∀ W' : Sub,
    (∀ w : V, mem_sub W' w → mem_sub (W i) w) →
    (∃ w : V, mem_sub W' w ∧ w ≠ v_zero) →
    (∀ w : V, mem_sub (W i) w → mem_sub W' w)
  completely_reducible :
    ∀ g : G, (∀ i : I, ∀ w : V, mem_sub (W i) w → act g w = w) → ∀ v : V, act g v = v
  unipotent_fixed_pt :
    ∀ W' : Sub, (∃ w : V, mem_sub W' w ∧ w ≠ v_zero) →
      ∃ w : V, mem_sub W' w ∧ w ≠ v_zero ∧ (∀ u : U, act (u_incl u) w = w)
  fixed_pts_sub :
    ∀ W' : Sub, ∃ W_U : Sub,
      (∀ w : V, mem_sub W_U w ↔ (mem_sub W' w ∧ ∀ u : U, act (u_incl u) w = w))

namespace ReductiveGroupData

variable (D : ReductiveGroupData)

/-- The unipotent subgroup `U` acts trivially on each irreducible summand `W i`:
combining irreducibility with the existence of a unipotent fixed point forces
`U` to fix every element of `W i`. -/
theorem u_acts_trivially_on_summand (i : D.I) :
    ∀ w : D.V, D.mem_sub (D.W i) w → ∀ u : D.U, D.act (D.u_incl u) w = w := by

  obtain ⟨W_U, hW_U⟩ := D.fixed_pts_sub (D.W i)

  have hW_U_nonempty : ∃ w : D.V, D.mem_sub W_U w ∧ w ≠ D.v_zero := by
    obtain ⟨w, hw_mem, hw_ne, hw_fix⟩ := D.unipotent_fixed_pt (D.W i) (D.W_nonempty i)
    exact ⟨w, (hW_U w).mpr ⟨hw_mem, hw_fix⟩, hw_ne⟩

  have hW_U_sub : ∀ w : D.V, D.mem_sub W_U w → D.mem_sub (D.W i) w := by
    intro w hw
    exact ((hW_U w).mp hw).1

  have hW_sub_WU : ∀ w : D.V, D.mem_sub (D.W i) w → D.mem_sub W_U w :=
    D.irred i W_U hW_U_sub hW_U_nonempty

  intro w hw u
  exact ((hW_U w).mp (hW_sub_WU w hw)).2 u

/-- The unipotent subgroup `U` acts trivially on all of `V`, by complete
reducibility together with triviality on each summand. -/
theorem u_acts_trivially :
    ∀ v : D.V, ∀ u : D.U, D.act (D.u_incl u) v = v := by
  intro v u

  have h_fixes_summands : ∀ i : D.I, ∀ w : D.V,
      D.mem_sub (D.W i) w → D.act (D.u_incl u) w = w :=
    fun i w hw => D.u_acts_trivially_on_summand i w hw u

  exact D.completely_reducible (D.u_incl u) h_fixes_summands v

/-- The unipotent subgroup is trivial: every element of `U` equals the identity. -/
theorem u_is_trivial : ∀ u : D.U, u = D.u_one := by
  intro u
  apply D.u_faithful
  intro v
  exact D.u_acts_trivially v u

/-- Lemma 1.30.2 (Etingof–Gelaki–Nikshych–Ostrik): A reductive group acting on a
completely reducible faithful representation has trivial unipotent radical. -/
theorem lemma_1_30_2 (D : ReductiveGroupData) : ∀ u : D.U, u = D.u_one :=
  D.u_is_trivial

end ReductiveGroupData
