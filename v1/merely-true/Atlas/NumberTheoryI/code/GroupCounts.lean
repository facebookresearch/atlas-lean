/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

open scoped Classical

namespace GroupCounts

section Z2Z4

abbrev G₂₄ := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)

lemma G₂₄_inv_eq_self (a : G₂₄) : a⁻¹ = a := by
  fin_cases a <;> decide

noncomputable def subgroupToFinset₂₄ (H : Subgroup G₂₄) : Finset G₂₄ :=
  Finset.univ.filter (· ∈ H)

lemma subgroupToFinset₂₄_mem (H : Subgroup G₂₄) (g : G₂₄) :
    g ∈ subgroupToFinset₂₄ H ↔ g ∈ H := by
  unfold subgroupToFinset₂₄; simp [Finset.mem_filter]

set_option maxHeartbeats 400000 in
lemma subgroupToFinset₂₄_card (H : Subgroup G₂₄) :
    (subgroupToFinset₂₄ H).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card, subgroupToFinset₂₄, Fintype.card_of_subtype]
  intro x; simp

lemma natcard_G₂₄ : Nat.card G₂₄ = 16 := by
  rw [Nat.card_eq_fintype_card]; decide

lemma index_eq_two_iff_card_eq_eight (H : Subgroup G₂₄) :
    H.index = 2 ↔ Nat.card H = 8 := by
  constructor
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega

lemma subgroupToFinset₂₄_is_carrier (H : Subgroup G₂₄) :
    (1 : G₂₄) ∈ subgroupToFinset₂₄ H ∧
    (∀ a ∈ subgroupToFinset₂₄ H, ∀ b ∈ subgroupToFinset₂₄ H,
      a * b ∈ subgroupToFinset₂₄ H) := by
  constructor
  · rw [subgroupToFinset₂₄_mem]; exact H.one_mem
  · intro a ha b hb
    rw [subgroupToFinset₂₄_mem] at ha hb ⊢; exact H.mul_mem ha hb

noncomputable def finsetToSubgroup₂₄ (s : Finset G₂₄)
    (h1 : (1 : G₂₄) ∈ s) (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
    Subgroup G₂₄ where
  carrier := {g | g ∈ s}
  mul_mem' {a b} ha hb := hmul a ha b hb
  one_mem' := h1
  inv_mem' {a} ha := by rw [G₂₄_inv_eq_self]; exact ha

lemma round_trip_finset₂₄ (s : Finset G₂₄) (h1 : (1 : G₂₄) ∈ s)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
    subgroupToFinset₂₄ (finsetToSubgroup₂₄ s h1 hmul) = s := by
  ext g; rw [subgroupToFinset₂₄_mem]; simp [finsetToSubgroup₂₄]

lemma round_trip_subgroup₂₄ (H : Subgroup G₂₄) :
    finsetToSubgroup₂₄ (subgroupToFinset₂₄ H)
      (subgroupToFinset₂₄_is_carrier H).1
      (subgroupToFinset₂₄_is_carrier H).2 = H := by
  apply Subgroup.ext; intro g
  simp [finsetToSubgroup₂₄, subgroupToFinset₂₄_mem]

def subgroupCarriersIdx2 : Finset (Finset G₂₄) :=
  (Finset.univ : Finset G₂₄).powerset.filter
    (fun s => decide ((1 : G₂₄) ∈ s ∧
      (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ s.card = 8))


lemma mem_subgroupCarriersIdx2 (s : Finset G₂₄) :
    s ∈ subgroupCarriersIdx2 ↔
    (1 : G₂₄) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ s.card = 8 := by
  simp [subgroupCarriersIdx2, Finset.mem_filter]

noncomputable def subgroupIdx2Equiv :
    {H : Subgroup G₂₄ // H.index = 2} ≃
    {s : Finset G₂₄ // s ∈ subgroupCarriersIdx2} where
  toFun := fun ⟨H, hidx⟩ => ⟨subgroupToFinset₂₄ H, by
    rw [mem_subgroupCarriersIdx2]
    exact ⟨(subgroupToFinset₂₄_is_carrier H).1,
      (subgroupToFinset₂₄_is_carrier H).2, by
      rw [subgroupToFinset₂₄_card, (index_eq_two_iff_card_eq_eight H).mp hidx]⟩⟩
  invFun := fun ⟨s, hs⟩ => by
    rw [mem_subgroupCarriersIdx2] at hs
    exact ⟨finsetToSubgroup₂₄ s hs.1 hs.2.1, by
      rw [index_eq_two_iff_card_eq_eight]
      rw [← subgroupToFinset₂₄_card]
      rw [round_trip_finset₂₄]; exact hs.2.2⟩
  left_inv := fun ⟨H, hidx⟩ => by
    simp only; congr 1; exact round_trip_subgroup₂₄ H
  right_inv := fun ⟨s, hs⟩ => by
    simp only; congr 1
    rw [mem_subgroupCarriersIdx2] at hs
    exact round_trip_finset₂₄ s hs.1 hs.2.1

end Z2Z4


section Z4Z3

abbrev G₄₃ := Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)

def addHomTriple (a b c : ZMod 4) :
    (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4 where
  toFun := fun ⟨x, y, z⟩ => a * x + b * y + c * z
  map_zero' := by simp
  map_add' := by intro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩; simp; ring

def mulHomTriple (a b c : ZMod 4) :
    G₄₃ →* Multiplicative (ZMod 4) :=
  AddMonoidHom.toMultiplicative (addHomTriple a b c)

lemma mem_ker_mulHomTriple (a b c : ZMod 4) (g : G₄₃) :
    g ∈ (mulHomTriple a b c).ker ↔
    a * g.toAdd.1 + b * g.toAdd.2.1 + c * g.toAdd.2.2 = 0 := by
  simp [MonoidHom.mem_ker, mulHomTriple, AddMonoidHom.toMultiplicative,
        addHomTriple, Multiplicative.ofAdd, Multiplicative.toAdd]
  rfl

def isSurjTriple (a b c : ZMod 4) : Prop :=
  ∃ x y z : ZMod 4, a * x + b * y + c * z = 1

private instance (a b c : ZMod 4) : Decidable (isSurjTriple a b c) := by
  unfold isSurjTriple; infer_instance

set_option maxHeartbeats 800000 in
lemma mulHomTriple_surjective (a b c : ZMod 4) (h : isSurjTriple a b c) :
    Function.Surjective (mulHomTriple a b c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  intro t
  use Multiplicative.ofAdd (t.toAdd * x, t.toAdd * y, t.toAdd * z)
  show mulHomTriple a b c (Multiplicative.ofAdd (t.toAdd * x, t.toAdd * y, t.toAdd * z)) = t
  simp only [mulHomTriple, AddMonoidHom.toMultiplicative, addHomTriple,
        Multiplicative.ofAdd, Multiplicative.toAdd, Equiv.coe_fn_symm_mk,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.coe_fn_mk]
  have key : a * (t.toAdd * x) + b * (t.toAdd * y) + c * (t.toAdd * z) = t.toAdd := by
    have h1 : a * (t.toAdd * x) = t.toAdd * (a * x) := by ring
    have h2 : b * (t.toAdd * y) = t.toAdd * (b * y) := by ring
    have h3 : c * (t.toAdd * z) = t.toAdd * (c * z) := by ring
    rw [h1, h2, h3, ← mul_add, ← mul_add, hxyz, mul_one]
  exact key

lemma mulHomTriple_ker_index (a b c : ZMod 4) (h : isSurjTriple a b c) :
    (mulHomTriple a b c).ker.index = 4 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (mulHomTriple_surjective a b c h)]
  rw [Subgroup.card_top, Nat.card_eq_fintype_card]; decide

lemma mulHomTriple_ker_isCyclic (a b c : ZMod 4)
    (h : isSurjTriple a b c) :
    IsCyclic (G₄₃ ⧸ (mulHomTriple a b c).ker) := by
  have e := QuotientGroup.quotientKerEquivOfSurjective
    (mulHomTriple a b c) (mulHomTriple_surjective a b c h)
  exact (MulEquiv.isCyclic e).mpr inferInstance

lemma addHom_eq_triple (f : (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4)
    (x y z : ZMod 4) :
    f (x, y, z) = f (1, 0, 0) * x + f (0, 1, 0) * y + f (0, 0, 1) * z := by
  have decomp : (x, y, z) = (x, (0 : ZMod 4), (0 : ZMod 4)) +
    ((0 : ZMod 4), y, (0 : ZMod 4)) + ((0 : ZMod 4), (0 : ZMod 4), z) := by
    ext <;> simp
  rw [decomp, map_add, map_add]
  have nsmul_cast : ∀ (n : ℕ) (a : ZMod 4), n • a = (n : ZMod 4) * a := by
    intros; simp
  have h1 : f (x, 0, 0) = f (1, 0, 0) * x := by
    have he : (x, (0 : ZMod 4), (0 : ZMod 4)) =
        x.val • ((1 : ZMod 4), (0 : ZMod 4), (0 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  have h2 : f (0, y, 0) = f (0, 1, 0) * y := by
    have he : ((0 : ZMod 4), y, (0 : ZMod 4)) =
        y.val • ((0 : ZMod 4), (1 : ZMod 4), (0 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  have h3 : f (0, 0, z) = f (0, 0, 1) * z := by
    have he : ((0 : ZMod 4), (0 : ZMod 4), z) =
        z.val • ((0 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  rw [h1, h2, h3]

lemma mulHom_eq_triple (f : G₄₃ →* Multiplicative (ZMod 4)) :
    ∃ a b c : ZMod 4,
      ∀ g : G₄₃, f g = mulHomTriple a b c g := by
  let f' : (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4 := AddMonoidHom.toMultiplicative.symm f
  use f' (1, 0, 0), f' (0, 1, 0), f' (0, 0, 1)
  intro g
  have hf : f = AddMonoidHom.toMultiplicative f' := by simp [f']
  rw [hf]
  simp only [mulHomTriple]
  show AddMonoidHom.toMultiplicative f' g =
    AddMonoidHom.toMultiplicative (addHomTriple (f' (1, 0, 0)) (f' (0, 1, 0)) (f' (0, 0, 1))) g
  congr 1
  ext ⟨x, y, z⟩
  exact addHom_eq_triple f' x y z

noncomputable def subgroupToFinset₄₃ (H : Subgroup G₄₃) : Finset G₄₃ :=
  Finset.univ.filter (· ∈ H)

lemma subgroupToFinset₄₃_mem (H : Subgroup G₄₃) (g : G₄₃) :
    g ∈ subgroupToFinset₄₃ H ↔ g ∈ H := by
  unfold subgroupToFinset₄₃; simp [Finset.mem_filter]

lemma subgroupToFinset₄₃_injective :
    Function.Injective subgroupToFinset₄₃ := by
  intro H₁ H₂ h; apply Subgroup.ext; intro g
  rw [← subgroupToFinset₄₃_mem H₁, ← subgroupToFinset₄₃_mem H₂, h]

set_option maxHeartbeats 400000 in

lemma natcard_G₄₃ : Nat.card G₄₃ = 64 := by
  rw [Nat.card_eq_fintype_card]; decide

def kerFinsetMul (a b c : ZMod 4) : Finset G₄₃ :=
  Finset.univ.filter (fun g =>
    a * (Multiplicative.toAdd g).1 + b * (Multiplicative.toAdd g).2.1 +
    c * (Multiplicative.toAdd g).2.2 = 0)

def surjKernelsMul : Finset (Finset G₄₃) :=
  ((Finset.univ : Finset (ZMod 4 × ZMod 4 × ZMod 4)).filter
    (fun abc => decide (isSurjTriple abc.1 abc.2.1 abc.2.2))).image
    (fun abc => kerFinsetMul abc.1 abc.2.1 abc.2.2)


lemma ker_carrier_eq_kerFinsetMul (a b c : ZMod 4) :
    subgroupToFinset₄₃ (mulHomTriple a b c).ker = kerFinsetMul a b c := by
  ext g
  rw [subgroupToFinset₄₃_mem, mem_ker_mulHomTriple]
  simp [kerFinsetMul, Finset.mem_filter]

lemma ker_carrier_mem_surjKernels (a b c : ZMod 4) (h : isSurjTriple a b c) :
    subgroupToFinset₄₃ (mulHomTriple a b c).ker ∈ surjKernelsMul := by
  rw [ker_carrier_eq_kerFinsetMul]
  unfold surjKernelsMul
  rw [Finset.mem_image]
  exact ⟨(a, b, c), by simp [Finset.mem_filter, h], rfl⟩

noncomputable def surjTripleOf (s : Finset G₄₃) (hs : s ∈ surjKernelsMul) :
    { abc : ZMod 4 × ZMod 4 × ZMod 4 // isSurjTriple abc.1 abc.2.1 abc.2.2 ∧
      s = kerFinsetMul abc.1 abc.2.1 abc.2.2 } := by
  have : ∃ abc : ZMod 4 × ZMod 4 × ZMod 4, isSurjTriple abc.1 abc.2.1 abc.2.2 ∧
      s = kerFinsetMul abc.1 abc.2.1 abc.2.2 := by
    simp only [surjKernelsMul, Finset.mem_image, Finset.mem_filter] at hs
    obtain ⟨⟨a, b, c⟩, ⟨_, hsurj⟩, heq⟩ := hs
    exact ⟨(a, b, c), of_decide_eq_true hsurj, heq.symm⟩
  exact Classical.indefiniteDescription _ this

lemma carrier_of_cyclic_idx4_in_surjKernels
    (H : Subgroup G₄₃) (hidx : H.index = 4)
    (hcyc : IsCyclic (G₄₃ ⧸ H)) :
    subgroupToFinset₄₃ H ∈ surjKernelsMul := by
  haveI : Fintype (G₄₃ ⧸ H) := Fintype.ofFinite _
  have hcard_quot : Nat.card (G₄₃ ⧸ H) = 4 := by
    rw [← Subgroup.index_eq_card]; exact hidx
  have iso := zmodCyclicMulEquiv hcyc
  rw [hcard_quot] at iso
  let π := QuotientGroup.mk' H
  let f := iso.symm.toMonoidHom.comp π
  have hf_surj : Function.Surjective f := by
    apply Function.Surjective.comp iso.symm.surjective
    exact QuotientGroup.mk'_surjective H
  have hker : f.ker = H := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, f]
    constructor
    · intro h
      have h1 : iso.symm (π g) = 1 := h
      have h2 : π g = iso 1 := by rw [← h1, MulEquiv.apply_symm_apply]
      rw [map_one] at h2
      exact (QuotientGroup.eq_one_iff g).mp h2
    · intro h
      have : π g = 1 := (QuotientGroup.eq_one_iff g).mpr h
      simp [this]
  obtain ⟨a, b, c, hf_eq⟩ := mulHom_eq_triple f
  have h_surj : isSurjTriple a b c := by
    obtain ⟨g, hg⟩ := hf_surj (Multiplicative.ofAdd (1 : ZMod 4))
    use g.toAdd.1, g.toAdd.2.1, g.toAdd.2.2
    have := hf_eq g
    rw [hg] at this
    simp only [mulHomTriple, AddMonoidHom.toMultiplicative, addHomTriple,
          Multiplicative.ofAdd, Multiplicative.toAdd, Equiv.coe_fn_symm_mk,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.coe_fn_mk] at this
    exact this.symm
  have hcarrier : subgroupToFinset₄₃ H = subgroupToFinset₄₃ (mulHomTriple a b c).ker := by
    ext g
    rw [subgroupToFinset₄₃_mem, subgroupToFinset₄₃_mem]
    rw [← hker]
    constructor
    · intro hg
      rw [MonoidHom.mem_ker]
      have : f g = mulHomTriple a b c g := hf_eq g
      rw [← this]
      rw [MonoidHom.mem_ker] at hg
      exact hg
    · intro hg
      rw [MonoidHom.mem_ker] at hg ⊢
      have : f g = mulHomTriple a b c g := hf_eq g
      rw [this]; exact hg
  rw [hcarrier]
  exact ker_carrier_mem_surjKernels a b c h_surj

noncomputable def subgroupCyclicIdx4Equiv :
    {H : Subgroup G₄₃ // H.index = 4 ∧
      IsCyclic (G₄₃ ⧸ H)} ≃
    {s : Finset G₄₃ // s ∈ surjKernelsMul} where
  toFun := fun ⟨H, hidx, hcyc⟩ =>
    ⟨subgroupToFinset₄₃ H, carrier_of_cyclic_idx4_in_surjKernels H hidx hcyc⟩
  invFun := fun ⟨s, hs⟩ =>
    let t := surjTripleOf s hs
    ⟨(mulHomTriple t.1.1 t.1.2.1 t.1.2.2).ker,
     mulHomTriple_ker_index t.1.1 t.1.2.1 t.1.2.2 t.2.1,
     mulHomTriple_ker_isCyclic t.1.1 t.1.2.1 t.1.2.2 t.2.1⟩
  left_inv := fun ⟨H, hidx, hcyc⟩ => by
    simp only
    have hmem := carrier_of_cyclic_idx4_in_surjKernels H hidx hcyc
    let t := surjTripleOf (subgroupToFinset₄₃ H) hmem
    have heq : subgroupToFinset₄₃ H = kerFinsetMul t.1.1 t.1.2.1 t.1.2.2 := t.2.2
    congr 1
    rw [← ker_carrier_eq_kerFinsetMul] at heq
    exact subgroupToFinset₄₃_injective heq.symm
  right_inv := fun ⟨s, hs⟩ => by
    simp only
    let t := surjTripleOf s hs
    have heq : s = kerFinsetMul t.1.1 t.1.2.1 t.1.2.2 := t.2.2
    congr 1
    rw [ker_carrier_eq_kerFinsetMul]
    exact heq.symm

end Z4Z3


end GroupCounts
