/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie

universe u v w

namespace DModules

open scoped TensorProduct

section DifferentialOperators

noncomputable def endBracketMul {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    (L : Module.End k A) (f : A) : Module.End k A :=
  L ∘ₗ (Algebra.lmul k A f) - (Algebra.lmul k A f) ∘ₗ L

noncomputable def diffOpOrder (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A] :
    ℕ → Submodule k (Module.End k A)
  | 0 => LinearMap.range (Algebra.lmul k A).toLinearMap
  | n + 1 =>
    { carrier := { L | ∀ f : A, endBracketMul L f ∈ diffOpOrder k A n }
      add_mem' := fun {a b} ha hb f => by
        have key : endBracketMul (a + b) f = endBracketMul a f + endBracketMul b f := by
          simp only [endBracketMul, LinearMap.add_comp, LinearMap.comp_add]; abel
        rw [key]; exact Submodule.add_mem _ (ha f) (hb f)
      zero_mem' := fun f => by
        have key : endBracketMul (0 : Module.End k A) f = 0 := by
          simp only [endBracketMul, LinearMap.zero_comp, LinearMap.comp_zero, sub_self]
        rw [key]; exact Submodule.zero_mem _
      smul_mem' := fun c L hL f => by
        have key : endBracketMul (c • L) f = c • endBracketMul L f := by
          simp only [endBracketMul, LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]
        rw [key]; exact Submodule.smul_mem _ c (hL f) }

noncomputable def diffOps (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A] :
    Submodule k (Module.End k A) :=
  ⨆ n, diffOpOrder k A n

end DifferentialOperators

section DModulesAffine

structure LeftDModule (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  vecFieldAction : Derivation k A A → M →ₗ[k] M
  vecFieldAction_smul : ∀ (v : Derivation k A A) (f : A) (m : M),
    vecFieldAction v (f • m) = f • vecFieldAction v m + v f • m
  vecFieldAction_smul_vec : ∀ (f : A) (v : Derivation k A A) (m : M),
    vecFieldAction (f • v) m = f • vecFieldAction v m
  vecFieldAction_lie : ∀ (v w : Derivation k A A) (m : M),
    vecFieldAction v (vecFieldAction w m) - vecFieldAction w (vecFieldAction v m) =
      vecFieldAction ⁅v, w⁆ m

structure RightDModule (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  vecFieldAction : Derivation k A A → M →ₗ[k] M
  right_leibniz : ∀ (v : Derivation k A A) (f : A) (m : M),
    vecFieldAction v (f • m) = f • vecFieldAction v m - v f • m
  lin_in_vec : ∀ (f : A) (v : Derivation k A A) (m : M),
    vecFieldAction (f • v) m = f • vecFieldAction v m
  flat : ∀ (v w : Derivation k A A) (m : M),
    vecFieldAction v (vecFieldAction w m) - vecFieldAction w (vecFieldAction v m) =
      - vecFieldAction ⁅v, w⁆ m

end DModulesAffine

section DModulesSheaf

structure SheafOfDiffOps (k : Type u) [CommRing k] where
  I : Type v
  coordRing : I → Type w
  instCommRing : ∀ i, CommRing (coordRing i)
  instAlgebra : ∀ i, Algebra k (coordRing i)
  diffOpsRing : I → Type w
  instDiffRing : ∀ i, Ring (diffOpsRing i)
  instDiffAlgebra : ∀ i, @Algebra (coordRing i) (diffOpsRing i)
    (instCommRing i).toCommSemiring (instDiffRing i).toSemiring
  incl : I → I → Prop
  incl_refl : ∀ i, incl i i
  incl_trans : ∀ {i j k}, incl i j → incl j k → incl i k
  coordRestrict : ∀ {i j}, incl i j →
    @RingHom (coordRing i) (coordRing j)
      (instCommRing i).toNonAssocSemiring (instCommRing j).toNonAssocSemiring
  diffOpsRestrict : ∀ {i j}, incl i j →
    @RingHom (diffOpsRing i) (diffOpsRing j)
      (instDiffRing i).toNonAssocSemiring (instDiffRing j).toNonAssocSemiring

variable {k : Type u} [CommRing k]

noncomputable def SheafOfDiffOps.baseChangeType
    (D : SheafOfDiffOps.{u, v, w} k) {i j : D.I} (h : D.incl i j)
    (Mi : Type w) (inst_acg : AddCommGroup Mi)
    (inst_mod : @Module (D.diffOpsRing i) Mi (D.instDiffRing i).toSemiring
      inst_acg.toAddCommMonoid) : Type w :=
  @TensorProduct (D.coordRing i) (D.instCommRing i).toCommSemiring (D.coordRing j) Mi
    (D.instCommRing j).toAddCommMonoid inst_acg.toAddCommMonoid
    (@Module.compHom (D.coordRing j) (D.coordRing i) (D.coordRing j)
      (D.instCommRing j).toSemiring (D.instCommRing j).toAddCommMonoid
      (@Semiring.toModule _ (D.instCommRing j).toSemiring)
      (D.instCommRing i).toSemiring (D.coordRestrict h))
    (@Module.compHom (D.diffOpsRing i) (D.coordRing i) Mi
      (D.instDiffRing i).toSemiring inst_acg.toAddCommMonoid inst_mod
      (D.instCommRing i).toSemiring
      (@algebraMap (D.coordRing i) (D.diffOpsRing i) (D.instCommRing i).toCommSemiring
        (D.instDiffRing i).toSemiring (D.instDiffAlgebra i)))

@[reducible] noncomputable def SheafOfDiffOps.baseChangeAddCommGroup
    (D : SheafOfDiffOps.{u, v, w} k) {i j : D.I} (h : D.incl i j)
    (Mi : Type w) (inst_acg : AddCommGroup Mi)
    (inst_mod : @Module (D.diffOpsRing i) Mi (D.instDiffRing i).toSemiring
      inst_acg.toAddCommMonoid) : AddCommGroup (D.baseChangeType h Mi inst_acg inst_mod) :=
  @TensorProduct.addCommGroup (D.coordRing i) (D.instCommRing i).toCommSemiring
    (D.coordRing j) Mi ((D.instCommRing j).toRing.toAddCommGroup) inst_acg.toAddCommMonoid
    (@Module.compHom (D.coordRing j) (D.coordRing i) (D.coordRing j)
      (D.instCommRing j).toSemiring (D.instCommRing j).toAddCommMonoid
      (@Semiring.toModule _ (D.instCommRing j).toSemiring)
      (D.instCommRing i).toSemiring (D.coordRestrict h))
    (@Module.compHom (D.diffOpsRing i) (D.coordRing i) Mi
      (D.instDiffRing i).toSemiring inst_acg.toAddCommMonoid inst_mod
      (D.instCommRing i).toSemiring
      (@algebraMap (D.coordRing i) (D.diffOpsRing i) (D.instCommRing i).toCommSemiring
        (D.instDiffRing i).toSemiring (D.instDiffAlgebra i)))

structure LeftDModuleSheaf (k : Type u) [CommRing k] (D : SheafOfDiffOps.{u, v, w} k) where
  sections : D.I → Type w
  instAddCommGroup : ∀ i, AddCommGroup (sections i)
  instModule : ∀ i, @Module (D.diffOpsRing i) (sections i) (D.instDiffRing i).toSemiring
    (instAddCommGroup i).toAddCommMonoid
  restrict : ∀ {i j}, D.incl i j → sections i → sections j
  restrict_add : ∀ {i j} (h : D.incl i j) (s t : sections i),
    restrict h (letI := instAddCommGroup i; s + t) =
    letI := instAddCommGroup j; restrict h s + restrict h t
  restrict_smul : ∀ {i j} (h : D.incl i j) (d : D.diffOpsRing i) (s : sections i),
    restrict h (letI := instModule i; d • s) =
    letI := instModule j; D.diffOpsRestrict h d • restrict h s
  restrict_id : ∀ (i : D.I) (s : sections i), restrict (D.incl_refl i) s = s
  restrict_comp : ∀ {i j k : D.I} (hij : D.incl i j) (hjk : D.incl j k) (s : sections i),
    restrict (D.incl_trans hij hjk) s = restrict hjk (restrict hij s)
  locality : ∀ (i : D.I) (s : sections i),
    (∀ j, ∀ h : D.incl i j, restrict h s = letI := instAddCommGroup j; 0) →
    s = letI := instAddCommGroup i; 0
  gluing : ∀ {i : D.I} (cover : D.I → Prop)
    (hcover : ∀ j, cover j → D.incl i j)
    (sec : ∀ j, cover j → sections j),
    (∀ (j : D.I) (hj : cover j) (l : D.I) (hl : cover l)
      (m : D.I) (hjm : D.incl j m) (hlm : D.incl l m),
      restrict hjm (sec j hj) = restrict hlm (sec l hl)) →
    ∃ s : sections i, ∀ j (hj : cover j), restrict (hcover j hj) s = sec j hj
  quasicoherent : ∀ {i j} (h : D.incl i j) (s : sections j),
    ∃ (n : ℕ) (fs : Fin n → D.coordRing j) (gs : Fin n → sections i),
    s = letI := instAddCommGroup j
        letI := instModule j
        letI := D.instCommRing j
        letI := D.instDiffRing j
        letI := D.instDiffAlgebra j
        Finset.sum Finset.univ fun t =>
          (algebraMap (D.coordRing j) (D.diffOpsRing j) (fs t)) • restrict h (gs t)
  quasicoherent_iso : ∀ {i j} (h : D.incl i j),
    letI := D.baseChangeAddCommGroup h (sections i) (instAddCommGroup i) (instModule i)
    letI := instAddCommGroup j
    Nonempty ((D.baseChangeType h (sections i) (instAddCommGroup i) (instModule i)) ≃+ sections j)

structure RightDModuleSheaf (k : Type u) [CommRing k] (D : SheafOfDiffOps.{u, v, w} k) where
  sections : D.I → Type w
  instAddCommGroup : ∀ i, AddCommGroup (sections i)
  instModule : ∀ i, letI := D.instDiffRing i
    @Module (D.diffOpsRing i)ᵐᵒᵖ (sections i) (inferInstance : Semiring _)
      (instAddCommGroup i).toAddCommMonoid
  restrict : ∀ {i j}, D.incl i j → sections i → sections j
  restrict_add : ∀ {i j} (h : D.incl i j) (s t : sections i),
    restrict h (letI := instAddCommGroup i; s + t) =
    letI := instAddCommGroup j; restrict h s + restrict h t
  restrict_smul : ∀ {i j} (h : D.incl i j) (d : (D.diffOpsRing i)ᵐᵒᵖ) (s : sections i),
    restrict h (letI := D.instDiffRing i; letI := instModule i; d • s) =
    letI := D.instDiffRing j; letI := instModule j;
    MulOpposite.op (D.diffOpsRestrict h (MulOpposite.unop d)) • restrict h s
  restrict_id : ∀ (i : D.I) (s : sections i), restrict (D.incl_refl i) s = s
  restrict_comp : ∀ {i j k : D.I} (hij : D.incl i j) (hjk : D.incl j k) (s : sections i),
    restrict (D.incl_trans hij hjk) s = restrict hjk (restrict hij s)
  locality : ∀ (i : D.I) (s : sections i),
    (∀ j, ∀ h : D.incl i j, restrict h s = letI := instAddCommGroup j; 0) →
    s = letI := instAddCommGroup i; 0
  gluing : ∀ {i : D.I} (cover : D.I → Prop)
    (hcover : ∀ j, cover j → D.incl i j)
    (sec : ∀ j, cover j → sections j),
    (∀ (j : D.I) (hj : cover j) (l : D.I) (hl : cover l)
      (m : D.I) (hjm : D.incl j m) (hlm : D.incl l m),
      restrict hjm (sec j hj) = restrict hlm (sec l hl)) →
    ∃ s : sections i, ∀ j (hj : cover j), restrict (hcover j hj) s = sec j hj
  quasicoherent : ∀ {i j} (h : D.incl i j) (s : sections j),
    ∃ (n : ℕ) (fs : Fin n → D.coordRing j) (gs : Fin n → sections i),
    s = letI := instAddCommGroup j
        letI := D.instDiffRing j
        letI := instModule j
        letI := D.instCommRing j
        letI := D.instDiffAlgebra j
        Finset.sum Finset.univ fun t =>
          MulOpposite.op (algebraMap (D.coordRing j) (D.diffOpsRing j) (fs t)) • restrict h (gs t)

end DModulesSheaf

section Connections

structure Connection (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  nabla : M →ₗ[k] (TensorProduct A M (KaehlerDifferential k A))
  leibniz : ∀ (f : A) (m : M), nabla (f • m) =
    f • nabla m + TensorProduct.mk A M (KaehlerDifferential k A) m (KaehlerDifferential.D k A f)

noncomputable def covariantDerivative {k : Type u} [CommRing k] {A : Type v} [CommRing A]
    [Algebra k A] {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M]
    (v : Derivation k A A) (conn : Connection k A M) : M →ₗ[k] M :=
  ((TensorProduct.rid A M).toLinearMap ∘ₗ
    (LinearMap.lTensor M v.liftKaehlerDifferential)).restrictScalars k ∘ₗ conn.nabla

noncomputable def curvature {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (conn : Connection k A M) (v w : Derivation k A A) : M →ₗ[k] M :=
  (covariantDerivative v conn) ∘ₗ (covariantDerivative w conn) -
  (covariantDerivative w conn) ∘ₗ (covariantDerivative v conn) -
  covariantDerivative ⁅v, w⁆ conn

def Connection.IsFlat {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (conn : Connection k A M) : Prop :=
  ∀ v w : Derivation k A A, curvature conn v w = 0

end Connections

section Prop289

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

lemma liftKaehlerDifferential_smul (f : A) (v : Derivation k A A) :
    (f • v).liftKaehlerDifferential = f • v.liftKaehlerDifferential := by
  apply Derivation.liftKaehlerDifferential_unique
  ext g
  simp [Derivation.liftKaehlerDifferential_comp_D, LinearMap.compDer]

noncomputable def LeftDModule.ofFlatConnection (conn : Connection k A M)
    (hflat : conn.IsFlat) : LeftDModule k A M where
  vecFieldAction v := covariantDerivative v conn
  vecFieldAction_smul v f m := by
    simp only [covariantDerivative, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [conn.leibniz f m]
    simp [map_add, map_smul, TensorProduct.mk_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, Derivation.liftKaehlerDifferential_comp_D]
  vecFieldAction_smul_vec f v m := by
    simp only [covariantDerivative, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [liftKaehlerDifferential_smul, LinearMap.lTensor_smul, LinearMap.smul_apply,
      LinearMap.map_smul]
  vecFieldAction_lie v w m := by
    have h := hflat v w
    have key := LinearMap.ext_iff.mp h m
    simp only [curvature, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] at key
    exact sub_eq_zero.mp key





end Prop289

section DirectInverseImage

noncomputable abbrev TransferBimodule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (DY : Type w) [AddCommGroup DY] [Module OY DY] :
    Type (max v w) :=
  TensorProduct OY OX DY

noncomputable abbrev inverseImageModule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (N : Type w) [AddCommGroup N] [Module OY N] :
    Type (max v w) :=
  TensorProduct OY OX N

noncomputable abbrev directImageModule
    (OY : Type u) [CommRing OY]
    (OX : Type v) [CommRing OX] [Algebra OY OX]
    (DY : Type w) [AddCommGroup DY] [Module OY DY]
    (M : Type x) [AddCommGroup M] [Module OX M] :
    Type (max x v w) :=
  TensorProduct OX M (TransferBimodule OY OX DY)

end DirectInverseImage

end DModules
