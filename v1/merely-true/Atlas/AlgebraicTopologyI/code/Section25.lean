/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Atlas.AlgebraicTopologyI.code.EilenbergZilber

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace TensorChainComplex

variable (R : Type) [CommRing R]

/-- The tensor product of two chain complexes of $R$-modules, with the Leibniz
differential
$d(x \otimes y) = dx \otimes y + (-1)^{|x|} x \otimes dy$.
This is the algebraic side of the Künneth formula. -/
def tensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj C D

/-- The canonical inclusion of the bidegree $(p,q)$ summand $C_p \otimes D_q$ into the
total complex $(C \otimes D)_n$ for $p + q = n$. -/
def ιTensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ)
    (p q n : ℕ) (h : p + q = n) :
    (C.X p ⊗ D.X q) ⟶ (tensorChainComplex R C D).X n :=
  HomologicalComplex.ιTensorObj C D p q n h

/-- The index set of pairs $(p, q)$ of nonnegative integers with $p + q = n$, used to
index the bidegree summands of the total complex of a tensor product. -/
abbrev PairSum (n : ℕ) := { pq : ℕ × ℕ // pq.1 + pq.2 = n }

variable [IsPrincipalIdealRing R]

set_option linter.unusedSectionVars false in
/-- Every $R$-module $M$ admits a projective (in particular free) resolution; this is the
existence input needed to define $\mathrm{Tor}$. -/
theorem moduleCat_free_resolution (M : ModuleCat.{0} R) :
    Nonempty (ProjectiveResolution M) :=
  HasProjectiveResolution.out






end TensorChainComplex

namespace FreeResolutions

open CategoryTheory

/-- The category $\mathrm{ModuleCat}\,R$ of $R$-modules has projective resolutions; an
instance reused throughout the Tor / UCT / Künneth development. -/
instance moduleCat_hasProjectiveResolutions (R : Type) [Ring R] :
    HasProjectiveResolutions (ModuleCat.{0} R) := inferInstance

end FreeResolutions

namespace AcyclicModels

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **Definition 25.7 ($\mathcal{M}$-epi)**. A natural transformation $\eta : F \to G$
between functors $\mathcal{C} \to \mathrm{Ab}$ is $\mathcal{M}$-epi if its component
$\eta_M : F(M) \to G(M)$ is surjective for every $M$ in the family of models
$\mathcal{M} \subseteq \mathcal{C}$. -/
def IsMEpi (𝓜 : Set 𝒞) {F G : 𝒞 ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) : Prop :=
  ∀ M ∈ 𝓜, Function.Surjective (η.app M)

/-- **Definition 25.7 ($\mathcal{M}$-exact)**. A sequence
$G' \xrightarrow{\eta} G \xrightarrow{\psi} G''$ of functors $\mathcal{C} \to \mathrm{Ab}$
is $\mathcal{M}$-exact if, on every model $M \in \mathcal{M}$, the composite is zero and
the image of $\eta_M$ equals the kernel of $\psi_M$. -/
def IsMExact (𝓜 : Set 𝒞) {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}}
    (η : G' ⟶ G) (ψ : G ⟶ G'') : Prop :=
  ∀ M ∈ 𝓜, (∀ y : G'.obj M, ψ.app M (η.app M y) = 0) ∧
            (∀ x : G.obj M, ψ.app M x = 0 → ∃ y : G'.obj M, η.app M y = x)

/-- The free-abelian-coyoneda functor at a model $M$: the composite of $\mathrm{Hom}(M, -)$
with the free abelian group functor, sending $X$ to $\mathbb{Z}\langle \mathrm{Hom}(M, X) \rangle$.
This is the basic building block of an $\mathcal{M}$-free functor. -/
def freeAbelianCoyoneda (M : 𝒞) : 𝒞 ⥤ AddCommGrpCat.{v} :=
  coyoneda.obj (Opposite.op M) ⋙ AddCommGrpCat.free

/-- **Definition 25.4 ($\mathcal{M}$-free)**. A functor $F : \mathcal{C} \to \mathrm{Ab}$
is $\mathcal{M}$-free if it is naturally isomorphic to a direct sum of free-abelian-coyoneda
functors indexed by some family of models in $\mathcal{M}$. Such functors lift against
$\mathcal{M}$-epis. -/
@[simp]
def IsMFree (𝓜 : Set 𝒞) (F : 𝒞 ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (ι : Type v) (models : ι → 𝒞),
    (∀ i, models i ∈ 𝓜) ∧
    Nonempty (F ≅ ∐ (fun i => freeAbelianCoyoneda (models i)))

/-- The natural transformation $\mathbb{Z}\langle \mathrm{Hom}(M, -) \rangle \to G'$
classified by an element $c \in G'(M)$: it sends a morphism $\varphi : M \to X$ to
$G'(\varphi)(c)$. This is the universal property of the free-abelian-coyoneda functor. -/
def liftNatTrans {M : 𝒞} {G' : 𝒞 ⥤ AddCommGrpCat.{v}} (c : G'.obj M) :
    freeAbelianCoyoneda M ⟶ G' where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun φ => (ConcreteCategory.hom (G'.map φ)) c))
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
    dsimp [freeAbelianCoyoneda]
    erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    change (ConcreteCategory.hom (G'.map ((yoneda.map g).app (Opposite.op M) φ))) c =
      (ConcreteCategory.hom (G'.map g)) ((ConcreteCategory.hom (G'.map φ)) c)
    simp only [yoneda_map_app]; rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

/-- The free-abelian-coyoneda functor sends $\mathrm{id}_M$ to the generator
$\mathrm{id}_M \in \mathbb{Z}\langle \mathrm{Hom}(M, M) \rangle$, and sends $\varphi$
applied to this generator to $\varphi \in \mathbb{Z}\langle \mathrm{Hom}(M, X) \rangle$. -/
lemma freeAbelianCoyoneda_map_of_id {M X : 𝒞} (φ : M ⟶ X) :
    (ConcreteCategory.hom ((freeAbelianCoyoneda M).map φ)) (FreeAbelianGroup.of (𝟙 M)) =
    FreeAbelianGroup.of φ := by
  show (ConcreteCategory.hom (AddCommGrpCat.free.map ((coyoneda.obj (Opposite.op M)).map φ)))
    (FreeAbelianGroup.of (𝟙 M)) = _
  rw [AddCommGrpCat.free_map_coe]
  change FreeAbelianGroup.map ((coyoneda.obj (Opposite.op M)).map φ)
    (FreeAbelianGroup.of (𝟙 M)) = _
  rw [FreeAbelianGroup.map_of_apply]; simp [coyoneda]

/-- Lifting property of free-abelian-coyoneda functors: any natural transformation
$f : \mathbb{Z}\langle \mathrm{Hom}(M, -)\rangle \to G$ lifts through an $\mathcal{M}$-epi
$\eta : G' \to G$, provided $M \in \mathcal{M}$. -/
theorem freeAbelianCoyoneda_hasLiftingProperty
    {𝓜 : Set 𝒞} {M : 𝒞} (hM : M ∈ 𝓜)
    {G G' : 𝒞 ⥤ AddCommGrpCat.{v}} (η : G' ⟶ G) (hη : IsMEpi 𝓜 η)
    (f : freeAbelianCoyoneda M ⟶ G) :
    ∃ f' : freeAbelianCoyoneda M ⟶ G', f = f' ≫ η := by
  obtain ⟨c, hc⟩ := hη M hM ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M)))
  use liftNatTrans c
  ext X : 2; apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
  simp only [NatTrans.comp_app]; dsimp [liftNatTrans]
  erw [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of]
  have hf_nat : (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
      (ConcreteCategory.hom (G.map φ))
        ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) (FreeAbelianGroup.of (𝟙 M)))
      (f.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this
    rw [freeAbelianCoyoneda_map_of_id] at this; exact this
  have hη_nat : (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c) =
      (ConcreteCategory.hom (G.map φ)) ((ConcreteCategory.hom (η.app M)) c) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) c) (η.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this; exact this
  show (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c)
  rw [hf_nat, hη_nat, hc]

/-- Lifting property of $\mathcal{M}$-free functors: any natural transformation
$f : F \to G$ from an $\mathcal{M}$-free $F$ lifts through an $\mathcal{M}$-epi
$\eta : G' \to G$. Generalises `freeAbelianCoyoneda_hasLiftingProperty` to arbitrary
direct sums of corepresentables. -/
theorem isMFree_hasLiftingProperty {𝓜 : Set 𝒞} {F : 𝒞 ⥤ AddCommGrpCat.{v}}
    (hF : IsMFree 𝓜 F) {G G' : 𝒞 ⥤ AddCommGrpCat.{v}} (η : G' ⟶ G) (hη : IsMEpi 𝓜 η)
    (f : F ⟶ G) : ∃ f' : F ⟶ G', f = f' ≫ η := by
  obtain ⟨ι, models, hmodels, ⟨e⟩⟩ := hF
  have hlift : ∀ i, ∃ f'_i : freeAbelianCoyoneda (models i) ⟶ G',
      Sigma.ι (fun i => freeAbelianCoyoneda (models i)) i ≫ e.inv ≫ f = f'_i ≫ η :=
    fun i => freeAbelianCoyoneda_hasLiftingProperty (hmodels i) η hη _
  choose f'_i hf'_i using hlift
  use e.hom ≫ Limits.Sigma.desc f'_i
  rw [Category.assoc]
  have hdesc_comp : Limits.Sigma.desc f'_i ≫ η =
      Limits.Sigma.desc (fun i => f'_i i ≫ η) := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [hdesc_comp]
  have hsubst : (fun i => f'_i i ≫ η) = (fun i => Sigma.ι _ i ≫ e.inv ≫ f) :=
    funext (fun i => (hf'_i i).symm)
  rw [hsubst]
  have hdesc_inv : Limits.Sigma.desc
      (fun i => Sigma.ι _ i ≫ (e.inv ≫ f)) = e.inv ≫ f := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc]
  rw [hdesc_inv, Iso.hom_inv_id_assoc]

/-- Exact-sequence version of the lifting property for free-abelian-coyoneda functors: in
an $\mathcal{M}$-exact sequence $G' \xrightarrow{\eta} G \xrightarrow{\psi} G''$, any
natural transformation $f : \mathbb{Z}\langle \mathrm{Hom}(M, -) \rangle \to G$ killed by
$\psi$ factors through $\eta$. -/
theorem freeAbelianCoyoneda_hasLiftingProperty_exact
    {𝓜 : Set 𝒞} {M : 𝒞} (hM : M ∈ 𝓜)
    {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}} (η : G' ⟶ G) (ψ : G ⟶ G'')
    (hExact : IsMExact 𝓜 η ψ)
    (f : freeAbelianCoyoneda M ⟶ G) (hf : f ≫ ψ = 0) :
    ∃ f' : freeAbelianCoyoneda M ⟶ G', f = f' ≫ η := by
  have hfM_ker : (ConcreteCategory.hom (ψ.app M))
      ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) = 0 := by
    have := congr_arg (fun h => (ConcreteCategory.hom (h.app M)) (FreeAbelianGroup.of (𝟙 M))) hf
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
    simpa using this
  obtain ⟨_, hsurj⟩ := hExact M hM
  obtain ⟨c, hc⟩ := hsurj _ hfM_ker
  use liftNatTrans c
  ext X : 2; apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
  simp only [NatTrans.comp_app]; dsimp [liftNatTrans]
  erw [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of]
  have hf_nat : (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
      (ConcreteCategory.hom (G.map φ))
        ((ConcreteCategory.hom (f.app M)) (FreeAbelianGroup.of (𝟙 M))) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) (FreeAbelianGroup.of (𝟙 M)))
      (f.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this
    rw [freeAbelianCoyoneda_map_of_id] at this; exact this
  have hη_nat : (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c) =
      (ConcreteCategory.hom (G.map φ)) ((ConcreteCategory.hom (η.app M)) c) := by
    have := congr_arg (fun h => (ConcreteCategory.hom h) c) (η.naturality φ)
    simp only [ConcreteCategory.comp_apply] at this; exact this
  show (ConcreteCategory.hom (f.app X)) (FreeAbelianGroup.of φ) =
    (ConcreteCategory.hom (η.app X)) ((ConcreteCategory.hom (G'.map φ)) c)
  rw [hf_nat, hη_nat, hc]

/-- Exact-sequence lifting property for $\mathcal{M}$-free functors: any natural
transformation $f : F \to G$ from an $\mathcal{M}$-free $F$ that is killed by $\psi$
factors through $\eta$, given $\eta, \psi$ form an $\mathcal{M}$-exact sequence. -/
theorem isMFree_hasLiftingProperty_exact {𝓜 : Set 𝒞} {F : 𝒞 ⥤ AddCommGrpCat.{v}}
    (hF : IsMFree 𝓜 F) {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}} (η : G' ⟶ G) (ψ : G ⟶ G'')
    (hExact : IsMExact 𝓜 η ψ)
    (f : F ⟶ G) (hf : f ≫ ψ = 0) : ∃ f' : F ⟶ G', f = f' ≫ η := by
  obtain ⟨ι, models, hmodels, ⟨e⟩⟩ := hF
  have hlift : ∀ i, ∃ f'_i : freeAbelianCoyoneda (models i) ⟶ G',
      Sigma.ι (fun i => freeAbelianCoyoneda (models i)) i ≫ e.inv ≫ f =
        f'_i ≫ η := by
    intro i
    apply freeAbelianCoyoneda_hasLiftingProperty_exact (hmodels i) η ψ hExact
    simp only [Category.assoc, hf, comp_zero]
  choose f'_i hf'_i using hlift
  use e.hom ≫ Limits.Sigma.desc f'_i
  rw [Category.assoc]
  have hdesc_comp : Limits.Sigma.desc f'_i ≫ η =
      Limits.Sigma.desc (fun i => f'_i i ≫ η) := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [hdesc_comp]
  have hsubst : (fun i => f'_i i ≫ η) = (fun i => Sigma.ι _ i ≫ e.inv ≫ f) :=
    funext (fun i => (hf'_i i).symm)
  rw [hsubst]
  have hdesc_inv : Limits.Sigma.desc
      (fun i => Sigma.ι _ i ≫ (e.inv ≫ f)) = e.inv ≫ f := by
    apply Sigma.hom_ext; intro i; simp [Sigma.ι_desc]
  rw [hdesc_inv, Iso.hom_inv_id_assoc]

/-- An augmented chain-complex-valued functor: a functor $\mathcal{C} \to \mathrm{Ch}_*$
together with an augmentation $F_0 \to T$ to a target functor $T : \mathcal{C} \to \mathrm{Ab}$.
This is the input data on which the acyclic models theorem operates. -/
structure AugChainComplexFunctor (𝒞 : Type u) [Category.{v} 𝒞] where
  chainFun : 𝒞 ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ)
  target : 𝒞 ⥤ AddCommGrpCat.{v}
  augmentation :
    chainFun ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.down ℕ) 0 ⟶ target

/-- The degree-$n$ component of an augmented chain-complex functor as a functor
$\mathcal{C} \to \mathrm{Ab}$, obtained by composing with the evaluation functor at $n$. -/
def AugChainComplexFunctor.componentFun (F : AugChainComplexFunctor 𝒞) (n : ℕ) :
    𝒞 ⥤ AddCommGrpCat.{v} :=
  F.chainFun ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.down ℕ) n

/-- An augmented chain-complex functor is $\mathcal{M}$-exact (acyclic on models) if on
each model $M \in \mathcal{M}$ the augmented chain complex is exact: higher exactness in
positive degrees, surjectivity of the augmentation, and exactness at degree 0. This is
the acyclicity hypothesis in the acyclic models theorem. -/
def IsMExactAugmented (𝓜 : Set 𝒞) (F : AugChainComplexFunctor 𝒞) : Prop :=
  ∀ M ∈ 𝓜,
    (∀ n : ℕ, (F.chainFun.obj M).ExactAt (n + 1)) ∧
    Function.Surjective (F.augmentation.app M) ∧
    (F.chainFun.obj M).d 1 0 ≫ F.augmentation.app M = 0 ∧
    (∀ x : (F.chainFun.obj M).X 0, F.augmentation.app M x = 0 →
      ∃ y : (F.chainFun.obj M).X 1, (F.chainFun.obj M).d 1 0 y = x)

/-- The natural transformation $F_i \Rightarrow F_j$ induced by the differential
$d_{ij}$ of the underlying chain complex, viewed in the functor category. -/
def AugChainComplexFunctor.dNat (F : AugChainComplexFunctor 𝒞) (i j : ℕ) :
    F.componentFun i ⟶ F.componentFun j where
  app X := (F.chainFun.obj X).d i j
  naturality X Y f := by
    simp only [componentFun, Functor.comp_map, HomologicalComplex.eval_map]
    exact (F.chainFun.map f).comm i j

/-- The augmentation of an $\mathcal{M}$-exact augmented chain-complex functor is an
$\mathcal{M}$-epi: extraction of the surjectivity clause from `IsMExactAugmented`. -/
theorem IsMExactAugmented.augmentation_isMEpi {𝓜 : Set 𝒞} {G : AugChainComplexFunctor 𝒞}
    (hG : IsMExactAugmented 𝓜 G) :
    IsMEpi 𝓜 G.augmentation := by
  intro M hM
  exact (hG M hM).2.1

/-- Consecutive differentials of an $\mathcal{M}$-exact augmented functor form an
$\mathcal{M}$-exact pair in positive degrees: extraction of the higher-exactness clause. -/
theorem IsMExactAugmented.dNat_isMExact {𝓜 : Set 𝒞} {G : AugChainComplexFunctor 𝒞}
    (hG : IsMExactAugmented 𝓜 G) (n : ℕ) :
    IsMExact 𝓜 (G.dNat (n + 2) (n + 1)) (G.dNat (n + 1) n) := by
  intro M hM
  obtain ⟨hexact, _, _⟩ := hG M hM
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  ·
    show ((G.chainFun.obj M).d (n + 1) n) ((G.chainFun.obj M).d (n + 2) (n + 1) y) = 0
    rw [← CategoryTheory.comp_apply
        ((G.chainFun.obj M).d (n + 2) (n + 1))
        ((G.chainFun.obj M).d (n + 1) n) y,
        (G.chainFun.obj M).d_comp_d (n + 2) (n + 1) n]
    simp
  ·
    have hexact_at := hexact n
    rw [HomologicalComplex.exactAt_iff' (G.chainFun.obj M)
      (n + 2) (n + 1) n
      (ChainComplex.prev ℕ (n + 1))
      (ChainComplex.next_nat_succ n)] at hexact_at
    rw [ShortComplex.ab_exact_iff] at hexact_at
    exact hexact_at x hx

/-- The differential $d_{1,0}$ and the augmentation form an $\mathcal{M}$-exact pair: the
zero-degree exactness clause of `IsMExactAugmented`. -/
theorem IsMExactAugmented.augmentation_dNat_isMExact {𝓜 : Set 𝒞} {G : AugChainComplexFunctor 𝒞}
    (hG : IsMExactAugmented 𝓜 G) :
    IsMExact 𝓜 (G.dNat 1 0) G.augmentation := by
  intro M hM
  obtain ⟨_, _, hcomp, hexact0⟩ := hG M hM
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  ·
    show G.augmentation.app M ((G.chainFun.obj M).d 1 0 y) = 0
    have h := CategoryTheory.comp_apply ((G.chainFun.obj M).d 1 0) (G.augmentation.app M) y
    rw [hcomp] at h
    simp at h
    exact h.symm
  ·
    exact hexact0 x hx

/-- The covering condition: a chain map $\varphi : F \to G$ between augmented
chain-complex functors covers a natural transformation $\theta : F_{\mathrm{aug}} \to G_{\mathrm{aug}}$
of targets iff the obvious square commutes on every object $X$. -/
def Covers (F G : AugChainComplexFunctor 𝒞)
    (φ : F.chainFun ⟶ G.chainFun) (θ : F.target ⟶ G.target) : Prop :=
  ∀ X : 𝒞, (φ.app X).f 0 ≫ G.augmentation.app X = F.augmentation.app X ≫ θ.app X

/-- A natural transformation between functors valued in chain complexes is a natural
chain-homotopy equivalence if there is a natural inverse and, on every object, the pair
$(\varphi_X, \psi_X)$ assembles into a `HomotopyEquiv`. -/
def IsNatChainHomotopyEquiv
    {F_star G_star : 𝒞 ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ)}
    (φ : F_star ⟶ G_star) : Prop :=
  ∃ ψ : G_star ⟶ F_star, ∀ X : 𝒞,
    ∃ e : HomotopyEquiv (F_star.obj X) (G_star.obj X),
      e.hom = φ.app X ∧ e.inv = ψ.app X

/-- Two natural transformations of chain-complex functors are objectwise chain homotopic
if, for every $X \in \mathcal{C}$, the components $\Phi_X$ and $\Psi_X$ are chain
homotopic as ordinary chain maps. -/
def ObjectwiseHomotopic
    {F G : AugChainComplexFunctor 𝒞}
    (Φ Ψ : F.chainFun ⟶ G.chainFun) : Prop :=
  ∀ X : 𝒞, Nonempty (Homotopy (Φ.app X) (Ψ.app X))

/-- The shape of homotopy data used in the acyclic models uniqueness proof: a family of
natural transformations $s_n : F_n \to G_{n+1}$, evaluated at $X$ and re-indexed to match
the `ComplexShape.down ℕ` relation. -/
noncomputable def natTransHomotopyData
    {F G : AugChainComplexFunctor 𝒞}
    (s : ∀ n : ℕ, F.componentFun n ⟶ G.componentFun (n + 1))
    (X : 𝒞) :
    (i j : ℕ) → (ComplexShape.down ℕ).Rel j i →
      ((F.chainFun.obj X).X i ⟶ (G.chainFun.obj X).X j) :=
  fun i j (hij : i + 1 = j) => hij ▸ ((s i).app X)

/-- The objectwise chain homotopy between $\Phi_1$ and $\Phi_2$ associated to a family of
natural transformations $s_n : F_n \to G_{n+1}$ satisfying the chain-homotopy identity
$\Phi_1 - \Phi_2 = d \circ s + s \circ d$ as a null-homotopic map. -/
noncomputable def natTransHomotopy
    {F G : AugChainComplexFunctor 𝒞}
    (Φ₁ Φ₂ : F.chainFun ⟶ G.chainFun)
    (s : ∀ n : ℕ, F.componentFun n ⟶ G.componentFun (n + 1))
    (heq : ∀ X : 𝒞,
      Φ₁.app X - Φ₂.app X = Homotopy.nullHomotopicMap' (natTransHomotopyData s X))
    (X : 𝒞) : Homotopy (Φ₁.app X) (Φ₂.app X) :=
  Homotopy.equivSubZero.symm (by
    rw [heq]
    exact Homotopy.nullHomotopy' (natTransHomotopyData s X))



end AcyclicModels

open AcyclicModels CategoryTheory in
/-- **Acyclic Models — existence**. Given an $\mathcal{M}$-free augmented chain functor
$F$ and an $\mathcal{M}$-exact augmented chain functor $G$, any natural transformation
$\theta$ between their targets is covered by a chain map $F \to G$. The proof builds the
chain map degree-by-degree using the lifting properties of $\mathcal{M}$-free functors. -/
theorem AcyclicModels.acyclic_models_existence
    {𝒞 : Type u} [Category.{v} 𝒞]
    (𝓜 : Set 𝒞)
    (F_aug G_aug : AugChainComplexFunctor 𝒞)
    (θ : F_aug.target ⟶ G_aug.target)
    (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
    (hG_exact : IsMExactAugmented 𝓜 G_aug)
    (hF_d_aug : F_aug.dNat 1 0 ≫ F_aug.augmentation = 0) :
    ∃ Φ : F_aug.chainFun ⟶ G_aug.chainFun, Covers F_aug G_aug Φ θ := by

  obtain ⟨φ₀, hφ₀⟩ := isMFree_hasLiftingProperty (hF_free 0)
    G_aug.augmentation (hG_exact.augmentation_isMEpi) (F_aug.augmentation ≫ θ)

  have hzero1 : (F_aug.dNat 1 0 ≫ φ₀) ≫ G_aug.augmentation = 0 := by
    rw [Category.assoc, ← hφ₀, ← Category.assoc, hF_d_aug, zero_comp]
  obtain ⟨φ₁, hφ₁⟩ := isMFree_hasLiftingProperty_exact (hF_free 1)
    (G_aug.dNat 1 0) G_aug.augmentation
    hG_exact.augmentation_dNat_isMExact
    (F_aug.dNat 1 0 ≫ φ₀) hzero1

  have ind_step : ∀ (n : ℕ)
    (φ_n : F_aug.componentFun n ⟶ G_aug.componentFun n)
    (φ_np1 : F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 1))
    (_ : F_aug.dNat (n + 1) n ≫ φ_n = φ_np1 ≫ G_aug.dNat (n + 1) n),
    ∃ (φ_np2 : F_aug.componentFun (n + 2) ⟶ G_aug.componentFun (n + 2)),
      F_aug.dNat (n + 2) (n + 1) ≫ φ_np1 = φ_np2 ≫ G_aug.dNat (n + 2) (n + 1) := by
    intro n φ_n φ_np1 hchain
    have hzero : (F_aug.dNat (n + 2) (n + 1) ≫ φ_np1) ≫ G_aug.dNat (n + 1) n = 0 := by
      rw [Category.assoc, ← hchain, ← Category.assoc]
      have hdd : F_aug.dNat (n + 2) (n + 1) ≫ F_aug.dNat (n + 1) n = 0 := by
        ext X : 2
        simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat]
        exact (F_aug.chainFun.obj X).d_comp_d (n + 2) (n + 1) n
      rw [hdd, zero_comp]
    exact isMFree_hasLiftingProperty_exact (hF_free (n + 2))
      (G_aug.dNat (n + 2) (n + 1)) (G_aug.dNat (n + 1) n)
      (hG_exact.dNat_isMExact n)
      (F_aug.dNat (n + 2) (n + 1) ≫ φ_np1) hzero

  let ChainPair (n : ℕ) := { p : (F_aug.componentFun n ⟶ G_aug.componentFun n) ×
    (F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 1)) //
    F_aug.dNat (n + 1) n ≫ p.1 = p.2 ≫ G_aug.dNat (n + 1) n }
  let advance : (n : ℕ) → ChainPair n → ChainPair (n + 1) := fun n ⟨(φn, φnp1), hc⟩ =>
    ⟨(φnp1, (ind_step n φn φnp1 hc).choose), (ind_step n φn φnp1 hc).choose_spec⟩
  let base : ChainPair 0 := ⟨(φ₀, φ₁), hφ₁⟩
  let seq : (n : ℕ) → ChainPair n := fun n => Nat.rec base (fun k ih => advance k ih) n

  let φ : (n : ℕ) → (F_aug.componentFun n ⟶ G_aug.componentFun n) := fun n => (seq n).val.1

  have hshift : ∀ n, (seq (n + 1)).val.1 = (seq n).val.2 := fun n => rfl
  have hcomm : ∀ n, F_aug.dNat (n + 1) n ≫ φ n = φ (n + 1) ≫ G_aug.dNat (n + 1) n := by
    intro n
    show F_aug.dNat (n + 1) n ≫ (seq n).val.1 = (seq (n + 1)).val.1 ≫ G_aug.dNat (n + 1) n
    rw [hshift n]
    exact (seq n).property

  refine ⟨?_, ?_⟩
  · exact {
      app := fun X => {
        f := fun n => (φ n).app X
        comm' := fun i j (hij : (ComplexShape.down ℕ).Rel i j) => by
          rw [ComplexShape.down_Rel] at hij
          subst hij
          have := congr_arg (fun α => NatTrans.app α X) (hcomm j)
          simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat] at this
          exact this.symm
      }
      naturality := fun X Y f => by
        ext n : 2
        simp only [HomologicalComplex.comp_f,
          AugChainComplexFunctor.componentFun]
        exact congr_arg AddCommGrpCat.Hom.hom ((φ n).naturality f)
    }
  ·
    intro X
    show (φ 0).app X ≫ G_aug.augmentation.app X = F_aug.augmentation.app X ≫ θ.app X
    have h0 : φ 0 = φ₀ := rfl
    rw [h0]
    have := congr_arg (fun α => NatTrans.app α X) hφ₀
    simp only [NatTrans.comp_app] at this
    exact this.symm

section
open AcyclicModels CategoryTheory

/-- **Acyclic Models — uniqueness**. Any two natural chain maps $F \to G$ covering the
same augmentation morphism are objectwise chain homotopic. The proof again proceeds by
induction, using the exact lifting property of $\mathcal{M}$-free functors to build the
chain homotopy degree-by-degree. -/
theorem AcyclicModels.acyclic_models_uniqueness
    {𝒞 : Type u} [Category.{v} 𝒞]
    (𝓜 : Set 𝒞)
    (F_aug G_aug : AugChainComplexFunctor 𝒞)
    (θ : F_aug.target ⟶ G_aug.target)
    (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
    (hG_exact : IsMExactAugmented 𝓜 G_aug)
    (Φ₁ Φ₂ : F_aug.chainFun ⟶ G_aug.chainFun)
    (hΦ₁ : Covers F_aug G_aug Φ₁ θ)
    (hΦ₂ : Covers F_aug G_aug Φ₂ θ) :
    ObjectwiseHomotopic Φ₁ Φ₂ := by

  let ℓ : ∀ n : ℕ, F_aug.componentFun n ⟶ G_aug.componentFun n := fun n =>
    { app := fun X => (Φ₁.app X).f n - (Φ₂.app X).f n
      naturality := fun X Y f => by
        simp only [AugChainComplexFunctor.componentFun, Functor.comp_map,
          HomologicalComplex.eval_map, Preadditive.comp_sub, Preadditive.sub_comp]
        have nat1 := congr_arg (fun α => HomologicalComplex.Hom.f α n) (Φ₁.naturality f)
        have nat2 := congr_arg (fun α => HomologicalComplex.Hom.f α n) (Φ₂.naturality f)
        simp only [HomologicalComplex.comp_f] at nat1 nat2
        exact show (F_aug.chainFun.map f).f n ≫ ((Φ₁.app Y).f n - (Φ₂.app Y).f n) =
          ((Φ₁.app X).f n - (Φ₂.app X).f n) ≫ (G_aug.chainFun.map f).f n from by
          rw [Preadditive.comp_sub, Preadditive.sub_comp, nat1, nat2] }

  have hℓ_chain : ∀ n, F_aug.dNat (n + 1) n ≫ ℓ n = ℓ (n + 1) ≫ G_aug.dNat (n + 1) n := by
    intro n
    ext X
    simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat, ℓ,
      AugChainComplexFunctor.componentFun, Functor.comp_obj, HomologicalComplex.eval_obj,
      Preadditive.comp_sub, Preadditive.sub_comp,
      (Φ₁.app X).comm' (n + 1) n rfl, (Φ₂.app X).comm' (n + 1) n rfl]

  have hℓ0_ker : ℓ 0 ≫ G_aug.augmentation = 0 := by
    ext X
    simp only [NatTrans.comp_app, ℓ, AugChainComplexFunctor.componentFun, Functor.comp_obj,
      HomologicalComplex.eval_obj, Preadditive.sub_comp, hΦ₁ X, hΦ₂ X, sub_self]
    rfl

  obtain ⟨s₀, hs₀⟩ := isMFree_hasLiftingProperty_exact (hF_free 0)
    (G_aug.dNat 1 0) G_aug.augmentation
    hG_exact.augmentation_dNat_isMExact
    (ℓ 0) hℓ0_ker

  have hzero1 : (ℓ 1 - F_aug.dNat 1 0 ≫ s₀) ≫ G_aug.dNat 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, ← hs₀, hℓ_chain 0, sub_self]
  obtain ⟨s₁, hs₁⟩ := isMFree_hasLiftingProperty_exact (hF_free 1)
    (G_aug.dNat 2 1) (G_aug.dNat 1 0)
    (hG_exact.dNat_isMExact 0)
    (ℓ 1 - F_aug.dNat 1 0 ≫ s₀) hzero1

  have advance_htpy : ∀ (n : ℕ)
    (s_n : F_aug.componentFun n ⟶ G_aug.componentFun (n + 1))
    (s_np1 : F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 2))
    (_ : ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s_n = s_np1 ≫ G_aug.dNat (n + 2) (n + 1)),
    ∃ (s_np2 : F_aug.componentFun (n + 2) ⟶ G_aug.componentFun (n + 3)),
      ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1 = s_np2 ≫ G_aug.dNat (n + 3) (n + 2) := by
    intro n s_n s_np1 hchain
    have hdd : F_aug.dNat (n + 2) (n + 1) ≫ F_aug.dNat (n + 1) n = 0 := by
      ext X : 2
      simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat]
      exact (F_aug.chainFun.obj X).d_comp_d (n + 2) (n + 1) n
    have hzero : (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) ≫
        G_aug.dNat (n + 2) (n + 1) = 0 := by
      have h1 : F_aug.dNat (n + 2) (n + 1) ≫ s_np1 ≫ G_aug.dNat (n + 2) (n + 1) =
          F_aug.dNat (n + 2) (n + 1) ≫ (ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s_n) := by
        congr 1; exact hchain.symm
      have key : (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) ≫ G_aug.dNat (n + 2) (n + 1) =
        ℓ (n + 2) ≫ G_aug.dNat (n + 2) (n + 1) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1 ≫
        G_aug.dNat (n + 2) (n + 1) := by rw [Preadditive.sub_comp, Category.assoc]
      rw [key, h1, Preadditive.comp_sub, ← Category.assoc, hdd, zero_comp, sub_zero,
        ← hℓ_chain (n + 1), sub_self]
    exact isMFree_hasLiftingProperty_exact (hF_free (n + 2))
      (G_aug.dNat (n + 3) (n + 2)) (G_aug.dNat (n + 2) (n + 1))
      (hG_exact.dNat_isMExact (n + 1))
      (ℓ (n + 2) - F_aug.dNat (n + 2) (n + 1) ≫ s_np1) hzero

  let HtpyPair (n : ℕ) := { p : (F_aug.componentFun n ⟶ G_aug.componentFun (n + 1)) ×
    (F_aug.componentFun (n + 1) ⟶ G_aug.componentFun (n + 2)) //
    ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ p.1 = p.2 ≫ G_aug.dNat (n + 2) (n + 1) }
  let advance : (n : ℕ) → HtpyPair n → HtpyPair (n + 1) := fun n ⟨(sn, snp1), hc⟩ =>
    ⟨(snp1, (advance_htpy n sn snp1 hc).choose), (advance_htpy n sn snp1 hc).choose_spec⟩
  let base : HtpyPair 0 := ⟨(s₀, s₁), hs₁⟩
  let seq : (n : ℕ) → HtpyPair n := fun n => Nat.rec base (fun k ih => advance k ih) n
  let s : (n : ℕ) → (F_aug.componentFun n ⟶ G_aug.componentFun (n + 1)) :=
    fun n => (seq n).val.1
  have hshift : ∀ n, (seq (n + 1)).val.1 = (seq n).val.2 := fun n => rfl
  have hhtpy_eq : ∀ n,
      ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ s n = s (n + 1) ≫ G_aug.dNat (n + 2) (n + 1) := by
    intro n
    show ℓ (n + 1) - F_aug.dNat (n + 1) n ≫ (seq n).val.1 =
      (seq (n + 1)).val.1 ≫ G_aug.dNat (n + 2) (n + 1)
    rw [hshift n]
    exact (seq n).property
  have hhtpy_base : ℓ 0 = s 0 ≫ G_aug.dNat 1 0 := hs₀

  have heq : ∀ X : 𝒞, Φ₁.app X - Φ₂.app X =
      Homotopy.nullHomotopicMap' (natTransHomotopyData s X) := by
    intro X
    ext n
    cases n with
    | zero =>
      have h0 := Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (k₁ := 1) (show (0 : ℕ) + 1 = 1 from rfl)
        (fun l (h : (ComplexShape.down ℕ).Rel 0 l) => by
          simp [ComplexShape.down_Rel] at h)
        (natTransHomotopyData s X)
      simp only [HomologicalComplex.sub_f_apply, h0, natTransHomotopyData]
      have h := congr_arg (fun α => NatTrans.app α X) hhtpy_base
      simp only [NatTrans.comp_app, AugChainComplexFunctor.dNat, ℓ,
        AugChainComplexFunctor.componentFun, Functor.comp_obj,
        HomologicalComplex.eval_obj] at h
      exact congrArg (fun g => AddCommGrpCat.Hom.hom g _) h
    | succ n =>
      have hn := Homotopy.nullHomotopicMap'_f
        (k₂ := n + 2) (k₀ := n)
        (show (n + 1 : ℕ) + 1 = n + 2 from rfl)
        (show n + 1 = n + 1 from rfl)
        (natTransHomotopyData s X)
      simp only [HomologicalComplex.sub_f_apply, hn, natTransHomotopyData]
      have heq_n := congr_arg (fun α => NatTrans.app α X) (hhtpy_eq n)
      simp only [NatTrans.comp_app, NatTrans.app_sub, AugChainComplexFunctor.dNat, ℓ,
        AugChainComplexFunctor.componentFun, Functor.comp_obj,
        HomologicalComplex.eval_obj] at heq_n
      have h := eq_add_of_sub_eq heq_n
      simp only [NatTrans.comp_app] at h
      conv at h => rhs; rw [add_comm]
      exact congrArg (fun g => AddCommGrpCat.Hom.hom g _) h

  intro X
  exact ⟨natTransHomotopy Φ₁ Φ₂ s heq X⟩
end

open AcyclicModels CategoryTheory in
/-- **Theorem 25.11 (Acyclic Models)**. Combining existence and uniqueness: for an
$\mathcal{M}$-free augmented functor $F$ and an $\mathcal{M}$-exact augmented functor $G$,
any natural transformation between their targets is covered by a chain map that is unique
up to objectwise chain homotopy. -/
theorem AcyclicModels.acyclic_models
    {𝒞 : Type u} [Category.{v} 𝒞]
    (𝓜 : Set 𝒞)
    (F_aug G_aug : AugChainComplexFunctor 𝒞)
    (θ : F_aug.target ⟶ G_aug.target)
    (hF_free : ∀ n : ℕ, IsMFree 𝓜 (F_aug.componentFun n))
    (hG_exact : IsMExactAugmented 𝓜 G_aug)
    (hF_d_aug : F_aug.dNat 1 0 ≫ F_aug.augmentation = 0) :
    (∃ Φ : F_aug.chainFun ⟶ G_aug.chainFun, Covers F_aug G_aug Φ θ) ∧
    (∀ Φ₁ Φ₂ : F_aug.chainFun ⟶ G_aug.chainFun,
      Covers F_aug G_aug Φ₁ θ → Covers F_aug G_aug Φ₂ θ →
      ObjectwiseHomotopic Φ₁ Φ₂) :=
  ⟨acyclic_models_existence 𝓜 F_aug G_aug θ hF_free hG_exact hF_d_aug,
   fun Φ₁ Φ₂ hΦ₁ hΦ₂ => acyclic_models_uniqueness 𝓜 F_aug G_aug θ hF_free hG_exact Φ₁ Φ₂ hΦ₁ hΦ₂⟩


namespace KunnethTopological

open AlgebraicTopology

variable (R : Type) [CommRing R]

/-- The $n$-th singular homology of a space $X$ with coefficients in the ring $R$
(viewed as the regular $R$-module), as an object of $\mathrm{ModuleCat}\,R$. -/
def singularHomologyMod (n : ℕ) (X : TopCat.{0}) : ModuleCat R :=
  ((singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).obj X

/-- The induced map on $n$-th singular homology with $R$ coefficients of a continuous map
$f : X \to Y$. -/
def singularHomologyModMap (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularHomologyMod R n X ⟶ singularHomologyMod R n Y :=
  ((singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).map f

/-- The tensor term in the topological Künneth short exact sequence: the direct sum
$\bigoplus_{p+q=n} H_p(X; R) \otimes_R H_q(Y; R)$. -/
def kunnethTensorTerm (n : ℕ) (X Y : TopCat.{0}) : ModuleCat R :=
  ∐ fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 = n }) =>
    singularHomologyMod R pq.1.1 X ⊗ singularHomologyMod R pq.1.2 Y

/-- The Tor term in the topological Künneth short exact sequence: the direct sum
$\bigoplus_{p+q=n-1} \mathrm{Tor}_1^R(H_p(X; R), H_q(Y; R))$. -/
def kunnethTorTerm (n : ℕ) (X Y : TopCat.{0}) : ModuleCat R :=
  ∐ fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 + 1 = n }) =>
    ((Tor (ModuleCat R) 1).obj (singularHomologyMod R pq.1.1 X)).obj
      (singularHomologyMod R pq.1.2 Y)











end KunnethTopological
