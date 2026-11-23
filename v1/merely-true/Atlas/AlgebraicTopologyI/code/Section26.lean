/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.CupProductHelpers
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

noncomputable section

namespace SingularCohomology

/-- **Definition 26.3**. A singular $n$-cochain on $X$ with values in an abelian group $N$ is
a function $\operatorname{Sin}_n(X) \to N$. -/
def SingularCochain (n : ℕ) (X : Type*) [TopologicalSpace X]
    (N : Type*) [AddCommGroup N] : Type _ :=
  SingularSimplex n X → N

/-- Pointwise addition makes singular $n$-cochains into an abelian group. -/
instance (n : ℕ) (X : Type*) [TopologicalSpace X]
    (N : Type*) [AddCommGroup N] : AddCommGroup (SingularCochain n X N) :=
  Pi.addCommGroup

/-- **Definition 26.5**. The $n$th singular cohomology
$H^n(X; G) = H^n(\operatorname{Hom}_R(S_*(X; R), G))$ of $X$ with coefficients in an
$R$-module $G$. -/
def singularCohomology (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) (n : ℕ) :
    ModuleCat R :=
  ((((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G).homology n

/-- The singular cochain complex $S^*(X; G) = \operatorname{Hom}_R(S_*(X; R), G)$, the
underlying cochain complex computing singular cohomology. -/
def singularCochainComplex (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) : CochainComplex (ModuleCat.{0} R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The restriction map of cochain complexes $S^*(X; G) \to S^*(A; G)$ induced by an inclusion
$A \hookrightarrow X$. -/
def restrictionCochainMap (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X A : TopCat.{0}} (i : A ⟶ X) :
    singularCochainComplex R X G ⟶ singularCochainComplex R A G :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map i)).op)

/-- **Definition 26.8**. The relative singular cochain complex
$S^n(X, A; N) = \ker(S^n(X; N) \to S^n(A; N))$. -/
def relativeSingularCochainComplex (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X A : TopCat.{0}} (i : A ⟶ X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  haveI : HasKernels (CochainComplex (ModuleCat.{0} R) ℕ) := inferInstance
  kernel (restrictionCochainMap R G i)

/-- **Definition 26.8** (cohomology version). Relative singular cohomology
$H^n(X, A; N) = H^n(S^*(X, A; N))$. -/
def relativeSingularCohomology (R : Type) [CommRing R]
    (X A : TopCat.{0}) (i : A ⟶ X) (G : ModuleCat.{0} R) (n : ℕ) :
    ModuleCat R :=
  haveI : HasKernels (CochainComplex (ModuleCat.{0} R) ℕ) := inferInstance
  (kernel (restrictionCochainMap R G i)).homology n

/-- The $n$th singular homology module $H_n(X; R)$, as an object of `ModuleCat R`. -/
abbrev singularHomologyModule (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).obj X

/-- The graded family of underlying types $n \mapsto H_n(X; R)$. -/
abbrev singularHomologyFamily (R : Type) [CommRing R]
    (X : TopCat.{0}) : ℕ → Type :=
  fun n => (singularHomologyModule R X n : Type)

/-- The total singular homology $H_*(X; R) = \bigoplus_n H_n(X; R)$ as a graded $R$-module. -/
abbrev totalSingularHomology (R : Type) [CommRing R]
    (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularHomologyFamily R X)

/-- The diagonal $X \to X \times X$, $x \mapsto (x, x)$. -/
def TopCat.diag (X : TopCat.{0}) : X ⟶ TopCat.of (X × X) :=
  ⟨fun x => (x, x), by fun_prop⟩

/-- The map on $n$th homology induced by the diagonal $X \to X \times X$. -/
def diagHomology (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    singularHomologyFamily R X n →ₗ[R]
      singularHomologyFamily R (TopCat.of (X × X)) n :=
  (((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map
    (TopCat.diag X)).hom

/-- The total map on graded homology $H_*(X) \to H_*(X \times X)$ induced by the diagonal,
half of the comultiplication on the graded coalgebra $H_*(X; R)$ of Corollary 26.2. -/
def totalDiagMap (R : Type) [CommRing R] (X : TopCat.{0}) :
    totalSingularHomology R X →ₗ[R]
      totalSingularHomology R (TopCat.of (X × X)) :=
  @DirectSum.lmap R _ ℕ (singularHomologyFamily R X) _ _
    (singularHomologyFamily R (TopCat.of (X × X))) _ _
    (fun n => diagHomology R X n)

end SingularCohomology
end

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology




/-- The unique continuous map $X \to \{\ast\}$ to the one-point space. -/
noncomputable def toTerminal (X : TopCat.{0}) : X ⟶ TopCat.of PUnit.{1} :=
  ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The map $H_0(X; R) \to H_0(\{\ast\}; R)$ induced by collapsing $X$ to a point. -/
noncomputable def h0MapToTerminal
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularHomologyModule R X 0 ⟶ singularHomologyModule R (TopCat.of PUnit.{1}) 0 :=
  (((singularHomologyFunctor (ModuleCat.{0} R) 0).obj (ModuleCat.of R R)).map (toTerminal X))

/-- The zeroth homology of the singleton, identified with a coproduct of one copy of $R$. -/
noncomputable def h0TerminalIsoCoproduct (R : Type) [CommRing R] :
    singularHomologyModule R (TopCat.of PUnit.{1}) 0 ≅
      ∐ fun _ : (TopCat.of PUnit.{1} : Type) ↦ (ModuleCat.of R R) :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat.{0} R) (ModuleCat.of R R) (TopCat.of PUnit)

/-- The fold map collapsing a one-element coproduct of $R$ to $R$. -/
noncomputable def coproductPUnitFold (R : Type) [CommRing R] :
    (∐ fun _ : (TopCat.of PUnit.{1} : Type) ↦ (ModuleCat.of R R)) ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ => 𝟙 _)

/-- The augmentation $H_0(X; R) \to R$, obtained by collapsing $X$ to a point. -/
noncomputable def augmentationH0
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularHomologyModule R X 0 ⟶ ModuleCat.of R R :=
  h0MapToTerminal R X ≫ (h0TerminalIsoCoproduct R).hom ≫ coproductPUnitFold R

/-- The counit $\varepsilon : H_*(X; R) \to R$ for the graded coalgebra structure of
Corollary 26.2: project to the degree-$0$ component and then augment. -/
noncomputable def augmentation
    (R : Type) [CommRing R]
    (X : TopCat.{0}) :
    totalSingularHomology R X →ₗ[R] R :=
  (augmentationH0 R X).hom ∘ₗ DirectSum.component R ℕ (singularHomologyFamily R X) 0






noncomputable section
namespace SingularCohomology


/-- The cochain map $S^*(Y; R) \to S^*(X; R)$ induced (contravariantly) by $f : X \to Y$. -/
def inducedCochainMap (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularCochainComplex R Y (ModuleCat.of R R) ⟶
    singularCochainComplex R X (ModuleCat.of R R) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map f)).op)

/-- The induced map on $n$th singular cohomology $f^* : H^n(Y; R) \to H^n(X; R)$. -/
def singularCohomologyMap (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singularCohomology R Y (ModuleCat.of R R) n ⟶
    singularCohomology R X (ModuleCat.of R R) n :=
  HomologicalComplex.homologyMap (inducedCochainMap R f) n

section AlexanderWhitney

/-- The Alexander–Whitney "front face" $\alpha_p : [p] \to [p+q]$ sending $i \mapsto i$. -/
def awFrontFace (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun i => (Fin.castAdd q i).cast (by omega),
    fun _ _ h => by simp only [Fin.le_def]; exact h⟩

/-- The Alexander–Whitney "back face" $\omega_q : [q] \to [p+q]$ sending $j \mapsto j + p$. -/
def awBackFace (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun j => (Fin.natAdd p j).cast (by omega),
    fun _ _ h => by show (Fin.cast _ (Fin.natAdd p _)).val ≤ _
                    simp only [Fin.val_cast, Fin.val_natAdd]; omega⟩

/-- The Alexander–Whitney "front" $\sigma \mapsto \sigma \circ \alpha_p$ of a $(p+q)$-simplex. -/
def awFront (Z : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk p)) :=
  (TopCat.toSSet.obj Z).map (awFrontFace p q).op σ

/-- The Alexander–Whitney "back" $\sigma \mapsto \sigma \circ \omega_q$ of a $(p+q)$-simplex. -/
def awBack (Z : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk q)) :=
  (TopCat.toSSet.obj Z).map (awBackFace p q).op σ

/-- Evaluate a morphism from a coproduct of copies of $R$ at a fixed index $\sigma$. -/
def evalGen (R : Type) [CommRing R] {α : Type}
    (φ : (∐ fun (_ : α) => ModuleCat.of R R) ⟶ ModuleCat.of R R) (σ : α) : R :=
  (Sigma.ι (fun (_ : α) => ModuleCat.of R R) σ ≫ φ).hom (1 : R)

end AlexanderWhitney

/-- Evaluation of a singular $n$-cochain at a singular $n$-simplex $\sigma$, as an $R$-linear
map $S^n(Z; R) \to R$. -/
def evalAtSimplex (R : Type) [CommRing R] {n : ℕ} (Z : TopCat.{0}) (σ : (TopCat.toSSet.obj Z).obj
    (Opposite.op (SimplexCategory.mk n))) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X n →ₗ[R] R where
  toFun φ := (Sigma.ι (fun (_ : (TopCat.toSSet.obj Z).obj
    (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of R R) σ ≫ φ).hom (1 : R)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Glue lemma: $(f + g)$ in `ModuleCat.ofHom` agrees with $f + g$ on underlying linear maps. -/
lemma ofHom_add_hom_eq (R : Type) [CommRing R] (f g : R →ₗ[R] R) :
    (ModuleCat.ofHom f + ModuleCat.ofHom g).hom = f + g := rfl

/-- The Alexander–Whitney bilinear cup product on cochains:
$(f \cup g)(\sigma) = f(\sigma \circ \alpha_p) \cdot g(\sigma \circ \omega_q)$. -/
def cupBilinear (R : Type) [CommRing R] (Z : TopCat.{0}) (p q : ℕ) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X p →ₗ[R]
    (singularCochainComplex R Z (ModuleCat.of R R)).X q →ₗ[R]
    (singularCochainComplex R Z (ModuleCat.of R R)).X (p + q) :=
  LinearMap.mk₂ R
    (fun f g => Sigma.desc fun σ =>
      ModuleCat.ofHom ((evalAtSimplex R Z (awFront Z p q σ) f *
        evalAtSimplex R Z (awBack Z p q σ) g) • LinearMap.id))
    (fun f₁ f₂ g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Preadditive.comp_add, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext
      show ((evalAtSimplex R Z (awFront Z p q b) (f₁ + f₂) * _) • (LinearMap.id : R →ₗ[R] R)) = _
      rw [map_add, add_mul, add_smul, ofHom_add_hom_eq R])
    (fun c f g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Linear.comp_smul, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext; ext
      show ((evalAtSimplex R Z (awFront Z p q b) (c • f) * _) • (LinearMap.id : R →ₗ[R] R)) _ = _
      change (c * evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) * _ = _
      show _ = (c • ((evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) • (LinearMap.id : R →ₗ[R] R))) 1
      simp [smul_eq_mul]; ring)
    (fun f g₁ g₂ => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Preadditive.comp_add, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext
      show ((_ * evalAtSimplex R Z (awBack Z p q b) (g₁ + g₂)) • (LinearMap.id : R →ₗ[R] R)) = _
      rw [map_add, mul_add, add_smul, ofHom_add_hom_eq R])
    (fun c f g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Linear.comp_smul, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext; ext
      show ((_ * evalAtSimplex R Z (awBack Z p q b) (c • g)) • (LinearMap.id : R →ₗ[R] R)) _ = _
      change (evalAtSimplex R Z (awFront Z p q b) f * (c *
        evalAtSimplex R Z (awBack Z p q b) g)) * _ = _
      show _ = (c • ((evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) • (LinearMap.id : R →ₗ[R] R))) 1
      simp [smul_eq_mul]; ring)

/-- The Alexander–Whitney cup product on cochains, packaged as a morphism out of the tensor
product $S^p(Z) \otimes S^q(Z) \to S^{p+q}(Z)$. -/
def awCochainPairingHom
    (R : Type) [CommRing R] (Z : TopCat.{0}) (p q : ℕ) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X p ⊗
    (singularCochainComplex R Z (ModuleCat.of R R)).X q ⟶
    (singularCochainComplex R Z (ModuleCat.of R R)).X (p + q) :=
  ModuleCat.ofHom (TensorProduct.lift (cupBilinear R Z p q))










section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The zeroth singular cohomology `H^0(X; N)` is naturally isomorphic to the
kernel of the coboundary `d^0 : C^0(X; N) → C^1(X; N)`. -/
noncomputable def singularCohomologyZeroIsoKer (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    singularCohomology ℤ X N 0 ≅
    @ModuleCat.of ℤ Int.instCommRing.toRing
      (LinearMap.ker ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom)
      ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom.ker.addCommGroup
      ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom.ker.module :=
  (CochainComplex.isoHomologyπ₀ (singularCochainComplex ℤ X N)).symm ≪≫
    (singularCochainComplex ℤ X N).cyclesIsoSc' 0 0 1
      CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) ≪≫
    ((singularCochainComplex ℤ X N).sc' 0 0 1).cyclesIsoKernel ≪≫
    ModuleCat.kernelIsoKer ((singularCochainComplex ℤ X N).sc' 0 0 1).g

end

/-- The submodule of `N`-valued functions on `X` that are constant on path
components: `f x = f y` whenever `x` and `y` are joined by a path. -/
def pathConstantSubmodule (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) : Submodule ℤ (X → N) where
  carrier := {f | ∀ x y : X, Joined x y → f x = f y}
  add_mem' {f g} hf hg x y hxy := by
    show f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  zero_mem' _ _ _ := rfl
  smul_mem' c f hf x y hxy := by
    show c • f x = c • f y
    rw [hf x y hxy]

/-- A function constant on path components is the same as a function on the
set of path components `π₀(X)`. -/
noncomputable def pathConstantSubmoduleEquivPi0Func (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    (pathConstantSubmodule X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) where
  toFun := fun ⟨f, hf⟩ => Quotient.lift f (fun a b hab => hf a b hab)
  invFun := fun g => ⟨fun x => g (Quotient.mk (pathSetoid X) x),
      fun x y hxy => congrArg g (Quotient.sound hxy)⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext x
    simp only [Quotient.lift_mk]
  right_inv := fun g => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)
  map_smul' := fun c ⟨f, hf⟩ => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)

/-- Convenience alias for `pathConstantSubmoduleEquivPi0Func` viewed as a
linear equivalence on the coerced submodule. -/
noncomputable def pathConstantEquivPi0Func (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    ↥(pathConstantSubmodule X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) :=
  pathConstantSubmoduleEquivPi0Func X N

open scoped Simplicial
open Opposite SimplexCategory

/-- The set of singular `n`-simplices in `X`: continuous maps `Δ^n → X`. -/
abbrev Sing (n : ℕ) (X : TopCat.{0}) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- A singular `0`-simplex in `X` is the same data as a point of `X`. -/
noncomputable def sing0EquivX (X : TopCat.{0}) : Sing 0 X ≃ X :=
  TopCat.toSSetObj₀Equiv

/-- The `0`-th face of a singular `1`-simplex (its endpoint). -/
def face₀ (X : TopCat.{0}) (σ : Sing 1 X) : Sing 0 X :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ 0).op σ

/-- The `1`-st face of a singular `1`-simplex (its starting point). -/
def face₁ (X : TopCat.{0}) (σ : Sing 1 X) : Sing 0 X :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ 1).op σ

/-- The singular `1`-simplex obtained from a path `γ : Path x y` by composing
with the canonical homeomorphism `Δ^1 ≃ [0,1]`. -/
noncomputable def oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) : Sing 1 X :=
  (TopCat.toSSetObjEquiv X (op ⦋1⦌)).symm
    (⟨γ ∘ stdSimplexHomeomorphUnitInterval, γ.continuous.comp
      stdSimplexHomeomorphUnitInterval.continuous⟩)

section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Identifying a face of `σ` with a point of `X` agrees with evaluating
the underlying continuous map at the corresponding vertex of `Δ^1`. -/
lemma sing0EquivX_face_eq (X : TopCat.{0}) (i : Fin 2) (σ : Sing 1 X) :
    sing0EquivX X ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ) =
    (TopCat.toSSetObjEquiv X (op ⦋1⦌) σ).1
      (_root_.stdSimplex.map (SimplexCategory.δ i).toOrderHom default) := by
  rfl

/-- The image of the standard `0`-simplex under `δ_1 : Δ^0 → Δ^1` is the
first standard basis point `e₀`. -/
lemma stdSimplex_map_δ1_default :
    (_root_.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)).toOrderHom
      (default : stdSimplex ℝ (Fin 1))) =
    ⟨Pi.single 0 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
  rw [Subsingleton.elim default (_root_.stdSimplex.vertex 0),
    _root_.stdSimplex.map_vertex]
  simp [SimplexCategory.δ, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb,
    Fin.succAbove, _root_.stdSimplex.vertex]

/-- The image of the standard `0`-simplex under `δ_0 : Δ^0 → Δ^1` is the
second standard basis point `e₁`. -/
lemma stdSimplex_map_δ0_default :
    (_root_.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)).toOrderHom
      (default : stdSimplex ℝ (Fin 1))) =
    ⟨Pi.single 1 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
  rw [Subsingleton.elim default (_root_.stdSimplex.vertex 0),
    _root_.stdSimplex.map_vertex]
  simp [SimplexCategory.δ, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb,
    Fin.succAbove, _root_.stdSimplex.vertex]

/-- The `1`-st face of the singular `1`-simplex of a path `γ : Path x y` is
the starting point `x`. -/
lemma face₁_oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) :
    sing0EquivX X (face₁ X (oneSimplexOfPath X γ)) = x := by
  simp only [face₁, oneSimplexOfPath]
  rw [sing0EquivX_face_eq]
  simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk, Function.comp]
  rw [stdSimplex_map_δ1_default, stdSimplexHomeomorphUnitInterval_zero]
  exact γ.source

/-- The `0`-th face of the singular `1`-simplex of a path `γ : Path x y` is
the endpoint `y`. -/
lemma face₀_oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) :
    sing0EquivX X (face₀ X (oneSimplexOfPath X γ)) = y := by
  simp only [face₀, oneSimplexOfPath]
  rw [sing0EquivX_face_eq]
  simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk, Function.comp]
  rw [stdSimplex_map_δ0_default, stdSimplexHomeomorphUnitInterval_one]
  exact γ.target

/-- Any singular `1`-simplex `σ` realises a path joining its two faces. -/
lemma joined_of_one_simplex (X : TopCat.{0}) (σ : Sing 1 X) :
    Joined (sing0EquivX X (face₁ X σ)) (sing0EquivX X (face₀ X σ)) := by
  set f := TopCat.toSSetObjEquiv X (op ⦋1⦌) σ
  rw [face₁, sing0EquivX_face_eq, face₀, sing0EquivX_face_eq]
  rw [stdSimplex_map_δ1_default, stdSimplex_map_δ0_default]
  have h0 : stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval) =
      ⟨Pi.single 0 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
    rw [← stdSimplexHomeomorphUnitInterval_zero, Homeomorph.symm_apply_apply]
  have h1 : stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval) =
      ⟨Pi.single 1 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
    rw [← stdSimplexHomeomorphUnitInterval_one, Homeomorph.symm_apply_apply]
  let g : C(unitInterval, stdSimplex ℝ (Fin 2)) :=
    ⟨stdSimplexHomeomorphUnitInterval.symm, stdSimplexHomeomorphUnitInterval.symm.continuous⟩
  refine ⟨⟨f.comp g, ?_, ?_⟩⟩
  · show f (g 0) = f ⟨Pi.single 0 1, single_mem_stdSimplex _ _⟩
    simp only [g, ContinuousMap.coe_mk, h0]
  · show f (g 1) = f ⟨Pi.single 1 1, single_mem_stdSimplex _ _⟩
    simp only [g, ContinuousMap.coe_mk, h1]

end

section KerD0EquivPi0

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

/-- The underlying linear map of the zeroth coboundary
`d^0 : C^0(X; N) → C^1(X; N)`. -/
abbrev d0Hom (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :=
  ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom

end KerD0EquivPi0

/-- The integral singular chain complex `C_*(X; ℤ)` of `X`. -/
abbrev singularChainZ (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X

/-- Evaluate a singular `n`-cochain `f : C^n(X; N)` on a singular `n`-simplex
`σ`, returning the corresponding element of `N`. -/
def cochainEvalN (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) (n : ℕ)
    (f : (singularCochainComplex ℤ X N).X n) (σ : Sing n X) : N :=
  (Sigma.ι (fun (_ : Sing n X) => ModuleCat.of ℤ ℤ) σ ≫ f).hom (1 : ℤ)

section CoboundaryFormula

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

/-- Boundary formula for a singular `1`-simplex: `∂σ = face₀(σ) − face₁(σ)`. -/
lemma singularChainZ_ι_comp_d (X : TopCat.{0}) (σ : Sing 1 X) :
    Sigma.ι (fun (_ : Sing 1 X) => ModuleCat.of ℤ ℤ) σ ≫
      (singularChainZ X).d 1 0 =
    Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₀ X σ) -
    Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₁ X σ) := by
  simp only [singularChainZ, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  dsimp only [Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft, Functor.postcompose₂]
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    SimplicialObject.δ, sub_eq_add_neg]
  erw [Sigma.ι_comp_map' _ _ σ, Sigma.ι_comp_map' _ _ σ]
  simp only [Category.id_comp, face₀, face₁]

/-- Dual formula: for a `0`-cochain `f`, the value of `d^0 f` on a singular
`1`-simplex `σ` is `f(face₀ σ) − f(face₁ σ)`. -/
lemma coboundary_zero_eval (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f : (singularCochainComplex ℤ X N).X 0)
    (σ : Sing 1 X) :
    cochainEvalN X N 1 ((singularCochainComplex ℤ X N).d 0 1 f) σ =
    cochainEvalN X N 0 f (face₀ X σ) - cochainEvalN X N 0 f (face₁ X σ) := by
  simp only [cochainEvalN]
  erw [show (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) σ ≫
      (singularChainZ X).d 1 0 ≫ f).hom (1 : ℤ) =
    ((Sigma.ι _ σ ≫ (singularChainZ X).d 1 0) ≫ f).hom (1 : ℤ) from by
      rw [Category.assoc]]
  rw [singularChainZ_ι_comp_d]
  simp only [Preadditive.sub_comp, ModuleCat.hom_sub, LinearMap.sub_apply]

end CoboundaryFormula

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Build a singular `0`-cochain `C^0(X; N)` from a function `g : X → N`,
sending each singular `0`-simplex `σ₀` to the linear map `1 ↦ g(σ₀)`. -/
noncomputable def cochainOfFunc (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (g : X → N) : (singularCochainComplex ℤ X N).X 0 :=
  Sigma.desc (fun (σ₀ : Sing 0 X) =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ N (g (sing0EquivX X σ₀))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Evaluating the cochain `cochainOfFunc X N g` on a `0`-simplex `σ₀`
returns `g` evaluated at the corresponding point. -/
lemma cochainOfFunc_eval (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (g : X → N) (σ₀ : Sing 0 X) :
    cochainEvalN X N 0 (cochainOfFunc X N g) σ₀ = g (sing0EquivX X σ₀) := by
  simp only [cochainEvalN, cochainOfFunc]
  rw [Sigma.ι_desc]
  simp [LinearMap.toSpanSingleton_apply]

/-- Two morphisms `ℤ ⟶ N` of `ℤ`-modules that agree on `1` are equal. -/
lemma moduleCat_int_hom_ext {N : ModuleCat.{0} ℤ}
    (φ ψ : ModuleCat.of ℤ ℤ ⟶ N) (h : φ.hom (1 : ℤ) = ψ.hom (1 : ℤ)) : φ = ψ := by
  ext
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Two `0`-cochains are equal iff they take the same value on every
singular `0`-simplex. -/
lemma cochain_ext (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f₁ f₂ : (singularCochainComplex ℤ X N).X 0)
    (h : ∀ σ₀ : Sing 0 X, cochainEvalN X N 0 f₁ σ₀ = cochainEvalN X N 0 f₂ σ₀) :
    f₁ = f₂ := by
  apply Sigma.hom_ext
  intro σ₀
  exact moduleCat_int_hom_ext _ _ (h σ₀)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- A `1`-cochain vanishes iff it evaluates to zero on every singular
`1`-simplex. -/
lemma cochain1_eq_zero_iff (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f : (singularCochainComplex ℤ X N).X 1) :
    f = 0 ↔ ∀ σ : Sing 1 X, cochainEvalN X N 1 f σ = 0 := by
  constructor
  · intro hf σ
    simp only [cochainEvalN, hf, Limits.HasZeroMorphisms.comp_zero]
    rfl
  · intro h
    apply Sigma.hom_ext; intro σ
    exact moduleCat_int_hom_ext _ _ (by simpa [cochainEvalN] using h σ)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- A `0`-cocycle is the same data as a function `X → N` that is constant
on path components. This is the key linear equivalence underlying
`H^0(X; N) ≅ Map(π₀(X), N)`. -/
noncomputable def kerD0EquivPathConstant (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    LinearMap.ker (d0Hom X N) ≃ₗ[ℤ] pathConstantSubmodule X N where

  toFun := fun ⟨f, hf⟩ =>
    ⟨fun x => cochainEvalN X N 0 f ((sing0EquivX X).symm x),
     fun x y hxy => by
       obtain ⟨γ⟩ := hxy
       have hker : d0Hom X N f = 0 := by rwa [LinearMap.mem_ker] at hf
       let σ := oneSimplexOfPath X γ
       have hσ : cochainEvalN X N 0 f (face₀ X σ) =
           cochainEvalN X N 0 f (face₁ X σ) := by
         have hcb := coboundary_zero_eval X N f σ
         have hzero : cochainEvalN X N 1 ((singularCochainComplex ℤ X N).d 0 1 f) σ = 0 := by
           rw [show (singularCochainComplex ℤ X N).d 0 1 f = d0Hom X N f from rfl, hker]
           simp [cochainEvalN]
         rw [hzero] at hcb
         exact sub_eq_zero.mp hcb.symm
       show cochainEvalN X N 0 f ((sing0EquivX X).symm x) =
            cochainEvalN X N 0 f ((sing0EquivX X).symm y)
       conv_lhs => rw [show (sing0EquivX X).symm x = face₁ X σ from by
             rw [Equiv.symm_apply_eq]; exact (face₁_oneSimplexOfPath X γ).symm]
       conv_rhs => rw [show (sing0EquivX X).symm y = face₀ X σ from by
             rw [Equiv.symm_apply_eq]; exact (face₀_oneSimplexOfPath X γ).symm]
       exact hσ.symm⟩

  invFun := fun ⟨g, hg⟩ =>
    ⟨cochainOfFunc X N g, by
       rw [LinearMap.mem_ker]
       rw [show d0Hom X N (cochainOfFunc X N g) =
           (singularCochainComplex ℤ X N).d 0 1 (cochainOfFunc X N g) from rfl]
       rw [cochain1_eq_zero_iff]
       intro σ
       rw [coboundary_zero_eval]
       rw [cochainOfFunc_eval, cochainOfFunc_eval]
       have := joined_of_one_simplex X σ
       rw [hg _ _ this]
       simp⟩

  left_inv := fun ⟨f, hf⟩ => by
    simp only
    congr 1
    apply cochain_ext
    intro σ₀
    simp only [cochainOfFunc_eval]
    congr 1
    exact (sing0EquivX X).symm_apply_apply σ₀

  right_inv := fun ⟨g, hg⟩ => by
    simp only
    simp_rw [cochainOfFunc_eval, Equiv.apply_symm_apply]
  map_add' := fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ => by simp only; rfl
  map_smul' := fun c ⟨f, hf⟩ => by simp only; rfl

/-- Composing the kernel-vs-path-constant equivalence with the
path-constant-vs-`π₀` equivalence: `ker(d^0) ≃ Map(π₀(X), N)`. -/
noncomputable def singularCohomologyKerEquivPi0Map (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    LinearMap.ker (d0Hom X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) :=
  (kerD0EquivPathConstant X N).trans (pathConstantEquivPi0Func X N)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Lemma 26.6: the zeroth singular cohomology with coefficients in `N`
is naturally isomorphic to the module of functions from `π₀(X)` to `N`. -/
noncomputable def singularCohomology_zero_eq_map_pi0
    (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    singularCohomology ℤ X N 0 ≅ ModuleCat.of ℤ (ZerothHomotopy X → N) := by
  refine (singularCohomologyZeroIsoKer X N).trans ?_
  convert (singularCohomologyKerEquivPi0Map X N).toModuleIso using 1
  · congr 1; exact Subsingleton.elim _ _

end SingularCohomology
end
