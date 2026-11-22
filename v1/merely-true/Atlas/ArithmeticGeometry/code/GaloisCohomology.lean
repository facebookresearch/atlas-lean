/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure

open groupCohomology

namespace GaloisCohomology

/-- A function $\alpha \colon G \to A$ is a *crossed homomorphism* (1-cocycle) iff it satisfies the
cocycle identity $\alpha(\tau\sigma) = \alpha(\tau) + \tau \cdot \alpha(\sigma)$, identified here
with `groupCohomology.IsCocycle₁`. -/
def IsCrossedHom {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A] (α : G → A) : Prop :=
  groupCohomology.IsCocycle₁ α

/-- A bundled crossed homomorphism: a function $G \to A$ together with a proof of the cocycle
condition. -/
structure CrossedHom (G A : Type*) [Mul G] [AddCommGroup A] [SMul G A] where
  toFun : G → A
  cocycle_condition : IsCrossedHom toFun

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A `CrossedHom G A` can be coerced to a function $G \to A$ in a `FunLike` manner. -/
instance : FunLike (CrossedHom G A) G A where
  coe := CrossedHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Crossed homomorphisms are determined by their function values: two crossed homs agreeing
pointwise are equal. -/
@[ext]
theorem ext {α β : CrossedHom G A} (h : ∀ g, α g = β g) : α = β :=
  DFunLike.ext α β h

/-- The coercion of a constructed `CrossedHom.mk f hf` to a function is `f` itself. -/
@[simp]
theorem coe_mk (f : G → A) (hf) : (CrossedHom.mk f hf : G → A) = f := rfl

/-- The cocycle condition rewritten in the convenient form
$\alpha(\tau\sigma) = \alpha(\tau) + \tau \cdot \alpha(\sigma)$. -/
theorem cocycle_condition_eq (α : CrossedHom G A) (τ σ : G) :
    α (τ * σ) = α τ + τ • α σ := by
  have := α.cocycle_condition τ σ
  rwa [add_comm] at this

/-- A bundled crossed hom is a crossed hom (as a predicate on its underlying function). -/
theorem isCrossedHom (α : CrossedHom G A) : IsCrossedHom (α : G → A) :=
  α.cocycle_condition


section Group

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The zero crossed homomorphism $\alpha \equiv 0$. -/
def zero : CrossedHom G A where
  toFun := 0
  cocycle_condition τ σ := by simp [smul_zero]

/-- Pointwise addition of two crossed homomorphisms is again a crossed homomorphism. -/
def add (α β : CrossedHom G A) : CrossedHom G A where
  toFun := α + β
  cocycle_condition τ σ := by
    simp only [Pi.add_apply]
    rw [α.cocycle_condition_eq, β.cocycle_condition_eq, smul_add]
    abel

/-- Pointwise negation of a crossed homomorphism is again a crossed homomorphism. -/
def neg (α : CrossedHom G A) : CrossedHom G A where
  toFun := -α
  cocycle_condition τ σ := by
    simp only [Pi.neg_apply]
    rw [α.cocycle_condition_eq, smul_neg]
    abel

/-- The zero element of `CrossedHom G A`. -/
instance : Zero (CrossedHom G A) := ⟨zero⟩
/-- Pointwise addition on `CrossedHom G A`. -/
instance : Add (CrossedHom G A) := ⟨add⟩
/-- Pointwise negation on `CrossedHom G A`. -/
instance : Neg (CrossedHom G A) := ⟨neg⟩

/-- The zero crossed hom evaluates to $0$ at every $g \in G$. -/
@[simp] theorem zero_apply (g : G) : (0 : CrossedHom G A) g = 0 := rfl
/-- Sum of two crossed homs evaluates pointwise. -/
@[simp] theorem add_apply (α β : CrossedHom G A) (g : G) : (α + β) g = α g + β g := rfl
/-- Negation of a crossed hom evaluates pointwise. -/
@[simp] theorem neg_apply (α : CrossedHom G A) (g : G) : (-α) g = -(α g) := rfl

/-- Crossed homomorphisms form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (CrossedHom G A) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc α β γ := by ext g; simp [add_assoc]
  zero_add α := by ext g; simp
  add_zero α := by ext g; simp
  add_comm α β := by ext g; simp [add_comm]
  neg_add_cancel α := by ext g; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

end Group

end CrossedHom

/-- A *continuous* crossed homomorphism: a crossed hom whose underlying function is continuous. -/
structure ContCrossedHom (G A : Type*) [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A] extends CrossedHom G A where
  continuous_toFun : Continuous toFun

namespace ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A]

/-- A `ContCrossedHom G A` can be coerced to a function $G \to A$. -/
instance : FunLike (ContCrossedHom G A) G A where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; simp only [mk.injEq]
    exact CrossedHom.ext (fun x => congrFun h x)

/-- Continuous crossed homs are determined by their pointwise values. -/
@[ext]
theorem ext {α β : ContCrossedHom G A} (h : ∀ g, α g = β g) : α = β :=
  DFunLike.ext α β h

/-- Coercion of a constructed `ContCrossedHom.mk f hf` returns `f`. -/
@[simp]
theorem coe_mk' (f : CrossedHom G A) (hf) : (ContCrossedHom.mk f hf : G → A) = f := rfl

/-- Restated cocycle identity for continuous crossed homs:
$\alpha(\tau\sigma) = \alpha(\tau) + \tau \cdot \alpha(\sigma)$. -/
theorem cocycle_condition_eq (α : ContCrossedHom G A) (τ σ : G) :
    α (τ * σ) = α τ + τ • α σ :=
  α.toCrossedHom.cocycle_condition_eq τ σ

/-- The underlying function of a continuous crossed hom is continuous. -/
theorem continuous (α : ContCrossedHom G A) : Continuous α :=
  α.continuous_toFun

/-- Underlying crossed-hom property of a continuous crossed hom. -/
theorem isCrossedHom (α : ContCrossedHom G A) : IsCrossedHom (α : G → A) :=
  α.toCrossedHom.cocycle_condition

/-- Restatement of the cocycle condition in Mathlib's `IsCocycle₁` form. -/
theorem isCocycle₁ (α : ContCrossedHom G A) : groupCohomology.IsCocycle₁ (α : G → A) :=
  α.toCrossedHom.cocycle_condition

section Group

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace G] [TopologicalSpace A] [ContinuousAdd A] [ContinuousNeg A]

/-- The zero continuous crossed homomorphism $\alpha \equiv 0$, which is continuous as a constant
function. -/
def zero : ContCrossedHom G A where
  toCrossedHom := CrossedHom.zero
  continuous_toFun := continuous_const

/-- Pointwise sum of two continuous crossed homomorphisms is again continuous. -/
def add (α β : ContCrossedHom G A) : ContCrossedHom G A where
  toCrossedHom := CrossedHom.add α.toCrossedHom β.toCrossedHom
  continuous_toFun := α.continuous.add β.continuous

/-- Pointwise negation of a continuous crossed homomorphism is continuous. -/
def neg (α : ContCrossedHom G A) : ContCrossedHom G A where
  toCrossedHom := CrossedHom.neg α.toCrossedHom
  continuous_toFun := α.continuous.neg

/-- Zero on `ContCrossedHom`. -/
instance : Zero (ContCrossedHom G A) := ⟨zero⟩
/-- Pointwise addition on `ContCrossedHom`. -/
instance : Add (ContCrossedHom G A) := ⟨add⟩
/-- Pointwise negation on `ContCrossedHom`. -/
instance : Neg (ContCrossedHom G A) := ⟨neg⟩

omit [ContinuousAdd A] [ContinuousNeg A] in
/-- The zero continuous crossed hom evaluates to $0$ everywhere. -/
@[simp] theorem zero_apply (g : G) : (0 : ContCrossedHom G A) g = 0 := rfl

omit [ContinuousNeg A] in
/-- Sum of two continuous crossed homs evaluates pointwise. -/
@[simp] theorem add_apply (α β : ContCrossedHom G A) (g : G) :
    (α + β) g = α g + β g := rfl

omit [ContinuousAdd A] in
/-- Negation of a continuous crossed hom evaluates pointwise. -/
@[simp] theorem neg_apply (α : ContCrossedHom G A) (g : G) : (-α) g = -(α g) := rfl

/-- Continuous crossed homomorphisms form an additive commutative group. -/
instance : AddCommGroup (ContCrossedHom G A) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc α β γ := by ext g; simp [add_assoc]
  zero_add α := by ext g; simp
  add_zero α := by ext g; simp
  add_comm α β := by ext g; simp [add_comm]
  neg_add_cancel α := by ext g; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

end Group

end ContCrossedHom

section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- A function $\alpha \colon G \to A$ is a *principal crossed homomorphism* (1-coboundary) iff it
has the form $\alpha(\sigma) = \sigma \cdot P - P$ for some $P \in A$. -/
def IsPrincipalCrossedHom (α : G → A) : Prop :=
  groupCohomology.IsCoboundary₁ α

/-- Unfolding: $\alpha$ is a coboundary iff there exists $P \in A$ with
$\sigma \cdot P - P = \alpha(\sigma)$ for all $\sigma$. -/
theorem isPrincipalCrossedHom_iff (α : G → A) :
    IsPrincipalCrossedHom α ↔ ∃ P : A, ∀ σ : G, σ • P - P = α σ :=
  Iff.rfl

/-- Every principal (1-coboundary) crossed homomorphism is itself a crossed homomorphism
(1-cocycle). -/
theorem IsPrincipalCrossedHom.isCrossedHom {α : G → A} (h : IsPrincipalCrossedHom α) :
    IsCrossedHom α := by
  obtain ⟨P, hP⟩ := h
  intro τ σ
  simp_rw [← hP]
  simp [smul_sub, mul_smul]

/-- The principal crossed hom $\sigma \mapsto \sigma \cdot P - P$ associated to a point $P \in A$. -/
def principalCrossedHom (P : A) : CrossedHom G A where
  toFun σ := σ • P - P
  cocycle_condition :=
    IsPrincipalCrossedHom.isCrossedHom ⟨P, fun _ => rfl⟩

/-- The principal crossed hom at $P$ evaluates as $\sigma \mapsto \sigma \cdot P - P$. -/
@[simp]
theorem principalCrossedHom_apply (P : A) (σ : G) :
    principalCrossedHom P σ = σ • P - P := rfl

/-- The subgroup of principal crossed homomorphisms (1-coboundaries) inside the additive group of
all crossed homomorphisms. -/
def principalCrossedHomSubgroup (G A : Type*) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : AddSubgroup (CrossedHom G A) where
  carrier := { α | IsPrincipalCrossedHom (α : G → A) }
  zero_mem' := ⟨0, fun σ => by simp [smul_zero]⟩
  add_mem' := by
    rintro α β ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun σ => by
      simp only [CrossedHom.add_apply, smul_add]
      rw [← hP, ← hQ]
      abel⟩
  neg_mem' := by
    rintro α ⟨P, hP⟩
    exact ⟨-P, fun σ => by
      simp only [CrossedHom.neg_apply, smul_neg]
      rw [← hP]
      abel⟩

/-- Membership criterion for the subgroup of principal crossed homomorphisms. -/
theorem mem_principalCrossedHomSubgroup_iff (α : CrossedHom G A) :
    α ∈ principalCrossedHomSubgroup G A ↔ IsPrincipalCrossedHom (α : G → A) :=
  Iff.rfl

section Continuous

variable [TopologicalSpace G] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousNeg A] [ContinuousSMul G A]

/-- The principal continuous crossed hom $\sigma \mapsto \sigma \cdot P - P$ associated to
$P \in A$, viewed as a `ContCrossedHom`. -/
def contPrincipalCrossedHom (P : A) : ContCrossedHom G A where
  toCrossedHom := principalCrossedHom P
  continuous_toFun := by
    show Continuous (fun σ => σ • P - P)
    simp only [sub_eq_add_neg]
    exact (continuous_id.smul continuous_const).add continuous_const.neg

/-- Evaluation formula for the continuous principal crossed hom at $P$. -/
@[simp]
theorem contPrincipalCrossedHom_apply (P : A) (σ : G) :
    contPrincipalCrossedHom P σ = σ • P - P := rfl

/-- The subgroup of continuous principal crossed homomorphisms inside `ContCrossedHom G A`. -/
def contPrincipalCrossedHomSubgroup (G A : Type*) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace G] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousNeg A] [ContinuousSMul G A] :
    AddSubgroup (ContCrossedHom G A) where
  carrier := { α | IsPrincipalCrossedHom (α : G → A) }
  zero_mem' := ⟨0, fun σ => by simp [smul_zero]⟩
  add_mem' := by
    rintro α β ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun σ => by
      simp only [ContCrossedHom.add_apply, smul_add]
      rw [← hP, ← hQ]
      abel⟩
  neg_mem' := by
    rintro α ⟨P, hP⟩
    exact ⟨-P, fun σ => by
      simp only [ContCrossedHom.neg_apply, smul_neg]
      rw [← hP]
      abel⟩

/-- Membership criterion for the subgroup of continuous principal crossed homomorphisms. -/
theorem mem_contPrincipalCrossedHomSubgroup_iff (α : ContCrossedHom G A) :
    α ∈ contPrincipalCrossedHomSubgroup G A ↔ IsPrincipalCrossedHom (α : G → A) :=
  Iff.rfl

end Continuous

end PrincipalCrossedHom

section H1

variable (G A : Type*) [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace G] [TopologicalSpace A] [ContinuousAdd A] [ContinuousNeg A]
    [ContinuousSMul G A]

/-- The first (continuous) Galois cohomology group: $H^1(G, A) := Z^1 / B^1$ where $Z^1$ is the
group of continuous crossed homs and $B^1$ the subgroup of principal ones. -/
abbrev H1 := ContCrossedHom G A ⧸ contPrincipalCrossedHomSubgroup G A

/-- The canonical projection $\mathrm{ContCrossedHom}(G, A) \to H^1(G, A)$. -/
def H1.mk (α : ContCrossedHom G A) : H1 G A :=
  QuotientAddGroup.mk α

/-- Equality criterion in $H^1$: $[\alpha] = [\beta]$ iff $\alpha - \beta$ is a principal crossed
homomorphism. -/
theorem H1.eq_iff (α β : ContCrossedHom G A) :
    H1.mk G A α = H1.mk G A β ↔ α - β ∈ contPrincipalCrossedHomSubgroup G A := by
  rw [H1.mk, H1.mk, QuotientAddGroup.eq]
  constructor
  · intro h
    have : -(-α + β) = α - β := by abel
    rw [← this]
    exact (contPrincipalCrossedHomSubgroup G A).neg_mem h
  · intro h
    have : -α + β = -(α - β) := by abel
    rw [this]
    exact (contPrincipalCrossedHomSubgroup G A).neg_mem h

end H1

section WeilChateletGroupReal

open scoped Classical

/-- The *absolute Galois group* $\mathrm{Gal}(\bar k/k)$ of a field $k$, realized as $k$-algebra
automorphisms of an algebraic closure of $k$. -/
abbrev AbsGaloisGroup (k : Type*) [Field k] :=
  AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k

/-- The Krull topology on the absolute Galois group: open subgroups are stabilizers of finite
extensions. -/
noncomputable instance absGaloisGroupTopologicalSpace (k : Type*) [Field k] :
    TopologicalSpace (AbsGaloisGroup k) :=
  krullTopology k (AlgebraicClosure k)

/-- The points of an elliptic curve over the algebraic closure $\bar k$: $E(\bar k)$. -/
def ECurvePointsAlgClosure (k : Type*) [Field k] (W : WeierstrassCurve k) :=
  (W.baseChange (AlgebraicClosure k)).toAffine.Point

/-- The group structure on $E(\bar k)$ coming from the Weierstrass curve's affine point group law. -/
noncomputable instance instAddCommGroupECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    AddCommGroup (ECurvePointsAlgClosure k W) :=
  WeierstrassCurve.Affine.Point.instAddCommGroup (F := AlgebraicClosure k)

/-- The Galois group $\mathrm{Gal}(\bar k/k)$ acts on $E(\bar k)$ by transporting points along
each $k$-algebra automorphism of $\bar k$. -/
noncomputable def galoisDistribMulAction (k : Type*) [Field k] (W : WeierstrassCurve k) :
    DistribMulAction (AbsGaloisGroup k) (ECurvePointsAlgClosure k W) where
  smul σ P := WeierstrassCurve.Affine.Point.map σ.toAlgHom P
  one_smul P := by
    show WeierstrassCurve.Affine.Point.map (AlgEquiv.refl.toAlgHom (R := k)) P = P
    cases P with
    | zero => rfl
    | some x y h => simp [WeierstrassCurve.Affine.Point.map_some]
  mul_smul σ τ P := by
    show WeierstrassCurve.Affine.Point.map (σ * τ).toAlgHom P =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom
        (WeierstrassCurve.Affine.Point.map τ.toAlgHom P)
    rw [WeierstrassCurve.Affine.Point.map_map]
    cases P with
    | zero => rfl
    | some x y h => simp [WeierstrassCurve.Affine.Point.map_some]
  smul_zero σ := by
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom 0 = 0
    exact WeierstrassCurve.Affine.Point.map_zero σ.toAlgHom
  smul_add σ P Q := by
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom (P + Q) =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P +
        WeierstrassCurve.Affine.Point.map σ.toAlgHom Q
    exact (WeierstrassCurve.Affine.Point.map σ.toAlgHom).map_add P Q

/-- Promote the Galois `DistribMulAction` on $E(\bar k)$ to an `instance`. -/
noncomputable instance instDistribMulActionGaloisOnECurvePoints (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    DistribMulAction (AbsGaloisGroup k) (ECurvePointsAlgClosure k W) :=
  galoisDistribMulAction k W

/-- We endow $E(\bar k)$ with the discrete topology, which is appropriate for the topology on
the cocycle group. -/
noncomputable instance instTopologicalSpaceECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    TopologicalSpace (ECurvePointsAlgClosure k W) := ⊥

/-- Confirmation that the topology on $E(\bar k)$ chosen above is the discrete topology. -/
instance instDiscreteTopologyECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    DiscreteTopology (ECurvePointsAlgClosure k W) := ⟨rfl⟩

/-- Addition on $E(\bar k)$ is continuous (vacuously, since the topology is discrete). -/
instance instContinuousAddECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    ContinuousAdd (ECurvePointsAlgClosure k W) where
  continuous_add := continuous_of_discreteTopology

/-- Negation on $E(\bar k)$ is continuous (vacuously, in the discrete topology). -/
instance instContinuousNegECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    ContinuousNeg (ECurvePointsAlgClosure k W) where
  continuous_neg := continuous_of_discreteTopology

/-- The Galois action on $E(\bar k)$ is continuous (in the Krull topology on $\mathrm{Gal}(\bar k/k)$
and the discrete topology on $E(\bar k)$): the stabilizer of every point is open, since it
contains the open subgroup fixing a finite subextension containing the coordinates of $P$. -/
noncomputable def galoisContinuousSMul (k : Type*) [Field k] (W : WeierstrassCurve k) :
    @ContinuousSMul (AbsGaloisGroup k) (ECurvePointsAlgClosure k W)
      (galoisDistribMulAction k W).toSMul
      (absGaloisGroupTopologicalSpace k)
      (instTopologicalSpaceECurvePointsAlgClosure k W) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro P
  suffices h : ∃ (E : IntermediateField k (AlgebraicClosure k)),
      FiniteDimensional k E ∧ E.fixingSubgroup ≤ MulAction.stabilizer _ P by
    obtain ⟨E, _, hle⟩ := h
    exact Subgroup.isOpen_of_mem_nhds
      (MulAction.stabilizer (AbsGaloisGroup k) P)
      (Filter.mem_of_superset
        ((IntermediateField.fixingSubgroup_isOpen E).mem_nhds E.fixingSubgroup.one_mem)
        hle)
  change ECurvePointsAlgClosure k W at P
  match P with
  | .zero =>
    exact ⟨⊥, IntermediateField.instFiniteSubtypeMemBot k, fun σ _ => by
      simp only [MulAction.mem_stabilizer_iff]
      show WeierstrassCurve.Affine.Point.map σ.toAlgHom .zero = .zero
      exact WeierstrassCurve.Affine.Point.map_zero σ.toAlgHom⟩
  | .some x y h =>
    refine ⟨IntermediateField.adjoin k {x, y},
      IntermediateField.finiteDimensional_adjoin (fun z _ =>
        isAlgebraic_iff_isIntegral.mp ((AlgebraicClosure.isAlgebraic k).isAlgebraic z)),
      fun σ hσ => ?_⟩
    simp only [MulAction.mem_stabilizer_iff]
    show WeierstrassCurve.Affine.Point.map σ.toAlgHom (.some x y h) = .some x y h
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
    have hx : σ x = x :=
      hσ' x (IntermediateField.subset_adjoin k _ (Set.mem_insert x {y}))
    have hy : σ y = y :=
      hσ' y (IntermediateField.subset_adjoin k _ (Set.mem_insert_iff.mpr (Or.inr rfl)))
    simp only [WeierstrassCurve.Affine.Point.map_some, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe, hx, hy]

/-- Promote `galoisContinuousSMul` to an `instance`. -/
noncomputable instance instContinuousSMulGaloisOnECurvePoints (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    ContinuousSMul (AbsGaloisGroup k) (ECurvePointsAlgClosure k W) :=
  galoisContinuousSMul k W

/-- The realisation of the Weil-Châtelet group via Galois cohomology:
$H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$. -/
noncomputable abbrev WeilChateletGroupReal (k : Type*) [Field k] (W : WeierstrassCurve k) :=
  H1 (AbsGaloisGroup k) (ECurvePointsAlgClosure k W)

end WeilChateletGroupReal

end GaloisCohomology
