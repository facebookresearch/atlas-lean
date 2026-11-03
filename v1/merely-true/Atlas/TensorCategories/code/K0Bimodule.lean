/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite

set_option maxHeartbeats 800000

open Finset FusionRing

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The Grothendieck group `K₀(R)` of a fusion ring `R`, represented as integer-valued
coefficient vectors indexed by the basis `ι`. -/
@[ext]
structure K0Group (R : FusionRing ι) where
  coeff : ι → ℤ

namespace K0Group

variable {R : FusionRing ι}

/-- The zero element of `K₀(R)` is the all-zero coefficient vector. -/
instance : Zero (K0Group R) := ⟨⟨fun _ => 0⟩⟩
/-- Componentwise addition of elements of `K₀(R)`. -/
instance : Add (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Componentwise negation on `K₀(R)`. -/
instance : Neg (K0Group R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Componentwise subtraction on `K₀(R)`. -/
instance : Sub (K0Group R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Natural-number scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℕ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Integer scalar multiplication on `K₀(R)`, applied componentwise. -/
instance : SMul ℤ (K0Group R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Each coefficient of the zero element of `K₀(R)` is `0`. -/
@[simp] lemma coeff_zero (k : ι) : (0 : K0Group R).coeff k = 0 := rfl
/-- Addition on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_add (a b : K0Group R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Negation on `K₀(R)` is componentwise. -/
@[simp] lemma coeff_neg (a : K0Group R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Subtraction on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_sub (a b : K0Group R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- `K₀(R)` is an additive abelian group with componentwise operations. -/
instance instAddCommGroup : AddCommGroup (K0Group R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]
    ring

end K0Group

/-- Left action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(r ◃ p)_k = Σᵢⱼ rᵢ pⱼ N_{i* k j}`. -/
def k0ActLeft (r p : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun i => univ.sum fun j => r i * p j * (R.N (R.star i) k j : ℤ)

/-- Right action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(p ▹ r)_k = Σ_{a,j} pₐ rⱼ N_{k j* a}`. -/
def k0ActRight (p r : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun a => univ.sum fun j => p a * r j * (R.N k (R.star j) a : ℤ)

/-- The left `K₀`-action coincides with multiplication in the Grothendieck ring `Gr(R)`. -/
theorem k0ActLeft_eq_grMul (r p : ι → ℤ) : R.k0ActLeft r p = R.grMul r p := by
  funext k
  simp only [k0ActLeft, grMul]
  congr 1; ext i; congr 1; ext j; congr 1
  exact_mod_cast (R.N_star_transpose i j k).symm

/-- The right action by the unit of `Gr(R)` is the identity. -/
theorem k0ActRight_one (p : ι → ℤ) : R.k0ActRight p R.grOne = p := by
  funext k
  simp only [k0ActRight, grOne]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true]
  rw [R.star_unit]
  simp only [R.mul_unit_int, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]

/-- Additivity of the right action in the module argument. -/
theorem k0ActRight_add_left (p₁ p₂ r : ι → ℤ) :
    R.k0ActRight (fun k => p₁ k + p₂ k) r =
    fun k => R.k0ActRight p₁ r k + R.k0ActRight p₂ r k := by
  funext k; simp only [k0ActRight]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Additivity of the right action in the ring argument. -/
theorem k0ActRight_add_right (p r₁ r₂ : ι → ℤ) :
    R.k0ActRight p (fun k => r₁ k + r₂ k) =
    fun k => R.k0ActRight p r₁ k + R.k0ActRight p r₂ k := by
  funext k; simp only [k0ActRight]
  have h : ∀ a j, p a * (r₁ j + r₂ j) * (R.N k (R.star j) a : ℤ) =
      p a * r₁ j * (R.N k (R.star j) a : ℤ) + p a * r₂ j * (R.N k (R.star j) a : ℤ) :=
    fun _ _ => by ring
  simp_rw [h, Finset.sum_add_distrib]

/-- Right action of any ring element on the zero module element is zero. -/
theorem k0ActRight_zero_left (r : ι → ℤ) :
    R.k0ActRight (fun _ => 0) r = fun _ => 0 := by
  funext k; simp only [k0ActRight]; simp

/-- Right action of the zero ring element on any module element is zero. -/
theorem k0ActRight_zero_right (p : ι → ℤ) :
    R.k0ActRight p (fun _ => 0) = fun _ => 0 := by
  funext k; simp only [k0ActRight]; simp

/-- Symmetry of the duality involution `star`: `a = b*` iff `b = a*`. -/
lemma star_eq_iff (a b : ι) : a = R.star b ↔ b = R.star a := by
  constructor <;> (intro h; rw [h, R.star_star])

/-- Cyclic symmetry of the structure constants under duality:
`N_{i j k*} = N_{j k i*}`. -/
lemma N_cyclic_star (i j k : ι) : R.N i j (R.star k) = R.N j k (R.star i) := by
  have h := R.assoc i j k R.unit
  simp only [R.duality, mul_ite, mul_one, mul_zero] at h
  simp_rw [R.star_eq_iff k] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

/-- Star-equivariance of the structure constants: `N_{p* j* q*} = N_{j p q}`. -/
lemma N_star_triple (p j q : ι) : R.N (R.star p) (R.star j) (R.star q) = R.N j p q := by
  rw [R.N_cyclic_star (R.star p) (R.star j) q, R.star_star]
  have h := R.N_star_transpose (R.star j) q p
  rw [R.star_star] at h
  exact h

/-- The involutive duality on the index set viewed as a self-equivalence of `ι`. -/
noncomputable def starEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

/-- A sum over `ι` is invariant under reparametrization by the duality involution `star`. -/
lemma sum_star_reparametrize (f : ι → ℤ) :
    (univ.sum fun m => f m) = (univ.sum fun q => f (R.star q)) := by
  apply Finset.sum_equiv R.starEquiv
  · intro i; simp [Finset.mem_univ]
  · intro i _; simp [starEquiv, R.star_star]

/-- Inner-sum identity used to prove associativity of the right `K₀`-action: rewrites a
contraction over `k` in terms of a contraction over `q` via the cyclic identity. -/
lemma inner_sum_k0ActRight_assoc (a j p l : ι) :
    (univ.sum fun k => (R.N k (R.star j) a : ℤ) * (R.N l (R.star p) k : ℤ)) =
    (univ.sum fun q => (R.N j p q : ℤ) * (R.N l (R.star q) a : ℤ)) := by
  simp_rw [mul_comm ((R.N _ (R.star j) a : ℤ)) _]
  have h_assoc : (univ.sum fun k => (R.N l (R.star p) k : ℤ) * (R.N k (R.star j) a : ℤ)) =
    (univ.sum fun m => (R.N (R.star p) (R.star j) m : ℤ) * (R.N l m a : ℤ)) := by
    exact_mod_cast R.assoc l (R.star p) (R.star j) a
  rw [h_assoc, R.sum_star_reparametrize]
  congr 1; ext q
  congr 1
  exact_mod_cast R.N_star_triple p j q

/-- Inner-sum identity used to prove the bimodule compatibility: rewrites the contraction
exchanging the roles of left and right action variables. -/
lemma inner_sum_bimodule (a j i l : ι) :
    (univ.sum fun k => (R.N k (R.star j) a : ℤ) * (R.N i k l : ℤ)) =
    (univ.sum fun b => (R.N i a b : ℤ) * (R.N l (R.star j) b : ℤ)) := by
  have h1 : ∀ k, (R.N i k l : ℤ) = (R.N (R.star i) l k : ℤ) := by
    intro k; exact_mod_cast R.N_star_transpose i k l
  simp_rw [h1, mul_comm ((R.N _ (R.star j) a : ℤ)) _]
  have h_assoc : (univ.sum fun k => (R.N (R.star i) l k : ℤ) * (R.N k (R.star j) a : ℤ)) =
    (univ.sum fun m => (R.N l (R.star j) m : ℤ) * (R.N (R.star i) m a : ℤ)) := by
    exact_mod_cast R.assoc (R.star i) l (R.star j) a
  rw [h_assoc]
  have h2 : ∀ m, (R.N (R.star i) m a : ℤ) = (R.N i a m : ℤ) := by
    intro m
    have := R.N_star_transpose (R.star i) m a
    rw [R.star_star] at this
    exact_mod_cast this
  simp_rw [h2]
  congr 1; ext b; ring

/-- Associativity of the right `K₀`-action: `(m ▹ s) ▹ r = m ▹ (s ⋆ r)`. -/
theorem k0ActRight_mul_assoc (m s r : ι → ℤ) :
    R.k0ActRight (R.k0ActRight m s) r = R.k0ActRight m (R.grMul s r) := by
  funext l
  simp only [k0ActRight, grMul]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]


  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]

  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]

  congr 1; ext a; congr 1; ext j; congr 1; ext p

  trans m a * s j * r p * ∑ x, (R.N x (R.star j) a : ℤ) * (R.N l (R.star p) x : ℤ)
  · rw [Finset.mul_sum]; congr 1; ext x; ring
  trans m a * s j * r p * ∑ x, (R.N j p x : ℤ) * (R.N l (R.star x) a : ℤ)
  · rw [R.inner_sum_k0ActRight_assoc a j p l]
  · rw [Finset.mul_sum]; congr 1; ext x; ring

/-- Bimodule compatibility: the left action by `Gr(R)` commutes with the right action,
namely `r ⋆ (m ▹ s) = (r ⋆ m) ▹ s`. -/
theorem k0_bimodule_compat (r : ι → ℤ) (m : ι → ℤ) (s : ι → ℤ) :
    R.grMul r (R.k0ActRight m s) = R.k0ActRight (R.grMul r m) s := by
  funext l
  simp only [grMul, k0ActRight]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]


  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]


  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]

  congr 1; ext i; congr 1; ext a; congr 1; ext j

  trans r i * m a * s j * ∑ x, (R.N x (R.star j) a : ℤ) * (R.N i x l : ℤ)
  · rw [Finset.mul_sum]; congr 1; ext x; ring
  trans r i * m a * s j * ∑ x, (R.N i a x : ℤ) * (R.N l (R.star j) x : ℤ)
  · rw [R.inner_sum_bimodule a j i l]
  · rw [Finset.mul_sum]; congr 1; ext x; ring

namespace K0Group

variable {R : FusionRing ι}

/-- Left action of the Grothendieck ring `Gr(R)` on `K₀(R)` via `k0ActLeft`. -/
instance instSMulLeft : SMul (GrRingOf R) (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActLeft r.coeff m.coeff⟩⟩

/-- Coefficients of the left scalar product are computed by `k0ActLeft`. -/
@[simp] lemma smul_left_coeff (r : GrRingOf R) (m : K0Group R) (k : ι) :
    (r • m).coeff k = R.k0ActLeft r.coeff m.coeff k := rfl

/-- `K₀(R)` is a left module over the Grothendieck ring `Gr(R)`. -/
instance instModule : Module (GrRingOf R) (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActLeft R.grOne m.coeff k = m.coeff k
    rw [R.k0ActLeft_eq_grMul, R.grMul_one_left]
  mul_smul r s m := by
    ext k
    show R.k0ActLeft (R.grMul r.coeff s.coeff) m.coeff k =
         R.k0ActLeft r.coeff (R.k0ActLeft s.coeff m.coeff) k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActLeft r.coeff (fun _ => 0) k = 0
    rw [R.k0ActLeft_eq_grMul, R.grMul_zero]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActLeft r.coeff (fun k => m₁.coeff k + m₂.coeff k) k =
         R.k0ActLeft r.coeff m₁.coeff k + R.k0ActLeft r.coeff m₂.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_left_distrib]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActLeft (fun k => r₁.coeff k + r₂.coeff k) m.coeff k =
         R.k0ActLeft r₁.coeff m.coeff k + R.k0ActLeft r₂.coeff m.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_right_distrib]
  zero_smul m := by
    ext k
    show R.k0ActLeft (fun _ => 0) m.coeff k = 0
    rw [R.k0ActLeft_eq_grMul, R.grZero_mul]

/-- Right action of `Gr(R)ᵐᵒᵖ` on `K₀(R)` via `k0ActRight`. -/
instance instSMulRight : SMul (GrRingOf R)ᵐᵒᵖ (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActRight m.coeff r.unop.coeff⟩⟩

/-- Coefficients of the right scalar product are computed by `k0ActRight`. -/
@[simp] lemma smul_right_coeff (r : (GrRingOf R)ᵐᵒᵖ) (m : K0Group R) (k : ι) :
    (r • m).coeff k = R.k0ActRight m.coeff r.unop.coeff k := rfl

/-- `K₀(R)` is a right module over the Grothendieck ring `Gr(R)`, presented as a left module
over `Gr(R)ᵐᵒᵖ`. -/
instance instModuleOp : Module (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActRight m.coeff R.grOne k = m.coeff k
    rw [R.k0ActRight_one]
  mul_smul r s m := by
    ext k

    change R.k0ActRight m.coeff (R.grMul s.unop.coeff r.unop.coeff) k =
           R.k0ActRight (R.k0ActRight m.coeff s.unop.coeff) r.unop.coeff k
    rw [← R.k0ActRight_mul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActRight (fun _ => 0) r.unop.coeff k = 0
    rw [R.k0ActRight_zero_left]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActRight (fun k => m₁.coeff k + m₂.coeff k) r.unop.coeff k =
         R.k0ActRight m₁.coeff r.unop.coeff k +
           R.k0ActRight m₂.coeff r.unop.coeff k
    rw [R.k0ActRight_add_left]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActRight m.coeff (fun k => r₁.unop.coeff k + r₂.unop.coeff k) k =
         R.k0ActRight m.coeff r₁.unop.coeff k +
           R.k0ActRight m.coeff r₂.unop.coeff k
    rw [R.k0ActRight_add_right]
  zero_smul m := by
    ext k
    show R.k0ActRight m.coeff (fun _ => 0) k = 0
    rw [R.k0ActRight_zero_right]

/-- The left and right actions of the Grothendieck ring on `K₀(R)` commute, equipping it
with a `Gr(R)`-bimodule structure. -/
instance instSMulCommClass :
    SMulCommClass (GrRingOf R) (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  smul_comm r s m := by
    ext l
    show R.k0ActLeft r.coeff (R.k0ActRight m.coeff s.unop.coeff) l =
         R.k0ActRight (R.k0ActLeft r.coeff m.coeff) s.unop.coeff l
    rw [R.k0ActLeft_eq_grMul, R.k0ActLeft_eq_grMul]
    exact congr_fun (R.k0_bimodule_compat r.coeff m.coeff s.unop.coeff) l

end K0Group

/-- Proposition 1.47.1 (EGNO). For a fusion ring `R`, the Grothendieck group `K₀(R)` carries a
canonical bimodule structure over the Grothendieck ring `Gr(R)`. -/
theorem prop_1_47_1 :
    SMulCommClass (GrRingOf R) (GrRingOf R)ᵐᵒᵖ (K0Group R) :=
  K0Group.instSMulCommClass

end FusionRing
