/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.KahlerManifolds
import Atlas.GeometryOfManifolds.code.AdvancedKahler

set_option autoImplicit false

open DifferentialFormSpace


/-- Data witnessing the Hopf surface: a compact complex manifold with $H^2$ trivial and which admits no symplectic structure. -/
structure HopfSurfaceData where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  J : @AlmostComplexStr Ω VF inst
  nij : @NijenhuisTensor Ω VF inst J
  integrable : @IsIntegrable Ω VF inst J nij
  h2_trivial : ∀ (ω : Ω 2), inst.d ω = 0 → ∃ (β : Ω 1), inst.d β = ω
  not_symplectic : ¬ Nonempty (@SymplecticManifold Ω VF inst)


/-- Data witnessing the $4$-sphere $S^4$: a compact manifold which admits no symplectic structure (every closed $2$-form is exact, so $\omega^2$ cannot be a volume form). -/
structure S4Data where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  compact : @IsCompactSymplectic Ω VF inst
  h2_trivial : ∀ (α : Ω 2), inst.d α = 0 → ∃ (β : Ω 1), α = inst.d β


/-- The fundamental group $\Gamma$ of the Kodaira–Thurston manifold, presented as quadruples $(a,b,c,d) \in \mathbb{Z}^4$ with a twisted multiplication. -/
structure KTGamma where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace KTGamma

/-- Twisted group multiplication on `KTGamma`: $(a,b,c,d)(a',b',c',d') = (a+a',\,b+b',\,c+c'+bd',\,d+d')$. -/
def mul' (g h : KTGamma) : KTGamma :=
  ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.b * h.d, g.d + h.d⟩

/-- Identity element of `KTGamma`. -/
def one' : KTGamma := ⟨0, 0, 0, 0⟩

/-- Group inverse in `KTGamma`. -/
def inv' (g : KTGamma) : KTGamma :=
  ⟨-g.a, -g.b, -g.c + g.b * g.d, -g.d⟩

/-- Extensionality for `KTGamma`: two elements are equal iff all four components agree. -/
@[ext] theorem ext {g h : KTGamma} (ha : g.a = h.a) (hb : g.b = h.b)
    (hc : g.c = h.c) (hd : g.d = h.d) : g = h := by
  cases g; cases h; simp_all

instance : Group KTGamma where
  mul := mul'
  one := one'
  inv := inv'
  mul_assoc a b c := by
    show mul' (mul' a b) c = mul' a (mul' b c)
    simp only [mul']; ext <;> ring
  one_mul a := by
    show mul' one' a = a
    simp only [mul', one']; ext <;> simp
  mul_one a := by
    show mul' a one' = a
    simp only [mul', one']; ext <;> simp
  inv_mul_cancel a := by
    show mul' (inv' a) a = one'
    simp only [mul', one', inv']; ext <;> ring

/-- Unfold the `Group` multiplication on `KTGamma` to `mul'`. -/
@[simp] lemma mul_def (g h : KTGamma) : g * h = mul' g h := rfl
/-- Unfold the identity of `KTGamma` to `one'`. -/
@[simp] lemma one_def : (1 : KTGamma) = one' := rfl
/-- Unfold the inverse of `KTGamma` to `inv'`. -/
@[simp] lemma inv_def (g : KTGamma) : g⁻¹ = inv' g := rfl

/-- The "third generator" $(0,0,1,0) \in \Gamma$, which lies in the commutator subgroup. -/
def generator3 : KTGamma := mk 0 0 1 0

/-- `generator3` equals the commutator $[(0,1,0,0), (0,0,0,1)]$ in $\Gamma$. -/
theorem generator3_eq_commutator :
    generator3 = mk 0 1 0 0 * mk 0 0 0 1 * (mk 0 1 0 0)⁻¹ * (mk 0 0 0 1)⁻¹ := by
  ext <;> simp [generator3, mul', inv']

/-- In the abelianization $\Gamma^{\mathrm{ab}}$, the image of `generator3` is trivial. -/
theorem of_generator3_eq_one : Abelianization.of generator3 = 1 := by
  rw [generator3_eq_commutator, map_mul, map_mul, map_mul, map_inv, map_inv]
  simp [mul_assoc, mul_inv_cancel]

/-- The $c$-component of $\Gamma$ is killed in the abelianization for every $c \in \mathbb{Z}$. -/
theorem of_c_component_trivial (c : ℤ) :
    Abelianization.of (mk 0 0 c 0) = (1 : Abelianization KTGamma) := by
  induction c using Int.induction_on with
  | zero => change Abelianization.of 1 = 1; exact map_one _
  | succ n ih =>
    have : mk 0 0 (n + 1) 0 = mk 0 0 n 0 * generator3 := by
      ext <;> simp [mul', generator3]

    rw [this, map_mul, ih, of_generator3_eq_one, mul_one]
  | pred n ih =>
    have : mk 0 0 (-↑n - 1) 0 = mk 0 0 (-↑n) 0 * generator3⁻¹ := by
      ext <;> simp [mul', inv', generator3]; ring

    rw [this, map_mul, ih, map_inv, of_generator3_eq_one, inv_one, mul_one]

/-- In $\Gamma^{\mathrm{ab}}$, the class of $(a,b,c,d)$ equals that of $(a,b,0,d)$. -/
theorem of_eq_of_drop_c (a b c d : ℤ) :
    Abelianization.of (mk a b c d) = Abelianization.of (mk a b 0 d) := by
  have : mk a b c d = mk a b 0 d * mk 0 0 c 0 := by ext <;> simp [mul']
  rw [this, map_mul, of_c_component_trivial, mul_one]

/-- The projection homomorphism $\Gamma \to \mathbb{Z}^3$ sending $(a,b,c,d) \mapsto (a,b,d)$. -/
def projHom : KTGamma →* Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ where
  toFun g := (Multiplicative.ofAdd g.a, Multiplicative.ofAdd g.b, Multiplicative.ofAdd g.d)
  map_one' := by simp [one']
  map_mul' g h := by
    simp only [mul_def, mul']
    ext <;> simp [ofAdd_add]

/-- The induced homomorphism $\Gamma^{\mathrm{ab}} \to \mathbb{Z}^3$ from `projHom`. -/
def liftedProj :
    Abelianization KTGamma →* Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ :=
  Abelianization.lift projHom

/-- A section $\mathbb{Z}^3 \to \Gamma^{\mathrm{ab}}$ of `liftedProj`, sending $(x,y,z)$ to the class of $(x,y,0,z)$. -/
def sectionHom :
    Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ →* Abelianization KTGamma where
  toFun p := Abelianization.of
    (mk (Multiplicative.toAdd p.1) (Multiplicative.toAdd p.2.1) 0 (Multiplicative.toAdd p.2.2))
  map_one' := by change Abelianization.of 1 = 1; exact map_one _
  map_mul' p q := by
    show Abelianization.of _ = Abelianization.of _ * Abelianization.of _
    rw [← map_mul, mul_def, mul']
    exact (of_eq_of_drop_c _ _ _ _).symm

/-- The composite $\mathbb{Z}^3 \xrightarrow{\mathrm{sec}} \Gamma^{\mathrm{ab}} \xrightarrow{\mathrm{proj}} \mathbb{Z}^3$ is the identity. -/
theorem liftedProj_sectionHom : liftedProj.comp sectionHom = MonoidHom.id _ := by
  apply MonoidHom.ext; intro ⟨x, y, z⟩
  simp [liftedProj, sectionHom, projHom]

/-- The composite $\Gamma^{\mathrm{ab}} \xrightarrow{\mathrm{proj}} \mathbb{Z}^3 \xrightarrow{\mathrm{sec}} \Gamma^{\mathrm{ab}}$ is the identity. -/
theorem sectionHom_liftedProj : sectionHom.comp liftedProj = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext; intro ⟨a, b, c, d⟩
  simp [liftedProj, sectionHom, projHom]
  exact (of_eq_of_drop_c a b c d).symm


/-- The abelianization of the Kodaira–Thurston fundamental group is $\Gamma^{\mathrm{ab}} \cong \mathbb{Z}^3$. -/
noncomputable def abelianizationEquiv :
    Abelianization KTGamma ≃*
      Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ :=
  MulEquiv.ofBijective liftedProj
    ⟨fun x y h => by
      have := congr_arg sectionHom h
      simp only [← MonoidHom.comp_apply, sectionHom_liftedProj, MonoidHom.id_apply] at this
      exact this,
     fun z => ⟨sectionHom z, by
      simp only [← MonoidHom.comp_apply, liftedProj_sectionHom, MonoidHom.id_apply]⟩⟩

end KTGamma


/-- Typeclass recording the rank of a free abelian group $G$. -/
class FreeAbelianRank (G : Type*) [CommGroup G] where
  rank : ℕ

/-- The free abelian group $\mathbb{Z}$ has rank $1$. -/
instance freeAbelianRank_Z : FreeAbelianRank (Multiplicative ℤ) where
  rank := 1

/-- The rank of a product of free abelian groups is the sum of the ranks. -/
instance freeAbelianRank_prod {A B : Type*} [CommGroup A] [CommGroup B]
    [FreeAbelianRank A] [FreeAbelianRank B] :
    FreeAbelianRank (A × B) where
  rank := FreeAbelianRank.rank (G := A) + FreeAbelianRank.rank (G := B)

/-- The free abelian group $\mathbb{Z}^3$ has rank $3$. -/
theorem freeAbelianRank_Z3 :
    FreeAbelianRank.rank (G := Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ) = 3 := by
  rfl

/-- The free rank of the abelianization $\Gamma^{\mathrm{ab}}$ of the Kodaira–Thurston group. -/
def KTGamma.abelianizationFreeRank : ℕ :=
  FreeAbelianRank.rank (G := Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ)

/-- Lemma 1: $H_1(M, \mathbb{Z}) \cong \mathbb{Z}^3$ for the Kodaira–Thurston manifold; equivalently $\Gamma^{\mathrm{ab}}$ has free rank $3$. -/
theorem KTGamma.abelianizationFreeRank_eq_three :
    KTGamma.abelianizationFreeRank = 3 := by
  unfold KTGamma.abelianizationFreeRank
  exact freeAbelianRank_Z3


/-- Data of the Kodaira–Thurston manifold: a compact symplectic $4$-manifold with $b_1 = 3$ (odd), hence not Kähler. -/
structure KodairaThurstonManifold where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  compact : @IsCompactSymplectic Ω VF inst
  bracket : @HasLieBracket Ω VF inst
  symplectic : @SymplecticManifold Ω VF inst
  J : @AlmostComplexStr Ω VF inst
  hodge : @HasHodgeNumbers Ω VF inst
  betti_one_eq_three : hodge.betti 1 = 3


/-- The first Betti number of the Kodaira–Thurston manifold is $b_1(M) = 3$. -/
theorem kodaira_thurston_first_betti (M : KodairaThurstonManifold) :
    M.hodge.betti 1 = 3 :=
  M.betti_one_eq_three

/-- The Kodaira–Thurston manifold is not Kähler: a compact Kähler manifold has even odd Betti numbers, but $b_1 = 3$ is odd. -/
theorem kodaira_thurston_not_kahler
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hcs : IsCompactSymplectic Ω VF]
    [hbr : HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    [hH : @HasHodgeNumbers Ω VF inst]
    (hb1 : hH.betti 1 = 3) :
    ¬ IsKahler S J := by
  intro hK


  have ⟨m, hm⟩ := compact_kahler_odd_betti_even S J hK 1 (by norm_num)

  omega


/-- Data witnessing the connected sum $\mathbb{CP}^2 \# \mathbb{CP}^2 \# \mathbb{CP}^2$: a smooth $4$-manifold which is neither symplectic nor complex (no integrable almost complex structure). -/
structure CP2TripleSumData where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  J : @AlmostComplexStr Ω VF inst
  not_symplectic : ¬ Nonempty (@SymplecticManifold Ω VF inst)
  not_complex : ∀ (J' : @AlmostComplexStr Ω VF inst)
       (nij : @NijenhuisTensor Ω VF inst J'),
       ¬ @IsIntegrable Ω VF inst J' nij
