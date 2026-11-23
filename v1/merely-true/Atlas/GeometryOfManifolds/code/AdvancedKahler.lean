/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.KahlerManifolds
import Atlas.GeometryOfManifolds.code.ConnectionsCurvature

set_option autoImplicit false

open DifferentialFormSpace


/-- A typeclass packaging the Hodge numbers $h^{p,q}(M)$ and Betti numbers $b_k(M)$
of a compact Kähler manifold, together with the basic symmetries they satisfy:
conjugation symmetry $h^{p,q} = h^{q,p}$, Hodge-star symmetry
$h^{p,q} = h^{n-q,\,n-p}$, and the link $b_k = \sum_{p+q=k} h^{p,q}$ from the
Hodge decomposition $H^k_{dR}(M,\mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}_{\bar\partial}(M)$. -/
class HasHodgeNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  complexDim : ℕ
  hodge : ℕ → ℕ → ℕ
  conjugation_symmetry : ∀ p q, hodge p q = hodge q p
  star_symmetry : ∀ p q, hodge p q = hodge (complexDim - q) (complexDim - p)
  betti : ℕ → ℕ
  betti_hodge_link : ∀ (k : ℕ),
    betti k = (Finset.range (k + 1)).sum (fun p => hodge p (k - p))

/-- Conjugation symmetry of Hodge numbers on a compact Kähler manifold:
$h^{p,q}(M) = h^{q,p}(M)$. -/
theorem hodge_conjugation_symmetry
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    [hH : @HasHodgeNumbers Ω VF inst]
    (p q : ℕ) :
    hH.hodge p q = hH.hodge q p :=
  hH.conjugation_symmetry p q


/-- Hodge decomposition consequence: on a compact Kähler manifold the $k$-th Betti
number decomposes as a sum of Hodge numbers, $b_k(M) = \sum_{p+q=k} h^{p,q}(M)$. -/
theorem betti_eq_sum_hodge
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    [hH : @HasHodgeNumbers Ω VF inst]
    (k : ℕ) :
    hH.betti k = (Finset.range (k + 1)).sum (fun p => hH.hodge p (k - p)) :=
  hH.betti_hodge_link k


/-- On a compact Kähler manifold, all odd Betti numbers are even:
for odd $k$, $b_k(M) = 2m$ for some $m \in \mathbb{N}$. This follows from the
Hodge decomposition together with the conjugation symmetry $h^{p,q} = h^{q,p}$. -/
theorem compact_kahler_odd_betti_even
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (k : ℕ) (hk : k % 2 = 1)
    [hH : @HasHodgeNumbers Ω VF inst] :
    ∃ (m : ℕ), hH.betti k = 2 * m := by
  rw [betti_eq_sum_hodge S J hK k]


  set f := (fun p => hH.hodge p (k - p))

  have hf : ∀ p, p ≤ k → f p = f (k - p) := by
    intro p hp
    simp only [f]
    have h1 : k - (k - p) = p := Nat.sub_sub_self hp
    rw [hodge_conjugation_symmetry S J hK p (k - p)]
    congr 1; omega

  have ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  subst hj
  have hlen : 2 * j + 1 + 1 = (j + 1) + (j + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  suffices h : (Finset.range (j + 1)).sum (fun x => f (j + 1 + x)) =
               (Finset.range (j + 1)).sum f by
    rw [h]; exact ⟨_, (two_mul _).symm⟩
  apply Finset.sum_bij' (fun a _ => j - a) (fun a _ => j - a)
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hp : j + 1 + a ≤ 2 * j + 1 := by omega
    rw [hf (j + 1 + a) hp]
    congr 1
    omega


/-- A cohomology structure equipped with iterated Lefschetz operators
$L^m : H^k(M) \to H^{k+2m}(M)$. On a compact Kähler manifold these
are the linear maps appearing in the Hard Lefschetz theorem. -/
class HasCohomologyWithLefschetz
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomology Ω VF inst where
  L_map : ∀ (k m : ℕ),
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ) (H k) (H (k + 2 * m))
      (H_addCommGroup k).toAddCommMonoid (H_addCommGroup (k + 2 * m)).toAddCommMonoid
      (H_module k) (H_module (k + 2 * m))


/-- A projective embedding datum for a symplectic manifold $(M, \omega)$:
an embedding $\iota : M \hookrightarrow N$ into a target carrying a closed
form $\omega_N$ such that $\iota^* \omega_N = \omega + d\alpha$ for some $\alpha \in \Omega^1(M)$.
This is the existence half of the Kodaira embedding theorem. -/
class HasProjectiveEmbedding
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  embeddingDim : ℕ
  Ω_target : ℕ → Type*
  VF_target : Type*
  inst_target : DifferentialFormSpace Ω_target VF_target
  embedding : DFSMorphism Ω VF Ω_target VF_target
  targetForm : Ω_target 2
  targetForm_closed : inst_target.d targetForm = 0
  pullback_cohomologous : ∃ (α : Ω 1),
    @DFSMorphism.pullback _ _ _ _ inst inst_target embedding (p := 2) targetForm =
      S.ω + inst.d α

/-- Propositional version of `HasProjectiveEmbedding`: there exists a target
differential form space, an embedding, and a closed form whose pullback represents
$[\omega]$ in de Rham cohomology. -/
def HasProjectiveEmbeddingProp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Prop :=
  ∃ (_N : ℕ) (Ω_target : ℕ → Type) (VF_target : Type)
    (inst_target : DifferentialFormSpace Ω_target VF_target)
    (emb : DFSMorphism Ω VF Ω_target VF_target)
    (targetForm : Ω_target 2),
    inst_target.d targetForm = 0 ∧
    ∃ (α : Ω 1), @DFSMorphism.pullback _ _ _ _ inst inst_target emb (p := 2) targetForm =
      S.ω + inst.d α

/-- The symplectic class $[\omega] \in H^2(M, \mathbb{R})$ is integral and
nontrivial: no integer multiple $k\omega$ ($k \neq 0$) is exact. This is the
hypothesis of the Kodaira embedding theorem. -/
class IsIntegralClass
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  not_exact : ∀ (α : Ω 1), inst.d α ≠ S.ω
  smul_not_exact : ∀ (k : ℤ), k ≠ 0 → ∀ (α : Ω 1), inst.d α ≠ k • S.ω


/-- Holomorphic bundle structure: a $(0,1)$-connection operator
$\bar\partial_E : \Omega^{0,q}(E) \to \Omega^{0,q+1}(E)$ on $E$-valued forms
satisfying the integrability condition $\bar\partial_E^2 = 0$. -/
structure HolomorphicBundleStr
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (Sections : Type*) [AddCommGroup Sections]
    (FormsWithValues : ℕ → Type*) [∀ q, AddCommGroup (FormsWithValues q)] where
  delbar_E : ∀ {q : ℕ}, FormsWithValues q → FormsWithValues (q + 1)
  delbar_sq : ∀ {q : ℕ} (σ : FormsWithValues q), delbar_E (delbar_E σ) = 0
  delbar_add : ∀ {q : ℕ} (σ τ : FormsWithValues q),
    delbar_E (σ + τ) = delbar_E σ + delbar_E τ

/-- A holomorphic section of a holomorphic bundle: a section $\sigma$ such that
$\bar\partial_E \sigma = 0$. -/
structure HolomorphicSection
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Sections : Type*} [AddCommGroup Sections]
    {FormsWithValues : ℕ → Type*} [∀ q, AddCommGroup (FormsWithValues q)]
    (hol : HolomorphicBundleStr (inst := inst) Sections FormsWithValues)
    (toSections : Sections → FormsWithValues 0) where
  section_ : Sections
  is_holomorphic : hol.delbar_E (toSections section_) = 0


/-- A Hermitian metric datum on a line bundle, represented abstractly by an
invertible element $h \in R$ in a ring of bundle endomorphisms. -/
structure HermitianBundleMetric (R : Type*) [Ring R] where
  h : R
  h_inv : R
  h_inv_left : h_inv * h = 1
  h_right_inv : h * h_inv = 1


/-- Data attached to a Hermitian line bundle: a closed curvature $2$-form
$R^\nabla \in \Omega^2(M)$ representing $2\pi \cdot c_1(L) \in H^2(M, \mathbb{R})$. -/
structure LineBundleData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  curvature : Ω 2
  curvature_closed : inst.d curvature = 0


/-- A line bundle $L$ is ample if its curvature form is nondegenerate, i.e.
$X \mapsto \iota_X R^\nabla$ is injective. Geometrically this expresses
positivity of $c_1(L)$. -/
class IsAmple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : LineBundleData (inst := inst)) : Prop where
  positive_curvature : Function.Injective (fun (X : VF) => inst.ι X L.curvature)

/-- A line bundle is very ample if its global sections separate points,
giving an embedding into projective space; the curvature is still positive
and there exist nontrivial sections distinguishing points. -/
class IsVeryAmple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : LineBundleData (inst := inst)) : Prop where
  sections_give_embedding : Function.Injective (fun (X : VF) => inst.ι X L.curvature)
  has_sections : ∃ (s₁ s₂ : Ω 0), s₁ ≠ s₂ ∧ inst.d s₁ ≠ inst.d s₂


/-- A $2$-form $\omega$ is a Kähler form if it is closed ($d\omega = 0$) and
nondegenerate ($X \mapsto \iota_X \omega$ is injective). -/
class IsKahlerForm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (ω : Ω 2) : Prop where
  closed : inst.d ω = 0
  nondegenerate : Function.Injective (fun (X : VF) => inst.ι X ω)


/-- An approximately-holomorphic family of sections of a line bundle $L$:
for each $k$ and each point $p$, a section $s_{k,p} \in \Omega^0(L^k)$.
Used in Donaldson's construction of approximately holomorphic sections. -/
structure ApproxHolomorphicSectionFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  L : LineBundleData (inst := inst)
  section_ : ℕ → VF → Ω 0


/-- An $L^2$-norm structure on differential forms: a seminorm
$\|\cdot\|_{L^2}$ on each $\Omega^p$ satisfying the triangle inequality and
the scaling law $\|r\cdot\alpha\|_{L^2} = |r|\cdot\|\alpha\|_{L^2}$. -/
class L2NormSpace
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  l2norm : ∀ {p : ℕ}, Ω p → ℝ
  l2norm_nonneg : ∀ {p : ℕ} (α : Ω p), 0 ≤ l2norm α
  l2norm_add : ∀ {p : ℕ} (α β : Ω p), l2norm (α + β) ≤ l2norm α + l2norm β
  l2norm_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), l2norm (r • α) = |r| * l2norm α

/-- A scale-weighted $C^r$ sup-norm on sections: for each scale $k$ and order
$r$, a seminorm $\|s\|_{k,r}$ controlling derivatives up to order $r$ with
weights appropriate to the scale-$k$ geometry (used in Donaldson estimates). -/
class WeightedDerivSupNorm
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  weighted_supnorm : (k : ℕ) → (r : ℕ) → Ω 0 → ℝ
  weighted_supnorm_nonneg : ∀ (k r : ℕ) (s : Ω 0), 0 ≤ weighted_supnorm k r s
  weighted_supnorm_add : ∀ (k r : ℕ) (s t : Ω 0),
    weighted_supnorm k r (s + t) ≤ weighted_supnorm k r s + weighted_supnorm k r t
  weighted_supnorm_neg : ∀ (k r : ℕ) (s : Ω 0),
    weighted_supnorm k r (-s) ≤ weighted_supnorm k r s

/-- Pointwise evaluation of $0$-forms (i.e. functions/sections): a map
$(x, s) \mapsto |s(x)|$ taking nonnegative values and bounded by the
weighted $C^0$ sup-norm. -/
class PointwiseEval
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF] where
  peval : VF → Ω 0 → ℝ
  peval_nonneg : ∀ (x : VF) (s : Ω 0), 0 ≤ peval x s
  peval_le_supnorm : ∀ (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (x : VF) (k : ℕ) (s : Ω 0), peval x s ≤ wdn.weighted_supnorm k 0 s

/-- A distance function on the manifold (representing the Riemannian/Kähler
metric distance), satisfying the standard axioms of a pseudo-metric:
nonnegativity, symmetry, $d(p,p) = 0$, and the triangle inequality. -/
class ManifoldDist
    (VF : Type*) where
  mdist : VF → VF → ℝ
  mdist_nonneg : ∀ (p q : VF), 0 ≤ mdist p q
  mdist_symm : ∀ (p q : VF), mdist p q = mdist q p
  mdist_self : ∀ (p : VF), mdist p p = 0
  mdist_triangle : ∀ (p q r : VF), mdist p r ≤ mdist p q + mdist q r

/-- A section family is uniformly bounded if its derivatives in every weighted
$C^r$ norm are bounded uniformly in $k$ and $p$. -/
structure IsUniformlyBounded
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  deriv_bounded : ∃ (wdn : WeightedDerivSupNorm Ω (inst := inst)),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- A section family is approximately holomorphic: $\bar\partial s_{k,p}$ is
exact and its $L^2$-norm decays like $1/\sqrt{k}$, which is the precise
Donaldson approximate-holomorphicity condition. -/
structure IsApproxHolomorphic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (fam.section_ k p) = inst.d β
  delbar_l2_decay : ∃ (l2 : L2NormSpace Ω (inst := inst)) (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C / Real.sqrt (k : ℝ)

/-- A section family is uniformly concentrated: distinct base points give
distinct sections, the sections exhibit Gaussian decay
$|s_{k,p}(x)| \lesssim (1 + \sqrt{k}\,d(p,x))^N e^{-\lambda k\, d(p,x)^2}$
away from $p$, and derivative norms are uniformly bounded. -/
structure IsUniformlyConcentrated
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q → fam.section_ k p ≠ fam.section_ k q
  gaussian_decay : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (C_gd lam : ℝ) (N : ℕ),
    C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (fam.section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)
  deriv_norm_bounded : ∃ (wdn : WeightedDerivSupNorm Ω (inst := inst)),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- A section family is genuinely holomorphic if $\bar\partial s_{k,p} = 0$
for every $k$ and $p$. -/
structure IsHolomorphicFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  holomorphic : ∀ (k : ℕ) (p : VF),
    dol.delbar (fam.section_ k p) = 0


/-- Existence axiom: a compact symplectic manifold equipped with a compatible
almost complex structure admits a family of approximately-holomorphic sections
that are simultaneously uniformly bounded, approximately holomorphic, uniformly
concentrated, and locally bounded below by Gaussian peaks. -/
class HasGaussianSections
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] where
  sections_exist :
    ∀ (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
      (_hcompat : IsCompatibleACS S J),
    ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧

      (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
        ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p))


/-- Abstract data for a Weitzenböck decomposition $\bar\square = D + R$, where
$D$ is a positive second-order operator and $R$ is a $0$-th order curvature
term acting on a vector space of $k$-forms; both are additive. -/
structure WeitzenboeckDecomposition
    (V : Type*) [AddCommGroup V] where
  D : V → V
  R_term : V → V
  k : ℕ
  D_add : ∀ a b, D (a + b) = D a + D b
  R_add : ∀ a b, R_term (a + b) = R_term a + R_term b


/-- A Green operator for the $\bar\partial$-Laplacian: produces a correction
$\xi = G(s)$ such that $s + \xi$ is holomorphic and the $L^2$-norm of $\xi$
is controlled by $1/\sqrt{k}$ times the $L^2$-norm of $\bar\partial s$,
encoding the spectral gap of $\bar\square$ on $L^k$. -/
class HasGreenOperator
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) where
  greenCorrection : ℕ → Ω 0 → Ω 0
  green_holomorphic : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    dol.delbar (s + greenCorrection k s) = 0

  green_l2_sq_bound : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    ∃ (c : ℝ), c > 0 ∧
      l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
        c / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))


/-- Helper: from a squared bound $a^2 \le (C/k) b^2$ with $a, b \ge 0$ and
$C/k \ge 0$, conclude the linear bound $a \le \sqrt{C/k}\, b$. -/
theorem l2_bound_from_squared_bound
    {a b C : ℝ} {k : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCk : 0 ≤ C / (k : ℝ))
    (hsq : a * a ≤ C / (k : ℝ) * (b * b)) :
    a ≤ Real.sqrt (C / (k : ℝ)) * b := by
  have h1 : Real.sqrt (a * a) ≤ Real.sqrt (C / (k : ℝ) * (b * b)) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul_self ha] at h1
  rw [Real.sqrt_mul hCk, Real.sqrt_mul_self hb] at h1
  exact h1

/-- Helper algebraic identity: $\sqrt{C/k} = \sqrt{C}/\sqrt{k}$ for $C > 0$
and $k \ne 0$. -/
theorem sqrt_div_eq_div_sqrt {C : ℝ} {k : ℕ} (hC : 0 < C) (_hk : k ≠ 0) :
    Real.sqrt (C / (k : ℝ)) = Real.sqrt C / Real.sqrt (k : ℝ) := by
  rw [Real.sqrt_div (le_of_lt hC)]


/-- The hypothesis that $\bar\partial s_{k,p}$ decays exponentially in
$k^{1/3}$: $\|\bar\partial s_{k,p}\|_{L^2} \le C e^{-\lambda k^{1/3}}$.
This is the form of cutoff-error bound used in Donaldson's argument. -/
structure HasGaussianDecayOfDelbar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  gaussian_decay : ∃ (lam : ℝ) (C : ℝ), lam > 0 ∧ C > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))

/-- Cauchy-type estimates for holomorphic sections: weighted $C^r$ norms of a
holomorphic section $\xi$ (with $\bar\partial \xi = 0$) are controlled by its
$L^2$-norm. -/
structure HasCauchyEstimates
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) : Prop where
  cauchy_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (ξ : Ω 0),
      dol.delbar ξ = 0 →
        wdn.weighted_supnorm k r ξ ≤ C_r * l2.l2norm ξ

/-- Quantitative form of uniform boundedness for a section family with respect
to an explicit weighted derivative sup-norm. -/
structure IsQuantUniformlyBounded
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  deriv_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- Quantitative form of approximate holomorphicity: $\bar\partial$ of each
section is exact and its $L^2$-norm satisfies the explicit $C/\sqrt{k}$ decay
bound. -/
structure IsQuantApproxHolomorphic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (fam.section_ k p) = inst.d β
  delbar_l2_bound : ∃ (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C / Real.sqrt (k : ℝ)

/-- Quantitative form of uniform concentration: distinct base points yield
distinct sections, derivative norms are uniformly bounded, and the sections
exhibit explicit Gaussian decay away from their peak. -/
structure IsQuantUniformlyConcentrated
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q →
    fam.section_ k p ≠ fam.section_ k q
  norm_bounded : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r
  gaussian_decay : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (C_gd lam : ℝ) (N : ℕ),
    C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (fam.section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)


/-- Two families on the same line bundle are exponentially close if all
weighted derivative differences decay like $e^{-\lambda k / 3}$. -/
structure IsExponentiallyClose
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam fam' : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  same_bundle : fam.L = fam'.L
  exp_close_all_derivs : ∃ (lam : ℝ), lam > 0 ∧
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C_r * Real.exp (-lam * (k : ℝ) / 3)


/-- Cube-root version of exponential closeness: the decay rate is
$e^{-\lambda k^{1/3}}$ instead of $e^{-\lambda k}$, which is the
natural rate provided by Donaldson's argument. -/
structure IsExponentiallyCloseCubeRoot
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam fam' : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  same_bundle : fam.L = fam'.L
  exp_close_all_derivs : ∃ (lam : ℝ), lam > 0 ∧
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))


/-- For $k \ge 1$, the cube root $k^{1/3}$ is bounded above by $k$. -/
lemma nat_rpow_one_third_le (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ ((1:ℝ)/3) ≤ (k : ℝ) := by
  calc (k : ℝ) ^ ((1:ℝ)/3) ≤ (k : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hk) (by linarith)
      _ = k := by simp [Real.rpow_one]

/-- Convexity-style comparison: $e^{-\lambda k / 3} \le e^{-(\lambda/3) k^{1/3}}$
for $\lambda > 0$ and all $k \in \mathbb{N}$, used to convert linear decay
into cube-root decay. -/
lemma exp_neg_linear_le_exp_neg_cuberoot (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    Real.exp (-lam * (k : ℝ) / 3) ≤ Real.exp (-(lam / 3) * (k : ℝ) ^ ((1:ℝ)/3)) := by
  apply Real.exp_le_exp.mpr
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hcr := nat_rpow_one_third_le k hk
    nlinarith [mul_le_mul_of_nonneg_left hcr (le_of_lt (div_pos hlam (by linarith : (0:ℝ) < 3)))]

/-- Linear exponential closeness implies cube-root exponential closeness:
the rate $e^{-\lambda k}$ dominates $e^{-(\lambda/3) k^{1/3}}$. -/
theorem IsExponentiallyClose.to_cube_root
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {wdn : WeightedDerivSupNorm Ω (inst := inst)}
    {fam fam' : ApproxHolomorphicSectionFamily (inst := inst)}
    (h : IsExponentiallyClose wdn fam fam') :
    IsExponentiallyCloseCubeRoot wdn fam fam' where
  same_bundle := h.same_bundle
  exp_close_all_derivs := by
    obtain ⟨lam, hlam_pos, h_all⟩ := h.exp_close_all_derivs
    refine ⟨lam / 3, div_pos hlam_pos (by linarith : (0:ℝ) < 3), ?_⟩
    intro r
    obtain ⟨C_r, hC_pos, h_bound⟩ := h_all r
    refine ⟨C_r, hC_pos, ?_⟩
    intro k p
    calc wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p)
        ≤ C_r * Real.exp (-lam * (k : ℝ) / 3) := h_bound k p
      _ ≤ C_r * Real.exp (-(lam / 3) * (k : ℝ) ^ ((1:ℝ)/3)) := by
          apply mul_le_mul_of_nonneg_left
          · exact exp_neg_linear_le_exp_neg_cuberoot lam hlam_pos k
          · exact le_of_lt hC_pos

/-- A section family has a uniform local lower bound: each section is nonzero,
its weighted $C^0$ norm is uniformly bounded below, and there is a uniform
lower bound on $|s_{k,p}(q)|$ when $d(p,q) \le 1/\sqrt{k}$ (the natural
scale-$k$ ball). -/
structure HasLocalLowerBound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  section_nonzero : ∀ (k : ℕ) (p : VF), fam.section_ k p ≠ 0
  lower_bound_exists : ∃ (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k 0 (fam.section_ k p) ≥ c
  ball_lower_bound : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ),
    c > 0 ∧
    ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
      c ≤ pe.peval q (fam.section_ k p)



/-- Combines a "large $k$" curvature bound (of the form $1/(k - C_{geom})$) with
a "small $k$" general bound to produce a single spectral-gap estimate
$\|G(s)\|^2 \le (c/k) \|\bar\partial s\|^2$ valid for all $k \ge 1$. -/
theorem spectral_gap_from_curvature_bound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] [HasLieBracket Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (greenCorrection : ℕ → Ω 0 → Ω 0)
    (C_geom : ℝ) (hC_pos : C_geom > 0)
    (hcurv_bound : ∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom →
      l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
        1 / ((k : ℝ) - C_geom) *
          (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))
    (hgeneral_bound : ∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0),
      ∃ (B : ℝ), B > 0 ∧
        l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
          B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) :
    ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
      ∃ (c : ℝ), c > 0 ∧
        l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
          c / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)) := by
  intro k hk s

  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)

  by_cases hkC : (k : ℝ) > C_geom
  ·

    have hbound := hcurv_bound k s hkC


    have hkC_pos : (k : ℝ) - C_geom > 0 := by linarith
    refine ⟨(k : ℝ) / ((k : ℝ) - C_geom), ?_, ?_⟩
    ·
      exact div_pos hk_pos hkC_pos
    ·
      have h_eq : 1 / ((k : ℝ) - C_geom) = ((k : ℝ) / ((k : ℝ) - C_geom)) / (k : ℝ) := by
        field_simp
      rw [h_eq] at hbound
      exact hbound
  ·
    push_neg at hkC
    obtain ⟨B, hB_pos, hB_bound⟩ := hgeneral_bound k hk s

    refine ⟨B * (k : ℝ), ?_, ?_⟩
    ·
      exact mul_pos hB_pos hk_pos
    ·
      have h_eq : B * (k : ℝ) / (k : ℝ) = B := by
        field_simp
      rw [h_eq]
      exact hB_bound





/-- Bundled input data for applying Green-operator corrections to a family of
approximately-holomorphic sections: a Green operator, a Gaussian decay bound
for $\bar\partial$, Cauchy estimates on the correction, an $L^2$-bound on the
correction, holomorphicity at $k=0$, and bundle-equality data. -/
structure GreenCorrectionInput
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  greenOp : HasGreenOperator Ω l2 dol
  gaussian_decay : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
  cauchy_estimates : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (s : Ω 0),
      wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
        C_r * l2.l2norm (greenOp.greenCorrection k s)
  correction_l2_exp_bound : ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (greenOp.greenCorrection k (fam.section_ k p)) ≤
        C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3))
  hol_at_zero : ∀ (p : VF),
    dol.delbar (fam.section_ 0 p + greenOp.greenCorrection 0 (fam.section_ 0 p)) = 0

  same_bundle_data : LineBundleData (inst := inst)
  corrected_bundle_eq : fam.L = same_bundle_data

/-- The Green-corrected section family: replaces each $s_{k,p}$ by
$s_{k,p} + G(s_{k,p})$, producing a (genuinely) holomorphic family on the
same line bundle. -/
noncomputable def correctedFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (gci : GreenCorrectionInput wdn l2 dol fam) :
    ApproxHolomorphicSectionFamily (inst := inst) :=
  { L := gci.same_bundle_data,
    section_ := fun k p => fam.section_ k p + gci.greenOp.greenCorrection k (fam.section_ k p) }

/-- The Green-corrected family is genuinely holomorphic: $\bar\partial$ of every
corrected section vanishes (using the Green operator's defining property for
$k \ne 0$ and the `hol_at_zero` hypothesis for $k = 0$). -/
theorem green_corrected_family_is_holomorphic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (gci : GreenCorrectionInput wdn l2 dol fam) :
    IsHolomorphicFamily dol (correctedFamily wdn l2 dol fam gci) := by
  constructor
  intro k p
  simp only [correctedFamily]
  by_cases hk : k = 0
  ·
    subst hk
    exact gci.hol_at_zero p
  ·
    exact gci.greenOp.green_holomorphic k hk (fam.section_ k p)

/-- The Green-corrected family is exponentially close (at the $k^{1/3}$ rate)
to the original family: combining the Cauchy estimates with the
exponential $L^2$-bound on the correction gives the required uniform
$\|s_{k,p} - s'_{k,p}\|_{k,r} \le C_r e^{-\lambda k^{1/3}}$ bound. -/
theorem green_correction_exp_close
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (gci : GreenCorrectionInput wdn l2 dol fam) :
    IsExponentiallyCloseCubeRoot wdn fam (correctedFamily wdn l2 dol fam gci) := by
  constructor
  ·
    exact gci.corrected_bundle_eq
  ·
    obtain ⟨C_l2, lam_l2, hCl2_pos, hlam_l2_pos, h_l2_bound⟩ := gci.correction_l2_exp_bound
    refine ⟨lam_l2, hlam_l2_pos, ?_⟩
    intro r
    obtain ⟨C_r, hCr_pos, h_cauchy⟩ := gci.cauchy_estimates r

    refine ⟨C_r * C_l2, mul_pos hCr_pos hCl2_pos, ?_⟩
    intro k p

    have h_diff : fam.section_ k p - (correctedFamily wdn l2 dol fam gci).section_ k p =
        -(gci.greenOp.greenCorrection k (fam.section_ k p)) := by
      simp only [correctedFamily]
      abel
    rw [h_diff]

    have h_neg := wdn.weighted_supnorm_neg k r (gci.greenOp.greenCorrection k (fam.section_ k p))

    have h_cauchy_k := h_cauchy k (fam.section_ k p)

    have h_l2_k := h_l2_bound k p

    calc wdn.weighted_supnorm k r (-(gci.greenOp.greenCorrection k (fam.section_ k p)))
        ≤ wdn.weighted_supnorm k r (gci.greenOp.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (gci.greenOp.greenCorrection k (fam.section_ k p)) := h_cauchy_k
      _ ≤ C_r * (C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left h_l2_k (le_of_lt hCr_pos)
      _ = C_r * C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring

/-- A "Donaldson correction" witness for a section family: a corrected
holomorphic family together with the proof that it is exponentially close
(cube-root rate) to the original. -/
structure HasHolomorphicCorrection
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where

  corrected_family : ApproxHolomorphicSectionFamily (inst := inst)
  is_holomorphic : IsHolomorphicFamily dol corrected_family
  is_exp_close : IsExponentiallyCloseCubeRoot wdn fam corrected_family

/-- The PDE infrastructure required to run the Green-correction construction:
a weighted derivative sup-norm, an $L^2$-norm, the Dolbeault operator, and a
recipe for producing `GreenCorrectionInput` for any section family. -/
class HasPDEInfrastructure
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] where
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  dol : DolbeaultOps (inst := inst)
  greenCorrection : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
    GreenCorrectionInput wdn l2 dol fam


/-- A uniform-in-norm constant $c_G > 0$ such that for every $k \ne 0$ and
$s \in \Omega^0$, $\|G(s)\|_{L^2}^2 \le (c_G/k)\, \|\bar\partial s\|_{L^2}^2$.
This expresses the spectral gap of $\bar\square$ uniformly across $L^k$. -/
structure UniformGreenL2Bound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (greenOp : ∀ (l2 : L2NormSpace Ω (inst := inst)) (dol : DolbeaultOps (inst := inst)),
      HasGreenOperator Ω l2 dol)
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) where
  c_G : ℝ
  c_G_pos : c_G > 0
  uniform_bound : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
    l2.l2norm ((greenOp l2 dol).greenCorrection k s) *
      l2.l2norm ((greenOp l2 dol).greenCorrection k s) ≤
      c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))

/-- Derives an exponential $L^2$-bound on the Green correction from a uniform
spectral-gap bound and a Gaussian decay bound on $\bar\partial s_{k,p}$: the
output bound is $\|G(s_{k,p})\|_{L^2} \le C_{L^2} e^{-\lambda k^{1/3}}$. -/
theorem derive_correction_l2_exp_bound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    {l2 : L2NormSpace Ω (inst := inst)}
    {dol : DolbeaultOps (inst := inst)}
    {greenOp : HasGreenOperator Ω l2 dol}
    {fam : ApproxHolomorphicSectionFamily (inst := inst)}

    (c_G : ℝ) (hcG_pos : c_G > 0)
    (h_green_sq : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
      l2.l2norm (greenOp.greenCorrection k s) *
        l2.l2norm (greenOp.greenCorrection k s) ≤
        c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))

    (C_g : ℝ) (lam : ℝ) (hCg_pos : C_g > 0) (hlam_pos : lam > 0)
    (h_gauss : ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))

    (h_zero : ∀ (p : VF),
      l2.l2norm (greenOp.greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))) :
    ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (greenOp.greenCorrection k (fam.section_ k p)) ≤
          C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by

  refine ⟨Real.sqrt c_G * C_g, lam, mul_pos (Real.sqrt_pos.mpr hcG_pos) hCg_pos, hlam_pos, ?_⟩
  intro k p
  by_cases hk : k = 0
  ·
    subst hk
    convert h_zero p using 2
    simp
  ·

    have h_norm_xi_nn := l2.l2norm_nonneg (greenOp.greenCorrection k (fam.section_ k p))
    have h_norm_ds_nn := l2.l2norm_nonneg (dol.delbar (fam.section_ k p))
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hCk_nn : 0 ≤ c_G / (k : ℝ) := div_nonneg (le_of_lt hcG_pos) (le_of_lt hk_pos)
    have h_sq := h_green_sq k hk (fam.section_ k p)
    have h_linear := l2_bound_from_squared_bound h_norm_xi_nn h_norm_ds_nn hCk_nn h_sq


    have h1_le_k : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have h_div_le : c_G / (k : ℝ) ≤ c_G :=
      div_le_self (le_of_lt hcG_pos) h1_le_k
    have h_sqrt_mono : Real.sqrt (c_G / (k : ℝ)) ≤ Real.sqrt c_G :=
      Real.sqrt_le_sqrt h_div_le

    have h_gauss_k := h_gauss k p

    calc l2.l2norm (greenOp.greenCorrection k (fam.section_ k p))
        ≤ Real.sqrt (c_G / (k : ℝ)) *
            l2.l2norm (dol.delbar (fam.section_ k p)) := h_linear
      _ ≤ Real.sqrt c_G *
            l2.l2norm (dol.delbar (fam.section_ k p)) := by
          apply mul_le_mul_of_nonneg_right h_sqrt_mono h_norm_ds_nn
      _ ≤ Real.sqrt c_G *
            (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left h_gauss_k (le_of_lt (Real.sqrt_pos.mpr hcG_pos))
      _ = Real.sqrt c_G * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring

/-- Assembles a `GreenCorrectionInput` from its constituent estimates:
a Green operator, uniform spectral-gap constant, Gaussian decay of
$\bar\partial$, Cauchy estimates, $k=0$ holomorphicity, and bundle data. -/
noncomputable def buildGreenCorrectionInput
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))

    (greenOp : HasGreenOperator Ω l2 dol)

    (c_G : ℝ) (hcG_pos : c_G > 0)
    (h_green_sq : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
      l2.l2norm (greenOp.greenCorrection k s) *
        l2.l2norm (greenOp.greenCorrection k s) ≤
        c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))

    (h_gauss : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))

    (h_cauchy : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s))

    (h_hol_zero : ∀ (p : VF),
      dol.delbar (fam.section_ 0 p + greenOp.greenCorrection 0 (fam.section_ 0 p)) = 0)
    (bundle_data : LineBundleData (inst := inst))
    (h_bundle_eq : fam.L = bundle_data)

    (h_l2_zero : ∀ (C_g : ℝ) (lam : ℝ), C_g > 0 → lam > 0 →
      (∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) →
      ∀ (p : VF),
        l2.l2norm (greenOp.greenCorrection 0 (fam.section_ 0 p)) ≤
          Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))) :
    GreenCorrectionInput wdn l2 dol fam where
  greenOp := greenOp
  gaussian_decay := h_gauss
  cauchy_estimates := h_cauchy
  correction_l2_exp_bound := by

    obtain ⟨C_g, lam, hCg_pos, hlam_pos, h_gauss_bound⟩ := h_gauss
    exact derive_correction_l2_exp_bound c_G hcG_pos h_green_sq
      C_g lam hCg_pos hlam_pos h_gauss_bound (h_l2_zero C_g lam hCg_pos hlam_pos h_gauss_bound)
  hol_at_zero := h_hol_zero
  same_bundle_data := bundle_data
  corrected_bundle_eq := h_bundle_eq


/-- Bundled "Gaussian peak section" data on a compatibly-almost-complex
symplectic manifold: a line bundle, a section family, and all the analytic
infrastructure (norms, pointwise evaluation, distance) together with the
uniform bound, Gaussian decay, concentration, and local lower-bound estimates
that comprise Donaldson's peak sections. -/
structure GaussianPeakData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hcompat : IsCompatibleACS S J) where
  L : LineBundleData (inst := inst)
  section_ : ℕ → VF → Ω 0
  pe : PointwiseEval Ω VF
  md : ManifoldDist VF
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  uniform_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (section_ k p) ≤ C_r
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (section_ k p) = inst.d β
  delbar_l2_decay : ∃ (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (section_ k p)) ≤ C / Real.sqrt (k : ℝ)
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q → section_ k p ≠ section_ k q
  gaussian_decay : ∃ (C_gd lam : ℝ) (N : ℕ), C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)

  local_lower_bound : ∃ (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p q : VF),
      md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (section_ k p)

/-- Typeclass assumption that `GaussianPeakData` is available for a given
compact symplectic manifold with a compatible almost-complex structure. -/
class HasGaussianPeakData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hcompat : IsCompatibleACS S J) where
  peakData : GaussianPeakData S J hcompat

/-- Existence of Donaldson's Gaussian peak sections, derived directly from the
packaged `GaussianPeakData`: a uniformly-bounded, approximately-holomorphic,
uniformly-concentrated section family with a local lower bound on Gaussian peaks. -/
theorem gaussian_peak_sections_exist_sorry
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hcompat : IsCompatibleACS S J)
    [HasGaussianPeakData Ω S J _hcompat] :
    ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
        ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) := by


  let gpd := HasGaussianPeakData.peakData (S := S) (J := J) (hcompat := _hcompat)

  let fam : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := gpd.L
      section_ := gpd.section_ }


  have hUB : IsUniformlyBounded fam := ⟨⟨gpd.wdn, gpd.uniform_bound⟩⟩

  have hAH : IsApproxHolomorphic fam := by
    constructor
    · exact gpd.delbar_exact
    · obtain ⟨C, hC_pos, hC_bound⟩ := gpd.delbar_l2_decay
      exact ⟨gpd.l2, C, hC_pos, hC_bound⟩

  have hUC : IsUniformlyConcentrated fam := by
    constructor
    · exact gpd.concentrated
    · obtain ⟨C_gd, lam, N, hCgd_pos, hlam_pos, hgd_bound⟩ := gpd.gaussian_decay
      exact ⟨gpd.pe, gpd.md, C_gd, lam, N, hCgd_pos, hlam_pos, hgd_bound⟩
    · exact ⟨gpd.wdn, gpd.uniform_bound⟩

  have hLB : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
      c ≤ pe.peval q (fam.section_ k p) := by
    obtain ⟨c, hc_pos, hc_bound⟩ := gpd.local_lower_bound
    exact ⟨gpd.pe, gpd.md, c, hc_pos, hc_bound⟩
  exact ⟨fam, hUB, hAH, hUC, hLB⟩


/-- Abstract Weitzenböck decomposition data on a compact symplectic manifold:
a Green correction, its holomorphicity property, a spectral-gap squared
bound, and a uniform spectral-gap constant $c_G$. -/
class HasWeitzenbockDecomp
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) where
  greenCorrection : ℕ → Ω 0 → Ω 0
  green_holomorphic : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    dol.delbar (s + greenCorrection k s) = 0
  green_l2_sq_bound : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    ∃ (c : ℝ), c > 0 ∧
      l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
        c / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))
  c_G : ℝ
  c_G_pos : c_G > 0
  uniform_l2_bound : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
      c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))


/-- Forget the uniform Weitzenböck constant: a `HasWeitzenbockDecomp` instance
yields a `HasGreenOperator` instance. -/
noncomputable def HasWeitzenbockDecomp.toHasGreenOperator
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    HasGreenOperator Ω l2 dol where
  greenCorrection := wb.greenCorrection
  green_holomorphic := wb.green_holomorphic
  green_l2_sq_bound := wb.green_l2_sq_bound


/-- Convenience alias: the Green operator obtained from `HasWeitzenbockDecomp`. -/
noncomputable def weitzenbock_green_operator_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    HasGreenOperator Ω l2 dol :=
  HasWeitzenbockDecomp.toHasGreenOperator l2 dol

/-- The uniform Weitzenböck constant $c_G$ extracted from a
`HasWeitzenbockDecomp` instance. -/
noncomputable def weitzenbock_uniform_constant_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] : ℝ :=
  wb.c_G

/-- Positivity of the Weitzenböck constant: $c_G > 0$. -/
theorem weitzenbock_uniform_constant_pos
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    weitzenbock_uniform_constant_axiom l2 dol > 0 :=
  wb.c_G_pos

/-- Uniform $L^2$ bound from the Weitzenböck decomposition: for all $k \ne 0$,
$\|G(s)\|_{L^2}^2 \le (c_G/k)\, \|\bar\partial s\|_{L^2}^2$. -/
theorem weitzenbock_uniform_l2_bound_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),

      l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) *
        l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤
        (weitzenbock_uniform_constant_axiom l2 dol) / (k : ℝ) *
          (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)) :=
  wb.uniform_l2_bound


/-- Elementary inequality: $y \cdot e^{-y} \le e^{-1}$ for all $y \in \mathbb{R}$,
attained at $y = 1$. -/
theorem mul_exp_neg_le_exp_neg_one (y : ℝ) :
    y * Real.exp (-y) ≤ Real.exp (-1) := by
  have hexp_ineq : y ≤ Real.exp (y - 1) := by
    have := Real.add_one_le_exp (y - 1); linarith
  calc y * Real.exp (-y)
      ≤ Real.exp (y - 1) * Real.exp (-y) := by
        apply mul_le_mul_of_nonneg_right hexp_ineq (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((y - 1) + (-y)) := by rw [← Real.exp_add]
    _ = Real.exp (-1) := by ring_nf

/-- Rescaled form of `mul_exp_neg_le_exp_neg_one`:
$t \cdot e^{-\lambda t} \le 1 / (\lambda e)$ for $\lambda > 0$ and all $t \in \mathbb{R}$. -/
theorem t_exp_neg_lam_t_bound (t lam : ℝ) (hlam_pos : lam > 0) :
    t * Real.exp (-lam * t) ≤ 1 / (lam * Real.exp 1) := by
  by_cases ht : 0 ≤ t
  · have h_ue := mul_exp_neg_le_exp_neg_one (lam * t)
    have h_eq : t * Real.exp (-lam * t) =
        (1 / lam) * (lam * t * Real.exp (-(lam * t))) := by field_simp
    rw [h_eq]
    calc (1 / lam) * (lam * t * Real.exp (-(lam * t)))
        ≤ (1 / lam) * Real.exp (-1) := by
          apply mul_le_mul_of_nonneg_left h_ue; positivity
      _ = 1 / (lam * Real.exp 1) := by rw [Real.exp_neg]; field_simp
  · push_neg at ht
    have h1 : t * Real.exp (-lam * t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht) (le_of_lt (Real.exp_pos _))
    linarith [show (0 : ℝ) < 1 / (lam * Real.exp 1) from by positivity]

/-- Absorption lemma: $A\,t\,e^{-\lambda_0 t} \le C_g\, e^{-\lambda t}$ for some
$C_g, \lambda > 0$ and all $t \ge 0$. The polynomial factor $t$ is absorbed
into a slightly smaller exponential rate. -/
theorem absorb_poly_into_exp (A lam0 : ℝ) (hA : A > 0) (hlam0 : lam0 > 0) :
    ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        A * t * Real.exp (-lam0 * t) ≤ C_g * Real.exp (-lam * t) := by
  refine ⟨A / (lam0 / 2 * Real.exp 1) + 1, lam0 / 2, by positivity, by linarith, ?_⟩
  intro t ht
  have hlam_pos : lam0 / 2 > 0 := by linarith
  have hexp_split : Real.exp (-lam0 * t) =
      Real.exp (-(lam0 / 2) * t) * Real.exp (-(lam0 / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  calc A * t * Real.exp (-lam0 * t)
      = A * t * (Real.exp (-(lam0/2) * t) * Real.exp (-(lam0/2) * t)) := by rw [hexp_split]
    _ = (A * (t * Real.exp (-(lam0/2) * t))) * Real.exp (-(lam0/2) * t) := by ring
    _ ≤ (A * (1 / ((lam0/2) * Real.exp 1))) * Real.exp (-(lam0/2) * t) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
              (t_exp_neg_lam_t_bound t (lam0/2) hlam_pos) (le_of_lt hA)
        · exact le_of_lt (Real.exp_pos _)
    _ = A / ((lam0/2) * Real.exp 1) * Real.exp (-(lam0/2) * t) := by ring
    _ ≤ (A / ((lam0/2) * Real.exp 1) + 1) * Real.exp (-(lam0/2) * t) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        linarith

/-- Cutoff-localized Gaussian decay data: the $\bar\partial$ of the cutoff
peak section satisfies $\|\bar\partial s_{k,p}\|_{L^2} \le A_{\sup}\, k^{1/3}
e^{-\lambda_0 k^{1/3}}$. After absorption (via `absorb_poly_into_exp`) this
becomes the exponential bound used in the Donaldson construction. -/
structure CutoffGaussianData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  A_sup : ℝ
  A_sup_pos : A_sup > 0
  lam_0 : ℝ
  lam_0_pos : lam_0 > 0
  l2_delbar_bound : ∀ (k : ℕ) (p : VF),
    l2.l2norm (dol.delbar (fam.section_ k p)) ≤
      A_sup * (k : ℝ) ^ ((1 : ℝ) / 3) * Real.exp (-lam_0 * (k : ℝ) ^ ((1 : ℝ) / 3))

/-- Convert a `CutoffGaussianData` polynomial-times-exponential bound into a
pure exponential bound: $\|\bar\partial s_{k,p}\|_{L^2} \le C_g\, e^{-\lambda k^{1/3}}$. -/
theorem derive_gaussian_l2_bound'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    {l2 : L2NormSpace Ω (inst := inst)}
    {dol : DolbeaultOps (inst := inst)}
    {fam : ApproxHolomorphicSectionFamily (inst := inst)}
    (cgd : CutoffGaussianData l2 dol fam) :
    ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
  obtain ⟨C_g, lam, hCg, hlam, h_absorb⟩ :=
    absorb_poly_into_exp cgd.A_sup cgd.lam_0 cgd.A_sup_pos cgd.lam_0_pos
  refine ⟨C_g, lam, hCg, hlam, ?_⟩
  intro k p
  set t := (k : ℝ) ^ ((1 : ℝ) / 3) with ht_def
  have ht_nn : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg k) _
  calc l2.l2norm (dol.delbar (fam.section_ k p))
      ≤ cgd.A_sup * t * Real.exp (-cgd.lam_0 * t) := cgd.l2_delbar_bound k p
    _ ≤ C_g * Real.exp (-lam * t) := h_absorb t ht_nn

/-- Donaldson's PDE-axiom package: provides cutoff Gaussian data for every
section family, Cauchy estimates for every Green operator, holomorphicity of
the corrected $k=0$ section, and the $L^2$ zero-edge correction bound. -/
class HasDonaldsonPDEData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol] where
  cutoffGaussianData : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
    CutoffGaussianData l2 dol fam
  cauchyEstimates : ∀ (greenOp : HasGreenOperator Ω l2 dol),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s)
  correctionHolAtZero : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)) (p : VF),
    dol.delbar (fam.section_ 0 p +
      (HasWeitzenbockDecomp.toHasGreenOperator l2 dol).greenCorrection 0 (fam.section_ 0 p)) = 0
  correctionL2ZeroEdge : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (c_G : ℝ) (C_g : ℝ) (lam : ℝ),
    C_g > 0 → lam > 0 →
    (∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) →
    ∀ (p : VF),
      l2.l2norm ((HasWeitzenbockDecomp.toHasGreenOperator l2 dol).greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))

/-- Pull the cutoff Gaussian data out of the Donaldson PDE-axioms instance. -/
noncomputable def cutoff_gaussian_data_exists'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    CutoffGaussianData l2 dol fam := hpde.cutoffGaussianData fam

/-- Cauchy estimates for the Green correction of any Green operator, taken
from the Donaldson PDE axioms. -/
theorem cauchy_estimates_for_green_op'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (greenOp : HasGreenOperator Ω l2 dol) :
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s) := hpde.cauchyEstimates greenOp

/-- Exponential ($k^{1/3}$) Gaussian decay of $\bar\partial$ on any
section family, derived from the cutoff Gaussian data via absorption. -/
theorem gaussian_decay_delbar_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) :=
  derive_gaussian_l2_bound' (cutoff_gaussian_data_exists' wdn l2 dol fam)

/-- Cauchy estimates specialized to the Weitzenböck-derived Green operator. -/
theorem cauchy_estimates_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol] :
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤
          C_r * l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) :=
  cauchy_estimates_for_green_op' wdn l2 dol (weitzenbock_green_operator_axiom l2 dol)

/-- The corrected section at $k = 0$ is holomorphic:
$\bar\partial(s_{0,p} + G(s_{0,p})) = 0$. -/
theorem correction_hol_at_zero_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (_wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    ∀ (p : VF),
      dol.delbar (fam.section_ 0 p +
        (weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) = 0 :=
  hpde.correctionHolAtZero fam

/-- Trivial wrapper: extract the underlying line bundle data from a section family. -/
noncomputable def correction_bundle_data_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    LineBundleData (inst := inst) := fam.L

/-- Reflexivity: `fam.L` is the same as `correction_bundle_data_axiom fam`. -/
theorem correction_bundle_eq_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    fam.L = correction_bundle_data_axiom fam := rfl

/-- Edge case bound: at $k = 0$ the $L^2$-norm of the Green correction is
controlled by $\sqrt{c_G}\, C_g\, e^{-\lambda \cdot 0^{1/3}}$, used to
initialize the inductive Donaldson construction. -/
theorem correction_l2_zero_edge_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (_wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (c_G : ℝ) (C_g : ℝ) (lam : ℝ)
    (_hCg_pos : C_g > 0) (_hlam_pos : lam > 0)
    (_h_gauss : ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) :
    ∀ (p : VF),
      l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3)) :=
  hpde.correctionL2ZeroEdge fam c_G C_g lam _hCg_pos _hlam_pos _h_gauss

/-- Assemble the full `GreenCorrectionInput` for a family using the Weitzenböck
decomposition, the cutoff Gaussian decay, Cauchy estimates, and the $k=0$
zero-edge bound provided by the Donaldson PDE axioms. -/
noncomputable def green_correction_data_sorry
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionInput wdn l2 dol fam :=


  buildGreenCorrectionInput wdn l2 dol fam

    (weitzenbock_green_operator_axiom l2 dol)

    (weitzenbock_uniform_constant_axiom l2 dol)
    (weitzenbock_uniform_constant_pos l2 dol)
    (weitzenbock_uniform_l2_bound_axiom l2 dol)

    (gaussian_decay_delbar_axiom wdn l2 dol fam)

    (cauchy_estimates_axiom wdn l2 dol)

    (correction_hol_at_zero_axiom wdn l2 dol fam)

    (correction_bundle_data_axiom fam)
    (correction_bundle_eq_axiom fam)

    (fun C_g lam hCg hlam h_gauss =>
      correction_l2_zero_edge_axiom wdn l2 dol fam
        (weitzenbock_uniform_constant_axiom l2 dol) C_g lam hCg hlam h_gauss)

/-- Bundles all data needed to run Donaldson's Proposition 1 proof on a compact
symplectic manifold with compatible almost-complex structure: a weighted
sup-norm, an $L^2$-norm, a Dolbeault operator, Gaussian peak sections, a
Weitzenböck decomposition, and the PDE-axioms package. -/
class HasDonaldsonProofData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hcompat : IsCompatibleACS S J) where
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  dol : DolbeaultOps (inst := inst)
  gaussianPeakInst : HasGaussianPeakData Ω S J hcompat
  weitzenbockInst : HasWeitzenbockDecomp Ω l2 dol
  pdeDataInst : @HasDonaldsonPDEData Ω VF inst _ wdn l2 dol weitzenbockInst

/-- Legacy internal version of Donaldson's Proposition 1: on a compact Kähler
manifold with the full `HasDonaldsonProofData`, there exist approximately
holomorphic sections with Gaussian peak structure and an exponentially-close
genuinely holomorphic family. -/
theorem donaldson_prop1_legacy_internal
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (_hcompat : IsCompatibleACS S J)
    [hpd : HasDonaldsonProofData Ω S J _hcompat] :


    ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      1 ≤ k₀ ∧
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧

      (∃ (c : ℝ), c > 0 ∧
        ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) ∧

      (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)),
        IsHolomorphicFamily hpd.dol fam' ∧
        IsExponentiallyCloseCubeRoot hpd.wdn fam fam') := by

  let wdn := hpd.wdn
  let l2 := hpd.l2
  let dol := hpd.dol
  letI : HasGaussianPeakData Ω S J _hcompat := hpd.gaussianPeakInst
  letI : HasWeitzenbockDecomp Ω l2 dol := hpd.weitzenbockInst
  letI : HasDonaldsonPDEData Ω wdn l2 dol := hpd.pdeDataInst


  obtain ⟨fam, hbound, happrox, hconc, pe, md, c, hc_pos, hpeak⟩ :=
    gaussian_peak_sections_exist_sorry S J _hcompat

  refine ⟨1, pe, md, fam, le_refl 1, hbound, happrox, hconc,
    ⟨c, hc_pos, fun k _hk p q hdist => hpeak k p q hdist⟩, ?_⟩


  have h_gci : GreenCorrectionInput wdn l2 dol fam :=
    green_correction_data_sorry wdn l2 dol fam

  let fam' := correctedFamily wdn l2 dol fam h_gci

  have h_hol : IsHolomorphicFamily dol fam' :=
    green_corrected_family_is_holomorphic wdn l2 dol fam h_gci

  have h_exp : IsExponentiallyCloseCubeRoot wdn fam fam' :=
    green_correction_exp_close wdn l2 dol fam h_gci
  exact ⟨fam', h_hol, h_exp⟩


/-- Donaldson's Gaussian peak sections on a compact Kähler manifold, in their
externally-facing form: a uniformly-bounded, approximately-holomorphic,
uniformly-concentrated family with local lower bounds. -/
theorem donaldson_gaussian_peak_sections
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J) (_hcompat : IsCompatibleACS S J)
    [HasGaussianPeakData Ω S J _hcompat] :
    ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
        ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) :=
  gaussian_peak_sections_exist_sorry S J _hcompat

/-- The PDE-axioms package for a Green correction operator on a specific
section family: the Green correction, its holomorphicity, the uniform
spectral gap, Gaussian decay of $\bar\partial$, Cauchy estimates, $k=0$
holomorphicity, bundle data, and the $L^2$-bound at $k=0$. -/
structure GreenCorrectionPDEAxioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  greenCorrection : ℕ → Ω 0 → Ω 0
  green_holomorphic : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    dol.delbar (s + greenCorrection k s) = 0
  uniform_spectral_gap : ∃ (C : ℝ), C > 0 ∧ ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
      C / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))
  gaussian_decay : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
  cauchy_estimates : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (s : Ω 0),
      wdn.weighted_supnorm k r (greenCorrection k s) ≤
        C_r * l2.l2norm (greenCorrection k s)
  hol_at_zero : ∀ (p : VF),
    dol.delbar (fam.section_ 0 p + greenCorrection 0 (fam.section_ 0 p)) = 0
  same_bundle_data : LineBundleData (inst := inst)
  corrected_bundle_eq : fam.L = same_bundle_data
  correction_l2_at_zero : ∃ (B : ℝ), B > 0 ∧
    ∀ (p : VF), l2.l2norm (greenCorrection 0 (fam.section_ 0 p)) ≤ B

/-- From the uniform spectral gap, Gaussian decay of $\bar\partial$, and the
$L^2$-bound at $k = 0$, derive the exponential $L^2$-bound for the Green
correction at every $k$:
$\|G(s_{k,p})\|_{L^2} \le C_{L^2}\, e^{-\lambda k^{1/3}}$. -/
theorem correction_l2_exp_bound_from_spectral_gap
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (pde : GreenCorrectionPDEAxioms wdn l2 dol fam) :
    ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (pde.greenCorrection k (fam.section_ k p)) ≤
          C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by

  obtain ⟨C_spec, hC_pos, h_spec⟩ := pde.uniform_spectral_gap

  obtain ⟨C_g, lam, hCg_pos, hlam_pos, h_gauss⟩ := pde.gaussian_decay

  obtain ⟨B, hB_pos, h_zero⟩ := pde.correction_l2_at_zero


  refine ⟨Real.sqrt C_spec * C_g + B, lam, ?_, ?_, ?_⟩
  ·
    exact add_pos (mul_pos (Real.sqrt_pos.mpr hC_pos) hCg_pos) hB_pos
  · exact hlam_pos
  · intro k p
    by_cases hk : k = 0
    ·
      subst hk
      have h0 := h_zero p
      simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0),
        mul_zero, Real.exp_zero, mul_one]
      linarith [mul_pos (Real.sqrt_pos.mpr hC_pos) hCg_pos]
    ·
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      have h_spec_k := h_spec k hk (fam.section_ k p)
      have h_gauss_k := h_gauss k p

      have h_l2nn := l2.l2norm_nonneg (pde.greenCorrection k (fam.section_ k p))
      have h_delbar_nn := l2.l2norm_nonneg (dol.delbar (fam.section_ k p))
      have hCk_nn : (0 : ℝ) ≤ C_spec / (k : ℝ) := div_nonneg (le_of_lt hC_pos) (le_of_lt hk_pos)
      have h_lin : l2.l2norm (pde.greenCorrection k (fam.section_ k p)) ≤
          Real.sqrt (C_spec / (k : ℝ)) * l2.l2norm (dol.delbar (fam.section_ k p)) :=
        l2_bound_from_squared_bound h_l2nn h_delbar_nn hCk_nn h_spec_k

      have h_sqrt_mono : Real.sqrt (C_spec / (k : ℝ)) ≤ Real.sqrt C_spec := by
        apply Real.sqrt_le_sqrt
        exact div_le_self (le_of_lt hC_pos)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)

      have h_exp_pos := Real.exp_pos (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
      calc l2.l2norm (pde.greenCorrection k (fam.section_ k p))
          ≤ Real.sqrt (C_spec / (k : ℝ)) * l2.l2norm (dol.delbar (fam.section_ k p)) := h_lin
        _ ≤ Real.sqrt C_spec * l2.l2norm (dol.delbar (fam.section_ k p)) := by
            apply mul_le_mul_of_nonneg_right h_sqrt_mono h_delbar_nn
        _ ≤ Real.sqrt C_spec * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
            apply mul_le_mul_of_nonneg_left h_gauss_k (Real.sqrt_nonneg C_spec)
        _ = Real.sqrt C_spec * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring
        _ ≤ (Real.sqrt C_spec * C_g + B) * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt h_exp_pos)
            linarith

/-- Convert a `GreenCorrectionPDEAxioms` package into the `GreenCorrectionInput`
structure used by `correctedFamily` and the holomorphic-correction theorems. -/
noncomputable def GreenCorrectionInput_of_pde_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (pde : GreenCorrectionPDEAxioms wdn l2 dol fam) :
    GreenCorrectionInput wdn l2 dol fam where
  greenOp :=
    { greenCorrection := pde.greenCorrection,
      green_holomorphic := pde.green_holomorphic,
      green_l2_sq_bound := fun k hk s => by

        obtain ⟨C, hC_pos, h_unif⟩ := pde.uniform_spectral_gap
        exact ⟨C, hC_pos, h_unif k hk s⟩ }
  gaussian_decay := pde.gaussian_decay
  cauchy_estimates := pde.cauchy_estimates
  correction_l2_exp_bound :=
    correction_l2_exp_bound_from_spectral_gap wdn l2 dol fam pde
  hol_at_zero := pde.hol_at_zero
  same_bundle_data := pde.same_bundle_data
  corrected_bundle_eq := pde.corrected_bundle_eq

/-- Construct the Donaldson Green-correction PDE-axiom package on a compact
Kähler manifold by combining the Weitzenböck decomposition with the Donaldson
PDE-data infrastructure. -/
noncomputable def donaldson_green_correction_pde_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J) (_hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionPDEAxioms wdn l2 dol fam where
  greenCorrection := wb.greenCorrection
  green_holomorphic := wb.green_holomorphic
  uniform_spectral_gap := ⟨wb.c_G, wb.c_G_pos, wb.uniform_l2_bound⟩
  gaussian_decay := gaussian_decay_delbar_axiom wdn l2 dol fam
  cauchy_estimates := cauchy_estimates_axiom wdn l2 dol
  hol_at_zero := hpde.correctionHolAtZero fam
  same_bundle_data := fam.L
  corrected_bundle_eq := rfl
  correction_l2_at_zero := by
    obtain ⟨C_g, lam, hCg, hlam, hbound⟩ := gaussian_decay_delbar_axiom wdn l2 dol fam
    have h0 := hpde.correctionL2ZeroEdge fam wb.c_G C_g lam hCg hlam hbound
    exact ⟨Real.sqrt wb.c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3)),
           mul_pos (mul_pos (Real.sqrt_pos.mpr wb.c_G_pos) hCg) (Real.exp_pos _), h0⟩

/-- Existence of a `GreenCorrectionInput` on a compact Kähler manifold equipped
with the Weitzenböck decomposition and Donaldson PDE data: obtained by
composing `donaldson_green_correction_pde_axioms` with
`GreenCorrectionInput_of_pde_axioms`. -/
noncomputable def donaldson_green_correction_exists
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J) (_hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionInput wdn l2 dol fam :=
  GreenCorrectionInput_of_pde_axioms wdn l2 dol fam
    (donaldson_green_correction_pde_axioms S J _hK _hcompat wdn l2 dol fam)


/-- Normalized local section data: a section family together with the
pointwise-evaluation and manifold-distance structures, plus a starting
index $k_0 \ge 1$ from which all estimates begin to hold. -/
structure NormalizedLocalSectionData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  fam : ApproxHolomorphicSectionFamily (inst := inst)
  pe : PointwiseEval Ω VF
  md : ManifoldDist VF
  k₀ : ℕ
  hk₀ : 1 ≤ k₀









set_option maxHeartbeats 800000 in
/-- Donaldson's Proposition 1 with explicit hypotheses: given normalized
coordinates, cutoff Gaussian decay, curvature lower bound, Hodge orthogonality
and Cauchy estimates, there exists an exponentially-close holomorphic family
approximating the peak sections at the cube-root rate. -/
theorem donaldson_proposition_1_with_hypotheses
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))


    (h_normal_coords :
      ∃ (nls : NormalizedLocalSectionData (inst := inst)),
        IsUniformlyConcentrated nls.fam ∧
        IsUniformlyBounded nls.fam ∧
        IsApproxHolomorphic nls.fam ∧
        (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), nls.k₀ < k → ∀ (p q : VF),
          nls.md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
            c ≤ nls.pe.peval q (nls.fam.section_ k p)))


    (h_cutoff : ∀ (nls : NormalizedLocalSectionData (inst := inst)),
      ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧
        ∀ (k : ℕ) (p : VF),
          l2.l2norm (dol.delbar (nls.fam.section_ k p)) ≤
            C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))


    (h_curvature :
      Σ' (greenCorrection : ℕ → Ω 0 → Ω 0) (C_geom : ℝ),
      C_geom > 0 ∧
      (∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom →
        l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
          1 / ((k : ℝ) - C_geom) *
            (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) ∧
      (∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0),
        ∃ (B : ℝ), B > 0 ∧
          l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
            B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))))


    (h_hodge : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
      dol.delbar (s + h_curvature.1 k s) = 0)


    (h_cauchy :
      (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
        ∀ (k : ℕ) (s : Ω 0),
          wdn.weighted_supnorm k r (h_curvature.1 k s) ≤
            C_r * l2.l2norm (dol.delbar s)) ∧
      (∀ (s : Ω 0),
        dol.delbar (s + h_curvature.1 0 s) = 0)) :


    ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      1 ≤ k₀ ∧
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧

      (∃ (c : ℝ), c > 0 ∧
        ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) ∧

      (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)),
        IsHolomorphicFamily dol fam' ∧
        IsExponentiallyCloseCubeRoot wdn fam fam') := by


  obtain ⟨nls, hconc, hbound, happrox, hpeak⟩ := h_normal_coords

  obtain ⟨C_g, lam, hCg, hlam, hdelbar_decay⟩ := h_cutoff nls


  let hG : HasGreenOperator Ω l2 dol :=
    { greenCorrection := h_curvature.1
      green_holomorphic := h_hodge
      green_l2_sq_bound :=
        spectral_gap_from_curvature_bound l2 dol h_curvature.1
          h_curvature.2.1 h_curvature.2.2.1 h_curvature.2.2.2.1 h_curvature.2.2.2.2 }

  obtain ⟨hCrBound, hHolZero⟩ := h_cauchy


  let fam := nls.fam
  let fam' : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := fam.L
      section_ := fun k p => fam.section_ k p + hG.greenCorrection k (fam.section_ k p) }

  have hhol_sections : ∀ (k : ℕ) (p : VF), dol.delbar (fam'.section_ k p) = 0 := by
    intro k p
    by_cases hk : k = 0
    · subst hk; exact hHolZero (fam.section_ 0 p)
    · exact hG.green_holomorphic k hk (fam.section_ k p)

  have hcr_close : ∀ (r : ℕ), ∃ (C'_r : ℝ), C'_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C'_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro r
    obtain ⟨C_r, hCr_pos, hCr⟩ := hCrBound r
    refine ⟨C_r * C_g, mul_pos hCr_pos hCg, ?_⟩
    intro k p
    have h_diff : fam.section_ k p - fam'.section_ k p =
        -(hG.greenCorrection k (fam.section_ k p)) := by
      show fam.section_ k p - (fam.section_ k p + hG.greenCorrection k (fam.section_ k p)) =
        -(hG.greenCorrection k (fam.section_ k p))
      abel
    rw [h_diff]
    have h_neg := wdn.weighted_supnorm_neg k r (hG.greenCorrection k (fam.section_ k p))
    have h_cr := hCr k (fam.section_ k p)
    have h_decay := hdelbar_decay k p
    calc wdn.weighted_supnorm k r (-(hG.greenCorrection k (fam.section_ k p)))
        ≤ wdn.weighted_supnorm k r (hG.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (dol.delbar (fam.section_ k p)) := h_cr
      _ ≤ C_r * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left h_decay (le_of_lt hCr_pos)
      _ = C_r * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring


  refine ⟨nls.k₀, nls.pe, nls.md, fam, nls.hk₀, hbound, happrox, hconc, hpeak, fam', ?_, ?_⟩

  · exact ⟨hhol_sections⟩

  · exact ⟨rfl, lam, hlam, hcr_close⟩


set_option maxHeartbeats 800000 in
/-- Donaldson's Proposition 1 (book statement): on a compact Kähler manifold
$(M, \omega, J)$ with normalized coordinates, the line bundles $L^k$ admit
approximately holomorphic Gaussian peak sections and, for $k$ sufficiently
large, there is a genuinely holomorphic family exponentially close (at the
cube-root rate) to the peak sections. -/
theorem donaldson_proposition_1_book
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (h_normal_coords :
      ∃ (nls : NormalizedLocalSectionData (inst := inst)),
        IsUniformlyConcentrated nls.fam ∧
        IsUniformlyBounded nls.fam ∧
        IsApproxHolomorphic nls.fam ∧
        (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), nls.k₀ < k → ∀ (p q : VF),
          nls.md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
            c ≤ nls.pe.peval q (nls.fam.section_ k p)))
    (h_cutoff : ∀ (nls : NormalizedLocalSectionData (inst := inst)),
      ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧
        ∀ (k : ℕ) (p : VF),
          l2.l2norm (dol.delbar (nls.fam.section_ k p)) ≤
            C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))
    (h_curvature :
      Σ' (greenCorrection : ℕ → Ω 0 → Ω 0) (C_geom : ℝ),
      C_geom > 0 ∧
      (∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom →
        l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
          1 / ((k : ℝ) - C_geom) *
            (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) ∧
      (∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0),
        ∃ (B : ℝ), B > 0 ∧
          l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
            B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))))
    (h_hodge : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
      dol.delbar (s + h_curvature.1 k s) = 0)
    (h_cauchy :
      (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
        ∀ (k : ℕ) (s : Ω 0),
          wdn.weighted_supnorm k r (h_curvature.1 k s) ≤
            C_r * l2.l2norm (dol.delbar s)) ∧
      (∀ (s : Ω 0),
        dol.delbar (s + h_curvature.1 0 s) = 0)) :
    ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      1 ≤ k₀ ∧
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ (c : ℝ), c > 0 ∧
        ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) ∧
      (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)),
        IsHolomorphicFamily dol fam' ∧
        IsExponentiallyCloseCubeRoot wdn fam fam') := by

  obtain ⟨nls, hconc, hbound, happrox, hpeak⟩ := h_normal_coords
  obtain ⟨C_g, lam, hCg, hlam, hdelbar_decay⟩ := h_cutoff nls

  let hG : HasGreenOperator Ω l2 dol :=
    { greenCorrection := h_curvature.1
      green_holomorphic := h_hodge
      green_l2_sq_bound :=
        spectral_gap_from_curvature_bound l2 dol h_curvature.1
          h_curvature.2.1 h_curvature.2.2.1 h_curvature.2.2.2.1 h_curvature.2.2.2.2 }
  obtain ⟨hCrBound, hHolZero⟩ := h_cauchy

  let fam := nls.fam
  let fam' : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := fam.L
      section_ := fun k p => fam.section_ k p + hG.greenCorrection k (fam.section_ k p) }
  have hhol_sections : ∀ (k : ℕ) (p : VF), dol.delbar (fam'.section_ k p) = 0 := by
    intro k p
    by_cases hk : k = 0
    · subst hk; exact hHolZero (fam.section_ 0 p)
    · exact hG.green_holomorphic k hk (fam.section_ k p)
  have hcr_close : ∀ (r : ℕ), ∃ (C'_r : ℝ), C'_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C'_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro r
    obtain ⟨C_r, hCr_pos, hCr⟩ := hCrBound r
    refine ⟨C_r * C_g, mul_pos hCr_pos hCg, ?_⟩
    intro k p
    have h_diff : fam.section_ k p - fam'.section_ k p =
        -(hG.greenCorrection k (fam.section_ k p)) := by
      show fam.section_ k p - (fam.section_ k p + hG.greenCorrection k (fam.section_ k p)) =
        -(hG.greenCorrection k (fam.section_ k p))
      abel
    rw [h_diff]
    have h_neg := wdn.weighted_supnorm_neg k r (hG.greenCorrection k (fam.section_ k p))
    have h_cr := hCr k (fam.section_ k p)
    have h_decay := hdelbar_decay k p
    calc wdn.weighted_supnorm k r (-(hG.greenCorrection k (fam.section_ k p)))
        ≤ wdn.weighted_supnorm k r (hG.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (dol.delbar (fam.section_ k p)) := h_cr
      _ ≤ C_r * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left h_decay (le_of_lt hCr_pos)
      _ = C_r * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring

  refine ⟨nls.k₀, nls.pe, nls.md, fam, nls.hk₀, hbound, happrox, hconc, hpeak, fam', ?_, ?_⟩
  · exact ⟨hhol_sections⟩
  · exact ⟨rfl, lam, hlam, hcr_close⟩







/-- A symplectic manifold admits a "symplectic hypersurface" in the sense of
Donaldson's construction: there exist Dolbeault operators, weighted norms,
and a family of holomorphic peak sections with uniform Gaussian concentration
together with an exponentially-close holomorphic family approximating them.
The zero sets of these holomorphic sections give the desired symplectic
submanifolds. -/
class HasSymplecticHypersurface
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Prop where
  has_holomorphic_peak_sections :
    ∃ (dol : DolbeaultOps (inst := inst))
      (wdn : WeightedDerivSupNorm Ω (inst := inst))
      (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      1 ≤ k₀ ∧
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ (c : ℝ), c > 0 ∧
        ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) ∧
      (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)),
        IsHolomorphicFamily dol fam' ∧
        IsExponentiallyCloseCubeRoot wdn fam fam')
