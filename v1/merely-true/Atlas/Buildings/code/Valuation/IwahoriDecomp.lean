/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.LatticesValuations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *`DVRClosureGL2` axioms*: the structural closure properties of a DVR context needed to
prove the Iwahori decomposition for $GL_2$. Beyond the basic `DVRClosure`, we require: units
are nonzero, the maximal ideal absorbs products with elements of $\mathfrak{o}$, units are
closed under inversion, and a unit minus a maximal-ideal element is still a unit. -/
class DVRClosureGL2 (C : DVRContext) extends DVRClosure C where
  isUnitInO_ne_zero : ∀ {x : C.k}, C.isUnitInO x → x ≠ 0
  isInMaxIdeal_mul_isInO : ∀ {x y : C.k}, C.isInMaxIdeal x → C.isInO y → C.isInMaxIdeal (x * y)
  isUnitInO_inv_isUnitInO : ∀ {x : C.k}, C.isUnitInO x → C.isUnitInO x⁻¹
  isUnitInO_sub_isInMaxIdeal : ∀ {x y : C.k},
    C.isUnitInO x → C.isInMaxIdeal y → C.isUnitInO (x - y)

variable [DVRClosureGL2 C]


section GL2

variable {C}

/-- *Construct an invertible $2\times 2$ matrix from a function*: given a $2\times 2$ matrix
$f$ over the fraction field $k$ with nonzero determinant, produce the corresponding element
of $GL_2(k)$. The construction uses `unitOfDetInvertible` together with `invertibleOfNonzero`
to convert nonvanishing of the determinant into invertibility data. -/
noncomputable def mkGL2 (f : Fin 2 → Fin 2 → C.k)
    (hdet : (show Matrix (Fin 2) (Fin 2) C.k from f).det ≠ 0) :
    GL (Fin 2) C.k := by
  haveI : Invertible (show Matrix (Fin 2) (Fin 2) C.k from f).det :=
    invertibleOfNonzero hdet
  exact unitOfDetInvertible (show Matrix (Fin 2) (Fin 2) C.k from f)

/-- *Entries of `mkGL2` are the original entries*: the matrix underlying the unit produced by
`mkGL2 f hdet` has the same entries as $f$. -/
@[simp]
lemma mkGL2_val_apply (f : Fin 2 → Fin 2 → C.k)
    (hdet : (show Matrix (Fin 2) (Fin 2) C.k from f).det ≠ 0) (i j : Fin 2) :
    (mkGL2 f hdet).val i j = f i j := by
  simp only [mkGL2, unitOfDetInvertible]; rfl

variable (C)


/-- *The Iwahori subgroup of $GL_2$*: elements of $GL_2(k)$ whose diagonal entries are units
in $\mathfrak{o}$, whose upper-right entry lies in $\mathfrak{o}$, and whose lower-left entry
lies in the maximal ideal $\mathfrak{m}$. -/
def IwahoriGL2 : Set (GL (Fin 2) C.k) :=
  { g |
    C.isUnitInO (g.val 0 0) ∧ C.isUnitInO (g.val 1 1) ∧
    C.isInO (g.val 0 1) ∧ C.isInMaxIdeal (g.val 1 0) }

/-- *Upper unipotent subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix}$. -/
def UpperUnipGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 0 = 1 ∧ g.val 1 1 = 1 ∧ g.val 1 0 = 0 }

/-- *Lower unipotent subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} 1 & 0 \\ * & 1 \end{pmatrix}$. -/
def LowerUnipGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 0 = 1 ∧ g.val 1 1 = 1 ∧ g.val 0 1 = 0 }

/-- *Diagonal subgroup of $GL_2$*: invertible matrices of the form
$\begin{pmatrix} * & 0 \\ 0 & * \end{pmatrix}$. -/
def DiagGL2 : Set (GL (Fin 2) C.k) :=
  { g | g.val 0 1 = 0 ∧ g.val 1 0 = 0 }


/-- *Generic-indexed formulation of the Iwahori subgroup*: an element $g \in GL_2(k)$ belongs
to the Iwahori subgroup iff its diagonal entries are units, its strictly-upper-triangular
entries lie in $\mathfrak{o}$, and its strictly-lower-triangular entries lie in $\mathfrak{m}$.
This form quantifies over indices and is convenient for later generalisations. -/
def IwahoriGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, C.isUnitInO (g.val i i)) ∧
    (∀ i j : Fin 2, i < j → C.isInO (g.val i j)) ∧
    (∀ i j : Fin 2, j < i → C.isInMaxIdeal (g.val i j)) }

/-- *Generic-indexed formulation of the lower unipotent subgroup*: an element $g \in GL_2(k)$
is lower unipotent iff its diagonal entries are $1$ and its strictly-upper-triangular entries
vanish. -/
def LowerUnipGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, g.val i i = 1) ∧
    (∀ i j : Fin 2, i < j → g.val i j = 0) }

/-- *Generic-indexed formulation of the upper unipotent subgroup*: an element $g \in GL_2(k)$
is upper unipotent iff its diagonal entries are $1$ and its strictly-lower-triangular entries
vanish. -/
def UpperUnipGL2Gen : Set (GL (Fin 2) C.k) :=
  { g |
    (∀ i : Fin 2, g.val i i = 1) ∧
    (∀ i j : Fin 2, j < i → g.val i j = 0) }

/-- *Generic-indexed formulation of the diagonal subgroup*: an element $g \in GL_2(k)$ is
diagonal iff all its off-diagonal entries vanish. -/
def DiagGL2Gen : Set (GL (Fin 2) C.k) :=
  { g | ∀ i j : Fin 2, i ≠ j → g.val i j = 0 }


/-- *Generic and concrete Iwahori formulations agree*: the index-quantified definition
`IwahoriGL2Gen` describes the same set as the explicit four-entry condition `IwahoriGL2`. -/
lemma iwahoriGL2Gen_eq_iwahoriGL2 :
    C.IwahoriGL2Gen = C.IwahoriGL2 := by
  ext g
  simp only [IwahoriGL2Gen, IwahoriGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hupper, hlower⟩
    exact ⟨hdiag 0, hdiag 1, hupper 0 1 (by omega), hlower 1 0 (by omega)⟩
  · rintro ⟨h00, h11, h01, h10⟩
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> fin_cases j <;> simp_all

/-- *Generic and concrete lower-unipotent formulations agree*: the index-quantified definition
`LowerUnipGL2Gen` describes the same set as the explicit three-entry condition
`LowerUnipGL2`. -/
lemma lowerUnipGL2Gen_eq_lowerUnipGL2 :
    C.LowerUnipGL2Gen = C.LowerUnipGL2 := by
  ext g
  simp only [LowerUnipGL2Gen, LowerUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hupper⟩
    exact ⟨hdiag 0, hdiag 1, hupper 0 1 (by omega)⟩
  · rintro ⟨h00, h11, h01⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all

/-- *Generic and concrete upper-unipotent formulations agree*: the index-quantified definition
`UpperUnipGL2Gen` describes the same set as the explicit three-entry condition
`UpperUnipGL2`. -/
lemma upperUnipGL2Gen_eq_upperUnipGL2 :
    C.UpperUnipGL2Gen = C.UpperUnipGL2 := by
  ext g
  simp only [UpperUnipGL2Gen, UpperUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hlower⟩
    exact ⟨hdiag 0, hdiag 1, hlower 1 0 (by omega)⟩
  · rintro ⟨h00, h11, h10⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all

/-- *Generic and concrete diagonal formulations agree*: the index-quantified definition
`DiagGL2Gen` describes the same set as the explicit two-entry condition `DiagGL2`. -/
lemma diagGL2Gen_eq_diagGL2 :
    C.DiagGL2Gen = C.DiagGL2 := by
  ext g
  simp only [DiagGL2Gen, DiagGL2, Set.mem_setOf_eq]
  constructor
  · intro h; exact ⟨h 0 1 (by omega), h 1 0 (by omega)⟩
  · rintro ⟨h01, h10⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all


/-- *$1$ is a unit in $\mathfrak{o}$*: the multiplicative identity of $k$ comes from the unit
$1$ in the local ring $\mathfrak{o}$. -/
lemma isUnitInO_one : C.isUnitInO (1 : C.k) :=
  ⟨1, isUnit_one, C.embed.map_one⟩

/-- *$0$ lies in the maximal ideal*: the zero of $k$ comes from $0 \in \mathfrak{m}$. -/
lemma isInMaxIdeal_zero : C.isInMaxIdeal (0 : C.k) :=
  ⟨0, Ideal.zero_mem _, C.embed.map_zero⟩

/-- *Entry formula for a unipotent--diagonal--unipotent product*: when the middle factor $m$
is diagonal, the $(i,j)$ entry of the triple product $u' \cdot m \cdot u$ simplifies to
$u'_{i0} m_{00} u_{0j} + u'_{i1} m_{11} u_{1j}$. This identity is the computational core of
the explicit Iwahori decomposition for $GL_2$. -/
lemma gl2_triple_product_entry (u' m u : GL (Fin 2) C.k)
    (hm01 : m.val 0 1 = 0) (hm10 : m.val 1 0 = 0) (i j : Fin 2) :
    (u' * m * u).val i j =
      u'.val i 0 * m.val 0 0 * u.val 0 j +
      u'.val i 1 * m.val 1 1 * u.val 1 j := by
  show (u'.val * m.val * u.val) i j = _
  simp only [mul_apply, Fin.sum_univ_two]
  rw [hm01, hm10]; ring


/-- *Existence of the Iwahori decomposition for $GL_2$*: every Iwahori element $b$ factors as
a product $b = u' \cdot m \cdot u$ where $u'$ is lower unipotent (inside the Iwahori), $m$ is
diagonal (inside the Iwahori), and $u$ is upper unipotent (inside the Iwahori). Explicitly,
$u' = \begin{pmatrix} 1 & 0 \\ c a^{-1} & 1 \end{pmatrix}$,
$m = \mathrm{diag}(a, d - c a^{-1} \beta)$, and
$u = \begin{pmatrix} 1 & a^{-1}\beta \\ 0 & 1 \end{pmatrix}$, where
$a, \beta, c, d$ are the entries of $b$. -/
theorem iwahori_decomp_gl2_exists :
    ∀ b ∈ C.IwahoriGL2,
      ∃ (u' m u : GL (Fin 2) C.k),
        u' ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧
        m ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧
        u ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧
        b = u' * m * u := by
  intro b ⟨ha_unit, hd_unit, hβ_O, hc_m⟩
  set a := b.val 0 0
  set β := b.val 0 1
  set c := b.val 1 0
  set d := b.val 1 1
  have ha_ne : a ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero ha_unit
  have ha_inv_O : C.isInO a⁻¹ := DVRClosure.isUnitInO_inv ha_unit
  have hca_inv_m : C.isInMaxIdeal (c * a⁻¹) :=
    DVRClosureGL2.isInMaxIdeal_mul_isInO hc_m ha_inv_O
  have ha_inv_β_O : C.isInO (a⁻¹ * β) := DVRClosure.isInO_mul ha_inv_O hβ_O
  have hcab_m : C.isInMaxIdeal (c * a⁻¹ * β) :=
    DVRClosureGL2.isInMaxIdeal_mul_isInO hca_inv_m hβ_O
  have hd_mid_unit : C.isUnitInO (d - c * a⁻¹ * β) :=
    DVRClosureGL2.isUnitInO_sub_isInMaxIdeal hd_unit hcab_m
  have hd_mid_ne : d - c * a⁻¹ * β ≠ 0 :=
    DVRClosureGL2.isUnitInO_ne_zero hd_mid_unit

  let u'_f : Fin 2 → Fin 2 → C.k := ![![1, 0], ![c * a⁻¹, 1]]
  have hu'_det : (show Matrix (Fin 2) (Fin 2) C.k from u'_f).det ≠ 0 := by
    rw [det_fin_two]; simp [u'_f]

  let m_f : Fin 2 → Fin 2 → C.k := ![![a, 0], ![0, d - c * a⁻¹ * β]]
  have hm_det : (show Matrix (Fin 2) (Fin 2) C.k from m_f).det ≠ 0 := by
    rw [det_fin_two]; simp [m_f]; exact ⟨ha_ne, hd_mid_ne⟩

  let u_f : Fin 2 → Fin 2 → C.k := ![![1, a⁻¹ * β], ![0, 1]]
  have hu_det : (show Matrix (Fin 2) (Fin 2) C.k from u_f).det ≠ 0 := by
    rw [det_fin_two]; simp [u_f]
  let u'_gl := mkGL2 u'_f hu'_det
  let m_gl := mkGL2 m_f hm_det
  let u_gl := mkGL2 u_f hu_det

  have hu'_e : u'_gl.val 0 0 = 1 ∧ u'_gl.val 0 1 = 0 ∧
               u'_gl.val 1 0 = c * a⁻¹ ∧ u'_gl.val 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u'_gl, u'_f]
  have hm_e : m_gl.val 0 0 = a ∧ m_gl.val 0 1 = 0 ∧
              m_gl.val 1 0 = 0 ∧ m_gl.val 1 1 = d - c * a⁻¹ * β := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [m_gl, m_f]
  have hu_e : u_gl.val 0 0 = 1 ∧ u_gl.val 0 1 = a⁻¹ * β ∧
              u_gl.val 1 0 = 0 ∧ u_gl.val 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u_gl, u_f]
  refine ⟨u'_gl, m_gl, u_gl, ?_, ?_, ?_, ?_⟩

  · exact ⟨⟨hu'_e.1, hu'_e.2.2.2, hu'_e.2.1⟩,
           hu'_e.1 ▸ C.isUnitInO_one,
           hu'_e.2.2.2 ▸ C.isUnitInO_one,
           hu'_e.2.1 ▸ DVRClosure.isInO_zero,
           hu'_e.2.2.1 ▸ hca_inv_m⟩

  · exact ⟨⟨hm_e.2.1, hm_e.2.2.1⟩,
           hm_e.1 ▸ ha_unit,
           hm_e.2.2.2 ▸ hd_mid_unit,
           hm_e.2.1 ▸ DVRClosure.isInO_zero,
           hm_e.2.2.1 ▸ C.isInMaxIdeal_zero⟩

  · exact ⟨⟨hu_e.1, hu_e.2.2.2, hu_e.2.2.1⟩,
           hu_e.1 ▸ C.isUnitInO_one,
           hu_e.2.2.2 ▸ C.isUnitInO_one,
           hu_e.2.1 ▸ ha_inv_β_O,
           hu_e.2.2.1 ▸ C.isInMaxIdeal_zero⟩

  · apply Units.val_injective
    ext i j
    show b.val i j = (u'_gl * m_gl * u_gl).val i j
    rw [gl2_triple_product_entry C u'_gl m_gl u_gl hm_e.2.1 hm_e.2.2.1]
    fin_cases i <;> fin_cases j <;> dsimp

    · rw [hu'_e.1, hu'_e.2.1, hu_e.1, hu_e.2.2.1, hm_e.1, hm_e.2.2.2]; ring

    · rw [hu'_e.1, hu'_e.2.1, hu_e.2.1, hu_e.2.2.2, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero]
      rw [mul_inv_cancel_left₀ ha_ne]

    · rw [hu'_e.2.2.1, hu'_e.2.2.2, hu_e.1, hu_e.2.2.1, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero]
      rw [inv_mul_cancel_right₀ ha_ne]

    · rw [hu'_e.2.2.1, hu'_e.2.2.2, hu_e.2.1, hu_e.2.2.2, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one]
      rw [inv_mul_cancel_right₀ ha_ne, mul_assoc]
      exact (add_sub_cancel (c * (a⁻¹ * β)) d).symm


/-- *Uniqueness of the Iwahori decomposition for $GL_2$*: any two factorisations $b = u'_i
m_i u_i$ ($i = 1, 2$) of the same Iwahori element into lower-unipotent times diagonal times
upper-unipotent factors must coincide. The proof reads off the diagonal and off-diagonal
entries of $u'\,m\,u$ via `gl2_triple_product_entry`. -/
theorem iwahori_decomp_gl2_unique :
    ∀ b ∈ C.IwahoriGL2,
      ∀ (t₁ t₂ : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k),
        (t₁.1 ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧
         t₁.2.1 ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧
         t₁.2.2 ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧
         b = t₁.1 * t₁.2.1 * t₁.2.2) →
        (t₂.1 ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧
         t₂.2.1 ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧
         t₂.2.2 ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧
         b = t₂.1 * t₂.2.1 * t₂.2.2) →
        t₁ = t₂ := by
  intro b _hb ⟨u'₁, m₁, u₁⟩ ⟨u'₂, m₂, u₂⟩ h₁ h₂

  simp only [Prod.fst, Prod.snd] at h₁ h₂
  obtain ⟨⟨⟨hu'₁_00, hu'₁_11, hu'₁_01⟩, _⟩,
          ⟨⟨hm₁_01, hm₁_10⟩, hm₁_iwa⟩,
          ⟨⟨hu₁_00, hu₁_11, hu₁_10⟩, _⟩, heq₁⟩ := h₁
  obtain ⟨⟨⟨hu'₂_00, hu'₂_11, hu'₂_01⟩, _⟩,
          ⟨⟨hm₂_01, hm₂_10⟩, _⟩,
          ⟨⟨hu₂_00, hu₂_11, hu₂_10⟩, _⟩, heq₂⟩ := h₂

  have h_eq : u'₁ * m₁ * u₁ = u'₂ * m₂ * u₂ := by rw [← heq₁, ← heq₂]
  have h_entry : ∀ i j : Fin 2,
      (u'₁ * m₁ * u₁).val i j = (u'₂ * m₂ * u₂).val i j := by
    intro i j; rw [h_eq]

  have p₁ := gl2_triple_product_entry C u'₁ m₁ u₁ hm₁_01 hm₁_10
  have p₂ := gl2_triple_product_entry C u'₂ m₂ u₂ hm₂_01 hm₂_10

  have hm00_ne : m₁.val 0 0 ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero hm₁_iwa.1

  have hm00 : m₁.val 0 0 = m₂.val 0 0 := by
    have := h_entry 0 0; rw [p₁, p₂] at this
    rw [hu'₁_00, hu'₁_01, hu₁_00, hu₁_10,
        hu'₂_00, hu'₂_01, hu₂_00, hu₂_10] at this
    ring_nf at this; exact this

  have hu01 : u₁.val 0 1 = u₂.val 0 1 := by
    have := h_entry 0 1; rw [p₁, p₂] at this
    rw [hu'₁_00, hu'₁_01, hu₁_11,
        hu'₂_00, hu'₂_01, hu₂_11] at this
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero] at this
    rw [hm00] at this
    have hm₂_ne : (↑m₂ : Matrix (Fin 2) (Fin 2) C.k) 0 0 ≠ 0 := hm00 ▸ hm00_ne
    exact mul_left_cancel₀ hm₂_ne this

  have hu'10 : u'₁.val 1 0 = u'₂.val 1 0 := by
    have := h_entry 1 0; rw [p₁, p₂] at this
    rw [hu'₁_11, hu₁_00, hu₁_10,
        hu'₂_11, hu₂_00, hu₂_10] at this
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero] at this
    rw [hm00] at this
    have hm₂_ne : (↑m₂ : Matrix (Fin 2) (Fin 2) C.k) 0 0 ≠ 0 := hm00 ▸ hm00_ne
    exact mul_right_cancel₀ hm₂_ne this

  have hm11 : m₁.val 1 1 = m₂.val 1 1 := by
    have := h_entry 1 1; rw [p₁, p₂] at this
    rw [hu'₁_11, hu₁_11, hu'₂_11, hu₂_11] at this
    simp only [one_mul, mul_one] at this
    rw [hu'10, hm00, hu01] at this
    exact add_left_cancel this

  have h_u'_eq : u'₁ = u'₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hu'10 | simp_all
  have h_m_eq : m₁ = m₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hm00 | exact hm11 | simp_all
  have h_u_eq : u₁ = u₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hu01 | simp_all
  exact Prod.ext h_u'_eq (Prod.ext h_m_eq h_u_eq)


/-- *Iwahori decomposition for $GL_2$ (generic form)*: every element of the Iwahori subgroup
$I$ of $GL_2$ factors uniquely as $b = u' \cdot m \cdot u$ with $u' \in U^- \cap I$,
$m \in T \cap I$, and $u \in U^+ \cap I$, where $U^\pm$ are the (lower/upper) unipotent
subgroups and $T$ is the diagonal torus. This is the abstract statement using the
index-quantified group definitions. -/
theorem IwahoriDecomposition :
    ∀ b ∈ C.IwahoriGL2Gen,
      ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k),
        let (u', m, u) := triple
        u' ∈ C.LowerUnipGL2Gen ∩ C.IwahoriGL2Gen ∧
        m ∈ C.DiagGL2Gen ∩ C.IwahoriGL2Gen ∧
        u ∈ C.UpperUnipGL2Gen ∩ C.IwahoriGL2Gen ∧
        b = u' * m * u := by

  rw [iwahoriGL2Gen_eq_iwahoriGL2, lowerUnipGL2Gen_eq_lowerUnipGL2,
      upperUnipGL2Gen_eq_upperUnipGL2, diagGL2Gen_eq_diagGL2]

  intro b hb

  obtain ⟨u', m, u, hu'_mem, hm_mem, hu_mem, heq⟩ :=
    C.iwahori_decomp_gl2_exists b hb

  refine ⟨(u', m, u), ⟨hu'_mem, hm_mem, hu_mem, heq⟩, ?_⟩
  intro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂, hm₂, hu₂, heq₂⟩
  exact C.iwahori_decomp_gl2_unique b hb
    (u'₂, m₂, u₂) (u', m, u)
    ⟨hu'₂, hm₂, hu₂, heq₂⟩ ⟨hu'_mem, hm_mem, hu_mem, heq⟩

/-- *Iwahori decomposition for $GL_2$ (concrete form)*: the same unique factorisation
$b = u' \cdot m \cdot u$ as `IwahoriDecomposition`, phrased using the explicit four-entry
membership conditions rather than the index-quantified ones. -/
theorem IwahoriDecomposition_concrete :
    ∀ b ∈ C.IwahoriGL2,
      ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k),
        let (u', m, u) := triple
        u' ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧
        m ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧
        u ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧
        b = u' * m * u := by
  rw [← iwahoriGL2Gen_eq_iwahoriGL2, ← lowerUnipGL2Gen_eq_lowerUnipGL2,
      ← upperUnipGL2Gen_eq_upperUnipGL2, ← diagGL2Gen_eq_diagGL2]
  exact C.IwahoriDecomposition

end GL2

end DVRContext
