/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Atlas.TheoryOfComputation.code.BPP
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite

import Mathlib.Algebra.Order.Archimedean.Basic

namespace Probabilistic

/-- A formal description of a pair of finite simple graphs `(G, H)`, packaged
together with the decidability and finiteness instances needed to manipulate
them constructively. Used as the underlying mathematical object for the graph
isomorphism problem `ISO`. -/
structure GraphPairDesc where
  V : Type
  instFintypeV : Fintype V
  instDecEqV : DecidableEq V
  G : SimpleGraph V
  instDecRelG : DecidableRel G.Adj
  W : Type
  instFintypeW : Fintype W
  instDecEqW : DecidableEq W
  H : SimpleGraph W
  instDecRelH : DecidableRel H.Adj

/-- A graph-pair description `d` is *isomorphic* if there exists a graph
isomorphism `d.G ≃g d.H`. This is the property defining membership in `ISO`. -/
def GraphPairDesc.isIsomorphic (d : GraphPairDesc) : Prop :=
  Nonempty (d.G ≃g d.H)

/-- A faithful encoding of graph-pair descriptions as strings over alphabet `Γ`,
specified by an injective `encode` function and a `decode` function that inverts
it. Used to turn the mathematical object `GraphPairDesc` into the language
`ISO ⊆ List Γ`. -/
structure GraphPairEncoding (Γ : Type) where
  encode : GraphPairDesc → List Γ
  decode : List Γ → Option GraphPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The graph isomorphism language

`ISO = {⟨G, H⟩ ∣ G and H are isomorphic graphs}`,

defined here as the set of strings `s` over alphabet `Γ` that encode some
graph-pair description `d` for which `d.G ≃g d.H`. -/
def ISO {Γ : Type} (enc : GraphPairEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : GraphPairDesc, enc.encode d = s ∧ d.isIsomorphic}

open Polynomial in
/-- **Polynomial Lemma.** A non-zero univariate polynomial `p : F[X]` over a
field has at most `deg p` roots: the cardinality of its root multiset is bounded
by its degree. -/
theorem polynomial_roots_le_degree {F : Type*} [Field F] (p : F[X]) (hp : p ≠ 0) :
    (Multiset.card (p.roots) : WithBot ℕ) ≤ p.degree :=
  Polynomial.card_roots hp

open Polynomial in
/-- **Corollary of the Polynomial Lemma.** If `p₁, p₂ : F[X]` both have degree
`≤ d` and `p₁ ≠ p₂`, then they agree on at most `d` points: equivalently, the
difference `p₁ - p₂` has at most `d` roots. -/
theorem distinct_poly_agree_le_degree {F : Type*} [Field F]
    (p₁ p₂ : F[X]) (d : ℕ)
    (hd₁ : p₁.natDegree ≤ d) (hd₂ : p₂.natDegree ≤ d) (_hne : p₁ ≠ p₂) :
    Multiset.card (p₁ - p₂).roots ≤ d :=
  calc Multiset.card (p₁ - p₂).roots
      ≤ (p₁ - p₂).natDegree := Polynomial.card_roots' _
    _ ≤ max p₁.natDegree p₂.natDegree := Polynomial.natDegree_sub_le p₁ p₂
    _ ≤ d := max_le hd₁ hd₂

open Polynomial in
/-- Over a finite field `F`, a non-zero polynomial of degree `≤ d` has at most
`d` roots inside `F`: the cardinality of `{r ∈ F ∣ p(r) = 0}` is bounded by
`d`. -/
theorem poly_root_count_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : F[X]) (hp : p ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    (Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card ≤ d := by
  calc (Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card
      ≤ p.roots.toFinset.card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rw [Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hp).mpr hr
    _ ≤ p.roots.card := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ d := hd

open Polynomial in
/-- **Univariate Schwartz-Zippel (probability form).** If `p ∈ F[X]` is non-zero
with degree `≤ d` and `r` is chosen uniformly at random from a finite field `F`,
then `Pr[p(r) = 0] ≤ d / |F|`. -/
theorem poly_root_prob_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : F[X]) (hp : p ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    ((Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card : ℚ) / Fintype.card F
      ≤ (d : ℚ) / Fintype.card F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr Fintype.card_pos).le
  exact_mod_cast poly_root_count_le p hp d hd

open Finset MvPolynomial Fintype in
/-- **Schwartz-Zippel Lemma (Sipser textbook form).** If
`p(x₁, …, xₘ) ∈ F[x₁, …, xₘ]` is a non-zero multivariate polynomial of degree
`≤ d` in each variable and `r₁, …, rₘ` are chosen uniformly at random from a
finite field `F`, then

`Pr[p(r₁, …, rₘ) = 0] ≤ dm / |F|`. -/
theorem schwartz_zippel_book
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} {p : MvPolynomial (Fin m) F} (hp : p ≠ 0) (d : ℕ)
    (hd : ∀ i : Fin m, p.degreeOf i ≤ d) :
    (#{r ∈ (univ : Finset (Fin m → F)) | MvPolynomial.eval r p = 0} : ℚ≥0) /
      ((Fintype.card F : ℚ≥0) ^ m) ≤
    (d * m : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  rw [show (univ : Finset (Fin m → F)) = piFinset fun _ => (univ : Finset F) from
    piFinset_univ.symm]
  have h := MvPolynomial.schwartz_zippel_sum_degreeOf hp (fun _ => (Finset.univ : Finset F))
  simp only [Finset.card_univ] at h
  calc (#{f ∈ piFinset fun _ => Finset.univ | (MvPolynomial.eval f) p = 0} : ℚ≥0) /
      ((Fintype.card F : ℚ≥0) ^ m)
    = (#{f ∈ piFinset fun _ => Finset.univ | (MvPolynomial.eval f) p = 0} : ℚ≥0) /
      (∏ _ : Fin m, (Fintype.card F : ℚ≥0)) := by simp
    _ ≤ ∑ i : Fin m, ((p.degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)) := h
    _ ≤ ∑ _ : Fin m, ((d : ℚ≥0) / (Fintype.card F : ℚ≥0)) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact Nat.cast_le.mpr (hd i)
    _ = (d * m : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end Probabilistic

namespace TuringMachine

open TuringMachine

/-- A language `A ⊆ Σ*` is *in BPP with error `ε`* if some polynomial-time
probabilistic Turing machine `M` decides `A` with two-sided error `ε`: there
exist `Q`, `M`, an exponent `k`, and a runtime bound `t'` such that `M` runs in
time `t'`, `t' = O(nᵏ)`, and `M.decidesWithError A ε t'` holds. The class BPP
itself corresponds to `ε = 1/3`. -/
def InBPPWithError {Γ : Type} [DecidableEq Γ] (ε : ℚ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : PTM Q Γ) (k : ℕ) (t' : ℕ → ℕ),
    M.runsInTime t' ∧
    IsBigO t' (fun n => n ^ k) ∧
    M.decidesWithError A ε t'

/-- Monotonicity of `decidesWithError`: if a PTM `M` decides `A` with error at
most `ε₁` and `ε₁ ≤ ε₂`, then it also decides `A` with error at most `ε₂`. -/
lemma decidesWithError_mono {Q : Type} [DecidableEq Q] {Γ : Type} [DecidableEq Γ]
    (M : PTM Q Γ) (A : Set (List Γ)) (ε₁ ε₂ : ℚ) (t : ℕ → ℕ)
    (hle : ε₁ ≤ ε₂) (hε₂ : 0 ≤ ε₂) (hDec : M.decidesWithError A ε₁ t) :
    M.decidesWithError A ε₂ t :=
  ⟨hε₂, fun w hw => le_trans (hDec.2.1 w hw) hle,
   fun w hw => le_trans (hDec.2.2 w hw) hle⟩


/-- Arithmetic fact: for `0 < ε < 1/2`, the majority-vote error update
`ε ↦ ε² (3 - 2ε)` strictly decreases `ε`. -/
lemma error_reduction_lt (ε : ℚ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2) :
    ε ^ 2 * (3 - 2 * ε) < ε := by
  have h1 : ε * (3 - 2 * ε) < 1 := by nlinarith
  nlinarith [sq_nonneg ε]

/-- Arithmetic fact: for `0 < ε < 1/2`, the majority-vote error update
`ε² (3 - 2ε)` is strictly positive. -/
lemma error_reduction_pos (ε : ℚ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2) :
    0 < ε ^ 2 * (3 - 2 * ε) := by
  apply mul_pos (sq_pos_of_pos hε_pos)
  linarith

/-- Arithmetic fact: the majority-vote error update stays in `(0, 1/2)`, i.e.
`ε² (3 - 2ε) < 1/2` whenever `0 < ε < 1/2`. -/
lemma error_reduction_lt_half (ε : ℚ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2) :
    ε ^ 2 * (3 - 2 * ε) < 1 / 2 :=
  lt_trans (error_reduction_lt ε hε_pos hε_lt) hε_lt

/-- The sequence of error bounds obtained by iterating the majority-vote
update: `iterError ε₁ 0 = ε₁`, and `iterError ε₁ (n+1) = e² (3 - 2e)` where
`e = iterError ε₁ n`. Each step corresponds to amplifying the BPP machine by a
three-fold majority vote. -/
noncomputable def iterError (ε₁ : ℚ) : ℕ → ℚ
  | 0 => ε₁
  | n + 1 => let e := iterError ε₁ n; e ^ 2 * (3 - 2 * e)

/-- Joint invariant: every iterate `iterError ε₁ n` stays strictly between `0`
and `1/2`, provided the initial error `ε₁` does. -/
lemma iterError_pos_and_lt_half (ε₁ : ℚ) (hε₁_pos : 0 < ε₁) (hε₁_lt : ε₁ < 1 / 2) :
    ∀ n, 0 < iterError ε₁ n ∧ iterError ε₁ n < 1 / 2 := by
  intro n; induction n with
  | zero => exact ⟨hε₁_pos, hε₁_lt⟩
  | succ n ih =>
    constructor
    · exact error_reduction_pos _ ih.1 ih.2
    · exact error_reduction_lt_half _ ih.1 ih.2

/-- Positivity of the iterated error: `iterError ε₁ n > 0` for all `n`, given
`0 < ε₁ < 1/2`. -/
lemma iterError_pos (ε₁ : ℚ) (hε₁_pos : 0 < ε₁) (hε₁_lt : ε₁ < 1 / 2) (n : ℕ) :
    0 < iterError ε₁ n :=
  (iterError_pos_and_lt_half ε₁ hε₁_pos hε₁_lt n).1

/-- Upper bound on the iterated error: `iterError ε₁ n < 1/2` for all `n`,
given `0 < ε₁ < 1/2`. -/
lemma iterError_lt_half (ε₁ : ℚ) (hε₁_pos : 0 < ε₁) (hε₁_lt : ε₁ < 1 / 2) (n : ℕ) :
    iterError ε₁ n < 1 / 2 :=
  (iterError_pos_and_lt_half ε₁ hε₁_pos hε₁_lt n).2


/-- Convergence of the iterated error to zero: for any target `ε₂ > 0` there
exists some iteration count `n` with `iterError ε₁ n ≤ ε₂`. The proof bounds
`iterError ε₁ n ≤ ε₁ · rⁿ` for `r = ε₁(3 - 2ε₁) < 1` and uses that geometric
sequences with ratio `< 1` shrink below any positive threshold. -/
lemma iterError_eventually_le (ε₁ ε₂ : ℚ)
    (hε₁_pos : 0 < ε₁) (hε₁_lt : ε₁ < 1 / 2)
    (hε₂_pos : 0 < ε₂) :
    ∃ n, iterError ε₁ n ≤ ε₂ := by

  set r := ε₁ * (3 - 2 * ε₁) with hr_def
  have hr_pos : (0 : ℚ) < r := by rw [hr_def]; nlinarith
  have hr_lt : r < 1 := by rw [hr_def]; nlinarith

  have bound : ∀ n, iterError ε₁ n ≤ ε₁ * r ^ n := by
    intro n; induction n with
    | zero => simp [iterError]
    | succ n ih =>
      have hiter_pos := iterError_pos ε₁ hε₁_pos hε₁_lt n
      have hiter_lt := iterError_lt_half ε₁ hε₁_pos hε₁_lt n
      have hiter_le : iterError ε₁ n ≤ ε₁ := by
        clear ih; induction n with
        | zero => simp [iterError]
        | succ m ihm =>
          exact le_trans (le_of_lt (error_reduction_lt _
            (iterError_pos ε₁ hε₁_pos hε₁_lt m)
            (iterError_lt_half ε₁ hε₁_pos hε₁_lt m)))
            (ihm (iterError_pos ε₁ hε₁_pos hε₁_lt m)
              (iterError_lt_half ε₁ hε₁_pos hε₁_lt m))
      have ratio_bound : iterError ε₁ n * (3 - 2 * iterError ε₁ n) ≤ r := by
        rw [hr_def]; nlinarith


      show iterError ε₁ n ^ 2 * (3 - 2 * iterError ε₁ n) ≤ ε₁ * r ^ (n + 1)
      have h1 : iterError ε₁ n ^ 2 * (3 - 2 * iterError ε₁ n) =
          iterError ε₁ n * (iterError ε₁ n * (3 - 2 * iterError ε₁ n)) := by ring
      rw [h1, pow_succ]
      calc iterError ε₁ n * (iterError ε₁ n * (3 - 2 * iterError ε₁ n))
          ≤ iterError ε₁ n * r :=
            mul_le_mul_of_nonneg_left ratio_bound (le_of_lt hiter_pos)
        _ ≤ (ε₁ * r ^ n) * r :=
            mul_le_mul_of_nonneg_right ih (le_of_lt hr_pos)
        _ = ε₁ * (r ^ n * r) := by ring

  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε₂_pos hε₁_pos) hr_lt
  refine ⟨n, le_trans (bound n) (le_of_lt ?_)⟩
  rwa [lt_div_iff₀ hε₁_pos, mul_comm] at hn



end TuringMachine

namespace BranchingPrograms

open TuringMachine

/-- A node of a branching program with `m` input variables and `N` total nodes.
A node is either a `query` on variable `var : Fin m` with two successors `zero,
one : Fin N` (followed depending on whether the bit is `0` or `1`), or an
`output` leaf carrying a Boolean answer. -/
inductive BPNode (m : ℕ) (N : ℕ) where
  | query (var : Fin m) (zero : Fin N) (one : Fin N) : BPNode m N
  | output (val : Bool) : BPNode m N

/-- A branching program on `m` Boolean input variables. It has `numNodes`
nodes (with node `0` being the start node) and a `nodes` table assigning each
index a `BPNode`. -/
structure BranchingProgram (m : ℕ) where
  numNodes : ℕ
  numNodes_pos : 0 < numNodes
  nodes : Fin numNodes → BPNode m numNodes

/-- Evaluate a branching program `bp` on a Boolean `assignment`. Execution
starts at node `0` and follows `query` edges according to the assignment; the
recursion is bounded by `bp.numNodes` units of fuel via the inner `go`. -/
def BranchingProgram.eval (bp : BranchingProgram m) (assignment : Fin m → Bool)
    : Bool :=
  go bp assignment ⟨0, bp.numNodes_pos⟩ bp.numNodes
where
  go (bp : BranchingProgram m) (assignment : Fin m → Bool)
      (node : Fin bp.numNodes) : ℕ → Bool
    | 0 => false
    | fuel + 1 =>
      match bp.nodes node with
      | BPNode.output val => val
      | BPNode.query var zero one =>
        if assignment var then go bp assignment one fuel
        else go bp assignment zero fuel

/-- Two branching programs are *equivalent* (`B₁ ≡ B₂`) if they compute the
same Boolean function: `bp₁.eval a = bp₂.eval a` for every assignment `a`. -/
def BPEquiv (bp₁ bp₂ : BranchingProgram m) : Prop :=
  ∀ assignment : Fin m → Bool, bp₁.eval assignment = bp₂.eval assignment

/-- A branching program is *read-once* if, along any computation path, each
input variable is queried at most once. Formally: for every list of nodes
`path` along which the program might step, any two indices `i, j` whose nodes
both `query` the same variable `v` must coincide. -/
def BranchingProgram.isReadOnce (bp : BranchingProgram m) : Prop :=
  ∀ (path : List (Fin bp.numNodes)),
    (∀ (i j : Fin path.length) (v : Fin m),
      (∃ z o, bp.nodes (path.get i) = BPNode.query v z o) →
      (∃ z o, bp.nodes (path.get j) = BPNode.query v z o) →
      i = j)

/-- A description of a pair `(B₁, B₂)` of read-once branching programs on the
same number of variables, together with proofs that each is read-once. This is
the mathematical object whose equivalence problem is `EQ_ROBP`. -/
structure ROBPPairDesc where
  numVars : ℕ
  B₁ : BranchingProgram numVars
  B₂ : BranchingProgram numVars
  B₁_readOnce : B₁.isReadOnce
  B₂_readOnce : B₂.isReadOnce

/-- The semantic equivalence relation on `ROBPPairDesc`: `d.B₁ ≡ d.B₂` as
Boolean functions. -/
def ROBPPairDesc.isEquivalent (d : ROBPPairDesc) : Prop :=
  BPEquiv d.B₁ d.B₂

/-- A faithful encoding of `ROBPPairDesc` as strings over alphabet `Γ`, used
to turn the abstract equivalence problem into a language `EQ_ROBP ⊆ List Γ`. -/
structure ROBPPairEncoding (Γ : Type) where
  encode : ROBPPairDesc → List Γ
  decode : List Γ → Option ROBPPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The language of equivalent read-once branching programs:

`EQ_ROBP = {⟨B₁, B₂⟩ ∣ B₁ ≡ B₂ as ROBPs}`,

with the pair encoded as a string over `Γ` using `enc`. Membership in BPP is
proved in `EQ_ROBP_in_BPP`. -/
def EQ_ROBP {Γ : Type} (enc : ROBPPairEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : ROBPPairDesc, enc.encode d = s ∧ d.isEquivalent}

/-- Number of random bits used by the `EQ_ROBP` BPP decider on inputs of
length `n`: a polynomial budget of `n² + 1` bits, enough to sample a random
field element per variable. -/
def eqROBP_numBits (n : ℕ) : ℕ := n ^ 2 + 1

/-- The random-bit budget `eqROBP_numBits n = n² + 1` is polynomial in `n`,
specifically `O(n²)`. -/
theorem eqROBP_numBits_poly : IsBigO eqROBP_numBits (fun n => n ^ 2) :=
  ⟨2, 1, by norm_num, fun n hn => by simp [eqROBP_numBits]; nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0)]⟩




open MvPolynomial Finset in
/-- The arithmetization "edge factor" for variable `i` and bit `b`: returns the
multivariate polynomial `Xᵢ` when `b = true` and `1 - Xᵢ` when `b = false`.
Evaluated at a Boolean point, this factor is `1` iff `xᵢ = b`. -/
noncomputable def edgeFactor {m : ℕ} (R : Type*) [CommRing R] (i : Fin m) (b : Bool) :
    MvPolynomial (Fin m) R :=
  if b then X i else 1 - X i

/-- Simp lemma: `edgeFactor R i true = Xᵢ`. -/
@[simp]
theorem edgeFactor_true {m : ℕ} {R : Type*} [CommRing R] (i : Fin m) :
    edgeFactor R i true = MvPolynomial.X i := by
  simp [edgeFactor]

/-- Simp lemma: `edgeFactor R i false = 1 - Xᵢ`. -/
@[simp]
theorem edgeFactor_false {m : ℕ} {R : Type*} [CommRing R] (i : Fin m) :
    edgeFactor R i false = 1 - MvPolynomial.X i := by
  simp [edgeFactor]

open MvPolynomial Finset in
/-- The monomial associated to a Boolean assignment `a : Fin m → Bool`:
`∏ᵢ edgeFactor R i (a i)`, i.e. the product `∏ᵢ Xᵢ^{aᵢ} (1 - Xᵢ)^{1 - aᵢ}`.
Over a Boolean point `x`, this is the indicator `[x = a]`. -/
noncomputable def pathMonomial {m : ℕ} (R : Type*) [CommRing R] (a : Fin m → Bool) :
    MvPolynomial (Fin m) R :=
  ∏ i : Fin m, edgeFactor R i (a i)

open MvPolynomial Finset in
/-- Arithmetization of a Boolean function `f : 2^m → 2` as a multilinear
polynomial: sum of `pathMonomial R a` over all assignments `a` with `f a =
true`. On Boolean inputs this evaluates to `1` iff `f a = true`. -/
noncomputable def arithmetizeFn {m : ℕ} (R : Type*) [CommRing R]
    (f : (Fin m → Bool) → Bool) : MvPolynomial (Fin m) R :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = true), pathMonomial R a

open MvPolynomial Finset in
/-- Arithmetization of a branching program `bp`: the multivariate polynomial
representing the Boolean function `bp.eval`. Two equivalent ROBPs arithmetize
to equal polynomials, which is the algebraic core of the `EQ_ROBP ∈ BPP`
proof. -/
noncomputable def arithmetize {m : ℕ} (R : Type*) [CommRing R]
    (bp : BranchingProgram m) : MvPolynomial (Fin m) R :=
  arithmetizeFn R bp.eval

open MvPolynomial Finset in
/-- The degree of any single variable `Xⱼ` in the monomial `Xᵢ` is at most `1`
(it is `1` when `i = j` and `0` otherwise). -/
theorem degreeOf_X_le_one' {m : ℕ} {R : Type*} [CommRing R]
    (i j : Fin m) :
    degreeOf j (X i : MvPolynomial (Fin m) R) ≤ 1 := by
  rw [degreeOf_le_iff]
  intro d hd
  have : d ∈ ({Finsupp.single i 1} : Finset (Fin m →₀ ℕ)) :=
    support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

open MvPolynomial Finset in
/-- Every variable appears with degree at most `1` in the edge factor
`edgeFactor R i b` (which is `Xᵢ` or `1 - Xᵢ`). -/
theorem degreeOf_edgeFactor_le {m : ℕ} {R : Type*} [CommRing R]
    (i j : Fin m) (b : Bool) :
    degreeOf j (edgeFactor R i b) ≤ 1 := by
  cases b with
  | true =>
    simp only [edgeFactor_true]
    exact degreeOf_X_le_one' i j
  | false =>
    simp only [edgeFactor_false]
    calc degreeOf j (1 - X i : MvPolynomial (Fin m) R)
        ≤ max (degreeOf j (1 : MvPolynomial (Fin m) R))
              (degreeOf j (X i : MvPolynomial (Fin m) R)) :=
          degreeOf_sub_le j 1 (X i)
      _ ≤ max 0 1 := by
          apply max_le_max
          · exact le_of_eq (degreeOf_one j)
          · exact degreeOf_X_le_one' i j
      _ = 1 := by norm_num

open MvPolynomial Finset in
/-- A different variable does not appear: `degreeOf j Xᵢ = 0` whenever
`j ≠ i`. -/
theorem degreeOf_X_of_ne' {m : ℕ} {R : Type*} [CommRing R]
    (i j : Fin m) (hij : j ≠ i) :
    degreeOf j (X i : MvPolynomial (Fin m) R) = 0 := by
  apply Nat.le_zero.mp
  rw [degreeOf_le_iff]
  intro d hd
  have : d ∈ ({Finsupp.single i 1} : Finset (Fin m →₀ ℕ)) :=
    support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  simp [hij]

open MvPolynomial Finset in
/-- An unrelated variable does not appear in an edge factor:
`degreeOf j (edgeFactor R i b) = 0` whenever `j ≠ i`. -/
theorem degreeOf_edgeFactor_of_ne {m : ℕ} {R : Type*} [CommRing R]
    (i j : Fin m) (b : Bool) (hij : j ≠ i) :
    degreeOf j (edgeFactor R i b) = 0 := by
  cases b with
  | true =>
    simp only [edgeFactor_true]
    exact degreeOf_X_of_ne' i j hij
  | false =>
    simp only [edgeFactor_false]
    apply Nat.le_zero.mp
    calc degreeOf j (1 - X i : MvPolynomial (Fin m) R)
        ≤ max (degreeOf j (1 : MvPolynomial (Fin m) R))
              (degreeOf j (X i : MvPolynomial (Fin m) R)) :=
          degreeOf_sub_le j 1 (X i)
      _ = max 0 0 := by
          rw [degreeOf_one, degreeOf_X_of_ne' i j hij]
      _ = 0 := by norm_num

open MvPolynomial Finset in
/-- Each path monomial is multilinear: every variable `j` appears with degree
at most `1` in `pathMonomial R a`. -/
theorem degreeOf_pathMonomial_le {m : ℕ} {R : Type*} [CommRing R]
    (a : Fin m → Bool) (j : Fin m) :
    degreeOf j (pathMonomial R a) ≤ 1 := by
  unfold pathMonomial
  calc degreeOf j (∏ i : Fin m, edgeFactor R i (a i))
      ≤ ∑ i : Fin m, degreeOf j (edgeFactor R i (a i)) :=
        degreeOf_prod_le j Finset.univ _
    _ ≤ ∑ i : Fin m, (if j = i then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hij
        · subst hij
          exact degreeOf_edgeFactor_le j j (a j)
        · exact le_of_eq (degreeOf_edgeFactor_of_ne i j (a i) hij)
    _ = 1 := by simp

open MvPolynomial Finset in
/-- The arithmetization of any branching program is multilinear: each variable
appears with degree at most `1` in `arithmetize R bp`. This is the degree
bound that feeds into Schwartz-Zippel for the `EQ_ROBP` soundness argument. -/
theorem arithmetize_degreeOf_le {m : ℕ} {R : Type*} [CommRing R]
    (bp : BranchingProgram m) (j : Fin m) :
    degreeOf j (arithmetize R bp) ≤ 1 := by
  unfold arithmetize arithmetizeFn
  calc degreeOf j (∑ a ∈ Finset.univ.filter (fun a => bp.eval a = true), pathMonomial R a)
      ≤ (Finset.univ.filter (fun a => bp.eval a = true)).sup
          (fun a => degreeOf j (pathMonomial R a)) :=
        degreeOf_sum_le j _ _
    _ ≤ 1 := by
        apply Finset.sup_le
        intro a _
        exact degreeOf_pathMonomial_le a j

end BranchingPrograms
