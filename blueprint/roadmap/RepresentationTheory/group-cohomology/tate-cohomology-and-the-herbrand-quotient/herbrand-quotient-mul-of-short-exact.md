# Multiplicativity of the Herbrand quotient in short exact sequences

Let $G$ be a finite cyclic group, $R$ a commutative ring and

$$0 \to A \to B \to C \to 0$$

a short exact sequence of $R$-linear representations of $G$. If two of $A$, $B$, $C$ satisfy the
Herbrand finiteness hypothesis, that is, their Tate cohomology groups $\hat H^0(G, \cdot)$ and
$\hat H^{-1}(G, \cdot)$ are finite, then so does the third, and the Herbrand quotients
$h(M) = |\hat H^0(G, M)| / |\hat H^{-1}(G, M)|$ satisfy

$$h(B) = h(A) \, h(C).$$

Milne states the result for $G$-modules, that is, for $R = \mathbb{Z}$. The Tate cohomology groups of
an $R$-linear representation are, as abelian groups, those of its underlying $G$-module, so the
statement above is the same. Milne's Herbrand quotient divides by $|H^1(G, M)|$ instead of
$|\hat H^{-1}(G, M)|$; for cyclic $G$ the two groups are isomorphic by the periodicity of Tate
cohomology, so the two quotients agree.

Milne's proof truncates the long exact sequence of Tate cohomology. With the periodicity
isomorphisms $\hat H^r(G, \cdot) \cong \hat H^{r+2}(G, \cdot)$ that a generator of $G$ determines,
the cokernels of $\hat H^{-1}(G, B) \to \hat H^{-1}(G, C)$ and of $H^1(G, B) \to H^1(G, C)$ are
isomorphic, and this turns the long exact sequence into a finite exact sequence through
$\hat H^0$ and $H^1$ of $A$, $B$ and $C$. The alternating product of the orders of the groups in a
finite exact sequence of finite groups is $1$, which gives the formula. The comparison of the two
cokernels uses that the periodicity isomorphisms commute with the maps induced by $B \to C$, their
[naturality](natural-periodicity-iso.md), which is more than the
[existence of an isomorphism for each representation](nonempty-periodicity-iso.md).

## Depends on

- [Herbrand quotient](herbrand-quotient.md)
- [Finiteness hypothesis for the Herbrand quotient](herbrand-finite.md)

## Proof depends on

- [Naturality of the periodicity isomorphisms of Tate cohomology for finite cyclic groups](natural-periodicity-iso.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter II, §3: Proposition 3.6 (the statement,
  for an exact sequence of $G$-modules and $G$ finite cyclic) with its proof and Lemma 3.7 (orders in a
  finite exact sequence); Proposition 3.4 (periodicity) and the definition of the Herbrand quotient
  before Proposition 3.6.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.GroupCoh.herbrandQuotient_eq_mul_of_shortExact`, in
  its proof of the first inequality of global class field theory.
