# The theory of the primitive recursive m-degrees of computable sets is hereditarily undecidable

The first-order theory of the upper semilattice of computable sets under many-one reductions by primitive recursive functions is hereditarily
undecidable: every subtheory in the same language is undecidable.

For $A, B \subseteq \mathbb{N}$, $A$ is *primitively recursively $m$-reducible* to $B$, written $A \le^{pr}_m B$, if some primitive recursive function $f$ satisfies $x \in A \iff f(x) \in B$ for all $x$. The induced equivalence classes of computable sets, other than those of $\emptyset$ and $\mathbb{N}$, form the
*primitive recursive $m$-degrees* $\mathbf{C}^{pr}_m$, a distributive upper semilattice under the order induced by $\le^{pr}_m$ and the join induced by $A \oplus B$. A theory is *hereditarily undecidable* if all of its subtheories in the same language are undecidable.

**Theorem (Kalmurzayev, Bazhenov and Iskakov).** The first-order theory of $\mathbf{C}^{pr}_m$ in the language of upper semilattices, with the partial order and the join, is hereditarily undecidable (Theorem 1 of the source).

It follows the outline of undecidability results of Downey and Nies for degree structures of low complexity time classes.

## Depends on

- [Complete theory of a first-order structure](../../Logic/first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof follows the scheme of Downey and Nies: it interprets, with parameters, inside $\mathbf{C}^{pr}_m$ the lattice of $\Sigma^0_n$-ideals of an effectively dense $\Sigma^0_n$-Boolean algebra, whose theory is hereditarily undecidable by a theorem of Nies. The interpretation uses a primitive recursive version of
*super sparse* sets: the degrees below a suitable super sparse set behave like the ideals of the Boolean algebra, by a main lemma proved by a construction with requirements. A complete expansion links Nies's theorem on lattices of $\Sigma^0_n$-ideals and the transfer of hereditary undecidability through
interpretations with parameters.

## Sources

- B. S. Kalmurzayev, N. A. Bazhenov and A. M. Iskakov, "Undecidability of the degree structure of primitive recursive $m$-reducibility", *Journal of Logic and Computation* 35(4), article exae074, 2025, doi:10.1093/logcom/exae074; read in arXiv:2311.15253v1, titled "A note on the degree structure of primitive recursive m-reducibility": Theorem 1 with the definitions of Section 1, the cited theorem of Nies and the proof scheme in Section 2, and the main lemma of Section 4.
