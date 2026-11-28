# The theory of the primitive recursive m-degrees of computable sets is hereditarily undecidable

The first-order theory of the upper semilattice of primitive recursive $m$-degrees of computable sets other than $\emptyset$ and $\mathbb{N}$ is hereditarily undecidable: every subtheory in the same language is undecidable.

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

A good expansion links pages for the following steps of the source's proof (Section 2), which follows the scheme of Downey and Nies.

- *Super pr-sparse sets.* A computable set $A$ is super pr-sparse via a strictly increasing computable function $f$ if $A$ is not primitive recursive, the graph of $f$ is primitive recursive, $A \subseteq \operatorname{range}(f)$ with $\chi_A(f(x))$ computable in at most $f(x+1)$ steps, and every primitive recursive function $p$ satisfies $f(n+1) > p(f(n))$ for all large $n$ (Definition 3.1). Such a set exists (Lemma 3.3).
- *The Boolean algebra $B(a)$.* For the degree $a$ of a super pr-sparse set, the complemented elements of the lower cone, $B(a) = \{b \in \mathbf{C}^{pr}_m : \exists c\,(b \wedge c = 0 \text{ and } b \vee c = a)\}$, form an effectively dense $\Sigma^0_2$-Boolean algebra (Proposition 3.2, through Lemmas 3.5 and 3.7).
- *The interpretation.* Every $\Sigma^0_2$-ideal $I$ of $B(a)$ is $\{x \in B(a) : x \le c_I\}$ for some degree $c_I \le a$ (Lemma 4.1). So, with the parameter $a$, the lattice $I(B(a))$ of $\Sigma^0_2$-ideals of $B(a)$ is interpreted in $\mathbf{C}^{pr}_m$ by the domain formula $x \le a$ and the order formula $\forall z\,[\exists w\,(z \vee w = a \wedge z \wedge w = 0) \to (z \le x \to z \le y)]$ (Section 4).
- *Nies's theorem.* For every effectively dense $\Sigma^0_n$-Boolean algebra $B$, the theory of the lattice of its $\Sigma^0_n$-ideals is hereditarily undecidable (Theorem 2 of the source, from A. Nies, "Intervals of the lattice of computably enumerable sets and effective Boolean algebras", *Bulletin of the London Mathematical Society* 29(6), 683–692, 1997).
- *Transfer through interpretations.* Hereditary undecidability passes from an interpreted structure to a structure that interprets it with parameters, which the source cites to Ershov, Lavrov, Taimanov and Taitslin (1965) and to Burris and Sankappanavar (1975).

## Sources

- B. S. Kalmurzayev, N. A. Bazhenov and A. M. Iskakov, "Undecidability of the degree structure of primitive recursive $m$-reducibility", *Journal of Logic and Computation* 35(4), article exae074, 2025, doi:10.1093/logcom/exae074; read in arXiv:2311.15253v1, titled "A note on the degree structure of primitive recursive m-reducibility": Theorem 1 with the definitions of Section 1, Theorem 2 (Nies) and the proof scheme in Section 2, Definition 3.1, Lemma 3.3, Proposition 3.2 and Lemmas 3.5 and 3.7 in Section 3, and Lemma 4.1 with the interpretation of Section 4.
