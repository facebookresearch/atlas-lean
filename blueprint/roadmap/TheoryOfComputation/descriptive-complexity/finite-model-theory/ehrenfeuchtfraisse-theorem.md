# Ehrenfeucht–Fraïssé theorem

Let $\sigma$ be a finite relational signature without constant symbols. The *quantifier rank* $\mathrm{qr}(\varphi)$ of a first-order formula is its depth
of quantifier nesting: $0$ for atomic formulas, unchanged by $\neg$, the maximum of the two ranks for $\wedge$ and $\vee$, and $\mathrm{qr}(\varphi) + 1$ for
$\exists x\,\varphi$ and $\forall x\,\varphi$. In the *$k$-round Ehrenfeucht–Fraïssé game* on $\sigma$-structures $\mathfrak{A}$ and $\mathfrak{B}$, each round the
Spoiler picks one of the two structures and an element of it, and the Duplicator answers with an element of the other structure. After $k$ rounds, with
$a_1, \dots, a_k$ the elements played in $\mathfrak{A}$ and $b_1, \dots, b_k$ those played in $\mathfrak{B}$, the Duplicator wins if $(a_i)$ and $(b_i)$ define a
partial isomorphism: $a_i = a_j$ if and only if $b_i = b_j$, and for every relation symbol $P$ of arity $r$ and all indices $i_1, \dots, i_r$,
$(a_{i_1}, \dots, a_{i_r}) \in P^{\mathfrak{A}}$ if and only if $(b_{i_1}, \dots, b_{i_r}) \in P^{\mathfrak{B}}$.

**Theorem (Ehrenfeucht–Fraïssé).** For every $k \in \mathbb{N}$, $\mathfrak{A}$ and $\mathfrak{B}$ satisfy the same first-order sentences of quantifier rank at most
$k$ if and only if the Duplicator has a winning strategy in the $k$-round Ehrenfeucht–Fraïssé game on $\mathfrak{A}$ and $\mathfrak{B}$.

Consequently, a property of finite $\sigma$-structures is not first-order definable if for every $k$ some pair of finite structures, one with the property and
one without, admits a winning strategy for the Duplicator in the $k$-round game.

## Depends on

- [Logics on finite structures as query languages](logics-on-finite-structures-as-query-languages.md)

## Related topics

- [Even cardinality is not first-order definable](even-cardinality-is-not-first-order-definable.md): an application over the empty signature and over finite linear orders.
- [Connectivity is not first-order definable on finite graphs](../../../ComputerScience/databases/query-language-expressiveness/connectivity-is-not-first-order-definable-on-finite-graphs.md): an application to finite graphs.

## Sources

- L. Libkin, *Elements of Finite Model Theory*, Springer, 2004 (author copy), <https://www.cs.utoronto.ca/~libkin/fmt/fmt.pdf>: Definition 3.8 (quantifier rank), Section 3.2 and Definition 3.5 (the game and partial isomorphisms), Theorem 3.9 (Ehrenfeucht–Fraïssé) and Corollary 3.10 (the inexpressibility method).
- H.-D. Ebbinghaus and J. Flum, *Finite Model Theory*, 2nd ed., Springer, 1999
