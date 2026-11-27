# Rank-$n$ types and Hintikka formulas

For a vocabulary with finitely many relation symbols, the *rank-$n$ type* of a $k$-tuple $\bar a$ in $\mathfrak{A}$ is defined recursively: for $n = 0$ it is the atomic diagram of $\bar a$ (the set of atomic formulas in $x_1,\dots,x_k$ it satisfies); for $n > 0$ it is the pair consisting of the atomic diagram and the set of rank-$(n-1)$ types of the extensions $\bar a c$, $c \in A$. The *Hintikka formula* $\varphi^n_{\bar a}$ is the conjunction of the atomic formulas in $x_1,\dots,x_k$ satisfied by $\bar a$ and the negations of those not satisfied, together (for $n > 0$) with $\bigwedge_{\tau} \exists x_{k+1}\, \varphi_\tau$ over the rank-$(n-1)$ types $\tau$ realized by extensions $\bar a c$, where $\varphi_\tau$ is the Hintikka formula of $\tau$ in $x_1,\dots,x_{k+1}$, and $\forall x_{k+1} \bigvee_\tau \varphi_\tau$ (finitely many types, since the vocabulary is finite); it has quantifier rank $n$ and defines the rank-$n$ type.

## Depends on

- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)
- [Partial isomorphisms between pointed structures](partial-isomorphisms.md)

## Sources

- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
