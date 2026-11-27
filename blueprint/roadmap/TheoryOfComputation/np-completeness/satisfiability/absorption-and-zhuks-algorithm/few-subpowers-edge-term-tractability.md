# Idziak–Marković–McKenzie–Valeriote–Willard: edge polymorphisms give polynomial-time CSPs via compact representations

A finite algebra has few subpowers if and only if it has a $k$-edge term for some $k$ (Berman–Idziak–Marković–McKenzie–Valeriote–Willard). If a finite constraint language $\Gamma$ has a $k$-edge polymorphism, then $\mathrm{CSP}(\Gamma)$ is solvable in polynomial time: every subpower $R\le\mathbf{A}^n$ has a generating set ("compact representation") of size polynomial in $n$, and the algorithm maintains such a representation of the solution set while adding constraints one at a time. The special case of a Mal'tsev polymorphism is the Bulatov–Dalmau algorithm, which subsumes linear equations over finite fields and, more generally, cosets of subgroups of finite groups.

## Proof sketch

Using the edge identities, a relation $R\subseteq A^n$ is determined by its "forks" (pairs of tuples agreeing on a prefix and differing at the next coordinate) together with projections to at most $k-1$ coordinates; choosing one witness per fork and per small projection gives a generating set whose size is polynomial in $n$ for fixed $\mathbf{A}$ and $k$. Intersecting with a new constraint is done coordinate by coordinate, using the edge term to repair witnesses, in polynomial time. Conversely, without an edge term one constructs exponentially many distinct subpowers.

## Depends on

- [Few subpowers, Mal'tsev operations and edge terms](few-subpowers-maltsev-edge-terms.md)

## Sources

- Joel Berman, Paweł Idziak, Petar Marković, Ralph McKenzie, Matthew Valeriote and Ross Willard, "Varieties with few subalgebras of powers", Transactions of the American Mathematical Society 362(3) (2010).
- Paweł Idziak, Petar Marković, Ralph McKenzie, Matthew Valeriote and Ross Willard, "Tractability and learnability arising from algebras with few subpowers", SIAM Journal on Computing 39(7) (2010).
- Andrei Bulatov and Víctor Dalmau, "A simple algorithm for Mal'tsev constraints", SIAM Journal on Computing 36(1) (2006).
