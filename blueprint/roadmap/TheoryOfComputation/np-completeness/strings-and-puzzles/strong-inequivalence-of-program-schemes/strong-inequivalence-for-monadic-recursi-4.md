# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

The STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: finite sets $F$ and $P$ of function and predicate symbols, a set $G$ of "defined" function symbols disjoint from $F$, a specified symbol $f_0 \in G$, and two linear monadic recursion schemes $S_1$ and $S_2$, each consisting of a defining statement for each $f \in G$ of the form $fx = \text{if } px \text{ then } \alpha x \text{ else } \beta x$, where $p \in P$, $\alpha, \beta \in (F \cup G)^*$, and $\alpha$ and $\beta$ each contain at most one occurrence of a symbol from $G$. Question: is there a domain set $D$, an interpretation of each $f \in F$ as a function $f : D \to D$, an interpretation of each $p \in P$ as a function $p : D \to \{T, F\}$, and an initial value $x_0 \in D$ such that, as defined by the recursion schemes $S_1$ and $S_2$, either the two values for $f_0(x_0)$ differ or one is defined and the other isn't?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO17] STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES, p. 277 (reference [Constable, Hunt, and Sahni, 1974]; transformation from STRONG INEQUIVALENCE OF IANOV SCHEMES).
- H. B. Hunt III, R. L. Constable and S. Sahni, "On the computational complexity of program scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, [doi:10.1137/0209031](https://doi.org/10.1137/0209031) (journal version of the 1974 Cornell report GJ cites: strong equivalence of linear monadic recursion schemes is NP-complete).
