# Certificate complexity, degree and decision-tree depth

Use the decision-tree depth $D$, degree $\deg$, sensitivity $s$, block sensitivity $bs$ and certificate complexities $C$, $C_0$, $C_1$ of
[decision-tree depth and degree of a Boolean function](decision-tree-depth-and-degree-of-a-boolean.md). For every $f : \{0,1\}^n \to \{0,1\}$:

1. $s(f) \le bs(f) \le D(f)$;
2. $bs(f) \le C(f) \le D(f)$;
3. $D(f) \le C_0(f)\, C_1(f) \le C(f)^2$;
4. $C(f) \le s(f)\, bs(f)$;
5. $\deg(f) \le D(f)$, and $D(f) \le \deg(f)^2\, bs(f) = O(\deg(f)^4)$.

For 2, the variables queried along the path of $x$ in an optimal decision tree form a certificate for $x$, and each block witnessing $bs(f, x)$
must meet every certificate for $x$. For 3, every $0$-certificate meets every $1$-certificate in a position where they disagree. A decision tree
repeatedly queries all bits of a remaining $0$-certificate, at most $C_0(f)$ queries per round; each round either reveals $f(x) = 0$ or
shortens every remaining $1$-certificate by one unfixed bit, so there are at most $C_1(f)$ rounds.

## Depends on

- [Decision-tree depth and degree of a Boolean function](decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Chapter 11: Definitions 11.7–11.8, Theorem 11.11 and its proof (which bounds the number of rounds by the length of the $1$-certificates and the queries per round by the length of a $0$-certificate), Definition 11.19, Lemma 11.20, Theorem 11.21 (Nisan), Definition 11.22 and Theorem 11.24. Items 2 and the refinement $C_0(f) C_1(f)$ in 3 are derived on this page.
