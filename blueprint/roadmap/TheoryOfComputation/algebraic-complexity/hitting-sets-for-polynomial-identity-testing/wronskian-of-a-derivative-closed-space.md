# The Wronskian of a derivative-closed space depends only on t

Let $V$ be an $r$-dimensional space of polynomials in $x_1,\dots,x_n$ closed under every partial derivative, with basis $g_1,\dots,g_r$, and let $D=Q\,\partial_t+\sum_ib_i\partial_{x_i}$ be a derivation of $F[t][x]$ with $b_i,Q\in F[t]$. Then the Wronskian $\det\bigl(D^{a}g_j\bigr)_{0\le a<r,\,1\le j\le r}$ is a polynomial in $t$ alone (independent of $x$), of degree at most $nr^2$ after clearing the denominator $Q$.

## Proof sketch

Each $\partial_{x_i}$ commutes with $D$ and acts on $V$ by a matrix $T_i$; applying $\partial_{x_i}$ to the Wronskian gives $\operatorname{tr}(T_i)$ times the Wronskian, and $\operatorname{tr}T_i=0$ because $\partial_{x_i}$ is nilpotent on $V$. So all $x$-derivatives of the Wronskian vanish.

## Depends on

- [The partial-derivative measure](../algebraic-circuit-lower-bound-methods/partial-derivative-measure.md)

## Sources

- Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay et al., "Hitting Sets from Derivations: Waring Rank and Noncommutative ABPs", Electronic Colloquium on Computational Complexity, 2026.
