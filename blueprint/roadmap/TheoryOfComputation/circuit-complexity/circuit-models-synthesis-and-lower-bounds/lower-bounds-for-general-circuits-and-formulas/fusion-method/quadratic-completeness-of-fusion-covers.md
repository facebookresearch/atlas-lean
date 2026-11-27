# Quadratic completeness of semifilter covers

Conversely to the fusion lower bound, a pair cover of length $t$ for $(T;S_1,\dots,S_n)$ yields a construction of $T$ from $S_1,\dots,S_n$ by unions and intersections that uses at most $t^2$ intersections, unions being free. Hence the cover complexity $\rho$ and the least number $\mathrm{AND}$ of intersections (for a Boolean function: of AND gates in a monotone circuit over the literals) satisfy $\rho\le\mathrm{AND}\le\rho^2$. The total number of operations of the construction is $O((t+n)^3)$.

## Proof sketch

Fix a cover $\Lambda=\{(E_1,H_1),\dots,(E_t,H_t)\}$. For an element $w$, the semifilters preserving $\Lambda$ and above $w$ are closed under the propagation that starts from the supplied sets containing $w$ and adds $E_i\cap H_i$ whenever $E_i$ and $H_i$ are present; $w\in T$ exactly when this closure reaches $\emptyset$. The closure is computed for all $w$ simultaneously in $t+1$ synchronous stages, each stage using at most $t$ intersections after the first, which gives at most $t^2$ intersections.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Proof depends on

- [Semifilter covers lower-bound the AND count of monotone circuits](fusion-covers-lower-bound-and-gates.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 167–176, 1989.
- Mauricio Karchmer, "On Proving Lower Bounds for Circuit Size", Proceedings of the 8th Annual Structure in Complexity Theory Conference, 112–118, 1993.
- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", ACM Transactions on Computation Theory, 2025 (Theorem 24 and Corollary 28).
