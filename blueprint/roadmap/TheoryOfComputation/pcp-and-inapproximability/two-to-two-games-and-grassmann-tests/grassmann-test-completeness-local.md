# Zoom-local soundness structure of the Grassmann test

Suppose $F$ passes the Grassmann test with probability at least $\delta > 0$, where $\ell$ is large in terms of $\delta$ and $n$ is large in terms of $\ell$. Then there exist subspaces $Q \subseteq W$ with $\dim Q + \operatorname{codim} W \le r(\delta)$ and a linear function $g : \mathbb{F}_2^n \to \mathbb{F}_2$ such that

$$
\Pr_{L : Q \subseteq L \subseteq W}\bigl[F[L] = g|_L\bigr] \ge \delta'(\delta) > 0.
$$

That is, a successful assignment agrees with a global linear function on a non-negligible fraction of some zoom-in/zoom-out restriction, though possibly on a vanishing fraction of all vertices.

## Proof sketch

For each linear function $g$ consider the set $S_g = \{L : F[L] = g|_L\}$. Passing the test with probability $\delta$ means that the edges inside the sets $S_g$ carry a $\delta$-fraction of all edges, so some $S_g$ is a set whose expansion is at most $1 - \delta''$. The structure theorem for non-expanding sets of the Grassmann graph then forces $S_g$ to have density at least $\delta'$ inside a zoom-in/zoom-out of bounded order.

## Depends on

- [The Grassmann linearity agreement test](grassmann-linearity-test.md)
- [Zoom-in and zoom-out subgraphs of the Grassmann graph](grassmann-zoom.md)

## Proof depends on

- [Non-expanding sets in the Grassmann graph (Khot–Minzer–Safra)](../../../GraphTheory/algebraic-graph-theory/part-01/grassmann-graphs/theorem-1-12.md)

## Sources

- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "Towards a proof of the 2-to-1 games conjecture?", STOC (2018), ECCC TR16-198.
- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "On non-optimally expanding sets in Grassmann graphs", STOC (2018); Israel Journal of Mathematics 243 (2021), ECCC TR17-094.
- S. Khot, D. Minzer, M. Safra, "Pseudorandom sets in Grassmann graph have near-perfect expansion", FOCS (2018); Annals of Mathematics 198 (2023), ECCC TR18-006.
