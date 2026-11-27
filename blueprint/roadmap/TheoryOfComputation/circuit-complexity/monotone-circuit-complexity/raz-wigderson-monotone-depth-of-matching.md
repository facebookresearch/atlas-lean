# Raz–Wigderson: monotone formulas for perfect matching need linear depth

Every monotone formula computing bipartite perfect matching on $K_{n,n}$ has depth $\Omega(n)$; explicitly at least $(n-2^{14})/2^{13}$. Equivalently, the monotone Karchmer–Wigderson game of $\mathrm{PM}_n$ has communication complexity $\Omega(n)$.

## Proof sketch

By the monotone Karchmer–Wigderson theorem it suffices to lower-bound the game; a protocol for it yields a protocol for set disjointness on $\Omega(n)$ elements, whose randomized communication complexity is linear.

## Depends on

- [Perfect matching](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/perfect-matching.md)
- [The Karchmer–Wigderson game of a Boolean function](../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/karchmer-wigderson-game.md)

## Proof depends on

- [Karchmer–Wigderson: formula depth equals communication complexity](../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/karchmer-wigderson-theorem.md)

## Sources

- Ran Raz, Avi Wigderson, "Monotone Circuits for Matching Require Linear Depth", Journal of the ACM, 1992.
- Eyal Kushilevitz, Noam Nisan, "Communication Complexity", Cambridge University Press, 1997.
