# Number-on-forehead protocols and cylinder intersections

In the $k$-party *number-on-forehead* (NOF) model the input is $x = (x_1, \dots, x_k) \in X_1 \times \dots \times X_k$ and player $i$ sees every $x_j$ with $j \ne i$ but not $x_i$. A protocol is a tree whose inner nodes name a speaker $i$ and a bit computed from the speaker's view; the cost is the depth. A *cylinder in direction $i$* is a set $C \subseteq \prod_j X_j$ whose membership does not depend on $x_i$; a *cylinder intersection* is an intersection of cylinders, one per direction. The set of inputs reaching a leaf of a NOF protocol is a cylinder intersection, so a protocol of cost $c$ partitions the inputs into at most $2^c$ cylinder intersections. With $k = 2$ the model coincides with the two-party model (cylinders are rectangles).

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Rectangle lemma](../deterministic-communication-protocols/transcript-eq-iff.md)

## Sources

- A. K. Chandra, M. L. Furst and R. J. Lipton, "Multi-Party Protocols", STOC 1983.
- L. Babai, N. Nisan and M. Szegedy, "Multiparty Protocols, Pseudorandom Generators for Logspace, and Time-Space Trade-offs", Journal of Computer and System Sciences 45(2), 1992.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
