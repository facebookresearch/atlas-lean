# Göös–Pitassi–Watson: query-to-communication lifting for BPP

There is a constant $C$ such that for every $n$, every $f : \{0,1\}^n \to \{0,1\}$ (or search problem) and the index gadget $g = \mathrm{IND}_m$ with $m = n^{C}$,

$$
R^{cc}_{1/3}\bigl(f \circ g^n\bigr) = \Theta\bigl(R^{dt}_{1/3}(f) \cdot \log m\bigr),
$$

where $R^{cc}$ is public-coin randomized communication complexity and $R^{dt}$ is randomized decision-tree complexity. Consequently, separations between randomized query complexity and other query measures (quantum query complexity, degree, certificate complexity) lift to the corresponding separations in communication complexity.

## Proof sketch

The upper bound simulates the decision tree, spending $O(\log m)$ bits per query. For the lower bound, a randomized protocol is turned into a randomized decision tree by a simulation that, maintaining a rectangle where Alice's input is blockwise dense on the unqueried coordinates, queries a coordinate exactly when the protocol's rectangle loses density there; uniform marginals on dense coordinates make the simulation faithful, and the expected number of queries is $O(\text{cost}/\log m)$.

## Depends on

- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)
- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Proof depends on

- [Göös–Lovett–Meka–Watson–Zuckerman: rectangles are nonnegative juntas](rectangles-are-juntas.md)

## Sources

- M. Göös, T. Pitassi, T. Watson, "Query-to-communication lifting for BPP", FOCS (2017); SIAM Journal on Computing 49 (2020), arXiv:1703.07666.
