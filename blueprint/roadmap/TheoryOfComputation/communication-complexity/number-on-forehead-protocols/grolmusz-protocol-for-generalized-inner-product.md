# Grolmusz's protocol for the generalized inner product

For $k + 1$ players there is a deterministic NOF protocol computing $\mathrm{GIP}_{k+1, n}$ with $O(k\, n / 2^k)$ bits (for $n$ at least $2^k$). Hence the exponential decay in $k$ of the Babai–Nisan–Szegedy lower bound cannot be removed, and generalized inner product is easy for $k \gtrsim \log n$ players.

## Proof sketch

View the input as a $(k+1) \times n$ matrix and process blocks of fewer than $2^k$ columns. Player $0$ names a pattern $z \in \{0,1\}^k$ not appearing among the columns' rows $1..k$; along the chain of patterns obtained by successively setting rows $1, \dots, t$ to one, each player $t$ announces the parity of the number of columns matching consecutive chain patterns on the rows it sees. The telescoping sum of these $k + 1$ parities equals the number of all-ones columns modulo two.

## Depends on

- [Number-on-forehead protocols and cylinder intersections](number-on-forehead-protocols.md)

## Sources

- V. Grolmusz, "The BNS Lower Bound for Multi-Party Protocols Is Nearly Optimal", Information and Computation 112(1), 1994.
