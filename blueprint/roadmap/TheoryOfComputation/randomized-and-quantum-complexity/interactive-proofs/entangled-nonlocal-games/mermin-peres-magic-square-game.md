# The Mermin–Peres magic square game

In the *magic square game* Alice receives a row $r \in \{1,2,3\}$ and Bob a column $c \in \{1,2,3\}$, uniformly and independently; Alice answers three bits with even parity (a row of a $\pm1$ square with product $+1$), Bob three bits with odd parity (a column with product $-1$), and they win iff they agree on the shared cell. Its classical value is $8/9$, while a perfect entangled strategy exists using two EPR pairs and the nine two-qubit Pauli observables of the Mermin–Peres square.

## Proof sketch

A classical strategy would fill a $3 \times 3$ table whose row products are all $+1$ and column products all $-1$, impossible since the product of all entries would be both; so some cell disagrees and at most $8$ of $9$ question pairs win. The Pauli square has commuting observables in each row and column, with row products $I$ and column products $-I$, giving a perfect strategy on the maximally entangled state.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Sources

- N. D. Mermin, "Simple Unified Form for the Major No-Hidden-Variables Theorems", Physical Review Letters 65(27), 1990.
- A. Peres, "Incompatible Results of Quantum Measurements", Physics Letters A 151(3-4), 1990.
- G. Brassard, A. Broadbent and A. Tapp, "Quantum Pseudo-Telepathy", Foundations of Physics 35(11), 2005.
