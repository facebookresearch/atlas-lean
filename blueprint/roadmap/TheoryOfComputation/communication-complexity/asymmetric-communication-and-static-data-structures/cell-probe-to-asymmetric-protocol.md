# Static cell-probe structures yield asymmetric protocols

If a static problem $f$ (Alice holding the query, Bob the input) has a deterministic cell-probe structure with $S$ cells of $w$ bits and query time $t$, then $f$ has a $[t \lceil \log_2 S \rceil, \; t w]$-protocol with $2t$ rounds; the same holds for randomized structures and protocols with the same error.

## Proof sketch

Bob builds the structure for his input. Alice simulates the query algorithm: for each probe she sends the address of the cell to probe ($\lceil \log_2 S\rceil$ bits) and Bob replies with its $w$-bit content; after $t$ probes Alice knows the answer.

## Depends on

- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)
- [Static cell-probe structure with space $S$ and query time $t$](../../../ComputerScience/data-structures/cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)

## Proof depends on

- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)
- [Static cell-probe structure with space $S$ and query time $t$](../../../ComputerScience/data-structures/cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)

## Sources

- Peter Bro Miltersen, Noam Nisan, Shmuel Safra, Avi Wigderson, "On Data Structures and Asymmetric Communication Complexity", Journal of Computer and System Sciences 57(1) (1998).
