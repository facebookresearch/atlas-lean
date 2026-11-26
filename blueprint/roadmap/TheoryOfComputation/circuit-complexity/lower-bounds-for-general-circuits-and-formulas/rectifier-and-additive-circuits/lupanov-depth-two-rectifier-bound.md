# Depth-two rectifier realization with p + q·2^{q-1} wires

Every Boolean $p\times q$ matrix has a depth-two rectifier realization with at most $p+q\cdot2^{q-1}$ edges.

## Proof sketch

Group the $p$ rows by their pattern in $\{0,1\}^q$: one middle node per occurring nonzero pattern collects its rows ($p$ edges in total) and is joined to the outputs where the pattern has a one; the $2^q$ patterns contribute at most $q2^{q-1}$ edges to the outputs.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)

## Sources

- O. B. Lupanov, "On Rectifier and Switching-and-Rectifier Schemes", Doklady Akademii Nauk SSSR, 1956.
