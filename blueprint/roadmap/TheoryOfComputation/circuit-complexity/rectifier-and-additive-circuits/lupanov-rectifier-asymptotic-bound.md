# Lupanov's asymptotic rectifier synthesis bound

For every $\varepsilon>0$ there are $N$ and $K$ such that every Boolean $p\times q$ matrix with $p\ge N$ and $q\ge K\log_2 p$ has a depth-two rectifier realization with at most $(1+\varepsilon)\,pq/\log_2 p$ edges. This matches the counting lower bound asymptotically, so the maximal OR-complexity of $p\times q$ matrices is $(1+o(1))pq/\log_2 p$ in this range.

## Proof sketch

Split the columns into blocks of about $\log_2 p-2\log_2\log_2 p$ columns and apply the row-pattern construction in each block; the per-block cost $p+w2^{w-1}$ summed over $q/w$ blocks gives $(1+o(1))pq/\log_2 p$.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)

## Proof depends on

- [Depth-two rectifier realization with p + q·2^{q-1} wires](lupanov-depth-two-rectifier-bound.md)

## Sources

- O. B. Lupanov, "On Rectifier and Switching-and-Rectifier Schemes", Doklady Akademii Nauk SSSR, 1956.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
