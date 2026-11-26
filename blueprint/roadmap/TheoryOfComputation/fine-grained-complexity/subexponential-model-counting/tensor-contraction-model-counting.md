# Model counting by tensor contraction in time 2^{O(m/√log n)}

For every fixed clause width $k$ there are a constant $A$ and a deterministic algorithm that computes the number of satisfying assignments of every $k$-CNF with $n$ variables and $m$ clauses in time

$$
2^{A(m+1)/\sqrt{\log_2(n+2)}}\cdot\mathrm{poly}(L)
$$

(and in exponent $A(N+1)/\sqrt{\log_2(N+2)}$ for $N$ literal occurrences, with no width bound). In particular, on formulas of clause density at most $D$, $\#k$-SAT is solvable in time $2^{O(n/\sqrt{\log n})}$.

## Proof sketch

Express the model count as the value of a factored tensor network with one tensor per clause and one index per variable. Group the network into blocks of about $\sqrt{\log n}$ clauses, so that contracting along a block order costs a factor $2^{O(\text{boundary})}$ per merge; the block structure keeps all intermediate boundaries of size $O(m/\sqrt{\log n})$ while the number of block configurations stays polynomial.

## Depends on

- [Counting satisfying assignments of a CNF formula](../../counting-complexity/counting-satisfiability-sat/count-sat-fun.md)
- [Merging vertices of a factored tensor network](../tensor-network-contraction/contraction-of-factored-tensor-networks/merge.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Sources

- OpenAI, "The Exponential Time Hypothesis is False", Manuscript, 2026.
