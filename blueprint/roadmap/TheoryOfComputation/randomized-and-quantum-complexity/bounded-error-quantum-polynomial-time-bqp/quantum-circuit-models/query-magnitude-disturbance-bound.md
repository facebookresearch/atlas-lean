# Changing oracle answers on a coherent query: the query-magnitude bound

Let $\rho$ be a joint state of a query register and an arbitrary reference system, and let $H,H'$ be two oracles. Then the trace distance between the states after one coherent XOR query to $H$ and to $H'$ is at most $2\sqrt{p}$, where $p$ is the probability that measuring the query's address register yields an address $x$ with $H(x)\neq H'(x)$. Summed over the queries of an oracle circuit, changing the oracle on a set of addresses of total query magnitude $\sum_tp_t$ moves the final state by $O\bigl(\sum_t\sqrt{p_t}\bigr)$.

## Proof sketch

The two query unitaries agree on the subspace of addresses where $H=H'$; the difference applied to the state has norm at most twice the norm of its projection onto the disagreeing addresses, which is $\sqrt p$; the hybrid argument sums over queries.

## Depends on

- [Quantum oracle circuits with coherent XOR queries](quantum-oracle-circuits-with-xor-queries.md)

## Sources

- Charles H. Bennett, Ethan Bernstein, Gilles Brassard, Umesh Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM Journal on Computing 26(5), 1510–1523, 1997, Theorem 3.3 (Euclidean distance at most $2\sqrt{T\sum_t q_y(\varphi_t)}$; the trace-distance form for one query follows since trace distance is at most the Euclidean distance of purifications).
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
