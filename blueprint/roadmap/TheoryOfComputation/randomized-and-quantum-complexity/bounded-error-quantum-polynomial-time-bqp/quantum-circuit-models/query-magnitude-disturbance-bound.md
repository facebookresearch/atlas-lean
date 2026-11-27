# Changing oracle answers on a coherent query: the query-magnitude bound

Let $|\varphi_t\rangle$ be the state of a quantum oracle computation with oracle $H$ just before its query at time $t$, for $0 \le t < T$, and let the *query magnitude* $q_y(|\varphi_t\rangle)$ be the sum of squared magnitudes of the configurations in $|\varphi_t\rangle$ that query address $y$. Let $\varepsilon > 0$ and let $F$ be a set of time–address pairs with $\sum_{(t,y)\in F} q_y(|\varphi_t\rangle) \le \varepsilon^2/T$. If the answer to each query $(t, y) \in F$ is changed to an arbitrary fixed answer (not necessarily consistent with an oracle), then the final states of the original and the modified computation are within Euclidean distance $\varepsilon$.

## Proof sketch

Write the modified final state as the original one minus the error vectors $|E_t\rangle$ created at each time $t$ by the modified answers, each carried to the end by unitaries that preserve its norm. The squared norms of the $|E_t\rangle$ sum to $\sum_{(t,y)\in F} q_y(|\varphi_t\rangle) \le \varepsilon^2/T$, and the squared norm of a sum of $T$ vectors is at most $T$ times the sum of their squared norms, which gives $\varepsilon^2$.

Derived mixed-state form (not stated in the cited sources): for a joint state $\rho$ of a query register and an arbitrary reference system and two oracles $H, H'$, the trace distance between the states after one coherent XOR query to $H$ and to $H'$ is at most $2\sqrt{p}$, where $p$ is the probability that measuring the query's address register yields an address $x$ with $H(x)\neq H'(x)$ (apply the one-query bound to a purification; trace distance is at most the Euclidean distance of purifications). Summed over the queries of an oracle circuit, changing the oracle on addresses of total query magnitude $\sum_t p_t$ moves the final state by $O\bigl(\sum_t\sqrt{p_t}\bigr)$.

## Depends on

- [Quantum oracle circuits with coherent XOR queries](quantum-oracle-circuits-with-xor-queries.md)

## Proof depends on

- [Trace norm and trace distance](../../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/trace-norm-and-trace-distance.md)

## Sources

- Charles H. Bennett, Ethan Bernstein, Gilles Brassard, Umesh Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM Journal on Computing 26(5), 1510–1523, 1997, numbering of arXiv:quant-ph/9701001, Definition 3.2 (query magnitude) and Theorem 3.3.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
