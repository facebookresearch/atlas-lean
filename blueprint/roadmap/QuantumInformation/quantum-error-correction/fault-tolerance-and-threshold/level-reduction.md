# Level reduction

Let $C'$ be the [fault-tolerant simulation](fault-tolerant-simulation-and-extended-rectangles.md) of a circuit $C$ with an
$[[n, 1, 2t + 1]]$ code, and suppose $C'$ undergoes a [local stochastic error model](local-stochastic-error-model.md)
with bounds $p_i$, and suppose that at every location $i$ of $C$ the sum displayed below is less than $1$ (for instance
when $p_j \le p$ for all $j$ and $A p^{t+1} < 1$). Replacing $C$, for each set $S$ of faulty locations of $C'$, by the circuit $\tilde C_S$ of
[bad extended rectangles simulating faulty locations](bad-extended-rectangles-simulate-faulty-locations.md), with the
probability of $S$, defines a local stochastic error model on $C$ whose bounds satisfy

$$p'_i \le \sum_{R} \prod_{j \in R} p_j ,$$

the sum over sets $R$ of exactly $t + 1$ locations of the ExRec of $C_i$. If $p_i \le p$ for all $i$, then
$p'_i \le A p^{t+1}$, where $A$ is the largest number of sets of $t + 1$ locations in one ExRec. The truncation of
extended rectangles is what makes the bound multiply over sets of overlapping ExRecs. The hypothesis is needed because the
error model requires every bound to be less than $1$: for $t = 1$, if two of the three locations of a final measurement
ExRec are chosen uniformly to be faulty and no other location is, the model on $C'$ is local stochastic (bounds $2/3$ on
singletons and $1/3 \le (2/3)^2$ on pairs), but that ExRec is bad on every draw.

## Depends on

- [Fault-tolerant simulation of a circuit and extended rectangles](fault-tolerant-simulation-and-extended-rectangles.md)
- [Local stochastic error model](local-stochastic-error-model.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Bad extended rectangles simulate faulty locations](bad-extended-rectangles-simulate-faulty-locations.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.2, Definitions 11 and 12, Theorem 9 and its proof, equations (84)–(85).
