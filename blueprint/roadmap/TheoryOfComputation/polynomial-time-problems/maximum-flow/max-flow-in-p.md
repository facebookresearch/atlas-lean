# Max flow is in P (Edmonds-Karp)

The max-flow decision problem belongs to the complexity
class P. This is the problem of deciding, for a vertex count $n$, a list of edges joining
distinct vertices below $n$ with natural-number capacities, distinct vertices $s, t < n$ and a
target $K$, encoded as a bitstring, whether some flow in natural numbers that respects the
capacities and is conserved at every vertex other than $s$ and $t$ has net outflow from $s$ at
least $K$.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", Journal of the ACM 19 (1972), 248-264; L. R. Ford Jr. and D. R. Fulkerson, Flows in Networks, Princeton University Press, 1962.
