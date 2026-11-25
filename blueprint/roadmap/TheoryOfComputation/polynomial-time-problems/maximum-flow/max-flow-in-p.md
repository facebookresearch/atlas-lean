# Max flow is in P (Edmonds-Karp)

The max-flow decision problem belongs to the complexity
class P. This is the problem of deciding, for a vertex count $n$, a list of edges joining
distinct vertices below $n$ with natural-number capacities, distinct vertices $s, t < n$ and a
target $K$, encoded as a bitstring, whether some flow in natural numbers that respects the
capacities and is conserved at every vertex other than $s$ and $t$ has net outflow from $s$ at
least $K$.

## Informally uses

- [Edmonds–Karp augmentation bound (Edmonds and Karp)](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/four-mul-le-of-reachable.md): in a network with $v$ vertices and no parallel arcs, augmenting along shortest augmenting paths reaches a maximum flow after at most $(v^3 - v)/4$ augmentations, whatever the capacities. An encoded instance is first reduced to such a network: parallel arcs are merged into one arc whose capacity is the sum of theirs, and only $s$, $t$ and the endpoints of listed edges are kept and renumbered, so that $v \le 2m + 2$ for $m$ listed edges. Each augmentation is computed with arithmetic on numbers of polynomially many bits, so the running time is polynomial in the length of the encoding.

## Sources

- Jack Edmonds and Richard M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", Journal of the ACM 19 (1972), 248-264; Lester R. Ford Jr. and Delbert R. Fulkerson, Flows in Networks, Princeton University Press, 1962.
