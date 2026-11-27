# Perfect matching in uniform hypergraphs with a codegree condition

For a natural number
$k$ and a rational $c$, $\mathrm{PM}(k, c)$ is the decision problem on bitstrings that decodes an
input as a pair $(n, E)$ of a natural number $n$ and a list $E$ of lists of natural numbers, and
accepts it iff every list in $E$ consists of $k$ distinct vertices below $n$, $k \mid n$, every
$(k-1)$-element subset of $\{0, \dots, n-1\}$ is contained in at least $cn$ edges of the
hypergraph $H$ whose edges are the vertex sets of the lists in $E$, and $H$ has a perfect
matching, that is, $n/k$ pairwise disjoint edges. Inputs that do not decode are rejected.
