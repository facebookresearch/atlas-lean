# Killed random walks (lazy random walks of truncated geometric length)

Let $G$ be a $D$-regular multigraph on $V$ given by a rotation map, $T \ge 1$ and $q \ge 1$. A killed walk is a start vertex $v$, $T$ labels $\ell_1, \dots, \ell_T$ and $T$ kill signals $c_1, \dots, c_T \in \{0, \dots, q - 1\}$. Its kill time $\kappa$ is the least $i$ with $c_{i+1} = 0$ (the walk is killed before its $(i+1)$-st step), or $T$ if no signal is $0$; the walk follows the labels $\ell_1, \dots, \ell_\kappa$ and ignores the rest. Under uniform signals the kill time is geometric truncated at $T$: $\Pr[\kappa = m] = (1 - 1/q)^m / q$ for $m < T$ and $\Pr[\kappa \ge m] = (1 - 1/q)^m$ for $m \le T$. Killed walks are the edges of the killed power of $G$, whose rotation map reverses a killed walk up to its kill time.

## Depends on

- [Rotation map of a regular multigraph](../../../GraphTheory/graph-families-and-operations/zig-zag-product-and-explicit-expanders/rotation-map.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", Automata, Languages and Programming (ICALP 2006), 2006.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM, 2007.
