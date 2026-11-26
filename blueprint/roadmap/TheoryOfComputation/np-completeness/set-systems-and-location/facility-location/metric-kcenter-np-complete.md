# METRIC K-CENTER is NP-complete

The [decision problem](metric-kcenter-dec.md) METRIC K-CENTER belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: the shortest-path distances of a connected network with positive edge lengths form a metric, so the vertex $p$-center problem on such networks, which the cited work proves NP-hard, is a special case.

## Sources

- P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem MINIMUM K-CENTER.
- O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
