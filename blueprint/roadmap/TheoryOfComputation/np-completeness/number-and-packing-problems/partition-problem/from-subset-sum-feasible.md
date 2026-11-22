# Correctness of the SUBSET-SUM to PARTITION padding map

For every list $a = (a_1, \dots, a_n)$ of natural numbers and every natural number $t$, the
[padded instance](from-subset-sum.md) $(a_1 + \dots + a_n, 2t, a_1, \dots, a_n)$ is a
[feasible](partition-feasible.md) PARTITION instance if and only if some sublist of $a$ has sum
$t$.
