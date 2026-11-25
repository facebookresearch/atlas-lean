# PARTITION as SUBSET-SUM on the doubled list

A list $a = (a_1, \dots, a_n)$ of natural numbers is a [feasible](partition-feasible.md)
PARTITION instance if and only if some sublist of $(2a_1, \dots, 2a_n)$ has sum
$a_1 + \dots + a_n$.

Doubling the entries, instead of halving the total, avoids rounding when the total is odd.
