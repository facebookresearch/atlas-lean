# Padding map from SUBSET-SUM to PARTITION

For a list $a = (a_1, \dots, a_n)$ of natural numbers and a natural number $t$, the padded
instance is the list $(a_1 + \dots + a_n,\ 2t,\ a_1, \dots, a_n)$.

No condition on $t$ is needed: the padding is a correct reduction also when
$t > a_1 + \dots + a_n$ ([correctness](from-subset-sum-feasible.md)).
