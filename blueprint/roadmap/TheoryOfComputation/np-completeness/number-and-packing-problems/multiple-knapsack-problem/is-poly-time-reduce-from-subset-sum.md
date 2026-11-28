# The SUBSET-SUM to MULTIPLE KNAPSACK map is polynomial-time

The map on bit strings sending
the SUBSET-SUM encoding of numbers $a_1, \dots, a_n$ and a target $t$ to the canonical encoding of
the multiple-knapsack instance with items $(a_i, a_i)$, one knapsack of capacity $t$ and target
$t$, and every other bit string to the encoding of a fixed no-instance, is computable in
polynomial time, within a quadratic number of steps of a multi-stack Turing machine.

## Sources

- original to this formalization; the input check follows the PARTITION hardness machine of this library.
