# The MULTIPLE KNAPSACK certificate check is polynomial-time

The map sending a pair of bit
strings $(x, w)$ to the certificate check, which decodes $x$ as a multiple-knapsack instance with
$k$ items and $m$ knapsacks and reads $w$ as $m$ masks of $k$ bits (missing bits count as false,
and the bits of $w$ after the first $mk$ are ignored), is computable in polynomial time for the
canonical bitstring encodings, within a cubic number of steps of a multi-stack Turing machine.

## Sources

- original to this formalization.
