# The KNAPSACK decision problem

KNAPSACK is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a knapsack instance
$(I, C, T)$ for which some subsequence of the item list $I$, possibly empty, has total weight at
most $C$ and total value at least $T$. Bitstrings that do not decode are rejected.
