# The MAXIMUM COVERAGE decision problem

MAXIMUM COVERAGE is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
maximum-coverage instance $(n, S, K, M)$ that is well formed and feasible: every subset in the
list $S$ has no repeated elements and only elements less than $n$, and some sublist of $S$ with
at most $K$ entries covers at least $M$ distinct elements less than $n$. Bitstrings that do not
decode are rejected.
