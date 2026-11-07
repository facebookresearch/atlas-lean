# The decision problem MINIMUM BISECTION

The decision problem MINIMUM BISECTION accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of instances, to an
instance $(n, es, K)$ of MINIMUM BISECTION that is well formed and feasible (its vertices split
into two sets of $n / 2$ vertices with at most $K$ entries of $es$ between them). Bitstrings that
do not decode are rejected.
