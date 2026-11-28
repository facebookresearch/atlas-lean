# MINIMUM BISECTION on 3-regular graphs as a decision problem

The decision problem MINIMUM BISECTION on 3-regular graphs accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$, to an instance that is well-formed for MINIMUM BISECTION on 3-regular graphs and feasible for MINIMUM BISECTION: some set $S$ of $n / 2$ vertices such that no $K + 1$ listed edges each have exactly one endpoint in $S$, that is, at most $K$ edges join $S$ to its complement. It rejects every bitstring that does not decode to such an instance.
