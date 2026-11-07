# The MAXIMUM INDUCED MATCHING decision problem

MAXIMUM INDUCED MATCHING is the decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a maximum-induced-matching instance $(n, E, K)$ that is well formed and feasible:
the edge list $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$
and $u \ne v$ with $(v, u)$ not in $E$, and some sublist $M$ of $E$ of length at least $K$ is an
induced matching, meaning that any two distinct pairs in $M$ share no endpoint and no pair in $E$
joins an endpoint of one pair in $M$ to an endpoint of a different pair in $M$. Bitstrings that
do not decode are rejected.
