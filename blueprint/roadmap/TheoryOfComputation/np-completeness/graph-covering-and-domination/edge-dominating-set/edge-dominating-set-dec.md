# The EDGE DOMINATING SET decision problem

EDGE DOMINATING SET is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to an EDGE DOMINATING SET instance $(n, E, K)$ that is well formed and feasible, that is, some
sublist of $E$ with at most $K$ entries contains, for every edge of $E$, an edge sharing an
endpoint with it. Bitstrings that do not decode to an instance are rejected.
