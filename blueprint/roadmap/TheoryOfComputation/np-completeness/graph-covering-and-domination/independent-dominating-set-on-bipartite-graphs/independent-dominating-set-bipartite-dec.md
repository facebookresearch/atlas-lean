# INDEPENDENT DOMINATING SET on bipartite graphs as a decision problem

The decision problem INDEPENDENT DOMINATING SET on bipartite graphs accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of its instances, to an
instance $(n, E, K)$ that is a well-formed DOMINATING SET instance whose graph is bipartite,
with $0 < K$, and that is [feasible for INDEPENDENT DOMINATING
SET](../independent-dominating-set/independent-dominating-set-feasible.md): some independent set
of at most $K$ vertices dominates the graph. It rejects every bitstring that does not decode to
an instance.
