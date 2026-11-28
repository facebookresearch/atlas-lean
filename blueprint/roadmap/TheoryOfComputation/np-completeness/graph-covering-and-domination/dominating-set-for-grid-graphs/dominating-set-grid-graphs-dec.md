# DOMINATING SET for grid graphs as a decision problem

The decision problem DOMINATING SET for grid graphs accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of its instances, to an instance that is
[well-formed](well-formed.md) and whose [DOMINATING SET
instance](to-dominating-set-instance.md), the grid graph of its points with the same bound, is
[feasible for DOMINATING SET](../dominating-set/dominating-set-feasible.md). It rejects every
bitstring that does not decode to an instance.
