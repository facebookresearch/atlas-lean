# INDUCED CONNECTED SUBGRAPH WITH PROPERTY Π as a decision problem

For a graph property $\Pi$, the decision problem INDUCED CONNECTED SUBGRAPH WITH PROPERTY $\Pi$
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of its
instances, to an instance that is [well-formed for INDUCED SUBGRAPH WITH PROPERTY
Π](../induced-subgraph-with-property/well-formed.md) and [feasible for
$\Pi$](induced-connected-subgraph-with-property.md). It rejects every bitstring that does not
decode to an instance.
