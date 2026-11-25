# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM as a decision problem

For a pattern digraph on $\{0, \dots, k-1\}$ with arc list $A_H$, the decision problem
FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM accepts a bitstring $x$ exactly when $x$ decodes,
under the canonical bitstring encoding of its instances, to an instance that is [well-formed for
$k$](well-formed.md) and [feasible for $A_H$](fixed-vertex-directed-subgraph-homeomorp-2.md). It
rejects every bitstring that does not decode to an instance.
