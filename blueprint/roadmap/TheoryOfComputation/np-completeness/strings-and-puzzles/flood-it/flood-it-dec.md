# FLOOD-IT with c colors as a decision problem

For a natural number $c$, the decision problem FLOOD-IT with $c$ colors accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of its instances, to an
instance that is [well-formed for $c$ colors](well-formed.md) and [feasible with $c$
colors](flood-it-feasible.md). It rejects every bitstring that does not decode to an instance.
