# PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests as a decision problem

The decision problem PRECEDENCE CONSTRAINED SCHEDULING on dedicated processors for forests
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of its
instances, to an instance that is [well-formed](well-formed.md) and admits a schedule on its $m$
dedicated processors that meets the overall deadline $D$, obeys the precedence constraints, and
runs any two different tasks assigned to the same processor in disjoint intervals. It rejects
every bitstring that does not decode to an instance.
