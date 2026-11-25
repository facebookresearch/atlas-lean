# PARALLEL BATCHING of in-trees with release dates as a decision problem

The decision problem PARALLEL BATCHING of in-trees with release dates accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of its instances, to an
instance that is [well-formed](well-formed.md) and admits a schedule of its unit-time jobs on
$m$ machines that respects the release dates and the precedence constraints and has makespan at
most $K$. It rejects every bitstring that does not decode to an instance.
