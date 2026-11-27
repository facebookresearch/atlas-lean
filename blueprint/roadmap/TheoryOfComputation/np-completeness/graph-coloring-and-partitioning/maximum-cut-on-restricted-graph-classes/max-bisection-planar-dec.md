# MAXIMUM BISECTION ON PLANAR GRAPHS as a decision problem

The decision problem MAXIMUM BISECTION ON PLANAR GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for MAXIMUM BISECTION ON PLANAR GRAPHS and feasible for MAXIMUM BISECTION (a side of exactly $\lfloor n/2 \rfloor$ vertices with at least $K$ listed edges crossing it). It rejects every bitstring that does not decode to such an instance.
