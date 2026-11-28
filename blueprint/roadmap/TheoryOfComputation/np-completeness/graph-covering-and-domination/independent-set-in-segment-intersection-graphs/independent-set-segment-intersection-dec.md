# INDEPENDENT SET in segment intersection graphs as a decision problem

The decision problem INDEPENDENT SET in segment intersection graphs accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of its instances, to an
instance consisting of a list of $m$ closed segments with endpoints in $\mathbb{Z}^2$, each coordinate a difference of two natural numbers, and a natural bound $K$, in which every segment has distinct endpoints, the
segments are pairwise distinct as point sets, and $0 < K \le m$, and that is
[feasible](independent-set-segment-intersection-fea.md). It rejects every bitstring that does
not decode to an instance.
