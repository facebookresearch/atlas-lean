# Snir's size–depth trade-off for prefix circuits

Every prefix circuit on $N\ge1$ inputs satisfies $c+d\ge 2N-2$, where $c$ is the number of binary gates and $d$ the depth. Hence zero-deficiency circuits are exactly those meeting this bound.

## Proof sketch

The last output $x_1\ast\cdots\ast x_N$ needs a tree of $N-1$ distinct binary gates, one for each segment it multiplies. Only the gates on the leftmost path of that tree compute prefixes, and that path has at most $d$ binary gates, one of which is the output itself; so at most $d-1$ of the $N-2$ prefixes $x_1\ast x_2,\dots,x_1\ast\cdots\ast x_{N-1}$ come from the tree, and each of the other, at least $N-1-d$, needs a further gate. Summing gives $c\ge 2N-2-d$ (for $N=1$ both sides are $0$).

## Depends on

- [Universal prefix circuits and fanout-bounded optimality](universal-prefix-circuits.md)

## Sources

- Marc Snir, "Depth-Size Trade-offs for Parallel Prefix Computation", Journal of Algorithms 7(2), 185–201, 1986.
