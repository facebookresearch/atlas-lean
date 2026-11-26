# Catalytic Savitch theorems for nondeterministic and unbounded-error catalytic space

For all $s=s(n)$, $c=c(n)$ with $\log n\le s\le c\le 2^{s}$,

$$
\mathsf{CNSPACE}[s,c]\subseteq\mathsf{CSPACE}[O(s^2),O(c)]\qquad\text{and}\qquad\mathsf{CPrSPACE}[s,c]\subseteq\mathsf{CSPACE}[O(s^2),O(c)].
$$

The quadratic overhead in free space matches Savitch's theorem $\mathsf{NSPACE}[s]\subseteq\mathsf{DSPACE}[s^2]$ and the Borodin–Cook–Pippenger bound $\mathsf{PrSPACE}[s]\subseteq\mathsf{DSPACE}[s^2]$, and the catalytic space grows only by a constant factor.

## Proof sketch

By the oracle reduction the problem becomes one query of length $N=2^{O(s)}$ to $\mathsf{NSPACE}[O(s)]$ (respectively promise-$\mathsf{PrSPACE}[O(s)]$). Savitch's midpoint recursion (respectively Borodin–Cook–Pippenger) answers it deterministically in space $O(\log^2 N)=O(s^2)$, recomputing query bits on demand from the reduction, without touching the catalytic tape.

## Depends on

- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)
- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../savitch.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
