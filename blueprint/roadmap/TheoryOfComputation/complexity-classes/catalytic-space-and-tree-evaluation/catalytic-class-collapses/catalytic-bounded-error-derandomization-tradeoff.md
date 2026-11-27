# Catalytic Nisan–Saks–Zhou: bounded-error catalytic space derandomized for all parameters

For all $s=s(n)$, $c=c(n)$ with $\log n\le s\le c\le 2^{s}$ and all $\alpha\in[0,1/2]$,

$$
\mathsf{CBPSPACE}[s,c]\subseteq\mathsf{CSPACE}\bigl[O(s^{1+\alpha}),\,O(c+s^{2-\alpha})\bigr].
$$

In particular $\mathsf{CBPSPACE}[s,c]=\mathsf{CSPACE}[O(s),O(c)]$ whenever $c\ge s^2$, and $\mathsf{CBPSPACE}[s,c]\subseteq\mathsf{CSPACE}[O(s^{3/2}),O(c)]$ for every $c\ge s$, a catalytic analogue of the Saks–Zhou bound. Earlier unconditional derandomization of catalytic randomness (Cook–Li–Mertz–Pyne) required $c=2^{\Theta(s)}$.

## Proof sketch

The oracle reduction with $\mathcal{B}=\mathrm{BP}$ produces one promise-$\mathsf{BPSPACE}[O(s)]$ query of length $2^{O(s)}$. Pyne's catalytic derandomization $\mathsf{BPSPACE}[O(s)]\subseteq\mathsf{CSPACE}[O(s^{1+\alpha}),O(s^{2-\alpha})]$, applied to the query with a fresh catalytic segment of length $O(s^{2-\alpha})$, answers it; the reduction then resets its own segment.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- Edward Pyne, "Derandomizing Logspace with a Small Shared Hard Drive", CCC (2024), LIPIcs 300, 4:1-4:20.
- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
