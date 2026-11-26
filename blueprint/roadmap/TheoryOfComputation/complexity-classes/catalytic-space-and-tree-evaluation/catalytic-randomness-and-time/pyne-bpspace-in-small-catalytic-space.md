# Pyne: randomized space S runs in catalytic space with S work and S^2 catalytic cells, with a tradeoff

For space-constructible $S=S(n)\ge\log n$, write $\mathsf{CSPACE}[S,C]$ for catalytic algorithms using $O(S)$ work cells and $O(C)$ catalytic cells. Then

$$
\mathsf{BPSPACE}[S]\subseteq\mathsf{CSPACE}[S,S^{2}],
$$

and more generally, for every $\alpha\in[1,3/2]$,

$$
\mathsf{BPSPACE}[S]\subseteq\mathsf{CSPACE}\bigl[S^{\alpha},S^{3-\alpha}\bigr].
$$

Previously only $\mathsf{BPSPACE}[S]\subseteq\mathsf{CSPACE}[S,2^{O(S)}]$ was known. The method also solves the corresponding search problems in $\mathsf{CSPACE}[S,S^2]$ and gives an alternative proof of the Cai–Chakaravarthy–van Melkebeek time-space tradeoff for derandomizing $\mathsf{BPSPACE}[S]$.

## Proof sketch

The algorithm avoids the algebraic register-program techniques. Blocks of the catalytic tape are treated as candidate random strings for the read-once randomized computation; a primitive tests whether a block is random conditioned on the previous ones with respect to the branching program at hand, and if so it is used as randomness, while if not it can be compressed and its space reused. Instantiating this primitive in a recursive framework yields the $S^2$ catalytic bound, and trading recursion depth for work space gives the tradeoff.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Sources

- Edward Pyne, "Derandomizing Logspace with a Small Shared Hard Drive", CCC (2024), LIPIcs 300, 4:1-4:20.
- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
