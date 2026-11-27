# Koucký–Mertz–Pyne–Sami: unbounded-error randomness collapses into catalytic logspace (CL = CPrL)

$\mathsf{CL}=\mathsf{CPrL}$, where $\mathsf{CPrL}$ is unbounded-error randomized catalytic logspace with read-once random bits and certain restoration of the catalytic tape on every random path. Combined with the elementary inclusions among catalytic logspace classes and $\mathsf{CL}=\mathsf{CNL}$,

$$
\mathsf{CL}=\mathsf{CZPL}=\mathsf{CBPL}=\mathsf{CPrL}=\mathsf{CNL}=\mathsf{coCNL}.
$$

## Proof sketch

Use the oracle reduction with $\mathcal{B}=\mathrm{Pr}$: the query asks whether a random walk on a polynomial-size labeled graph from $r$ reaches $t$ with probability above $1/2$, a promise-$\mathsf{PrSPACE}[O(\log n)]$ question. Replace the oracle by the catalytic simulation $\mathsf{PrSPACE}[O(s)]\subseteq\mathsf{CSPACE}[O(s),2^{O(s)}]$. The chain of equalities follows from $\mathsf{CL}\subseteq\mathsf{CZPL}\subseteq\mathsf{CBPL}\subseteq\mathsf{CPrL}$.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)
- [Buhrman–Cleve–Koucký–Loff–Speelman: logspace-uniform TC^1 is contained in catalytic logspace](bcklss-tc1-in-catalytic-logspace.md)
- [Koucký–Mertz–Pyne–Sami: catalytic logspace absorbs nondeterminism (CL = CNL = coCNL)](kmps-cl-equals-cnl.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
