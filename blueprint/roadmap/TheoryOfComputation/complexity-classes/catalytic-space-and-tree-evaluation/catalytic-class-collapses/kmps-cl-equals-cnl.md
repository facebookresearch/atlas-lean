# Koucký–Mertz–Pyne–Sami: catalytic logspace absorbs nondeterminism (CL = CNL = coCNL)

$\mathsf{CL}=\mathsf{CNL}$. Since $\mathsf{CL}$ is closed under complement, also $\mathsf{CNL}=\mathsf{coCNL}$.

## Proof sketch

Apply the oracle reduction with $\mathcal{B}=\mathrm{N}$: a $\mathsf{CNL}$ language reduces in $\mathsf{CSPACE}[O(\log n),\mathrm{poly}(n)]$ to a single $\mathsf{NSPACE}[O(\log n)]$ query of polynomial length. Replace the oracle by the catalytic simulation $\mathsf{NSPACE}[O(s)]\subseteq\mathsf{CSPACE}[O(s),2^{O(s)}]$ of Buhrman et al., run on the implicitly given query with a separate catalytic segment; it restores its segment, after which the reduction resets its own tape.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)
- [Buhrman–Cleve–Koucký–Loff–Speelman: logspace-uniform TC^1 is contained in catalytic logspace](bcklss-tc1-in-catalytic-logspace.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- Harry Buhrman, Michal Koucký, Bruno Loff and Florian Speelman, "Catalytic Space: Non-determinism and Hierarchy", Theory of Computing Systems 62(1) (2018).
