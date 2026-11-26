# The nondeterministic and Arthur–Merlin catalytic logspace hierarchies collapse to CL

Define $\Sigma_k^{\mathsf{CL}}$ ($\Pi_k^{\mathsf{CL}}$) by valid catalytic logspace machines that receive quantified strings $y_1,\dots,y_k$ with alternating quantifiers starting with $\exists$ ($\forall$), written outermost first on a one-way read-only tape, so each $y_j$ is read once and no $y_j$ is read after any $y_{j'}$ with $j'>j$; define $\mathsf{MA}_k^{\mathsf{CL}}$ and $\mathsf{AM}_k^{\mathsf{CL}}$ analogously with alternating existential and bounded-error random quantifiers. Then

$$
\mathsf{CL}=\bigcup_{k\in\mathbb{N}}\Sigma_k^{\mathsf{CL}}=\bigcup_{k\in\mathbb{N}}\Pi_k^{\mathsf{CL}}=\bigcup_{k\in\mathbb{N}}\mathsf{MA}_k^{\mathsf{CL}}=\bigcup_{k\in\mathbb{N}}\mathsf{AM}_k^{\mathsf{CL}}.
$$

## Proof sketch

The compute-or-compress reduction only manipulates the configuration graph and is insensitive to how acceptance is defined on it, so the same argument scales to quantified read-once choices and reduces each hierarchy class to a single query to the corresponding ordinary logspace hierarchy on a polynomial-size graph. With read-once quantifier access the logspace levels collapse to classes already simulable in $\mathsf{CL}$ (for instance $\Sigma_k^{\mathsf{L}}=\mathsf{NL}$, and Mertz–Sdroievski place Merlin–Arthur logspace in $\mathsf{CL}$), and these oracles are replaced by catalytic simulations.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)
- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)
- [Koucký–Mertz–Pyne–Sami: unbounded-error randomness collapses into catalytic logspace (CL = CPrL)](kmps-cl-equals-cprl.md)
- [Buhrman–Cleve–Koucký–Loff–Speelman: logspace-uniform TC^1 is contained in catalytic logspace](bcklss-tc1-in-catalytic-logspace.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
