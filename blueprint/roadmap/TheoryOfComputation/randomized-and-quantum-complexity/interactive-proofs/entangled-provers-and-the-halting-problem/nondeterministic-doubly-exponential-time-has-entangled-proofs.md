# NEEXP has two-prover entangled interactive proofs

$\mathrm{NEEXP} \subseteq \mathrm{MIP}^*$, where $\mathrm{NEEXP} = \bigcup_k \mathrm{NTIME}(2^{2^{n^k}})$. Consequently $\mathrm{MIP}^* \ne \mathrm{MIP}$, since $\mathrm{MIP} = \mathrm{NEXP} \subsetneq \mathrm{NEEXP}$ by the nondeterministic time hierarchy. Earlier, Fitzsimons-Ji-Vidick-Yuen showed that for every time-constructible $R$, nondeterministic time $\exp(\exp(\cdots\exp(n)))$ with $R(n)$ exponentials has entangled multiprover protocols with a constant number of provers, completeness $1$ and soundness $1 - \exp(-C\exp(\cdots\exp(n)))$ with $R(n)-1$ exponentials, for a universal constant $C > 0$.

## Proof sketch

Natarajan and Wright perform one round of introspection: the provers sample exponentially long questions of the $\mathrm{NEXP}$-complete protocol themselves from shared EPR pairs, certified by the quantum low-degree test, turning a protocol for $\mathrm{NEXP}$ on exponentially long inputs into one with polynomial-size questions. Separation from $\mathrm{MIP} = \mathrm{NEXP}$ follows from the non-deterministic time hierarchy.

## Depends on

- [The class MIP* of languages with entangled two-prover proofs](the-class-mip-star.md)

## Proof depends on

- [Pauli basis test with polylogarithmic question length](introspectable-pauli-basis-test.md)

## Sources

- Anand Natarajan, John Wright, "NEEXP is contained in MIP*", FOCS (2019); arXiv:1904.05870.
- Joseph Fitzsimons, Zhengfeng Ji, Thomas Vidick, Henry Yuen, "Quantum proof systems for iterated exponential time, and beyond", STOC (2019); arXiv:1805.12166.
