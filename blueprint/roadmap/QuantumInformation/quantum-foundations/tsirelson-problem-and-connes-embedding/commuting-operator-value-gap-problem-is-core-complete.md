# Deciding whether the commuting-operator value of a nonlocal game is 1 or below 1/2 is coRE-complete

Multiprover interactive proofs with commuting-operator entanglement capture exactly coRE: deciding, for a nonlocal game promised to have commuting-operator value $1$ or less than $1/2$, which case holds is coRE-complete and hence undecidable.

For a two-player one-round nonlocal game $\mathcal{G}$, the *commuting-operator value* $\omega^{co}(\mathcal{G})$ is the supremum of the winning probability over [commuting-operator strategies](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md). The *commuting operator value problem* is the promise problem with yes-instances $\{\mathcal{G} : \omega^{co}(\mathcal{G}) = 1\}$ and no-instances $\{\mathcal{G} : \omega^{co}(\mathcal{G}) < 1/2\}$, with games given by a polynomial-time verifier. $\mathrm{MIP}^{co}$ is the class of languages with a two-prover one-round interactive proof in which the provers share commuting-operator entanglement; it is complete, under polynomial-time reductions, for the commuting operator value problem.

**Theorem (Lin).** $\mathrm{MIP}^{co} = \mathrm{coRE}$ (Theorem 1.1 of the source). Equivalently, the commuting operator value problem is $\mathrm{coRE}$-complete; in particular it is undecidable.

The inclusion $\mathrm{MIP}^{co} \subseteq \mathrm{coRE}$ follows from the convergence of the NPA semidefinite hierarchy to the commuting-operator value. For the tensor-product model the analogous class is $\mathrm{MIP}^* = \mathrm{RE}$, so the two models of entanglement give different verification powers. The source also shows that deciding whether $\omega^*(\mathcal{G}) = \omega^{co}(\mathcal{G})$ or $|\omega^*(\mathcal{G}) - \omega^{co}(\mathcal{G})| > c$, for any fixed constant $c$, is $\mathrm{RE}$-complete.

## Depends on

- [Commuting-operator strategies and value](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md)
- [Two-player nonlocal games: classical and entangled values](../../../QuantumInformation/quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Polynomial-time reduction between promise problems](../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)

## Proof depends on

- [The NPA semidefinite hierarchy converges to the commuting-operator value](npa-hierarchy-converges-to-commuting-operator-value.md)
- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The upper bound is the NPA hierarchy: its semidefinite programs converge from above to $\omega^{co}(\mathcal{G})$, so the no-instances form a recursively enumerable set. For hardness the source introduces a condition on promise problems, *compressibility*, under which a problem is $\mathrm{RE}$- or $\mathrm{coRE}$-complete as soon as it admits a compression theorem and an algorithm that halts on one side of the promise; this avoids the need to preserve resources such as the entanglement dimension, which the proof of $\mathrm{MIP}^* = \mathrm{RE}$ uses and which is not available for commuting-operator strategies. The source then proves a gap compression theorem valid for both the tensor-product and the commuting-operator value, for games given by conditionally linear verifiers, using question reduction by introspection, answer reduction and a new information-theoretic proof of anchored parallel repetition in the commuting-operator model. Together with the NPA algorithm, which halts on the no side, this gives $\mathrm{coRE}$-hardness by a reduction from the complement of the halting problem. The compressibility criterion and the commuting-operator compression theorem have no pages.

## Sources

- J. Lin, "MIP^co = coRE", Proceedings of the 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 314–322, https://doi.org/10.1145/3798129.3800751; read in arXiv:2510.07162v1 (Theorem 1.1, Definition 1.2 and Theorem 1.3 in Section 1 of arXiv:2510.07162v1, with the value problem defined in its section on sequences and compression).
