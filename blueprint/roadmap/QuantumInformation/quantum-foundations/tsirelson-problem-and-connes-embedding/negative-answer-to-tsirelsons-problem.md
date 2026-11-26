# Negative answer to Tsirelson's problem: C_qa is not C_qc

There exist finite sets $\mathcal{X}, \mathcal{A}$ with $C_{qa}(\mathcal{X}, \mathcal{A}) \subsetneq C_{qc}(\mathcal{X}, \mathcal{A})$. Moreover there is an explicit synchronous game $G$ with $\omega^*(G) < \omega^{co}(G)$.

## Proof sketch

If $C_{qa} = C_{qc}$ for all finite sets, then $\omega^* = \omega^{co}$ for every game. The gap problem would then be RE-hard by $\mathrm{MIP}^* = \mathrm{RE}$ and also in coRE by the NPA hierarchy, so the halting problem would be both recognizable and co-recognizable, hence decidable, a contradiction. Running the argument effectively produces an explicit game, constructed from a non-halting machine whose non-halting is unprovable in the relevant sense.

## Depends on

- [Tsirelson's problem](tsirelsons-problem-closure-version.md)
- [Quantum correlation sets C_q, C_qs, C_qa and C_qc](quantum-correlation-sets-q-qs-qa-qc.md)

## Proof depends on

- [MIP* = RE (Ji, Natarajan, Vidick, Wright, Yuen)](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/mip-star-equals-re.md)
- [The NPA semidefinite hierarchy converges to the commuting-operator value](npa-hierarchy-converges-to-commuting-operator-value.md)
- [The halting problem is not co-recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-co-recognizable-halting.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Miguel Navascues, Stefano Pironio, Antonio Acin, "A convergent hierarchy of semidefinite programs characterizing the set of quantum correlations", New Journal of Physics 10 (2008); arXiv:0803.4290.
