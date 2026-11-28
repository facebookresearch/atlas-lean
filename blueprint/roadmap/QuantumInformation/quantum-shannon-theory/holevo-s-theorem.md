# Holevo's theorem

For an ensemble $\eta$ of states on $\mathcal{Y}$, given by probabilities $p(a)$ and density operators
$\rho_a$ for $a$ in a finite alphabet, the Holevo quantity is
$\chi(\eta) = S\big(\sum_a p(a)\rho_a\big) - \sum_a p(a) S(\rho_a)$. For every measurement on $\mathcal{Y}$, the
mutual information between the label $a$ and the measurement outcome is at most $\chi(\eta)$; that is, the
accessible information satisfies $I_{\mathrm{acc}}(\eta) \le \chi(\eta)$.

## Depends on

- [Mutual information of a finite joint law](../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)
- [Positive-operator-valued measurements and the Born rule](../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)
- [Von Neumann entropy and Holevo information](classical-quantum-information/von-neumann-entropy-and-holevo-information.md)

## Proof depends on

- [Data processing for quantum relative entropy under Kraus channels](../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-kraus-data-processing.md): data processing for the measurement channel
- [Holevo information as classical-quantum mutual information and its bounds](classical-quantum-information/holevo-information-properties.md): the input relative entropy of the classical-quantum state is $\chi$, up to the factor $\ln 2$

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Theorem 5.49. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
