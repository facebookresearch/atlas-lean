# Anshu-Nirkhe: circuit lower bounds for low-error states of code Hamiltonians

For the code Hamiltonians of quantum LDPC codes with linear rate and polynomial distance $n^{\Omega(1)}$ (for instance hypergraph product codes of good classical LDPC codes), there is $\varepsilon > 0$ such that every state that is a codeword affected by errors on at most $\varepsilon n$ qubits (and more generally every state whose $X$- and $Z$-basis outcome distributions are supported near the code) has circuit depth $\Omega(\log d)$, where $d$ is the code distance.

## Proof sketch

Errors on few qubits keep the measurement distributions within small Hamming distance of the code's cosets, so the clustering structure holds with cluster separation equal to the distance $d$. The spread lemma with $D = d$ and the uncertainty relation for the $\Theta(n)$ logical qubits give the depth bound.

## Depends on

- [Output distributions of shallow circuits do not concentrate on two distant sets](shallow-circuits-produce-well-spread-distributions.md)
- [Uncertainty relation for complementary logical measurements](uncertainty-relation-for-logical-cluster-labels.md)
- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Proof depends on

- [Output distributions of shallow circuits do not concentrate on two distant sets](shallow-circuits-produce-well-spread-distributions.md)
- [Uncertainty relation for complementary logical measurements](uncertainty-relation-for-logical-cluster-labels.md)
- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Sources

- Anurag Anshu, Chinmay Nirkhe, "Circuit lower bounds for low-energy states of quantum code Hamiltonians", ITCS (2022); arXiv:2011.02044.
