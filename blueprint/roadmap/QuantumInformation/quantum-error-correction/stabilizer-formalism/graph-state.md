# Graph state

Let $G = (V, E)$ be a finite simple graph with vertex set $V$, $|V| = n$, and neighbourhoods $N_a$. For each vertex $a$
the operator

$$K_a = X_a \prod_{b \in N_a} Z_b$$

is an element of the $n$-qubit [Pauli group](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md).
The $K_a$ commute pairwise and are independent, so they generate a stabilizer group of order $2^n$; the *graph state*
$|G\rangle$ is its [stabilizer state](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md),
the joint $+1$ eigenvector of all $K_a$. Equivalently
$|G\rangle = \prod_{\{a, b\} \in E} CZ_{ab}\, |+\rangle^{\otimes n}$, where $CZ_{ab}$ is the controlled-$Z$ gate on qubits
$a, b$. The other joint eigenvectors of the $K_a$ are $Z$-flips of $|G\rangle$ and together form a basis. The stabilizer
tableau of $|G\rangle$ is $(I \mid \Gamma)$, with $\Gamma$ the adjacency matrix.

## Depends on

- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- M. Hein, J. Eisert and H. J. Briegel, *Multiparty entanglement in graph states*, Phys. Rev. A 69 (2004), 062311, arXiv:quant-ph/0307130, Section II, equations (6)–(7) (the correlation operators $K_G^{(a)}$ and the graph state $|G\rangle$) and the equivalent description by Ising interactions (controlled-$Z$ gates) on $|+\rangle^{\otimes n}$.
- M. Van den Nest, J. Dehaene and B. De Moor, *Graphical description of the action of local Clifford transformations on graph states*, Phys. Rev. A 69 (2004), 022316, arXiv:quant-ph/0308151, Section II (generator matrix $(\Gamma \mid I)$ of a graph state).
