# Local correlations on the maximally entangled state and the transpose trick

Let $\Phi = |\iota|^{-1/2}\sum_{i\in\iota}|i,i\rangle$. For all $A,B\in M_\iota(\mathbb{C})$,

$$
\langle\Phi,(A\otimes B)\Phi\rangle = \frac{\operatorname{Tr}(A^{\mathsf T}B)}{|\iota|}.
$$

Consequently both reduced states of $|\Phi\rangle\langle\Phi|$ equal $I/|\iota|$, and for every $\pm1$ observable $O$ the observables $O\otimes I$ and $I\otimes O^{\mathsf T}$ agree perfectly in the vector state of $\Phi$: $\|O\otimes I - I\otimes O^{\mathsf T}\|_\Phi = 0$.

## Proof sketch

Expanding in the basis, $\langle\Phi,(A\otimes B)\Phi\rangle = |\iota|^{-1}\sum_{i,j}A_{ij}B_{ij}$, which is $\operatorname{Tr}(A^{\mathsf T}B)/|\iota|$. For a $\pm1$ observable, $\|O\otimes I-I\otimes O^{\mathsf T}\|_\Phi^2 = 2-2\operatorname{Re}\langle\Phi,(O\otimes O^{\mathsf T})\Phi\rangle = 2-2\operatorname{Tr}(O^2)/|\iota| = 0$.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)
- [Bell basis and maximally entangled states](../bell-basis-and-maximally-entangled-states.md)

## Sources

- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
- R. Cleve, P. Hoyer, B. Toner and J. Watrous, "Consequences and limits of nonlocal strategies", Proceedings of the 19th IEEE Conference on Computational Complexity, 236-249, 2004.
