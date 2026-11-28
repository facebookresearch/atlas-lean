# No-signalling for local operations

Let $\rho$ be a state on $X \otimes Y$ and let $\Psi$ be a trace-preserving channel from $Y$ to any output system $Y'$,
for example a measurement of $Y$ whose outcome is recorded in a classical register that is part of $Y'$. Then
$\mathrm{Tr}_{Y'}((\mathrm{id}_X \otimes \Psi)(\rho)) = \mathrm{Tr}_Y(\rho)$: the reduced state on $X$ is unchanged. The invariant is
the unconditioned marginal; the state of $X$ conditioned on a particular outcome of a measurement on $Y$ can differ
from $\mathrm{Tr}_Y(\rho)$.

## Depends on

- [Partial trace over the second factor](../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)
- [Quantum channel](../quantum-operations/quantum-channel.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Section 2.1.3, equation (2.33) (the partial trace is the identity tensored with the trace on the traced-out factor) and Definition 2.13 (channels are completely positive and trace preserving), from which the identity follows. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Chapter 18, Exercise 7 (a local unitary on one half of an entangled pure state gives no information to the other party). <https://arxiv.org/pdf/1907.09415v6>
