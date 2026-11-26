# Chen-Cotler-Huang-Li: shadow tomography without quantum memory needs many samples

Every protocol that measures the copies of an unknown $n$-qubit state one at a time (with arbitrary adaptivity but without quantum memory across copies) and solves shadow tomography for $M$ observables to constant accuracy requires $\Omega(\min(M, 2^n))$ copies in the worst case. In contrast, protocols with quantum memory need only $\mathrm{polylog}(M)\cdot n$ copies.

## Proof sketch

Model a memoryless adaptive protocol as a tree of single-copy POVMs and compare the induced distribution over leaves for the maximally mixed state with that for a random perturbation $\frac{1}{2^n}(I + 3\varepsilon P)$ with $P$ a random Pauli. A second-moment (likelihood ratio) bound shows each copy reveals at most $O(1/\min(M, 2^n))$ information about $P$ on average, so distinguishing requires $\Omega(\min(M, 2^n))$ copies; upper bounds with memory come from the Bădescu-O'Donnell algorithm.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [Bădescu-O'Donnell: shadow tomography with log-squared dependence on the number of observables](improved-shadow-tomography-sample-complexity.md)

## Proof depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [Bădescu-O'Donnell: shadow tomography with log-squared dependence on the number of observables](improved-shadow-tomography-sample-complexity.md)

## Sources

- Sitan Chen, Jordan Cotler, Hsin-Yuan Huang, Jerry Li, "Exponential separations between learning with and without quantum memory", FOCS (2021); arXiv:2111.05881.
