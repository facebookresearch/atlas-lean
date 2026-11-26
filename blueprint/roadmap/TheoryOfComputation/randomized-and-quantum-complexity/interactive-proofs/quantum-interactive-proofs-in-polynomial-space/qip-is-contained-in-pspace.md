# QIP is contained in PSPACE (Jain-Ji-Upadhyay-Watrous)

$\mathrm{QIP} \subseteq \mathrm{PSPACE}$. Concretely, there is a polynomial-space algorithm that, given a QMAM verifier with completeness $c$ and soundness $s$ where $c - s \ge 1/\mathrm{poly}(n)$, decides on input $x$ which case holds.

## Proof sketch

By Kitaev-Watrous and Marriott-Watrous assume a QMAM protocol with completeness $1$ and soundness $1/2 + \varepsilon$. Its optimal value is the semidefinite program over $D = 2^{\mathrm{poly}(n)}$-dimensional density operators. A primal-dual matrix multiplicative weights scheme decides whether the optimum exceeds $7/8$ or is below $3/4$ using $T = O(\log D)$ iterations, each consisting of matrix exponentials and spectral projections computable in depth $\mathrm{poly}(n)$. The whole procedure is in $\mathrm{NC}(\mathrm{poly}) = \mathrm{PSPACE}$.

## Depends on

- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)
- [Marriott-Watrous: QIP equals QMAM](marriott-watrous-qip-equals-qmam.md)
- [Optimal QMAM acceptance probability as an exponential-size semidefinite program](qmam-acceptance-as-exponential-semidefinite-program.md)
- [Regret bound for the matrix multiplicative weights update](matrix-multiplicative-weights-regret-bound.md)
- [Matrix exponentials of exponential-dimension matrices in polynomial depth](matrix-exponentials-in-polynomial-depth.md)
- [Borodin: NC(poly) = PSPACE](borodin-polynomial-depth-equals-polynomial-space.md)

## Sources

- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
