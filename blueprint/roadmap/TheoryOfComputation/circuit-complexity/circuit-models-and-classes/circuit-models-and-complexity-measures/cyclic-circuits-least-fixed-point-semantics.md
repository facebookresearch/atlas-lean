# Cyclic circuits with least-fixed-point semantics

A *cyclic circuit* over a basis interpreted by monotone operations on a complete lattice $(U,\le)$ is a finite system of equations $y_j=\omega_j(z_{j,1},\dots,z_{j,k_j})$, $j=1,\dots,s$, where each argument $z_{j,i}$ is an input or any of the variables $y_1,\dots,y_s$ (feedback is allowed). For each input $x$ the map $(y_j)_j\mapsto(\omega_j(\dots))_j$ is monotone on $U^s$, so by the Knaster–Tarski theorem it has a least fixed point; the circuit computes the values of its designated outputs at that least fixed point. Its cost is $\sum_j c(\omega_j)$. Acyclic circuits are the special case in which the system is triangular.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
