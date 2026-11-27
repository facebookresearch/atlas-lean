# Kernelization and polynomial compression

A **kernelization** of a parameterized problem $(Q,\kappa)$ is a polynomial-time map $K$ with $K(x)\in Q\iff x\in Q$ and $|K(x)|+\kappa(K(x))\le g(\kappa(x))$ for some computable $g$; it is **polynomial** if $g$ is a polynomial. A **polynomial compression** into a language $B$ is a polynomial-time map $x\mapsto y$ with $x\in Q\iff y\in B$ and $|y|\le p(\kappa(x))$. A decidable parameterized problem is in $\mathsf{FPT}$ iff it has a kernel; problems in $\mathsf{P}$ have constant-size kernels.

## Depends on

- [Parameterized problems](../param-problem.md)
- [Fixed-parameter tractable problems](../fpt.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015.
- Jörg Flum and Martin Grohe, "Parameterized Complexity Theory", Springer, 2006.
