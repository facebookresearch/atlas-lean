# Blum complexity class

Given a Blum measure $\Phi$ and a function $t$ from $\mathbb{N}$ to
$\mathbb{N}$, the Blum class of $t$ consists of the partial functions $f$ from $\mathbb{N}$ to
$\mathbb{N}$ that are computed by some program $c$ whose cost $\Phi_c(n)$ is defined and at most
$t(n)$ for all but finitely many inputs $n$.

The bound is not required at every input: Blum's classes are defined up to finite exceptions,
and the finite exceptions are essential to the gap and union theorems (a program may be slow on
finitely many inputs without leaving the class).

## Sources

- Blum, "A machine-independent theory of the complexity of recursive functions", *Journal of the ACM* 14 (1967), 322–336, Definition 2.
