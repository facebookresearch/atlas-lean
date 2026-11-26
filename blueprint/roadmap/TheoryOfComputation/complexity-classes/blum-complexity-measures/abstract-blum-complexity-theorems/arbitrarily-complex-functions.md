# Arbitrarily complex computable functions; complexity classes are proper

For every Blum measure $\Phi$ and every total computable bound $t$, there is a total computable $0/1$-valued function $f$ such that every program $c$ computing $f$ satisfies $\Phi_c(n)>t(n)$ for all sufficiently large $n$. In particular, every complexity class $C_t=\{\varphi_c\text{ total}: \Phi_c(n)\le t(n)\text{ a.e.}\}$ of a computable bound misses some computable $0/1$-valued function.

## Proof sketch

Diagonalize with priorities: at input $n$, among programs $c\le n$ not yet cancelled with $\Phi_c(n)\le t(n)$ (decidable), cancel the least one and set $f(n)=1-\varphi_c(n)$. Each program that is cheap infinitely often is eventually cancelled, so it does not compute $f$.

## Depends on

- [Blum complexity measure](../blum-measure.md)
- [Blum complexity class](../blum-class.md)

## Sources

- Manuel Blum, "A Machine-Independent Theory of the Complexity of Recursive Functions", Journal of the ACM 14(2), 1967.
- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999.
