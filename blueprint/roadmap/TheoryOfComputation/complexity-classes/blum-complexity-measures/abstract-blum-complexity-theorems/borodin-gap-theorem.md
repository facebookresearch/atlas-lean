# Borodin's gap theorem

For every Blum measure $\Phi$ and every total computable $g$ with $g(n)\ge n$ (more generally $g(n,m)\ge m$), there is a total computable bound $t$ such that

$$
C_{g\circ t}=C_t ,
$$

i.e. no program has cost between $t(n)$ and $g(t(n))$ for almost all $n$ unless it already has cost at most $t(n)$ a.e. Hence complexity classes do not grow uniformly with the bound.

## Proof sketch

Choose $t(n)$ to be the least $m$ such that no program $c\le n$ has $m<\Phi_c(n)\le g(n,m)$; such $m$ exists because only finitely many values $\Phi_c(n)$, $c\le n$, occur, and it is computable since the Blum predicate is decidable.

## Depends on

- [Blum complexity measure](../blum-measure.md)
- [Blum complexity class](../blum-class.md)

## Sources

- Allan Borodin, "Computational Complexity and the Existence of Complexity Gaps", Journal of the ACM 19(1), 1972.
- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999.
