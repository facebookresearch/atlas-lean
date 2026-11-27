# Formula-size complexity classes

For $s:\mathbb{N}\to\mathbb{N}$, $\mathsf{Formula}[s]$ is the class of languages whose $n$-th slice is computed by a De Morgan formula with at most $s(n)$ leaves, for every $n$; $\mathsf{Formula}[\mathrm{poly}]=\bigcup_c\mathsf{Formula}[n^c]$. By Spira's theorem $\mathsf{Formula}[\mathrm{poly}]$ equals nonuniform $\mathsf{NC}^1$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The class NC^k](../../../../complexity-classes/time-and-space-complexity-classes/nck.md)

## Sources

- Igor Carboni Oliveira, Rahul Santhanam, "Hardness Magnification for Natural Problems", 59th IEEE Annual Symposium on Foundations of Computer Science (FOCS 2018), 2018.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
