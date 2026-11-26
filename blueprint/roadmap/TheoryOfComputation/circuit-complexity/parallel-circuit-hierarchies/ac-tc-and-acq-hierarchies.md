# The AC, TC and AC[q] hierarchies

For a Boolean basis $\Omega$ and $i\ge0$, let $\mathsf{C}^i[\Omega]$ be the class of languages whose slices are decided by circuits over $\Omega$ of size polynomial in $n$ and depth at most $c(\lfloor\log_2 n\rfloor+1)^i$ for a constant $c$. Then:

- $\mathsf{AC}^i$ uses $\neg$ and unbounded fan-in $\wedge,\vee$;
- $\mathsf{AC}^i[q]$ adds unbounded fan-in $\mathrm{MOD}_q$ gates (output $1$ iff the number of true inputs is not divisible by $q$);
- $\mathsf{TC}^i$ adds unbounded fan-in majority gates;
- $\mathsf{NC}^i$ uses fan-in two.

$\mathsf{TC}^0$ is the class of languages decided by polynomial-size constant-depth threshold (equivalently majority) circuits. One has $\mathsf{NC}^i\subseteq\mathsf{AC}^i\subseteq\mathsf{AC}^i[q]\subseteq\mathsf{TC}^i\subseteq\mathsf{NC}^{i+1}$.

## Depends on

- [Threshold gates and the basis of threshold circuits](threshold-gates-and-threshold-circuits.md)
- [The class NC^k](../../complexity-classes/time-and-space-complexity-classes/nck.md)
- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [The class $\mathsf{AC}^0(m)$](../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
