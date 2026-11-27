# The AC, TC and AC[q] hierarchies

For a Boolean basis $\Omega$ and $i\ge0$, let $\mathsf{C}^i[\Omega]$ be the non-uniform class of languages whose slices are decided by circuit families, with no uniformity condition, over $\Omega$ of size polynomial in $n$ and depth at most $c(\lfloor\log_2\max(n,1)\rfloor+1)^i$ for a constant $c$ (the maximum makes the bound defined for the slice $n=0$). Then:

- $\mathsf{AC}^i$ uses $\neg$ and unbounded fan-in $\wedge,\vee$;
- $\mathsf{AC}^i[q]$, for an integer $q\ge2$, adds unbounded fan-in $\mathrm{MOD}_q$ gates (output $1$ iff the number of true inputs is not divisible by $q$);
- $\mathsf{TC}^i$ adds unbounded fan-in majority gates;
- $\mathsf{NC}^i$ uses fan-in two.

$\mathsf{TC}^0$ is the class of languages decided by polynomial-size constant-depth threshold (equivalently majority) circuits. Directly from the definitions, $\mathsf{NC}^i\subseteq\mathsf{AC}^i\subseteq\mathsf{AC}^i[q]$ and $\mathsf{AC}^i\subseteq\mathsf{TC}^i$. The inclusions $\mathsf{AC}^i[q]\subseteq\mathsf{TC}^i$ and $\mathsf{TC}^i\subseteq\mathsf{NC}^{i+1}$ are not part of these definitions; they are separate results built on them, from constant-depth simulations of $\mathrm{MOD}_q$ gates by majority gates and logarithmic-depth fan-in-two circuits for majority. The log-space uniform $\mathsf{NC}^k$ of the linked page is the subclass of the non-uniform $\mathsf{NC}^k$ decided by log-space uniform families; the inclusions that hold by definition hold for the log-space uniform versions of all four hierarchies as well.

## Depends on

- [Threshold gates and the basis of threshold circuits](threshold-gates-and-threshold-circuits.md)
- [The class NC^k](../../complexity-classes/time-and-space-complexity-classes/nck.md)
- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [The class $\mathsf{AC}^0(m)$](../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
