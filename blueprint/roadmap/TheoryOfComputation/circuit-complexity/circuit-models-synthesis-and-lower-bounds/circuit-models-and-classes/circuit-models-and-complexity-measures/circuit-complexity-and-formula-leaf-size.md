# Circuit complexity, binary cost and formula leaf size

Fix a basis $\Omega$ over a carrier $U$ and a weight $c$ on $\Omega$. The *circuit complexity* $C_{\Omega,c}(f)$ of a map $f:U^n\to U^m$ is the least weighted cost of a circuit over $\Omega$ computing $f$ (and $+\infty$ if none exists). Standard instances for Boolean functions $f:\{0,1\}^n\to\{0,1\}$:

- *De Morgan size* $C(f)$: basis $\{\wedge,\vee,\neg,0,1\}$ with fan-in two, every gate charged;
- *binary cost*: only the AND and OR gates are charged, negations and constants are free;
- *$B_2$-complexity*: the full binary basis of all $16$ Boolean functions of two arguments, every gate charged;
- *formula leaf size* $L(f)$: the least number of input leaves (counted with multiplicity) of a De Morgan formula computing $f$.

$\mathrm{SIZE}(s(n))$ denotes the class of languages whose $n$-th slice $f_n$ has $C(f_n)\le s(n)$ for all $n$. De Morgan size and formula leaf size are the measures $\mathrm{CC}$ and leaf size of [Circuit complexity of a Boolean function and truth tables](../../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md).

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Circuit complexity of a Boolean function and truth tables](../../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
