# Small circuits agree with every function on 1/2 + t/2^n of the inputs

For every $f:\{0,1\}^n\to\{0,1\}$ and every integer $t$ with $2t\le 2^n$, some Boolean function $g$ of De Morgan circuit complexity at most $t(2n+3)+1$ agrees with $f$ on at least a $\tfrac12+t/2^n$ fraction of the inputs. In particular (for $t=1$, $n\ge1$) every function is approximated with advantage $2^{-n}$ by a circuit of size $2n+4$.

## Proof sketch

Start from the better of the two constant functions, which agrees with $f$ on at least half of the inputs, and correct it on $t$ further disagreeing points; each correction costs at most $2n+3$ gates.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Changing one value changes circuit complexity by at most 2n + 3](../circuit-models-and-complexity-measures/one-point-update-changes-complexity-by-2n-plus-3.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
