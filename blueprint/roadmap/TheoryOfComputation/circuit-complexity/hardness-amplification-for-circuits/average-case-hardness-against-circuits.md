# Average-case hardness against circuits

A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is *average-case hard for size $s$* if every Boolean function $g$ of De Morgan circuit complexity at most $s$ agrees with $f$ on fewer than a $\tfrac12+\tfrac1s$ fraction of the inputs. The *average-case hardness* $H_{\mathrm{avg}}(f)$ is the largest such $s$; the *worst-case hardness* $H_{\mathrm{wrs}}(f)$ is the largest $s$ such that no circuit of size $s$ computes $f$ exactly. A function is *$\delta$-hard for size $s$* if every circuit of size $s$ errs on at least a $\delta$ fraction of inputs.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 7–8", 2007.
