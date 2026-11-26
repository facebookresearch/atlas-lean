# Space-bounded pseudorandom generators are small-bias generators

For every set $S$ of positions, the parity $\bigoplus_{i \in S} y_i$ is computed by a read-once branching program of width $2$. Consequently, for every $s \ge 1$, an $(s, \varepsilon)$-pseudorandom generator is a $2\varepsilon$-bias generator.

## Proof sketch

The width-two program tracks the running parity of the bits read at positions in $S$ and ignores the others. The bias at $S$ is twice the distinguishing advantage of this program, since the uniform distribution has parity exactly one half.

## Depends on

- [Read-once branching program and space-bounded pseudorandom generator](read-once-branching-programs-and-space-bounded-prgs.md)
- [Small-bias distribution and generator](small-bias-distributions.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
