# Read-once branching programs and space-bounded pseudorandom generators

A *read-once branching program* of width $w$ and length $\ell$ over the binary alphabet has states $\{1, \dots, w\}$, a start state, and for each step $j \le \ell$ a transition function $\{1,\dots,w\} \times \{0,1\} \to \{1,\dots,w\}$; it reads the input bits $y_1, \dots, y_\ell$ once in order and accepts if the final state lies in an accepting set. A generator $G : \{0,1\}^k \to \{0,1\}^\ell$ is an $(s, \varepsilon)$-*pseudorandom generator* (against space $s$) if for every read-once program $B$ of width $2^s$,

$$
\bigl|\Pr[B(G(U_k)) = 1] - \Pr[B(U_\ell) = 1]\bigr| \le \varepsilon .
$$

Examples of read-once tests: counting ones modulo $m$ has width $m$, and the parity of the bits in a set $S$ has width $2$.

## Depends on

- [Uniform distribution on a finite type](../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica, 1992.
