# Log-space uniform circuit families

A family $(C_n)_{n \in \mathbb{N}}$ of flat Boolean
circuits, $C_n$ having $n$ inputs, is log-space uniform when there is a log-space computable
function $D$ on bitstrings such that, for every $n$, decoding $D(1^n)$ (where $1^n$ is the string
of $n$ ones) as a list of (gate kind, references) pairs succeeds and returns the serial encoding
of $C_n$, that is, the list of the serial encodings of its gates in order. Since $1^n$ has
length $n$, the description is computed in space $O(\log n)$.

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 6.21 (log-space uniformity); M. Sipser, Introduction to the Theory of Computation, 3rd ed., 2013, Definition 9.20.
