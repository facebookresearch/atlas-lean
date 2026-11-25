# Average-case hardness in E derandomizes BPP

Suppose there are a function $f : \{0,1\}^* \to \{0,1\}$ computable in time $2^{O(n)}$ and a constant $\varepsilon > 0$ such that for every $n$, every Boolean circuit of size at most $2^{\varepsilon n}$ agrees with $f$ on at most a $\tfrac12 + 2^{-\varepsilon n}$ fraction of the inputs of length $n$. Then $\mathsf{BPP} = \mathsf{P}$. The proof applies the Nisan–Wigderson generator with seed length $O(\log m)$ and enumerates seeds.

## Proof depends on

- [Nisan–Wigderson generator](nisanwigderson-generator.md)
- [Pseudorandom generators with logarithmic seed derandomize BPP](pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- N. Nisan and A. Wigderson, "Hardness vs randomness", *Journal of Computer and System Sciences* 49(2):149–167, 1994
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, <https://theory.cs.princeton.edu/complexity/>, Theorem 16.10
