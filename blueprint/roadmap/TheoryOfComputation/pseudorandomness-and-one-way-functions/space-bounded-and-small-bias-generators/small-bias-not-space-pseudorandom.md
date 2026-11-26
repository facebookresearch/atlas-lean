# An exponentially small-bias distribution fooled by no width-four automaton

Let $D_n$ be the uniform distribution on the words in $\{0,1\}^n$ whose Hamming weight is divisible by three. Then $D_n$ is $4c^n$-biased with $c = \sqrt{3}/2 < 1$, and for every $n \ge 10$ there is a read-once branching program of width $4$ (space $2$; three states suffice to count the weight modulo three) that distinguishes $D_n$ from the uniform distribution with advantage greater than $0.666$. Hence small bias does not imply pseudorandomness for space-bounded tests.

## Proof sketch

The program counts the weight modulo three and accepts on residue zero, which has probability $1$ under $D_n$ and about $1/3$ under the uniform distribution. The bias at a nonempty set $S$ is computed with cube roots of unity: the character sums $(1 + \omega)^{n}$ and $(1 - \omega)^{|S|}(1+\omega)^{n - |S|}$ have modulus at most $(\sqrt{3})^{n}$ relative to $2^n$, after normalizing by $|\{w : 3 \mid |w|\}| \approx 2^n/3$.

## Depends on

- [Small-bias distribution and generator](small-bias-distributions.md)
- [Read-once branching program and space-bounded pseudorandom generator](read-once-branching-programs-and-space-bounded-prgs.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
