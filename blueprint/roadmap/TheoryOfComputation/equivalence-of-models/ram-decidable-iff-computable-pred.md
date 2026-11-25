# RAM machines compute exactly the computable predicates

A predicate $P$ on $\mathbb{N}$ is RAM decidable if there is a RAM program, a finite list of RAM instructions, whose evaluation on the single input $n$ (placed in register $0$, with the accumulator, the program counter and all other registers at $0$) halts with output equal to the characteristic function of $P$ at $n$, for every $n \in \mathbb{N}$: output $1$ if $P(n)$ holds and $0$ otherwise.

Statement: for every predicate $P \subseteq \mathbb{N}$, $P$ is RAM decidable if and only if $P$ is computable, that is, $P$ has a decision procedure whose characteristic function $\mathbb{N} \to \{\mathrm{false}, \mathrm{true}\}$ is a computable function.

## Sources

- A. V. Aho, J. E. Hopcroft, J. D. Ullman, The Design and Analysis of Computer Algorithms, Addison-Wesley, 1974, §1.2.
- R. I. Soare, Recursively Enumerable Sets and Degrees, Springer, Ch. I, Theorem 2.3.
