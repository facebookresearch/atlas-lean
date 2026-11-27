# Isolated true inputs of a Boolean function

Let $g : \{0,1\}^n \to \{0,1\}$. An input $x$ is an *isolated true input* of $g$ if $g(x) = 1$ and $g(x \oplus e_i) = 0$ for every unit vector $e_i$, i.e. $g$ is false at all $n$ Hamming neighbours of $x$. Dually $x$ is an isolated false input if $g(x)=0$ and $g$ is true at all neighbours. For the parity function $\bigoplus_{i} x_i$, all $2^{n-1}$ true inputs and all $2^{n-1}$ false inputs are isolated.

## Sources

- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999, Article 11.
