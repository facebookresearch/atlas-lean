# Pseudorandom generators against circuits

Let $\ell : \mathbb{N} \to \mathbb{N}$ with $\ell(n) < n$ and $s, \varepsilon$ functions of $n$. A family of functions $G_n : \{0,1\}^{\ell(n)} \to \{0,1\}^{n}$ is an *$(s, \varepsilon)$-pseudorandom generator* if for every $n$ and every Boolean circuit $C$ with $n$ inputs and size at most $s(n)$,

$$\bigl|\Pr[C(G_n(U_{\ell(n)})) = 1] - \Pr[C(U_n) = 1]\bigr| \le \varepsilon(n),$$

where $U_k$ is uniform on $\{0,1\}^k$. For derandomization one further requires that $G_n$ be computable in time $2^{O(\ell(n))}$.

## Depends on

- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Sources

- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, <https://people.seas.harvard.edu/~salil/pseudorandomness/>
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
