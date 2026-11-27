# Strict hierarchy of exact-advice classes

Let $\ell',\Delta:\mathbb{N}\to\mathbb{N}$ with $\ell'(n)+\Delta(n)\le 2^{n}$ for all $n$ and $\Delta$ unbounded. Then $\mathsf{P}/\ell'$ is strictly contained in $\mathsf{P}/(\ell'+\Delta)$.

## Proof sketch

Let $\ell=\ell'+\Delta$. The machine that, given advice $a_n$ of length $\ell(n)$ and the $i$-th string of length $n$, outputs the $i$-th bit of $a_n$ (and $0$ beyond $|a_n|$) defines, for each advice sequence, a language in $\mathsf{P}/\ell$, and different sequences give different languages. A fixed machine with advice of length $\ell'(n)$ realizes at most $2^{\ell'(n)}$ behaviours at length $n$, a $2^{-\Delta(n)}$ fraction of the $2^{\ell(n)}$ functions $f_a$ restricted to length $n$; since $\Delta$ is unbounded, assigning to each machine its own infinite set of lengths and choosing the advice there accordingly defeats every machine that takes $\ell'$-bit advice.

Derived here (not stated in the cited refereed source; Goldreich's online addendum states the case of gap one): the counting step needs only $2^{\ell'(n)}<2^{\ell(n)}$ at each length, so the strict inclusion $\mathsf{P}/a\subsetneq\mathsf{P}/b$ already holds for $a(n)<b(n)\le 2^{n}$, with inclusion by padding advice of length $a(n)$ with a delimiter to length exactly $b(n)$. In particular $\mathsf{P}/k\subsetneq\mathsf{P}/(k+1)$ for every constant $k$, and $\mathsf{P}/(b-1)\subsetneq\mathsf{P}/b$ for positive $b$.

## Depends on

- [Polynomial time with exact-length advice](exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Definition 3.5 and Theorem 4.1, with Theorem 3.7 and Exercise 3.3.
- Oded Goldreich, "A Tighter Version of Thm 4.1", online addendum to "Computational Complexity: A Conceptual Perspective", not refereed (Theorem 4.1': $\mathsf{P}/(\ell-1)\subsetneq\mathsf{P}/\ell$ whenever $\ell(n)\le 2^n$).
