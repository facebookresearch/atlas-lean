# Strict hierarchy of exact-advice classes

Let $a,b:\mathbb{N}\to\mathbb{N}$ with $a(n)< b(n)$ for all $n$ and with $b(n)\le 2^{n}$ eventually (so that $b(n)$ advice bits can be stored in the truth table of length-$n$ inputs). Then $\mathsf{P}/a\subsetneq\mathsf{P}/b$. In particular $\mathsf{P}/k\subsetneq\mathsf{P}/(k+1)$ for every constant $k$, and $\mathsf{P}/(b-1)\subsetneq\mathsf{P}/b$ for positive $b$.

## Proof sketch

Inclusion: pad advice of length $a(n)$ with a delimiter to length exactly $b(n)$. Strictness: the machine that outputs the $i$-th advice bit on the $i$-th input of length $n$ (and $0$ beyond $b(n)$) defines, for each advice sequence of length $b$, a language in $\mathsf{P}/b$, and different sequences give different languages. A fixed machine with advice of length $a(n)\le b(n)-1$ realizes at most $2^{a(n)}$ behaviours at length $n$, so some advice string of length $b(n)$ defeats it at that length; assigning to each machine its own infinite set of lengths and choosing the advice there accordingly defeats every machine that takes $a$-bit advice.

## Depends on

- [Polynomial time with exact-length advice](exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 3.7, Exercise 3.3 and Theorem 4.1 (strictness for unbounded gaps).
- Oded Goldreich, "A Tighter Version of Thm 4.1", online addendum to "Computational Complexity: A Conceptual Perspective" (Theorem 4.1': $\mathsf{P}/(\ell-1)\subsetneq\mathsf{P}/\ell$ whenever $\ell(n)\le 2^n$).
