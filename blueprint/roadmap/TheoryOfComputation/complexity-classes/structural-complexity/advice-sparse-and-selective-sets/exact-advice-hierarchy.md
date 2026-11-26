# Strict hierarchy of exact-advice classes

Let $a,b:\mathbb{N}\to\mathbb{N}$ with $a(n)< b(n)$ for all $n$ and with $b(n)\le 2^{n}$ eventually (so that $b(n)$ advice bits can be stored in the truth table of length-$n$ inputs). Then $\mathsf{P}/a\subsetneq\mathsf{P}/b$. In particular $\mathsf{P}/k\subsetneq\mathsf{P}/(k+1)$ for every constant $k$, and $\mathsf{P}/(b-1)\subsetneq\mathsf{P}/b$ for positive $b$. On the other hand, unbounded nonnegative gaps alone do not force containment: there are polynomially bounded $a\le b$ with $b-a$ unbounded and $\mathsf{P}/a\not\subseteq\mathsf{P}/b$, so pointwise strict growth is the natural hypothesis.

## Proof sketch

Inclusion: pad advice of length $a(n)$ with a delimiter to length exactly $b(n)$. Strictness: by counting, at each length there are $2^{b(n)}$ possible behaviours of a language on the first $b(n)$ inputs, but only $2^{a(n)}$ advice strings for each of countably many machines; diagonalize length by length against machine $i$ at length $n_i$. The counterexample uses advice lengths that are not monotone so that delimiter padding is impossible.

## Depends on

- [Polynomial time with exact-length advice](exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Theorem 3.7, Exercise 3.3, Theorem 4.1.
- Oded Goldreich, "A Tighter Version of Theorem 4.1", Online addendum to Computational Complexity: A Conceptual Perspective.
