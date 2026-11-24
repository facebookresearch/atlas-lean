# Restricting a Frobenius element to an intermediate field

Let $K \subseteq L \subseteq M$
be a tower of number fields with $L/K$ and $M/K$ Galois, and let $\mathcal{O}_K$,
$\mathcal{O}_L$ and $\mathcal{O}_M$ be their rings of integers. Let $Q_L$ be a prime of
$\mathcal{O}_L$ at which $\mathcal{O}_L$ is unramified over $\mathcal{O}_K$, let $Q_M$ be a
prime of $\mathcal{O}_M$ lying over $Q_L$ with $\mathcal{O}_M/Q_M$ finite, and let $q$ be the
number of elements of $\mathcal{O}_K/\mathfrak{p}$, where $\mathfrak{p}$ is the prime of
$\mathcal{O}_K$ below $Q_M$ (equivalently, below $Q_L$). If $\sigma_M \in \mathrm{Gal}(M/K)$
satisfies $\sigma_M(x) \equiv x^q \pmod{Q_M}$ for all $x \in \mathcal{O}_M$ and
$\sigma_L \in \mathrm{Gal}(L/K)$ satisfies $\sigma_L(y) \equiv y^q \pmod{Q_L}$ for all
$y \in \mathcal{O}_L$, then the restriction of $\sigma_M$ to $L$ equals $\sigma_L$.

## Sources

- A. V. Sutherland, *Number Theory I*, MIT 18.785 lecture notes (Fall 2021), Lecture 7, Proposition 7.22 (its second statement) and Proposition 7.13 (the diagram of decomposition and inertia groups it rests on), https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/. Proposition 7.22 assumes the prime of the top field unramified; here only the prime $Q_L$ of the intermediate field needs to be unramified over $\mathcal{O}_K$, and the Frobenius elements are any elements satisfying the congruences.
