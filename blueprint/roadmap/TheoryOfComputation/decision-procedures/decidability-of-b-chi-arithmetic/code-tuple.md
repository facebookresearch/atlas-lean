# Gödel number of a tuple of codes

The code of a finite tuple $(x_0, \dots, x_{l-1})$ of natural numbers is defined by recursion on its length $l$:

$$\langle\, \rangle = 0, \qquad \langle x_0, \dots, x_l \rangle = \pi\big(\langle x_0, \dots, x_{l-1} \rangle, x_l\big).$$

Here $\pi$ is the pairing function on $\mathbb{N}$ given by $\pi(a, b) = b^2 + a$ if $a < b$ and $\pi(a, b) = a^2 + a + b$ otherwise, a bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$. The coding does not depend on any formula language: the same function codes tuples for Büchi arithmetic, for first-order logic in Church's theorem and for Presburger arithmetic.
