# Gödel numbers of Büchi terms

Let $n \in \mathbb{N}$. The Gödel number of a term of Büchi arithmetic with no free variables and bound variables $x_0, \dots, x_{n-1}$ in scope is defined by recursion on the term:

$$\ulcorner x_i \urcorner = \pi(1, i), \qquad \ulcorner f(t_1, \dots, t_l) \urcorner = \pi\big(2, \pi(\ulcorner f \urcorner, \langle \ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner \rangle)\big),$$

where $\ulcorner 0 \urcorner = 0$, $\ulcorner S \urcorner = 1$, $\ulcorner + \urcorner = 2$ number the function symbols and $\langle \cdot \rangle$ is the tuple code built by iterated pairing, $\langle\,\rangle = 0$ and $\langle x_0, \dots, x_l \rangle = \pi(\langle x_0, \dots, x_{l-1} \rangle, x_l)$. Here $\pi$ is the pairing function on $\mathbb{N}$ given by $\pi(a, b) = b^2 + a$ if $a < b$ and $\pi(a, b) = a^2 + a + b$ otherwise, a bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$.
