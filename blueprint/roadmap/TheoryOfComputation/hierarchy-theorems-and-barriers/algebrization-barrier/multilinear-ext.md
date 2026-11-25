# Multilinear extension of a Boolean function

Identify the booleans true and false with $1$
and $0$. Let $F$ be a field, $n$ a natural number and $f : \{0,1\}^n \to \{0,1\}$.
The multilinear extension of $f$ at a point $x = (x_0, \dots, x_{n-1}) \in F^n$ is

$$\sum_{a \in \{0,1\}^n} f(a) \prod_{i=0}^{n-1} \ell_{a_i}(x_i),$$

where $f(a) \in \{0, 1\}$ is read in $F$, $\ell_1(t) = t$ and $\ell_0(t) = 1 - t$.
