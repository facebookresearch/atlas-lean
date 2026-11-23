# Intermediate length bound of the composite machine

Let $h_1$ be a polynomial-time multi-stack computation of $f : \alpha \to \beta$ with polynomial
time bound $p_1 \in \mathbb{N}[X]$, and let $c$ be the push bound of the machine of $h_1$. The
intermediate length bound is the polynomial $X + c\,p_1 \in \mathbb{N}[X]$.

Evaluated at the length $n$ of an input, its value $n + c\,p_1(n)$ bounds the length of the
intermediate string that the machine of $h_1$ writes for the composite machine.
