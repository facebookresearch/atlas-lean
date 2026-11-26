# The Aaronson-Ambainis conjecture on influential variables of bounded polynomials

The *Aaronson-Ambainis conjecture* asserts that there is a polynomial $P$ such that every multilinear polynomial $p : \{\pm1\}^n \to [0, 1]$ of degree $d$ has a variable $i$ with influence

$$
\mathrm{Inf}_i(p) := \mathbb{E}_x\Big[\big(p(x) - p(x^{\oplus i})\big)^2\Big] / 4 \ \ge\ P\!\left(\frac{\mathrm{Var}[p]}{d}\right).
$$

## Sources

- Scott Aaronson, Andris Ambainis, "The need for structure in quantum speedups", Theory of Computing 10 (2014); arXiv:0911.0996.
