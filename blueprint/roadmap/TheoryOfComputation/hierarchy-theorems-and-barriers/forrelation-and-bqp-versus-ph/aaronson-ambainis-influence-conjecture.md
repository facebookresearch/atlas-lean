# The Aaronson-Ambainis conjecture on influential variables of bounded polynomials

The *Aaronson-Ambainis conjecture* asserts that there are universal constants $c, C > 0$ such that for every $d \ge 1$, every multilinear polynomial $p : \{\pm1\}^n \to [0, 1]$ of degree $d$ has a variable $i$ with influence

$$
\mathrm{Inf}_i(p) := \mathbb{E}_x\Big[\big(p(x) - p(x^{\oplus i})\big)^2\Big] / 4 \ \ge\ c\left(\frac{\mathrm{Var}[p]}{d}\right)^{C}.
$$

## Sources

- Scott Aaronson, Andris Ambainis, "The need for structure in quantum speedups", Theory of Computing 10 (2014); arXiv:0911.0996.
