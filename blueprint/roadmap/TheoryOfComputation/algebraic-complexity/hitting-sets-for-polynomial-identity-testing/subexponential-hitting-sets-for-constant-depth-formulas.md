# Subexponential hitting sets for constant-depth formulas from the LST lower bound

Over a field of characteristic zero, for every product-depth $\Delta$, every exponent $c$ and every $\varepsilon>0$, for all large $n$ there is an explicit set of at most $2^{n^{\varepsilon}}$ points of $F^n$ that hits every nonzero polynomial computed by an unbounded fan-in formula of product-depth at most $\Delta$ with at most $n^c$ nodes, and (at a larger exponent) by a circuit of product-depth at most $\Delta$ with at most $n^c$ gates.

## Proof sketch

Use the Kabanets–Impagliazzo generator with the IMM-based hard polynomial of Limaye–Srinivasan–Tavenas on $m=n^{\Theta(\varepsilon)}$ variables and a design with small intersections; the LST lower bound supplies the required hardness against product-depth $\Delta+2$ formulas.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](../constant-depth-algebraic-circuits/unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Kabanets–Impagliazzo: hardness gives hitting sets for constant-depth formulas](hardness-to-hitting-sets-for-constant-depth-formulas.md)
- [Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field](../constant-depth-algebraic-circuits/lst-constant-depth-formula-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai et al., "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026.
