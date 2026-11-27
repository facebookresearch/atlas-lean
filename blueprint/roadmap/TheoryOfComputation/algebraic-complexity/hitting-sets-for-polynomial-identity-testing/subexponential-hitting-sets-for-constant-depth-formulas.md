# Subexponential hitting sets for constant-depth formulas from the LST lower bound

Over a field of characteristic zero, for every product-depth $\Delta$, every exponent $c$ and every $\varepsilon>0$, for all large $n$ there is an explicit set of at most $2^{n^{\varepsilon}}$ points of $F^n$ that hits every nonzero polynomial computed by an unbounded fan-in circuit of product-depth at most $\Delta$ with at most $n^c$ nodes, in particular by every such formula.

## Proof sketch

Use the Kabanets–Impagliazzo generator with the hard polynomial $\mathrm{IMM}_{\nu,\delta}$ on $m=n^{\Theta(\varepsilon)}$ variables, of slowly growing degree $\delta$, and a suitable design. The Limaye–Srinivasan–Tavenas lower bound shows that this polynomial has no polynomial-size circuits of product-depth $\Delta+O(1)$, which is the hardness the generator needs; the resulting hitting set has size $\bigl(n^{O(c\Delta+1)}\bigr)^{O(n^{\varepsilon/2})}\le2^{n^{\varepsilon}}$ for large $n$.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](../constant-depth-algebraic-circuits/unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Kabanets–Impagliazzo: hardness gives hitting sets for constant-depth formulas](hardness-to-hitting-sets-for-constant-depth-formulas.md)
- [Constant-depth algebraic circuits for IMM need superpolynomial size](../constant-depth-algebraic-circuits/lst-constant-depth-circuit-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021, Corollary 6 and Lemma 18 (deterministic identity testing in time $(s^{\Delta+1}n)^{O(n^{\mu})}$ for every $\mu>0$).
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai, Varun Ramanathan, Ramprasad Saptharishi, Shubhangi Saraf, "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026; arXiv:2506.23214, Theorem 6.1.
