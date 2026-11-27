# Quantum LDPC code families and asymptotically good quantum codes

A family of CSS codes $[[n_i, k_i, d_i]]$ with $n_i \to \infty$ is *LDPC* (low-density parity-check) of weight $w$ if every row and every column of $H_X$ and $H_Z$ has at most $w$ nonzero entries, with $w$ independent of $i$; equivalently each check acts on at most $w$ qubits and each qubit is involved in at most $w$ checks. The family is *asymptotically good* if $k_i \ge \alpha n_i$ and $d_i \ge \beta n_i$ for constants $\alpha, \beta > 0$. By the quantum Singleton bound, $k \le n - 2(d - 1)$ for every code.

## Depends on

- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)
- [Regular low-density parity-check matrix](../../../InformationTheory/error-correcting-codes/low-density-parity-check-codes/is-regular.md)
- [The quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654.
- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566.
