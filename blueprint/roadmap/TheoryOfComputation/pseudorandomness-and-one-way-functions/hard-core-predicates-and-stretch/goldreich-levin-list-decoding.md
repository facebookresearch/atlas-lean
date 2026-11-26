# Goldreich–Levin list decoding of the Hadamard code with oracle access

There is a probabilistic oracle algorithm $\mathrm{GL}$ that, on input $n$ and $\varepsilon = 1/m$ (given in unary), runs in time polynomial in $n$ and $m$ and, for every oracle $B : \{0,1\}^n \to \{0,1\}$ (no efficiency assumption), outputs with probability at least $1/2$ a list $L$ (whose size is polynomial in $n$ and $m$, by the running time) such that every $x \in \{0,1\}^n$ with

$$\Pr_{r \leftarrow \{0,1\}^n}\bigl[B(r) = \langle x, r \rangle\bigr] \ge \frac{1}{2} + \varepsilon$$

belongs to $L$, simultaneously for all such $x$ (Goldreich 2008, Theorem 7.8).

## Proof sketch

Guess the values $\langle x, s_j\rangle$ on $O(\log(nm^2))$ random seeds and use all XOR combinations of the seeds as pairwise independent query points $r$. For each coordinate $i$, a majority vote of $B(r \oplus e_i) \oplus \langle x, r\rangle$ over these points recovers $x_i$ with high probability by Chebyshev's inequality; enumerating all guesses produces the list.

## Depends on

- [Inner product modulo 2](../goldreich-levin-theorem/xor-dot.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [List-decodable code](../../../InformationTheory/error-correcting-codes/list-decoding/is-list-decodable.md)

## Sources

- O. Goldreich and L. A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
