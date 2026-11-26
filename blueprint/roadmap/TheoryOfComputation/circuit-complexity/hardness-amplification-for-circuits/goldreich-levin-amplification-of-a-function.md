# The Goldreich–Levin amplification of a Boolean function

For $f:\{0,1\}^n\to\{0,1\}$ and $k\ge1$, let $f^{k}:(\{0,1\}^n)^k\to\{0,1\}^k$ be the direct product and define the *Goldreich–Levin amplification*

$$
\mathrm{Amp}_k(f)(y_1,\dots,y_k,r)=\langle f^k(y_1,\dots,y_k),r\rangle\bmod 2,\qquad r\in\{0,1\}^k .
$$

If $f$ has a circuit of size $s$ then $\mathrm{Amp}_k(f)$ has a circuit of size $ks+O(k)$; conversely a circuit predicting $\mathrm{Amp}_k(f)$ with noticeable advantage yields, via Goldreich–Levin decoding and direct-product decoding, a circuit computing $f$ on most inputs.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)
- [Goldreich-Levin: hardcore predicate from one-way permutations](../../pseudorandomness-and-one-way-functions/goldreich-levin-theorem/goldreich-levin.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), 2016.
- Oded Goldreich, Leonid A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
