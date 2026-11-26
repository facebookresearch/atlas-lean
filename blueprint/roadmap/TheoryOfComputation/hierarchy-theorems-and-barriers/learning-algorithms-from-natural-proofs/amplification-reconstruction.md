# Reconstruction for $(f^k)^{GL}$: a learner for the amplified class yields a learner for the class

Let $A$ be a membership-query learner for $\{\mathrm{Amp}(f) : f \in C\}$, $\mathrm{Amp}(f) = (f^k)^{GL}$, with error $\frac12 - \gamma$ ($\gamma > 0$) and success probability $p$. Put $\delta_0 = \gamma/2^{K+3}$ and suppose $k \le 2(\gamma/2)^2(2^K - 1)$, $2s \le k$, $s \ge \frac{64}{\varepsilon}\ln\frac{512}{\varepsilon\delta_0^2}$ and $m \ge \frac{16}{\delta_0}\ln\frac8\varepsilon$ for some $0 < \varepsilon \le 1$. The black-box reduction that answers each query of $A$ with $k$ queries to $f$, decodes $A$'s hypothesis by Goldreich-Levin list decoding over $K$ masks, and then applies a direct-product decoder with parameters $s, m$, learns $C$ with error $\varepsilon$ and success probability $p\,\delta_0^2/8$, using $k$ queries to $f$ for each query of $A$ plus the decoder's queries.

## Proof sketch

A hypothesis with advantage $\gamma$ for $(f^k)^{GL}$ yields, by Goldreich-Levin decoding over the $2^K - 1$ nonzero masks, a candidate that computes $f^k$ correctly on a $\delta_0$ fraction of $k$-tuples with noticeable probability. The uniform direct-product decoder of Impagliazzo-Jaiswal-Kabanets-Wigderson, which fixes $s$ coordinates on a random restriction and votes with $m$ trials, turns such an agreement into a circuit for $f$ with error $\varepsilon$ with probability $\delta_0^2/8$. The reduction lemma multiplies the success probabilities.

## Depends on

- [Direct-product Goldreich-Levin amplification $(f^k)^{GL}$](direct-product-goldreich-levin-amplification.md)
- [Randomized membership-query learner as a family of decision trees](../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)

## Proof depends on

- [Black-box reductions between membership-query learners multiply success probabilities](../../circuit-complexity/learning-under-the-uniform-distribution/black-box-reduction-between-query-learners.md)
- [Goldreich-Levin: hardcore predicate from one-way permutations](../../pseudorandomness-and-one-way-functions/goldreich-levin-theorem/goldreich-levin.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets and Avi Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing, 2010.
- Oded Goldreich and Leonid A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing, 1989.
