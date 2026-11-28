# Reconstruction for $(f^k)^{GL}$: a learner for the amplified class yields a learner for the class

Let $c$ be the constant of the uniform direct-product reconstruction: for every $k$ and $0 < \varepsilon, \delta < 1$ with $\delta > e^{-k/c}$ there is a probabilistic algorithm that, given any circuit computing the direct product $f^k$ on at least a $\delta$ fraction of $k$-tuples, outputs with probability $\Omega(\delta)$ a circuit computing $f$ on all but an $\varepsilon$ fraction of inputs. For $0 < \varepsilon, \gamma < 1$ put $k = \lceil 3c \cdot \frac{1}{\varepsilon}\ln\frac{1}{\gamma}\rceil + 1$ and $\mathrm{Amp}(f) = (f^k)^{GL}$ over GF(2), a function on $kn + k$ bits. Then there is a probabilistic algorithm with membership queries to $f : \{0,1\}^n \to \{0,1\}$ that, given a confidence parameter $\alpha$ and any circuit computing $\mathrm{Amp}(f)$ on at least a $\frac12 + \gamma$ fraction of inputs, outputs with probability at least $1 - \alpha$ a circuit computing $f$ on all but an $\varepsilon$ fraction of inputs, in time $\mathrm{poly}(n, 1/\varepsilon, 1/\gamma)$.

Consequently, if $A$ is a membership-query learner for $\{\mathrm{Amp}(f) : f \in C\}$ with error $\frac12 - \gamma$, the black-box reduction that runs $A$, answers each query of $A$ with $k$ queries to $f$, and applies this algorithm to $A$'s hypothesis outputs, whenever that hypothesis has error at most $\frac12 - \gamma$, a hypothesis for $f$ of error at most $\varepsilon$ with probability at least $1 - \alpha$ over its own randomness.

## Proof sketch

For a circuit $C'$ computing $\mathrm{Amp}(f)$ on a $\frac12 + \gamma$ fraction of inputs, at least a $\gamma/2$ fraction of tuples $x$ have $C'(x, \cdot)$ agreeing with $r \mapsto \langle f^k(x), r\rangle$ on a $\frac12 + \frac\gamma2$ fraction of masks $r$. Goldreich-Levin list decoding (list size $O(1/\gamma^2)$, success probability $1/2$) followed by a uniformly random choice from the list computes $f^k$ on an $\Omega(\gamma^3)$ fraction of tuples. The choice of $k$ gives $\Omega(\gamma^3) > e^{-k/(3c)}$, so the direct-product reconstruction applies with $\delta = \Omega(\gamma^3)$; repeating it and keeping the output of largest estimated agreement with $f$ raises its success probability to $1 - \alpha$. Each value of $\mathrm{Amp}(f)$ costs $k$ queries to $f$. Composing with $A$, the output is good with probability at least $p(1 - \alpha)$ when $A$ succeeds with probability $p$.

The sources leave the constants unspecified. One explicit instantiation, with $K$ Goldreich-Levin masks, $\delta_0 = \gamma/2^{K+3}$, $k \le 2(\gamma/2)^2(2^K - 1)$ and a direct-product decoder that fixes $s$ coordinates with $2s \le k$ and votes with $m$ trials, where $s \ge \frac{64}{\varepsilon}\ln\frac{512}{\varepsilon\delta_0^2}$ and $m \ge \frac{16}{\delta_0}\ln\frac8\varepsilon$, succeeds with probability $\delta_0^2/8$ per run, so the composed learner has success probability $p\,\delta_0^2/8$.

## Depends on

- [Direct-product Goldreich-Levin amplification $(f^k)^{GL}$](direct-product-goldreich-levin-amplification.md)
- [Randomized membership-query learner as a family of decision trees](../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)
- [Black-box reductions between membership-query learners multiply success probabilities](../../circuit-complexity/learning-under-the-uniform-distribution/black-box-reduction-between-query-learners.md)

## Proof depends on

- [Goldreich-Levin: hardcore predicate from one-way permutations](../../pseudorandomness-and-one-way-functions/goldreich-levin-theorem/goldreich-levin.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016, Section 4, Theorem 4.1, Theorem 4.2, Theorem 4.3 and its proof (Claim 4.4), with Definitions 2.2 and 3.4.
- Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets and Avi Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing, 2010.
- Oded Goldreich and Leonid A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing, 1989.
