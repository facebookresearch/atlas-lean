# Nisan-Wigderson reconstruction as a membership-query weak learner (one run)

Let $S_1, \ldots, S_m \subseteq [\ell]$ be an $(\ell, n, a)$-design with $m \ge 1$, let $\mathrm{NW}^f(z) = (f(z|_{S_1}), \ldots, f(z|_{S_m}))$ be the Nisan-Wigderson generator of $f : \{0,1\}^n \to \{0,1\}$, and let $D : \{0,1\}^m \to \{0,1\}$ be a deterministic test with $\Pr_z[D(\mathrm{NW}^f(z)) = 1] - \Pr_y[D(y) = 1] \ge \varepsilon$. The reconstruction, with its random choices (a hybrid index, fixed seed bits and random bits) as the seed, is a membership-query learner that queries $f$ at no more than $m2^a$ points determined by the seed and outputs a guess for $f$. On a uniformly random seed it outputs a hypothesis of error at most $\frac12 - \frac{\varepsilon}{2m}$ with probability at least $\frac{\varepsilon}{2m}$. Every hypothesis has De Morgan circuit size at most $\mathrm{size}(D) + m(2^a(2a+3) + 1) + 1$. In particular, a test accepting a $\delta$ fraction of all strings but no output of the generator gives, through its negation, a weak learner with advantage $\delta/(2m)$.

## Proof sketch

A hybrid argument turns the distinguishing advantage into a next-bit predictor with advantage $\varepsilon/m$ at a random position. Fixing the seed bits outside $S_i$, each earlier output bit depends on at most $a$ of the free bits, so its values are read from a table of $2^a$ queries to $f$; a random completion bit then predicts $f$, and averaging shows the guess has advantage $\varepsilon/(2m)$ with probability $\varepsilon/(2m)$. The tables become multiplexers of size $2^a(2a+3)$ added to the test.

## Depends on

- [Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)
- [Combinatorial designs for the Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/combinatorial-designs-for-the-nisanwigderson.md)
- [Randomized membership-query learner as a family of decision trees](../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)

## Proof depends on

- [Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Noam Nisan and Avi Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences 49(2), 1994.
