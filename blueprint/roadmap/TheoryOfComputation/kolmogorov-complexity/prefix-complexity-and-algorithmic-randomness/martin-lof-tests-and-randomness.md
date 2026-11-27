# Martin-Löf tests and Martin-Löf randomness

A *Martin-Löf test* is a uniformly computably enumerable sequence $(V_k)_{k \ge 1}$ of sets of binary strings such that the open set $[V_k]$ of infinite sequences extending some string of $V_k$ has fair-coin measure at most $2^{-k}$. An infinite binary sequence $\omega$ *passes* the test if $\omega \notin \bigcap_k [V_k]$, and it is *Martin-Löf random* if it passes every Martin-Löf test. There is a *universal* test whose null set contains those of all tests, so randomness means passing the universal test. A *Solovay test* is a computable enumeration of strings $w_i$ with $\sum_i 2^{-|w_i|} < \infty$; $\omega$ passes it if it extends only finitely many $w_i$.

## Sources

- P. Martin-Löf, "The Definition of Random Sequences", Information and Control 9(6), 602–619, 1966.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
