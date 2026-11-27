# Direct-product Goldreich-Levin amplification $(f^k)^{GL}$

For a Boolean function $f : \{0,1\}^n \to \{0,1\}$ and $k \ge 1$, the amplification $\mathrm{Amp}(f) = (f^k)^{GL} : \{0,1\}^{kn + k} \to \{0,1\}$ reads its input as $k$ blocks $x_1, \ldots, x_k \in \{0,1\}^n$ and a mask $r \in \{0,1\}^k$ and outputs $\bigoplus_{i=1}^k r_i f(x_i)$, the inner product over GF(2) of the direct product $(f(x_1),\ldots,f(x_k))$ with $r$. Each value of $\mathrm{Amp}(f)$ is computed from $k$ membership queries to $f$.

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets and Avi Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing, 2010.
- Oded Goldreich and Leonid A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing, 1989.
