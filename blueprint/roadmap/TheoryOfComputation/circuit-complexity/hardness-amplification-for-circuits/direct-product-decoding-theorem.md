# Direct-product decoding

There is a randomized decoder with the following property. Let $f:U\to V$ and let $C':U^k\to V^k$ agree with the direct product $f^k$ on at least a $\delta$ fraction of $k$-tuples, where $\delta\ge e^{-ck}$ for a small constant $c$. Then, with probability $\mathrm{poly}(\delta)$ over its random seed, the decoder (which queries $C'$ on tuples built from its input) outputs a hypothesis $h:U\to V$ agreeing with $f$ on at least a $1-\varepsilon$ fraction of $U$, for $\varepsilon=O(\log(1/\delta)/k)$. The decoder is computed by circuits of size polynomial in $k$, $1/\delta$ and the size of $C'$.

## Proof sketch

Pick a random tuple $b_0$ on which $C'$ is (hopefully) correct and a random subset $P$ of positions; on input $x$, repeatedly embed $x$ into fresh tuples that agree with $b_0$ on $P$ and accept the answer of $C'$ at $x$ when $C'$ is consistent with $b_0$ on $P$. A sampling argument shows consistent tuples are mostly correct.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Sources

- Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets, Avi Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing, 2010.
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), 2016.
