# Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator

Let $0 < \varepsilon < 1$ and $L \le 2^n$ with $\log L$ an integer. For $f : \{0,1\}^n \to \{0,1\}$ let $\mathrm{Amp}(f) = (f^k)^{GL}$ be the amplification of the reconstruction for $(f^k)^{GL}$ with error $\varepsilon$ and advantage $\gamma = 1/L$, a function on $n' = kn + k$ bits, and let $G^{\mathrm{Amp}(f)} : \{0,1\}^{m} \to \{0,1\}^{L}$, $G^{\mathrm{Amp}(f)}(z) = \mathrm{Amp}(f)(z|_{S_1}) \cdots \mathrm{Amp}(f)(z|_{S_L})$, be the Nisan-Wigderson generator on $\mathrm{Amp}(f)$ with seed length $m = O((n')^2)$ and a design $S_1, \ldots, S_L \subseteq [m]$ with $|S_i| = n'$ and $|S_i \cap S_j| \le \log L$ for $i \ne j$. Let $D$ be a circuit on $L$-bit strings such that

1. (density) $D$ accepts at least a $1/5$ fraction of all $L$-bit strings;
2. (usefulness) for every $f \in C$, $D$ rejects every output $G^{\mathrm{Amp}(f)}(z)$.

Then there is a probabilistic algorithm that, given $D$, a confidence parameter $\alpha$ and membership queries to any $f \in C$, outputs with probability at least $1 - \alpha$ a circuit computing $f$ on all but an $\varepsilon$ fraction of inputs, in time $\mathrm{poly}(n, 1/\varepsilon, L)$. It runs the Nisan-Wigderson reconstruction on $\neg D$, repeated $\mathrm{poly}(L)$ times with the hypothesis of largest estimated agreement selected, answering each query to $\mathrm{Amp}(f)$ with $k$ queries to $f$, and then the reconstruction for $(f^k)^{GL}$.

## Proof sketch

By the two conditions $\neg D$ accepts every generator output and at most a $4/5$ fraction of all strings, so it distinguishes $G^{\mathrm{Amp}(f)}$ from uniform with advantage $1/5$. The Nisan-Wigderson reconstruction, boosted by repetition and selection, yields in time $\mathrm{poly}(L)$ a circuit computing $\mathrm{Amp}(f)$ on a $\frac12 + \frac1L$ fraction of inputs. The reconstruction for $(f^k)^{GL}$ with $\gamma = 1/L$ turns it into a circuit for $f$ with error $\varepsilon$ in time $\mathrm{poly}(n, 1/\varepsilon, L)$.

The sources state the bounds only up to polynomial factors. One explicit instantiation, with precision exponents $e, g, h \ge 0$, $L = 2^\ell$, $k = 2^{e + \lceil\log_2(6g + 3e + 36)\rceil + 9}$, a test of density at least $2^{\ell + 1 - g}$, error $2^{-e}$ and confidence $1 - 2^{-h}$, uses the one-run reconstruction (advantage $2^{\ell+1-g}/(2 \cdot 2^\ell) = 2^{-g}$), the explicit amplification reconstruction and one outer best-of selection, and makes at most $(h+1)\,2^{2\ell + 10g + 6e + 59}$ queries.

## Depends on

- [Direct-product Goldreich-Levin amplification $(f^k)^{GL}$](direct-product-goldreich-levin-amplification.md)
- [Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)
- [Nisan-Wigderson reconstruction as a membership-query weak learner (one run)](nisan-wigderson-reconstruction-weak-learner.md)
- [Reconstruction for $(f^k)^{GL}$: a learner for the amplified class yields a learner for the class](amplification-reconstruction.md)
- [Best-of-k selection boosts the confidence of a membership-query learner](../../circuit-complexity/learning-under-the-uniform-distribution/best-of-k-confidence-boosting.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016, Theorem 2.11 with the reconstruction sketch after it, Definitions 2.8-2.10, Theorem 3.2 and its proof, Theorem 3.3, and the proof of Theorem 5.1.
