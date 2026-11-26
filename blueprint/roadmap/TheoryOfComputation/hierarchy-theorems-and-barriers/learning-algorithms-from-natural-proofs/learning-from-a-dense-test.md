# Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator

Let $e, g, h \ge 0$ be precision exponents, $k = k(e,g) = 2^{e + \lceil\log_2(6g + 3e + 36)\rceil + 9}$, and let $D$ be a Boolean function on strings of $2^\ell$ bits such that

1. (density) $D$ accepts at least a $2^{\ell + 1 - g}$ fraction of all $2^{2^\ell}$ strings;
2. (usefulness) for every $f \in C$, $D$ rejects every output of the Nisan-Wigderson generator of $\mathrm{Amp}(f) = (f^k)^{GL}$ built from a fixed polynomial design on $kn + k$ bits with output length $2^\ell$.

Then a learner composed of the Nisan-Wigderson reconstruction on $\neg D$, the amplification reconstruction and one outer best-of selection learns $C$ with membership queries under the uniform distribution with error $2^{-e}$ and confidence $1 - 2^{-h}$, using at most $(h+1)\,2^{2\ell + 10g + 6e + 59}$ queries.

## Proof sketch

The negated test distinguishes the generator of $\mathrm{Amp}(f)$ from uniform with advantage at least $2^{\ell+1-g}$, so one run of the Nisan-Wigderson reconstruction is a weak learner for $\mathrm{Amp}(f)$ with advantage $2^{\ell+1-g}/(2 \cdot 2^\ell) = 2^{-g}$, the distinguishing advantage divided by twice the output length. The amplification reconstruction converts it into a learner for $f$ with error $2^{-(e+1)}$ that succeeds with probability $\gamma\delta_0^2/8$, and a single best-of selection over enough runs raises the confidence to $1 - 2^{-h}$. The parameter inequalities are checked for the explicit choices of $k$, mask count and decoder sizes.

## Depends on

- [Direct-product Goldreich-Levin amplification $(f^k)^{GL}$](direct-product-goldreich-levin-amplification.md)
- [Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)

## Proof depends on

- [Nisan-Wigderson reconstruction as a membership-query weak learner (one run)](nisan-wigderson-reconstruction-weak-learner.md)
- [Reconstruction for $(f^k)^{GL}$: a learner for the amplified class yields a learner for the class](amplification-reconstruction.md)
- [Best-of-k selection boosts the confidence of a membership-query learner](../../circuit-complexity/learning-under-the-uniform-distribution/best-of-k-confidence-boosting.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
