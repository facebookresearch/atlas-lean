# Efficient coding theorem for rKt

If a uniform sampler running in time $T(m)$ outputs $x$ with probability at least $\delta$, then $\mathrm{rKt}(x)=O(\log(1/\delta)+\log T(m)+\log m)$, and such a probabilistic representation can be computed from $x$ in polynomial time. This is the first unconditional coding theorem in time-bounded Kolmogorov complexity.

Suppose a randomized algorithm $A$, on input $1^m$, runs in time $T(m)$ and outputs a string $x\in\{0,1\}^*$ of length $n\le T(m)$ with probability at least $\delta>0$. Then

$$
\mathrm{rKt}(x)=O\bigl(\log(1/\delta)+\log T(m)+\log m\bigr),
$$

where the constant in $O(\cdot)$ depends on $|A|$ and on nothing else. Moreover, given $x$, $m$, the code of $A$ and $\delta$, one can compute with probability at least $0.99$ an rKt encoding of $x$ of at most this complexity, in randomized time $\mathrm{poly}(|A|,\log m,|x|,\log(1/\delta))$.

By Shannon's source coding theorem the expected encoding length is optimal up to a constant factor. The encoder runs in polynomial time regardless of the running time of the sampler, and needs only a lower bound on the probability of $x$.

## Expansion

Assume $\delta=2^{-\ell}$. The decoder, given $m$ and $\delta$, runs $A(1^m)$ about $64(1/\delta)\log(1/\delta)$ times; with probability at least $5/6$ every string of probability at least $\delta$ (at most $1/\delta$ of them, $x$ among them) appears at least $32\log(1/\delta)$ times, while few other strings do. A string isolation lemma, built from an explicit error-correcting code and a random walk on an explicit expander, gives a hash function with seed of length $O(\log(n/\delta))$ and output of length $O(\log(1/\delta))$ that is injective on this candidate set; storing the seed and the hash value of $x$ identifies $x$ with high probability. The decoder runs in time $\mathrm{poly}(1/\delta,T(m))$, contributing $O(\log(1/\delta)+\log T(m))$ through the $\log t$ term.

## Depends on

- [Randomized Levin complexity rKt and the problem MrKtP](randomized-levin-complexity-rkt.md)

## Proof depends on

None.

## Sources

- Zhenjian Lu and Igor C. Oliveira, "An Efficient Coding Theorem via Probabilistic Representations and Its Applications", *48th International Colloquium on Automata, Languages, and Programming (ICALP 2021)*, LIPIcs 198, 2021, [doi:10.4230/LIPIcs.ICALP.2021.94](https://doi.org/10.4230/LIPIcs.ICALP.2021.94) (Theorem 1, Lemma 15, Theorem 16 and its proof).
