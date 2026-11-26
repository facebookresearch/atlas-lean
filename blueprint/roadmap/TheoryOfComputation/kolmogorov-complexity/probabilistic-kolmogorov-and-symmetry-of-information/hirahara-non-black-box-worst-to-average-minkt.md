# Hirahara: errorless average-case easiness of MINKT yields worst-case additive Õ(√k) approximation of K^t

Recall that MINKT asks, given $(x,1^t,1^s)$, whether $K^t(x)\le s$. If the average-case version of MINKT (uniformly random $x$) admits an errorless heuristic polynomial-time algorithm (which on each input either answers correctly or outputs a failure symbol, and fails on a small fraction of inputs), then there is a zero-error randomized polynomial-time algorithm that, on every input $(x,1^t)$, approximates $k=K^t(x)$ within an additive error $\widetilde{O}(\sqrt{k})$. Similarly, for truth tables of length $2^n$, approximating the circuit complexity within a factor $2^{(1-\varepsilon)n}$ is in $\mathsf{BPP}$ for some constant $\varepsilon>0$ if and only if its average-case version is easy. The approximation problem is at least as hard as avoiding any polynomial-time computable hitting set generator that extends a seed of length $n$ by $\widetilde{\omega}(\sqrt{n})$ bits, and in particular is Random-3SAT-hard, so it is believed to lie outside $\mathsf{coNP}$ and the reduction is necessarily non-black-box.

## Proof sketch

Given $x$ with $K^t(x)=k$, encode $x$ by an error-correcting code and feed it to the direct-product generator; strings in the image of this generator have time-bounded complexity about $k$ plus seed length, whereas uniformly random strings are incompressible. An errorless heuristic for average-case MINKT therefore distinguishes the generator's outputs from random, and the reconstruction property of the direct-product generator (via a list-decodable code) converts such a distinguisher, which is efficient, into a short description, certifying an upper bound on $K^t(x)$ up to $\widetilde{O}(\sqrt k)$. The argument uses the efficiency of the oracle, which is why it escapes the Bogdanov–Trevisan barrier against black-box reductions.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Sandwich bounds: K(x) − O(log t) ≤ pK^t(x) ≤ rK^t(x), K^t(x) up to constants and time overhead](pkt-sandwich-between-kolmogorov-and-time-bounded.md)
- [Heuristica](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/heuristica.md)
- [Few strings have small complexity](../incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Pseudorandom generators against circuits](../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- Shuichi Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS (2018), ECCC TR18-138.
