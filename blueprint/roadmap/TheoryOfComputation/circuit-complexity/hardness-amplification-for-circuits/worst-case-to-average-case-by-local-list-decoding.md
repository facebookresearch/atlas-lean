# Worst-case to average-case hardness by local list decoding

Let $f$ be a Boolean function on $n=m\cdot b$ bits and let $\hat f$ be its *encoding*: the low-degree extension $p:\mathbb{F}^m\to\mathbb{F}$ of $f$ (viewed on $(\{0,1\}^b)^m$, of total degree at most $m(2^b-1)$, with $b=O(\log n)$ (so $2^b=\mathrm{poly}(n)$), over a field $\mathbb{F}$ of $2^w\ge\mathrm{poly}(m2^b/\varepsilon)$ elements) concatenated with the Hadamard code, $\hat f(y,r)=\langle \mathrm{bits}(p(y)),r\rangle$. If some circuit of size $S$ agrees with $\hat f$ on a $\tfrac12+\varepsilon$ fraction of inputs, then $f$ has a circuit of size $\mathrm{poly}(S, n, 1/\varepsilon)$. Consequently, if a language in $\mathsf{E}$ requires circuits of size $2^{\gamma n}$, then some language in $\mathsf{E}$ has average-case hardness $2^{\gamma' n}$ for a constant $\gamma'>0$.

## Proof sketch

Goldreich–Levin decoding turns a predictor for $\hat f$ into a list of candidates for $p$ that are correct on a noticeable fraction of points; Reed–Muller local list decoding (interpolation along random lines or curves) followed by self-correction recovers $p$, hence $f$, everywhere, with nonuniform advice selecting the right list element.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)
- [Dimension and distance of binary Reed–Muller codes](../../../InformationTheory/error-correcting-codes/reed-muller-codes-dimension-and-distance.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Goldreich-Levin: hardcore predicate from one-way permutations](../../pseudorandomness-and-one-way-functions/goldreich-levin-theorem/goldreich-levin.md)

## Sources

- Madhu Sudan, Luca Trevisan, Salil Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences, 2001.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
