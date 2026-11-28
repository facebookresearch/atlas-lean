# Almost-linear lower bounds for MCSP are equivalent to the non-existence of natural proofs

Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam show that almost-linear circuit lower bounds for approximate or worst-case gap MCSP are equivalent to hardness of learning polynomial-size circuits, to the non-existence of natural properties against them, and to non-uniform pseudorandom functions.

Let $N = 2^n$ and let $\mathsf{Circuit}[s]$ denote fan-in-two circuits with at most $s$ gates. For $s(n) \le t(n)$ and $0 \le \sigma, \varepsilon < 1/2$, write $\mathrm{MCSP}[(s, \sigma), (t, \varepsilon)]$ for the promise problem whose yes-instances are truth tables $y \in \{0,1\}^N$ such that some circuit of size $s(n)$ $(1-\sigma)$-approximates $f_y$, and whose no-instances are those for which no circuit of size $t(n)$ $(1-\varepsilon)$-approximates $f_y$; $\mathrm{MCSP}[s, t] = \mathrm{MCSP}[(s,0),(t,0)]$. The following statements are equivalent.

1. There are $c \ge 1$, $0 < \gamma < 1$ and $\varepsilon > 0$ with $\mathrm{MCSP}[(n^c, 0), (2^{n^\gamma}, n^{-c})] \notin \mathsf{Circuit}[N^{1+\varepsilon}]$.
2. There are $c \ge 1$ and $\varepsilon > 0$ with $\mathrm{MCSP}[n^c, 2^n/n^c] \notin \mathsf{Circuit}[N^{1+\varepsilon}]$.
3. There are $\ell \ge 1$ and $0 < \gamma < 1$ such that $\mathsf{Circuit}[n^\ell]$ cannot be learned up to error $O(1/n^\ell)$ under the uniform distribution by circuits of size $2^{O(n^\gamma)}$ using non-adaptive membership queries.
4. For some $d \ge 1$ there is no $\mathsf{Circuit}[\mathrm{poly}(N)]$-natural property useful against $\mathsf{Circuit}[n^d]$.
5. For every constant $a \ge 0$ there are $d \ge 1$, families $\mathcal{F}_n$ of $n$-bit Boolean functions in $\mathsf{Circuit}[n^d]$ and distributions $\mathcal{D}_n$ on $\mathcal{F}_n$ such that for infinitely many $n$, $(\mathcal{F}_n, \mathcal{D}_n)$ is a pseudorandom function family that $N^{-\omega(1)}$-fools oracle circuits of size $2^{a n}$.

## Proof sketch

The new direction is hardness magnification for learnability: an almost-linear lower bound for approximate MCSP (or, following Hirahara, for worst-case gap MCSP) already rules out sub-exponential non-adaptive learners for polynomial-size circuits, because such a learner yields a small circuit that tests whether the input truth table is consistent with a learned hypothesis. Learning versus natural properties is the Carmosino–Impagliazzo–Kabanets–Kolokolova correspondence, and learning versus pseudorandom functions is the Oliveira–Santhanam correspondence. In particular every $\mathsf{P/poly}$-natural property against $\mathsf{P/poly}$ can be turned into an almost-linear-size algorithm for one of these MCSP variants, so magnification for approximate MCSP is provably non-naturalizing.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Approximate MCSP](../../../circuit-complexity/hardness-magnification/approximate-mcsp.md)
- [Natural property](../../natural-proofs-barrier/natural-property.md)
- [Randomized membership-query learner as a family of decision trees](../../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)

## Proof depends on

- [Learning size-s circuits from a dense property of functions with large circuit complexity](../../learning-algorithms-from-natural-proofs/learning-from-a-property-useful-against-circuits.md)
- [Oliveira-Santhanam: learners for SIZE(s) yield P/poly-natural properties useful against SIZE(s)](../../learning-versus-pseudorandomness/learners-yield-natural-properties.md)
- [A membership-query learner for a keyed family distinguishes it from random functions](../../learning-versus-pseudorandomness/learners-distinguish-pseudorandom-functions.md)

## Sources

- Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Jan Pich, Ninad Rajgopal and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", *Journal of the ACM* 69(4), 2022 (conference version ITCS 2020), DOI 10.1145/3538391, arXiv:1911.08297v1 (Theorem 1, Equivalences for Hardness Magnification, Section 1.2; proof in Section 4; Definition 6 for the MCSP variants).
