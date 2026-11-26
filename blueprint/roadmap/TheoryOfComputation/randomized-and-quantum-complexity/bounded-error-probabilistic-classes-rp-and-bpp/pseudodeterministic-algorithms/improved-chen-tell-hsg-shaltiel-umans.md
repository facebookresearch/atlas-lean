# Chen–Lu–Oliveira–Ren–Santhanam: Chen–Tell hitting sets with a Shaltiel–Umans core are printable in time poly(T)

Let $f\colon\{1^n\}\to\{0,1\}^n$ be computed by sufficiently uniform circuits of size $T$ and depth $d$, and let $M$ be an output length. There are a deterministic algorithm printing a set $H\subseteq\{0,1\}^M$ in time $\mathrm{poly}(T)$ and a probabilistic reconstruction algorithm such that for every $Q_M\subseteq\{0,1\}^M$ that is dense and decidable in time $\mathrm{poly}(M)$, either $H\cap Q_M\neq\emptyset$, or, given oracle access to $Q_M$, the reconstruction outputs $f(1^n)$ with high probability in time $\mathrm{poly}(d,n,M)$. Moreover $H$ itself is computable by uniform circuits of depth $d\cdot\log T+M^{O(1)}$, so the lemma can be applied again to the function that scans $H$.

## Proof sketch

Starting from the Chen–Tell layered-polynomial representation of the computation of $f$, the Nisan–Wigderson generator, which costs $2^{\Theta(\log^2T/\log M)}$, is replaced by a variant of the Shaltiel–Umans generator with polynomial construction time. That generator lacks the uniform learning reconstruction the framework needs; this is sidestepped by a further win-win analysis, and the circuit uniformity of the new generator is tracked so that it can be fed back as the next function $f$.

## Depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](../../../pseudorandomness-and-one-way-functions/instance-wise-hardness-versus-randomness/instance-wise-reconstruction-targeted-hsg.md)

## Proof depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](../../../pseudorandomness-and-one-way-functions/instance-wise-hardness-versus-randomness/instance-wise-reconstruction-targeted-hsg.md)

## Sources

- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
