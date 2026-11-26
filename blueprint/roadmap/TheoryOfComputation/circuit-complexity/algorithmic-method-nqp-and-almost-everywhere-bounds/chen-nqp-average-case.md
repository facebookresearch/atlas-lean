# Chen: NQP is average-case hard for ACC0

For every constant $c$, depth $d$ and modulus $m$ there is a language $L \in \mathrm{NQP}$ such that for infinitely many $n$, every polynomial-size $\mathrm{AC}^0[m]$ circuit of depth $d$ agrees with $L$ on at most a $\frac{1}{2} + \frac{1}{\log^{c} n}$ fraction of inputs of length $n$. Chen-Ren strengthen this: for every constant $a$, $\mathrm{NQP}$ cannot be $(\frac{1}{2} + 2^{-\log^{a} n})$-approximated by $\mathrm{ACC}^0 \circ \mathrm{THR}$ circuits of size $2^{\log^{a} n}$.

## Proof sketch

Combine the Murray-Williams worst-case lower bound with hardness amplification that is computable within $\mathrm{NQP}$: encode the hard function with a locally list-decodable code whose decoder is an $\mathrm{AC}^0[m]$ circuit with few oracle calls; an approximate $\mathrm{ACC}^0$ circuit for the encoded function would yield a worst-case $\mathrm{ACC}^0$ circuit, using the fact that $\mathrm{ACC}^0$ can compute approximate majority needed by the decoder up to $\operatorname{polylog}$ advantage.

## Depends on

- [Nondeterministic quasi-polynomial time](nqp-class.md)

## Proof depends on

- [Murray–Williams: NQP is not contained in ACC0](murray-williams-nqp-acc.md)

## Sources

- L. Chen, "Non-deterministic quasi-polynomial time is average-case hard for ACC circuits", FOCS (2019), ECCC TR19-031.
- L. Chen, H. Ren, "Strong average-case circuit lower bounds from non-trivial derandomization", STOC (2020); SIAM Journal on Computing 51 (2022).
