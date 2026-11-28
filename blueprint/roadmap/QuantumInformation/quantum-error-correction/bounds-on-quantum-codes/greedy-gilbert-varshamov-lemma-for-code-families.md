# The greedy Gilbert–Varshamov lemma for code families

Let $\varphi$ be a nonempty family of $k$-dimensional binary
[linear codes](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md) in $\mathbb{F}_2^n$, $k \ge 1$,
such that every nonzero vector of $\mathbb{F}_2^n$ lies in the same number $W$ of codes of $\varphi$. If

$$\sum_{j=1}^{d-1} \binom{n}{j} < \frac{2^n - 1}{2^k - 1} ,$$

then some code in $\varphi$ has minimum distance at least $d$. Proof: counting pairs (code, nonzero codeword) gives
$(2^n - 1) W = (2^k - 1) |\varphi|$, Calderbank and Shor's equation (24); the nonzero vectors of weight less than $d$ lie in
at most $W \sum_{j=1}^{d-1} \binom{n}{j} < |\varphi|$ codes. This is Calderbank and Shor's Lemma 3 in finite form, slightly
sharper since its sums start at zero. With the
[entropy bound on Hamming balls](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md)
it gives the Gilbert–Varshamov bound from below: for $0 < \delta < 1/2$ and fixed $0 < r < 1 - H_2(\delta)$, every such
family of codes of dimension $k = \lfloor r n \rfloor$ contains a code of minimum distance at least $\lceil \delta n \rceil$,
for all large $n$, since $\sum_{j < \lceil \delta n \rceil} \binom{n}{j} \le 2^{n H_2(\delta)} < 2^{n(1 - r)} \le (2^n - 1)/(2^k - 1)$.
The family used for good CSS codes, the duals of weakly self-dual codes, is not uniform on all of $\mathbb{F}_2^n$; its own
count is on the page on [counting weakly self-dual codes](counting-weakly-self-dual-codes.md).

## Depends on

- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Proof depends on

- [Volume of a Hamming ball, entropy upper bound](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md)

## Related topics

- [Counting weakly self-dual codes](counting-weakly-self-dual-codes.md): the same counting for the duals of weakly self-dual codes

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section V, Lemma 3 and its proof, equations (23)–(26) (attributed there to MacWilliams and Sloane, Chapter 17).
