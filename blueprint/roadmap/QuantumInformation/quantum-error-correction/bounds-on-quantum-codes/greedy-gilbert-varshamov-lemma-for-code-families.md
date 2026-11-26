# The greedy Gilbert–Varshamov lemma for code families

Let $\varphi$ be a nonempty family of $[n, k]$ binary [linear codes](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)
such that every nonzero vector of $\mathbb{F}_2^n$ lies in the same number $W$ of codes of $\varphi$. If

$$\sum_{j=1}^{d-1} \binom{n}{j} < \frac{2^n - 1}{2^k - 1} ,$$

then some code in $\varphi$ has minimum distance at least $d$. Proof: counting pairs (code, nonzero codeword) gives
$(2^n - 1) W = (2^k - 1) |\varphi|$; the nonzero vectors of weight less than $d$ lie in at most
$W \sum_{j=1}^{d-1} \binom{n}{j} < |\varphi|$ codes. With the
[entropy bound on Hamming balls](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md),
families of rate $k/n > R$ contain codes with $R \ge 1 - H_2(d/n)$ asymptotically, the Gilbert–Varshamov bound.

## Depends on

- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Proof depends on

- [Volume of a Hamming ball, entropy upper bound](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md)

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section V, Lemma 3 and its proof, equations (23)–(26) (attributed there to MacWilliams and Sloane, Chapter 17).
