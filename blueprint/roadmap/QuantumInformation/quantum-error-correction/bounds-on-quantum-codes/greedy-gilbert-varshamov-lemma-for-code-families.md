# The greedy Gilbert–Varshamov lemma for code families

Let $V \subseteq \mathbb{F}_2^n$ be a subspace, let $Z \subseteq V$ be a set of nonzero vectors of weight at least $d$, and
let $\varphi$ be a nonempty family of $k$-dimensional binary
[linear codes](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md) contained in $V$ such that
every nonzero vector of $V \setminus Z$ lies in the same number $W$ of codes of $\varphi$. If

$$\big|\{ v \in V : 1 \le \mathrm{wt}(v) < d \}\big| < \frac{2^{\dim V} - 1 - |Z|}{2^k - 1} ,$$

then some code in $\varphi$ has minimum distance at least $d$. Proof: counting pairs (code, nonzero codeword outside $Z$)
gives $(2^{\dim V} - 1 - |Z|) W \le (2^k - 1) |\varphi|$; the vectors of $V$ of weight between $1$ and $d - 1$, none of
which is in $Z$, lie in at most $W \cdot |\{ v \in V : 1 \le \mathrm{wt}(v) < d \}| < |\varphi|$ codes. Calderbank and
Shor's Lemma 3 is the case $V = \mathbb{F}_2^n$, $Z = \emptyset$, where the condition reads
$\sum_{j=1}^{d-1} \binom{n}{j} < (2^n - 1)/(2^k - 1)$; for good CSS codes it is applied to the codes $C^{\perp}$ of
[weakly self-dual codes](counting-weakly-self-dual-codes.md), with $V$ the even-weight words and $Z = \{1_n\}$. With the
[entropy bound on Hamming balls](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md),
families of rate $k/n > R$ contain codes with $R \ge 1 - H_2(d/n)$ asymptotically, the Gilbert–Varshamov bound.

## Depends on

- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Proof depends on

- [Volume of a Hamming ball, entropy upper bound](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/sum-choose-mul-pow-le-exp.md)

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section V, Lemma 3 and its proof, equations (23)–(26) (attributed there to MacWilliams and Sloane, Chapter 17), and the application to weakly self-dual codes that follows, where uniformity holds only for even-weight vectors.
