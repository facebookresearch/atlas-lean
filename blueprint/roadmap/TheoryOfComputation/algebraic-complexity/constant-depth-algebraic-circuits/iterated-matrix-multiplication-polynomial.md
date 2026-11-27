# Iterated matrix multiplication and word polynomials

For $n,d\ge1$, the *iterated matrix multiplication polynomial* $\mathrm{IMM}_{n,d}$ is the $(1,1)$ entry of the product $X^{(1)}X^{(2)}\cdots X^{(d)}$ of $d$ generic $n\times n$ matrices with disjoint sets of variables; it is set-multilinear in the $d$ blocks of matrix entries and computable by an ABP of width $n$ and length $d$.

For a word $w=(w_1,\dots,w_d)$ with nonzero integer letters, let the block $X(w_i)$ have $2^{|w_i|}$ variables labelled by the strings in $\{0,1\}^{|w_i|}$. A set-multilinear monomial $m$ on these blocks splits as $m=m^+m^-$ into its factors on the blocks with $w_i>0$ and with $w_i<0$; let $\sigma(m^+)$ and $\sigma(m^-)$ be the concatenations, in block order, of the labels of their variables. The *word polynomial* is

$$
P_w=\sum_{m\,:\ \sigma(m^+)\text{ and }\sigma(m^-)\text{ are prefix-comparable}}m ,
$$

the sum over set-multilinear monomials for which one of the two strings is a prefix of the other. Its partial-derivative matrix $M_w(P_w)$ has full rank. The word $w$ is *$b$-unbiased* if $|w_1+\dots+w_t|\le b$ for every $t\le d$; for such $w$, $P_w$ is obtained from $\mathrm{IMM}_{2^b,d}$ by a set-multilinear linear substitution (each variable of the $p$-th matrix replaced by a linear form in the block $X(w_p)$), and $\mathrm{IMM}_{2^b,d}$ is obtained from $\mathrm{IMM}_{n,d}$ for every $n\ge2^b$ by setting variables to $0$.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)
- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021; full version, Electronic Colloquium on Computational Complexity TR21-081, revision 1, Section 2.2, Lemma 8 and Section 8.
