# Allender–Cheraghchi–Myrisiotis–Tirumala–Volkovich: McKTP is NP-complete under randomized reductions

For some polynomial-time computable conditional length $m(n)$, the Minimum Conditional KT Problem is NP-complete under polynomial-time randomized reductions, by an Ilango-style reduction from approximating Set Cover.

**Theorem.** There is a polynomial-time computable $m:\mathbb{N}\to\mathbb{N}$ such that McK$^m$TP is NP-complete under polynomial-time randomized reductions.

**Key lemma.** Let $S_1,\dots,S_t\subseteq[n]$ cover $[n]$, let $b$ be a string of length $N\ge(nt)^{5}$ and let $P=(P_1,\dots,P_n)$ be a uniformly random partition of $[N]$ into $n$ parts. Let $y$ be the truth table of the oracle $O(i,z)=b_{\langle S_i^{P}\rangle}(z)$ for $i\in[t]$, $z\in[N]$ (and $0$ otherwise), where $S^{P}=\bigcup_{j\in S}P_j$ and $b_{\langle R\rangle}$ zeroes the positions outside $R$; so $|y|=Nt$. If $\ell$ is the size of an optimal cover, then

$$
\mathrm{KT}(b\mid y)\le 200\,\ell(\log t+\log N)
$$

always, and $\mathrm{KT}(b\mid y)>\ell(\log t+\log N)/2$ with high probability over a uniformly random $b$. Hence, with $c=\log N+\log t$, the quantity $\tfrac{2}{c}\mathrm{KT}(b\mid y)$ approximates Set Cover within a factor $400$ with probability $1-o(1)$.

## Expansion

A program that names the $\ell$ sets of an optimal cover reconstructs each bit $b_j$ by querying the oracle at the index of a set whose lift contains $j$, giving the upper bound. Conversely, a program of size below $\ell(\log t+\log N)/2$ can query too few lifted sets to recover a random $b$: counting oracle programs against the $2^{N}$ choices of $b$ and using the random partition shows that any short program would yield a cover smaller than $\ell$. Since Set Cover is NP-hard to approximate within $(1-o(1))\ln n$ (Dinur–Steurer), a constant-factor gap for $\mathrm{KT}(b\mid y)$ suffices for NP-hardness; membership in NP is direct. Liu and Pass proved the analogous NP-completeness for conditional $\mathrm{K}^t$.

## Depends on

- [Conditional KT complexity and the Minimum Conditional KT Problem McKTP](conditional-kt-complexity-and-mcktp.md)

## Proof depends on

- [The SET COVER decision problem](../../../np-completeness/set-systems-and-location/set-cover/set-cover-dec.md)

## Sources

- Eric Allender, Mahdi Cheraghchi, Dimitrios Myrisiotis, Harsha Tirumala and Ilya Volkovich, "One-Way Functions and a Conditional Variant of MKTP", *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.FSTTCS.2021.7 (Theorem 2, Definition 26, Theorem 27, Lemma 29, Corollaries 32, 33 and 34, Appendix B).
