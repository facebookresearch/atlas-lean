# Formula-XOR circuits and their local oracle extension

A Formula-XOR circuit is a De Morgan formula whose leaves compute parities of arbitrary subsets of the input bits. Its local oracle extension Formula-$\mathcal{O}$-XOR inserts, directly above the parity leaves, a layer of oracle gates of small fan-in that may compute any fixed function.

Let $x_1, \dots, x_N$ be the input bits. For $s \ge 1$, $\mathsf{Formula}\text{-}\mathsf{XOR}[s]$ is the class of formulas over the De Morgan basis (fan-in-two AND and OR gates, negations only at the leaves) with at most $s$ leaves, in which every leaf is labelled by a parity $\bigoplus_{i \in S} x_i$ for an arbitrary set $S \subseteq [N]$; Oliveira, Pich and Santhanam write $U_2\text{-}\mathsf{Formula}\text{-}\oplus[s]$ and also allow literals and constants at the leaves. Size is the number of leaves.

For a language $\mathcal{O} \subseteq \{0,1\}^*$ and a fan-in bound $\ell$, a $\mathsf{Formula}\text{-}\mathcal{O}\text{-}\mathsf{XOR}$ circuit is a Formula-XOR circuit in which gates $\mathcal{O}(p_1, \dots, p_k)$ with $k \le \ell$ may be placed in the layer right above the parity leaves, each input $p_j$ being a parity leaf. It is the special case of the local circuit classes in which the oracle gates have locality $\ell$ and adaptivity $1$. The analogous class $\mathsf{AC}^0\text{-}\mathsf{XOR}[s]$ consists of constant-depth circuits with $s$ gates whose bottom-layer gates compute arbitrary parities.

## Expansion

Every parity of at most $N$ bits has a De Morgan formula with $O(N^2)$ leaves, so $\mathsf{Formula}\text{-}\mathsf{XOR}[N^{1.01}] \subseteq \mathsf{Formula}[N^{3.01}]$; understanding barely superlinear Formula-XOR circuits is therefore a prerequisite for super-cubic De Morgan formula lower bounds. Tal's bound for bipartite formulas gives $\mathsf{InnerProduct} \notin \mathsf{Formula}\text{-}\mathsf{XOR}[N^{1.99}]$ on $N$ input bits, which makes this class the setting of the hardness magnification frontier for MCSP studied by Chen et al.

## Depends on

- [Oracle circuits and local circuit classes](../../../circuit-complexity/hardness-magnification/oracle-circuits-and-local-circuit-classes.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Jan Pich, Ninad Rajgopal and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", *Journal of the ACM* 69(4), 2022 (conference version ITCS 2020), DOI 10.1145/3538391, arXiv:1911.08297v1 (Section 1.1, frontier B and its note; Section 5, the Formula-XOR lower bound of Tal).
- Igor C. Oliveira, Ján Pich and Rahul Santhanam, "Hardness Magnification Near State-of-the-Art Lower Bounds", *Theory of Computing* 17(11), 2021 (CCC 2019 special issue), DOI 10.4086/toc.2021.v017a011 (Section 1.2, Notation).
