# The lossy coding problem LossyCode and the classes LOSSY[C]

An instance of **LossyCode** is a pair of Boolean circuits $C:\{0,1\}^m\to\{0,1\}^{m-1}$ (compressor) and $D:\{0,1\}^{m-1}\to\{0,1\}^m$ (decompressor); a solution is any $z\in\{0,1\}^m$ with $D(C(z))\ne z$. Solutions always exist, since $D\circ C$ has image of size at most $2^{m-1}$, and at least half of all $z$ are solutions. $\mathsf{LOSSY}$ is the class of languages polynomial-time reducible to LossyCode. For a complexity class $\mathcal{C}$ closed under the relevant compositions, $\mathsf{LOSSY}[\mathcal{C}]$ is the class of problems $\mathcal{C}$-reducible to LossyCode where the compressor and decompressor are themselves computable and evaluable in $\mathcal{C}$. By the counting fact,

$$
\mathcal{C}\subseteq\mathsf{LOSSY}[\mathcal{C}]\subseteq\mathsf{ZP}\mbox{-}\mathcal{C},
$$

and in particular $\mathsf{P}\subseteq\mathsf{LOSSY}\subseteq\mathsf{ZPP}$.

## Depends on

- [ZPP](../../time-and-space-complexity-classes/zpp.md)
- [Polynomial time on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/p.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
