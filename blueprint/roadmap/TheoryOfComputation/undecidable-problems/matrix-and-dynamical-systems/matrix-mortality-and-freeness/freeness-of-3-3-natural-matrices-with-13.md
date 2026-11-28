# Freeness of 13 natural 3×3 matrices is undecidable

For every $k\ge13$, no algorithm decides whether a given set of $k$ matrices of size $3\times3$ with natural-number entries is a code; the same holds for pairs of words, sets of $k$ elements of the direct product of two free monoids.

**Theorem (Cassaigne and Nicolas).** For every integer $k\ge13$, the problems $\mathrm{Free}(k)[\mathbb W\times\mathbb W]$ and $\mathrm{Free}(k)[\mathbb N^{3\times3}]$ of the [freeness problem](the-freeness-problem-for-semigroups.md) are undecidable: there is no algorithm that, given $k$ elements of $\{0,1\}^*\times\{0,1\}^*$ (respectively $k$ matrices in $\mathbb N^{3\times3}$), decides whether they form a code.

In higher dimension fewer matrices suffice: for every $h\in\mathbb N$, $\mathrm{Free}(7+h)[\mathbb N^{6\times6}]$, $\mathrm{Free}(5+h)[\mathbb N^{9\times9}]$, $\mathrm{Free}(4+h)[\mathbb N^{12\times12}]$, $\mathrm{Free}(3+h)[\mathbb N^{18\times18}]$ and $\mathrm{Free}(2+h)[\mathbb N^{36\times36}]$ are undecidable (Corollary 8.3 in the numbering of arXiv:0808.3112v4, Corollary 8.6 in the published version). For $k=1$ freeness of a single rational matrix is decidable in polynomial time, and over $\mathbb Q$ or $\mathbb Z$ the decidability of $\mathrm{Free}(k)$ is the same (Theorem 3.13).

## Depends on

- [The freeness problem for semigroups](the-freeness-problem-for-semigroups.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable for Claus instances of size 7](../../post-correspondence-problem/pcp-is-undecidable-for-claus-instances-of-size-7.md)

## Expansion

By Matiyasevich and Sénizergues, accessibility in semi-Thue systems with $3$ rules is undecidable, and Claus's reduction then makes Post's correspondence problem undecidable for $7$ pairs, even on [Claus instances](../../post-correspondence-problem/pcp-is-undecidable-for-claus-instances-of-size-7.md), which have a prescribed first and last pair (Corollary 7.9; Cassaigne and Nicolas use Claus instances in the sense of their Definition 7.7, which a good expansion relates to the form on the linked page); the mixed modification of the problem is undecidable on Claus instances with $7$ pairs as well (Halava, Harju and Hirvensalo). Theorem 7.18 shows that decidability of $\mathrm{Free}(2k-1)[\mathbb W\times\mathbb W]$ would decide both problems for $k$ pairs on Claus instances, which gives undecidability for $2\cdot7-1=13$ elements, and Proposition 7.1 extends it to every $k\ge13$. Pairs of binary words embed into $\mathbb N^{3\times3}$ by a multiplicative injective morphism (Theorem 7.21). The higher-dimensional bounds come from Theorem 8.1, which reduces $\mathrm{Free}(kd+1)[D]$ to $\mathrm{Free}(k+1)[D^{d\times d}]$.

## Sources

- Julien Cassaigne and Francois Nicolas, "On the decidability of semigroup freeness", *RAIRO - Theoretical Informatics and Applications* 46(3), 2012, pp. 355–399, doi:[10.1051/ita/2012010](https://doi.org/10.1051/ita/2012010); read in arXiv:0808.3112v4 ([arXiv](https://arxiv.org/abs/0808.3112v4)), whose numbering is used: Corollaries 7.19 and 7.22 with Theorems 7.5, 7.6, 7.16, 7.18 and 7.21, Corollary 7.9 and Proposition 7.1; Theorem 8.1 and Corollary 8.3; Theorem 3.13 and Section 2 for small cases. The published version, read in its open-access copy at <http://www.numdam.org/item/ITA_2012__46_3_355_0/>, numbers the higher-dimensional result Corollary 8.6.
