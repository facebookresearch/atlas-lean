# The freeness problem for semigroups

The freeness problem over a semigroup is the decision problem whose instances are finite sets of its elements and whose question is whether the set is a code: distinct finite sequences of elements of the set must have distinct products.

Let $S$ be a semigroup whose elements have a computable representation. A subset $X\subseteq S$ is a *code* if for all $m,n\ge1$ and $x_1,\dots,x_m,y_1,\dots,y_n\in X$, the equality $x_1x_2\cdots x_m=y_1y_2\cdots y_n$ is possible only when $m=n$ and $x_i=y_i$ for every $i$; equivalently, $X$ freely generates the subsemigroup $X^+$ and is a minimal generating set of it.

The *freeness problem over $S$*, $\mathrm{Free}[S]$, asks, given a finite subset $X\subseteq S$, whether $X$ is a code; for $k\ge1$, $\mathrm{Free}(k)[S]$ is its restriction to $k$-element subsets. Freeness of $X^+$ is a different question: $X^+$ is free iff some code $Y\subseteq X$ satisfies $X\subseteq Y^+$.

Relevant semigroups include the free monoid $\mathbb W=\{0,1\}^*$ under concatenation, the direct product $\mathbb W\times\mathbb W$ with componentwise concatenation, and the multiplicative semigroups $\mathbb N^{d\times d}$, $\mathbb Z^{d\times d}$ and $\mathbb Q^{d\times d}$ of square matrices.

## Depends on

None.

## Proof depends on

None.

## Expansion

Over a free monoid $\Sigma^*$ the freeness problem is decidable (Sardinas and Patterson), and over $\mathbb W\times\mathbb W$ it is decidable for two-element sets, since $\{x,y\}$ is not a code iff its two elements commute. For a single matrix the problem is decidable in polynomial time over $\mathbb Q^{d\times d}$. Over $\mathbb N^{3\times3}$ it is undecidable (Klarner, Birget and Satterfield, 1991).

## Sources

- Julien Cassaigne and Francois Nicolas, "On the decidability of semigroup freeness", *RAIRO - Theoretical Informatics and Applications* 46(3), 2012, pp. 355–399, doi:[10.1051/ita/2012010](https://doi.org/10.1051/ita/2012010); read in arXiv:0808.3112v4 ([arXiv](https://arxiv.org/abs/0808.3112v4)), whose numbering is used: Section 1.1 (Definitions 1.1–1.2 and Example 1.4 on codes), Definition 1.7 (the freeness problems), Remark 1.8 and Examples 1.9–1.11.
