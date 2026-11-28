# Prime and dimension-minimal counter nets

A counter net is composite if its language is an intersection of languages of finitely many counter nets of smaller dimension, prime if it is not, and dimension-minimal if no counter net of smaller dimension accepts the same language.

**Definition.** For $d,n\in\mathbb N$, a $k$-dimensional [counter net](counter-nets.md) ($k$-CN) $\mathcal A$ is *$(d,n)$-composite* if there are $d$-CNs $\mathcal B_1,\dots,\mathcal B_n$ with

$$
L(\mathcal A)=\bigcap_{i=1}^nL(\mathcal B_i).
$$

It is *composite* if it is $(d,n)$-composite for some $d<k$ and some $n$, and *prime* otherwise; it is *dimension-minimal* if it is not $(k-1,1)$-composite, that is, if no counter net of smaller dimension accepts the same language. Being $(0,1)$-composite means accepting a regular language.

## Depends on

- [Counter nets](counter-nets.md)

## Proof depends on

None.

## Expansion

Every $k$-DCN is $(1,k)$-composite: projecting its transitions onto each counter gives $k$ deterministic one-counter nets with the same state structure whose languages intersect to $L(\mathcal A)$. A deterministic counter net is therefore prime only in dimension $0$, or in dimension $1$ when its language is not regular. Primality thus measures what nondeterminism together with several counters can express beyond intersections of lower-dimensional languages.

## Sources

- Shaull Almagor, Guy Avni, Henry Sinclair-Banks and Asaf Yeshurun, "Dimension-Minimality and Primality of Counter Nets", in *Foundations of Software Science and Computation Structures (FoSSaCS 2024)*, Lecture Notes in Computer Science, Springer, 2024, pp. 229–249, doi:[10.1007/978-3-031-57231-9_11](https://doi.org/10.1007/978-3-031-57231-9_11); read in arXiv:2307.14492v2 ([arXiv](https://arxiv.org/abs/2307.14492v2)): Section 3 (the definition of compositeness, primality and dimension-minimality, the remark on regularity, and the proposition that deterministic counter nets are $(1,k)$-composite).
