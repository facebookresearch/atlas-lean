# Subshifts of finite type, sofic and effective subshifts

A subshift of $\Sigma^{\mathbb{Z}^d}$ is the set of colorings avoiding a family of forbidden patterns; it is of finite type, sofic or effective according to how the family can be given. A configuration is aperiodic when no nonzero translation fixes it.

**Definitions.** Let $\Sigma$ be a finite alphabet and $d \ge 1$. A *configuration* is a map $x : \mathbb{Z}^d \to \Sigma$, with value $x_i$ at $i \in \mathbb{Z}^d$, and a *pattern* is a map $w : D \to \Sigma$ on a finite domain $D \subseteq \mathbb{Z}^d$. The pattern $w$ *appears* in $x$ if there is $i \in \mathbb{Z}^d$ with $x_{i+j} = w_j$ for all $j \in D$. For a family $\mathcal{F}$ of patterns,

$$
X_{\mathcal{F}} = \{ x \in \Sigma^{\mathbb{Z}^d} : \text{no } w \in \mathcal{F} \text{ appears in } x \}.
$$

A *subshift* is a set of the form $X_{\mathcal{F}}$; equivalently, a closed subset of $\Sigma^{\mathbb{Z}^d}$ (product of discrete topologies) invariant under the shifts $\sigma^t(x)_i = x_{i-t}$. A subshift $Y$ is

- *of finite type* (an SFT) if $Y = X_{\mathcal{F}}$ for a finite family $\mathcal{F}$;
- *sofic* if $Y = \pi(X)$ for an SFT $X \subseteq {\Sigma'}^{\mathbb{Z}^d}$ and a letter-to-letter map $\pi : \Sigma' \to \Sigma$ applied at every cell;
- *effective* if $Y = X_{\mathcal{F}}$ for a recursively enumerable family $\mathcal{F}$.

Every SFT is sofic and every sofic subshift is effective. A vector $p \in \mathbb{Z}^d$ is *broken at* $i$ in $x$ if $x_{i+p} \ne x_i$, and $x$ is (strongly) *aperiodic* if every nonzero $p \in \mathbb{Z}^d$ is broken at some position, that is, $\sigma^p(x) \ne x$ for all $p \ne 0$.

## Depends on

None.

## Proof depends on

None.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Definitions 1, 2 and 3 (periodicity and classes of subshifts).
