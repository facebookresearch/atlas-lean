# Subshifts and the aperiodic domino problem

A subshift of $\Sigma^{\mathbb{Z}^d}$ is the set of colorings avoiding a family of forbidden patterns; it is of finite type, sofic or effective according to how the family can be given. The aperiodic domino problem asks whether a given subshift contains a configuration that no nonzero translation fixes.

**Definitions.** Let $\Sigma$ be a finite alphabet and $d \ge 1$. A *configuration* is a map $x : \mathbb{Z}^d \to \Sigma$, with value $x_i$ at $i \in \mathbb{Z}^d$, and a *pattern* is a map $w : D \to \Sigma$ on a finite domain $D \subseteq \mathbb{Z}^d$. The pattern $w$ *appears* in $x$ if there is $i \in \mathbb{Z}^d$ with $x_{i+j} = w_j$ for all $j \in D$. For a family $\mathcal{F}$ of patterns,

$$
X_{\mathcal{F}} = \{ x \in \Sigma^{\mathbb{Z}^d} : \text{no } w \in \mathcal{F} \text{ appears in } x \}.
$$

A *subshift* is a set of the form $X_{\mathcal{F}}$; equivalently, a closed subset of $\Sigma^{\mathbb{Z}^d}$ (product of discrete topologies) invariant under the shifts $\sigma^t(x)_i = x_{i-t}$. A subshift $Y$ is

- *of finite type* (an SFT) if $Y = X_{\mathcal{F}}$ for a finite family $\mathcal{F}$;
- *sofic* if $Y = \pi(X)$ for an SFT $X \subseteq {\Sigma'}^{\mathbb{Z}^d}$ and a letter-to-letter map $\pi : \Sigma' \to \Sigma$ applied at every cell;
- *effective* if $Y = X_{\mathcal{F}}$ for a recursively enumerable family $\mathcal{F}$.

Every SFT is sofic and every sofic subshift is effective. A vector $p \in \mathbb{Z}^d$ is *broken at* $i$ in $x$ if $x_{i+p} \ne x_i$, and $x$ is (strongly) *aperiodic* if every nonzero $p \in \mathbb{Z}^d$ is broken at some position, that is, $\sigma^p(x) \ne x$ for all $p \ne 0$.

The *aperiodic domino problem* (AD) asks, given an effective family $\mathcal{F}$ of $d$-dimensional patterns, whether $X_{\mathcal{F}}$ contains an aperiodic configuration. Its variants restrict the input: for SFTs the input is a finite family $\mathcal{F}$, and for sofic subshifts it is a finite family defining an SFT $X$ together with the map $\pi$, the question being whether $\pi(X)$ contains an aperiodic configuration.

**The class $\Sigma^1_1$.** A decision problem $P : \mathbb{N} \to \{0, 1\}$ is in $\Sigma^1_1$ if there is an arithmetical relation $R$, evaluated with an oracle $f$, such that $P(n) = 1$ exactly when there is $f \in 2^{\mathbb{N}}$ with $R^f(n)$. A problem is $\Sigma^1_1$-hard if every $\Sigma^1_1$ problem many-one reduces to it, and $\Sigma^1_1$-complete if moreover it is in $\Sigma^1_1$. Every arithmetical problem is in $\Sigma^1_1$, and a $\Sigma^1_1$-complete problem is not arithmetical; in particular it is undecidable.

The aperiodic domino problem is in $\Sigma^1_1$ for every $d$, since it asks for a configuration (a second-order object, coded in $2^{\mathbb{N}}$) satisfying the arithmetical conditions "no pattern of $\mathcal{F}$ appears" and "every nonzero vector is broken". It is $\Pi^0_1$-hard for $d \ge 2$: taking the product with a fixed SFT all of whose configurations are aperiodic reduces the classical domino problem to it (Proposition 9 of the source).

## Depends on

None.

## Proof depends on

None.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Definitions 1, 2, 3 (periodicity and classes of subshifts), Definition 6 (the class $\Sigma^1_1$), Definition 8 (the problem AD), Proposition 9 ($\Pi^0_1$-hardness) and Proposition 10 (membership in $\Sigma^1_1$).
