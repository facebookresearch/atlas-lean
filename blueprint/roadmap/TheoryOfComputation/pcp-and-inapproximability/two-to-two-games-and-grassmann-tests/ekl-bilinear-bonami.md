# Ellis–Kindler–Lifshitz: Bonami-type lemma on spaces of linear maps

Let $\mathcal{L} = \operatorname{Lin}(\mathbb{F}_q^n, \mathbb{F}_q^m)$ with the uniform measure (for a prime power $q$). A **two-sided $d$-restriction** fixes $A \in \mathcal{L}$ on a subspace $V_1 \le \mathbb{F}_q^n$ and fixes its dual map $A^*$ on the annihilator $W_1^\perp \le (\mathbb{F}_q^m)^*$ for a subspace $W_1 \le \mathbb{F}_q^m$ with $\dim V_1 + \operatorname{codim} W_1 \le d$ (in matrix terms, fixing $r$ rows and $c$ columns with $r + c \le d$), yielding the restricted function $f_{(V_1, W_1) \to T}$. A **$d$-junta** is a function depending on the values of $A$ on at most $r$ vectors and $A^*$ on at most $c$ covectors with $r + c \le d$, and $f^{\le d}$ denotes the orthogonal projection of $f : \mathcal{L} \to \mathbb{C}$ onto the span of $d$-juntas (junta-degree at most $d$). Call $f$ **$(d, \delta)$-restriction-global** (for $d \in \mathbb{N}$ and $\delta > 0$) if $\|f_{(V_1, W_1) \to T}\|_2^2 \le \delta$ for every two-sided restriction of total dimension at most $d$. Then there is an absolute constant $C > 0$ such that every $(d, \delta)$-restriction-global function $f : \mathcal{L} \to \mathbb{C}$ satisfies (Ellis–Kindler–Lifshitz, Theorem 1.5 / v1 Theorem 5)

$$
\|f^{\le d}\|_4^4 \le q^{C d^2}\, \delta\, \|f^{\le d}\|_2^2.
$$

As a consequence, global sets in the bilinear scheme expand near-perfectly, which gives a short proof of the $2$-to-$2$ Games Theorem with explicit quantitative bounds.

## Proof sketch

Decompose $f^{\le d}$ using two-sided restrictions (conditioning on both $A|_{V_1}$ and $A^*|_{W_1^\perp}$) and prove a hypercontractive $L^4$-versus-$L^2$ estimate by induction on the junta-degree $d$, using that two-sided restrictions of global functions remain global and bounding the bilinear analogue of generalized influences. Two-sided globalness replaces the small-influence hypothesis that fails in non-product spaces.

## Proof depends on

- [Equivalence of Grassmann, shortcode and bilinear small-set expansion](shortcode-equivalence.md)
- [Hypercontractivity Theorem (Bonami–Beckner)](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/hypercontractivity-theorem.md)

## Sources

- D. Ellis, G. Kindler, N. Lifshitz, "An analogue of Bonami's lemma for functions on spaces of linear maps, and 2-2 games", STOC (2023), arXiv:2209.04243.
