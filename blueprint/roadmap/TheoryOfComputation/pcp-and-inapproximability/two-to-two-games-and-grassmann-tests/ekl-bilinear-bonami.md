# Ellis–Kindler–Lifshitz: Bonami-type lemma on spaces of linear maps

Let $\mathcal{L} = \operatorname{Lin}(\mathbb{F}_q^n, \mathbb{F}_q^m)$ with the uniform measure, and for $f : \mathcal{L} \to \mathbb{R}$ of degree at most $d$ (in the natural filtration by functions depending on the images of at most $d$ vectors) define $f$ to be **$(d, \varepsilon)$-global** if every restriction of $f$ to a coset $\{T : T v_i = w_i,\ 1 \le i \le d\}$ has $L^2$-norm at most $\varepsilon$. Then there is a constant $C_{d,q}$ depending only on $d$ and $q$ such that every $(d,\varepsilon)$-global $f$ of degree at most $d$ satisfies

$$
\|f\|_4^4 \le C_{d,q}\, \varepsilon^2\, \|f\|_2^2.
$$

As a consequence, global sets in the bilinear scheme expand near-perfectly, which gives a short proof of the $2$-to-$2$ Games Theorem with explicit quantitative bounds.

## Proof sketch

Decompose $f$ by successive conditioning on images of basis vectors and prove a hypercontractive estimate for each derivative using the fact that restrictions of global functions are global; the main step is a level-$d$ inequality obtained by induction on $d$ with a careful accounting of the $q$-analogue of influences. Globalness replaces the missing small-influence hypothesis that fails in non-product spaces.

## Proof depends on

- [Equivalence of Grassmann, shortcode and bilinear small-set expansion](shortcode-equivalence.md)
- [Hypercontractivity Theorem (Bonami–Beckner)](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/hypercontractivity-theorem.md)

## Sources

- D. Ellis, G. Kindler, N. Lifshitz, "An analogue of Bonami's lemma for functions on spaces of linear maps, and 2-2 games", STOC (2023), arXiv:2209.04243.
