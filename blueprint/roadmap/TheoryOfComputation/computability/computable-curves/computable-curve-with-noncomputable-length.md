# Some polynomial-time computable simple plane curve has finite but noncomputable length

There is a simple plane curve, smooth except at one endpoint, with a parametrization computable in polynomial time, whose length is finite and lower semicomputable but not a computable real number.

**Curves and length.** A *curve* is the range $\Gamma$ of a continuous map $f : [a, b] \to \mathbb{R}^n$, a *parametrization* of $\Gamma$; it is *simple* if some parametrization is one-to-one. For a one-to-one parametrization $f$ the *length* of $\Gamma$ is

$$
\mathcal{L}(\Gamma) = \sup \Bigl\{ \sum_{i=0}^{m-1} |f(t_{i+1}) - f(t_i)| \ :\ a = t_0 < t_1 < \dots < t_m = b \Bigr\},
$$

which does not depend on the choice of $f$, and $\Gamma$ is *rectifiable* if $\mathcal{L}(\Gamma) < \infty$. A real number $x$ is *computable* if some algorithm outputs rationals $q_k$ with $|x - q_k| \le 2^{-k}$ for all $k$, and *lower semicomputable* if it is the limit of a computable increasing sequence of rationals. A curve is *smooth except at one endpoint* if it has a tangent at every interior point and a one-sided tangent at one endpoint, these tangents varying continuously along the curve. A parametrization is computable (in polynomial time) if an algorithm approximates $f(t)$ to precision $2^{-k}$ from approximations of $t$ (in time polynomial in $k$).

**Theorem (Ko; Gu, Lutz and Mayordomo).** There is a simple, rectifiable plane curve $\Gamma \subseteq \mathbb{R}^2$, smooth except at one endpoint, with a parametrization computable in polynomial time, whose length $\mathcal{L}(\Gamma)$ is not computable. The length of every simple rectifiable curve in $\mathbb{R}^n$ with a computable parametrization is lower semicomputable, even when every computable parametrization of it retraces parts of the curve (Section 4 of the source).

Ko first proved the existence of polynomial-time computable curves of finite but noncomputable length. Gu, Lutz and Mayordomo construct such a curve with the further property that every computable parametrization of it retraces some subcurve of positive length arbitrarily many times (their main theorem), and derive the noncomputability of its length from this (Corollary 5.2).

## Depends on

None.

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The curve is traced by a particle whose acceleration on the time interval reserved for $n$ makes it move back and forth along a short stretch, in a way governed by the running time of the $n$-th Turing machine on input $n$, so that the curve encodes the diagonal halting set $K$ (Construction 3.1 of the source). Gu, Lutz and Mayordomo show that the constant-speed parametrization of a simple rectifiable curve with a computable parametrization is computable relative to its length (Theorem 5.1 of the source), while for their curve no computable parametrization avoids unbounded retracing (main theorem, Theorem 3.2); since the constant-speed parametrization never retraces, the length cannot be computable. Lower semicomputability comes from approximating the length by inscribed polygons (Section 4). A good expansion links pages for the construction of Theorem 3.2 and for Theorem 5.1.

## Sources

- X. Gu, J. H. Lutz and E. Mayordomo, "Curves that must be retraced", Information and Computation 209 (2011), no. 6, 992–1006, https://doi.org/10.1016/j.ic.2011.01.004; read in arXiv:0802.4312v2 (Section 2, the introduction's consequences (1) and (2), Theorem 3.2, Section 4, Theorem 5.1 and Corollary 5.2 of arXiv:0802.4312v2).
- K.-I. Ko, "A polynomial-time computable curve whose interior has a nonrecursive measure", Theoretical Computer Science 145 (1995), no. 1–2, 241–270, https://doi.org/10.1016/0304-3975(94)00154-B (cited after the paper above, which states this result of Ko).
