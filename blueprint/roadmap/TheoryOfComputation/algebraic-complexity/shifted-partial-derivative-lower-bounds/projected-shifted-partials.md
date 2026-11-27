# Projected shifted partials and the Nisan–Wigderson design polynomial

For $f$ and parameters $k, \ell$, let $\pi_{\mathrm{ML}}$ be the linear projection that keeps only the multilinear monomials. The **projected shifted partials measure** is

$$
\mathrm{PSP}_{k,\ell}(f) = \dim \operatorname{span}\bigl\{\, \pi_{\mathrm{ML}}(m \cdot g) \;:\; m \text{ multilinear of degree } \ell,\ g \in \partial^{=k} f \,\bigr\}.
$$

The **Nisan-Wigderson design polynomial** over a field $\mathbb{F}_q$-indexed set of variables $\{x_{i,j}\}_{i \in [d], j \in [q]}$ is

$$
\mathrm{NW}_{q,d,k} = \sum_{h \in \mathbb{F}_q[z],\ \deg h < k} \ \prod_{i=1}^{d} x_{i, h(i)},
$$

a polynomial in $\mathrm{VNP}$ whose monomials pairwise share fewer than $k$ variables.

## Depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Sources

- N. Kayal, N. Limaye, C. Saha, S. Srinivasan, "An exponential lower bound for homogeneous depth four arithmetic formulas", SIAM Journal on Computing 46 (2017); FOCS (2014).
- N. Kayal, C. Saha, R. Saptharishi, "A super-polynomial lower bound for regular arithmetic formulas", STOC (2014), ECCC TR13-091.
