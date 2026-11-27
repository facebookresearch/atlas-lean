# Projected shifted partials and the Nisan–Wigderson design polynomial

For $f$ and parameters $k, \ell$, let $\pi_{\mathrm{ML}}$ be the linear projection that keeps only the multilinear monomials. The **projected shifted partials measure** is

$$
\mathrm{PSP}_{k,\ell}(f) = \dim \operatorname{span}\bigl\{\, \pi_{\mathrm{ML}}(m \cdot g) \;:\; m \text{ multilinear of degree } \ell,\ g \in \partial^{=k} f \,\bigr\}.
$$

Let $q$ be a prime power and $1 \le k \le d \le q$. Identify $[q]$ with $\mathbb{F}_q$ by a bijection and $[d]$ with $d$ distinct elements of $\mathbb{F}_q$, so that for $h \in \mathbb{F}_q[z]$ and $i \in [d]$ the value $h(i)$ is an element of $[q]$. The **Nisan-Wigderson design polynomial** on the variables $\{x_{i,j}\}_{i \in [d],\, j \in [q]}$ is

$$
\mathrm{NW}_{q,d,k} = \sum_{h \in \mathbb{F}_q[z],\ \deg h < k} \ \prod_{i=1}^{d} x_{i, h(i)},
$$

a homogeneous multilinear polynomial of degree $d$ with $q^{k}$ distinct monomials, which pairwise share fewer than $k$ variables because two distinct polynomials of degree less than $k$ agree on at most $k - 1$ of the $d \ge k$ points. Kayal–Saha–Saptharishi take $q = d$; Kayal–Limaye–Saha–Srinivasan take $q = d^2$, with $[d]$ the subfield $\mathbb{F}_d$ of $\mathbb{F}_{d^2}$; with either choice the family is in $\mathrm{VNP}$.

## Depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Sources

- N. Kayal, N. Limaye, C. Saha, S. Srinivasan, "An exponential lower bound for homogeneous depth four arithmetic formulas", SIAM Journal on Computing 46 (2017); FOCS (2014), ECCC TR14-005 (Section 5.1).
- N. Kayal, C. Saha, R. Saptharishi, "A super-polynomial lower bound for regular arithmetic formulas", STOC (2014), ECCC TR13-091 (construction (4) and Proposition 6).
