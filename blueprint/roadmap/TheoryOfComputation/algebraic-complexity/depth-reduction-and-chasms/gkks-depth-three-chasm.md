# Gupta–Kamath–Kayal–Saptharishi: the chasm at depth three

Let $\mathbb{F}$ be a field of characteristic $0$. If a homogeneous polynomial $f \in \mathbb{F}[x_1, \dots, x_n]$ of degree $d$ is computed by an arithmetic circuit of size $s$, then $f$ is computed by a (non-homogeneous) $\Sigma\Pi\Sigma$ circuit of size $s^{O(\sqrt{d})}$. Consequently, an $n^{\omega(\sqrt{d})}$ lower bound for depth-three circuits computing an explicit family in $\mathrm{VNP}$ of polynomial degree would imply $\mathrm{VP} \ne \mathrm{VNP}$ over characteristic $0$.

## Proof sketch

Start from the depth-four reduction. Convert each product of $O(\sqrt{d})$ bottom polynomials into a sum of powers of sums by Fischer's identity, then apply Saxena's duality to rewrite each power of a sum of low-degree polynomials as a sum of products of univariate polynomials in those polynomials. Expanding the univariates and applying Fischer once more on the bottom monomials gives a sum of products of linear forms of size $s^{O(\sqrt{d})}$, losing homogeneity.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Proof depends on

- [Agrawal–Vinay–Koiran–Tavenas reduction to depth four](agrawal-vinay-tavenas.md)
- [Fischer's identity: products of variables as sums of powers of linear forms](fischer-identity.md)
- [Saxena's duality trick for powers of sums of products](saxena-duality.md)

## Sources

- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Arithmetic circuits: a chasm at depth three", FOCS (2013); SIAM Journal on Computing 45 (2016) 1064-1079.
