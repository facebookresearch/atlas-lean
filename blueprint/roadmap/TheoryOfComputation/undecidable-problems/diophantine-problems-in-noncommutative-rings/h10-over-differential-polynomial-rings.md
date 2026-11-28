# Hilbert's tenth problem over rings of differential polynomials is undecidable

For every differential field $K$ with one derivation, no algorithm decides whether a finite system of polynomial equations with coefficients in $\mathbb{Q}[\partial]$ or $\mathbb{F}_p[\partial]$ has a solution in the ring $K[\partial]$ of differential operators.

**Setting (Eggink).** A *derivation* on a commutative ring $R$ is an additive map $\frac{d}{dx} : R \to R$ with $\frac{d}{dx}(rs) = r \frac{d}{dx}(s) + s \frac{d}{dx}(r)$. A *differential field* is a field $K$ with pairwise commuting derivations $\frac{d}{dx_1}, \dots, \frac{d}{dx_k}$; its *field of constants* $C$ consists of the elements killed by all of them. The ring of *differential polynomials* $K[\partial_1, \dots, \partial_k]$ is the noncommutative ring of polynomials $\sum a_{\alpha} \partial^{\alpha}$ with coefficients in $K$, with the usual addition and the multiplication determined by $\partial_i \partial_j = \partial_j \partial_i$ and $\partial_i a = a \partial_i + \frac{d}{dx_i}(a)$ for $a \in K$. It satisfies the left Ore condition, and $K(\partial_1, \dots, \partial_k)$ is its left division ring of fractions. *Hilbert's tenth problem over $R$ with ring of coefficients $R_0$* asks for an algorithm that decides, given a finite system of polynomial equations in noncommuting variables with coefficients in a computable subring $R_0 \subseteq R$, whether it has a solution in $R$.

**Theorem (Eggink).** Let $(K, \frac{d}{dx})$ be a differential field. Then Hilbert's tenth problem over $K[\partial]$ with ring of coefficients $\mathbb{Q}[\partial]$ (characteristic $0$) or $\mathbb{F}_p[\partial]$ (characteristic $p$) has a negative answer (Theorem 1.2.5 of arXiv:2410.03485v1).

For the division rings the source proves: if $K$ is a differential field with derivations $\frac{d}{dx_1}, \dots, \frac{d}{dx_k}$ and field of constants $C$, Hilbert's tenth problem over $K(\partial_1, \dots, \partial_k)$ with ring of coefficients $\mathbb{Q}(\partial_1, \dots, \partial_k)$ has a negative answer if $C = \mathbb{R}$, or if $C = \mathbb{C}$ and $k \ge 2$ (Theorem 1.2.6 of arXiv:2410.03485v1).

The source notes that $K[\partial]$ is sometimes called a Weyl algebra; the classical [Weyl algebra of polynomial differential operators](../../../Algebra/associative-algebras/weyl-algebra.md) has polynomial rather than field coefficients.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Ring with identity](../../../Algebra/rings-and-fields/ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The map $\phi : C[t] \to K[\partial]$ with $\phi(t) = \partial$ is an injective ring homomorphism whose image is defined by equations, so Hilbert's tenth problem over $C[t]$ with a constant for $t$ reduces to that over $K[\partial]$; the former has a negative answer by Denef's theorems in characteristic $0$ and $p$. A good expansion adds and links a page for Denef's undecidability of the Diophantine problem over polynomial rings over integral domains.

## Sources

- A. Eggink, "Hilbert's tenth problem for some noncommutative rings", *Annals of Pure and Applied Logic* 177(8), 2026, article 103745, doi:[10.1016/j.apal.2026.103745](https://doi.org/10.1016/j.apal.2026.103745); read as arXiv:2410.03485v1 ([arXiv](https://arxiv.org/abs/2410.03485v1)), whose numbering is used: the definitions and Theorems 1.2.5 and 1.2.6 of the introduction, and their proofs in Section 7.
