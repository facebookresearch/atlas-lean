# Hilbert's tenth problem over twisted polynomial rings in positive characteristic is undecidable

For a field $K$ of characteristic $p$ and a power $q$ of $p$, no algorithm decides whether a polynomial equation with coefficients in $\mathbb{F}_p\{\tau\}$ has a solution in the twisted polynomial ring $K\{\tau\}$, where $\tau a = a^q \tau$; the same holds for its division ring of fractions $K(\tau)$.

**Setting (Eggink).** Let $K$ be a field of characteristic $p$ and $q$ a power of $p$. The *twisted polynomial ring* $K\{\tau\}$ consists of the polynomials $\sum_i a_i \tau^i$ with $a_i \in K$, with the usual addition and the multiplication determined by $\tau a = a^q \tau$ for $a \in K$. It satisfies the left Ore condition, and $K(\tau)$ denotes its left division ring of fractions. For a ring $R$ (not necessarily commutative) and a computable subring $R_0$ of coefficients, *Hilbert's tenth problem over $R$ with ring of coefficients $R_0$* asks for an algorithm that decides, given a finite system of polynomial equations in noncommuting variables with coefficients in $R_0$, whether it has a solution in $R$; equivalently, whether a positive existential sentence in the language of rings with constants for $R_0$ is true in $R$. The problem *has a negative answer* when no such algorithm exists.

**Theorem (Eggink).**

1. Hilbert's tenth problem over $K\{\tau\}$ with ring of coefficients $\mathbb{F}_p\{\tau\}$ has a negative answer.
2. Hilbert's tenth problem over $K(\tau)$ with ring of coefficients $\mathbb{F}_p(\tau)$ has a negative answer.

(Theorem 1.2.2 of arXiv:2410.03485v1, clauses 1 and 2, proved as Theorems 6.1.7 and 6.2.8 there.)

The same paper shows that for $K = \mathbb{F}_{q^n}$ the recursively enumerable and the Diophantine subsets of $\mathbb{F}_{q^n}\{\tau\}$ coincide when the ring itself is the ring of coefficients, and reduces Hilbert's tenth problem over the twisted power series and Laurent series rings to that over $\mathbb{F}_q[[T]]$ and $\mathbb{F}_q((T))$.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Ring with identity](../../../Algebra/rings-and-fields/ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Give $K$ the structure of an $\mathbb{F}_q[T]$-field by an $\mathbb{F}_q$-algebra map $\psi : \mathbb{F}_q[T] \to K$, which may be chosen with $\psi(T) = 0$. The Carlitz module $\phi : \mathbb{F}_q[T] \to K\{\tau\}$, $\phi(T) = \psi(T) + \tau$, is an injective ring homomorphism whose image is the endomorphism ring $\{u : u \phi_T = \phi_T u\}$, a Diophantine set; addition and multiplication are preserved, so $\phi$ is an effective Diophantine map. Hilbert's tenth problem over $\mathbb{F}_q[T]$ (with a constant for $T$) has a negative answer by Denef's theorem, which transfers to $K\{\tau\}$ along $\phi$. For $K(\tau)$ the Carlitz module extends to the fraction field $\mathbb{F}_q(T)$, and the negative answer over $\mathbb{F}_q(T)$ (Pheidas for odd $p$, Videla for $p = 2$) transfers in the same way. A complete expansion links pages for the undecidability of Hilbert's tenth problem over $\mathbb{F}_q[T]$ and over $\mathbb{F}_q(T)$ with a constant for $T$, and for the description of the endomorphism ring of the Carlitz module, which have none on main.

## Sources

- A. Eggink, "Hilbert's tenth problem for some noncommutative rings", *Annals of Pure and Applied Logic* 177(8), 2026, article 103745, doi:[10.1016/j.apal.2026.103745](https://doi.org/10.1016/j.apal.2026.103745); read as arXiv:2410.03485v1 ([arXiv](https://arxiv.org/abs/2410.03485v1)): the definitions and Theorem 1.2.2 of the introduction, the definition of Hilbert's tenth problem over a ring with a language in Section 5, and Theorems 6.1.7 and 6.2.8 in Section 6, in the numbering of that version.
