# Polynomial Calculus Resolution cannot efficiently prove algebraic circuit lower bounds

Garlík, Gryaznov, Lu, Santhanam and Tzameret prove that refuting the statement that a polynomial $f$ has a small algebraic circuit requires superpolynomially many monomials in Polynomial Calculus Resolution over $\mathbb{F}_2$, for every $f$ once the size bound is a large enough polynomial.

For a polynomial $f(\bar{u})$ in $n$ variables, a size $s$ and a degree bound $\ell$, $\mathrm{lb}(f, s, \ell)$ is the polynomial system whose variables encode, for each of $s$ gates, its type (variable, constant, $+$ or $\times$), its inputs and the coefficient vector over all $N$ monomials of degree at most $\ell$ of the polynomial it computes, and whose axioms force the encoded object to be an algebraic circuit of size $s$ and syntactic degree $\ell$ computing $f$; its size is $\mathrm{poly}(s, n, N^\ell)$. A refutation of $\mathrm{lb}(f, s, \ell)$ is thus a proof that $f$ has no such circuit.

**Theorem.** There is a constant $c > 0$ such that for every polynomial $f$ of degree at most $\ell$ over $\mathbb{F}_2$ in $n$ variables and every $s \ge (\ell n)^c$, every $\mathsf{PCR}_{\mathbb{F}_2}$ refutation of $\mathrm{lb}(f, s, \ell)$ requires superpolynomially many monomials.

## Expansion

The proof reduces the negation of the iterated weak rank principle, that an $m \times m$ matrix of rank greater than $n$ cannot be written as a product of an $m \times n$ and an $n \times m$ matrix, to $\mathrm{lb}(f, s, \ell)$: under a substitution, every axiom of $\mathrm{lb}(f, s, \ell)$ has a short $\mathsf{PCR}$ derivation from the iterated rank axioms, so a short refutation of $\mathrm{lb}$ would give a short refutation of the rank system, which is known to be hard for $\mathsf{PCR}$ over $\mathbb{F}_2$. This is the first unconditional hardness result for proving an algebraic circuit lower bound and a weak algebraic analogue of the Krajíček–Razborov conjecture; in contrast, the rank-based constant-depth lower bounds for the Permanent are provable in $\mathsf{VNC}^2$.

## Depends on

- [Arithmetic circuits](../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

None.

## Sources

- Michal Garlik, Svyatoslav Gryaznov, Jiaqi Lu, Rahul Santhanam and Iddo Tzameret, "Meta-Mathematics of Algebraic Complexity", *LICS* 2026, DOI 10.4230/LIPIcs.LICS.2026.49, arXiv:2610.33938v1 (Theorem 1.2, Section 1.2; definition of lb(f, s, ell) and proof in Section 3).
