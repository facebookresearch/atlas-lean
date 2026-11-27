# Shoup: deterministic construction of irreducible polynomials over GF(2)

For every odd prime $q$ an irreducible polynomial of degree $q$ over $\mathbb{F}_2$ can be constructed deterministically in time polynomial in $q$. (Shoup's general method constructs irreducible polynomials of any degree $d$ over $\mathbb{F}_p$ deterministically in time polynomial in $d$ and $p$.)

## Proof sketch

Factor the cyclotomic polynomial $\Phi_q$ over $\mathbb{F}_2$ with Berlekamp's algorithm to obtain the splitting field $K=\mathbb{F}_2(\zeta_q)$, of degree $m=\mathrm{ord}_q(2)$, and use factoring again to find a $q$-th power nonresidue $a\in K$ (Shoup's Theorem 3.1). Then $X^{q}-a$ is irreducible over $K$, giving an extension $E$ of degree $mq$ over $\mathbb{F}_2$; the trace from $E$ down to its subfield $\mathbb{F}_{2^{q}}$ yields an element of degree $q$ over $\mathbb{F}_2$, whose minimal polynomial is the output (Theorem 2.1). The running time is $O(p^{1/2}n^{4})$ operations up to logarithmic factors for degree $n$ over $\mathbb{F}_p$ (Theorem 3.2).

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Deterministic Berlekamp factorization over GF(2)](berlekamp-factorization-gf2.md)

## Sources

- Victor Shoup, "New Algorithms for Finding Irreducible Polynomials over Finite Fields", Mathematics of Computation 54(189), 435–447, 1990, Theorems 2.1, 3.1 and 3.2.
