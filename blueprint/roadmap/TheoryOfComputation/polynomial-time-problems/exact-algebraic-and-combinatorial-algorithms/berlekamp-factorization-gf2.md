# Deterministic Berlekamp factorization over GF(2)

Every polynomial $f\in\mathbb{F}_2[x]$ of degree $d$ can be factored into irreducibles by a deterministic algorithm in time polynomial in $d$. In particular irreducibility over $\mathbb{F}_2$ is decidable in polynomial time.

## Proof sketch

After removing repeated factors via $\gcd(f,f')$ (when $f'=0$, $f$ is a square $g^2$ in $\mathbb{F}_2[x]$ and one factors $g$), the Berlekamp subalgebra $\{g : g^{2}\equiv g\pmod f\}$ is the kernel of $Q-I$ for the Frobenius matrix $Q$; its dimension is the number of irreducible factors, and for an element $g$ of the subalgebra that is not a constant, $f=\gcd(f,g)\cdot\gcd(f,g+1)$ is a nontrivial splitting because $g(g+1)\equiv0\pmod f$; refining with all basis elements yields the complete factorization. Since the field has two elements, trying both constants is deterministic, and the linear algebra is over $\mathbb{F}_2$.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [XOR-SAT is solvable by Gaussian elimination over GF(2)](../two-sat-and-xor-sat-algorithms/xor-sat-gaussian-elimination.md)

## Sources

- Elwyn R. Berlekamp, "Factoring Polynomials over Finite Fields", Bell System Technical Journal 46(8), 1853–1859, 1967.
