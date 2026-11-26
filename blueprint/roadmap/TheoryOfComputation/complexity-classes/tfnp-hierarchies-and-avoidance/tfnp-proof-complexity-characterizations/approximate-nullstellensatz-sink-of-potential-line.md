# Approximate Nullstellensatz lower bound for the sink-of-potential-line formulas via approximate degree of OR

An **$\epsilon$-approximate Nullstellensatz** ($\epsilon$-NS) refutation of equations $a_i=0$ over $\mathbb R$ is a family $p_i$ with $\sum_ip_i(x)a_i(x)\in[1-\epsilon,1+\epsilon]$ for all $x\in\{0,1\}^n$. Let $\mathrm{SoPL}_n$ be the CNF encoding of SINK-OF-POTENTIAL-LINE on the $n\times n$ grid. Every $\tfrac12$-NS refutation of $\mathrm{SoPL}_n$ has degree $n^{\Omega(1)}$. Moreover, for any field $\mathbb F$, every $\mathbb F$-NS refutation of $\mathrm{SoPL}_n$ has degree $n^{\Omega(1)}$.

## Proof sketch

A randomized decision-to-search reduction embeds an instance $z$ of $\mathrm{OR}$ on $n^{\Omega(1)}$ bits into a random $\mathrm{SoPL}_n$ instance so that every solution of the search problem reveals whether $z$ is all-zero; a low-degree $\epsilon$-NS refutation would then yield an approximating polynomial for OR of degree $O(k\log n)$, contradicting the $\Omega(\sqrt n)$ approximate degree of OR. The field-independent bound follows instead from the intersection theorem: a low-degree $\mathbb F$-NS refutation together with the easy Resolution refutation would place the problem in a class it is known not to lie in.

## Depends on

- [Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas](unary-nullstellensatz-and-unary-sherali-adams.md)

## Proof depends on

- [Reversible Resolution: a MaxSAT-style fragment of Resolution with consumed premises](reversible-resolution.md)
- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Intersection theorems: Reversible Resolution is the intersection of Resolution and unary Sherali–Adams](reversible-resolution-intersection-theorem.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
