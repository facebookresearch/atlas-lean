# Counting satisfying assignments has interactive proofs

The language $\{\langle \varphi, k\rangle : \varphi \text{ is a CNF formula with exactly } k \text{ satisfying assignments}\}$ has an interactive proof with a probabilistic polynomial-time verifier. For $\varphi$ with $n$ variables and $m$ clauses, the verifier rejects if $k > 2^n$; otherwise the prover sends a prime $q$ with $Q < q \le 2Q$ for $Q = \max(2^n, 3nm)$, which exists by Bertrand's postulate and has polynomially many bits, and the verifier checks these bounds and the primality of $q$ deterministically in polynomial time and rejects if either check fails, so that $k < q$; the formula is first normalized by removing repeated literals from each clause and deleting every clause that contains a variable together with its negation, which changes neither the satisfying assignments nor the bound $m$; after that each variable occurs at most once in each clause. The clause $C$ is arithmetized as $1 - \prod_{\ell \in C} (1 - \hat\ell)$ with $\hat x = x$ and $\widehat{\neg x} = 1 - x$, and $\varphi$ as the product $g$ of its clauses, a polynomial of degree at most $m$ in each variable whose sum over $\{0,1\}^n$ is the number of satisfying assignments modulo $q$, hence the number itself since $q > 2^n$. Running the sum-check protocol on $g$ over $\mathbb{F}_q$ gives perfect completeness and soundness error at most $nm/q < 1/3$.

## Depends on

- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Proof depends on

- [The sum-check protocol](the-sum-check-protocol.md)
- [PRIMES is in P](../../polynomial-time-problems/aks-primality-test/primes-in-p.md)

## Expansion

This page becomes ready once:

- Bertrand's postulate, that there is a prime between $Q$ and $2Q$ for every $Q \ge 1$ (proof prerequisite; not yet stated)

## Sources

- C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic methods for interactive proof systems", *Journal of the ACM* 39(4):859–868, 1992, <https://lance.fortnow.com/papers/files/ip.pdf>
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
