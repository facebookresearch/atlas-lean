# Semifilters and semifilter (fusion) covers

Let $U$ be a set. A *semifilter* on $U$ is a monotone predicate $F$ on subsets of $U$ with $F(U)$ true and $F(\emptyset)$ false (intersection-closure is not required). Fix a target set $T\subseteq U$ and supplied sets $S_1,\dots,S_n\subseteq U$. A *witness* is a pair $(u,F)$ with $u\in T$ and $F$ a semifilter on $U\setminus T$ that accepts the restriction of every supplied set containing $u$. A pair $(A,B)$ of subsets *defeats* a witness $(u,F)$ if $u\in A\cap B$, $F$ accepts both $A\setminus T$ and $B\setminus T$, and $F$ rejects $(A\cap B)\setminus T$. A *pair cover* of $(T;S_1,\dots,S_n)$ is a family of pairs defeating every witness; the *cover complexity* is the least length of a pair cover.

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
- Igor Carboni Oliveira, "Notes on the Method of Approximations and the Emergence of the Fusion Method", 2018.
- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", Electronic Colloquium on Computational Complexity, 2025.
