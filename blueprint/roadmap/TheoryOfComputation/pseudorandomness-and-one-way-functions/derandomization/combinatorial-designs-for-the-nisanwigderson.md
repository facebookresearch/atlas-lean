# Combinatorial designs for the Nisan–Wigderson generator

Let $\ell, n, a$ be positive integers. An $(\ell, n, a)$-design is a family of sets $S_1, \dots, S_m \subseteq \{1, \dots, \ell\}$ with $|S_i| = n$ for every $i$ and $|S_i \cap S_j| \le a$ for $i \ne j$; $m$ is its size. If $n > a$ and $\ell > 10 n^2 / a$, an $(\ell, n, a)$-design of size $\lfloor 2^{a/10} \rfloor$ exists and can be computed by a greedy search in time $2^{O(\ell)}$.

## Sources

- N. Nisan and A. Wigderson, "Hardness vs randomness", *Journal of Computer and System Sciences* 49(2):149–167, 1994
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2006-09-28, Section 17.2.2 (Definition 17.17 and Lemmas 17.18 and 17.19); published by Cambridge University Press, 2009
