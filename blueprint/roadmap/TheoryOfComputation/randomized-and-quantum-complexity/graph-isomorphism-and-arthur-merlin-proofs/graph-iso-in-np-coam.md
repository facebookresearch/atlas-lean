# Graph isomorphism is in NP and coAM

Consider the decision problem of directed graph isomorphism: on the bitstring encoding of a triple
$(n, E_1, E_2)$, where $n \in \mathbb{N}$ and $E_1, E_2$ are finite lists of pairs of natural numbers,
it answers whether some bijection $f$ of $\{0, \dots, n - 1\}$ satisfies
$(a, b) \in E_1 \iff (f(a), f(b)) \in E_2$ for all $a, b < n$; it rejects bitstrings that encode no
such triple. This decision problem belongs to NP and to coAM.

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", *Journal of the ACM* 38 (1991), 690–728, DOI 10.1145/116825.116852 (the interactive proof for graph non-isomorphism).
- S. Goldwasser and M. Sipser, "Private coins versus public coins in interactive proof systems", *Proceedings of the Eighteenth Annual ACM Symposium on Theory of Computing (STOC 1986)*, 59–68 (public coins suffice, which places graph non-isomorphism in AM).
- J. Köbler, U. Schöning and J. Torán, *The Graph Isomorphism Problem: Its Structural Complexity*, Birkhäuser, 1993.
