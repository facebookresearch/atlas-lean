# NP has PCPs with polynomial randomness and constantly many queries

$\mathsf{NP} \subseteq \mathsf{PCP}(\mathrm{poly}(n), O(1))$: every language in $\mathsf{NP}$ has a probabilistically checkable proof verifier that uses polynomially many random bits, reads a constant number of bits of the proof, accepts with probability $1$ on correct proofs of true instances, and rejects false instances with probability at least $1/2$. The proof encodes a satisfying assignment $u$ of an NP-complete system of quadratic equations over $\mathbb{F}_2$ by the Walsh–Hadamard codes of $u$ and of $u \otimes u$, and checks them with linearity tests, self-correction and a consistency test.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Proof depends on

- [Blum–Luby–Rubinfeld linearity test](../blum-luby-rubinfeld-linearity-test/blr-test.md)
- [CLIQUE is NP-complete](../../np-completeness/graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/clique-dec-np-complete.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, <https://theory.cs.princeton.edu/complexity/>, Theorem 18.21
