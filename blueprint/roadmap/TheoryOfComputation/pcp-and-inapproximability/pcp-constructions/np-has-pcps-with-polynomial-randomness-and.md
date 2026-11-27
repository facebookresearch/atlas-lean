# NP has PCPs with polynomial randomness and constantly many queries

**Theorem.** $\mathsf{NP} \subseteq \mathsf{PCP}(\mathrm{poly}(n), O(1))$: every language in $\mathsf{NP}$ has a probabilistically checkable proof verifier that uses polynomially many random
bits, reads a constant number of bits of the proof, accepts with probability $1$ on correct proofs of true instances, and rejects false instances with probability
at least $1/2$.

The verifier is designed for the NP-complete language QUADEQ of satisfiable systems $AU = b$ of quadratic equations over $\mathrm{GF}(2)$ in variables
$u_1, \dots, u_n$, where $U = u \otimes u$. The proof consists of the Walsh–Hadamard encodings of $u$ and of $u \otimes u$, which have exponential length, and the verifier
checks them with linearity tests, self-correction, a test that the second encoding is the tensor square of the first, and a random linear combination of the
equations.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Proof depends on

- [Blum–Luby–Rubinfeld linearity test](../blum-luby-rubinfeld-linearity-test/blr-test.md)
- [QUADRATIC EQUATIONS OVER GF[2] is NP-complete](../../np-completeness/satisfiability/polynomial-equations-over-gf-2/quadratic-equations-over-gf2-np-complete.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 18.1, Section 18.4, Theorem 18.21 and its proof in Section 18.4.2 (QUADEQ, Figure 18.2), Theorem 18.23 (linearity testing), and the exercise asking to show that QUADEQ is NP-complete.
