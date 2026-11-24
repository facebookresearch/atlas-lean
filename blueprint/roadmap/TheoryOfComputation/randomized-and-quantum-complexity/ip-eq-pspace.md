# IP = PSPACE (Shamir)

The class $\mathsf{IP}$ of decision problems that have
interactive proofs (a polynomial-time verifier using polynomially many rounds and random coins,
with completeness at least $2/3$ and soundness at most $1/3$ against every prover) equals the
class $\mathrm{PSPACE}$ of decision problems whose languages are decided by multi-tape Turing
machines in polynomial space.

## Informally uses

- [TQBF is PSPACE-complete](../completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md):
  the interactive proof is given for true quantified Boolean formulas, and every problem in PSPACE
  reduces to them.

## Background

- [Zero-knowledge proofs](../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-proofs/README.md):
  interactive proofs were introduced by Goldwasser, Micali and Rackoff together with zero knowledge;
  the graph-isomorphism protocol there is a three-message example.
- [Goldwasser–Sipser theorem](goldwasser-sipser-theorem/README.md): private and public coins give
  the same languages, so the class here does not depend on hiding the verifier's coins.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Internet draft dated January
  2007 (a pre-publication draft), Theorem 8.17 and Section 8.5 (the protocol for TQBF).
- A. Shamir, "IP = PSPACE", Journal of the ACM 39 (1992), 869-877 (FOCS 1990); see also C. Lund, L. Fortnow, H. Karloff, and N. Nisan, "Algebraic methods for interactive proof systems", Journal of the ACM 39 (1992), 859-868.
