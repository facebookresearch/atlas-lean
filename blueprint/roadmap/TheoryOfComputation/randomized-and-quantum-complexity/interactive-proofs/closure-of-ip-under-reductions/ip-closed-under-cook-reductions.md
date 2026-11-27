# IP is closed under polynomial-time Turing reductions

If $L \le_T^p L'$ and $L' \in \mathsf{IP}$, then $L \in \mathsf{IP}$. Here $\mathsf{IP}$ is the class of languages with an interactive proof system in which a probabilistic polynomial-time verifier accepts members with probability at least $2/3$ and accepts non-members with probability at most $1/3$ against every prover. No hypothesis on the complement of $L'$ is needed.

## Proof sketch

Since $\mathsf{IP} = \mathsf{PSPACE}$ and $\mathsf{PSPACE}$ is closed under complement and under polynomial-time Turing reductions, both $L'$ and its complement have interactive proofs. The verifier for $L$ runs the reduction, and for each query asks the prover for the answer and then runs (with error reduced by repetition) an interactive proof for that answer, membership or non-membership; a union bound over the polynomially many queries controls the error.

## Depends on

- [Polynomial-time Turing (Cook) reduction](polynomial-time-turing-reduction.md)
- [Interactive-proof game](../../../complexity-classes/time-and-space-complexity-classes/ipgame.md)

## Proof depends on

- [IP = PSPACE (Shamir)](../../ip-eq-pspace.md)
- [Error reduction for BPP](../../bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
