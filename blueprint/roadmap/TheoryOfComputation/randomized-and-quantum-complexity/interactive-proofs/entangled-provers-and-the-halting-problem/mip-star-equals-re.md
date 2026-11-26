# MIP* = RE (Ji, Natarajan, Vidick, Wright, Yuen)

$\mathrm{MIP}^* = \mathrm{RE}$. Equivalently, the class of languages decided by a classical polynomial-time verifier interacting in one round with two non-communicating provers who share finite-dimensional entanglement, with completeness $1$ and soundness $1/2$, is exactly the class of recursively enumerable languages.

## Proof sketch

The containment $\subseteq$ is the enumeration argument. For $\supseteq$, the halting problem is RE-complete under computable many-one reductions, and the reduction $M \mapsto G_M$ is computable by a polynomial-time uniformly generated verifier on input the description of $M$. Hence every RE language reduces to the gap problem for entangled values, which lies in $\mathrm{MIP}^*$.

## Depends on

- [The class MIP* of languages with entangled two-prover proofs](the-class-mip-star.md)

## Proof depends on

- [MIP* is contained in RE](mip-star-is-contained-in-re.md)
- [The halting problem reduces to the entangled value gap problem](halting-problem-reduces-to-entangled-value-gap.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
