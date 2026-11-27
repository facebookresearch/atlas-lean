# MIP* is contained in RE

Every language $L \in \mathrm{MIP}^*$ is recursively enumerable: there is a Turing machine that halts on input $z$ if and only if $z \in L$.

## Proof sketch

Given $z$, enumerate all dimensions $d$ and all strategies with algebraic (or rational, then approximately normalized) entries in a dense countable set, compute their values on $G_z$ to increasing precision, and halt as soon as some strategy is certified to have value strictly above $1/2$. If $z \in L$ then $\omega^*(G_z) = 1$, so some finite-dimensional strategy exceeds $1/2$ and the search halts; if $z \notin L$ every strategy has value below $1/2$ and the search never halts.

## Depends on

- [The class MIP* of languages with entangled two-prover proofs](the-class-mip-star.md)

## Proof depends on

- [The halting problem is recognizable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
