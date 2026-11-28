# Two-counter machines are universal

For every Turing machine $M$ there is a machine with two counters (registers over $\mathbb{N}$ with increment, decrement and test for zero) that, started with both counters at $0$, halts if and only if $M$ halts on the blank tape; more generally every partial computable function $f$ is computed by a two-counter machine that maps the counter value $2^x$ to $2^{f(x)}$. Consequently the halting problem for two-counter machines started with zero counters is undecidable.

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

This page becomes ready once:

- Register machines compute exactly the partial recursive functions (proof prerequisite; not yet stated)
- K counters are simulated by two counters holding 2^{a_1} 3^{a_2} \cdots p_k^{a_k}, with each operation implemented by multiplication and division loops (proof prerequisite; not yet stated)
- The input-output convention 2^x ↦ 2^{f(x)} must be checked against the cited source

## Sources

- M. L. Minsky, *Computation: Finite and Infinite Machines*, Prentice-Hall, 1967
- M. L. Minsky, "Recursive unsolvability of Post's problem of 'Tag' and other topics in theory of Turing machines", *Annals of Mathematics* 74(3):437–455, 1961
