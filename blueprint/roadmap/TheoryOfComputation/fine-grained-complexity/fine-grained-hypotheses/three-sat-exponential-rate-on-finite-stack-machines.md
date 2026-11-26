# Zero infimum of deterministic 3-SAT rates on finite-stack machines

For a fixed $\delta\ge0$, let $\delta$ be admissible if there are one deterministic finite-stack machine and $c\in\mathbb N$ such that, for every $n\ge0$ and every width-three CNF on $n$ variables in the specified encoding with $k=3$ fixed, it halts within $\lfloor c 2^{\delta n}\rfloor$ steps and outputs a single bit that is 1 exactly when some assignment satisfies every clause. The infimum $s_3$ of admissible rates, in the extended nonnegative reals, is zero (the infimum of the empty set is $+\infty$). Equivalently the positive-rate hypothesis $0<s_3$ fails. Machines and constants may depend on the rate; this formulation does not itself assert one machine meeting every rate.

## Depends on

- [Binary CNF and machine conventions](binary-cnf-on-finite-stack-machines.md)

## Proof depends on

- [Uniform exact counting bound](exact-cnf-counting-on-finite-stack-machines.md)

## Proof outline

Specify the reductions from the counting bound, including small formulas and unused variables. To compare this rate with one in a different machine model, first prove a simulation and an encoding overhead estimate preserving the subexponential rate.

## Related formulations

The [ETH and SETH overview](exponential-time-hypothesis-and-strong.md) uses a word-RAM formulation. A separate [fixed-width multitape SAT theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubexponentialSAT.lean#L194-L219) suggests another route to the zero infimum: for width three, canonicalize the list clauses into finite sets without changing the variable universe, simulate the multitape machine on finite stacks, and convert its decision output to the single-bit output here. A polynomial simulation and encoding overhead would preserve the subexponential rate. The present statement does not include these translations or assert the negation of a hypothesis that specifically excludes a fixed power saving in the exponent.

## Sources

- Anthropic, [MainResults.ethIsFalse](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/Challenge.lean#L11-L13).
- [The infimum and decision bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/MainResults.lean#L92-L122).
