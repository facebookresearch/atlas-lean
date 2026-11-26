# Short PCPs with projection queries for nondeterministic time

For every language $L \in \mathrm{NTIME}[T(n)]$ with $T(n) \ge n$ there is a probabilistically checkable proof system in which the verifier, on input $x$ of length $n$, uses $\log T(n) + O(\log\log T(n))$ random bits, reads $\operatorname{polylog}(T(n))$ proof bits, has perfect completeness and soundness $1/2$, and has **projection queries**: the positions it reads, as functions of the random string, are computable by circuits in which each output bit of the query address is a projection (or negation of a projection) of the random bits and the input index. The proof length is $T(n)\operatorname{polylog}(T(n))$.

## Proof sketch

Start from a quasi-linear-size PCP of proximity for circuit satisfiability based on Reed-Solomon codes over additive subgroups of binary fields. Choosing the evaluation domains as subspaces of $\mathbb{F}_2^m$ with coordinates aligned to the random bits makes every query address an affine, and after re-encoding a projection, function of the randomness, which is what the algorithmic method needs to check PCP queries with simple circuits.

## Proof depends on

- [The PCP theorem: NP = PCP(O(log n), O(1))](../../pcp-and-inapproximability/pcp-theorem.md)

## Sources

- E. Ben-Sasson, E. Viola, "Short PCPs with projection queries", ICALP (2014).
- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
