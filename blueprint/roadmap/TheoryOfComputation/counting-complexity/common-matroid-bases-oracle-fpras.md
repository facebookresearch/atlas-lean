# Independence-oracle FPRAS for common matroid bases

There exist a finite control program and constants $C>0,d\ge0$ for the following task. Take an $n$-point enumerated ground set, two matroids each with that full ground set and rank $r$, exact independence oracles on their $n$-bit subset masks, and rationals $0<\varepsilon,\delta<1$. Put $Z$ equal to the number of common bases. Write $L$ for six plus the total binary lengths of $n,r$ and the reduced numerator magnitudes and denominators of $\varepsilon,\delta$. Use $B=C(1+n+L+\lceil\varepsilon^{-1}\rceil+\lceil\log_2\lceil\delta^{-1}\rceil\rceil)^d$. At step $B$ on **every** bit stream there is a nonnegative rational output, with both oracle calls and charged bit operations at most $B$ and with output zero if $Z=0$. At least a fraction $1-\delta$ of the $2^B$ bit prefixes yield an output in $[(1-\varepsilon)Z,(1+\varepsilon)Z]$.

The program uses finitely many states and $k+8$ bit stacks for one fixed natural $k$. It starts at state zero, with the six little-endian input numerals in registers 0–5 in the order used in $L$ (including $n,r$ first), and empty remaining registers. In one instruction it either pushes a fixed bit, pops and branches on empty/zero/one, branches on the current stream bit, queries one selected oracle on one selected register, or halts. Push, pop and coin each charge one bit operation. A query on a register of length $n$ asks independence of the subset encoded in register order, increments oracle calls by one, and branches on the reply. A query on a register of the wrong length sets output to zero without an oracle call. Both query branches charge the register length plus $n+1$ bit operations. Halt sets the output to the quotient of the unsigned little-endian values of registers 6 and 7, with rational division by zero equal to zero, and charges their lengths plus one. Once the output is present, the configuration is absorbing. The bit presented to a step is indexed by the step, even if that instruction ignores it. The finite-prefix probability uses extension by false bits (no effect on the first $B$ steps).

## Depends on

- Oracle answers are exactly the two `Matroid.Indep` predicates, and every accepted mask describes one subset of the full enumerated ground set.
- Matroid ground set, rank and bases; a finite program with push, pop, coin, oracle-query and halt instructions, with query masks charged by length and rational output decoded from two binary stacks.

## Expansion

Separate the abstract exact-oracle fair experiment for common bases, including concentration and zero count, from its compiled execution. The physical-bit transfer must recover the same uniform law for bounded observables on the fair word embedded in the execution tape, not just one observed success event. Supply the exact independence-query and resource interfaces before using the two facts in the final FPRAS.

## Proof outline

Prove the common-base counting estimate separately from the finite register implementation; formalize query length and binary-output charging precisely, including the zero-return convention for malformed queries. No value-oracle polymatroid generalization is asserted.

## Sources

- [Comparator statement: `OAI.common_bases_fpras`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CommonBasesFPRAS.lean#L128-L130)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/114.md)
- [Oracle semantics, stack machine, per-instruction charges and initial registers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CommonBasesFPRAS.lean#L7-L106)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/MatroidCounting/CommonBases.lean)
