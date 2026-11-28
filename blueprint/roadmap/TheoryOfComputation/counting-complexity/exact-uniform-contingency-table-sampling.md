# Exact expected-polynomial-time contingency-table sampling

For natural row and column margins $r,c$ of lengths $m,n$ with common total $R$, let $\Omega$ be the natural matrices with those margins. One fixed [eight-symbol fair-bit Post–Turing machine](eight-symbol-fair-bit-post-turing-machine.md) takes the delimited natural codes for $m,n$, then the row margins and the column margins in order, without a precision parameter. At every time $t$ and on every length-$t$ prefix with absent control state, the right tape including the scanned cell equals the blank-padded row-major encoding of some table in $\Omega$. For each $X\in\Omega$ the fraction of length-$t$ prefixes halted with that padded encoding tends to $1/|\Omega|$, and the total fraction $h_t$ halted tends to one. The tail series $\sum_{t\ge0}(1-h_t)$ converges and is at most $C(m+n+\lceil\log_2(R+1)\rceil+1)^d$ for fixed integers $C>0,d\ge0$. The machine is chosen once; only the bit prefixes are random.

## Depends on

- [Exact execution, absorbing halt, and padded right-tape matrix encoding](eight-symbol-fair-bit-post-turing-machine.md)
- Finite set of integer tables, halted-output event under absorbing halt, and expected time as the tail sum.

## Expansion

State the same finite-box Prékopa–Leindler and finite-chain Cheeger inputs as the bounded-time sampler, without replacing either by a numerical mixing assertion for this one machine. Use them in the exact sampling proof, where stopping-law summability and expected charged bit cost are local to the construction.

## Proof outline

State the exact distribution and expected-time lemmas separately. Connect summability and tail budget to execution time without substituting a worst-case bound or dropping the configurations that have not halted yet.

## Sources

- [Comparator statement: `OAI.ContingencyTables.exactSampling`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L213-L215)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/115.md)
- [Sampling input, halt masses, and the expected-time statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L103-L174)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ContingencyTables/UnconditionalMain.lean)
