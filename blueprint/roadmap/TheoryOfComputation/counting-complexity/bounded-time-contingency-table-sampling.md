# Bounded-time almost-uniform contingency-table sampling

For nonnegative integer row and column margins $r,c$ of dimensions $m,n$ with equal total $R$, let $\Omega$ consist of all $m\times n$ natural matrices with those margins. There is one [eight-symbol fair-bit Post–Turing machine](eight-symbol-fair-bit-post-turing-machine.md) and fixed integers $C>0,d\ge0$. Its input concatenates the delimited binary natural codes for $m,n$ followed by the row margins in order, the column margins in order, then precision $k\ge1$. For every length-$t$ bit prefix, at $t=C(m+n+\lceil\log_2(R+1)\rceil+k+1)^d$ it is halted with the row-major encoded natural entries of a feasible table on its right tape including the scanned cell. With $p_t(X)$ the uniform fraction of these prefixes halted with exactly this padded encoding of $X$, $\tfrac12\sum_{X\in\Omega}|p_t(X)-|\Omega|^{-1}|\le2^{-k}$.

## Depends on

- [Exact machine tick, absorbing halt, and right-tape matrix output](eight-symbol-fair-bit-post-turing-machine.md)
- Contingency-table set, delimited binary margin and row-major output encodings, and finite-prefix total variation on feasible outputs.

## Expansion

State the finite-box Prékopa–Leindler input and the finite-chain Cheeger estimate as separate results on the precise box and chain interfaces used by the arbitrary-margin sampler. They are shared with the exact sampler and bounded-cell counter. Use them to control the sampler distribution; the worst-case truncation, feasible fallback, and all-tape cost belong to this endpoint.

## Proof outline

Separate feasibility and table-encoding lemmas, quality of the sampling law, and the deterministic time cutoff. Handle zero dimensions and equal zero totals without conditioning on a nonempty output tape.

## Sources

- [Comparator statement: `OAI.ContingencyTables.boundedSampling`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L210-L212)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/115.md)
- [Margins, encoding, precision, and fixed-time law](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L103-L160)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ContingencyTables/UnconditionalMain.lean)
