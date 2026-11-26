# FPRAS for counting cell-bounded contingency tables

Let $m,n>0$, let $r,c$ be natural row and column margins with equal totals, and give each cell a natural bound $b_{ij}$. Let $Z$ count the natural tables with these margins and $X_{ij}\le b_{ij}$. There is one [eight-symbol fair-bit Post–Turing machine](eight-symbol-fair-bit-post-turing-machine.md), with fixed integers $C>0,d\ge0$. Input gives the delimited natural codes for $m,n$, row margins, column margins and row-major cell bounds, followed by the fixed signed-numerator/positive-denominator encodings of rationals $0<\varepsilon,\delta<1$. For every length-$t$ prefix with $t=C(L+\lceil\varepsilon^{-1}\rceil+\lceil\log_2\lceil\delta^{-1}\rceil\rceil+1)^d$ and $L$ the full encoded length, the machine is halted with the exact padded right-tape encoding of a nonnegative rational $q$ (the right tape includes the scanned cell). If $Z=0$, every prefix outputs the encoding of zero. At least a uniform fraction $1-\delta$ of the prefixes produce $q\in[(1-\varepsilon)Z,(1+\varepsilon)Z]$.

## Depends on

- [Exact absorbing fair-bit transitions and right-tape rational output](eight-symbol-fair-bit-post-turing-machine.md)
- Cell-bounded table count, binary encoded bounds, and finite-alphabet bounded fair-bit execution.

## Expansion

Separate the finite-box Prékopa–Leindler and finite-chain Cheeger inputs shared with the two samplers, and the augmenting-path bound used for bounded-cell feasibility. Then prove this counting reduction, its zero-return branch, and its encoding/cost budget.

## Proof outline

Separate feasibility (including zero bounds), counting reduction, and finite-tape runtime/accuracy checks. Keep the equal-total assumption even though unequal totals would make the count zero.

## Sources

- [Comparator statement: `OAI.ContingencyTables.counting`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L216-L218)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/115.md)
- [Input and exact halted output conventions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L106-L143)
- [Bounded table count, tick budget and accuracy events](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L176-L207)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ContingencyTables/UnconditionalMain.lean)
