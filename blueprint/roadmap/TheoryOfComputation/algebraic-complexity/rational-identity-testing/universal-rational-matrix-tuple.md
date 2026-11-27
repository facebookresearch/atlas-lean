# One explicit matrix tuple for bounded noncommutative formulas in characteristic zero

Fix $n,s\ge1$. Formulas over any field of characteristic zero are binary addition and ordered multiplication trees with scalar and variable leaves; size counts all nodes. A formula is nonzero if some word coefficient is nonzero, using word concatenation for multiplication. Put $d=1$ if $n=s=1$, and $d=2ns^2$ otherwise. For each variable index $i=0,\ldots,n-1$, take the rational $d\times d$ matrix $T_i=[1]$ in the special case and otherwise with entry $(-1)^{r-q-1}/(r(i+1)^{r-q})$ for $q<r$, zero for $q\ge r$, using zero-based indices. Every nonzero formula of size at most $s$ evaluates to a nonzero matrix at this tuple after mapping rationals into the coefficient field and scalars to scalar matrices. This claim is not over positive characteristic.

## Depends on

- Word convolution, syntax-tree size, and evaluation in square matrices at the displayed rational tuple.

## Proof depends on

- Noncancellation of the coefficient readout for the explicit triangular matrices.

## Expansion

Prove compatibility of the word expansion with matrix evaluation; isolate the word separation argument in the readout and check the one-variable one-node case directly.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FormulaHitting.lean#L57-L63) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FormulaHitting.lean).
