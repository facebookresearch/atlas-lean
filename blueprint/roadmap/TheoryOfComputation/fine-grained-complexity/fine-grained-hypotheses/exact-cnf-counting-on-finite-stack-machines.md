# Uniform exact CNF counting on finite-stack Turing machines

There are one deterministic finite-stack machine, with every alphabet finite, and a natural number $C$ with the following property. For all $k\ge1$, $n\ge4$ and all width-$k$ CNF formulas on $n$ variables with $m\ge2$ clauses, no repeated clause, and every variable appearing in at least one literal, start the machine on the stated binary encoding including the unary prefix for $k$. It returns the number of satisfying assignments over **all** $2^n$ assignments, in exactly $n+1$ little-endian bits, within

$$
\left\lfloor 2^{C\min\{km/\sqrt{\log_2 m},\,k^2n\log_2\log_2 n/\sqrt{\log_2 n}\}}\right\rfloor
$$

steps, with the output and reset requirements of the machine model. The same machine and $C$ must serve every $k,n,m$ in this range. There is no promise about other input words.

## Depends on

- [Binary CNF and machine conventions](binary-cnf-on-finite-stack-machines.md)

## Expansion

Separate the recursive tensor-network contraction with counted steps and table queries from its realization as a padded solver. Prove the solver construction for machines satisfying the source's counted-operation and level hypotheses, including the cost of realizing table queries and individual steps on finite stacks. Then use that solver to derive both counting bounds and assemble one machine uniform in the width, with the stated input, exact output, and reset conventions. An arithmetic operation count alone does not bound finite-stack transitions.

## Related formulations

The [fixed-width multitape counting theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubexponentialSAT.lean#L194-L219) chooses a machine after fixing the width, uses a finite-set encoding, and gives separate count and decision outputs plus a visited-space bound. Its time bound is different. The uniform-in-width finite-stack result above gives neither that space bound nor a model translation.

## Sources

- Anthropic, [MainResults.mainTheorem](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/Challenge.lean#L15-L17).
- [Exact quantified counting specification](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/MainResults.lean#L107-L180).
- [The counted-operation route](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/Solution.lean#L11-L22) and [its padded solver and assembly](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/proof/maintheorem/CountedRoute/Main.lean#L18-L92).
