# Symbolic arithmetic formulas and variable-leaf size

A formula is a binary expression tree with leaves labelled by input variables or field constants. Its nodes apply $+$, $-$ or $\times$; rational formulas also have $/$. A repeated occurrence has its own place in the tree, even if two subtrees denote the same expression. The size here is the number of variable-leaf occurrences, counting constants as zero. Division-free evaluation is in the polynomial ring on the inputs. Rational evaluation takes place in its fraction field and is valid only if every divisor subtree evaluates to a nonzero element of that field. This need not mean the divisor is nonzero at every point.

For an $n\times n$ array of distinct variables $(x_{ij})$ the permanent polynomial is $\sum_{\sigma\in S_n}\prod_i x_{i,\sigma(i)}$.

## Expansion

Extend arithmetic syntax with a tree model that records occurrences and a fraction-field evaluation with a recursive division-validity predicate. Relate division-free trees to circuit evaluation, but do not substitute gate count in a shared circuit for the variable-leaf count.

## Sources

- [Pinned formula, evaluation, validity, and target](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/C_PermanentFormulaLowerBound.lean#L7-L80)
