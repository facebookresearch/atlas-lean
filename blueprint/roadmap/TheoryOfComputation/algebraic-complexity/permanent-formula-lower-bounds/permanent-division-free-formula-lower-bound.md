# Division-free formula lower bound for the permanent

Let $n\ge32$ and let a division-free arithmetic formula with complex constants on the $n^2$ matrix entries evaluate symbolically to the permanent polynomial. Its number of variable leaves is at least $n^4/(128\log_2 n)$, with the comparison in the reals. This is a bound for formulas, not arbitrary arithmetic circuits.

## Depends on

- [Symbolic arithmetic formulas and variable-leaf size](symbolic-arithmetic-formulas.md)

## Expansion

Develop the affine specialization and the formula measure used in the lower bound. Check the relation between leaf count and the complexity of this specialization, and retain the finite-dimensional threshold and explicit denominator.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 5](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `permanent_divisionFree_formula_logarithmic_lower_bound`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/C_PermanentFormulaLowerBound.lean#L82-L87)
