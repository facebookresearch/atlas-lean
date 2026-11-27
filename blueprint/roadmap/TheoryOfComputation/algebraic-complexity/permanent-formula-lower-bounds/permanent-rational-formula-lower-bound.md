# Rational formula lower bound for the permanent

Let $n\ge32$ and let a valid rational arithmetic formula with complex constants agree in the fraction field with the image of the $n\times n$ permanent polynomial. Validity requires a nonzero symbolic denominator at each division. Its number of variable leaves is at least $n^4/(192\log_2 n)$, with the comparison in the reals.

## Depends on

- [Symbolic arithmetic formulas and variable-leaf size](symbolic-arithmetic-formulas.md)

## Expansion

Verify compatibility of symbolic division and the formula lower-bound argument, including degeneracy of denominators on specializations. The result is not a determinant representation bound or a lower bound in an arbitrary circuit model.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 5](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `permanent_rational_formula_logarithmic_lower_bound`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/C_PermanentFormulaLowerBound.lean#L90-L99)
