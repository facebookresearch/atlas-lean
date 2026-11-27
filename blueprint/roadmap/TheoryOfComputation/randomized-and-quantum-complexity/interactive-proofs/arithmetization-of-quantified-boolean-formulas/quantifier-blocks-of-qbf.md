# Quantifier blocks and prenex $\Sigma_k$ quantified Boolean formulas

For lists of variables $B_1,\dots,B_k$ and a quantified Boolean formula $\varphi$, the formula $Q_1 B_1\, Q_2 B_2 \cdots Q_k B_k\, \varphi$ alternates existential and universal blocks ($Q_1 = \exists$ for $\Sigma_k$ form, $Q_1 = \forall$ for $\Pi_k$ form). Its truth under an assignment is the alternating quantification over words: $\exists B$ holds iff some assignment of a word of truth values to the list $B$ (later occurrences overriding earlier ones) makes the rest true. The value of a quantified formula depends only on its free variables, so closed formulas have a definite truth value.

## Depends on

- [Evaluation of a quantified CNF formula](../../../completeness-other-classes/true-quantified-boolean-formulas/eval-qbf.md)

## Sources

- L. J. Stockmeyer and A. R. Meyer, "Word Problems Requiring Exponential Time", Proceedings of the 5th ACM Symposium on Theory of Computing (STOC), 1–9, 1973.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapters 4–5.
