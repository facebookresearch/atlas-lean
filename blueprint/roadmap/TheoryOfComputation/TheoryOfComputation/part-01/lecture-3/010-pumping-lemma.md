---
article_id: af_d3eb332889083ce0d07e5083
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: RegularLanguages.pumping_lemma
---

# Pumping Lemma

For every regular language $A$, there is a number $p$ (the pumping length) such that if $s \in A$ and $|s| \geq p$ then $s = xyz$ where (1) $xy^i z \in A$ for all $i \geq 0$, (2) $y \neq \varepsilon$, (3) $|xy| \leq p$.

## Depends on

- [Definition (Regular language)](../lecture-1/008-regular-language.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 3](../../../../../sources/v1/TheoryOfComputation.md)
