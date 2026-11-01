---
article_id: af_f973d707bfe6efea0438d3f8
declaration: def
origin: cited
statement: formalized
lean: SpaceComplexity.LADDER_DFA
---

# Definition ($LADDER_{DFA}$)

A ladder is a sequence of strings of a common length where consecutive strings differ in a single symbol. A ladder in a language $A$ is a ladder of strings in $A$. $\mathrm{LADDER}_{\mathrm{DFA}} = \{\langle B, u, v \rangle \mid B \text{ is a DFA and } L(B) \text{ contains a ladder } y_1, y_2, \ldots, y_k \text{ where } y_1 = u \text{ and } y_k = v\}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 17, Example: Ladder Problem section](../../../../../sources/v1/TheoryOfComputation.md)
