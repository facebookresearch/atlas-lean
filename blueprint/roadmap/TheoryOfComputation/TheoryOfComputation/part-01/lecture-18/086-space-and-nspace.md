---
article_id: af_d1766e49a389f5030f5eea33
declaration: def
origin: cited
statement: formalized
lean: SpaceComplexity.InSPACE
---

# Definition (SPACE and NSPACE)

Let $f \colon \mathbb{N} \to \mathbb{N}$ where $f(n) \geq n$. Say TM $M$ runs in space $f(n)$ if $M$ always halts and uses at most $f(n)$ tape cells on all inputs of length $n$. An NTM $M$ runs in space $f(n)$ if all branches halt and each branch uses at most $f(n)$ tape cells on all inputs of length $n$. $\mathsf{SPACE}(f(n)) = \{B \mid \text{some 1-tape TM decides } B \text{ in space } O(f(n))\}$. $\mathsf{NSPACE}(f(n)) = \{B \mid \text{some 1-tape NTM decides } B \text{ in space } O(f(n))\}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition (SPACE complexity)](../lecture-17/064-space-complexity.md)
- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 18, Review: SPACE Complexity](../../../../../sources/v1/TheoryOfComputation.md)
