---
article_id: af_9119576fd933a99365643e50
declaration: theorem
origin: cited
statement: formalized
lean: SpaceComplexity.space_hierarchy_theorem
---

# Theorem (Space Hierarchy Theorem)

For any $f \colon \mathbb{N} \to \mathbb{N}$ (where $f$ satisfies a technical condition) there is a language $A$ where $A$ requires $O(f(n))$ space, i.e., (1) $A$ is decidable in $O(f(n))$ space, and (2) $A$ is not decidable in $o(f(n))$ space. In other words, $\mathsf{SPACE}(o(f(n))) \subsetneq \mathsf{SPACE}(f(n))$.

## Depends on

- [Definition (SPACE and NSPACE)](../../part-01/lecture-18/086-space-and-nspace.md)

## Proof depends on

- [Definition (SPACE complexity)](../../part-01/lecture-17/064-space-complexity.md)
- [Definition: Turing Machine](../../part-01/lecture-5/022-definition-turing-machine.md)
- [Definition: Decider](../../part-01/lecture-5/024-definition-decider.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Space Hierarchy Theorem (1/2)](../../../../../sources/v1/TheoryOfComputation.md)
