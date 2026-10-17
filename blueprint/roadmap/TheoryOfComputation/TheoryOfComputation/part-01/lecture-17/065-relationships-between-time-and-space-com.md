---
article_id: af_c3136fbe14a9d30bd90c3f38
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SpaceComplexity.TIME_SPACE_relationship
---

# Theorem (Relationships between Time and Space Complexity)

For $t(n) \geq n$: (1) $\mathsf{TIME}(t(n)) \subseteq \mathsf{SPACE}(t(n))$; (2) $\mathsf{SPACE}(t(n)) \subseteq \mathsf{TIME}(2^{O(t(n))}) = \bigcup_c \mathsf{TIME}(c^{t(n)})$.

## Depends on

- [Definition (SPACE and NSPACE)](../lecture-18/086-space-and-nspace.md)

## Proof depends on

- [Definition (SPACE complexity)](064-space-complexity.md)
- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)
- [Definition: Decider](../lecture-5/024-definition-decider.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 17, Relationships between Time and SPACE Complexity](../../../../../sources/v1/TheoryOfComputation.md)
