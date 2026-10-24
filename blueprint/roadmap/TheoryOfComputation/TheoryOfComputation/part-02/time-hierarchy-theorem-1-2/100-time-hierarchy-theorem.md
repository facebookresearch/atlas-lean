---
article_id: af_e37e7045dd307c01ce7e8cf5
declaration: theorem
origin: cited
lean: time_hierarchy_theorem
---

# Theorem (Time Hierarchy Theorem)

For any $f \colon \mathbb{N} \to \mathbb{N}$ where $f$ is time constructible there is a language $A$ where $A$ requires $O(f(n))$ time, i.e., (1) $A$ is decidable in $O(f(n))$ time, and (2) $A$ is not decidable in $o(f(n)/\log(f(n)))$ time. In other words, $\mathsf{TIME}(o(f(n)/\log(f(n)))) \subsetneq \mathsf{TIME}(f(n))$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition: Turing Machine](../../part-01/lecture-5/022-definition-turing-machine.md)
- [Definition: Decider](../../part-01/lecture-5/024-definition-decider.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Time Hierarchy Theorem (1/2)](../../../../../sources/v1/TheoryOfComputation.md)
