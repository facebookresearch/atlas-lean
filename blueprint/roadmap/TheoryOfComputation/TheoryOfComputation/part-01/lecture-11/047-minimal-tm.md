---
article_id: af_512fc91eca07b781a1000853
declaration: def
origin: cited
statement: formalized
lean: SelfReference.MIN_TM
---

# Definition (Minimal TM)

$M$ is a minimal TM if $|\langle M' \rangle| < |\langle M \rangle| \Rightarrow L(M') \neq L(M)$. Thus, a minimal TM has the shortest description among all equivalent TMs. $\mathrm{MIN}_{\mathrm{TM}} = \{\langle M \rangle \mid M \text{ is a minimal TM}\}$.

## Depends on

- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 11, Ex 3: MIN_TM is T-unrecognizable section](../../../../../sources/v1/TheoryOfComputation.md)
