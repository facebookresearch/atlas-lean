---
article_id: af_3cf66f9a480a77b06bf6945f
declaration: structure
origin: cited
statement: formalized
lean: TuringMachine.TuringEnumerator
---

# Definition: Turing Enumerator

A Turing Enumerator is a deterministic TM with a printer. It starts on a blank tape and it can print strings $w_1, w_2, w_3, \ldots$, possibly going forever. Its language is the set of all strings it prints. It is a generator, not a recognizer. For enumerator $E$ we say $L(E) = \{w \mid E \text{ prints } w\}$.

## Depends on

- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 6, Turing Enumerators](../../../../../sources/v1/TheoryOfComputation.md)
