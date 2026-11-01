---
article_id: af_13e6870aec1fab134446eaf0
declaration: theorem
origin: cited
statement: formalized
lean: CFLPumping.pumping_lemma_cfl
---

# Pumping Lemma for CFLs

For every CFL $A$, there is a $p$ such that if $s \in A$ and $|s| \geq p$ then $s = uvxyz$ where (1) $uv^i xy^i z \in A$ for all $i \geq 0$, (2) $vy \neq \varepsilon$, (3) $|vxy| \leq p$.

## Depends on

- [Definition (Context Free Language)](../lecture-4/014-context-free-language.md)

## Proof depends on

- [Lemma 1](../lecture-7/028-lemma-1.md)
- [Definition (Context Free Grammar)](../lecture-4/013-context-free-grammar.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 5, Proving languages not Context Free](../../../../../sources/v1/TheoryOfComputation.md)
