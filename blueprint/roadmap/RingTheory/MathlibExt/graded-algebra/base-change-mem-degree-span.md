---
article_id: af_e86c773e44cf1a35d45835b6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.MultigradedFreeModule.baseChange_mem_degreeSpan
---

# Multigraded Zero Eval Base Change

Zero-evaluation scalar-extension degree-span bridge: a homogeneous element of
degree `α` in a multigraded free module lands, after scalar extension along the
zero-evaluation augmentation, in the `K`-span of the base-changed basis vectors
of degree `α`. Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 862–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`, which split a
graded free resolution and take the degree-`α` component after tensoring with `K`.

## Depends on

- [Multigraded Free Module](multigraded-free-resolution/multigraded-free-module.md)
- [Multigraded Polynomial Module](multigraded-polynomial-module/multigraded-polynomial-module.md)
- [Zero Eval](multigraded-betti/zero-eval.md)

## Proof depends on

- [Nat Degree To Int](multigraded-polynomial-module/nat-degree-to-int.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedZeroEvalBaseChange](../../../../sources/v2/MathlibExt.md)
