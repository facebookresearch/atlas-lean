---
article_id: af_2c9ce26fef1c228507da0c25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.MultigradedFreeResolution.baseChangedDifferential_preservesDegree
---

# Multigraded Base Changed Differential

The scalar-extended differential preserves multidegree: a graded free
resolution splits into degree-indexed complexes, and tensoring along the
augmentation uses the differential `Id tensor partial`, so the `(i + 1) → i`
base-changed differential maps the degree-`α` piece to itself.

## Depends on

- [Multigraded Free Resolution](multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](multigraded-polynomial-module/multigraded-polynomial-module.md)
- [Base Changed Complex](multigraded-betti/base-changed-complex.md)
- [Base Changed Degree Piece](multigraded-betti/base-changed-degree-piece.md)

## Proof depends on

- [Is Degree Zero](multigraded-free-resolution/is-degree-zero.md)
- [Multigraded Free Module](multigraded-free-resolution/multigraded-free-module.md)
- [Multigraded Zero Eval Base Change](base-change-mem-degree-span.md)
- [Zero Eval](multigraded-betti/zero-eval.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedBaseChangedDifferential](../../../../sources/v2/MathlibExt.md)
- Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23 (2020), lines 862–867, `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.
