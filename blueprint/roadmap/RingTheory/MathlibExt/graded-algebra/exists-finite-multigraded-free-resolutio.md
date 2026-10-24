---
article_id: af_d3eccaba041ab4962576bcc8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.exists_finite_multigraded_free_resolution
---

# Multigraded Hilbert Syzygy

Existence of a finite multigraded free resolution over `MvPolynomial`.

Direct source: Hoffman–Wang,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612 (finite free
graded resolution). The Braun–Davis JIS passage
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876
supplies the motivating Hilbert-syzygy / Poincaré-series context only. No
`≤ n` bound is claimed here.

Proof: Uses stagewise minimal homogeneous free covers, the determinant trick,
dimension shifting, and Hilbert's syzygy theorem.

## Depends on

- [Multigraded Free Resolution](multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](multigraded-polynomial-module/multigraded-polynomial-module.md)

## Proof depends on

- [Hilbert Syzygy](../polynomial/hilbert-syzygy.md)
- [Is Degree Zero](multigraded-free-resolution/is-degree-zero.md)
- [Multigraded Free Module](multigraded-free-resolution/multigraded-free-module.md)
- [Nat Degree To Int](multigraded-polynomial-module/nat-degree-to-int.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy](../../../../sources/v2/MathlibExt.md)
