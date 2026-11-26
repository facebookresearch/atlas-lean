# Alternating formulas of depth d

An *alternating formula* of depth $d$ over $n$ variables is a formula in negation normal form whose gates are unbounded fan-in AND and OR gates that alternate along every root-to-leaf path, with exactly $d$ gates on each path and literals at the leaves. Its size is its number of gates. Every circuit of the unbounded fan-in basis of AND/OR depth $d$ unfolds into an alternating formula of depth $d$ (of possibly larger size).

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)
- [Unfolding a circuit into a formula of the same depth](../../circuit-models-and-classes/circuit-models-and-complexity-measures/unfolding-a-circuit-into-a-formula.md)

## Sources

- Oliver Korten, "Top-Down Lower Bounds for All Depths", Electronic Colloquium on Computational Complexity, 2026.
- Victor Lecomte, Prasanna Ramakrishnan, "Optimal Shallow Circuits for Majority", 2026.
