---
article_id: af_18d2a8491bbb885436e37830
declaration: def
origin: cited
statement: formalized
lean: AdjoinRoot.tensorProductAlgEquivPi
---

# Tensor Product Alg Equiv Pi

Base change of `AdjoinRoot f` along an explicit factorisation of `map f`
into pairwise nonassociated irreducibles.

This is the algebraic decomposition in ATLAS N86, Corollary 4.39 of
[MIT 18.785 *Number Theory I*](https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/).
The corresponding upstream declaration is
[`TensorSplitting.adjoinRoot_tensor_algEquiv_prod` in
`v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean`, lines 146--160,
at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean#L146-L160).
There, `L` is presented as
`K[X] / (f)`, the extension `K' / K` is arbitrary, and the distinct irreducible
factors of `f` over `K'` are represented here by `g`, `hirr`, `hne`, and
`hprod`. The source assumes that `f` is irreducible and separable in order to
say that `L / K` is a finite separable field extension. Those assumptions are
not needed for this CRT decomposition of the explicitly presented algebra
`AdjoinRoot f`; accordingly, this theorem makes no stronger field or
finite-etale claim about its factors.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Quotient Inf Alg Equiv Pi Quotient](quotient-inf-alg-equiv-pi-quotient.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.Polynomial.AdjoinRootTensorProduct](../../../../../sources/v2/MathlibExt.md)
