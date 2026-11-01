---
article_id: af_cf1ba31706fd4a9485344f0f
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted.ProgramVerification.CoCStrongNormalization.typing_polyId
---

# Typing poly Id

Anti-vacuity guard: the polymorphic identity `λ (A : Prop). λ (x : A). x` has type
`Π (A : Prop). Π (x : A). A`. This is typable only because `Prop` is impredicative.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.TheoryOfComputation.CoCStrongNormalizationWanted](../../../../sources/v2/WantedExt.md)
- Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
