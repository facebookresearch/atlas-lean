# From Normalized Chain Complex Nat Trans

The natural inclusion from the normalized chain complex to the unnormalized
chain complex, for fixed coefficients `R : C`.

Its components are the pointwise split monomorphisms
`SSet.fromNormalizedChainComplex`. This bundles the pointwise inclusion into a
natural transformation
`SSet.normalizedChainComplexFunctorObj R ⟶ (SSet.chainComplexFunctor C).obj R`
using Mathlib's existing normalized chain-map API.
