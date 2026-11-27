# Gaussian, Mellin, and parabolic-cylinder source bindings

The installed scope consists of eight MathlibExt sources: scaled and tilted
Gaussian Mellin transforms, the normalized parabolic-cylinder function U, and
its Gamma, integral, order and continuation identities. The four current export
ledgers list exactly those eight sources.

The versioned `active-source-snapshot-v2` archive contains the unchanged original
versions of these eight files, with their author notices and original hashes.
Its README and standard-library verifier describe verification and restoration.
The complete original 56-source dataset remains in private publication custody;
the public current archive does not include the 48 unrelated original sources.
Every active row retains its preceding whole-archive binding, so the projection
can be checked and reconstructed without changing original source bytes.

Integral and convergence statements retain Re(s)>0. Continuation at s=-1 uses
the meromorphic normal form, distinguished from the ordinary totalized Gamma
product. U has normalization U(a,z)=D(-a-1/2,z), positive-base complex powers,
and total reciprocal Gamma at poles. Current proof and documentation adaptations
are recorded in the export rows separately from their original source snapshots.

Installed source files:

- MathlibExt/Analysis/MellinTransform/Gaussian.lean
- MathlibExt/Analysis/MellinTransform/GaussianLaplace.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/Basic.lean
- MathlibExt/Analysis/MellinTransform/GaussianLaplaceSeries.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/GammaProduct.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/OrderAnalyticity.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/IntegralRepresentation.lean
- MathlibExt/Analysis/MellinTransform/GaussianContinuation.lean
