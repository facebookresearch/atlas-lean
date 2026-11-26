# Gaussian, Mellin, and parabolic-cylinder source bindings

Installed export scope: eight MathlibExt source files for scaled and tilted Gaussian Mellin transforms, the normalized parabolic-cylinder function U, and its Gamma/integral/order/continuation identities. Their active source/export rows remain in the original files-01 through files-04 paths.

Historical source dataset: the source-snapshot manifest and all four JSONL chunks retain56 complete original MathlibExt source rows, with original author notices and byte hashes. Original source revision and snapshot-file/line references are unchanged. The archive count is56; the installed source/export count is8.

Integral and convergence identities retain Re(s)>0. The endpoint s=-1 belongs to meromorphic continuation, with removable normal-form value distinguished from the ordinary totalized Gamma product. U uses the normalization U(a,z)=D(-a-1/2,z), principal positive-base complex powers, and total reciprocal Gamma at poles.

Installed source files:

- MathlibExt/Analysis/MellinTransform/Gaussian.lean
- MathlibExt/Analysis/MellinTransform/GaussianContinuation.lean
- MathlibExt/Analysis/MellinTransform/GaussianLaplace.lean
- MathlibExt/Analysis/MellinTransform/GaussianLaplaceSeries.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/Basic.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/GammaProduct.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/IntegralRepresentation.lean
- MathlibExt/Analysis/SpecialFunctions/ParabolicCylinder/OrderAnalyticity.lean
