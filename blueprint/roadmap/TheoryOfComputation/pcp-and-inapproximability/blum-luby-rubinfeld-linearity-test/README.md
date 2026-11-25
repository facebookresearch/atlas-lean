# Blum–Luby–Rubinfeld linearity test

The BLR test reads a function on the cube at three correlated points and accepts when the values are consistent with linearity. Its Fourier analysis, the prototype of local testing and of the long-code tests behind PCP-based hardness results, shows that a function accepted with probability $1 - \varepsilon$ is $\varepsilon$-close to a character.

- [Acceptance probability of the BLR test](blr-accept-prob.md)
- [Acceptance probability of the BLR test in Fourier form](blr-accept-prob-eq.md)
- [Blum–Luby–Rubinfeld linearity test](blr-test.md)
- [Relative Hamming distance on the Boolean cube](bool-dist.md)
- [Distance to a character](bool-dist-cube-chi-eq.md)
- [Characters are $\pm 1$-valued](cube-chi-eq-one-or-neg-one.md)

## Related topics

- [Fourier analysis on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/README.md): the characters, Plancherel and the convolution theorem used in the analysis of the test.
- [Approximability of MAX-3SAT](../approximability-of-max-3sat/README.md): Håstad's optimal hardness results come from 3-query tests that extend the BLR test.
