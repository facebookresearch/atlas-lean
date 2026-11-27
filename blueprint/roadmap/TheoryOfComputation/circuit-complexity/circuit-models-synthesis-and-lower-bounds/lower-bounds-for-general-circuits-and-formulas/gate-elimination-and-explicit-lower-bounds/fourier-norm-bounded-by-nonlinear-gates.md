# Fourier norm is at most 2^m for circuits with m nonlinear gates

For $g:\{0,1\}^n\to\{0,1\}$ write $\|g\|_{1}=\sum_{S}|\widehat{(-1)^g}(S)|$ for the Fourier $\ell_1$-norm. If $g$ is an output of a circuit over a basis of fan-in at most two containing $m$ non-affine gates (affine gates, constants and arbitrary fan-out free), then $\|g\|_1\le 2^m$.

## Proof sketch

Maintain the invariant that every character of the vector of all available wires has bounded norm. Adding a gate expands it in its own Fourier basis, producing linear combinations of products of old characters, which are old characters; affine gates have norm one and two-argument functions norm at most two.

## Depends on

- [The Zhegalkin basis and multiplicative complexity](../../circuit-models-and-classes/circuit-models-and-complexity-measures/zhegalkin-basis-and-multiplicative-complexity.md)
- [Fourier coefficient on the Boolean cube](../../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
