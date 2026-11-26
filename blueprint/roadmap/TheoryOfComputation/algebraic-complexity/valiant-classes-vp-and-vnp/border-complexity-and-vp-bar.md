# Approximative (border) circuits and the class VPbar

A polynomial $P\in K[x]$ is *approximated within $s$ nodes* if there is a polynomial $Q$ with coefficients in the Laurent series field $K((\varepsilon))$, computed by an arithmetic circuit with at most $s$ nodes whose constants are Laurent series in $\varepsilon$, such that $Q=P+\varepsilon G$ for some polynomial $G$ with coefficients in $K[[\varepsilon]]$ (no negative powers of $\varepsilon$ survive in $Q$, and the $\varepsilon$-free part is $P$). $\overline{\mathsf{VP}}_K$ is the class of p-families approximated within polynomially many nodes. One has $\mathsf{VP}_K\subseteq\overline{\mathsf{VP}}_K$, and approximation within $s$ nodes is preserved by affine projections.

## Depends on

- [Valiant's class VP](valiants-class-vp.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
