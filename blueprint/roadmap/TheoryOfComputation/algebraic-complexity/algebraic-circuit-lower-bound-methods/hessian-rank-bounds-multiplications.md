# Hessian rank bounds the number of multiplications

Let $f\in K[x_1,\dots,x_n]$ over a field $K$ (any characteristic), and fix a point $a\in K^n$. If $f$ is computed (as a formal polynomial) by an arithmetic circuit with $\mu$ multiplication gates (every multiplication gate charged, including multiplications by constants; additions, constants and wiring free), then the Hessian matrix $H_f(a)=(\partial^2f/\partial x_i\partial x_j(a))$ has rank at most $2\mu$. More generally, starting from supplied polynomials $g_1,\dots,g_k$, $\operatorname{rank}\bigl(H_f(a)-\sum_i\lambda_iH_{g_i}(a)\bigr)\le2\mu$ for suitable scalars $\lambda_i$.

## Proof sketch

At the fixed point, each multiplication $w=uv$ adds to the span of available Hessians the symmetrized outer product $\nabla u\,\nabla v^{T}+\nabla v\,\nabla u^{T}$ of rank at most two (plus combinations of earlier Hessians); additions and constants add nothing new. A shared gate contributes once.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
