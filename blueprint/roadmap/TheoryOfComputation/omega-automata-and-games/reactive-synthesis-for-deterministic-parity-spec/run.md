# Run of a deterministic parity specification

Let $(q_0, \delta, \Omega)$ be a deterministic parity specification over states $Q$, inputs $I$ and outputs $O$. The run on an input word $w^{\mathrm{in}} : \mathbb{N} \to I$ and an output word $w^{\mathrm{out}} : \mathbb{N} \to O$ is the sequence $\rho : \mathbb{N} \to Q$ defined by

$$\rho(0) = q_0, \qquad \rho(k + 1) = \delta\bigl(\rho(k), w^{\mathrm{in}}(k), w^{\mathrm{out}}(k)\bigr).$$
