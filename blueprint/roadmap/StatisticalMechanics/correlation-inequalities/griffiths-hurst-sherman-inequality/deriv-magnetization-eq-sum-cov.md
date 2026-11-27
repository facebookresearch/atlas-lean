# Field derivative of the magnetization as a sum of covariances

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$, let $o \in V$ and let $\langle \cdot \rangle_{\beta, h}$ be the
[finite-volume Ising expectation](../griffiths-inequalities/ising-expectation.md). The derivative in $h$
of the magnetization $h \mapsto \langle \sigma_o \rangle_{\beta, h}$ is

$$\frac{d}{dh} \langle \sigma_o \rangle_{\beta, h} = \beta \sum_{x \in V} \bigl(\langle \sigma_o \sigma_x \rangle_{\beta, h} - \langle \sigma_o \rangle_{\beta, h} \langle \sigma_x \rangle_{\beta, h}\bigr),$$

$\beta$ times the finite-volume susceptibility.
