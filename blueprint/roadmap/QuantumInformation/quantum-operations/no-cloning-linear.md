# No-cloning theorem (linear form)

Let $H$ be a complex inner product space containing two orthonormal vectors $e_1$ and $e_2$, and
let $b \in H$ be any blank state. Then there is no $\mathbb{C}$-linear map
$U : H \otimes_{\mathbb{C}} H \to H \otimes_{\mathbb{C}} H$ with $U(\psi \otimes b) = \psi \otimes \psi$
for every unit vector $\psi \in H$.

Linearity alone forbids cloning. For $\varphi = (e_1 + e_2)/\sqrt 2$, linearity gives
$U(\varphi \otimes b) = (e_1 \otimes e_1 + e_2 \otimes e_2)/\sqrt 2$, which has no
$e_1 \otimes e_2$ component, whereas $\varphi \otimes \varphi$ has the component $1/2$. Unitarity
of $U$ is not assumed, so the statement covers every isometry and every unitary, and it
complements the [two-state form](no-cloning-two-state.md), which rules out an isometry cloning
just two non-orthogonal, non-identical states. A third version says that if a unitary clones two pure
states that are not identical, the states are orthogonal. The linear form assumes neither unitarity
nor a particular pair of states.

The no-cloning theorem was long taken to make quantum error correction impossible, since
classical redundancy duplicates information; quantum codes instead spread the information over
many qubits (Calderbank and Shor 1996, Section I).

## Related topics

- [CSS codes](../quantum-error-correction/css-codes/README.md): quantum error-correcting codes, which achieve redundancy without cloning.

## Sources

- W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned", Nature 299 (1982), 802-803, DOI 10.1038/299802a0.
- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section I.
