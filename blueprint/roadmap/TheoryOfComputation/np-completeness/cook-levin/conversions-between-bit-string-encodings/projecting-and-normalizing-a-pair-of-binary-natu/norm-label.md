# Label map chaining the two field normalizers

For a field $s \in \{\text{first}, \text{second}\}$, the label map from the [payload normalizer
machine](../a-linear-time-machine-for-total-binary-payload-n/lab.md) to the [number-pair projector](lab.md) sends
the normalizer's halting label done to $\mathrm{norm}(\text{second}, \mathrm{read}(\text{none}))$ if $s$ is first
and to good if $s$ is second, and every other label $\ell$ to $\mathrm{norm}(s, \ell)$.
