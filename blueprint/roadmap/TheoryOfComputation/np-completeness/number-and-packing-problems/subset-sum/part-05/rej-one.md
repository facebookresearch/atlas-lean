# Rejecting in one step

Let $l$ be a label, $v$ a Boolean and $S$ an assignment of stack
contents. If executing the verifier's statement at label $l$ from internal state $v$ and stacks
$S$ yields the next label $\mathsf{no}$, then the verifier reaches a configuration with label
$\mathsf{no}$ from the configuration $(l, v, S)$ within one step.
