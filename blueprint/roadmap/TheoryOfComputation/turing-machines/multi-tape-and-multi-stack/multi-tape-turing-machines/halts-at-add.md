# Run composition for halting

Let $c$ be a configuration of a deterministic multi-tape
Turing machine and let $m, n \in \mathbb{N}$. If the run from $c$ is not halted after any $s < m$
steps, and the run from the configuration reached after $m$ steps halts at step $n$ (it is halted
after $n$ steps and not halted after fewer), then the run from $c$ halts at step $m + n$.
