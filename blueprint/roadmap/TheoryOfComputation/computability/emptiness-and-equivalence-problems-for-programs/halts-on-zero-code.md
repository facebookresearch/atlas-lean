# Halting-on-zero code

For a code $c$ of a partial recursive function on $\mathbb{N}$, the
code $h(c)$ is the composition $k_0 \circ c \circ k_0$, where $k_0$ is the code of the constant
function $0$: whatever its input, $h(c)$ runs $c$ on $0$ and, if this halts, outputs $0$.
