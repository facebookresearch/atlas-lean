# Name bits of a variable in the CLIQUE emitter

For $x \in \mathbb{N}$, the name of $x$ is
the list of symbols obtained from the binary encoding of $x$ (least significant bit first, empty
for $x = 0$) by writing each bit $b$ as the bit symbol $\mathrm{bit}(b)$. This is the form in which
the stacks $A$ and $D$ of the CLIQUE emitter hold variable names.
