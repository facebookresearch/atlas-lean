# Field-normalizer stack embedding in the number-pair projector

For a field $s \in \{\text{first}, \text{second}\}$, the stack embedding of the [payload normalizer
machine](../a-linear-time-machine-for-total-binary-payload-n/prog.md) into the [number-pair projector](prog.md)
sends

- the normalizer's input to the splitter's left stack (holding the first field) if $s$ is first, and to the
  splitter's input stack (holding the second field) if $s$ is second;
- the normalizer's buffer to the shared buffer;
- the normalizer's output to the left output if $s$ is first, and to the right output if $s$ is second,

with the identity on the bit alphabets. Each normalization consumes its field; the two share only the buffer.
