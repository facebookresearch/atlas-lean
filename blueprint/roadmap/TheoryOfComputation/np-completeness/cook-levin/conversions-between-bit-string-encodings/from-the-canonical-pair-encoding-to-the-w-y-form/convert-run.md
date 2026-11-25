# Full run of the pair-encoding converter

For bit lists $x$ and $w$, the converter program
goes in exactly $2|x| + 2|w| + 5$ steps from the configuration at the label *read first*, with
no bit in the state, the input stack holding every bit $b$ of $x$ in order as the six bits true,
true, true, $b$, true, false, then a single false, then every bit $b$ of $w$ in order as the three
bits true, $b$, false, and the other three stacks empty, to the halted configuration with no bit
in the state, the verifier's pair encoding of $(x, w)$ on the output stack and the other three
stacks empty.
