# One step of the emptiness test

If the verifier's instruction at label $l$ is the
emptiness test of stack $k$ with targets $e$ and $ne$, then from label $l$, in any internal state
and on any stacks, exactly one step of the verifier leads to label $e$ if stack $k$ is empty and
to label $ne$ otherwise, in some internal state and with the stacks unchanged.
