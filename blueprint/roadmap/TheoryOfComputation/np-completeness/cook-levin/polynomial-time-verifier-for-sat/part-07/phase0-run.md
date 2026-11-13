# Phase 0 of the SAT verifier host

Let $c$ be a flag, $x$ and $w$ bit strings of lengths
$m$ and $n$, $v$ an internal state, and $S$ host stacks whose input stack holds the pair encoding
$x \# w$ and whose other stacks are all empty. Then there are an internal state $v'$ and host
stacks $S'$ such that the host program with flag $c$ runs in exactly $2m + 2n + 5$ steps from
the configuration at the phase-0 label $m_1$ with internal state $v$ and stacks $S$ to the
configuration at the start label of the tokenizer with internal state $v'$ and stacks $S'$, the
stack $X$ of $S'$ holds the bits of $x$ in order and the stack $W$ holds the bits of $w$ in
order, each as a name-bit symbol, and every other stack of $S'$ is empty.
