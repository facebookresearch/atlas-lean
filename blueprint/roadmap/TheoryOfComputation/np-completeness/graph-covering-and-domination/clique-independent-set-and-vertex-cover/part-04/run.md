# The verifier machine for clique, independent set and vertex cover

Let $m$ be a
mode, $x$ and $w$ lists of bits, $v$ a state and $S$ stack contents in which the input
stack $X$ holds the bits of $x$, the witness stack $W$ holds the bits of $w$, and every other
stack is empty. Then there are a state $v'$ and stack contents $S'$ such that within at most
$8(|x| + |w| + 1)^3$ steps the verifier program of mode $m$ goes from the start label with
state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at the accepting label if the
verifier check of mode $m$ accepts $x$ with witness $w$, and at the rejecting label
otherwise.
