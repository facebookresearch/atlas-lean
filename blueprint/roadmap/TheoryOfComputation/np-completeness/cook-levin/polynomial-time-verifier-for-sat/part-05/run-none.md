# Rejecting run

Let $x$ and $w$ be bit strings such that $x$ does not decode as a CNF
formula. For every bit $v$ and stacks $S$ with the bits of $x$ on the formula stack $X$, the bits
of $w$ on the witness stack $W$, and both counter stacks $CC$ and $LC$ empty, the tokenizer
started at its start label with internal bit $v$ and stacks $S$ reaches a configuration with label
$\mathsf{rej}$ within $2|x| + 2$ steps.
