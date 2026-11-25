# Linear step bound for the payload normalizer machine

For every bit string $x$ there are an internal state $v$ and stack contents $S$ such that the [payload normalizer
machine](prog.md), started at label $\mathrm{read}(\text{none})$ with internal state $0$ (false), input stack $x$
and empty buffer and output stacks, reaches label done with internal state $v$ and stacks $S$ in at most
$2|x| + 3$ steps, and the output stack of $S$ holds the
[normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat.md) of $x$.
