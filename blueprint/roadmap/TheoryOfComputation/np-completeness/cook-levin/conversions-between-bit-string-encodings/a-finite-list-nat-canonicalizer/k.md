# Stacks of the list-of-naturals canonicalizer

The list canonicalizer has six stacks: the input, an accumulator holding the output reversed, the final output,
and a copy of the three stacks (input, buffer, output) of the [payload normalizer
machine](../a-linear-time-machine-for-total-binary-payload-n/k.md), used as the workspace for one number.
