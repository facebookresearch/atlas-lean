# Stack embedding of the number normalizer in the list canonicalizer

The stack embedding of the [payload normalizer machine](../a-linear-time-machine-for-total-binary-payload-n/prog.md)
into the [list canonicalizer](prog.md) sends each of the normalizer's three stacks (input, buffer, output) to the
corresponding workspace stack of the canonicalizer, with the identity on the bit alphabets. The normalizer sees no
other stack.
