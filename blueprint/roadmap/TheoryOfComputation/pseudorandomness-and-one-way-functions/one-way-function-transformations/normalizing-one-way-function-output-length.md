# Normalizing the output length of a one-way function

If a one-way function $f$ exists, then there is a one-way function $g$ and a polynomial-time computable length function $m$ such that $|g(x)| = m(|x|)$ for every input $x$. Moreover there is a one-way function $g'$ that is *length preserving*, $|g'(x)| = |x|$ for all $x$.

## Proof sketch

Pad each image with a self-delimiting suffix to a fixed polynomial bound on output lengths at that input length, tagging with the length so that preimages are preserved. For length preservation, apply $g$ to a prefix of the input whose length is chosen so that the padded output fits in the full input length, and output the padded image; an inverter for the new function yields one for $g$ at the shorter length.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
