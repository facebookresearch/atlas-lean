# Read phase of the payload normalizer consumes each bit once

Let $x$, $p$ and $w$ be bit strings and $v$ a Boolean, and let $\ell$ be the last bit of $p$ ("none" if $p$ is
empty). Started at label $\mathrm{read}(\ell)$ with internal state $v$, input stack $x$, buffer $p$ reversed and
output stack $w$, the [payload normalizer machine](prog.md) reaches, in exactly $|x| + 1$ steps, label copy with
internal state $0$ (false), an empty input stack, the [normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat.md)
of the concatenation $px$ reversed on the buffer, and output stack $w$. (Stack contents are listed from the top.)

Here $p$ is the part of the input already consumed.
