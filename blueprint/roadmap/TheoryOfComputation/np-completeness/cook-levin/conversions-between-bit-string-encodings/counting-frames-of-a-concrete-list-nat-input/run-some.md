# Frame counter counts every successfully decoded list of naturals

Let $x$ be a bit string on which the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
returns a list of length $k$ (the blocks need not be binary codes), let $c$ be a bit string and $v$ a Boolean.
Started at label loop with internal state $v$, input $x$, empty scratch stack and counter $c$, the [frame
counter](prog.md) reaches label good with internal state $0$ (false), empty input and scratch stacks and counter
$1^k c$ in at most $4|x| + 1$ steps.
