# List canonicalizer fails on malformed input

Let $x$ be a bit string on which the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
fails, let $a$ and $o$ be bit strings and $v$ a Boolean. Started at label loop with internal state $v$, input $x$,
accumulator $a$, output $o$ and empty workspace stacks, the [list canonicalizer](prog.md) reaches label bad, with
some internal state and some stack contents, in at most $8|x| + 2$ steps.

Nothing is claimed about the stacks at that point; the accumulator and the workspace may hold partial data.
