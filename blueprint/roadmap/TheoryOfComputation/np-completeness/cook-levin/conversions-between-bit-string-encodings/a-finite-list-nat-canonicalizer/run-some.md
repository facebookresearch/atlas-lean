# List canonicalizer runs in linear time on decodable input

Let $x$ be a bit string on which the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
returns a list $a$, let $o$ be a bit string and $v$ a Boolean. There is an internal state $v'$ such that the [list
canonicalizer](prog.md), started at label loop with internal state $v$, input $x$, empty accumulator, output $o$
and empty workspace stacks, reaches label good with internal state $v'$, empty input and accumulator, output equal
to the canonical code of $a$ followed by $o$, and empty workspace stacks, in at most $11|x| + 2$ steps.
