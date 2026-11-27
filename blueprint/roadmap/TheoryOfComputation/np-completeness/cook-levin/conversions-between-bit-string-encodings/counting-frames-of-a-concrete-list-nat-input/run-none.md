# Frame counter fails on malformed list framing

Let $x$ be a bit string on which the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
fails, that is, $x$ is not a concatenation of framed forms. Let $c$ be a bit string and $v$ a Boolean. Started at
label loop with internal state $v$, input $x$, empty scratch stack and counter $c$, the [frame counter](prog.md)
reaches label bad, with some internal state and some stack contents, in at most $4|x| + 2$ steps.

At that point the counter and the scratch stack may hold partial contents.
