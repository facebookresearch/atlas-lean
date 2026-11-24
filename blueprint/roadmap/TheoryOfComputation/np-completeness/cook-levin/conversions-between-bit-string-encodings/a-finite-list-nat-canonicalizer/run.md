# List canonicalizer reaches the decoding outcome with canonical output

Let $x$ be a bit string and $v$ a Boolean. There are an internal state $v'$ and stack contents $S$ such that the
[list canonicalizer](prog.md), started at label loop with internal state $v$, input $x$ and all other stacks empty,
reaches in at most $11|x| + 2$ steps, with internal state $v'$ and stacks $S$, the label good if the [decoder of
lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md) succeeds on $x$
and bad if it fails; moreover, if it returns a list $a$, then in $S$ every stack is empty except the output, which
holds the canonical code of $a$.
