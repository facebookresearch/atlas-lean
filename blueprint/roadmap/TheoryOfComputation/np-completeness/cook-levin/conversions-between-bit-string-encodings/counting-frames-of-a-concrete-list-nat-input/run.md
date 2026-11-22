# Frame counter decides decodability and counts length in unary

Let $x$ be a bit string and $v$ a Boolean. There are an internal state $v'$ and stack contents $S$ such that the
[frame counter](prog.md), started at label loop with internal state $v$, input $x$ and empty scratch and counter
stacks, reaches in at most $4|x| + 2$ steps, with internal state $v'$ and stacks $S$, the label good if the
[decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
succeeds on $x$ and the label bad if it fails; moreover, if it returns a list of length $k$, then $S$ has empty
input and scratch stacks and counter $1^k$.
