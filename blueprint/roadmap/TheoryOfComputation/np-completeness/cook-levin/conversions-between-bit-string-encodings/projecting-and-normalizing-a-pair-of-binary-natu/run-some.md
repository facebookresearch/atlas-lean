# Number-pair projector yields both canonical payloads on success

Let $x$ be a bit string on which the [decoder of pairs of natural numbers](decode-pair-nat.md) returns $(m, n)$, let
$\ell$, $\rho$ be bit strings and $v$ a Boolean. There is an internal state $v'$ such that the [number-pair
projector](prog.md) goes from label $\mathrm{pair}(\mathrm{read})$, internal state $v$, splitter input $x$, left
output $\ell$, right output $\rho$ and all other stacks empty, to label good, internal state $v'$, left output the
binary code of $m$ followed by $\ell$, right output the binary code of $n$ followed by $\rho$, and all other stacks
empty, in at most $2|x| + 6$ steps.
