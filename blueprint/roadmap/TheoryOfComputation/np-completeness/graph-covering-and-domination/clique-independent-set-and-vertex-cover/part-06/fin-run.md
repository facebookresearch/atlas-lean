# Clique emitter: the instance prefix

Let $v$ be a Boolean, $d$ and $e$ stack-symbol lists,
$o$ a list of bits and $c, n \in \mathbb{N}$. From label fin with flag $v$ and the state with
empty token stack, output $o$, empty name stack, walked stack $d$, walk side $e$, clause count
$c$, occurrence count $n$ and empty scratch stacks, the emitter machine reaches in exactly
$n + c + 4$ steps label done with some flag and some state whose output, read top-down, is $c$
ones, false, $n$ ones, false, then $o$.
