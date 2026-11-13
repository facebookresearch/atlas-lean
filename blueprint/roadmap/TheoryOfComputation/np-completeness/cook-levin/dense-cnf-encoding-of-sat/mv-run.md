# Moving the input onto the stash

Let $l$, $a$, $o$ be bit strings and $v$ an optional
bit, and list stacks top first. Started at the moving label with internal state $v$, input stack
$l$, stash $a$, output stack $o$, empty counter stacks $N$, $K$, $M$ and empty scratch stack $T$,
the dense-to-binary converter reaches, in exactly $|l| + 1$ steps, the label for reading with no
clause open, with no internal state, an empty input stack, the reversal of $l$ followed by $a$ on
the stash, output stack $o$, and $N$, $K$, $M$, $T$ still empty.
