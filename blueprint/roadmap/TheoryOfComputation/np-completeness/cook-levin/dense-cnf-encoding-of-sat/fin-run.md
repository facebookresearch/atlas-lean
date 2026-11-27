# The converter's final phase

Write $0$ for false, $1$ for true and $1^j$ for $j$ copies
of $1$. Let $o$ be a bit string, $\iota$ a flag saying whether a clause is open, and $n, k, m$
natural numbers with $n = 0$ if no clause is open; let $c = n + 1$ if a clause is open and $c = 0$
otherwise. Started at the label that clears the slot counter at the end, for the flag $\iota$, with
empty internal state, empty input and stash, output $o$, literal, slot and clause counter stacks
holding $n$, $k$ and $m$ ones respectively, and an empty scratch stack, the converter reaches in
exactly $(k + 1) + c + (m + 1)$ steps the halting configuration with empty internal state, every
stack but the output empty, and output $1^m 0 1^n 0 o$ if a clause is open and $1^m 0 o$ otherwise
(listed from the top of the stack).
