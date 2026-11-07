# Timed outputs compose

Let $M_1$ and $M_2$ be single-tape Turing machines over the same
alphabet, and let $M$ be their composite, whose states are the disjoint union of those of $M_1$
and of $M_2$: $M$ starts in the start state of $M_1$ and runs $M_1$, where $M_1$ would halt it
enters the start state of $M_2$ instead, and it then runs $M_2$ and halts where $M_2$ halts. Say
that a machine outputs a word $w$ on a word $v$ within $t$ steps when, started in its start state
on a tape holding $v$, it reaches in at most $t$ steps the halted configuration whose tape holds
exactly $w$, with the head at the start of $w$. For all words $a$, $b$, $c$ and all natural
numbers $t_1$, $t_2$: if $M_1$ outputs $b$ on $a$ within $t_1$ steps and $M_2$ outputs $c$ on $b$
within $t_2$ steps, then $M$ outputs $c$ on $a$ within $t_1 + t_2$ steps.
