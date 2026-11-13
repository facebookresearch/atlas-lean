# The single-tape simulation outputs within one extra step

Let $\Gamma_0$ be a finite
alphabet with at least one non-blank symbol, let $M$ be a Post–Turing machine over $\Gamma_0$
supported by the finite set of states $S$, and let $l$ and $l'$ be words of non-blank symbols of
$\Gamma_0$. If $M$, started on $l$, reaches in exactly $n$ steps a configuration $c$ in which it
halts, and the tape of $c$ holds $l'$ starting at the head with blanks everywhere else, then the
single-tape machine simulating $M$ outputs $l'$ on the input $l$ within $n + 1$ steps: its run
from the initial configuration on $l$ reaches, in at most $n + 1$ steps, the halting state with
the tape holding exactly $l'$, starting at the head.
