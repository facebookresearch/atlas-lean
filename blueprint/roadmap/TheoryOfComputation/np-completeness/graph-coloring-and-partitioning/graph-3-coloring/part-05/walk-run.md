# Walking the earlier occurrences

Let $l = (x, b)$ be a literal and let
$q_1, \dots, q_k$ be earlier occurrences, each a tuple $(y, c, L, M)$ of a variable, a polarity,
a literal vertex and a negation vertex with $M = L + 1$. Let $m$ be a quiescent state of the
3-coloring emitter whose earlier-occurrence stack $D$ holds the concatenation $\delta$ of the
stack encodings of $q_1, \dots, q_k$, whose name stack holds the name bits of $x$, whose
polarity stack holds the single marker of polarity $b$, and whose earlier-literal counter is $0$;
let $n$ and $r$ be its next-vertex and OR-output counter values. Then for every internal state,
the emitter runs in at most $12|\delta| + k(8(n + r) + 21) + 1$ steps from the walk label with
the stacks of $m$ to the back label, with some internal state, and with the stacks of the
quiescent state obtained from $m$ by emptying $D$, putting the reverse of $\delta$ on top of the
walk stack $E$, and putting on top of the output stack the output for the consistency edges of
$l$, with literal vertex $n$ and negation vertex $n + 1$, with $q_1, \dots, q_k$ in turn.
