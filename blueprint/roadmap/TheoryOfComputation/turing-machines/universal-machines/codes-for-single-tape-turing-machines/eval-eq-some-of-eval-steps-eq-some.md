# Clocked results agree with the machine's semantics

Let $c$ be a code, $x$ a list of
bits, $T$ a natural number and $l$ a list of natural numbers. If the clocked evaluator, running
$c$ on $x$ for at most $T$ steps, returns $l$, then the decoded machine of $c$, started on the
input word of $x$, halts, and the tape from its head rightwards in the halting configuration is
$l$ followed by blanks.
