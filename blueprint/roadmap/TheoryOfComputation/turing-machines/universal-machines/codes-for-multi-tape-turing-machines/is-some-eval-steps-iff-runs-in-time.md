# The evaluator returns within the clock exactly when the machine runs in time

For a code
$c$, an input $x$ and a clock $T$, the clocked evaluator of $c$ on $x$ with clock $T$ returns an
output if and only if the machine of $c$ runs in time $T$ on $x$, that is, every computation path
of that machine on $x$ with at least $T$ steps ends in a halted configuration.
