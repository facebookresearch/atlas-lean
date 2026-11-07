# Cleanup in a host

Let $c$ be a component machine, $\alpha$ an input alphabet, $o$ a host
stack, $a$ a bit, and $M$ a host program with Boolean state whose statement at the cleanup label
for $a$ is the cleanup round on the list of all host stacks with $o$ removed, kept in the order
of the list of host stacks, repeating at the cleanup label for $a$ and exiting to the output
label for $a$. If $S$ assigns to every host stack at most $m$ symbols, then for every state $v$,
$M$ runs from the cleanup label for $a$ with state $v$ and stacks $S$ to the output label for $a$
in at most $m + 1$ steps, ending with state false, stack $o$ holding $S(o)$ and every other stack
empty.
