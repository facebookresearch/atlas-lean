# Loop head of a for loop over a counter

For stacks $c$ and $c'$, a symbol $u'$ of stack
$c'$ and labels $b$ and $r$, the loop head is the statement that pops stack $c$, replaces the
machine state by the state whose flag bit records whether a symbol was popped, and branches on
that bit: if a symbol was popped, it pushes $u'$ onto the index stack $c'$ and goes to label $b$
(the loop body); if $c$ was empty, it goes to label $r$.
