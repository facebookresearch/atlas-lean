# The emitter state before the diamonds

For a CNF formula $\varphi$ with $m$ clauses and an
output list $o$, this is the quiescent state whose output stack is $o$, whose stack $F$ holds the
tokens of $\varphi$ in reading order, whose stack $V$ is the variable stack of the distinct
variables of $\varphi$ (each kept at its last occurrence), whose clause count and diamond top are
both $m$, whose count of three times the clauses is $3m$, and all of whose other stacks are empty
and other counters zero.

It is the state that phase A, followed by setting the diamond top, reaches from the initial
state.
