# Run lifting

Let $M$ be a counter machine (unit counters indexed by $C$ and a Boolean
output stack) and $M'$ a machine on the same stacks plus an input stack over $G$, such that $M'$
embeds $M$ along the inclusion of the counter stacks with the same labels (at every label whose
statement is not the halt statement, $M'$ runs $M$'s statement). If $M$ runs in $n$ steps from
optional label $l$, flag $v$ and stacks $S$ to a label $l'$, flag $v'$ and stacks $S'$, then for
every input list $xs$ over $G$, $M'$ runs in $n$ steps from label $l$, flag $v$, stacks $S$ and
input stack $xs$ to label $l'$, flag $v'$, stacks $S'$ and input stack $xs$.

This is an instance of run embedding.
