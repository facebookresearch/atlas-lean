# 3-COLOR emitter: moving the walk side back

Let $L$ be a list of token symbols each of
which is a walk token (a name bit, a literal marker or the clause symbol), let $m$ be a quiescent
state of the 3-COLOR emitter whose stack $E$ (the walk's other side) holds $L$, and let $v$ be a
Boolean. Then there is a Boolean $v'$ such that the emitter runs in exactly $|L| + 1$ steps from
label $\mathsf{back}$ with internal state $v$ and the stacks of $m$ to label $\mathsf{putN}$ with
internal state $v'$ and the stacks of the quiescent state obtained from $m$ by emptying $E$ and
replacing the occurrence stack $D$ by the reverse of $L$ followed by the old contents of $D$.
