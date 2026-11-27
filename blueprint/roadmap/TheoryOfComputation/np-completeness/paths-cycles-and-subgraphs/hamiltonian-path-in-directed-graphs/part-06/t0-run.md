# Moving the tokens back in the HAMPATH emitter

Let $L$ be a list of symbols that are all
tokens, $s$ a quiescent state of the emitter whose stack $T$ holds $L$, and $v$ an internal bit.
Then there is an internal bit $v'$ such that the emitter goes in exactly $|L| + 1$ steps from label
$\mathsf{t0}$ with bit $v$ and the stacks of $s$ to label $\mathsf{t1}$ with bit $v'$ and the
stacks of the state obtained from $s$ by emptying $T$ and replacing $F$ by $L$ reversed followed
by $F$.
