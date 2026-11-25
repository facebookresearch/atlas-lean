# HAMPATH emitter, phase A: moving the walk stack back onto the variable stack

Let $f$ be
a Boolean, let $L$ be a list of symbols each of which is a name bit or the separator
$\mathrm{cl}$, and let $s$ be a quiescent state of the HAMPATH emitter whose stack $W$ is $L$.
Then for every value $v$ of the machine's Boolean variable there is a value $v'$ such that the
emitter goes in exactly $|L|$ steps from label $\mathrm{ab}(f)$, variable $v$ and the stacks of
$s$ to label $\mathrm{ab}(f)$, variable $v'$ and the stacks of the state obtained from $s$ by
emptying $W$ and replacing $V$ by the reverse of $L$ followed by the old contents of $V$.
