# Draining the work stacks of the dense-SAT verifier

Let $\mathit{ans}$ be a Boolean, let
$i$, $a$, $b$ be lists of symbols of the work alphabet $G$, and let $v$ be any state. Start the
verifier's program at the label $\mathrm{drainI}(\mathit{ans})$ in state $v$, with the input
stack holding $i$, the formula stash empty, the assignment stacks $A$ and $B$ holding $a$ and
$b$, and the output stack empty. It then runs for exactly $|i| + |a| + |b| + 3$ steps and reaches
the label $\mathrm{finish}(\mathit{ans})$ with no symbol in its state, all four work stacks empty
and the output stack still empty.
