# The situation step

Let $M$ be a finite multi-stack Turing machine, let $l$ be either a
label of $M$ or $\mathrm{none}$ (the halted label), let $v$ be a state of $M$, and let $W$ assign
to each stack $k$ a window, a list of entries that are symbols of $k$ or the empty cell. If
$l = \mathrm{none}$, the step returns the label $\mathrm{none}$, the state $v$, no pushed symbols on
any stack and no consumed symbols on any stack. If $l$ is a label, the step is the effect, read
from the windows $W$, of the statement tree of $l$ started in state $v$ with nothing pushed and
nothing consumed.
