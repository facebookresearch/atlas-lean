# Program of the reversal component

The multi-stack program over the stacks $X$ and $O$,
both with alphabet $\mathrm{Bool}$, with a Boolean internal state: at label mv it moves the bits
of $X$ one at a time onto $O$ (reversing them) and then goes to drop; at drop it pops $O$ once
and goes to done; at done it halts.
