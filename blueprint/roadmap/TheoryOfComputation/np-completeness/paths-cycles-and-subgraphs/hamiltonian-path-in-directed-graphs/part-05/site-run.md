# Run of a HAMPATH copy site

Let $j$ be a copy site, $b$ and $v$ bits and $s$ a quiescent
state of the HAMPATH emitter; let $c$ be the value in $s$ of the counter that $j$ reads and $e$
the number of ones that $j$ adds to its counter. Started at label $\mathrm{cpA}(j, b)$ with
internal state $v$ and the stacks of $s$, the emitter runs in exactly $2c + 3$ steps to the label
that follows $j$ for $b$, with some internal state and the stacks of the quiescent state obtained
from $s$ by appending $c + e$ copies of true followed by one false to its edge bits.
