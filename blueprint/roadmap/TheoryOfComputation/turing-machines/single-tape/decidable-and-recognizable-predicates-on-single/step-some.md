# One step of a single-tape Turing machine

Let $M$ be a single-tape Turing machine, $q$ a
state of $M$ other than the halting state and $t$ a tape, and let the transition function of $M$
at $q$ and the symbol under the head of $t$ (possibly blank) give the symbol $s$ to write
(possibly blank), the head movement $d$ (left, right or none) and the next state $q'$ (possibly
the halting state). Then the configuration in state $q$ with tape $t$ has a successor, namely the
configuration in state $q'$ whose tape is obtained from $t$ by writing $s$ under the head and
then moving the head by $d$.
