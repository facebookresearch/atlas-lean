# A transition lifted to the fenced machine

A transition of a single-tape machine $M$, made
of an optional symbol to write, an optional move and an optional next state, becomes the
transition of the fenced machine of $M$ that writes the symbol, or a right padding cell where $M$
writes a blank, makes the same move, and goes to the running state of the next state $q$ of $M$,
or halts where $M$ halts.
