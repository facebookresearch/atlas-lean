# Gate depths with constants at depth one

The depths of all gates of a flat circuit, in order, each computed from the depths of the gates before it:
an input gate has depth $0$, a constant gate depth $1$, and a negation, AND, OR or MOD gate one more than
the largest depth among its references. No well-formedness is assumed: a reference to a position with no
earlier gate reads depth $0$, and the largest depth among no references is $0$.
