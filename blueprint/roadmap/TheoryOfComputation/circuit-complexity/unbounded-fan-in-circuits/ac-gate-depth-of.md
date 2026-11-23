# Gate depth with constants at depth one

The depth of one flat gate given the depths of the earlier gates, counted as in straight-line circuits.
The earlier depths form a list $d$ read with default $0$: a reference with no entry in $d$ counts as
depth $0$. An input gate has depth $0$, a constant gate has depth $1$, and a negation, AND, OR or MOD
gate has depth one more than the largest depth among its references, the largest depth among no
references being $0$, so an AND, OR or MOD gate with no references has depth $1$. This is the flat depth
except that a constant gate has depth $1$ instead of $0$.
