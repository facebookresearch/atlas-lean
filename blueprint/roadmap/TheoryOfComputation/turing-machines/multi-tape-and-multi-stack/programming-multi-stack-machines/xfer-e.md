# Draining a counter while prepending a block

Let $k$ and $o$ be stack indices, $ys$ a list
of symbols of the alphabet of stack $o$, and $\ell$ and $\ell'$ labels. This is the TM2 statement
that pops stack $k$ and sets the internal state to the flag bit recording whether a symbol was
popped. If one was, it prepends $ys$ to stack $o$ (so that $ys$ reads from the top down) and goes
to $\ell$; if stack $k$ was empty, it goes to $\ell'$.

Used as the statement at label $\ell$ with $k \ne o$, it empties a unary counter on stack $k$ and
prepends one copy of $ys$ to stack $o$ per unit removed, then goes to $\ell'$.
