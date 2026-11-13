# Load step of the 3-COLOR verifier

If the counter stack $N$ is empty, go to the label
that moves the codes onto the color stack $P$. Otherwise pop one symbol off $N$ and two bits $a$,
$b$ off the witness stack $W$, pushing each onto the scratch stack $T$ as it is popped (so the
codes end up reversed on $T$), and go back to the load label; reject instead if $W$ is empty
when a bit is due, or if $a$ and $b$ are both $1$ (the invalid code $11$). A symbol of $W$ that
is not a bit is read as $0$.
