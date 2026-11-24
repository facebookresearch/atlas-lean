# The dense-to-binary converter program

The program uses an input stack, a stash, an
output stack, unary counter stacks $N$, $K$, $M$ and a scratch stack $T$; each label first pops
one stack and keeps the popped bit (or nothing, if the stack was empty) as its internal state.
Below, $\iota$ says whether a clause is open, $0$ is false and $1$ is true.

Moving: pop the input; if a bit $b$ was popped, push $b$ onto the stash and repeat, otherwise go to
reading with $\iota$ false.

Reading with $\iota$: pop the stash; if a bit $s$ was popped, go to the second read with $\iota$
and $s$, otherwise go to clearing with $\iota$.

Second read with $\iota$ and $s$: pop the stash. If it was empty, go to clearing with $\iota$. If
it gave $0$: when $s = 1$, push $1$ onto $K$ and go to reading with $\iota$; when $s = 0$ and
$\iota$ is true, push $0$ onto the output and go to the first closing label; when $s = 0$ and
$\iota$ is false, go to the second closing label. If it gave $1$: when $\iota$ is true, push
$\lnot s$ and then $0$ onto the output and go to the first literal label; otherwise go to reading
with $\iota$ false.

First literal label: pop $K$; if a bit was popped, push $1$ twice onto the output and $1$ onto $T$
and repeat, otherwise go to the second literal label.

Second literal label: pop $T$; if a bit was popped, push $1$ onto $K$ and repeat, otherwise push
$1$ onto $N$, then $1$ onto $K$, and go to reading with $\iota$ true.

First closing label: pop $N$; if a bit was popped, push $1$ onto the output and repeat, otherwise
go to the second closing label.

Second closing label: pop $K$; if a bit was popped, repeat, otherwise push $1$ onto $M$ and go to
reading with $\iota$ true.

Clearing with $\iota$: pop $K$; if a bit was popped, repeat, otherwise push $0$ onto the output and
go to the literal-count label if $\iota$ is true and to the clause-count label otherwise.

Literal-count label: pop $N$; if a bit was popped, push $1$ onto the output and repeat, otherwise
push $0$ onto the output and go to the clause-count label.

Clause-count label: pop $M$; if a bit was popped, push $1$ onto the output and repeat, otherwise
halt.
