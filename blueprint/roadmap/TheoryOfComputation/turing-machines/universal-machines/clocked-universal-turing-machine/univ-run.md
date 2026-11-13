# Correctness and running time of the clocked universal machine

Let $c$ be a code, $x$ a
list of bits and $T$ a natural number. Start the clocked universal stack program at the label
$\mathrm{pc0}$ with internal bit $\mathrm{false}$, with every stack empty except $X$, which holds
the input encoding of $(c, x, T)$: the cell of $T$, the cells of the input symbols of $x$ (the
symbol $1$ for $\mathrm{false}$ and $2$ for $\mathrm{true}$), the bit $\mathrm{false}$, and the
code stack of $c$ reversed, where the cell of a number $n$ is $n$ bits $\mathrm{true}$ followed
by the bit $\mathrm{false}$. Then within at most $N(c, x, T)$ steps, where $N$ is the step bound
of the whole machine, the program reaches the label $\mathrm{done}$ (with some internal bit and
some stack contents) with the output encoding of the clocked evaluation of $c$ on $x$ with clock
$T$ on the stack $O$: the single bit $\mathrm{false}$ if the coded machine does not halt within
$T$ steps, and otherwise the bit $\mathrm{true}$ followed by the cells of its output, the tape
from the head rightwards without trailing blanks.
