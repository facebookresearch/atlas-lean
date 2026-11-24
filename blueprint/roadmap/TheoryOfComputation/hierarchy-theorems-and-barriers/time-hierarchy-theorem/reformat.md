# The reformatting machine for $n \mapsto n^2 + 1$

Let $f(n) = n^2 + 1$. This is a
finite multi-stack Turing machine whose input and output alphabets are identified with the bits,
together with a polynomial $p$, such that for every bit list $x$, started with $x$ on its input
stack it halts within $p(|x|)$ steps with output the clocked universal machine's input bits for
the universal machine's argument $(c, w, T)$ for the diagonal language of $f$ at $x$: the clock
$T$ as a cell, the cells of the input symbols of $w$, a blank cell and the code stack of $c$
reversed. It runs the checking machine and then the layout machine.
