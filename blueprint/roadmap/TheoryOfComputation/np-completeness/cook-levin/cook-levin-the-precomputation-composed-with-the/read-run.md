# The read loop's run

Let $M$ be a program of the full machine whose read-loop label carries
the read loop over all of $\mathrm{Fin}\,r$, with code map $c_f$ and separator code $c_s$, and let
$o$ be a list of booleans. For every raw input $s = s_1 \cdots s_\ell$, list of codes $w$,
$n \in \mathbb{N}$ and flag $v$: started at the read-loop label with flag $v$, raw input stack $s$,
input stack $w$, scratch counter $N = n$, output stack $o$ and every other stack empty, $M$ runs in
exactly $\ell + 1$ steps to the counter program's first label, with flag false, raw input stack
empty, input stack $c_s, c_f(s_\ell), \dots, c_f(s_1)$ followed by $w$, scratch counter
$N = n + \ell$, output stack $o$ and every other stack empty.
