# The init family

Let $L$ be a layout, let $i_c$ be a label/state code, let $k_0$ be a
stack, let $y$ be a list of natural numbers, let $x$ be a list of symbol codes of $L$ of length
$\ell$, and let $m, T, H$ be natural numbers. The init family is the CNF formula obtained by
concatenating, in this order: the start-code clause of the initial row for $i_c$, $T$, $H$ (I1);
the row-$0$ clauses for the stacks other than $k_0$ for $T$, $H$ (I2); the input clauses of the
initial row for $k_0$, $x$, $T$, $H$ (I3); the certificate clauses of the initial row for $k_0$,
$y$, $n = \ell$, $m$, $T$, $H$ (I4); the row-$0$ prefix clauses for $k_0$, $n = \ell$, $m$, $T$,
$H$ (I5); and the row-$0$ tail clauses for $k_0$, $m$, $T$, $H$ (I6).
