# Short accepted certificates exist exactly for satisfiable circuits

Let $c$ be a circuit
over the Boolean signature with $n$ inputs, $s$ gates and one output. The Boolean certificate
verifier accepts some array of at most $n + 2s$ truth values if and only if there are truth
values $x_0, \dots, x_{n-1}$ on which the output of $c$ under the Boolean interpretation is
true.
