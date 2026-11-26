# Correctness of the SAT-verifier lookup machine

Let $q$ be a list of bits, $es$ a list of
table entries and $R$ a list of symbols that is empty or starts with a symbol other than a name
bit. Suppose the stacks of the lookup machine are as follows: $T$ holds the bits of $q$ as name
bits, last bit on top, above $R$; $B$ holds the table stack of $es$, of length $\ell$; and $S$,
$A$, $C$ and $V$ are empty. Then the lookup program, started at its start label with any
internal bit, reaches the label $\mathsf{done}$ within $8\ell + 4$ steps, with some internal bit;
there $V$ holds the single name bit carrying the live value of $q$ in $es$ (the value of the
first entry of $es$ named $q$ that has a value, or false if there is none), and every other
stack is as it started.
