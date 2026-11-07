# The scan loop of the lookup machine

Let $q$ be a list of bits, let $R$ be a list of
symbols that is empty or starts with a symbol other than a name bit, and let $pre$ and $post$ be
lists of table entries; the live value of $q$ in an entry list is the value of its first entry
named $q$ that has a value, or false if there is none. Suppose the lookup program is at label
$\mathsf{scan}$, with any internal bit, and its stacks are: $T$ holds the bits of $q$ as name
bits, last bit on top, above $R$; $B$ holds the table stack of $pre$, of length $\ell$; $S$ holds
the symbols of the entries of $post$ in reading order, first entry on top; $A$ and $C$ are empty;
and $V$ holds the single name bit carrying the live value of $q$ in $post$. Then within
$6\ell + 1$ steps the program reaches label $\mathsf{back}$, with some internal bit, where $B$ is
empty, $S$ holds the symbols of the entries of $pre$ followed by $post$ in reading order, first
entry on top, $V$ holds the single name bit carrying the live value of $q$ in $pre$ followed by
$post$, and $T$, $A$ and $C$ are unchanged.
