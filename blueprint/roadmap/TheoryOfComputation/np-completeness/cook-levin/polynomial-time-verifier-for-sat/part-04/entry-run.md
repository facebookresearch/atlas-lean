# One scan step of the lookup

Write stack contents top first; for a list of bits $u$ let
$\overleftarrow{u}$ be its bit symbols in reverse order; for a list $E$ of table entries let
$\tau(E)$ be the symbols of its entries in reading order (each entry's name bits, then its marker)
and $\mathrm{val}_E(q)$ the value of the first live entry of $E$ named $q$, or false if there is
none. Let $q$ be a list of bits, $e = (n, m)$ a table entry, $E$ a list of entries, $eE$ the list
$E$ with $e$ prepended, and $R$, $r$ lists of symbols each empty or topped by a symbol that is not
a bit. From label $\mathsf{scan}$ with any internal state, $\overleftarrow{q}R$ on $T$, the marker
of $e$ above $\overleftarrow{n}r$ on $B$, $\tau(E)$ on $S$, the stacks $A$ and $C$ empty and the
bit symbol of $\mathrm{val}_E(q)$ alone on $V$, the lookup program reaches, in at most
$4|n| + 6$ steps, label $\mathsf{scan}$ with some internal state, $\overleftarrow{q}R$ on $T$, $r$
on $B$, $\tau(eE)$ on $S$, the stacks $A$ and $C$ empty and the bit symbol of
$\mathrm{val}_{eE}(q)$ alone on $V$.
