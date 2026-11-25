# Binary conversion (SUBSET-SUM reduction machine)

Let $k$ be a natural number, $v$ a value
of the machine's Boolean flag and $S$ an assignment of contents to the stacks, and list the binary
digits of $k$ least significant first, without leading zeros (so there are none for $k = 0$).
Suppose stack $A$ holds $k$ copies of the unit symbol and stack $H$ is empty. Then, starting at
label $\mathrm{hv}$ with flag $v$ and stacks $S$, the machine reaches label $\mathrm{tem0}$ in at
most $6k + 1$ steps, with some flag $v'$ and stacks $S'$ such that $S'(T)$ is the reverse of the
list of input-bit symbols $\mathrm{bit}(b)$ for these binary digits $b$ of $k$, followed by
$S(T)$, and every stack other than $A$, $H$, $T$ holds the same contents as in $S$.

The machine thus pushes the binary digits of $k$ onto $T$ least significant first.
