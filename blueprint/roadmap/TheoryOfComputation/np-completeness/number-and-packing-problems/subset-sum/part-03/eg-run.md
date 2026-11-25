# Edge-number phase (SUBSET-SUM reduction machine)

Let $d$ be a list of bits (in the
machine, the pair bits listed from the last pair down), $v$ a value of the machine's Boolean flag
and $S$ an assignment of contents to the stacks, and write $\mathrm{val}(d)$ for the list of the
symbols $\mathrm{val}(b)$ for the entries $b$ of $d$, in order. Suppose stack $Y$ holds
$\mathrm{val}(d)$ (first element on top), stacks $C$ and $M$ each hold $|d|$ copies of the unit
symbol, and stack $S_1$ is empty. Then, starting at label $\mathrm{eg}$ with flag $v$ and stacks
$S$, the machine reaches label $\mathrm{egY}$ in at most $|d|(3|d| + 4) + 1$ steps, with some
flag $v'$ and stacks $S'$ such that $S'(Y)$ is empty, $S'(Z)$ is the reverse of
$\mathrm{val}(d)$ followed by $S(Z)$, $S'(O)$ is the edge-number output of $d$ followed by
$S(O)$, and every stack other than $Y$, $Z$, $O$, $C$, $M$ holds the same contents as in $S$.

For each pair $q$ the machine pops its bit onto $Z$ and writes its edge number, using
$C = M = q$.
