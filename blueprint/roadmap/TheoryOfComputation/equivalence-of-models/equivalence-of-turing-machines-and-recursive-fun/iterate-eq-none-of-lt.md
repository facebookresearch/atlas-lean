# A run stays stopped after a configuration without successor

Let
$f : \sigma \to \mathrm{Option}\ \sigma$ be a step function and $a, b \in \sigma$, and write
$f^{(k)}(a) \in \mathrm{Option}\ \sigma$ for the result of $k$ steps from $a$: the $k$-th
iterate, applied to $\mathrm{some}\ a$, of the map sending $\mathrm{none}$ to $\mathrm{none}$
and $\mathrm{some}\ x$ to $f(x)$. If $f^{(k)}(a) = \mathrm{some}\ b$ and $f(b) = \mathrm{none}$,
then $f^{(m)}(a) = \mathrm{none}$ for every $m > k$.
