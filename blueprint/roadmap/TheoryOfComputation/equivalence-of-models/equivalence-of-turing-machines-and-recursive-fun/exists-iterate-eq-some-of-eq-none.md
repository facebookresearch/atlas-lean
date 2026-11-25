# A run that stops passes through a configuration without successor

Let
$f : \sigma \to \mathrm{Option}\ \sigma$ be a step function and $a \in \sigma$, and write
$f^{(k)}(a) \in \mathrm{Option}\ \sigma$ for the result of $k$ steps from $a$: the $k$-th
iterate, applied to $\mathrm{some}\ a$, of the map sending $\mathrm{none}$ to $\mathrm{none}$
and $\mathrm{some}\ x$ to $f(x)$. If $f^{(k)}(a) = \mathrm{none}$ for some $k$, then there are
$j \in \mathbb{N}$ and $b \in \sigma$ with $f^{(j)}(a) = \mathrm{some}\ b$ and
$f(b) = \mathrm{none}$.
