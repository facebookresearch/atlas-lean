# A run halts iff it reaches a configuration without successor

Let
$f : \sigma \to \mathrm{Option}\ \sigma$ be a step function and $a \in \sigma$, and write
$f^{(k)}(a) \in \mathrm{Option}\ \sigma$ for the result of $k$ steps from $a$: the $k$-th
iterate, applied to $\mathrm{some}\ a$, of the map sending $\mathrm{none}$ to $\mathrm{none}$
and $\mathrm{some}\ x$ to $f(x)$. The evaluation of $f$ from $a$ (the configuration where the run
from $a$ stops) is defined if and only if there are $k \in \mathbb{N}$ and $b \in \sigma$ with
$f^{(k)}(a) = \mathrm{some}\ b$ and $f(b) = \mathrm{none}$.
