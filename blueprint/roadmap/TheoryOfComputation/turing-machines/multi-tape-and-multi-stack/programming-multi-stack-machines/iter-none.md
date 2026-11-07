# A halted run stays halted

Let $f : \sigma \to \mathrm{Option}\,\sigma$ be a partial step
function and let $\hat f$ be its lift to $\mathrm{Option}\,\sigma$, which sends $\mathrm{none}$ to
$\mathrm{none}$ and $\mathrm{some}\,x$ to $f(x)$. Then $\hat f^{\,n}(\mathrm{none}) = \mathrm{none}$
for every $n \in \mathbb{N}$.
