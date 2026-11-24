# Reachability with nonempty sides many-one reduces to MPCP with nonempty words

Let
$\alpha$ be an alphabet with a primitive recursive coding, and let $\alpha'$ be $\alpha$ extended
with two new symbols, the star and the end marker. There is a computable function $f$ from
instances $(R, x, y)$ of the reachability problem over $\alpha$, where $R$ is a list of rewriting
rules over $\alpha$ and $x$ and $y$ are words over $\alpha$, to finite lists of dominoes over
$\alpha'$ such that, for every such instance, the following are equivalent: every rule of $R$ has
a nonempty left side and a nonempty right side and $x$ rewrites to $y$ in zero or more steps of
$R$; and every domino of $f(R, x, y)$ has a nonempty top word and a nonempty bottom word and
$f(R, x, y)$ has an MPCP solution.
