# Reachability for rules with nonempty sides many-one reduces to PCP

Let $\alpha$ be an
alphabet with a primitive recursive coding, let $\alpha'$ be $\alpha$ extended with two new
symbols, the star and the end marker, and let $\alpha''$ be $\alpha'$ extended in the same way by
two further new symbols. There is a computable function $f$ from instances $(R, x, y)$ of the
reachability problem over $\alpha$, where $R$ is a list of rewriting rules over $\alpha$ and $x$
and $y$ are words over $\alpha$, to finite lists of dominoes over $\alpha''$ such that, for every
such instance, $f(R, x, y)$ has a PCP solution if and only if every rule of $R$ has a nonempty
left side and a nonempty right side and $x$ rewrites to $y$ in zero or more steps of $R$.
