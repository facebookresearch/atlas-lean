# Normalized images are bounded by the evaluation length

Let $\alpha$ be an alphabet of constants and $V$ a set of variables, disjoint from $\alpha$. A pattern is a finite word over $\alpha \cup V$, and for a substitution $\sigma : V \to \alpha^*$ the evaluation $\sigma(w)$ of a pattern $w$ is the word over $\alpha$ obtained by replacing each variable $x$ in $w$ by $\sigma(x)$. The normalization of $\sigma$ with respect to a pattern $w$ is the substitution that agrees with $\sigma$ on the variables occurring in $w$ and sends every other variable to the empty word. For every substitution $\sigma$, pattern $w$ and variable $x$ (occurring in $w$ or not), the image of
$x$ under the normalization of $\sigma$ with respect to $w$ has length at most $|\sigma(w)|$.
