# Normalization keeps images of occurring variables

Let $\alpha$ be an alphabet of constants and $V$ a set of variables, disjoint from $\alpha$. A pattern is a finite word over $\alpha \cup V$, and for a substitution $\sigma : V \to \alpha^*$ the evaluation $\sigma(w)$ of a pattern $w$ is the word over $\alpha$ obtained by replacing each variable $x$ in $w$ by $\sigma(x)$. The normalization of $\sigma$ with respect to a pattern $w$ is the substitution that agrees with $\sigma$ on the variables occurring in $w$ and sends every other variable to the empty word. If the variable $x$ occurs in the pattern $w$, then the normalization of $\sigma$ with respect to $w$
sends $x$ to $\sigma(x)$.
