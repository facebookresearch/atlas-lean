# Word evaluation depends only on occurring variables

Let $\alpha$ be an alphabet of constants and $V$ a set of variables, disjoint from $\alpha$. A pattern is a finite word over $\alpha \cup V$, and for a substitution $\sigma : V \to \alpha^*$ the evaluation $\sigma(w)$ of a pattern $w$ is the word over $\alpha$ obtained by replacing each variable $x$ in $w$ by $\sigma(x)$. Let $\sigma, \tau : V \to \alpha^*$ and let $w$ be a pattern such that $\sigma(x) = \tau(x)$ for every
variable $x$ occurring in $w$. Then $\sigma(w) = \tau(w)$.
