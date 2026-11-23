# Word substitution normalized by emptying unused images

Let $\alpha$ be an alphabet of constants and $V$ a set of variables, disjoint from $\alpha$. A pattern is a finite word over $\alpha \cup V$, and for a substitution $\sigma : V \to \alpha^*$ the evaluation $\sigma(w)$ of a pattern $w$ is the word over $\alpha$ obtained by replacing each variable $x$ in $w$ by $\sigma(x)$. For a substitution $\sigma : V \to \alpha^*$ and a pattern $w$, the normalization of $\sigma$ with respect
to $w$ is the substitution sending a variable $x$ to $\sigma(x)$ if $x$ occurs in $w$, and to the empty word
otherwise.
